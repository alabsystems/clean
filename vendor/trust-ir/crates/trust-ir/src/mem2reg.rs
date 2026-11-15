// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Escape-checked alloca promotion (mem2reg), the conservative no-phi subset.
//!
//! # Why this pass exists
//!
//! Frontends that lower a register machine (e.g. `tla-ir`'s TY bytecode
//! lowering) commonly materialize **one `alloca i64` per virtual register**
//! and emit a `Load`/`Store` for every read/write of that register. This is
//! the textbook "correct first, optimize later" lowering: it is trivially
//! SSA-correct because every value lives in memory, so there are never any
//! use-before-def or phi obligations to discharge at lowering time.
//!
//! The cost is IR bloat: a tiny straight-line action that would be a handful
//! of arithmetic SSA values balloons into dozens of `Alloca`/`Load`/`Store`
//! nodes. Downstream `trust-cg` can promote supported shapes when its selected
//! optimization pipeline includes SROA, but only after paying to materialize
//! and type-check that memory traffic. Promoting the obvious cases *here*,
//! cheaply, shrinks the IR before it ever reaches codegen.
//!
//! # What this pass does (and only this)
//!
//! [`promote_allocas_function`] / [`promote_allocas_module`] promote exactly
//! the allocas for which promotion is **provably value-identical with zero phi
//! insertion**. An alloca is promoted iff:
//!
//! 1. **It never escapes.** A scalar alloca's result `ValueId` is used *only* as
//!    the `ptr` operand of `Load`/`Store`. It is never GEP'd, never stored as
//!    a value, never passed to a call, never returned, never used as any other
//!    operand. Escape detection and SSA rewriting share one exhaustive operand
//!    walker, so a newly added instruction variant cannot be missed by one
//!    path while being handled by the other.
//!
//! 2. **All of its loads and stores live in a single block.** This is the
//!    conservative subset that needs no phi/block-param insertion: within one
//!    block, the live stored value at each load is unambiguous by linear scan.
//!    Allocas whose loads/stores span multiple blocks are left untouched
//!    (they remain correct memory traffic for a later, phi-capable pass or for
//!    `trust-cg`).
//!
//! 3. **Every load is dominated by a prior store in that block.** A load that
//!    executes before any store would read the alloca's *uninitialized*
//!    contents; we never invent a value for it, so such an alloca is rejected
//!    outright (left as memory). Within a single block, "dominated by a prior
//!    store" is simply "a store to this alloca appears earlier in the block".
//!
//! 4. **The alloca, every store, and every load have exactly the same type.**
//!    An opaque pointer permits differently typed memory accesses, but those
//!    are not scalar identity: a narrow load extracts bytes and a wider access
//!    can exceed the allocation or read bytes a prior store did not initialize.
//!
//! When an alloca qualifies, each promoted `Load`'s result is rewritten to the
//! live stored value (function-wide, via [`rewrite_inst`]), and the now-dead
//! `Alloca`/`Load`/`Store` nodes for it are deleted.
//!
//! # Why the output is identical
//!
//! For a single-block, never-escaping alloca with every load dominated by a
//! prior store, the value read by each load is *exactly* the value of the most
//! recent store, by the semantics of a private (non-escaping) stack slot.
//! Replacing the load's result with that stored value, and deleting the dead
//! memory traffic, changes nothing observable: the slot is private (no other
//! pointer can read or write it), so the stores were dead once their values
//! are forwarded, and `Alloca` itself is side-effect-free. The substitution is
//! dominance-safe because the load's def dominates all of its uses (SSA), and
//! the forwarded store dominates the load (it precedes it in the same block),
//! so the store value dominates every use of the load result.
//!
//! After scalar-register forwarding, a bounded fixed-count integer-array
//! subset additionally admits same-typed constant-offset GEPs and pointer
//! `Copy` aliases. Every access remains in the allocation block, uses exactly
//! the element type, satisfies alignment/bounds, and reads a prior store to
//! that lane. Live casts and other address uses refuse promotion; only a
//! genuinely unused `PtrToInt` leaf may disappear. No source-memory load moves:
//! destination forwarding preserves the original snapshot, not a borrowed
//! view into possibly changing memory. Counts never size analysis collections.

use crate::dialect::{AttrValue, DialectInst};
use crate::inst::{BindingFrameDef, Inst, SwitchCase};
use crate::node::InstrNode;
use crate::value::{FuncId, ValueId};
use crate::{Function, Module};
use std::collections::{HashMap, HashSet};

mod fixed_slots;
#[cfg(test)]
mod fixed_slots_tests;

// ---------------------------------------------------------------------------
// SSA value remapping (shared with the canonical pretty-printer in `format`).
//
// These helpers walk an instruction and rewrite every `ValueId` it mentions
// — results and operands — through a `ValueId -> ValueId` table. They live
// here (always compiled) rather than in the `fmt`-gated `format` module so
// that this pass, which must run during ordinary lowering, can reuse them.
// `format::canonicalize_function` calls back into `rewrite_node` for its dense
// SSA renumbering, so there is exactly one match-on-every-variant rewrite.
// ---------------------------------------------------------------------------

/// Rewrite every `ValueId` inside `node` — results and operands — via `map`.
///
/// Values not present in `map` are left untouched, so the rewrite is a no-op
/// on ids the caller did not ask to remap (and never panics on malformed
/// input).
pub fn rewrite_node(node: &mut InstrNode, map: &HashMap<ValueId, ValueId>) {
    for r in &mut node.results {
        *r = *map.get(r).unwrap_or(r);
    }
    rewrite_inst(&mut node.inst, map);
}

/// Rewrite every `ValueId` *operand* inside `inst` via `map`. Result ids live
/// on the enclosing [`InstrNode`], not on the `Inst`, so this rewrites uses
/// only; use [`rewrite_node`] to rewrite both.
///
/// This is the single authoritative operand-remap: it matches on every `Inst`
/// variant so that adding a new variant fails to compile rather than silently
/// skipping a `ValueId`.
pub fn rewrite_inst(inst: &mut Inst, map: &HashMap<ValueId, ValueId>) {
    rewrite_inst_with(inst, &mut |value| *map.get(value).unwrap_or(value));
}

/// Visit and optionally replace every `ValueId` operand in `inst`.
///
/// Keeping the exhaustive variant match behind this callback lets escape
/// analysis inspect all operands once while [`rewrite_inst`] applies an actual
/// substitution through the same code path.
fn rewrite_inst_with(inst: &mut Inst, lookup: &mut impl FnMut(&ValueId) -> ValueId) {
    match inst {
        // Trust (wave-DS): the dropped pointer is an ordinary operand for substitution --
        // and because a drop USES the pointer, escape analysis sees the alloca as escaping,
        // which is correct: an alloca that is dropped cannot be promoted to a register.
        Inst::Drop { ptr, .. } => {
            *ptr = lookup(ptr);
        }
        // Amendment D: the dropped pointer (an escape, as for `Drop`) and the
        // normal-edge arguments.
        Inst::DropInvoke {
            ptr, normal_args, ..
        } => {
            *ptr = lookup(ptr);
            for a in normal_args {
                *a = lookup(a);
            }
        }
        Inst::BinOp { lhs, rhs, .. }
        | Inst::Overflow { lhs, rhs, .. }
        | Inst::ICmp { lhs, rhs, .. }
        | Inst::FCmp { lhs, rhs, .. } => {
            *lhs = lookup(lhs);
            *rhs = lookup(rhs);
        }
        Inst::UnOp { operand, .. } | Inst::Cast { operand, .. } | Inst::Copy { operand, .. } => {
            *operand = lookup(operand);
        }
        // SeqMap's `fwd` is a FuncId, not a ValueId — only `seq` is remapped.
        Inst::SeqMapAddK { seq, .. } | Inst::SeqMapNot { seq, .. } | Inst::SeqMap { seq, .. } => {
            *seq = lookup(seq);
        }
        Inst::Load { ptr, .. } => {
            *ptr = lookup(ptr);
        }
        Inst::Store { ptr, value, .. } => {
            *ptr = lookup(ptr);
            *value = lookup(value);
        }
        Inst::Alloca { count, .. } | Inst::HeapAlloc { count, .. } => {
            if let Some(c) = count {
                *c = lookup(c);
            }
        }
        Inst::GEP { base, indices, .. } => {
            *base = lookup(base);
            for i in indices {
                *i = lookup(i);
            }
        }
        Inst::PtrData { ptr, .. } | Inst::PtrMetadata { ptr, .. } => {
            *ptr = lookup(ptr);
        }
        Inst::PtrFromParts { data, metadata, .. } => {
            *data = lookup(data);
            *metadata = lookup(metadata);
        }
        Inst::AtomicLoad { ptr, .. } => {
            *ptr = lookup(ptr);
        }
        Inst::AtomicStore { ptr, value, .. } => {
            *ptr = lookup(ptr);
            *value = lookup(value);
        }
        Inst::AtomicRMW { ptr, value, .. } => {
            *ptr = lookup(ptr);
            *value = lookup(value);
        }
        Inst::CmpXchg {
            ptr,
            expected,
            desired,
            ..
        } => {
            *ptr = lookup(ptr);
            *expected = lookup(expected);
            *desired = lookup(desired);
        }
        Inst::Fence { .. } => {}
        Inst::Br { args, .. } => {
            for a in args {
                *a = lookup(a);
            }
        }
        Inst::CondBr {
            cond,
            then_args,
            else_args,
            ..
        } => {
            *cond = lookup(cond);
            for a in then_args {
                *a = lookup(a);
            }
            for a in else_args {
                *a = lookup(a);
            }
        }
        Inst::Switch {
            value,
            default_args,
            cases,
            ..
        } => {
            *value = lookup(value);
            for a in default_args {
                *a = lookup(a);
            }
            for case in cases {
                rewrite_switch_case(case, lookup);
            }
        }
        Inst::Call { args, .. } | Inst::CallCannotUnwind { args, .. } => {
            for a in args {
                *a = lookup(a);
            }
        }
        Inst::CallIndirect { callee, args, .. }
        | Inst::CallIndirectCannotUnwind { callee, args, .. } => {
            *callee = lookup(callee);
            for a in args {
                *a = lookup(a);
            }
        }
        Inst::Return { values } => {
            for v in values {
                *v = lookup(v);
            }
        }
        Inst::MakeAggregate { fields, .. }
        | Inst::MakeClosure {
            captures: fields, ..
        } => {
            for field in fields.iter_mut() {
                *field = lookup(field);
            }
        }
        Inst::ArraySplat { value, .. } => {
            *value = lookup(value);
        }
        // The two tensors; the axis pairs are not values.
        Inst::TensorContract { lhs, rhs, .. } => {
            *lhs = lookup(lhs);
            *rhs = lookup(rhs);
        }
        // PKG-U13c: the operands; a map's lanes, a reduction's axes and a
        // view's node ids are not values.
        Inst::TensorMap { args, .. } => {
            for argument in args.iter_mut() {
                *argument = lookup(argument);
            }
        }
        Inst::TensorReduce { src, .. } => {
            *src = lookup(src);
        }
        Inst::TensorView {
            src, params, fill, ..
        } => {
            *src = lookup(src);
            for param in params.iter_mut() {
                *param = lookup(param);
            }
            if let Some(fill) = fill {
                *fill = lookup(fill);
            }
        }
        // PKG-U13d: the data (or the initial tensor and the source), then
        // the coordinate tensors in axis order.
        Inst::TensorGather { data, coords, .. } => {
            *data = lookup(data);
            for coord in coords.iter_mut() {
                *coord = lookup(coord);
            }
        }
        Inst::TensorScatter {
            init, src, coords, ..
        } => {
            *init = lookup(init);
            *src = lookup(src);
            for coord in coords.iter_mut() {
                *coord = lookup(coord);
            }
        }
        Inst::ExtractField { aggregate, .. } => {
            *aggregate = lookup(aggregate);
        }
        Inst::InsertField {
            aggregate, value, ..
        } => {
            *aggregate = lookup(aggregate);
            *value = lookup(value);
        }
        Inst::ExtractElement { array, index, .. } => {
            *array = lookup(array);
            *index = lookup(index);
        }
        Inst::InsertElement {
            array,
            index,
            value,
            ..
        } => {
            *array = lookup(array);
            *index = lookup(index);
            *value = lookup(value);
        }
        Inst::Const { .. } | Inst::NullPtr | Inst::GlobalAddr { .. } | Inst::Undef { .. } => {
            // No ValueId operands. `Constant::Closure { func, .. }`
            // references a `FuncId`, not a `ValueId`.
        }
        Inst::Assume { cond } => {
            *cond = lookup(cond);
        }
        Inst::Assert { cond, kind, site } => {
            *cond = lookup(cond);
            if let Some(operands) = kind.operands_mut() {
                for operand in operands {
                    *operand = lookup(operand);
                }
            }
            // Amendment P: a run-time location is an SSA use.
            if let Some(location) = site
                .as_mut()
                .and_then(crate::inst::PanicSite::location_value_mut)
            {
                *location = lookup(location);
            }
        }
        Inst::AssertInvoke {
            cond,
            kind,
            site,
            normal_args,
            ..
        } => {
            *cond = lookup(cond);
            if let Some(operands) = kind.operands_mut() {
                for operand in operands {
                    *operand = lookup(operand);
                }
            }
            if let Some(location) = site.location_value_mut() {
                *location = lookup(location);
            }
            for a in normal_args {
                *a = lookup(a);
            }
        }
        Inst::Unreachable => {}
        Inst::Select {
            cond,
            then_val,
            else_val,
            ..
        } => {
            *cond = lookup(cond);
            *then_val = lookup(then_val);
            *else_val = lookup(else_val);
        }
        Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => {
            *ptr = lookup(ptr);
        }
        Inst::EndBorrow { borrow_ptr } => {
            *borrow_ptr = lookup(borrow_ptr);
        }
        Inst::Retain { ptr } | Inst::Release { ptr } | Inst::IsUnique { ptr } => {
            *ptr = lookup(ptr);
        }
        Inst::Dealloc { ptr } => {
            *ptr = lookup(ptr);
        }
        // WS3.20 bulk memory: every operand is an SSA value, and an alloca
        // named by any of them ESCAPES (the escape probe above runs this
        // walker), so a promoted cell can never be bulk-copied behind mem2reg's
        // back.
        Inst::MemCopy {
            dst, src, bytes, ..
        } => {
            *dst = lookup(dst);
            *src = lookup(src);
            *bytes = lookup(bytes);
        }
        Inst::MemSet { dst, byte, bytes } => {
            *dst = lookup(dst);
            *byte = lookup(byte);
            *bytes = lookup(bytes);
        }
        Inst::OpenFrame { def } => {
            rewrite_frame_def(def);
        }
        Inst::BindSlot { frame, value, .. } => {
            *frame = lookup(frame);
            *value = lookup(value);
        }
        Inst::LoadSlot { frame, .. } => {
            *frame = lookup(frame);
        }
        Inst::CloseFrame { frame } => {
            *frame = lookup(frame);
        }
        Inst::CoroSuspend { frame, value, .. } => {
            *frame = lookup(frame);
            *value = lookup(value);
        }
        Inst::Invoke {
            args, normal_args, ..
        } => {
            // Block targets are not values; only the call args and the
            // normal-edge block args are SSA values to be remapped.
            for a in args {
                *a = lookup(a);
            }
            for a in normal_args {
                *a = lookup(a);
            }
        }
        // Amendment D, Part 2: `CallIndirect`'s operands and the normal-edge
        // arguments.
        Inst::InvokeIndirect {
            callee,
            args,
            normal_args,
            ..
        } => {
            *callee = lookup(callee);
            for a in args {
                *a = lookup(a);
            }
            for a in normal_args {
                *a = lookup(a);
            }
        }
        // A landing pad has no SSA value operands (it PRODUCES values).
        Inst::LandingPad { .. } => {}
        Inst::Resume { exn } => {
            *exn = lookup(exn);
        }
        Inst::DialectOp(op) => {
            rewrite_dialect(op, lookup);
        }
    }
}

fn rewrite_switch_case(case: &mut SwitchCase, lookup: &mut impl FnMut(&ValueId) -> ValueId) {
    for a in &mut case.args {
        *a = lookup(a);
    }
}

fn rewrite_frame_def(_def: &mut BindingFrameDef) {
    // `BindingFrameDef` carries a `BindingFrameId` and a list of
    // `BindingSlot { name, ty }`. Neither carries `ValueId` operands —
    // `frame` and `value` are carried by `BindSlot`/`LoadSlot`/`CloseFrame`
    // and rewritten at their respective match arms. Nothing to do here,
    // but kept as an explicit hook so future binding-frame extensions
    // that add value operands have an obvious rewrite point.
}

fn rewrite_dialect(op: &mut DialectInst, lookup: &mut impl FnMut(&ValueId) -> ValueId) {
    for v in &mut op.operands {
        *v = lookup(v);
    }
    // `AttrValue` variants carry no `ValueId`. They can carry types,
    // strings, bytes, or primitive scalars — all independent of SSA.
    // Match on every variant so adding a new variant fails to compile
    // instead of silently skipping.
    for entry in &mut op.attrs {
        match &mut entry.value {
            AttrValue::I64(_)
            | AttrValue::U64(_)
            | AttrValue::F64(_)
            | AttrValue::Bool(_)
            | AttrValue::Str(_)
            | AttrValue::Bytes(_)
            | AttrValue::Ty(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------
// The pass.
// ---------------------------------------------------------------------------

/// Run scalar promotion and, on a canonical 64-bit scalar-layout target,
/// fixed-slot integer-array promotion on unprotected functions in `module`.
///
/// Pure compile-time rewrite: the generated machine-code behavior is
/// unchanged (see the module docs for the identical-output argument).
/// Functions named by a module proof obligation are left unchanged until a
/// proof-aware pass variant supplies both transform-specific verification and
/// a validated proof-table transaction. An unscoped obligation conservatively
/// protects the complete module. This keeps instruction-site coordinates and
/// proof authority from silently becoming stale during the migration to
/// proof-carrying passes.
pub fn promote_allocas_module(module: &mut Module) {
    // The fixed-slot planner checks byte extents in u64. Canonical scalar
    // alignment alone also admits wasm32, whose address arithmetic needs a
    // narrower bound; leave that target untouched by this new subset.
    let canonical_scalar_layout =
        module.target_has_canonical_scalar_layout() && module.pointer_bits() == 64;
    let mut protect_all_functions = false;
    let mut protected_functions: HashSet<FuncId> = HashSet::new();
    for obligation in &module.proof_obligations {
        match (obligation.function, obligation.site) {
            (Some(function), site) => {
                protected_functions.insert(function);
                if let Some(site) = site {
                    protected_functions.insert(site.function);
                }
            }
            (None, Some(site)) => {
                protected_functions.insert(site.function);
            }
            (None, None) => protect_all_functions = true,
        }
    }
    for func in &mut module.functions {
        if !protect_all_functions && !protected_functions.contains(&func.id) {
            promote_allocas_in_layout(func, canonical_scalar_layout);
        }
    }
}

/// Promote the never-escaping, single-block, store-before-load allocas of
/// `func` to SSA values in place.
///
/// Returns the number of allocas promoted (useful for tests / metrics).
/// A function carrying a summary, function- or instruction-level proof
/// annotations, or call-site proof context, is left unchanged. Summary clauses
/// can name SSA values even when no instruction uses those values; preserving
/// their authority needs a proof-aware transaction, not ordinary forwarding.
/// In particular, a function-level
/// [`crate::proof::ProofAnnotation::ProofRef`] may carry replayed module
/// authority even when this function is called without its containing module.
/// This function cannot see module-level proof obligations; callers with a
/// complete [`Module`] should use [`promote_allocas_module`], which also
/// protects externally sited facts. This function-only API remains scalar-only:
/// fixed-slot array promotion needs canonical 64-bit module-layout authority.
pub fn promote_allocas_function(func: &mut Function) -> usize {
    promote_allocas_in_layout(func, false)
}

fn promote_allocas_in_layout(func: &mut Function, canonical_scalar_layout: bool) -> usize {
    if func.summary.is_some()
        || !func.proofs.is_empty()
        || func.blocks.iter().any(|block| {
            block
                .body
                .iter()
                .any(|node| !node.proofs.is_empty() || node.proof_context.is_some())
        })
    {
        return 0;
    }

    // Register forwarding first can make the address cast of a fixed array
    // genuinely unused. The second, no-phi planner still rejects any live
    // integer address; it never assumes a cast roundtrip preserves provenance.
    let mut has_fixed_arrays = false;
    let scalars = promote_scalar_allocas(func, &mut has_fixed_arrays);
    scalars
        + if canonical_scalar_layout && has_fixed_arrays {
            fixed_slots::promote(func)
        } else {
            0
        }
}

fn promote_scalar_allocas(func: &mut Function, has_fixed_arrays: &mut bool) -> usize {
    // 1. Collect candidate allocas: result id -> defining (block_idx, inst_idx).
    //    Only `Alloca` with `count == None` (a single slot) is considered; a
    //    dynamically-counted alloca is an array, never a scalar register.
    let mut candidates: HashMap<ValueId, (usize, usize)> = HashMap::new();
    let mut candidate_types = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ii, node) in block.body.iter().enumerate() {
            *has_fixed_arrays |= matches!(node.inst, Inst::Alloca { count: Some(_), .. });
            if let Inst::Alloca {
                ty, count: None, ..
            } = &node.inst
                && let Some(&result) = node.results.first()
            {
                candidates.insert(result, (bi, ii));
                candidate_types.insert(result, ty.clone());
            }
        }
    }
    if candidates.is_empty() {
        return 0;
    }

    // 2. Escape analysis + locate every load/store of each candidate.
    //    For each candidate we record (block_idx, inst_idx, is_store) of each
    //    of its Load/Store uses, and the single block they all share. An
    //    escape, a multi-block spread, or any non-load/store use disqualifies
    //    the candidate (it is dropped from the map).
    let mut accesses: HashMap<ValueId, Vec<Access>> = HashMap::new();
    let mut use_block: HashMap<ValueId, Option<usize>> = HashMap::new();

    for (bi, block) in func.blocks.iter_mut().enumerate() {
        for (ii, node) in block.body.iter_mut().enumerate() {
            // The candidate's own defining `Alloca` node defines (not uses) the
            // id, and `rewrite_inst` only touches operands, so the escape probe
            // below never flags an `Alloca` against its own result.
            match &mut node.inst {
                Inst::Load {
                    ty, ptr, volatile, ..
                } if candidates.contains_key(ptr) => {
                    if *volatile || candidate_types.get(ptr) != Some(&*ty) {
                        // Volatile traffic is observable; a differently typed
                        // load is not the identity on the stored SSA value.
                        disqualify(&mut candidates, &mut accesses, &mut use_block, *ptr);
                    } else {
                        record_access(
                            &mut accesses,
                            &mut use_block,
                            &mut candidates,
                            *ptr,
                            bi,
                            ii,
                            false,
                        );
                    }
                }
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile,
                    ..
                } if candidates.contains_key(ptr) => {
                    // A candidate stored *as a value* (not as the ptr) escapes:
                    // its address becomes observable through the store target.
                    if candidates.contains_key(value) {
                        disqualify(&mut candidates, &mut accesses, &mut use_block, *value);
                    }
                    // `value == ptr` (degenerate self-store) disqualified ptr above.
                    if candidates.contains_key(ptr) {
                        if *volatile || candidate_types.get(ptr) != Some(&*ty) {
                            disqualify(&mut candidates, &mut accesses, &mut use_block, *ptr);
                        } else {
                            record_access(
                                &mut accesses,
                                &mut use_block,
                                &mut candidates,
                                *ptr,
                                bi,
                                ii,
                                true,
                            );
                        }
                    }
                }
                inst => {
                    // Any other instruction that mentions a candidate id as an
                    // operand is an escape (GEP base, call arg, return, copy,
                    // cast, select, a Store whose *value* is the candidate while
                    // its ptr is not, etc.). Inspect each operand exactly once
                    // through the same exhaustive walker used for rewriting.
                    // This is O(total operands), rather than probing every
                    // candidate alloca against every instruction.
                    let mut escaping = Vec::new();
                    rewrite_inst_with(inst, &mut |value| {
                        if candidates.contains_key(value) {
                            escaping.push(*value);
                        }
                        *value
                    });
                    escaping.sort_unstable();
                    escaping.dedup();
                    for candidate in escaping {
                        disqualify(&mut candidates, &mut accesses, &mut use_block, candidate);
                    }
                }
            }
        }
    }

    // Also handle the load/store-but-escaping-via-value case detected above
    // having possibly removed a candidate that is *also* a ptr elsewhere: the
    // removals above keep `candidates`/`accesses` consistent.

    // 3. For each surviving candidate, do single-block store-before-load
    //    value forwarding. Build a function-wide load-result -> stored-value
    //    remap, and a per-block set of node indices to delete.
    let mut value_remap: HashMap<ValueId, ValueId> = HashMap::new();
    // block_idx -> set of inst indices to delete (allocas, promoted loads/stores).
    let mut deletions: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut promoted_count = 0usize;

    'cand: for (&alloca, accs) in &accesses {
        // All accesses must be in a single block (no-phi subset).
        let block = match use_block.get(&alloca).copied().flatten() {
            Some(b) => b,
            // No loads/stores at all: the alloca is dead. We still promote
            // (delete) it below via the candidate map, but there is nothing to
            // forward. Skip the forwarding loop; deletion handled afterwards.
            None => continue,
        };

        // Accesses were appended during the single forward block walk, so
        // they are already in instruction order. Preserve that ordering
        // without allocating and sorting a second pointer vector per alloca.
        let mut current: Option<ValueId> = None;
        let mut local_loads: Vec<usize> = Vec::new();
        let mut local_stores: Vec<usize> = Vec::new();
        for a in accs {
            debug_assert_eq!(a.block, block);
            if a.is_store {
                // Record the freshly-stored value as live.
                if let Inst::Store { value, .. } = &func.blocks[block].body[a.inst].inst {
                    current = Some(*value);
                }
                local_stores.push(a.inst);
            } else {
                // Load: must be dominated by a prior store in this block.
                match current {
                    Some(v) => {
                        if let Some(&res) = func.blocks[block].body[a.inst].results.first() {
                            value_remap.insert(res, v);
                        }
                        local_loads.push(a.inst);
                    }
                    None => {
                        // Use-before-def: reading uninitialized slot. Reject
                        // this alloca entirely — undo nothing global yet
                        // because we only commit deletions/remaps after this
                        // per-candidate scan succeeds.
                        continue 'cand;
                    }
                }
            }
        }

        // Commit: schedule deletion of this alloca's def, its loads and stores.
        if let Some(&(def_block, def_inst)) = candidates.get(&alloca) {
            deletions.entry(def_block).or_default().push(def_inst);
        }
        for li in local_loads {
            deletions.entry(block).or_default().push(li);
        }
        for si in local_stores {
            deletions.entry(block).or_default().push(si);
        }
        promoted_count += 1;
    }

    // Dead allocas with zero loads/stores: a candidate that survived escape
    // analysis (still in `candidates`) but has no recorded `accesses` has no
    // uses at all. Its result is unused and `Alloca` is side-effect-free, so
    // deleting it is a no-op on behavior.
    for (&alloca, &(def_block, def_inst)) in &candidates {
        if !accesses.contains_key(&alloca) {
            deletions.entry(def_block).or_default().push(def_inst);
            promoted_count += 1;
        }
    }

    if value_remap.is_empty() && deletions.is_empty() {
        return 0;
    }

    apply_promotions(func, value_remap, deletions);
    promoted_count
}

/// Shared authority/debug-preserving commit step for the scalar and fixed-slot
/// planners. Each planner completes escape, initialization and type checks
/// before publishing any substitution or deletion here.
fn apply_promotions(
    func: &mut Function,
    mut value_remap: HashMap<ValueId, ValueId>,
    deletions: HashMap<usize, Vec<usize>>,
) {
    // This pass changes the semantic TrustIR artifact. The source-provenance
    // carrier is compiler authority, so a generic transform must invalidate it
    // rather than recomputing self-authenticating digests around a stale
    // compiler-source claim.
    func.source_provenance = None;
    // Likewise the license's evidence (v61), which names the digest of the
    // body before this rewrite.
    func.invalidate_gate_evidence();

    // 3b. Resolve forwarding chains. A promoted load can forward a value that
    //     is *itself* a promoted load result (e.g. `store(P,%5); %6=load(P);
    //     store(Q,%6); %7=load(Q)` yields `%6->%5, %7->%6`). `%6`'s load is
    //     being deleted, so `%7` must forward all the way to `%5`, not `%6`.
    //     Follow each edge to its ultimate non-promoted target with path
    //     compression. Termination is guaranteed: every edge `result->value`
    //     points at a strictly-earlier-defined SSA value, so the chain cannot
    //     cycle.
    if value_remap.len() > 1 {
        let keys: Vec<ValueId> = value_remap.keys().copied().collect();
        for k in keys {
            let mut target = value_remap[&k];
            // Chase while the target is itself a promoted (about-to-be-deleted)
            // load result. Bounded by the number of distinct keys.
            let mut guard = value_remap.len();
            while let Some(&next) = value_remap.get(&target) {
                target = next;
                guard -= 1;
                if guard == 0 {
                    break; // defensive: cannot happen for acyclic SSA forwarding
                }
            }
            value_remap.insert(k, target);
        }
    }

    // Record every definition that will disappear before mutating the debug
    // name side table. Promoted load results can be retargeted through the
    // compressed `value_remap`; an alloca result has no value-equivalent SSA
    // replacement and its address name must be dropped.
    let deleted_values: HashSet<ValueId> = deletions
        .iter()
        .flat_map(|(block, instructions)| {
            instructions.iter().flat_map(|instruction| {
                func.blocks[*block].body[*instruction]
                    .results
                    .iter()
                    .copied()
            })
        })
        .collect();

    // 4. Apply the load-result -> stored-value remap function-wide. This
    //    rewrites every *use* of a promoted load result (operands only). The
    //    load nodes themselves are about to be deleted, so their results need
    //    no remap.
    if !value_remap.is_empty() {
        for block in &mut func.blocks {
            for (val, _ty) in &mut block.params {
                if let Some(&n) = value_remap.get(val) {
                    *val = n;
                }
            }
            for node in &mut block.body {
                rewrite_inst(&mut node.inst, &value_remap);
                // Do NOT rewrite results: a promoted load's result is being
                // deleted; non-promoted definitions are never in `value_remap`.
            }
        }
    }

    if let Some(names) = &mut func.value_names {
        // Prefer a name already attached to a surviving definition over an
        // alias from a deleted load. If the target has no surviving name,
        // retain the first remapped alias in producer order. This preserves
        // the Function::value_names uniqueness invariant after many loads
        // collapse onto the same stored SSA value.
        let surviving_named: HashSet<ValueId> = names
            .iter()
            .filter_map(|(value, _)| (!deleted_values.contains(value)).then_some(*value))
            .collect();
        let mut seen = HashSet::new();
        names.retain_mut(|(value, _)| {
            if deleted_values.contains(value) {
                let Some(&replacement) = value_remap.get(value) else {
                    return false;
                };
                if surviving_named.contains(&replacement) {
                    return false;
                }
                *value = replacement;
            }
            seen.insert(*value)
        });
    }

    // 5. Delete the promoted alloca/load/store nodes in one stable compaction
    //    per block. Repeated `Vec::remove`, even in descending index order,
    //    shifts a suffix for every removal and is quadratic for the dense
    //    register-file traffic this pass is intended to eliminate.
    for (bi, mut idxs) in deletions {
        idxs.sort_unstable();
        idxs.dedup();
        let mut deleted = idxs.into_iter().peekable();
        let mut index = 0usize;
        func.blocks[bi].body.retain(|_| {
            let remove = deleted.peek().copied() == Some(index);
            if remove {
                deleted.next();
            }
            index += 1;
            !remove
        });
        debug_assert!(deleted.next().is_none());
    }
}

/// Permanently drop `cand` from consideration, clearing every record of it.
fn disqualify(
    candidates: &mut HashMap<ValueId, (usize, usize)>,
    accesses: &mut HashMap<ValueId, Vec<Access>>,
    use_block: &mut HashMap<ValueId, Option<usize>>,
    cand: ValueId,
) {
    candidates.remove(&cand);
    accesses.remove(&cand);
    use_block.remove(&cand);
}

/// Record a load/store access of candidate `cand` at (`bi`, `ii`), enforcing
/// the single-block restriction. If the access is in a different block from a
/// previously-seen access, the candidate is disqualified and removed.
fn record_access(
    accesses: &mut HashMap<ValueId, Vec<Access>>,
    use_block: &mut HashMap<ValueId, Option<usize>>,
    candidates: &mut HashMap<ValueId, (usize, usize)>,
    cand: ValueId,
    bi: usize,
    ii: usize,
    is_store: bool,
) {
    match use_block.get(&cand).copied().flatten() {
        Some(prev) if prev != bi => {
            // Spans multiple blocks: outside the no-phi subset. Disqualify.
            candidates.remove(&cand);
            accesses.remove(&cand);
            use_block.remove(&cand);
        }
        _ => {
            use_block.insert(cand, Some(bi));
            accesses.entry(cand).or_default().push(Access {
                block: bi,
                inst: ii,
                is_store,
            });
        }
    }
}

/// One `Load`/`Store` use of a candidate alloca: its `(block, inst)` position
/// and whether it is the store side. Recorded by [`record_access`] and replayed
/// in instruction order during single-block value forwarding.
struct Access {
    block: usize,
    inst: usize,
    is_store: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Block;
    use crate::constant::Constant;
    use crate::inst::{BinOp, Inst};
    use crate::node::InstrNode;
    use crate::proof::{ObligationKind, ProofAnnotation, ProofObligation, ProofStatus};
    use crate::ty::Ty;
    use crate::value::{BlockId, FuncId, FuncTyId, ProofId};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }
    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    // The function-type table is irrelevant to mem2reg, which only inspects
    // and rewrites block bodies; `FuncTyId(0)` is a fine placeholder.
    fn empty_func() -> Function {
        Function::new(FuncId::new(0), "f", FuncTyId::new(0), b(0))
    }

    fn alloca(res: u32) -> InstrNode {
        InstrNode::new(Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        })
        .with_result(v(res))
    }
    fn store(ptr: u32, value: u32) -> InstrNode {
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(ptr),
            value: v(value),
            volatile: false,
            align: None,
        })
    }
    fn load(res: u32, ptr: u32) -> InstrNode {
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: v(ptr),
            volatile: false,
            align: None,
        })
        .with_result(v(res))
    }
    fn konst(res: u32, val: i128) -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(val),
        })
        .with_result(v(res))
    }
    fn add(res: u32, lhs: u32, rhs: u32) -> InstrNode {
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: v(lhs),
            rhs: v(rhs),
        })
        .with_result(v(res))
    }

    fn block_count_kinds(block: &Block) -> (usize, usize, usize) {
        let mut allocas = 0;
        let mut loads = 0;
        let mut stores = 0;
        for n in &block.body {
            match n.inst {
                Inst::Alloca { .. } => allocas += 1,
                Inst::Load { .. } => loads += 1,
                Inst::Store { .. } => stores += 1,
                _ => {}
            }
        }
        (allocas, loads, stores)
    }

    /// Single-block: alloca, const, store, load, use. The load result must be
    /// forwarded to the stored value and all memory traffic removed.
    #[test]
    fn single_block_promotion() {
        let mut f = empty_func();
        f.source_provenance = Some(crate::SourceProvenance::new(
            crate::proof::ProofDigest::sha256([1; 32]),
            crate::proof::ProofDigest::sha256([2; 32]),
            Vec::new(),
        ));
        // v61: a license whose evidence names the body before the rewrite.
        f.body_gate = Some(crate::BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: Some(crate::GateEvidence {
                obligation: crate::ProofId::new(0),
                body_digest: crate::proof::ProofDigest::sha256([3; 32]),
            }),
        });
        let mut blk = Block::new(b(0));
        // %0 = alloca i64
        blk.body.push(alloca(0));
        // %1 = const 7
        blk.body.push(konst(1, 7));
        // store %1 -> %0
        blk.body.push(store(0, 1));
        // %2 = load %0
        blk.body.push(load(2, 0));
        // %3 = add %2, %2   (use of the load result)
        blk.body.push(add(3, 2, 2));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        f.blocks.push(blk);

        let n = promote_allocas_function(&mut f);
        assert_eq!(n, 1, "exactly one alloca promoted");
        assert!(
            f.source_provenance.is_none(),
            "a semantic rewrite must invalidate compiler source authority"
        );
        assert_eq!(
            f.body_gate,
            Some(crate::BodyGate::gated("clean-kernel-tv")),
            "a semantic rewrite drops the license's evidence and keeps the license"
        );

        let blk = &f.blocks[0];
        let (allocas, loads, stores) = block_count_kinds(blk);
        assert_eq!(
            (allocas, loads, stores),
            (0, 0, 0),
            "all memory traffic removed"
        );

        // The add must now reference %1 (the stored const) instead of %2.
        let add_node = blk
            .body
            .iter()
            .find(|n| matches!(n.inst, Inst::BinOp { .. }))
            .unwrap();
        match &add_node.inst {
            Inst::BinOp { lhs, rhs, .. } => {
                assert_eq!(*lhs, v(1));
                assert_eq!(*rhs, v(1));
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn function_with_instruction_proof_metadata_is_not_rewritten() {
        let mut f = empty_func();
        let mut blk = Block::new(b(0));
        blk.body
            .push(alloca(0).with_proof(ProofAnnotation::InBounds));
        blk.body.push(konst(1, 7));
        blk.body.push(store(0, 1));
        blk.body.push(load(2, 0));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f.blocks.push(blk);

        assert_eq!(promote_allocas_function(&mut f), 0);
        assert_eq!(block_count_kinds(&f.blocks[0]), (1, 1, 1));
        assert_eq!(f.blocks[0].body[0].proofs, vec![ProofAnnotation::InBounds]);
    }

    #[test]
    fn function_with_function_proof_metadata_is_not_rewritten() {
        let mut f = empty_func();
        f.proofs.push(ProofAnnotation::ProofRef(ProofId::new(7)));
        let mut blk = Block::new(b(0));
        blk.body.push(alloca(0));
        blk.body.push(konst(1, 7));
        blk.body.push(store(0, 1));
        blk.body.push(load(2, 0));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f.blocks.push(blk);

        assert_eq!(promote_allocas_function(&mut f), 0);
        assert_eq!(block_count_kinds(&f.blocks[0]), (1, 1, 1));
        assert_eq!(f.proofs, vec![ProofAnnotation::ProofRef(ProofId::new(7))]);
    }

    #[test]
    fn module_wrapper_preserves_functions_named_by_proof_obligations() {
        let mut module = Module::new("proof-bearing");
        let mut f = empty_func();
        let mut blk = Block::new(b(0));
        blk.body.push(alloca(0));
        blk.body.push(konst(1, 7));
        blk.body.push(store(0, 1));
        blk.body.push(load(2, 0));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f.blocks.push(blk);
        module.functions.push(f);
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::TranslationValidation,
                ProofStatus::Pending,
                "the source function and lowered function agree",
            )
            .with_function(FuncId::new(0)),
        );

        promote_allocas_module(&mut module);

        assert_eq!(block_count_kinds(&module.functions[0].blocks[0]), (1, 1, 1));
        assert_eq!(module.proof_obligations.len(), 1);
    }

    /// Multiple stores: each load reads the most-recent prior store value.
    #[test]
    fn multi_store_forwards_latest_value() {
        let mut f = empty_func();
        let mut blk = Block::new(b(0));
        blk.body.push(alloca(0)); // %0 = alloca
        blk.body.push(konst(1, 11)); // %1 = 11
        blk.body.push(konst(2, 22)); // %2 = 22
        blk.body.push(store(0, 1)); // store %1
        blk.body.push(load(3, 0)); // %3 = load -> %1
        blk.body.push(store(0, 2)); // store %2
        blk.body.push(load(4, 0)); // %4 = load -> %2
        blk.body.push(add(5, 3, 4)); // %5 = %3 + %4 -> %1 + %2
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(5)] }));
        f.blocks.push(blk);

        assert_eq!(promote_allocas_function(&mut f), 1);
        let blk = &f.blocks[0];
        assert_eq!(block_count_kinds(blk), (0, 0, 0));
        let add_node = blk
            .body
            .iter()
            .find(|n| matches!(n.inst, Inst::BinOp { .. }))
            .unwrap();
        match &add_node.inst {
            Inst::BinOp { lhs, rhs, .. } => {
                assert_eq!(*lhs, v(1), "first load forwards first store");
                assert_eq!(*rhs, v(2), "second load forwards second store");
            }
            _ => unreachable!(),
        }
    }

    /// Escape via GEP: the alloca address flows into a GEP base, so it must NOT
    /// be promoted; all nodes are preserved unchanged.
    #[test]
    fn escape_via_gep_rejected() {
        let mut f = empty_func();
        let mut blk = Block::new(b(0));
        blk.body.push(alloca(0)); // %0 = alloca
        blk.body.push(konst(1, 0)); // %1 = 0
        // %2 = gep %0, %1   (escape!)
        blk.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            })
            .with_result(v(2)),
        );
        blk.body.push(store(0, 1)); // store %1 -> %0
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);

        let before = f.clone();
        assert_eq!(
            promote_allocas_function(&mut f),
            0,
            "escaping alloca not promoted"
        );
        assert_eq!(f, before, "IR is unchanged when nothing is promotable");
    }

    /// Escape via being stored as a *value* (its address is written through a
    /// foreign pointer). The escaping alloca and the escaping store both stay.
    #[test]
    fn escape_via_store_value_rejected() {
        let mut f = empty_func();
        // Block param %9 is a foreign pointer (e.g. an out-pointer). Storing
        // %0 *into* %9 publishes %0's address — %0 escapes.
        let mut blk = Block::new(b(0));
        blk.params.push((v(9), Ty::Ptr));
        blk.body.push(alloca(0)); // %0 = alloca (the slot we care about)
        // store %0 -> %9   (%0's address escapes as the stored value)
        blk.body.push(store(9, 0));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);

        let before = f.clone();
        // %9 is not an alloca; the only alloca %0 escapes. Nothing promotable.
        assert_eq!(promote_allocas_function(&mut f), 0);
        assert_eq!(f, before, "escaped alloca and its escaping store preserved");
    }

    /// Use-before-def: a load with no prior store reads uninitialized memory;
    /// the alloca must be left as memory (not promoted), unchanged.
    #[test]
    fn use_before_def_rejected() {
        let mut f = empty_func();
        let mut blk = Block::new(b(0));
        blk.body.push(alloca(0)); // %0 = alloca
        blk.body.push(load(1, 0)); // %1 = load %0   (no prior store!)
        blk.body.push(store(0, 1)); // store %1 -> %0
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        f.blocks.push(blk);

        let before = f.clone();
        assert_eq!(promote_allocas_function(&mut f), 0);
        assert_eq!(f, before, "use-before-def alloca left untouched");
    }

    /// Cross-block loads/stores: outside the no-phi subset, left untouched.
    #[test]
    fn cross_block_not_promoted() {
        let mut f = empty_func();
        // Block 0: alloca + store, then branch to block 1.
        let mut b0 = Block::new(b(0));
        b0.body.push(alloca(0));
        b0.body.push(konst(1, 5));
        b0.body.push(store(0, 1));
        b0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![],
        }));
        // Block 1: load + return (load is in a different block from the store).
        let mut b1 = Block::new(b(1));
        b1.body.push(load(2, 0));
        b1.body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f.blocks.push(b0);
        f.blocks.push(b1);

        let before = f.clone();
        assert_eq!(
            promote_allocas_function(&mut f),
            0,
            "cross-block alloca not promoted in the no-phi subset"
        );
        assert_eq!(f, before);
    }

    /// Load result used in a *later* block must still be correctly forwarded
    /// (the substitution is function-wide). Store+load live in block 0; the
    /// use of the load result lives in block 1.
    #[test]
    fn load_result_used_in_later_block_forwarded() {
        let mut f = empty_func();
        let mut b0 = Block::new(b(0));
        b0.body.push(alloca(0)); // %0 = alloca
        b0.body.push(konst(1, 9)); // %1 = 9
        b0.body.push(store(0, 1)); // store %1 -> %0
        b0.body.push(load(2, 0)); // %2 = load %0  (forwards to %1)
        b0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![],
        }));
        let mut b1 = Block::new(b(1));
        b1.body.push(add(3, 2, 1)); // %3 = %2 + %1  (use of load result in block 1)
        b1.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        f.blocks.push(b0);
        f.blocks.push(b1);

        assert_eq!(promote_allocas_function(&mut f), 1);
        // %3 = add must now read %1, %1.
        let add_node = f.blocks[1]
            .body
            .iter()
            .find(|n| matches!(n.inst, Inst::BinOp { .. }))
            .unwrap();
        match &add_node.inst {
            Inst::BinOp { lhs, rhs, .. } => {
                assert_eq!(*lhs, v(1));
                assert_eq!(*rhs, v(1));
            }
            _ => unreachable!(),
        }
    }

    /// Volatile loads/stores are observable; their alloca must not be promoted.
    #[test]
    fn volatile_access_not_promoted() {
        let mut f = empty_func();
        let mut blk = Block::new(b(0));
        blk.body.push(alloca(0)); // %0 = alloca
        blk.body.push(konst(1, 3)); // %1 = 3
        // volatile store %1 -> %0
        blk.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            volatile: true,
            align: None,
        }));
        // %2 = volatile load %0
        blk.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(0),
                volatile: true,
                align: None,
            })
            .with_result(v(2)),
        );
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f.blocks.push(blk);

        let before = f.clone();
        assert_eq!(promote_allocas_function(&mut f), 0);
        assert_eq!(f, before, "volatile-accessed alloca left untouched");
    }

    /// A candidate passed to a call escapes and must not be promoted.
    #[test]
    fn escape_via_call_arg_rejected() {
        let mut f = empty_func();
        let mut blk = Block::new(b(0));
        blk.body.push(alloca(0)); // %0 = alloca
        blk.body.push(konst(1, 1)); // %1 = 1
        blk.body.push(store(0, 1)); // store %1 -> %0
        // call f(%0)  — %0's address escapes into the callee.
        blk.body.push(InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![v(0)],
        }));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);

        let before = f.clone();
        assert_eq!(promote_allocas_function(&mut f), 0);
        assert_eq!(f, before, "call-escaped alloca left untouched");
    }

    /// A dead alloca (never loaded or stored, never escaping) is removed.
    #[test]
    fn dead_alloca_removed() {
        let mut f = empty_func();
        let mut blk = Block::new(b(0));
        blk.body.push(alloca(0)); // %0 = alloca (unused)
        blk.body.push(konst(1, 0)); // %1 = 0
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        f.blocks.push(blk);

        assert_eq!(promote_allocas_function(&mut f), 1);
        let (allocas, _, _) = block_count_kinds(&f.blocks[0]);
        assert_eq!(allocas, 0, "dead alloca removed");
        // The unrelated const and return are untouched.
        assert!(
            f.blocks[0]
                .body
                .iter()
                .any(|n| matches!(n.inst, Inst::Const { .. }))
        );
    }

    /// Alloca defined in the entry block, but all of its loads/stores confined
    /// to a single *later* block. This is the no-phi subset (single-block
    /// accesses) even though the alloca def lives elsewhere. It must promote,
    /// deleting the entry-block alloca and the block-1 memory traffic.
    #[test]
    fn alloca_in_entry_accesses_in_later_block() {
        let mut f = empty_func();
        // Block 0: just the alloca, then branch.
        let mut b0 = Block::new(b(0));
        b0.body.push(alloca(0)); // %0 = alloca (entry)
        b0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![],
        }));
        // Block 1: const, store, load, use, return — all accesses here.
        let mut b1 = Block::new(b(1));
        b1.body.push(konst(1, 8)); // %1 = 8
        b1.body.push(store(0, 1)); // store %1 -> %0
        b1.body.push(load(2, 0)); // %2 = load %0  (forwards to %1)
        b1.body.push(add(3, 2, 2)); // %3 = %2 + %2
        b1.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        f.blocks.push(b0);
        f.blocks.push(b1);

        assert_eq!(promote_allocas_function(&mut f), 1);
        // Entry block: alloca gone, only the branch remains.
        assert_eq!(block_count_kinds(&f.blocks[0]), (0, 0, 0));
        // Block 1: no memory traffic, and the add reads %1, %1.
        assert_eq!(block_count_kinds(&f.blocks[1]), (0, 0, 0));
        let add_node = f.blocks[1]
            .body
            .iter()
            .find(|n| matches!(n.inst, Inst::BinOp { .. }))
            .unwrap();
        match &add_node.inst {
            Inst::BinOp { lhs, rhs, .. } => {
                assert_eq!(*lhs, v(1));
                assert_eq!(*rhs, v(1));
            }
            _ => unreachable!(),
        }
    }

    /// Chained forwarding: a promoted load feeds a store into a *second*
    /// promoted alloca. The transitive resolution must forward the final use
    /// all the way to the original stored constant, not to a deleted load.
    #[test]
    fn chained_forwarding_resolves_to_original() {
        let mut f = empty_func();
        let mut blk = Block::new(b(0));
        blk.body.push(alloca(0)); // %0 = alloca P
        blk.body.push(alloca(1)); // %1 = alloca Q
        blk.body.push(konst(2, 42)); // %2 = 42
        blk.body.push(store(0, 2)); // store %2 -> P
        blk.body.push(load(3, 0)); // %3 = load P     (=> %2)
        blk.body.push(store(1, 3)); // store %3 -> Q   (value %3, a promoted load)
        blk.body.push(load(4, 1)); // %4 = load Q     (=> %3 => %2)
        blk.body.push(add(5, 4, 4)); // %5 = %4 + %4
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(5)] }));
        f.blocks.push(blk);

        assert_eq!(promote_allocas_function(&mut f), 2);
        let blk = &f.blocks[0];
        assert_eq!(block_count_kinds(blk), (0, 0, 0), "all memory removed");
        let add_node = blk
            .body
            .iter()
            .find(|n| matches!(n.inst, Inst::BinOp { .. }))
            .unwrap();
        match &add_node.inst {
            Inst::BinOp { lhs, rhs, .. } => {
                // Must resolve to %2 (the original constant), NOT %3 (a deleted
                // load) and NOT %4 (a deleted load).
                assert_eq!(*lhs, v(2), "chain resolved to original stored value");
                assert_eq!(*rhs, v(2));
            }
            _ => unreachable!(),
        }
    }

    /// Debug names are an SSA side table: promotion must not leave them
    /// pointing at deleted allocas/loads or duplicate them when several load
    /// results collapse onto one stored value.
    #[test]
    fn promotion_keeps_value_names_referentially_closed() {
        let mut f = empty_func();
        f.value_names = Some(vec![
            (v(0), "slot".to_string()),
            (v(1), "stored".to_string()),
            (v(2), "first load".to_string()),
            (v(3), "second load".to_string()),
            (v(4), "sum".to_string()),
        ]);
        let mut blk = Block::new(b(0));
        blk.body.push(alloca(0));
        blk.body.push(konst(1, 42));
        blk.body.push(store(0, 1));
        blk.body.push(load(2, 0));
        blk.body.push(load(3, 0));
        blk.body.push(add(4, 2, 3));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(4)] }));
        f.blocks.push(blk);

        assert_eq!(promote_allocas_function(&mut f), 1);
        assert_eq!(
            f.value_names.as_deref(),
            Some(&[(v(1), "stored".to_string()), (v(4), "sum".to_string()),][..]),
            "the surviving value's own name wins and deleted definitions vanish"
        );
    }

    /// Counted (array) allocas are never promoted.
    #[test]
    fn counted_alloca_not_promoted() {
        let mut f = empty_func();
        let mut blk = Block::new(b(0));
        blk.body.push(konst(0, 4)); // %0 = 4 (count)
        blk.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(0)),
                align: None,
            })
            .with_result(v(1)),
        );
        blk.body.push(konst(2, 7));
        blk.body.push(store(1, 2)); // store into the array base
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);

        let before = f.clone();
        assert_eq!(promote_allocas_function(&mut f), 0);
        assert_eq!(f, before);
    }
}
