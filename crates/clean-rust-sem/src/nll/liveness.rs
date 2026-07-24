// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Backward liveness analysis over the VIR CFG.

use super::{LivenessResult, ProgramPoint};
use crate::ownership::Place;
use crate::types::RustType;
use crate::vir::{AssertMessage, BasicBlockId, Body, LocalId, Operand, Rvalue, Stmt, Term};
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

/// True if a `Drop` terminator of `place` counts as a *use* for liveness.
///
/// rustc's NLL applies *drop-liveness*: `Drop(x)` requires the regions in
/// `x`'s type to be live only when `x`'s type has drop glue that could
/// observe them (`needs_drop`). Copy types and references (`&T`/`&mut T`)
/// have no drop glue — their drop is a no-op — so such a `Drop` must NOT
/// extend the local's live range. Without this, a `&mut` reference's
/// scope-end `Drop` keeps its loan live past the reference's last real use,
/// falsely rejecting `let r = &mut x; *r = 2; x` (rustc accepts: the borrow
/// dies at `*r = 2`). Projected or indirect dropped places conservatively
/// remain uses: the base local's type is not the dropped type, and
/// `Drop(*p)` genuinely reads the pointer `p`.
fn drop_place_is_liveness_use(body: &Body, place: &Place) -> bool {
    match place {
        Place::Local(local) => body.local(*local).is_none_or(|decl| {
            !(decl.ty.is_copy() || matches!(decl.ty, RustType::Reference { .. }))
        }),
        _ => true,
    }
}

/// Locals a terminator uses for *liveness* purposes: identical to
/// [`term_uses`] except that `Drop` follows drop-liveness (see
/// [`drop_place_is_liveness_use`]).
pub(crate) fn term_uses_for_liveness(body: &Body, term: &Term) -> Vec<LocalId> {
    if let Term::Drop {
        place, target_args, ..
    } = term
    {
        let mut uses: Vec<LocalId> = if drop_place_is_liveness_use(body, place) {
            place_local(place).into_iter().collect()
        } else {
            Vec::new()
        };
        uses.extend(target_args.iter().flat_map(operand_uses));
        return uses;
    }
    term_uses(term)
}

/// Collect locals used by an operand.
pub(crate) fn operand_uses(op: &Operand) -> Vec<LocalId> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => place_local(p).into_iter().collect(),
        Operand::Constant(_) => vec![],
    }
}

/// Get the root local of a place (if it starts with Local).
pub(crate) fn place_local(place: &Place) -> Option<LocalId> {
    match place {
        Place::Local(id) => Some(*id),
        Place::Field { base, .. }
        | Place::Index { base, .. }
        | Place::Deref(base)
        | Place::Downcast { base, .. } => place_local(base),
        Place::Static(_) => None,
    }
}

/// True if writing to `place` writes *through* a pointer (the place's
/// projection chain contains a `Deref`).
///
/// SOUNDNESS (hole 2): `*r = v` writes through `r`; it does **not** redefine
/// the local `r`. Treating such an assignment as a def of `r` (as
/// `place_local` alone would) prematurely kills `r`'s liveness, so the
/// `&mut` loan `r` holds appears dead over the very region where the borrow
/// is actually still live — hiding use/assign-while-borrowed conflicts. An
/// indirect write is therefore not a def; the pointer local(s) it dereferences
/// are *reads* (see [`place_address_reads`]).
fn place_is_indirect(place: &Place) -> bool {
    match place {
        Place::Local(_) | Place::Static(_) => false,
        Place::Deref(_) => true,
        Place::Field { base, .. } | Place::Index { base, .. } | Place::Downcast { base, .. } => {
            place_is_indirect(base)
        }
    }
}

/// Locals read to *compute the address* of `place` (index operands and any
/// pointer local dereferenced along the projection chain). Writing `*r = v`
/// reads `r`; `a[i] = v` reads `i`; the final written storage is not itself a
/// read.
fn place_address_reads(place: &Place, out: &mut Vec<LocalId>) {
    match place {
        Place::Local(_) | Place::Static(_) => {}
        Place::Deref(base) => {
            // The pointer being dereferenced is read.
            out.extend(place_local(base));
            place_address_reads(base, out);
        }
        Place::Index { base, index } => {
            out.extend(place_local(index));
            place_address_reads(base, out);
        }
        Place::Field { base, .. } | Place::Downcast { base, .. } => {
            place_address_reads(base, out);
        }
    }
}

/// Locals used (read) by a statement.
pub(crate) fn stmt_uses(stmt: &Stmt) -> Vec<LocalId> {
    match stmt {
        Stmt::Assign { place, rvalue } => {
            let mut uses = rvalue_uses(rvalue);
            // The destination place's address computation reads locals too:
            // `*r = v` reads `r`, `a[i] = v` reads `i`. Without these, a
            // `&mut` reference written through appears dead over its live
            // region. See `place_address_reads`.
            place_address_reads(place, &mut uses);
            uses
        }
        Stmt::SetDiscriminant { place, .. } => {
            let mut uses = Vec::new();
            place_address_reads(place, &mut uses);
            uses
        }
        Stmt::Retag { place, .. } => place_local(place).into_iter().collect(),
        _ => vec![],
    }
}

/// Locals used by an rvalue.
fn rvalue_uses(rv: &Rvalue) -> Vec<LocalId> {
    match rv {
        Rvalue::Use(op) | Rvalue::Repeat { operand: op, .. } => operand_uses(op),
        Rvalue::Ref { place, .. } | Rvalue::AddressOf { place, .. } => {
            place_local(place).into_iter().collect()
        }
        Rvalue::Len(p) | Rvalue::Discriminant(p) | Rvalue::CopyForDeref(p) => {
            place_local(p).into_iter().collect()
        }
        Rvalue::Cast { operand, .. }
        | Rvalue::UnaryOp { operand, .. }
        | Rvalue::ShallowInitBox { operand, .. } => operand_uses(operand),
        Rvalue::BinaryOp { lhs, rhs, .. } | Rvalue::CheckedBinaryOp { lhs, rhs, .. } => {
            let mut uses = operand_uses(lhs);
            uses.extend(operand_uses(rhs));
            uses
        }
        Rvalue::Aggregate { operands, .. } => operands.iter().flat_map(operand_uses).collect(),
        // An opaque (nondeterministic) value reads no place; it only writes its
        // destination, which `stmt_defs` already accounts for.
        Rvalue::Opaque { .. } | Rvalue::ThreadLocalRef(_) | Rvalue::NullaryOp { .. } => vec![],
    }
}

/// Locals defined (written) by a statement.
///
/// SOUNDNESS (hole 2): an indirect write (`*r = v`, `(*r).f = v`) writes
/// through a pointer and defines *no* local — the base local is only read.
/// Only a direct place (the local itself or a field/index projection of it
/// that does not cross a `Deref`) defines its base local.
pub(crate) fn stmt_defs(stmt: &Stmt) -> Vec<LocalId> {
    match stmt {
        Stmt::Assign { place, .. } | Stmt::SetDiscriminant { place, .. } => {
            if place_is_indirect(place) {
                vec![]
            } else {
                place_local(place).into_iter().collect()
            }
        }
        _ => vec![],
    }
}

/// Locals used by a terminator.
pub(crate) fn term_uses(term: &Term) -> Vec<LocalId> {
    match term {
        Term::Return | Term::Unreachable | Term::UnwindResume | Term::UnwindTerminate => vec![],
        Term::Goto { args, .. } => args.iter().flat_map(operand_uses).collect(),
        Term::SwitchInt {
            discriminant,
            targets,
        } => {
            let mut uses = operand_uses(discriminant);
            for (_, tgt) in targets.iter_targets() {
                uses.extend(tgt.args.iter().flat_map(operand_uses));
            }
            uses
        }
        Term::Call {
            func,
            args,
            destination,
            target_args,
            ..
        } => {
            let mut uses = operand_uses(func);
            uses.extend(args.iter().flat_map(operand_uses));
            // An indirect destination (`*p = f(..)`) reads the pointer local.
            place_address_reads(destination, &mut uses);
            uses.extend(target_args.iter().flat_map(operand_uses));
            uses
        }
        Term::Assert {
            cond,
            msg,
            target_args,
            ..
        } => {
            let mut uses = operand_uses(cond);
            uses.extend(assert_message_uses(msg));
            uses.extend(target_args.iter().flat_map(operand_uses));
            uses
        }
        Term::Drop {
            place, target_args, ..
        } => {
            let mut uses = place_local(place).into_iter().collect::<Vec<_>>();
            uses.extend(target_args.iter().flat_map(operand_uses));
            uses
        }
        Term::Yield {
            value, resume_args, ..
        } => {
            let mut uses = operand_uses(value);
            uses.extend(resume_args.iter().flat_map(operand_uses));
            uses
        }
    }
}

fn assert_message_uses(msg: &AssertMessage) -> Vec<LocalId> {
    match msg {
        AssertMessage::BoundsCheck { len, index } => {
            let mut uses = operand_uses(len);
            uses.extend(operand_uses(index));
            uses
        }
        AssertMessage::Overflow(_, lhs, rhs) => {
            let mut uses = operand_uses(lhs);
            uses.extend(operand_uses(rhs));
            uses
        }
        AssertMessage::OverflowNeg(op)
        | AssertMessage::DivisionByZero(op)
        | AssertMessage::RemainderByZero(op) => operand_uses(op),
        AssertMessage::MisalignedPointerDereference { required, found } => {
            let mut uses = operand_uses(required);
            uses.extend(operand_uses(found));
            uses
        }
        AssertMessage::Custom(_) => vec![],
    }
}

/// Locals defined by a terminator.
///
/// SOUNDNESS (hole 2): an indirect call/resume destination (`*p = f(..)`)
/// writes through a pointer and defines no local; its address reads are
/// surfaced by `term_uses`.
pub(crate) fn term_defs(term: &Term) -> Vec<LocalId> {
    let direct_def = |place: &Place| {
        if place_is_indirect(place) {
            None
        } else {
            place_local(place)
        }
    };
    match term {
        Term::Call { destination, .. } => direct_def(destination).into_iter().collect(),
        Term::Yield { resume_arg, .. } => direct_def(resume_arg).into_iter().collect(),
        _ => vec![],
    }
}

/// Compute block-level gen/kill sets for liveness.
fn compute_block_gen_kill(body: &Body) -> (Vec<HashSet<LocalId>>, Vec<HashSet<LocalId>>) {
    let n = body.blocks.len();
    let mut block_gen = vec![HashSet::new(); n];
    let mut block_kill = vec![HashSet::new(); n];

    for (idx, block) in body.blocks.iter().enumerate() {
        let (generated, kill) = block_gen_kill(body, block);
        block_gen[idx] = generated;
        block_kill[idx] = kill;
    }
    (block_gen, block_kill)
}

/// Gen/kill for a single basic block (walked forward).
///
/// Walking forward ensures that a variable defined at stmt[i] is in `kill`
/// before we process a use at stmt[j] (j > i). The backward walk incorrectly
/// added locally-defined-then-used variables to `gen` because it saw the use
/// before the def.
///
/// Within a single statement, uses are processed before defs (the RHS is
/// evaluated before the LHS is assigned), so `x = x + 1` correctly generates
/// a use of `x` before the def kills it.
fn block_gen_kill(
    body: &Body,
    block: &crate::vir::BasicBlock,
) -> (HashSet<LocalId>, HashSet<LocalId>) {
    let mut generated = HashSet::new();
    let mut kill = HashSet::new();

    // Block params define locals at entry (before any statements).
    for param in &block.params {
        kill.insert(param.local);
    }

    // Walk statements forward.
    for stmt in &block.statements {
        for u in stmt_uses(stmt) {
            if !kill.contains(&u) {
                generated.insert(u);
            }
        }
        for d in stmt_defs(stmt) {
            kill.insert(d);
        }
    }

    // Terminator (at end of block).
    for u in term_uses_for_liveness(body, &block.terminator) {
        if !kill.contains(&u) {
            generated.insert(u);
        }
    }
    for d in term_defs(&block.terminator) {
        kill.insert(d);
    }

    (generated, kill)
}

/// Fixed-point iteration for block-level live_in / live_out.
fn fixpoint_block_liveness(
    body: &Body,
    block_gen: &[HashSet<LocalId>],
    block_kill: &[HashSet<LocalId>],
) -> (Vec<HashSet<LocalId>>, Vec<HashSet<LocalId>>) {
    let n = body.blocks.len();
    let mut live_in: Vec<HashSet<LocalId>> = vec![HashSet::new(); n];
    let mut live_out: Vec<HashSet<LocalId>> = vec![HashSet::new(); n];
    let mut worklist: VecDeque<usize> = (0..n).collect();

    while let Some(bi) = worklist.pop_front() {
        let mut new_out: HashSet<LocalId> = HashSet::new();
        for succ in body.blocks[bi].terminator.successors() {
            if let Some(succ_in) = live_in.get(succ as usize) {
                new_out.extend(succ_in);
            }
        }
        let mut new_in: HashSet<LocalId> = new_out
            .iter()
            .filter(|l| !block_kill[bi].contains(l))
            .copied()
            .collect();
        new_in.extend(&block_gen[bi]);

        if new_in != live_in[bi] {
            live_in[bi] = new_in;
            live_out[bi] = new_out;
            for (pi, pb) in body.blocks.iter().enumerate() {
                if pb.terminator.successors().contains(&(bi as BasicBlockId)) {
                    worklist.push_back(pi);
                }
            }
        } else {
            live_out[bi] = new_out;
        }
    }
    (live_in, live_out)
}

/// Per-point liveness from block-level live_out.
fn per_point_liveness(
    body: &Body,
    live_out: &[HashSet<LocalId>],
) -> HashMap<LocalId, BTreeSet<ProgramPoint>> {
    let mut live_points: HashMap<LocalId, BTreeSet<ProgramPoint>> = HashMap::new();

    for (block_idx, block) in body.blocks.iter().enumerate() {
        let block_id = block_idx as BasicBlockId;
        let mut current: HashSet<LocalId> = live_out[block_idx].clone();

        // Terminator: compute live_before.
        let tp = ProgramPoint::terminator(block_id, block.statements.len());
        for d in term_defs(&block.terminator) {
            current.remove(&d);
        }
        for u in term_uses_for_liveness(body, &block.terminator) {
            current.insert(u);
        }
        for local in &current {
            live_points.entry(*local).or_default().insert(tp);
        }

        // Statements backward.
        for (si, stmt) in block.statements.iter().enumerate().rev() {
            let pt = ProgramPoint::new(block_id, si);
            for d in stmt_defs(stmt) {
                current.remove(&d);
            }
            for u in stmt_uses(stmt) {
                current.insert(u);
            }
            for local in &current {
                live_points.entry(*local).or_default().insert(pt);
            }
        }
    }
    live_points
}

/// Compute backward liveness for all locals in the body.
pub(crate) fn compute_liveness(body: &Body) -> LivenessResult {
    let (block_gen, block_kill) = compute_block_gen_kill(body);
    let (_live_in, live_out) = fixpoint_block_liveness(body, &block_gen, &block_kill);
    let live_points = per_point_liveness(body, &live_out);
    LivenessResult { live_points }
}
