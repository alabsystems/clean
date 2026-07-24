// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reference operational semantics for the Perceus reset/reuse discipline,
//! expressed in the trust-ir CORE op subset and differentially checked with the
//! trust-ir reference interpreter.
//!
//! # Why this exists
//!
//! Clean's Perceus in-place-update optimization (`IRExpr::Reset` /
//! `IRExpr::Reuse`, inserted by `reset_reuse.rs`) is emitted by
//! `emit_trust_ir.rs` in one of two ways:
//!
//! * **Dialect mode** — opaque `clean.obj.reset` / `clean.obj.reuse`
//!   `DialectInst` nodes. They round-trip, but carry NO operational semantics
//!   and are out of the lowering-target conformance subset (the `clean.*`
//!   dialect was audited for admission on 2026-07-04 and refused).
//! * **ExternCalls mode** — real `clean_reset` / `clean_reuse` runtime `Call`s.
//!   These lower to machine code and ARE subset-admissible (`Inst::Call` is
//!   allowlisted), but the Perceus DISCIPLINE they implement lives inside the
//!   trusted C runtime, invisible to the IR.
//!
//! Neither form gives the reset/reuse discipline an *executable, checkable*
//! meaning at the trust-ir level. This module supplies that meaning as a
//! **reference model**: the RC-and-branch skeleton of reset/reuse, built from
//! core ops that already have Lean semantics + reference-interpreter support
//! (`IsUnique`, `Retain`, `Release`, `HeapAlloc(CleanHeap)`, `CondBr`), and a
//! differential run proving the reuse-vs-fresh-allocation branch behaves.
//!
//! # Honest boundary (what this DOES and does NOT model)
//!
//! This models the part of Perceus reset/reuse that is RC- and control-flow
//! visible and expressible in core ops:
//! * `reset(cell)` yields a valid reuse token IFF the cell is uniquely owned
//!   (`IsUnique`); on the shared path it `Release`s the cell and the token is
//!   null.
//! * `reuse(token)` reuses the cell in place when the token is valid, else
//!   performs a fresh `HeapAlloc(CleanHeap)`.
//!
//! It deliberately does NOT model the managed-object LAYOUT residue — the
//! child-field `Release` loop `clean_reset` runs before yielding a token, and
//! the in-place constructor field writes `clean_reuse` performs. Those depend
//! on the runtime object header/field layout and are the runtime's job (or a
//! future trust-ir reuse-token primitive — see the design note
//! `designs/2026-07-05-perceus-discipline-in-trust-ir.md`). The emitted handoff
//! form keeps them as the `clean_reset` / `clean_reuse` runtime calls.

use trust_ir::inst::AllocOrigin;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::FuncId;
use trust_ir::Module;
use trust_ir_build::{validate_module, ModuleBuilder};

/// Build a one-function module whose body models `reuse(reset(cell))` in core
/// ops, parameterized by a `shared: bool` flag that decides whether the cell
/// has a second owner (and is therefore NOT uniquely reusable).
///
/// Returns the module and the model function's id. The observable Bool return
/// is `true` when reuse landed in place (unique cell, allocation-free) and
/// `false` when it fell back to a fresh `HeapAlloc(CleanHeap)` (shared cell).
fn build_reset_reuse_model() -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("perceus_reset_reuse_model");
    let sig = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let mut fb = mb.function("reset_reuse", sig);

    // Blocks (entry created first is the SSA entry, carrying the `shared` param).
    let entry = fb.create_block();
    let shared = fb.add_block_param(entry, Ty::Bool);
    let retain_bb = fb.create_block();
    let reset_bb = fb.create_block();
    let unique_bb = fb.create_block();
    let dropped_bb = fb.create_block();
    let reuse_bb = fb.create_block();
    let token_valid = fb.add_block_param(reuse_bb, Ty::Bool);
    let inplace_bb = fb.create_block();
    let fresh_bb = fb.create_block();
    let done_bb = fb.create_block();
    let reused_in_place = fb.add_block_param(done_bb, Ty::Bool);

    // entry: allocate a fresh RC-1 Clean cell; branch on `shared`.
    fb.switch_to_block(entry);
    let cell = fb.heap_alloc(Ty::U64, None, Some(8), AllocOrigin::CleanHeap);
    fb.condbr(shared, retain_bb, vec![], reset_bb, vec![]);

    // retain_bb: simulate a second owner (refcount 1 -> 2), then fall into reset.
    fb.switch_to_block(retain_bb);
    fb.retain(cell);
    fb.br(reset_bb, vec![]);

    // reset_bb: the reuse token is valid IFF the cell is uniquely owned.
    fb.switch_to_block(reset_bb);
    let valid = fb.is_unique(cell);
    fb.condbr(valid, unique_bb, vec![], dropped_bb, vec![]);

    // unique_bb: keep the cell as the reuse token (refcount unchanged). `valid`
    // is statically true here — hand it off as the token-validity bit.
    fb.switch_to_block(unique_bb);
    fb.br(reuse_bb, vec![valid]);

    // dropped_bb: not reusable — `Release` our count (refcount 2 -> 1); `valid`
    // is statically false here, so the handed-off token is invalid.
    fb.switch_to_block(dropped_bb);
    fb.release(cell);
    fb.br(reuse_bb, vec![valid]);

    // reuse_bb: reuse the token's cell in place, else allocate a fresh one.
    fb.switch_to_block(reuse_bb);
    fb.condbr(token_valid, inplace_bb, vec![], fresh_bb, vec![]);

    // inplace_bb: reuse cell A in place (allocation-free — the Perceus win).
    fb.switch_to_block(inplace_bb);
    let yes = fb.bool_const(true);
    fb.br(done_bb, vec![yes]);

    // fresh_bb: the token was null -> a fresh CleanHeap allocation happens. Free
    // it again so the closed model leaves no dangling live allocation.
    fb.switch_to_block(fresh_bb);
    let fresh = fb.heap_alloc(Ty::U64, None, Some(8), AllocOrigin::CleanHeap);
    fb.release(fresh);
    let no = fb.bool_const(false);
    fb.br(done_bb, vec![no]);

    // done_bb: release the surviving cell A (models the eventual drop of the
    // reused object) and yield the branch observable.
    fb.switch_to_block(done_bb);
    fb.release(cell);
    fb.ret(vec![reused_in_place]);

    let fid = fb.build();
    (mb.build(), fid)
}

#[test]
fn perceus_reset_reuse_reference_semantics_differential() {
    let (module, fid) = build_reset_reuse_model();

    // (1) The core-op reference model is well-formed trust-ir.
    let errors = validate_module(&module);
    assert!(
        errors.is_empty(),
        "reset/reuse reference model must validate: {errors:?}"
    );

    // (2) It stays inside the lowering-target conformance subset — it uses only
    //     core ops (HeapAlloc / IsUnique / Retain / Release / CondBr / Br /
    //     Const / Return), NO `clean.*` dialect. So the Perceus discipline has a
    //     subset-clean core-op model even though the emitted handoff form
    //     delegates the layout residue to the `clean_reset`/`clean_reuse`
    //     runtime calls.
    let violations = trust_ir_conformance::subset::module_subset_violations(&module);
    assert!(
        violations.is_empty(),
        "reset/reuse reference model must be subset-clean: {violations:?}"
    );

    // (3) Differential over the reference interpreter (which models exact
    //     single-threaded refcounts + CleanHeap allocation): a UNIQUELY-owned
    //     cell reuses in place (allocation-free); a SHARED cell cannot, so
    //     reuse falls back to a fresh CleanHeap allocation. Both runs complete
    //     with no UB, which independently proves the model's Retain/Release are
    //     refcount-balanced (no double-free, no underflow).
    let interp = Interpreter::with_module(&module);
    let unique = interp
        .execute_func(fid, [InterpretValue::bool(false)])
        .expect("unique-cell run must not hit UB (balanced refcounts)");
    let shared = interp
        .execute_func(fid, [InterpretValue::bool(true)])
        .expect("shared-cell run must not hit UB (balanced refcounts)");

    assert_eq!(
        unique.returns.first().and_then(InterpretValue::as_bool),
        Some(true),
        "a uniquely-owned cell must reuse in place (allocation-free)"
    );
    assert_eq!(
        shared.returns.first().and_then(InterpretValue::as_bool),
        Some(false),
        "a shared cell must fall back to a fresh CleanHeap allocation"
    );

    // (4) Independently of the branch bit: the fresh-allocation path actually
    //     executed the extra `HeapAlloc(CleanHeap)` (plus the second-owner
    //     Retain and the give-back Release), so it does strictly more work than
    //     the allocation-free in-place path.
    assert!(
        shared.steps > unique.steps,
        "the fresh-alloc path must execute the extra HeapAlloc(CleanHeap): \
         unique={} shared={}",
        unique.steps,
        shared.steps
    );
}
