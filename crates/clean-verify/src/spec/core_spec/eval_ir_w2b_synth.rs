// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **W2b — the synthetic micro-module lane's memory tranche: `alloca`,
//! `ptrdata`, `ptrmetadata`, `ptrfromparts`.**
//!
//! Plan: `docs/analysis/evalir-completion-plan-2026-08-24.md` §5 W2b. These
//! four `IRInst` constructors have REAL dispatch arms (`ir_exec`,
//! `eval_ir_machine.rs:922,924-926`) but no committed emitted body exercises
//! them. Same lane discipline as W2a (`eval_ir_w2a_synth.rs`, read its module
//! doc first): one authored micro-module per constructor, kernel-executed
//! `ir_w2b_*` witnesses including the fault edges, synthetic `.trust-ir.txt`
//! twins under `tests/fixtures/synth/`, and `Synthetic`-labeled battery rows
//! (`tests/crystal_a3_semdiff/w2b_chains.rs`) that re-read this stage's module
//! lines through the `ir_w2b_*_module_defs` re-exports.
//!
//! ## Why every module here is a COMPOSITION, unlike W2a's
//!
//! W2a's constructors compute on values already in registers, so each body
//! could be one interesting instruction. A memory constructor's result is only
//! OBSERVABLE through the heap: an `alloca` is invisible until something is
//! stored to and loaded from it, and a pointer-lane projection is invisible
//! until the projected pointer is dereferenced (or the projected metadata
//! returned). So each module here is the SMALLEST composition that makes its
//! constructor observable — alloca/store/load for `alloca`, an extra
//! `ptr_data` inside that round-trip for `ptrdata`, a fat rebuild plus
//! metadata projection for `ptrmetadata`, and a rebuild-then-deref pair (thin
//! and fat arms behind a condbr) for `ptrfromparts`. `store`, `load` and
//! `condbr` ride along; all three already carry W1 agreement rows, so the new
//! information in each chain is its constructor's.
//!
//! ## Design constraints and measured facts that shaped the modules
//!
//! * **Addresses are transport-only, values are transport-only.** No module
//!   here does arithmetic on a stored value, so witnesses hold with payloads
//!   UNIVERSALLY QUANTIFIED (the `ir_is_zero_on_param` idiom), and u32::MAX /
//!   2^32 sentinel rows are phrasable in the battery without wrap residue.
//! * **The uninitialized-read edge diverges by FAULT SITE, not class.**
//!   Clean's `ir_load_value` faults `ub uninit` AT THE LOAD of a fresh cell;
//!   the reference interpreter's plain load of uninitialized bytes yields an
//!   inert `PartialBytes` poison value and faults `undefined_behavior` only
//!   when the value is INSPECTED — for the alloca module, at the `ret`
//!   signature check (`interpret.rs:5402-5403`, `reject_partial_error`,
//!   measured at trust-ir `a4e81b6`). Same program, same input, same UB
//!   verdict, different step of the trace. The battery compares the row at
//!   outcome CLASS (both UB) and this doc plus the chain's notes record the
//!   site split; a module that loaded uninitialized memory and only STORED it
//!   elsewhere would genuinely diverge (Clean UB, interpreter defined), and no
//!   module here does that — recorded as fragment residue in
//!   `data/evalir_w2b.PENDING.md`, not smoothed.
//! * **Clean's fat pointer erased the metadata's pointer-ness until crystal
//!   E5.** `IRScalar.fat_ d md` carries `md : Nat`, and `ir_ptrmeta_eval`
//!   returned `IRScalar.int_ md` even when the metadata was built from a
//!   pointer (`ir_ptrparts_at`'s vtable arm). Since E5 (decision memo §23) it
//!   reads the word at the node's declared metadata type -- `ptr_ md` at
//!   `IRTy.ptr_` -- and the thin/not-ptr witnesses below hold at EVERY
//!   declared type. The battery therefore measures
//!   `ptrmetadata` on the SLICE/STR shape, where both executors return the
//!   length as a pointer-sized unsigned integer; the vtable and fnptr rebuild
//!   arms are pinned kernel-side here (`ir_w2b_pp_vtable`/`ir_w2b_pp_fnptr`)
//!   and their E2-comparable observable is the DATA lane (the `ptrfromparts`
//!   chain's fat path), never the metadata lane.
//! * **`fatptr<str>` is the E2 twin's fat shape.** At the pinned 64-bit
//!   little-endian target the canonical str/slice metadata type is `u64`
//!   (`shape.rs::PointerMetadataShape::metadata_ty`), and
//!   `validate_fat_pointer_value` requires the metadata lane to inhabit it
//!   exactly. `str` needs no element TyId, so the synthetic module carries no
//!   type table. Clean's twin types the same instructions
//!   `IRTy.fatptr_ (IRTy.uint_ 8)` / `IRTy.uint_ 64` — cosmetic to the
//!   machine, which consults none of these type operands (the W5 adequacy
//!   grid owns proving that).
//!
//! Everything here is `DerivedProved`, zero axiom_deps: every witness is an
//! `Eq.refl` the kernel discharges by running the machine (whole-program
//! `ir_eval` witnesses) or by iota-reducing one evaluator match (value-level
//! witnesses over `ir_ptrdata_eval` / `ir_ptrmeta_eval` / `ir_ptrparts_at` /
//! `ir_ptrparts_eval`). Witness fuels are SUFFICIENT, not least — the battery
//! pins each row's least fuel from below.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ── alloca: fresh cell; store/load round-trip or uninitialized read ───────
//
//   bb0(%0: u32, %1: bool): %2 = alloca u32; condbr %1, bb1, bb2
//   bb1: store u32 %0, ptr %2; %3 = load u32, ptr %2; ret %3
//   bb2: %4 = load u32, ptr %2; ret %4

const SRC_IR_W2B_AL_B0: &str = "def ir_w2b_al_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.alloca (IRTy.uint_ 32) (IROption.none Nat)) ir_d2) (ir_nd (IRInst.condbr ir_d1 ir_d1 ir_nl0 ir_d2 ir_nl0)))";

const SRC_IR_W2B_AL_B1: &str = "def ir_w2b_al_b1 : IRBlock := IRBlock.mk ir_d1 ir_nl0 (ir_bd3 (ir_nd (IRInst.store (IRTy.uint_ 32) ir_d2 ir_d0 Bool.false)) (ir_nd1 (IRInst.load (IRTy.uint_ 32) ir_d2 Bool.false) ir_d3) (ir_nd (IRInst.ret (ir_nl1 ir_d3))))";

const SRC_IR_W2B_AL_B2: &str = "def ir_w2b_al_b2 : IRBlock := IRBlock.mk ir_d2 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.load (IRTy.uint_ 32) ir_d2 Bool.false) ir_d4) (ir_nd (IRInst.ret (ir_nl1 ir_d4))))";

const SRC_IR_W2B_AL_FUNC: &str = "def ir_w2b_al_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_w2b_al_b0 (ir_blk ir_w2b_al_b1 (ir_blk ir_w2b_al_b2 ir_blk0)))";

const SRC_IR_W2B_AL_MODULE: &str = "def ir_w2b_al_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_w2b_al_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

/// The `alloca` micro-module's definitions, in registration order — the lines
/// the battery registers, re-exported rather than re-typed.
#[must_use]
pub fn ir_w2b_al_module_defs() -> &'static [&'static str] {
    &[
        SRC_IR_W2B_AL_B0,
        SRC_IR_W2B_AL_B1,
        SRC_IR_W2B_AL_B2,
        SRC_IR_W2B_AL_FUNC,
        SRC_IR_W2B_AL_MODULE,
    ]
}

const SRC_IR_W2B_AL_ON_STORE: &str = "def ir_w2b_al_on_store (x : Nat) : Eq IROutcome (ir_eval ir_d8 ir_w2b_al_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ x) (IRList.cons IRScalar (IRScalar.bool_ Bool.true) (IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ x))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ x)))";

const SRC_IR_W2B_AL_ON_UNINIT: &str = "def ir_w2b_al_on_uninit (x : Nat) : Eq IROutcome (ir_eval ir_d8 ir_w2b_al_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ x) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.ub IRFault.uninit) := Eq.refl IROutcome (IROutcome.ub IRFault.uninit)";

const SRC_IR_W2B_AL_NONBOOL: &str = "def ir_w2b_al_nonbool (x : Nat) (n : Nat) : Eq IROutcome (ir_eval ir_d8 ir_w2b_al_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ x) (IRList.cons IRScalar (IRScalar.int_ n) (IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_bool) := Eq.refl IROutcome (IROutcome.type_error IRFault.not_bool)";

// ── ptrdata: thin data-lane identity inside a store/load round-trip ───────
//
//   bb0(%0: u32): %1 = alloca u32; store u32 %0, ptr %1;
//                 %2 = ptr_data ptr %1; %3 = load u32, ptr %2; ret %3

const SRC_IR_W2B_PD_B0: &str = "def ir_w2b_pd_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (ir_nd1 (IRInst.alloca (IRTy.uint_ 32) (IROption.none Nat)) ir_d1) (IRList.cons IRNode (ir_nd (IRInst.store (IRTy.uint_ 32) ir_d1 ir_d0 Bool.false)) (ir_bd3 (ir_nd1 (IRInst.ptrdata IRTy.ptr_ ir_d1) ir_d2) (ir_nd1 (IRInst.load (IRTy.uint_ 32) ir_d2 Bool.false) ir_d3) (ir_nd (IRInst.ret (ir_nl1 ir_d3))))))";

const SRC_IR_W2B_PD_FUNC: &str = "def ir_w2b_pd_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_w2b_pd_b0 ir_blk0)";

const SRC_IR_W2B_PD_MODULE: &str = "def ir_w2b_pd_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_w2b_pd_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

/// The `ptrdata` micro-module's definitions, in registration order.
#[must_use]
pub fn ir_w2b_pd_module_defs() -> &'static [&'static str] {
    &[SRC_IR_W2B_PD_B0, SRC_IR_W2B_PD_FUNC, SRC_IR_W2B_PD_MODULE]
}

const SRC_IR_W2B_PD_ON_ROUNDTRIP: &str = "def ir_w2b_pd_on_roundtrip (x : Nat) : Eq IROutcome (ir_eval ir_d8 ir_w2b_pd_module ir_d0 (ir_vl1 (IRScalar.int_ x)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ x))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ x)))";

const SRC_IR_W2B_PD_FAT: &str = "def ir_w2b_pd_fat (d : Nat) (md : Nat) : Eq IRStepResult (ir_ptrdata_eval (IRScalar.fat_ d md)) (IRStepResult.value (IRScalar.ptr_ d)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.ptr_ d))";

const SRC_IR_W2B_PD_NULL: &str = "def ir_w2b_pd_null : Eq IRStepResult (ir_ptrdata_eval IRScalar.nullptr_) (IRStepResult.value IRScalar.nullptr_) := Eq.refl IRStepResult (IRStepResult.value IRScalar.nullptr_)";

const SRC_IR_W2B_PD_NOT_PTR: &str = "def ir_w2b_pd_not_ptr (n : Nat) : Eq IRStepResult (ir_ptrdata_eval (IRScalar.int_ n)) (IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_ptr))";

// ── ptrmetadata: str-fat rebuild, metadata projection returns the length ──
//
//   bb0(%0: u32, %1: u64): %2 = alloca u32; store u32 %0, ptr %2;
//     %3 = ptr_from_parts fatptr<str> ptr %2, u64 %1;
//     %4 = ptr_metadata fatptr<str> %3 to u64; ret %4

const SRC_IR_W2B_PM_B0: &str = "def ir_w2b_pm_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (ir_nd1 (IRInst.alloca (IRTy.uint_ 32) (IROption.none Nat)) ir_d2) (IRList.cons IRNode (ir_nd (IRInst.store (IRTy.uint_ 32) ir_d2 ir_d0 Bool.false)) (ir_bd3 (ir_nd1 (IRInst.ptrfromparts (IRTy.fatptr_ (IRTy.uint_ 8)) (IRTy.uint_ 64) ir_d2 ir_d1) ir_d3) (ir_nd1 (IRInst.ptrmetadata (IRTy.fatptr_ (IRTy.uint_ 8)) (IRTy.uint_ 64) ir_d3) ir_d4) (ir_nd (IRInst.ret (ir_nl1 ir_d4))))))";

const SRC_IR_W2B_PM_FUNC: &str = "def ir_w2b_pm_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_w2b_pm_b0 ir_blk0)";

const SRC_IR_W2B_PM_MODULE: &str = "def ir_w2b_pm_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_w2b_pm_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

/// The `ptrmetadata` micro-module's definitions, in registration order.
#[must_use]
pub fn ir_w2b_pm_module_defs() -> &'static [&'static str] {
    &[SRC_IR_W2B_PM_B0, SRC_IR_W2B_PM_FUNC, SRC_IR_W2B_PM_MODULE]
}

const SRC_IR_W2B_PM_ON_LEN: &str = "def ir_w2b_pm_on_len (x : Nat) (n : Nat) : Eq IROutcome (ir_eval ir_d8 ir_w2b_pm_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ x) (IRList.cons IRScalar (IRScalar.int_ n) (IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ n))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ n)))";

const SRC_IR_W2B_PM_THIN: &str = "def ir_w2b_pm_thin (mt : IRTy) (a : Nat) : Eq IRStepResult (ir_ptrmeta_eval mt (IRScalar.ptr_ a)) (IRStepResult.value IRScalar.unit_) := Eq.refl IRStepResult (IRStepResult.value IRScalar.unit_)";

const SRC_IR_W2B_PM_NOT_PTR: &str = "def ir_w2b_pm_not_ptr (mt : IRTy) (n : Nat) : Eq IRStepResult (ir_ptrmeta_eval mt (IRScalar.int_ n)) (IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_ptr))";

// ── ptrfromparts: thin and fat rebuilds, each observed through a deref ────
//
//   bb0(%0: u32, %1: u64, %2: (), %3: bool):
//     %4 = alloca u32; store u32 %0, ptr %4; condbr %3, bb1, bb2
//   bb1: %5 = ptr_from_parts ptr ptr %4, () %2; %6 = load u32, ptr %5; ret %6
//   bb2: %7 = ptr_from_parts fatptr<str> ptr %4, u64 %1;
//        %8 = ptr_data fatptr<str> %7; %9 = load u32, ptr %8; ret %9

const SRC_IR_W2B_PP_B0: &str = "def ir_w2b_pp_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.alloca (IRTy.uint_ 32) (IROption.none Nat)) ir_d4) (ir_nd (IRInst.store (IRTy.uint_ 32) ir_d4 ir_d0 Bool.false)) (ir_nd (IRInst.condbr ir_d3 ir_d1 ir_nl0 ir_d2 ir_nl0)))";

const SRC_IR_W2B_PP_B1: &str = "def ir_w2b_pp_b1 : IRBlock := IRBlock.mk ir_d1 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.ptrfromparts IRTy.ptr_ IRTy.unit_ ir_d4 ir_d2) ir_d5) (ir_nd1 (IRInst.load (IRTy.uint_ 32) ir_d5 Bool.false) ir_d6) (ir_nd (IRInst.ret (ir_nl1 ir_d6))))";

const SRC_IR_W2B_PP_B2: &str = "def ir_w2b_pp_b2 : IRBlock := IRBlock.mk ir_d2 ir_nl0 (IRList.cons IRNode (ir_nd1 (IRInst.ptrfromparts (IRTy.fatptr_ (IRTy.uint_ 8)) (IRTy.uint_ 64) ir_d4 ir_d1) ir_d7) (ir_bd3 (ir_nd1 (IRInst.ptrdata (IRTy.fatptr_ (IRTy.uint_ 8)) ir_d7) ir_d8) (ir_nd1 (IRInst.load (IRTy.uint_ 32) ir_d8 Bool.false) ir_d9) (ir_nd (IRInst.ret (ir_nl1 ir_d9)))))";

const SRC_IR_W2B_PP_FUNC: &str = "def ir_w2b_pp_func : IRFunc := IRFunc.mk ir_d0 (IRList.cons Nat ir_d0 (IRList.cons Nat ir_d1 (IRList.cons Nat ir_d2 (IRList.cons Nat ir_d3 (IRList.nil Nat))))) ir_d0 (ir_blk ir_w2b_pp_b0 (ir_blk ir_w2b_pp_b1 (ir_blk ir_w2b_pp_b2 ir_blk0)))";

const SRC_IR_W2B_PP_MODULE: &str = "def ir_w2b_pp_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_w2b_pp_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

/// The `ptrfromparts` micro-module's definitions, in registration order.
#[must_use]
pub fn ir_w2b_pp_module_defs() -> &'static [&'static str] {
    &[
        SRC_IR_W2B_PP_B0,
        SRC_IR_W2B_PP_B1,
        SRC_IR_W2B_PP_B2,
        SRC_IR_W2B_PP_FUNC,
        SRC_IR_W2B_PP_MODULE,
    ]
}

const SRC_IR_W2B_PP_ON_THIN: &str = "def ir_w2b_pp_on_thin (x : Nat) (n : Nat) : Eq IROutcome (ir_eval ir_d8 ir_w2b_pp_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ x) (IRList.cons IRScalar (IRScalar.int_ n) (IRList.cons IRScalar IRScalar.unit_ (IRList.cons IRScalar (IRScalar.bool_ Bool.true) (IRList.nil IRScalar))))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ x))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ x)))";

const SRC_IR_W2B_PP_ON_FAT: &str = "def ir_w2b_pp_on_fat (x : Nat) (n : Nat) : Eq IROutcome (ir_eval ir_d8 ir_w2b_pp_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ x) (IRList.cons IRScalar (IRScalar.int_ n) (IRList.cons IRScalar IRScalar.unit_ (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.nil IRScalar))))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ x))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ x)))";

const SRC_IR_W2B_PP_VTABLE: &str = "def ir_w2b_pp_vtable (a : Nat) (x : Nat) : Eq IRStepResult (ir_ptrparts_at a (IRScalar.ptr_ x)) (IRStepResult.value (IRScalar.fat_ a x)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.fat_ a x))";

const SRC_IR_W2B_PP_FNPTR: &str = "def ir_w2b_pp_fnptr (a : Nat) (f : Nat) : Eq IRStepResult (ir_ptrparts_at a (IRScalar.fnptr_ f)) (IRStepResult.value (IRScalar.fat_ a f)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.fat_ a f))";

const SRC_IR_W2B_PP_BAD_MD: &str = "def ir_w2b_pp_bad_md (a : Nat) (b : Bool) : Eq IRStepResult (ir_ptrparts_at a (IRScalar.bool_ b)) (IRStepResult.fault (IROutcome.type_error IRFault.not_int)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_int))";

const SRC_IR_W2B_PP_NULL_DATA: &str = "def ir_w2b_pp_null_data (md : IRScalar) : Eq IRStepResult (ir_ptrparts_eval IRScalar.nullptr_ md) (IRStepResult.fault (IROutcome.ub IRFault.null_deref)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.ub IRFault.null_deref))";

impl Specification {
    /// The W2b synthetic micro-modules (memory tranche) and their
    /// kernel-executed witnesses.
    ///
    /// Reuses (all from `add_eval_ir`): the `IRInst`/`IRBlock`/`IRFunc`/
    /// `IRModule` syntax, the `ir_d0..ir_d16` numerals, the `ir_nd`/`ir_nd1`/
    /// `ir_bd1..3`/`ir_blk`/`ir_blk0`/`ir_nl0..2`/`ir_vl1` builders,
    /// `ir_mem0`, the memory lane (`ir_ptrdata_eval`/`ir_ptrmeta_eval`/
    /// `ir_ptrparts_at`/`ir_ptrparts_eval`, `IRStepResult`) and the machine
    /// (`ir_eval`, `IROutcome`, `IRFault`). Deliberately nothing from any
    /// chain stage, so the battery can register the module lines standalone
    /// into the minimal `EvalIr` bundle spec.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check — for the witnesses, that means the kernel RAN the machine
    /// and got a different outcome, which is a red to report, never to tune.
    pub(super) fn add_eval_ir_w2b_synth(&mut self) -> Result<(), SpecError> {
        for (line, doc) in [
            (SRC_IR_W2B_AL_B0, "ir_w2b_al_b0: SYNTHETIC micro-module entry (W2b alloca): allocate one fresh u32 cell at %2, then condbr on %1 between the initialized round-trip (bb1) and the uninitialized read (bb2). Count is IROption.none — trust-ir's 'absent means one'. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_AL_B1, "ir_w2b_al_b1: the initialized arm — store %0 through the fresh pointer, load it back, return it: the smallest observation that the allocation is real, writable and readable. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_AL_B2, "ir_w2b_al_b2: the uninitialized arm — load the fresh cell WITHOUT a store. ir_alloc_cells fills new cells with undef_, and ir_load_value on undef_ is `ub uninit`, so this arm is the fresh-cell UB edge. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_AL_FUNC, "ir_w2b_al_func: two parameters (value, selector at SSA ids 0,1), entry block 0, three blocks. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_AL_MODULE, "ir_w2b_al_module: the SYNTHETIC alloca module — authored for the W2b differential (E2 twin tests/fixtures/synth/synth_alloca.trust-ir.txt); no producer emitted it and no lineage gate applies. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_AL_ON_STORE, "ir_w2b_al_on_store: the initialized round-trip returns the stored value, for EVERY value — alloca/store/load transport without arithmetic, so the witness is universally quantified rather than a spot check. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_AL_ON_UNINIT, "ir_w2b_al_on_uninit: FAULT EDGE — reading the fresh cell without a store is `ub uninit` AT THE LOAD, at every (never-consulted) value argument. MEASURED FAULT-SITE SPLIT, recorded where the verdict lives: the reference interpreter's plain load of uninitialized bytes yields inert PartialBytes poison and faults undefined_behavior only when the value is INSPECTED — here at the ret signature check (reject_partial, interpret.rs:5402-5403, trust-ir a4e81b6). Same input, same UB verdict, different trace step; the battery compares the row at outcome class and carries this note. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_AL_NONBOOL, "ir_w2b_al_nonbool: FAULT EDGE — an integer in the selector slot is `type_error not_bool` at every pair of values (ir_condbr_exec), pinned so the uninit UB verdict cannot be confused with a selector type error. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PD_B0, "ir_w2b_pd_b0: SYNTHETIC micro-module block (W2b ptrdata). Alloca+store prepare a written cell; ptr_data projects the THIN data lane (identity on a thin pointer, ir_ptrdata_eval); the load through the PROJECTED pointer is what makes the identity observable rather than asserted. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PD_FUNC, "ir_w2b_pd_func: one u32 parameter (SSA id 0), entry block 0, one block. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PD_MODULE, "ir_w2b_pd_module: the SYNTHETIC ptrdata module (E2 twin tests/fixtures/synth/synth_ptrdata.trust-ir.txt). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PD_ON_ROUNDTRIP, "ir_w2b_pd_on_roundtrip: store x; load through ptr_data(ptr) returns x, for every x — the thin data lane preserves the address it projects. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PD_FAT, "ir_w2b_pd_fat: the FAT arm, value-level — ptr_data on fat_ d md is the thin pointer to d, at every data address and metadata word (the arm the ptrfromparts chain's fat path executes whole-program). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PD_NULL, "ir_w2b_pd_null: ptr_data on the null pointer is the null pointer — provenance-preserving identity, not a deref, so no UB here; the UB belongs to whoever dereferences it. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PD_NOT_PTR, "ir_w2b_pd_not_ptr: FAULT EDGE — ptr_data on an integer is `type_error not_ptr` at every value. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PM_B0, "ir_w2b_pm_b0: SYNTHETIC micro-module block (W2b ptrmetadata). Rebuild a str-shaped fat pointer from the fresh cell's address and the u64 length %1 (ptrfromparts), then project the metadata lane back (ptrmetadata) and return it — the length round-trip both executors can compare as an integer. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PM_FUNC, "ir_w2b_pm_func: two parameters (stored value, length at SSA ids 0,1), entry block 0, one block. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PM_MODULE, "ir_w2b_pm_module: the SYNTHETIC ptrmetadata module (E2 twin tests/fixtures/synth/synth_ptrmetadata.trust-ir.txt, whose fat shape is fatptr<str>: canonical metadata u64 at the pinned 64-bit target, so no element type table is needed). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PM_ON_LEN, "ir_w2b_pm_on_len: the metadata lane returns exactly the length the fat pointer was rebuilt with, for EVERY stored value and every length — both are transported, never computed on. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PM_THIN, "ir_w2b_pm_thin: the THIN arm, value-level — ptr_metadata of a thin pointer is unit_, at every address. Kernel-witnessed here rather than in the battery: a ret-of-unit row has no shared integer vocabulary, and the fat arm already measures the constructor whole-program. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PM_NOT_PTR, "ir_w2b_pm_not_ptr: FAULT EDGE — ptr_metadata on an integer is `type_error not_ptr` at every value. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PP_B0, "ir_w2b_pp_b0: SYNTHETIC micro-module entry (W2b ptrfromparts): alloca+store prepare a written cell, condbr on %3 selects which rebuild arm to observe. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PP_B1, "ir_w2b_pp_b1: the THIN rebuild — ptr_from_parts with unit metadata rebuilds a thin pointer (ir_ptrparts_at's unit_ arm), observed by loading the stored value through the REBUILT pointer. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PP_B2, "ir_w2b_pp_b2: the FAT rebuild — ptr_from_parts with an integer length rebuilds fat_ (the slice/str arm), then ptr_data projects the data lane and the load observes it: the whole-program execution of ir_w2b_pd_fat. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PP_FUNC, "ir_w2b_pp_func: four parameters (value, length, unit metadata, selector at SSA ids 0-3), entry block 0, three blocks. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PP_MODULE, "ir_w2b_pp_module: the SYNTHETIC ptrfromparts module (E2 twin tests/fixtures/synth/synth_ptrfromparts.trust-ir.txt). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PP_ON_THIN, "ir_w2b_pp_on_thin: the thin rebuild dereferences to the stored value, for every value and every (unused-on-this-path) length. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PP_ON_FAT, "ir_w2b_pp_on_fat: the fat rebuild's data lane dereferences to the stored value, for every value and every length — with ir_w2b_pm_on_len this pins that a rebuilt fat pointer carries BOTH lanes intact. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PP_VTABLE, "ir_w2b_pp_vtable: the TRAIT-OBJECT rebuild arm, value-level — pointer metadata rebuilds fat_ a x, at every address pair. fat_ carries md : Nat; since crystal E5 ir_ptrmeta_eval reads it back at the declared metadata type (ptr_ x at IRTy.ptr_, ir_e5_ptrmeta_mt_is_read), where it used to return int_ x at every type -- the reason the battery measures the metadata lane on the slice/str shape only (module doc). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PP_FNPTR, "ir_w2b_pp_fnptr: the FNPTR-metadata rebuild arm, value-level — function-pointer metadata rebuilds fat_ a f (vtable-as-fnptr shape), at every pair. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PP_BAD_MD, "ir_w2b_pp_bad_md: FAULT EDGE — a boolean in the metadata slot is `type_error not_int` at every address (ir_ptrparts_at rejects every non-metadata scalar shape). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2B_PP_NULL_DATA, "ir_w2b_pp_null_data: FAULT EDGE — a null data lane is `ub null_deref` at EVERY metadata value, universally quantified over the whole IRScalar family: the match decides on the data operand alone, so the metadata is never inspected. DerivedProved, zero axiom_deps."),
        ] {
            self.add_recursive_def(line, doc)?;
        }
        Ok(())
    }
}
