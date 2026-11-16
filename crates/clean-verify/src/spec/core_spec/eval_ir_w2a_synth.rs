// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **W2a — the synthetic micro-module lane's five constructors: `select`,
//! `undef`, `unreachable`, `extractelement`, `unop` (not_/ctpop).**
//!
//! Plan: `docs/analysis/evalir-completion-plan-2026-08-24.md` §5 W2a. These
//! five `IRInst` constructors have REAL dispatch arms (`ir_exec`,
//! `eval_ir_machine.rs`) but no committed emitted body exercises them, so the
//! semdiff battery could not measure them (W1 stopped at the nine
//! fixture-covered constructors). This stage authors one MICRO-MODULE per
//! constructor — the `ir_lzm` hand-model idiom (`eval_ir_crystal.rs`), each a
//! one-to-three-block function whose only interesting instruction is the
//! constructor under measure — plus kernel-executed `ir_w2a_*_on_*` witnesses
//! including the fault edges. The synthetic `.trust-ir.txt` twins live at
//! `tests/fixtures/synth_*.trust-ir.txt` and the `Synthetic`-labeled battery
//! rows in `tests/crystal_a3_semdiff/synth_chains.rs`; the battery re-reads
//! this stage's module lines through the `ir_w2a_*_module_defs` re-exports, so
//! the differential cannot drift from the modules the specification carries.
//!
//! ## What a synthetic module is, and is not
//!
//! These modules are AUTHORED FOR THE MEASUREMENT. No producer emitted them,
//! no shipped function corresponds to them (E3 absent by construction), and no
//! mint/lineage gate applies — there is no artifact for one to be about. What
//! they establish is per-constructor: the registered semantics computes what
//! the reference interpreter computes on the same text, on a small closed
//! input set, with every fault edge witnessed. That is measurement width for
//! B-SEM §4(b), not a lineage claim.
//!
//! ## Design constraints that shaped the modules (measured, not preferences)
//!
//! * **`unop` runs at width 8.** `ir_nat_bitnot w x` materializes
//!   `2^w - 1 - x`, and `ir_nat_ctpop` then walks that VALUE's unary
//!   magnitude through fuelled division (`ir_nat_ctpop_go`/`ir_nat_div`,
//!   `eval_ir_state.rs`). At width 32 a complement is ~4.29e9, the same
//!   unary-walk wall the bvar_in_range chain measured at five days; at width 8
//!   it is ≤ 255, which the kernel walks instantly. The width is the module's,
//!   chosen so the composition `ctpop(not x)` is exactly computable — the
//!   committed `ir_exact_integer_not`/`ir_exact_integer_ctpop` vectors made
//!   the same choice at width 4.
//! * **`select` and `extractelement` do no arithmetic.** Both transport
//!   already-materialized scalars, so their witnesses hold with the payload
//!   values UNIVERSALLY QUANTIFIED — `ir_w2a_sel_on_true` is a theorem over
//!   every pair of Nats, not a spot check (the `ir_is_zero_on_param` idiom).
//! * **`undef`'s module RETURNS the undef value.** Clean's arm binds
//!   `IRScalar.undef_` and continues; returning it is the sharpest statement
//!   of that arm. The reference interpreter instead refuses to execute
//!   `Inst::Undef` at all (`interpret.rs:619-623`, `undefined_behavior`,
//!   "executing undef would read an undefined value") — a measured executor
//!   divergence the battery records as a declared delta, not a silent one.
//! * **`unreachable` is measured on both edges.** The taken edge is the whole
//!   semantics (`ub unreachable`); the untaken edge pins that merely
//!   CONTAINING the instruction is not UB.
//!
//! Everything here is `DerivedProved`, zero axiom_deps: every witness is an
//! `Eq.refl` the kernel discharges by running the machine. Witness fuels are
//! SUFFICIENT, not least — the battery pins each row's least fuel from below
//! (`wide_fuel_out_obligation`); a stage witness's job is the outcome.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ── select: one block, `%3 = select u32 %0, %1, %2; ret %3` ──────────────

const SRC_IR_W2A_SEL_B0: &str = "def ir_w2a_sel_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.select (IRTy.uint_ 32) ir_d0 ir_d1 ir_d2) ir_d3) (ir_nd (IRInst.ret (ir_nl1 ir_d3))))";

const SRC_IR_W2A_SEL_FUNC: &str = "def ir_w2a_sel_func : IRFunc := IRFunc.mk ir_d0 (@IRList.cons Nat ir_d0 (@IRList.cons Nat ir_d1 (@IRList.cons Nat ir_d2 (@IRList.nil Nat)))) ir_d0 (ir_blk ir_w2a_sel_b0 ir_blk0)";

const SRC_IR_W2A_SEL_MODULE: &str = "def ir_w2a_sel_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_w2a_sel_func (@IRList.nil IRFunc)) (@IRList.nil IRGlobal)";

/// The `select` micro-module's definitions, in registration order — the lines
/// the battery registers, re-exported rather than re-typed.
#[must_use]
pub fn ir_w2a_sel_module_defs() -> &'static [&'static str] {
    &[
        SRC_IR_W2A_SEL_B0,
        SRC_IR_W2A_SEL_FUNC,
        SRC_IR_W2A_SEL_MODULE,
    ]
}

const SRC_IR_W2A_SEL_ON_TRUE: &str = "def ir_w2a_sel_on_true (a : Nat) (b : Nat) : @Eq IROutcome (ir_eval ir_d4 ir_w2a_sel_module ir_d0 (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.cons IRScalar (IRScalar.int_ a) (@IRList.cons IRScalar (IRScalar.int_ b) (@IRList.nil IRScalar)))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ a))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ a)))";

const SRC_IR_W2A_SEL_ON_FALSE: &str = "def ir_w2a_sel_on_false (a : Nat) (b : Nat) : @Eq IROutcome (ir_eval ir_d4 ir_w2a_sel_module ir_d0 (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.cons IRScalar (IRScalar.int_ a) (@IRList.cons IRScalar (IRScalar.int_ b) (@IRList.nil IRScalar)))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ b))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ b)))";

const SRC_IR_W2A_SEL_NONBOOL: &str = "def ir_w2a_sel_nonbool (c : Nat) (a : Nat) (b : Nat) : @Eq IROutcome (ir_eval ir_d4 ir_w2a_sel_module ir_d0 (@IRList.cons IRScalar (IRScalar.int_ c) (@IRList.cons IRScalar (IRScalar.int_ a) (@IRList.cons IRScalar (IRScalar.int_ b) (@IRList.nil IRScalar)))) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_bool) := @Eq.refl IROutcome (IROutcome.type_error IRFault.not_bool)";

// ── undef: one block, `%0 = undef u32; ret %0` ───────────────────────────

const SRC_IR_W2A_UD_B0: &str = "def ir_w2a_ud_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.undef (IRTy.uint_ 32)) ir_d0) (ir_nd (IRInst.ret (ir_nl1 ir_d0))))";

const SRC_IR_W2A_UD_FUNC: &str =
    "def ir_w2a_ud_func : IRFunc := IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk ir_w2a_ud_b0 ir_blk0)";

const SRC_IR_W2A_UD_MODULE: &str = "def ir_w2a_ud_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_w2a_ud_func (@IRList.nil IRFunc)) (@IRList.nil IRGlobal)";

/// The `undef` micro-module's definitions, in registration order.
#[must_use]
pub fn ir_w2a_ud_module_defs() -> &'static [&'static str] {
    &[SRC_IR_W2A_UD_B0, SRC_IR_W2A_UD_FUNC, SRC_IR_W2A_UD_MODULE]
}

const SRC_IR_W2A_UD_ON_RUN: &str = "def ir_w2a_ud_on_run : @Eq IROutcome (ir_eval ir_d4 ir_w2a_ud_module ir_d0 (@IRList.nil IRScalar) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 IRScalar.undef_)) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 IRScalar.undef_))";

// ── unreachable: condbr to a returning arm or the unreachable arm ────────

const SRC_IR_W2A_UR_B0: &str = "def ir_w2a_ur_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd1 (ir_nd (IRInst.condbr ir_d0 ir_d1 ir_nl0 ir_d2 ir_nl0)))";

const SRC_IR_W2A_UR_B1: &str = "def ir_w2a_ur_b1 : IRBlock := IRBlock.mk ir_d1 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ (IRTy.uint_ 32) (IRConst.int_ 3)) ir_d1) (ir_nd (IRInst.ret (ir_nl1 ir_d1))))";

const SRC_IR_W2A_UR_B2: &str =
    "def ir_w2a_ur_b2 : IRBlock := IRBlock.mk ir_d2 ir_nl0 (ir_bd1 (ir_nd IRInst.unreachable))";

const SRC_IR_W2A_UR_FUNC: &str = "def ir_w2a_ur_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_w2a_ur_b0 (ir_blk ir_w2a_ur_b1 (ir_blk ir_w2a_ur_b2 ir_blk0)))";

const SRC_IR_W2A_UR_MODULE: &str = "def ir_w2a_ur_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_w2a_ur_func (@IRList.nil IRFunc)) (@IRList.nil IRGlobal)";

/// The `unreachable` micro-module's definitions, in registration order.
#[must_use]
pub fn ir_w2a_ur_module_defs() -> &'static [&'static str] {
    &[
        SRC_IR_W2A_UR_B0,
        SRC_IR_W2A_UR_B1,
        SRC_IR_W2A_UR_B2,
        SRC_IR_W2A_UR_FUNC,
        SRC_IR_W2A_UR_MODULE,
    ]
}

const SRC_IR_W2A_UR_ON_TRUE: &str = "def ir_w2a_ur_on_true : @Eq IROutcome (ir_eval ir_d4 ir_w2a_ur_module ir_d0 (ir_vl1 (IRScalar.bool_ Bool.true)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d3))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d3)))";

const SRC_IR_W2A_UR_ON_FALSE: &str = "def ir_w2a_ur_on_false : @Eq IROutcome (ir_eval ir_d4 ir_w2a_ur_module ir_d0 (ir_vl1 (IRScalar.bool_ Bool.false)) ir_mem0 ir_d0) (IROutcome.ub IRFault.unreachable) := @Eq.refl IROutcome (IROutcome.ub IRFault.unreachable)";

const SRC_IR_W2A_UR_NONBOOL: &str = "def ir_w2a_ur_nonbool (n : Nat) : @Eq IROutcome (ir_eval ir_d4 ir_w2a_ur_module ir_d0 (ir_vl1 (IRScalar.int_ n)) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_bool) := @Eq.refl IROutcome (IROutcome.type_error IRFault.not_bool)";

// ── extractelement: `%2 = extractelement u32 %0, %1; ret %2` ─────────────

const SRC_IR_W2A_EE_B0: &str = "def ir_w2a_ee_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.extractelement (IRTy.uint_ 32) ir_d0 ir_d1) ir_d2) (ir_nd (IRInst.ret (ir_nl1 ir_d2))))";

const SRC_IR_W2A_EE_FUNC: &str = "def ir_w2a_ee_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_w2a_ee_b0 ir_blk0)";

const SRC_IR_W2A_EE_MODULE: &str = "def ir_w2a_ee_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_w2a_ee_func (@IRList.nil IRFunc)) (@IRList.nil IRGlobal)";

/// The `extractelement` micro-module's definitions, in registration order.
#[must_use]
pub fn ir_w2a_ee_module_defs() -> &'static [&'static str] {
    &[SRC_IR_W2A_EE_B0, SRC_IR_W2A_EE_FUNC, SRC_IR_W2A_EE_MODULE]
}

const SRC_IR_W2A_EE_AT0: &str = "def ir_w2a_ee_at0 (x : Nat) (y : Nat) (z : Nat) : @Eq IROutcome (ir_eval ir_d4 ir_w2a_ee_module ir_d0 (@IRList.cons IRScalar (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ x) (IRScalar.vcons (IRScalar.int_ y) (IRScalar.vcons (IRScalar.int_ z) IRScalar.vnil)))) (@IRList.cons IRScalar (IRScalar.int_ ir_d0) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ x))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ x)))";

const SRC_IR_W2A_EE_AT1: &str = "def ir_w2a_ee_at1 (x : Nat) (y : Nat) (z : Nat) : @Eq IROutcome (ir_eval ir_d4 ir_w2a_ee_module ir_d0 (@IRList.cons IRScalar (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ x) (IRScalar.vcons (IRScalar.int_ y) (IRScalar.vcons (IRScalar.int_ z) IRScalar.vnil)))) (@IRList.cons IRScalar (IRScalar.int_ ir_d1) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ y))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ y)))";

const SRC_IR_W2A_EE_AT2: &str = "def ir_w2a_ee_at2 (x : Nat) (y : Nat) (z : Nat) : @Eq IROutcome (ir_eval ir_d4 ir_w2a_ee_module ir_d0 (@IRList.cons IRScalar (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ x) (IRScalar.vcons (IRScalar.int_ y) (IRScalar.vcons (IRScalar.int_ z) IRScalar.vnil)))) (@IRList.cons IRScalar (IRScalar.int_ ir_d2) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ z))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ z)))";

const SRC_IR_W2A_EE_OOB: &str = "def ir_w2a_ee_oob (x : Nat) (y : Nat) (z : Nat) : @Eq IROutcome (ir_eval ir_d4 ir_w2a_ee_module ir_d0 (@IRList.cons IRScalar (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ x) (IRScalar.vcons (IRScalar.int_ y) (IRScalar.vcons (IRScalar.int_ z) IRScalar.vnil)))) (@IRList.cons IRScalar (IRScalar.int_ ir_d3) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.type_error IRFault.bad_field) := @Eq.refl IROutcome (IROutcome.type_error IRFault.bad_field)";

const SRC_IR_W2A_EE_NOT_AGG: &str = "def ir_w2a_ee_not_agg (n : Nat) (k : Nat) : @Eq IROutcome (ir_eval ir_d4 ir_w2a_ee_module ir_d0 (@IRList.cons IRScalar (IRScalar.int_ n) (@IRList.cons IRScalar (IRScalar.int_ k) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_agg) := @Eq.refl IROutcome (IROutcome.type_error IRFault.not_agg)";

const SRC_IR_W2A_EE_NOT_INT: &str = "def ir_w2a_ee_not_int (x : Nat) : @Eq IROutcome (ir_eval ir_d4 ir_w2a_ee_module ir_d0 (@IRList.cons IRScalar (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ x) IRScalar.vnil)) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_int) := @Eq.refl IROutcome (IROutcome.type_error IRFault.not_int)";

// ── unop: `%1 = not u8 %0; %2 = ctpop u8 %1; ret %2` ─────────────────────

const SRC_IR_W2A_UO_B0: &str = "def ir_w2a_uo_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.unop IRUnOp.not_ (IRTy.uint_ 8) ir_d0) ir_d1) (ir_nd1 (IRInst.unop IRUnOp.ctpop (IRTy.uint_ 8) ir_d1) ir_d2) (ir_nd (IRInst.ret (ir_nl1 ir_d2))))";

const SRC_IR_W2A_UO_FUNC: &str = "def ir_w2a_uo_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_w2a_uo_b0 ir_blk0)";

const SRC_IR_W2A_UO_MODULE: &str = "def ir_w2a_uo_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_w2a_uo_func (@IRList.nil IRFunc)) (@IRList.nil IRGlobal)";

/// The `unop` micro-module's definitions, in registration order.
#[must_use]
pub fn ir_w2a_uo_module_defs() -> &'static [&'static str] {
    &[SRC_IR_W2A_UO_B0, SRC_IR_W2A_UO_FUNC, SRC_IR_W2A_UO_MODULE]
}

const SRC_IR_W2A_UO_ON_ZERO: &str = "def ir_w2a_uo_on_zero : @Eq IROutcome (ir_eval ir_d4 ir_w2a_uo_module ir_d0 (ir_vl1 (IRScalar.int_ ir_d0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d8))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d8)))";

const SRC_IR_W2A_UO_ON_FF: &str = "def ir_w2a_uo_on_ff : @Eq IROutcome (ir_eval ir_d4 ir_w2a_uo_module ir_d0 (ir_vl1 (IRScalar.int_ 255)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d0))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d0)))";

const SRC_IR_W2A_UO_ON_AA: &str = "def ir_w2a_uo_on_aa : @Eq IROutcome (ir_eval ir_d4 ir_w2a_uo_module ir_d0 (ir_vl1 (IRScalar.int_ 170)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d4))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d4)))";

const SRC_IR_W2A_UO_NOT_INT: &str = "def ir_w2a_uo_not_int : @Eq IROutcome (ir_eval ir_d4 ir_w2a_uo_module ir_d0 (ir_vl1 (IRScalar.bool_ Bool.true)) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_int) := @Eq.refl IROutcome (IROutcome.type_error IRFault.not_int)";

impl Specification {
    /// The W2a synthetic micro-modules and their kernel-executed witnesses.
    ///
    /// Reuses (all from `add_eval_ir`): the `IRInst`/`IRBlock`/`IRFunc`/
    /// `IRModule` syntax, the `ir_d0..ir_d16` numerals, the `ir_nd`/`ir_nd1`/
    /// `ir_bd1..3`/`ir_blk`/`ir_blk0`/`ir_nl0..2`/`ir_vl1` builders,
    /// `ir_mem0`, and the machine (`ir_eval`, `IROutcome`, `IRFault`).
    /// Deliberately nothing from any chain stage, so the battery can register
    /// the module lines standalone into the minimal `EvalIr` bundle spec.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check — for the witnesses, that means the kernel RAN the machine
    /// and got a different outcome, which is a red to report, never to tune.
    pub(super) fn add_eval_ir_w2a_synth(&mut self) -> Result<(), SpecError> {
        for (line, doc) in [
            (SRC_IR_W2A_SEL_B0, "ir_w2a_sel_b0: SYNTHETIC micro-module block (W2a select). One select node binding %3 from condition %0 and arms %1/%2, then ret — the smallest body whose only value-producing instruction is the constructor under measure. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_SEL_FUNC, "ir_w2a_sel_func: three parameters (cond, then-val, else-val at SSA ids 0,1,2), entry block 0, one block. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_SEL_MODULE, "ir_w2a_sel_module: the SYNTHETIC select module — authored for the W2a differential (its committed E2 twin is tests/fixtures/synth_select.trust-ir.txt); no producer emitted it and no lineage gate applies. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_SEL_ON_TRUE, "ir_w2a_sel_on_true: select on a TRUE condition returns the then-arm, for EVERY pair of integer arms — select transports scalars without arithmetic, so the witness is universally quantified rather than a spot check. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_SEL_ON_FALSE, "ir_w2a_sel_on_false: select on a FALSE condition returns the else-arm, for every pair of arms. Bool.rec minor order is (false, true) in ir_select_eval; these two witnesses pin that the arms are not swapped. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_SEL_NONBOOL, "ir_w2a_sel_nonbool: FAULT EDGE — an integer in the condition slot is `type_error not_bool` at every payload, matching the interpreter's type_error on the same shape (eval_select, interpret.rs). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UD_B0, "ir_w2a_ud_b0: SYNTHETIC micro-module block (W2a undef). Bind an undef u32 at %0 and RETURN it — returning the value is the sharpest statement of the dispatch arm, which binds IRScalar.undef_ and continues. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UD_FUNC, "ir_w2a_ud_func: no parameters, entry block 0, one block. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UD_MODULE, "ir_w2a_ud_module: the SYNTHETIC undef module (E2 twin tests/fixtures/synth_undef.trust-ir.txt). MEASURED EXECUTOR DIVERGENCE, recorded where the module lives: trust-ir's reference interpreter refuses to EXECUTE Inst::Undef (undefined_behavior, interpret.rs:619-623) where this machine binds undef_ and returns it — the battery records that delta per row, never as agreement. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UD_ON_RUN, "ir_w2a_ud_on_run: the machine RUNS the undef arm and returns `ret [undef_]` — the whole-program witness that the arm binds rather than faults. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UR_B0, "ir_w2a_ur_b0: SYNTHETIC micro-module entry (W2a unreachable): condbr to the returning arm (bb1) or the unreachable arm (bb2). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UR_B1, "ir_w2a_ur_b1: the untaken-edge control — materialize 3 and return it, so the witness on TRUE pins that merely containing `unreachable` is not UB. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UR_B2, "ir_w2a_ur_b2: the unreachable arm — the constructor under measure IS this block's only node, the ir_lzm_b6 idiom as a subject instead of a default edge. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UR_FUNC, "ir_w2a_ur_func: one boolean parameter (SSA id 0), entry block 0, three blocks. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UR_MODULE, "ir_w2a_ur_module: the SYNTHETIC unreachable module (E2 twin tests/fixtures/synth_unreachable.trust-ir.txt). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UR_ON_TRUE, "ir_w2a_ur_on_true: the returning edge returns 3 — the negative control for the UB edge. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UR_ON_FALSE, "ir_w2a_ur_on_false: *** THE CONSTRUCTOR'S WHOLE SEMANTICS: executing unreachable is `ub IRFault.unreachable`. *** The interpreter agrees at outcome class (undefined_behavior, 'executed unreachable', interpret.rs:996-1000) — the one W2a fault edge where both executors' vocabularies genuinely align. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UR_NONBOOL, "ir_w2a_ur_nonbool: FAULT EDGE — a non-boolean condbr selector is `type_error not_bool` at every value (ir_condbr_exec), pinned so the UB verdict above cannot be confused with a selector type error. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_EE_B0, "ir_w2a_ee_b0: SYNTHETIC micro-module block (W2a extractelement). One computed-index element read binding %2 from container %0 at index %1, then ret. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_EE_FUNC, "ir_w2a_ee_func: two parameters (the aggregate and the index at SSA ids 0,1), entry block 0, one block. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_EE_MODULE, "ir_w2a_ee_module: the SYNTHETIC extractelement module (E2 twin tests/fixtures/synth_extractelement.trust-ir.txt, which carries the container as a three-field struct — under the inline-spine encoding an element read IS a field read at the computed index, per ir_extract_elem's own doc). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_EE_AT0, "ir_w2a_ee_at0: index 0 reads the first element, for EVERY element triple — extractelement transports without arithmetic, so the witness is universally quantified. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_EE_AT1, "ir_w2a_ee_at1: index 1 reads the second element, for every triple. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_EE_AT2, "ir_w2a_ee_at2: index 2 reads the last element, for every triple — with at0/at1 this pins the index-to-slot map across the whole container. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_EE_OOB, "ir_w2a_ee_oob: FAULT EDGE — index 3 on a three-element container is `type_error bad_field`, at every triple. MEASURED CLASS DIVERGENCE, recorded here where the verdict lives: the interpreter reports the same read as undefined_behavior ('element 3 is out of bounds', eval_extract_element, interpret.rs:4507-4516) — Clean's fail-closed choice and trust-ir's UB choice differ by outcome CLASS, and the battery carries that as a declared delta row rather than mapping one class onto the other. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_EE_NOT_AGG, "ir_w2a_ee_not_agg: FAULT EDGE — a scalar in the container slot is `type_error not_agg` at every index; the interpreter agrees at class (type_error, 'extract_element requires vector/array/sequence'). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_EE_NOT_INT, "ir_w2a_ee_not_int: FAULT EDGE — a boolean in the index slot is `type_error not_int`, decided BEFORE the container is examined (ir_extract_elem runs ir_as_int first); the interpreter agrees at class (runtime_index's type_error). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UO_B0, "ir_w2a_uo_b0: SYNTHETIC micro-module block (W2a unop). not_ then ctpop CHAINED at width 8, so one body measures both integer unary operators and the second consumes the first's output. Width 8 is a measured cost bound, not a preference: ir_nat_ctpop walks its operand's unary magnitude, and a width-32 complement is a ~4.29e9-step wall (the bvar_in_range five-day class) where a width-8 one is ≤ 255. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UO_FUNC, "ir_w2a_uo_func: one u8 parameter (SSA id 0), entry block 0, one block. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UO_MODULE, "ir_w2a_uo_module: the SYNTHETIC unop module (E2 twin tests/fixtures/synth_unop.trust-ir.txt). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UO_ON_ZERO, "ir_w2a_uo_on_zero: ctpop(not 0) at width 8 is 8 — the all-ones complement, kernel-computed through the exact bit substrate. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UO_ON_FF, "ir_w2a_uo_on_ff: ctpop(not 255) is 0 — the saturated input, entering as the raw literal 255 (the committed concrete-witness encoding for values above the ir_d name pool). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UO_ON_AA, "ir_w2a_uo_on_aa: ctpop(not 0b10101010) is 4 — the alternating pattern, so a complement that dropped or duplicated a bit position would be caught between this and the two edge witnesses. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2A_UO_NOT_INT, "ir_w2a_uo_not_int: FAULT EDGE — a boolean operand to an integer-typed not_ is `type_error not_int` (ir_not_eval's integer arms run ir_int1). DerivedProved, zero axiom_deps."),
        ] {
            self.add_recursive_def(line, doc)?;
        }
        Ok(())
    }
}
