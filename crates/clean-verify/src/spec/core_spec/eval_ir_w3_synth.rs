// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **W3 — the overflow value domain's synthetic micro-modules:** one unsigned
//! (`u8`) and one signed (`i8`) checked-arithmetic body, each running ALL
//! THREE `OverflowOp`s on the same operands and returning every result.
//!
//! Plan: `docs/analysis/evalir-completion-plan-2026-08-24.md` §5 W3. Unlike
//! the W2 tranches, W3 is a VALUE-DOMAIN wave: the `overflow` dispatch arm was
//! the tagged `unmodelled width_bounded` outcome until 2026-08-25, and the
//! same wave that authored these modules gave it real semantics
//! (`ir_overflow_exec`, `eval_ir_machine.rs`; the math in
//! `eval_ir_ops.rs::ir_overflow_value` / `ir_overflow_flag`, each doc citing
//! its trust-ir `a4e81b6` ground truth). Same lane discipline as W2a/W2b/W2c
//! otherwise: authored micro-modules, kernel-executed `ir_w3_*` witnesses
//! including the fault edges, synthetic `.trust-ir.txt` twins under
//! `tests/fixtures/synth/`, `Synthetic`-labeled battery rows
//! (`tests/crystal_a3_semdiff/w3_chains.rs`) reading this stage's module lines
//! through the `ir_w3_*_module_defs` re-exports.
//!
//! ## Why each module is shaped the way it is
//!
//! * **Three ops, one body, six-value `ret`.** An `Overflow` node declares TWO
//!   results — the wrapped value and the Bool flag (trust-ir `a4e81b6`
//!   `interpret.rs:637-644`) — and the honest observation of the two-result
//!   bind is to RETURN both, through the multi-value `ret` the machine already
//!   has (`ir_ret_to`: "a multi-value return needs no packing and loses
//!   nothing" — never battery-measured until this lane). Running add, sub and
//!   mul on the same operands in one body keeps the module count at two while
//!   every row observes all six bound results; no extra instruction stands
//!   between the overflow nodes and the `ret`, so the row IS the bind.
//! * **Signedness is a module split, not a row split.** The overflow FLAG is
//!   the one integer-arithmetic semantics where `int_` vs `uint_` changes the
//!   answer (`ir_overflow_flag`'s doc), so the unsigned and signed lanes are
//!   separate modules with separate E2 twins — same body shape, different
//!   carrier type, and the battery measures both.
//! * **Width 8 is the measured cost bound.** `ir_wrap w n` costs O(n) in the
//!   DIVIDEND (the re-measured residue cost law, `bundles.rs` sixth-chain
//!   comment), and a mul row's dividend is the raw product: at width 8 the
//!   worst battery row is `128 * 255 = 32640` (seconds), where a width-32
//!   product would be the five-day class. Registration-time witnesses stay
//!   under a ~800-step walk by choosing small operands; the expensive MIN×-1
//!   row lives in the battery (big box), not here.
//!
//! ## The polarity coverage (rows in `w3_chains.rs`, witnesses here)
//!
//! Both polarities of every op in both modules: unsigned add overflows on
//! (240,32) and not on (16,16)/(0,1)/(3,2); unsigned sub borrows on (0,1)
//! only; unsigned mul overflows on (16,16)/(240,32); signed add overflows on
//! (96,64) and (-128,-1); signed sub overflows on (-128,1) only; signed mul
//! overflows on (96,64) and (-128)×(-1) — the MIN asymmetry — and not on
//! (-128)×1, the boundary one step inside.
//!
//! Everything here is `DerivedProved`, zero axiom_deps: every witness is an
//! `Eq.refl` the kernel discharges by running the machine or by iota-reducing
//! one evaluator match. Witness fuels are SUFFICIENT, not least — the battery
//! pins each row's least fuel from below. No new inductive and no new
//! relation lands in this wave, so the vacuity firewall's family list is
//! untouched by construction.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ── unsigned lane: u8, all three ops, six-value ret ───────────────────────
//
//   bb0(%0: u8, %1: u8):
//     %2, %3 = add.overflow u8 %0, %1
//     %4, %5 = sub.overflow u8 %0, %1
//     %6, %7 = mul.overflow u8 %0, %1
//     ret %2, %3, %4, %5, %6, %7

const SRC_IR_W3_OU_B0: &str = "def ir_w3_ou_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.overflow IROverflowOp.addoverflow (IRTy.uint_ 8) ir_d0 ir_d1) (ir_nl2 ir_d2 ir_d3)) (ir_bd3 (IRNode.mk (IRInst.overflow IROverflowOp.suboverflow (IRTy.uint_ 8) ir_d0 ir_d1) (ir_nl2 ir_d4 ir_d5)) (IRNode.mk (IRInst.overflow IROverflowOp.muloverflow (IRTy.uint_ 8) ir_d0 ir_d1) (ir_nl2 ir_d6 ir_d7)) (ir_nd (IRInst.ret (IRList.cons Nat ir_d2 (IRList.cons Nat ir_d3 (IRList.cons Nat ir_d4 (IRList.cons Nat ir_d5 (ir_nl2 ir_d6 ir_d7)))))))))";

const SRC_IR_W3_OU_FUNC: &str = "def ir_w3_ou_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_w3_ou_b0 ir_blk0)";

const SRC_IR_W3_OU_MODULE: &str = "def ir_w3_ou_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_w3_ou_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

/// The unsigned (`u8`) overflow micro-module's definitions, in registration
/// order — the lines the battery registers, re-exported rather than re-typed.
#[must_use]
pub fn ir_w3_ou_module_defs() -> &'static [&'static str] {
    &[SRC_IR_W3_OU_B0, SRC_IR_W3_OU_FUNC, SRC_IR_W3_OU_MODULE]
}

// ── signed lane: i8, same body shape ──────────────────────────────────────

const SRC_IR_W3_OS_B0: &str = "def ir_w3_os_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.overflow IROverflowOp.addoverflow (IRTy.int_ 8) ir_d0 ir_d1) (ir_nl2 ir_d2 ir_d3)) (ir_bd3 (IRNode.mk (IRInst.overflow IROverflowOp.suboverflow (IRTy.int_ 8) ir_d0 ir_d1) (ir_nl2 ir_d4 ir_d5)) (IRNode.mk (IRInst.overflow IROverflowOp.muloverflow (IRTy.int_ 8) ir_d0 ir_d1) (ir_nl2 ir_d6 ir_d7)) (ir_nd (IRInst.ret (IRList.cons Nat ir_d2 (IRList.cons Nat ir_d3 (IRList.cons Nat ir_d4 (IRList.cons Nat ir_d5 (ir_nl2 ir_d6 ir_d7)))))))))";

const SRC_IR_W3_OS_FUNC: &str = "def ir_w3_os_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_w3_os_b0 ir_blk0)";

const SRC_IR_W3_OS_MODULE: &str = "def ir_w3_os_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_w3_os_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

/// The signed (`i8`) overflow micro-module's definitions, in registration
/// order.
#[must_use]
pub fn ir_w3_os_module_defs() -> &'static [&'static str] {
    &[SRC_IR_W3_OS_B0, SRC_IR_W3_OS_FUNC, SRC_IR_W3_OS_MODULE]
}

// ── whole-program witnesses (fuel ir_d8 is sufficient; least is 4) ────────

const SRC_IR_W3_OU_ON_SMALL: &str = "def ir_w3_ou_on_small : Eq IROutcome (ir_eval ir_d8 ir_w3_ou_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ ir_d3) (ir_vl1 (IRScalar.int_ ir_d2))) ir_mem0 ir_d0) (IROutcome.ret (IRList.cons IRScalar (IRScalar.int_ ir_d5) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ ir_d1) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ ir_d6) (ir_vl1 (IRScalar.bool_ Bool.false)))))))) := Eq.refl IROutcome (IROutcome.ret (IRList.cons IRScalar (IRScalar.int_ ir_d5) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ ir_d1) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ ir_d6) (ir_vl1 (IRScalar.bool_ Bool.false))))))))";

const SRC_IR_W3_OU_ON_BORROW: &str = "def ir_w3_ou_on_borrow : Eq IROutcome (ir_eval ir_d8 ir_w3_ou_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ ir_d0) (ir_vl1 (IRScalar.int_ ir_d1))) ir_mem0 ir_d0) (IROutcome.ret (IRList.cons IRScalar (IRScalar.int_ ir_d1) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ 255) (IRList.cons IRScalar (IRScalar.bool_ Bool.true) (IRList.cons IRScalar (IRScalar.int_ ir_d0) (ir_vl1 (IRScalar.bool_ Bool.false)))))))) := Eq.refl IROutcome (IROutcome.ret (IRList.cons IRScalar (IRScalar.int_ ir_d1) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ 255) (IRList.cons IRScalar (IRScalar.bool_ Bool.true) (IRList.cons IRScalar (IRScalar.int_ ir_d0) (ir_vl1 (IRScalar.bool_ Bool.false))))))))";

const SRC_IR_W3_OU_ON_MUL_BOUNDARY: &str = "def ir_w3_ou_on_mul_boundary : Eq IROutcome (ir_eval ir_d8 ir_w3_ou_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ ir_d16) (ir_vl1 (IRScalar.int_ ir_d16))) ir_mem0 ir_d0) (IROutcome.ret (IRList.cons IRScalar (IRScalar.int_ 32) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ ir_d0) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ ir_d0) (ir_vl1 (IRScalar.bool_ Bool.true)))))))) := Eq.refl IROutcome (IROutcome.ret (IRList.cons IRScalar (IRScalar.int_ 32) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ ir_d0) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ ir_d0) (ir_vl1 (IRScalar.bool_ Bool.true))))))))";

const SRC_IR_W3_OU_NOT_INT: &str = "def ir_w3_ou_not_int (b : Bool) (y : Nat) : Eq IROutcome (ir_eval ir_d8 ir_w3_ou_module ir_d0 (IRList.cons IRScalar (IRScalar.bool_ b) (ir_vl1 (IRScalar.int_ y))) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_int) := Eq.refl IROutcome (IROutcome.type_error IRFault.not_int)";

const SRC_IR_W3_OS_ON_SMALL: &str = "def ir_w3_os_on_small : Eq IROutcome (ir_eval ir_d8 ir_w3_os_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ ir_d3) (ir_vl1 (IRScalar.int_ 254))) ir_mem0 ir_d0) (IROutcome.ret (IRList.cons IRScalar (IRScalar.int_ ir_d1) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ ir_d5) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ 250) (ir_vl1 (IRScalar.bool_ Bool.false)))))))) := Eq.refl IROutcome (IROutcome.ret (IRList.cons IRScalar (IRScalar.int_ ir_d1) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ ir_d5) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ 250) (ir_vl1 (IRScalar.bool_ Bool.false))))))))";

const SRC_IR_W3_OS_ON_MIN_EDGE: &str = "def ir_w3_os_on_min_edge : Eq IROutcome (ir_eval ir_d8 ir_w3_os_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ 128) (ir_vl1 (IRScalar.int_ ir_d1))) ir_mem0 ir_d0) (IROutcome.ret (IRList.cons IRScalar (IRScalar.int_ 129) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ 127) (IRList.cons IRScalar (IRScalar.bool_ Bool.true) (IRList.cons IRScalar (IRScalar.int_ 128) (ir_vl1 (IRScalar.bool_ Bool.false)))))))) := Eq.refl IROutcome (IROutcome.ret (IRList.cons IRScalar (IRScalar.int_ 129) (IRList.cons IRScalar (IRScalar.bool_ Bool.false) (IRList.cons IRScalar (IRScalar.int_ 127) (IRList.cons IRScalar (IRScalar.bool_ Bool.true) (IRList.cons IRScalar (IRScalar.int_ 128) (ir_vl1 (IRScalar.bool_ Bool.false))))))))";

const SRC_IR_W3_OS_NOT_INT: &str = "def ir_w3_os_not_int (x : Nat) (b : Bool) : Eq IROutcome (ir_eval ir_d8 ir_w3_os_module ir_d0 (IRList.cons IRScalar (IRScalar.int_ x) (ir_vl1 (IRScalar.bool_ b))) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_int) := Eq.refl IROutcome (IROutcome.type_error IRFault.not_int)";

const SRC_IR_W3_OVF_BAD_TY: &str = "def ir_w3_ovf_bad_ty (s : IRMachine) (rs : IRList Nat) (a : IRScalar) (b : IRScalar) : Eq IRConfig (ir_overflow_exec s rs IROverflowOp.addoverflow IRTy.ptr_ a b) (IRConfig.halted (IROutcome.type_error IRFault.not_int)) := Eq.refl IRConfig (IRConfig.halted (IROutcome.type_error IRFault.not_int))";

impl Specification {
    /// The W3 overflow micro-modules (unsigned + signed lanes) and their
    /// kernel-executed witnesses.
    ///
    /// Reuses (all from `add_eval_ir`): the `IRInst`/`IROverflowOp`/`IRTy`/
    /// `IRBlock`/`IRFunc`/`IRModule` syntax, the `ir_d0..ir_d16` numerals,
    /// the `ir_nd`/`ir_bd3`/`ir_blk`/`ir_blk0`/`ir_nl0`/`ir_nl2`/`ir_vl1`
    /// builders, `ir_mem0`, `ir_overflow_exec`, and the machine (`ir_eval`,
    /// `IROutcome`, `IRFault`, `IRConfig`). Deliberately nothing from any
    /// chain stage, so the battery can register the module lines standalone
    /// into the minimal `EvalIr` bundle spec.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check — for the witnesses, that means the kernel RAN the machine
    /// and got a different outcome, which is a red to report, never to tune.
    pub(super) fn add_eval_ir_w3_synth(&mut self) -> Result<(), SpecError> {
        for (line, doc) in [
            (SRC_IR_W3_OU_B0, "ir_w3_ou_b0: SYNTHETIC micro-module entry (W3 overflow, unsigned lane): add.overflow, sub.overflow and mul.overflow at u8 on the same two parameters, each node declaring TWO results, then a six-value ret of every bound result — nothing stands between the two-result binds and the return, so a battery row observes exactly what the binds produced. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OU_FUNC, "ir_w3_ou_func: two parameters (SSA ids 0,1), entry block 0, one block, function id 0. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OU_MODULE, "ir_w3_ou_module: the SYNTHETIC unsigned-overflow module — authored for the W3 differential (E2 twin tests/fixtures/synth/synth_overflow_u8.trust-ir.txt); no producer emitted it and no lineage gate applies. The producer DOES emit overflow nodes (the no_overflow shape, mul.overflow usize — eval_ir_meta_tag.rs module doc), but every one is at usize, the width the type lane deliberately refuses to resolve, so the synthetic lane is the honest measurement route. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OS_B0, "ir_w3_os_b0: SYNTHETIC micro-module entry (W3 overflow, signed lane): the same three-op body at i8 — the carrier type's constructor choice is what flips ir_overflow_exec into the signed flag lane, which is the property this module exists to measure against the unsigned twin. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OS_FUNC, "ir_w3_os_func: two parameters (SSA ids 0,1), entry block 0, one block, function id 0. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OS_MODULE, "ir_w3_os_module: the SYNTHETIC signed-overflow module (E2 twin tests/fixtures/synth/synth_overflow_i8.trust-ir.txt). DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OU_ON_SMALL, "ir_w3_ou_on_small: 3 op 2 at u8 — add (5,false), sub (1,false), mul (6,false): the all-quiet row, pinning that the checked forms compute the plain values when nothing overflows. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OU_ON_BORROW, "ir_w3_ou_on_borrow: 0 op 1 at u8 — sub borrows: value 255, flag TRUE, while add (1,false) and mul (0,false) stay quiet in the same execution: one row, both polarities across the three ops. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OU_ON_MUL_BOUNDARY, "ir_w3_ou_on_mul_boundary: 16 op 16 at u8 — mul is EXACTLY 2^8: value wraps to 0 and the flag is TRUE at the boundary's first step (the ir_exact_ovf_mul_flag_u_boundary vector pins the last quiet product from below at width 4); add (32,false) and sub (0,false) quiet. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OU_NOT_INT, "ir_w3_ou_not_int: FAULT EDGE — a Bool in an operand slot is `type_error not_int` at every (b, y): checked arithmetic has no i1 form on either side (trust-ir's expect_int_value rejects Bool, a4e81b6 interpret.rs:5429-5434; Clean's ir_overflow_vals fails closed through ir_as_int). Universally quantified: the kernel iota-reduces the coercion match on the bool_ constructor, so the payloads never matter. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OS_ON_SMALL, "ir_w3_os_on_small: 3 op -2 at i8 (raw 254) — add (1,false), sub (5,false), mul (-6: raw 250, false): mixed signs, everything in range, and the raw-residue vocabulary carries the negative product as its bit pattern. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OS_ON_MIN_EDGE, "ir_w3_os_on_min_edge: -128 op 1 at i8 (raw 128) — sub overflows (-129: value raw 127, flag TRUE) while add (-127: raw 129, false) and mul (-128: raw 128, false) sit exactly ONE INSIDE their bounds: three answers straddling MIN in one execution, the signed edge the plan names. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OS_NOT_INT, "ir_w3_os_not_int: FAULT EDGE, second-operand side — an integer first operand coerces (quantified x rides through ir_as_int's some) and the Bool second operand fails closed, pinning that BOTH coercion arms of ir_overflow_vals are real. DerivedProved, zero axiom_deps."),
            (SRC_IR_W3_OVF_BAD_TY, "ir_w3_ovf_bad_ty: FAULT EDGE, type-dispatch side — ir_overflow_exec at a pointer type is `type_error not_int` at EVERY machine, result list and operand pair: the kernel iota-reduces the type match, so nothing else is consulted. The wildcard arm's representative witness (bool_ included in the same arm). DerivedProved, zero axiom_deps."),
        ] {
            self.add_recursive_def(line, doc)?;
        }
        Ok(())
    }
}
