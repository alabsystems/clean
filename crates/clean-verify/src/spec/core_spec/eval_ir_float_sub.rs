// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The float SUBTRACTION chain — `env::native_reducers_float::
//! reduce_float_sub::{closure#0}`: [`super::eval_ir_float_div`]'s sibling over
//! the same emitted shape, and a chain whose A4 RETURNS A COMPUTED BINARY64
//! VALUE ON FINITE OPERANDS where that one refuses.**
//!
//! (No ordinal is claimed. `fadd` and `fmul` are chainable on identical terms —
//! `float_div.rs`'s sibling census records all three with their measured
//! lineages — and which of the three lands first is a scheduling fact, not a
//! property of any of them.)
//!
//! ```text
//! pub(crate) fn reduce_float_sub(args: &[&Expr]) -> Option<Expr> {
//!     float_binary_op(args, |a, b| a - b)     // <- THIS closure
//! }
//! ```
//!
//! ```text
//! rustcc fn @env::native_reducers_float::reduce_float_sub::{closure#0}(functy.551) {
//!     ; #producer: trust
//!     ; #names: %1="a", %2="b"
//! bb0(%0: ptr, %1: f64, %2: f64):
//!     %3 = fsub f64 %1, %2  ; #loc: 354 214 33
//!     ret %3  ; #loc: 354 214 38
//! }
//! ```
//!
//! Structurally this is `fdiv`'s body with one token changed: same one block,
//! same two instructions, same three parameters, same `functy.551`, same four
//! real marker lines. The emitted fixture
//! (`tests/fixtures/float_sub.trust-ir.txt`) is byte-identical to
//! `float_div.trust-ir.txt` apart from the closure name, the operator and the
//! `#loc` column (214 rather than 222) — `tests/crystal_a1_lineage/float_sub.rs`
//! asserts exactly that rather than leaving the port's premise to be re-derived.
//!
//! ## What this chain buys that the `fdiv` chain cannot
//!
//! `env_reduce_float_sub` is `ir_f64_sub`, and `ir_f64_sub a b` is
//! `ir_f64_add a (ir_f64_negate b)` — so it dispatches into the CORRECTLY
//! ROUNDED finite arithmetic of [`super::eval_ir_float_fin`] that landed
//! 2026-08-16. `ir_f64_div`'s `fin`/`fin` cell is still `IROption.none`; this
//! one is not. Concretely:
//!
//! * **`ir_fs2_one_minus_two_answers` is the witness `fdiv` cannot have.** The
//!   kernel runs the emitted module on `1.0` and `2.0` for two steps and
//!   returns `0xBFF0000000000000` (measured, 0.155 s).
//!   `ir_fd_two_over_one_refused` next door registers the REFUSAL on the same
//!   shape of input, and the pair is the boundary of the modelled fragment
//!   drawn between two sibling bodies rather than asserted about one.
//! * **the operand order is observable in the ANSWERING direction.**
//!   `ir_fs2_one_minus_two_answers` and `ir_fs2_two_minus_one_answers` are the
//!   same two bit patterns in the two orders, and the results differ in exactly
//!   the sign bit — computed, not tabulated.
//! * **the signed-zero rule is where `a - b` and `a + b` genuinely disagree.**
//!   `(-0.0) - (+0.0)` is `-0.0` while `(-0.0) + (+0.0)` is `+0.0` (IEEE 754
//!   §6.3). Both are executed, side by side, in
//!   `ir_fs2_minus_zero_minus_plus_zero` and
//!   `ir_fs2_add_disagrees_at_signed_zero`.
//!
//! ## The price, MEASURED — and it is the exact mirror of the gain
//!
//! Buying the finite fragment costs the UNIVERSALLY QUANTIFIED corollaries, and
//! the reason is one line of `super::eval_ir_float`: `ir_f64_div_at`'s
//! `fin`/`fin` cell is `IROption.none`, while `ir_f64_add_at`'s is
//! `ir_f64_add_fin a b` — the whole bit-at-a-time rounding pipeline. Any
//! definitional-equality check that has to compare two COPIES of a type
//! containing `ir_fs2_res (env_reduce_float_sub a b)` at symbolic `a`, `b`
//! therefore descends into that arm and does not return.
//!
//! Measured on the EvalIR scratchpad, 2026-08-20, one 25.8 s spec build:
//!
//! ```text
//! ir_fs2_correct                          0.237 s   A4 itself
//! ir_fs2_correct_witness                  0.012 s   A4 APPLIED, result type written out
//! ir_fs2_sound_at                         0.080 s   A5 over an ABSTRACT outcome
//! ir_fs2_machine_sound_at_one_minus_two   0.010 s   A5 INSTANTIATED at concrete operands
//! ir_fs2_machine_sound (A5, symbolic)     > 900 s   killed, twice, two formulations
//! ir_fs2_returns_iff_modelled (symbolic)  > 60 s    killed
//! ir_fs2_never_traps (symbolic)           > 60 s    killed
//! ```
//!
//! The rule the numbers state: **A4 may be applied, and its conclusion may be
//! written out; it may not be used as a SUB-PROOF inside a larger term at
//! symbolic bit patterns.** So every corollary here is split in two — a lemma
//! over an abstract `o : IROption Nat` (`ir_fs2_sound_at`, `ir_fs2_ret_at`,
//! `ir_fs2_trap_at`), where nothing can unfold because there is nothing to
//! unfold, and CONCRETE instantiations of it against the executed witnesses,
//! where the value domain computes instead of expanding. That is strictly less
//! than `fdiv`'s `ir_fd_machine_sound` / `ir_fd_returns_iff_modelled` claim, it
//! is stated at the strength measured, and the gap is named rather than papered
//! over. The build item that would close it is a reducibility control (or an
//! opaque wrapper) on the finite arithmetic; there is none today.
//!
//! ## What the refinement theorem says
//!
//! `ir_fs2_correct` is TOTAL over a partial value domain: for every pair of bit
//! patterns, every environment pointer, every heap and every fuel at or above 2,
//! the machine returns `ir_fs2_res (env_reduce_float_sub a b)` — the value when
//! the fragment is modelled and the tagged refusal when it is not. The refusals
//! are still real (`inf - inf`, any NaN operand), so the `IROption` case
//! analysis and the non-`ret` fuel monotonicity are needed here for the same
//! reason they were for `fdiv`.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! `env_reduce_float_sub` is `ir_f64_sub`, and `ir_f64_sub` is **not proved to
//! be `f64::sub`**. It is `ir_f64_add` of the exact IEEE 754 negation, over a
//! table that is IEEE 754 on the classified fragment by construction and by
//! reading, dispatching into a rounding pipeline that is correct by construction
//! and by reading. The gap between it and the hardware subtracter is stated in
//! [`super::eval_ir_float`] and [`super::eval_ir_float_fin`] and closed nowhere.
//! A reader who wants "Clean proved the kernel's float subtraction correct" will
//! not find it here and should not say it.
//!
//! The link between the proved module and the emitted one is STRUCTURAL —
//! `tests/crystal_a1_lineage/float_sub.rs`. Everything past the flip seam is
//! downstream and covered by nothing here. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// NOTHING SHARED IS RE-DECLARED HERE, and the omissions are deliberate content
// rather than oversight. `EncodesF64Val`, `ir_outcome_fuelout_ne_unmodelled_prop`,
// `ir_option_is_some` and `ir_outcome_is_trap` are registered by
// [`super::eval_ir_float_div`], which runs one stage earlier; `ir_nl3` / `ir_vl3`
// by the FIFTH chain (`eval_ir_bvar_range`); `ir_outcome_is_ret` and
// `ir_outcome_fuelout_ne_ret_prop` by `add_eval_ir_correct` / `add_eval_ir_fuel`.
// Re-declaring a name that already exists is the eighth chain's ONE real error
// and it costs a full `Specification::new()` to find: the EvalIR bundle carries
// none of those stages, so a duplicate elaborates cleanly in every fast gate and
// fails only in the full build. A name that already exists is a name to REUSE.

// ── the reflected closure and its outcome ─────────────────────────────
const SRC_IR_FS2_TF64: &str = "def ir_fs2_tf64 : IRTy := IRTy.float_ 64";
const SRC_ENV_REDUCE_FLOAT_SUB: &str =
    "def env_reduce_float_sub (a : Nat) (b : Nat) : IROption Nat := ir_f64_sub a b";
const SRC_IR_FS2_RES: &str = "def ir_fs2_res (o : IROption Nat) : IROutcome := IROption.rec Nat (fun (_ : IROption Nat) => IROutcome) (IROutcome.unmodelled IRFault.float_domain) (fun (k : Nat) => IROutcome.ret (ir_vl1 (IRScalar.float_ k))) o";

// ── the emitted module, transcribed ───────────────────────────────────
const SRC_IR_FS2_B0: &str = "def ir_fs2_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.binop IRBinOp.fsub ir_fs2_tf64 ir_d1 ir_d2) ir_d3) (ir_nd (IRInst.ret (ir_nl1 ir_d3))))";
const SRC_IR_FS2_FUNC: &str = "def ir_fs2_func : IRFunc := IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0 (ir_blk ir_fs2_b0 ir_blk0)";
const SRC_IR_FS2_MODULE: &str = "def ir_fs2_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_fs2_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

// ── the machine ───────────────────────────────────────────────────────
const SRC_IR_FS2_MACH0: &str = "def ir_fs2_mach0 (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl3 ir_d0 ir_d1 ir_d2) (ir_vl3 p (IRScalar.float_ a) (IRScalar.float_ b)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";
const SRC_IR_FS2_M1: &str = "def ir_fs2_m1 (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) (o : IROption Nat) : IRConfig := ir_bind_result (ir_fs2_mach0 p a b mem na) (ir_nl1 ir_d3) (ir_f64_result o)";
const SRC_IR_FS2_ONE_STEP: &str = "def ir_fs2_one_step (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_steps ir_d1 ir_fs2_module (IRConfig.running (ir_fs2_mach0 p a b mem na))) (ir_fs2_m1 p a b mem na (env_reduce_float_sub a b)) := Eq.refl IRConfig (ir_fs2_m1 p a b mem na (env_reduce_float_sub a b))";
const SRC_IR_FS2_SPLIT: &str = "def ir_fs2_split (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) (o : IROption Nat) : Eq IROutcome (ir_run ir_d1 ir_fs2_module (ir_fs2_m1 p a b mem na o)) (ir_fs2_res o) := IROption.rec Nat (fun (o0 : IROption Nat) => Eq IROutcome (ir_run ir_d1 ir_fs2_module (ir_fs2_m1 p a b mem na o0)) (ir_fs2_res o0)) (Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)) (fun (k : Nat) => Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) o";
const SRC_IR_FS2_EXACT: &str = "def ir_fs2_exact (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d2 ir_fs2_module (IRConfig.running (ir_fs2_mach0 p a b mem na))) (ir_fs2_res (env_reduce_float_sub a b)) := Eq.trans IROutcome (ir_run ir_d2 ir_fs2_module (IRConfig.running (ir_fs2_mach0 p a b mem na))) (ir_run ir_d1 ir_fs2_module (ir_steps ir_d1 ir_fs2_module (IRConfig.running (ir_fs2_mach0 p a b mem na)))) (ir_fs2_res (env_reduce_float_sub a b)) (ir_run_steps_split ir_fs2_module ir_d1 ir_d1 (IRConfig.running (ir_fs2_mach0 p a b mem na))) (Eq.subst IRConfig (fun (c : IRConfig) => Eq IROutcome (ir_run ir_d1 ir_fs2_module c) (ir_fs2_res (env_reduce_float_sub a b))) (ir_fs2_m1 p a b mem na (env_reduce_float_sub a b)) (ir_steps ir_d1 ir_fs2_module (IRConfig.running (ir_fs2_mach0 p a b mem na))) (Eq.symm IRConfig (ir_steps ir_d1 ir_fs2_module (IRConfig.running (ir_fs2_mach0 p a b mem na))) (ir_fs2_m1 p a b mem na (env_reduce_float_sub a b)) (ir_fs2_one_step p a b mem na)) (ir_fs2_split p a b mem na (env_reduce_float_sub a b)))";

// ── fuel monotonicity for an outcome that may be a REFUSAL ────────────
const SRC_IR_FS2_FUELOUT_ABSURD: &str = "def ir_fs2_fuelout_absurd (o : IROption Nat) (C : Prop) : Eq IROutcome IROutcome.fuel_out (ir_fs2_res o) -> C := IROption.rec Nat (fun (o0 : IROption Nat) => Eq IROutcome IROutcome.fuel_out (ir_fs2_res o0) -> C) (fun (h : Eq IROutcome IROutcome.fuel_out (IROutcome.unmodelled IRFault.float_domain)) => ir_outcome_fuelout_ne_unmodelled_prop IRFault.float_domain C h) (fun (k : Nat) (h : Eq IROutcome IROutcome.fuel_out (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) => ir_outcome_fuelout_ne_ret_prop (ir_vl1 (IRScalar.float_ k)) C h) o";
const SRC_IR_FS2_RUN_SUCC: &str = "def ir_fs2_run_succ (f : Nat) : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fs2_module c) (ir_fs2_res o) -> Eq IROutcome (ir_run (Nat.succ f) ir_fs2_module c) (ir_fs2_res o) := Nat.rec (fun (k : Nat) => forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run k ir_fs2_module c) (ir_fs2_res o) -> Eq IROutcome (ir_run (Nat.succ k) ir_fs2_module c) (ir_fs2_res o)) (fun (c : IRConfig) (o : IROption Nat) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run Nat.zero ir_fs2_module c0) (ir_fs2_res o) -> Eq IROutcome (ir_run (Nat.succ Nat.zero) ir_fs2_module c0) (ir_fs2_res o)) (fun (s : IRMachine) (h : Eq IROutcome (ir_run Nat.zero ir_fs2_module (IRConfig.running s)) (ir_fs2_res o)) => ir_fs2_fuelout_absurd o (Eq IROutcome (ir_run (Nat.succ Nat.zero) ir_fs2_module (IRConfig.running s)) (ir_fs2_res o)) h) (fun (x : IROutcome) (h : Eq IROutcome (ir_run Nat.zero ir_fs2_module (IRConfig.halted x)) (ir_fs2_res o)) => h) c) (fun (k : Nat) (ih : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run k ir_fs2_module c) (ir_fs2_res o) -> Eq IROutcome (ir_run (Nat.succ k) ir_fs2_module c) (ir_fs2_res o)) (c : IRConfig) (o : IROption Nat) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run (Nat.succ k) ir_fs2_module c0) (ir_fs2_res o) -> Eq IROutcome (ir_run (Nat.succ (Nat.succ k)) ir_fs2_module c0) (ir_fs2_res o)) (fun (s : IRMachine) => ih (ir_step ir_fs2_module s) o) (fun (x : IROutcome) (h : Eq IROutcome (ir_run (Nat.succ k) ir_fs2_module (IRConfig.halted x)) (ir_fs2_res o)) => h) c) f";
const SRC_IR_FS2_RUN_LE: &str = "def ir_fs2_run_le (f : Nat) (g : Nat) (hle : Le f g) : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fs2_module c) (ir_fs2_res o) -> Eq IROutcome (ir_run g ir_fs2_module c) (ir_fs2_res o) := Le.rec f (fun (g0 : Nat) (_hg : Le f g0) => forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fs2_module c) (ir_fs2_res o) -> Eq IROutcome (ir_run g0 ir_fs2_module c) (ir_fs2_res o)) (fun (c : IRConfig) (o : IROption Nat) (h : Eq IROutcome (ir_run f ir_fs2_module c) (ir_fs2_res o)) => h) (fun (g2 : Nat) (_h2 : Le f g2) (ih : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fs2_module c) (ir_fs2_res o) -> Eq IROutcome (ir_run g2 ir_fs2_module c) (ir_fs2_res o)) (c : IRConfig) (o : IROption Nat) (h : Eq IROutcome (ir_run f ir_fs2_module c) (ir_fs2_res o)) => ir_fs2_run_succ g2 c o (ih c o h)) g hle";

// ── A4, and the inversions stated over an ABSTRACT outcome ────────────
const SRC_IR_FS2_CORRECT: &str = "def ir_fs2_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (ra : IRScalar) (rb : IRScalar) (a : Nat) (b : Nat) (ha : EncodesF64Val ra a) (hb : EncodesF64Val rb b) : Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fs2_module ir_d0 (ir_vl3 p ra rb) mem na) (ir_fs2_res (env_reduce_float_sub a b)) := EncodesF64Val.rec (fun (ra0 : IRScalar) (a0 : Nat) (_ : EncodesF64Val ra0 a0) => forall (rb0 : IRScalar) (b0 : Nat), EncodesF64Val rb0 b0 -> Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fs2_module ir_d0 (ir_vl3 p ra0 rb0) mem na) (ir_fs2_res (env_reduce_float_sub a0 b0))) (fun (x : Nat) => fun (rb0 : IRScalar) (b0 : Nat) (hb0 : EncodesF64Val rb0 b0) => EncodesF64Val.rec (fun (rb1 : IRScalar) (b1 : Nat) (_ : EncodesF64Val rb1 b1) => Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fs2_module ir_d0 (ir_vl3 p (IRScalar.float_ x) rb1) mem na) (ir_fs2_res (env_reduce_float_sub x b1))) (fun (y : Nat) (hle : Le ir_d2 fuel) => ir_fs2_run_le ir_d2 fuel hle (IRConfig.running (ir_fs2_mach0 p x y mem na)) (env_reduce_float_sub x y) (ir_fs2_exact p x y mem na)) rb0 b0 hb0) ra a ha rb b hb";
const SRC_IR_FS2_HEAD_FLOAT: &str = "def ir_fs2_head_float (v : IRList IRScalar) : Nat := IRList.rec IRScalar (fun (_ : IRList IRScalar) => Nat) Nat.zero (fun (x : IRScalar) (_ : IRList IRScalar) (_ : Nat) => ir_scalar_code x) v";
const SRC_IR_FS2_ANSWER: &str = "def ir_fs2_answer (o : IROutcome) : IROption Nat := IROutcome.rec (fun (_ : IROutcome) => IROption Nat) (fun (v : IRList IRScalar) => IROption.some Nat (ir_fs2_head_float v)) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (IROption.none Nat) o";
const SRC_IR_FS2_ANSWER_RES: &str = "def ir_fs2_answer_res (o : IROption Nat) : Eq (IROption Nat) (ir_fs2_answer (ir_fs2_res o)) o := IROption.rec Nat (fun (o0 : IROption Nat) => Eq (IROption Nat) (ir_fs2_answer (ir_fs2_res o0)) o0) (Eq.refl (IROption Nat) (IROption.none Nat)) (fun (k : Nat) => Eq.refl (IROption Nat) (IROption.some Nat k)) o";
const SRC_IR_FS2_SOUND_AT: &str = "def ir_fs2_sound_at (o : IROption Nat) (k : Nat) (x : IROutcome) (hx : Eq IROutcome x (ir_fs2_res o)) (hret : Eq IROutcome x (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) : Eq (IROption Nat) o (IROption.some Nat k) := Eq.trans (IROption Nat) o (ir_fs2_answer (ir_fs2_res o)) (IROption.some Nat k) (Eq.symm (IROption Nat) (ir_fs2_answer (ir_fs2_res o)) o (ir_fs2_answer_res o)) (Eq.cong IROutcome (IROption Nat) ir_fs2_answer (ir_fs2_res o) (IROutcome.ret (ir_vl1 (IRScalar.float_ k))) (Eq.trans IROutcome (ir_fs2_res o) x (IROutcome.ret (ir_vl1 (IRScalar.float_ k))) (Eq.symm IROutcome x (ir_fs2_res o) hx) hret))";
const SRC_IR_FS2_RES_IS_RET: &str = "def ir_fs2_res_is_ret (o : IROption Nat) : Eq Bool (ir_outcome_is_ret (ir_fs2_res o)) (ir_option_is_some o) := IROption.rec Nat (fun (o0 : IROption Nat) => Eq Bool (ir_outcome_is_ret (ir_fs2_res o0)) (ir_option_is_some o0)) (Eq.refl Bool Bool.false) (fun (_ : Nat) => Eq.refl Bool Bool.true) o";
const SRC_IR_FS2_RET_AT: &str = "def ir_fs2_ret_at (o : IROption Nat) (x : IROutcome) (hx : Eq IROutcome x (ir_fs2_res o)) : Eq Bool (ir_outcome_is_ret x) (ir_option_is_some o) := Eq.trans Bool (ir_outcome_is_ret x) (ir_outcome_is_ret (ir_fs2_res o)) (ir_option_is_some o) (Eq.cong IROutcome Bool ir_outcome_is_ret x (ir_fs2_res o) hx) (ir_fs2_res_is_ret o)";
const SRC_IR_FS2_RES_NEVER_TRAPS: &str = "def ir_fs2_res_never_traps (o : IROption Nat) : Eq Bool (ir_outcome_is_trap (ir_fs2_res o)) Bool.false := IROption.rec Nat (fun (o0 : IROption Nat) => Eq Bool (ir_outcome_is_trap (ir_fs2_res o0)) Bool.false) (Eq.refl Bool Bool.false) (fun (_ : Nat) => Eq.refl Bool Bool.false) o";
const SRC_IR_FS2_TRAP_AT: &str = "def ir_fs2_trap_at (o : IROption Nat) (x : IROutcome) (hx : Eq IROutcome x (ir_fs2_res o)) : Eq Bool (ir_outcome_is_trap x) Bool.false := Eq.trans Bool (ir_outcome_is_trap x) (ir_outcome_is_trap (ir_fs2_res o)) Bool.false (Eq.cong IROutcome Bool ir_outcome_is_trap x (ir_fs2_res o) hx) (ir_fs2_res_never_traps o)";
const SRC_IR_F64_SUB_ZERO_ZERO: &str = "def ir_f64_sub_zero_zero (a : Nat) (b : Nat) (hza : Eq IRF64Class (ir_f64_class a) IRF64Class.zero_) (hzb : Eq IRF64Class (ir_f64_class (ir_f64_negate b)) IRF64Class.zero_) : Eq (IROption Nat) (ir_f64_sub a b) (IROption.some Nat (ir_f64_pack (Bool.and (ir_f64_is_neg a) (ir_f64_is_neg (ir_f64_negate b))) Nat.zero)) := Eq.trans (IROption Nat) (ir_f64_add_at a (ir_f64_negate b) (ir_f64_class a) (ir_f64_class (ir_f64_negate b))) (ir_f64_add_at a (ir_f64_negate b) IRF64Class.zero_ (ir_f64_class (ir_f64_negate b))) (IROption.some Nat (ir_f64_pack (Bool.and (ir_f64_is_neg a) (ir_f64_is_neg (ir_f64_negate b))) Nat.zero)) (Eq.cong IRF64Class (IROption Nat) (fun (c : IRF64Class) => ir_f64_add_at a (ir_f64_negate b) c (ir_f64_class (ir_f64_negate b))) (ir_f64_class a) IRF64Class.zero_ hza) (Eq.cong IRF64Class (IROption Nat) (fun (c : IRF64Class) => ir_f64_add_at a (ir_f64_negate b) IRF64Class.zero_ c) (ir_f64_class (ir_f64_negate b)) IRF64Class.zero_ hzb)";

// ── kernel-EXECUTED witnesses ─────────────────────────────────────────
// The bit patterns, once, so the witnesses below read as numbers:
//   1.0        = 0x3FF0000000000000 = 4607182418800017408
//   2.0        = 0x4000000000000000 = 4611686018427387904
//   -1.0       = 0xBFF0000000000000 = 13830554455654793216
//   +0.0       = 0
//   -0.0       = 0x8000000000000000 = 9223372036854775808
//   +inf       = 0x7FF0000000000000 = 9218868437227405312
//   -inf       = 0xFFF0000000000000 = 18442240474082181120
//   a quiet NaN= 0x7FF8000000000000 = 9221120237041090560
const SRC_W_ONE_MINUS_TWO: &str = "def ir_fs2_one_minus_two_answers : Eq IROutcome (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 13830554455654793216))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 13830554455654793216)))";
const SRC_W_TWO_MINUS_ONE: &str = "def ir_fs2_two_minus_one_answers : Eq IROutcome (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4611686018427387904) (IRScalar.float_ 4607182418800017408)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 4607182418800017408))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 4607182418800017408)))";
const SRC_W_SELF_CANCELS: &str = "def ir_fs2_self_cancels_to_plus_zero : Eq IROutcome (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4607182418800017408)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 0)))";
const SRC_W_FIN_MINUS_ZERO: &str = "def ir_fs2_fin_minus_plus_zero_is_exact : Eq IROutcome (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 4607182418800017408))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 4607182418800017408)))";
const SRC_W_ZERO_MINUS_FIN: &str = "def ir_fs2_plus_zero_minus_fin_negates : Eq IROutcome (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 0) (IRScalar.float_ 4607182418800017408)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 13830554455654793216))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 13830554455654793216)))";
const SRC_W_MZERO_MINUS_PZERO: &str = "def ir_fs2_minus_zero_minus_plus_zero : Eq IROutcome (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9223372036854775808) (IRScalar.float_ 0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 9223372036854775808))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 9223372036854775808)))";
const SRC_W_PZERO_MINUS_PZERO: &str = "def ir_fs2_plus_zero_minus_plus_zero : Eq IROutcome (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 0) (IRScalar.float_ 0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 0)))";
const SRC_W_ADD_CONTRAST: &str = "def ir_fs2_add_disagrees_at_signed_zero : Eq (IROption Nat) (ir_f64_add 9223372036854775808 0) (IROption.some Nat 0) := Eq.refl (IROption Nat) (IROption.some Nat 0)";
const SRC_W_INF_MINUS_INF: &str = "def ir_fs2_inf_minus_inf_refused : Eq IROutcome (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 9218868437227405312)) ir_mem0 ir_d0) (IROutcome.unmodelled IRFault.float_domain) := Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)";
const SRC_W_INF_MINUS_MINF: &str = "def ir_fs2_inf_minus_minus_inf_answers : Eq IROutcome (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 18442240474082181120)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312)))";
const SRC_W_NAN: &str = "def ir_fs2_nan_operand_refused : Eq IROutcome (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9221120237041090560) (IRScalar.float_ 4607182418800017408)) ir_mem0 ir_d0) (IROutcome.unmodelled IRFault.float_domain) := Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)";
const SRC_W_INT_OPERAND: &str = "def ir_fs2_integer_operand_is_a_type_error : Eq IRStepResult (ir_binop_eval IRBinOp.fsub ir_fs2_tf64 (IRScalar.int_ 1) (IRScalar.int_ 0)) (IRStepResult.fault (IROutcome.type_error IRFault.not_float)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_float))";
const SRC_W_F32: &str = "def ir_fs2_binary32_is_unmodelled : Eq IRStepResult (ir_binop_eval IRBinOp.fsub (IRTy.float_ 32) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";
const SRC_W_CORRECT: &str = "def ir_fs2_correct_witness (a : Nat) (b : Nat) : Eq IROutcome (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ a) (IRScalar.float_ b)) ir_mem0 ir_d0) (ir_fs2_res (env_reduce_float_sub a b)) := ir_fs2_correct ir_mem0 ir_d2 ir_d0 IRScalar.undef_ (IRScalar.float_ a) (IRScalar.float_ b) a b (EncodesF64Val.mk a) (EncodesF64Val.mk b) (Le.refl ir_d2)";
const SRC_W_SOUND_AT: &str = "def ir_fs2_machine_sound_at_one_minus_two : Eq (IROption Nat) (env_reduce_float_sub 4607182418800017408 4611686018427387904) (IROption.some Nat 13830554455654793216) := ir_fs2_sound_at (env_reduce_float_sub 4607182418800017408 4611686018427387904) 13830554455654793216 (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_mem0 ir_d0) (ir_fs2_correct_witness 4607182418800017408 4611686018427387904) ir_fs2_one_minus_two_answers";
const SRC_W_RET_FIN: &str = "def ir_fs2_returns_at_one_minus_two : Eq Bool (ir_outcome_is_ret (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_mem0 ir_d0)) (ir_option_is_some (env_reduce_float_sub 4607182418800017408 4611686018427387904)) := ir_fs2_ret_at (env_reduce_float_sub 4607182418800017408 4611686018427387904) (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_mem0 ir_d0) (ir_fs2_correct_witness 4607182418800017408 4611686018427387904)";
const SRC_W_RET_INF: &str = "def ir_fs2_returns_at_inf_minus_inf : Eq Bool (ir_outcome_is_ret (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 9218868437227405312)) ir_mem0 ir_d0)) (ir_option_is_some (env_reduce_float_sub 9218868437227405312 9218868437227405312)) := ir_fs2_ret_at (env_reduce_float_sub 9218868437227405312 9218868437227405312) (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 9218868437227405312)) ir_mem0 ir_d0) (ir_fs2_correct_witness 9218868437227405312 9218868437227405312)";
const SRC_W_TRAP_FIN: &str = "def ir_fs2_never_traps_at_one_minus_two : Eq Bool (ir_outcome_is_trap (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_mem0 ir_d0)) Bool.false := ir_fs2_trap_at (env_reduce_float_sub 4607182418800017408 4611686018427387904) (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_mem0 ir_d0) (ir_fs2_correct_witness 4607182418800017408 4611686018427387904)";
const SRC_W_TRAP_INF: &str = "def ir_fs2_never_traps_at_inf_minus_inf : Eq Bool (ir_outcome_is_trap (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 9218868437227405312)) ir_mem0 ir_d0)) Bool.false := ir_fs2_trap_at (env_reduce_float_sub 9218868437227405312 9218868437227405312) (ir_eval ir_d2 ir_fs2_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 9218868437227405312)) ir_mem0 ir_d0) (ir_fs2_correct_witness 9218868437227405312 9218868437227405312)";

impl Specification {
    /// Register the float SUBTRACTION chain:
    /// `env::native_reducers_float::reduce_float_sub::{closure#0}`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_float_sub(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_IR_FS2_TF64, "ir_fs2_tf64: f64 -- binary64, the type the emitted fsub is at. Not decoration and not a width that happens to be right: ir_float_binop reads the width off it and DECIDES only 64, giving every other float width the tagged unmodelled outcome. ir_fs2_binary32_is_unmodelled executes exactly that difference. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ENV_REDUCE_FLOAT_SUB, "env_reduce_float_sub: the reflected env::native_reducers_float::reduce_float_sub::{closure#0} (native_reducers_float.rs:214), which is `|a, b| a - b` on f64. It is ir_f64_sub -- which is ir_f64_add of the exact IEEE 754 negation (super::eval_ir_float), so it dispatches into the correctly-rounded finite arithmetic of super::eval_ir_float_fin -- and NOT a proof that ir_f64_sub is the hardware subtracter. That gap is stated in those modules and closed nowhere. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_RES, "ir_fs2_res: the outcome a classified float answer produces -- the returned value when the fragment is modelled, and IROutcome.unmodelled IRFault.float_domain when it is not. Subtraction models strictly more of the 4x4 class product than division does (the whole fin/fin cell answers), and the shape is still exactly right: `inf - inf` and every NaN row are invalid operations whose NaN payload is implementation-defined, so the refusal half is real and A4 has to be total over both. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_B0, "ir_fs2_b0: THE WHOLE BODY, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/float_sub.trust-ir.txt). One fsub at f64 over %1 and %2 IN THAT ORDER into %3, then `ret %3`. The operand order is not a formality on this operator: ir_fs2_one_minus_two_answers and ir_fs2_two_minus_one_answers execute the same two bit patterns both ways and get answers differing in the sign bit. The TYPE on the binop and the RETURNED id (%3, the difference -- not %1, the minuend) are compared by tests/crystal_a1_lineage/float_sub.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_FUNC, "ir_fs2_func: the closure as EvalIR -- THREE parameters (%0 the closure environment pointer, %1 and %2 the operands), entry block 0, one block. %0 is bound and never read, and A4 quantifies over it with no premise at all. Through the FIFTH chain's ir_nl3, which this stage reuses rather than re-declares. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_MODULE, "ir_fs2_module: the module for env::native_reducers_float::reduce_float_sub::{closure#0}, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel, recorded at tests/fixtures/float_sub.trust-ir.txt and checked graph-for-graph and instruction-for-instruction, including the type and ret lanes, by tests/crystal_a1_lineage/float_sub.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_MACH0, "ir_fs2_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds THREE parameters positionally. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_M1, "ir_fs2_m1: the machine after the fsub, with the CLASSIFIED ANSWER ABSTRACTED to an IROption parameter. ir_f64_result dispatches with IROption.rec, and on symbolic bit patterns ir_f64_sub is stuck under ir_f64_class, so the machine is stuck there and no fuel unsticks it. At o := env_reduce_float_sub a b this term is DEFINITIONALLY one ir_step of ir_fs2_mach0. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_ONE_STEP, "ir_fs2_one_step: ONE step of the machine IS ir_fs2_m1 at the real classified answer. Eq.refl -- the kernel runs one step and compares two configurations, both of which carry the classification unreduced, so the check is bounded by the size of one instruction's semantics rather than by the rounding pipeline. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_SPLIT, "ir_fs2_split: THE CASE ANALYSIS, over the boundary of the modelled fragment. If the classified answer is `some k` the machine binds the float and the second step returns it; if it is `none` the fsub FAULTS and ir_bind_result halts immediately, so the remaining step is spent on an already-halted configuration. Both minors are Eq.refl. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_EXACT, "ir_fs2_exact: the machine agrees with the reflected closure at EXACTLY 2 steps, for every pair of bit patterns. 2 = 1 + 1, and the proof is that split: ir_run_steps_split peels the first step, ir_fs2_one_step identifies the resulting configuration, and the case analysis finishes the second. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_FUELOUT_ABSURD, "ir_fs2_fuelout_absurd: nothing in the IMAGE of ir_fs2_res is fuel_out. By IROption.rec: `none` lands on unmodelled and `some k` on ret, and each has its own discriminator -- ir_outcome_fuelout_ne_unmodelled_prop (registered by super::eval_ir_float_div) and ir_outcome_fuelout_ne_ret_prop (add_eval_ir_fuel). This is what makes fuel monotonicity TRUE for this chain's outcome shape. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_RUN_SUCC, "ir_fs2_run_succ: FUEL MONOTONICITY for an outcome that may be a REFUSAL. ir_run_le_ret is stated for IROutcome.ret and cannot be widened in place; this is the same Nat.rec-over-fuel with an IRConfig.rec convoy, at the ir_fs2_res image. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_RUN_LE, "ir_fs2_run_le: the same at a bound rather than a successor, by Le.rec iterating ir_fs2_run_succ. Note Le's first argument is a PARAMETER, so Le.rec takes it before the motive. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_CORRECT, "ir_fs2_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE, FOR FLOAT SUBTRACTION. *** For every pair of binary64 bit patterns a and b, every pair of values representing them, every closure environment pointer, every heap, every next-address counter and every fuel at or above 2, ir_eval on ir_fs2_module returns exactly ir_fs2_res (env_reduce_float_sub a b). \n\nTOTAL, not restricted to the modelled fragment: where the classified subtraction answers -- which now INCLUDES every finite/finite pair, correctly rounded -- the machine returns that float; where it refuses, the machine returns the tagged unmodelled outcome and nothing else. \n\nA0/A6 for this body are recorded at tests/fixtures/float_sub.lineage.json AT THE STRENGTH MEASURED THERE and no higher: lowered, spliced, unsupported [], derived_mir agreed over 6 canonical lines, markers_exact TRUE over 4 real marker lines, the producer's interpreter differential agreed on 64 sampled inputs, zero calls, and a codegen flip whose lineage equals the coverage row's -- from three clean non-incremental builds with byte-identical coverage recorded by the reproduction stanza, but using one unsealed local-stage1 producer rather than the sealed-driver protocol float_div.lineage.json records, and with no negative control. A1 is gated by tests/crystal_a1_lineage/float_sub.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_HEAD_FLOAT, "ir_fs2_head_float: the bit pattern of the first returned value, through ir_scalar_code -- which is the identity on IRScalar.float_ n. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_ANSWER, "ir_fs2_answer: read a classified answer back out of an outcome. A `ret` carries `some` of its float's bit pattern; every fault and exhaustion carries `none`. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_ANSWER_RES, "ir_fs2_answer_res: ir_fs2_answer INVERTS ir_fs2_res, on the nose, at both constructors. Two Eq.refl. This is what makes the inversion below an inversion rather than a restatement. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_SOUND_AT, "ir_fs2_sound_at: *** A5, THE INVERSION -- STATED OVER AN ABSTRACT OUTCOME. *** If a run x equals the outcome of a classified answer o, and that run returns the float k, then o is exactly `some k`. \n\nThe abstraction is FORCED and the reason is measured (see the module doc). The fdiv chain states its A5 directly about env_reduce_float_div because ir_f64_div_at's fin/fin cell is IROption.none; ir_f64_add_at's is ir_f64_add_fin, the whole rounding pipeline, so the same statement at symbolic bit patterns makes the kernel compare two copies of a type containing it and does not return (killed at 900 s, twice, in two formulations). Here o and x are variables, nothing can unfold, and the composition with A4 is done by INSTANTIATION at concrete operands -- ir_fs2_machine_sound_at_one_minus_two. What is lost is the universally-quantified A5; what is kept is its content and an executed instance. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_RES_IS_RET, "ir_fs2_res_is_ret: the outcome is a return exactly when the classified answer exists. Two Eq.refl. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_RET_AT, "ir_fs2_ret_at: *** THE BOUNDARY OF THE MODELLED FRAGMENT, over an abstract outcome. *** A run that equals ir_fs2_res o is a return if and only if o exists -- as an equality of Bools, so neither direction can be weakened. Abstract for the same measured reason as ir_fs2_sound_at, and instantiated against the shipped body at both a finite pair (ir_fs2_returns_at_one_minus_two, Bool.true) and a refused one (ir_fs2_returns_at_inf_minus_inf, Bool.false). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_RES_NEVER_TRAPS, "ir_fs2_res_never_traps: nothing in the image of ir_fs2_res is a trap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS2_TRAP_AT, "ir_fs2_trap_at: NO UB, NO TYPE ERROR, NO STUCK STATE, NO EXHAUSTION for a run that equals ir_fs2_res o -- over an abstract outcome, for the same measured reason. The one thing such a run may do is REFUSE, and ir_fs2_ret_at says exactly when. Instantiated at an answering and a refusing pair. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_F64_SUB_ZERO_ZERO, "ir_f64_sub_zero_zero: if the minuend is a zero and the NEGATED subtrahend is a zero, then a - b is the zero whose sign bit is the AND of their sign bits. Proved by rewriting the two class subterms with Eq.cong and letting ir_f64_add_at compute -- the device ir_f64_div_fin_zero uses, available here only because ir_f64_sub is stated as ir_f64_add of the negation, so ir_f64_add's table/application split sits underneath it. \n\nThe premise is on ir_f64_negate b rather than on b, which is what the definition actually dispatches on; assuming the interchange would be an unproved step even though negation is exact. This is a theorem about the VALUE DOMAIN. Carrying it onto the machine's arguments -- the fdiv chain's ir_fd_machine_sound_divzero -- needs the symbolic A5 that is measured unaffordable here, so it is not claimed. IEEE 754 6.3. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ONE_MINUS_TWO, "*** CONCRETE EXECUTION WITNESS -- 1.0 - 2.0 = -1.0, THROUGH THE EMITTED BODY. *** The kernel runs ir_fs2_module on two real binary64 bit patterns for two steps and returns 0xBFF0000000000000 (measured 0.155 s). \n\nThis is the witness the fdiv chain CANNOT have: ir_fd_two_over_one_refused next door registers the tagged refusal on the same shape of input, because a quotient's significand needs a second division at guard precision. Subtraction reaches the finite fragment through ir_f64_add_fin, so here the emitted body's answer is a COMPUTED float rather than a classified one, and the kernel computed it -- a wrong bit pattern in this declaration would fail elaboration. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_TWO_MINUS_ONE, "CONCRETE EXECUTION WITNESS -- 2.0 - 1.0 = 1.0, and with the witness above this is OPERAND ORDER OBSERVED IN THE ANSWERING DIRECTION. The same two bit patterns, the same emitted body, opposite order, answers differing in exactly the sign bit. A transcription that emitted `fsub f64 %2, %1` computes a different function and every CFG lane except the operand order agrees with it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_SELF_CANCELS, "CONCRETE EXECUTION WITNESS -- 1.0 - 1.0 = +0.0. IEEE 754 6.3 makes an exact zero difference POSITIVE zero under roundTiesToEven, not the sign of either operand. Reached through ir_f64_opposite, the one finite arm the classification decides without rounding. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_FIN_MINUS_ZERO, "CONCRETE EXECUTION WITNESS -- 1.0 - (+0.0) = 1.0. Subtracting a zero from a finite is exact, including from a subnormal: the classified fin/zero arm returns the minuend unchanged. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ZERO_MINUS_FIN, "CONCRETE EXECUTION WITNESS -- (+0.0) - 1.0 = -1.0. The zero/fin arm returns the NEGATED subtrahend, so the answer's sign comes from the operand the source never negates explicitly. With the witness above, the order contrast at the zero boundary rather than in the finite fragment. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_MZERO_MINUS_PZERO, "*** CONCRETE EXECUTION WITNESS -- (-0.0) - (+0.0) = -0.0. *** The signed-zero rule, executed through the emitted body rather than asserted about the table. Both operands are zeros; the answer's sign bit is the AND of the operand sign bits AFTER negation, and here that is negative. A model that treated the sign of a zero as noise returns +0.0 and passes every other witness in this file. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_PZERO_MINUS_PZERO, "CONCRETE EXECUTION WITNESS -- (+0.0) - (+0.0) = +0.0. The companion to the one above: same subtrahend, minuend differing only in its sign bit, and the emitted body's answers differ. Together the two rule out `sign of the subtrahend alone`; they do NOT separate the registered rule from `sign of the minuend` — the separating input would be (-0.0) - (-0.0) = +0.0, which is not registered here. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ADD_CONTRAST, "*** THE CONTRAST WITNESS. *** ir_f64_add on the SAME two bit patterns answers +0.0 where the subtraction above answers -0.0: (-0) + (+0) = +0 and (-0) - (+0) = -0, IEEE 754 6.3. The same contrast already runs at the ir_binop_eval level as ir_f64_w_add_mixed_zeros / ir_f64_w_sub_mixed_zeros (eval_ir_float_ops.rs); what THIS witness adds is the same fact executed through the EMITTED MODULE's two-step machine rather than the table -- the sub-lane's analogue of ir_fd_udiv_traps_where_fdiv_answers. Stated about ir_f64_add directly, since no reflected reduce_float_add closure is registered to run. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_INF_MINUS_INF, "CONCRETE REFUSAL WITNESS -- (+inf) - (+inf) is REFUSED. An invalid operation: IEEE 754 makes it a quiet NaN and the NaN's payload is implementation-defined, so there is no bit pattern to return. The machine says IROutcome.unmodelled IRFault.float_domain, which is not a value and cannot be mistaken for one. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_INF_MINUS_MINF, "CONCRETE EXECUTION WITNESS -- (+inf) - (-inf) = +inf, REFUSED one witness above at the same magnitudes. The subtrahend's sign bit alone decides refusal from value: ir_f64_ssign of the minuend and the NEGATED subtrahend selects the arm. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_NAN, "CONCRETE REFUSAL WITNESS -- a quiet NaN operand is REFUSED. 0x7FF8000000000000 has magnitude above the infinity boundary, so it classifies nan_ and the whole row is none. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_INT_OPERAND, "FAIL-CLOSED WITNESS -- an INTEGER operand at a float type is a TYPE ERROR, not a wrong number and not a refusal. ir_as_float declines IRScalar.int_ even though both constructors carry a Nat, which is exactly why A4's premise is EncodesF64Val and not EncodesU64Val. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_F32, "FAIL-CLOSED WITNESS -- the SAME operands at binary32 are UNMODELLED. 1.0 - 2.0 answers at f64 and is refused at f32, because binary32's exponent field is 8 bits wide and this module's boundary constants are binary64's. The width on the instruction is semantic input; a transcription that got it wrong would compute this instead of ir_fs2_one_minus_two_answers. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_CORRECT, "ir_fs2_correct_witness: A4's premises are all SATISFIABLE, discharged concretely -- the empty heap, an undef closure environment pointer (which the body never reads), the exact fuel bound by Le.refl, and two EncodesF64Val.mk. Both bit patterns stay universally quantified. It is also the ONLY affordable way to use A4 as a sub-proof: applied with its conclusion written out it costs 0.012 s, and every instantiated corollary below goes through it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_SOUND_AT, "*** A5 AGAINST THE SHIPPED BODY, AT CONCRETE OPERANDS. *** The machine running the emitted fsub on 1.0 and 2.0 returned -1.0 (ir_fs2_one_minus_two_answers, not an assumption); therefore the reflected closure answers exactly `some 0xBFF0000000000000` -- it did not refuse, and it did not answer a different bit pattern. ir_fs2_sound_at instantiated at this pair, with A4 supplying the run. The symbolic version of this statement is measured unaffordable; this is the instance, and it is executed end to end. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_RET_FIN, "ir_fs2_returns_at_one_minus_two: the shipped body RETURNS on 1.0 and 2.0 exactly when the classified subtraction answers -- both sides Bool.true, computed. The answering side of the modelled fragment's boundary. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_RET_INF, "ir_fs2_returns_at_inf_minus_inf: and the REFUSING side, on the same equality -- both sides Bool.false. The pair is what makes ir_fs2_ret_at non-vacuous against this body: an equality of Bools that is true at true and true at false. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_TRAP_FIN, "ir_fs2_never_traps_at_one_minus_two: no UB, no type error, no stuck state and no exhaustion on the answering pair. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_TRAP_INF, "ir_fs2_never_traps_at_inf_minus_inf: and none on the REFUSING pair either -- the tagged unmodelled verdict is a deliberate refusal, not a failure, and this is the witness that distinguishes the two. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
