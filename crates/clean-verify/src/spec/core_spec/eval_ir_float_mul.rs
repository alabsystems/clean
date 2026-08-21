// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The ELEVENTH complete width-one chain — the second over FLOAT
//! ARITHMETIC, and the first whose A4 RETURNS A COMPUTED VALUE on finite
//! inputs: `env::native_reducers_float::reduce_float_mul::{closure#0}`.**
//!
//! ```text
//! pub(crate) fn reduce_float_mul(args: &[&Expr]) -> Option<Expr> {
//!     float_binary_op(args, |a, b| a * b)     // <- THIS closure
//! }
//! ```
//!
//! ```text
//! rustcc fn @env::native_reducers_float::reduce_float_mul::{closure#0}(functy.551) {
//!     ; #producer: trust
//!     ; #names: %1="a", %2="b"
//! bb0(%0: ptr, %1: f64, %2: f64):
//!     %3 = fmul f64 %1, %2  ; #loc: 354 218 33
//!     ret %3  ; #loc: 354 218 38
//! }
//! ```
//!
//! The emitted body is the eighth chain's ([`super::eval_ir_float_div`])
//! character for character except for the opcode token and the source column —
//! `fmul` for `fdiv`, 218 for 222. Everything structural is therefore ported
//! rather than re-derived: one block, two instructions, three parameters, the
//! same 2-step run, the same `IROption`-abstracted intermediate configuration,
//! the same fuel monotonicity over a possibly-REFUSING outcome.
//!
//! ## What is NOT a rename, and is the whole reason to register it
//!
//! `env_reduce_float_mul` is `ir_f64_mul`, and `ir_f64_mul`'s `fin`/`fin` cell
//! is `IROption.some Nat (ir_f64_mul_fin a b)` where `ir_f64_div`'s is
//! `IROption.none` ([`super::eval_ir_float`], [`super::eval_ir_float_fin`]).
//! So this chain's A4 is the first in the program that concludes a COMPUTED
//! binary64 value on ordinary finite operands rather than only on the
//! classified special-value lattice: `ir_fm_one_times_two` runs the emitted
//! body on 1.0 and 2.0 for two steps and the kernel returns
//! `0x4000000000000000`. The eighth chain's sibling witness for that input,
//! `ir_fd_two_over_one_refused`, is a REFUSAL, and its comment says why —
//! a quotient's significand is itself a division, so division did not get the
//! finite fragment when addition, subtraction and multiplication did.
//!
//! The class lattice also differs from division's in three cells, and the
//! difference is not cosmetic:
//!
//! * `inf * inf` ANSWERS `+inf` here (`ir_fm_inf_times_inf`) where `inf / inf`
//!   is an invalid operation and is REFUSED.
//! * `0 * inf` is REFUSED here, in BOTH orders, where `0 / inf` answers a zero
//!   and `inf / 0` answers an infinity.
//! * `fin * 0` is a SIGNED ZERO here where `fin / 0` is a SIGNED INFINITY —
//!   executed side by side as `ir_fm_two_times_plus_zero` (`+0.0`) and
//!   `ir_fm_minus_two_times_plus_zero` (`-0.0`) against the eighth chain's
//!   `ir_fd_one_over_plus_zero` (`+inf`).
//!
//! Multiplication is COMMUTATIVE on the modelled fragment where division is
//! not, so the eighth chain's `ir_fd_order_is_observable` has no counterpart
//! and would be false if written. What replaces it is the pair
//! `ir_fm_two_times_three` / `ir_fm_three_times_two`: the same two operands in
//! the two orders through the same emitted body, both returning `6.0`. That is
//! a fact about this operator, not about the transcription — the operand ORDER
//! in `ir_fm_b0` is still gated structurally by the `binops` lane in
//! `tests/crystal_a1_lineage/float_mul.rs`, exactly as it is for `fdiv`.
//!
//! ## What the refinement theorem says
//!
//! `ir_fm_correct` is TOTAL over the two-constructor image of `ir_fm_res`: for
//! every pair of bit patterns, every environment pointer, every heap, every
//! next-address counter and every fuel at or above 2, the machine returns
//! exactly `ir_fm_res (env_reduce_float_mul a b)` — **the value where the
//! fragment is modelled and the tagged refusal where it is not.** The refusals
//! are narrower than division's but they have not gone away: a NaN operand and
//! `0 * inf` are still refused, and `ir_fm_zero_times_inf_refused` /
//! `ir_fm_inf_times_zero_refused` / `ir_fm_nan_operand_refused` execute that.
//!
//! ## What this chain does NOT carry that the eighth chain does, and why
//!
//! The eighth chain's A5 (`ir_fd_machine_sound`), its two Bool corollaries
//! (`ir_fd_returns_iff_modelled`, `ir_fd_never_traps`) and its
//! onto-the-arguments A5 (`ir_fd_machine_sound_divzero`) have **no counterpart
//! registered here.** They are not omitted for lack of a proof — the proof
//! terms are the eighth chain's under renaming, and the generic halves of them
//! ARE registered below (`ir_fm_sound_gen`, `ir_fm_res_is_ret`,
//! `ir_fm_res_never_traps`, `ir_fm_bool_gen`, `ir_fm_answer_res`). What is
//! missing is the step that INSTANTIATES one of those generic lemmas at
//! `env_reduce_float_mul a b`.
//!
//! That instantiation does not elaborate at this operator, and the boundary was
//! bisected rather than guessed (2026-08-20, `tests/evalir_scratchpad.rs`):
//!
//! ```text
//! applying A4 alone                                        0.039 s  PASS
//! ir_fm_sound_gen at a VARIABLE answer                     0.092 s  PASS
//! ir_fm_sound_gen at `env_reduce_float_mul a b`            >30 min  killed
//! ir_fm_bool_gen  at `env_reduce_float_mul a b`            >70 s    killed
//! `env_reduce_float_mul a b` vs `IROption.some Nat k`      0.011 s  PASS
//! the same comparison for `ir_f64_div`  (control)          0.012 s  PASS
//! ```
//!
//! So it is neither the naked comparison nor the delta unfold — both are
//! milliseconds, and the `fdiv` control is too. It is specifically applying an
//! `IROption.rec`-proved lemma AT the multiplication's classified answer, whose
//! `fin`/`fin` cell is `ir_f64_mul_fin a b` — the whole rounding pipeline —
//! where `ir_f64_div_at`'s is the constructor `IROption.none`. Registering the
//! inlined form would not have produced a false theorem; it would have wedged
//! `Specification::new()`, which is why it is absent rather than approximated.
//!
//! Everything the concrete inputs can carry is carried: the fifteen witnesses
//! below are the same facts at literal bit patterns, where the classification
//! and the rounding both COMPUTE and cost tenths of a second.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! `env_reduce_float_mul` is `ir_f64_mul`, and `ir_f64_mul` is **not proved to
//! be `f64::mul`**. It is IEEE 754 by construction and by reading — the
//! classified lattice of [`super::eval_ir_float`] over the exact 106-bit
//! rounded product of [`super::eval_ir_float_fin`] — and a tagged refusal
//! elsewhere. The finite fragment's agreement with the hardware is CHECKED, but
//! only on the witness set `test_every_finite_witness_agrees_with_real_f64`
//! enumerates; there is no theorem quantifying over all inputs and there is
//! none here. A reader who wants "Clean proved the kernel's float
//! multiplication correct" will not find it here and should not say it.
//!
//! Nothing in this module re-registers a shared name. `EncodesF64Val`,
//! `ir_outcome_fuelout_ne_unmodelled_prop`, `ir_option_get`,
//! `ir_option_is_some` and `ir_outcome_is_trap` are the eighth chain's, and
//! this stage runs after it. Re-declaring a name that already exists was that
//! chain's ONE real error, and it failed only in the full
//! `Specification::new()`, at 27 minutes an attempt.
//!
//! The link between the proved module and the emitted one is STRUCTURAL —
//! `tests/crystal_a1_lineage/float_mul.rs`. Everything past the flip seam is
//! downstream and covered by nothing here. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ── the reflected closure, its outcome ────────────────────────────────
// `EncodesF64Val` is NOT declared here: the eighth chain registers it and this
// stage runs after it. Nor are `ir_nl3` / `ir_vl3` (fifth chain),
// `ir_outcome_fuelout_ne_unmodelled_prop`, `ir_option_get`,
// `ir_option_is_some` or `ir_outcome_is_trap` (eighth chain). A name that
// already exists is a name to REUSE.
const SRC_IR_FM_TF64: &str = "def ir_fm_tf64 : IRTy := IRTy.float_ 64";
const SRC_ENV_REDUCE_FLOAT_MUL: &str =
    "def env_reduce_float_mul (a : Nat) (b : Nat) : IROption Nat := ir_f64_mul a b";
const SRC_IR_FM_RES: &str = "def ir_fm_res (o : IROption Nat) : IROutcome := IROption.rec Nat (fun (_ : IROption Nat) => IROutcome) (IROutcome.unmodelled IRFault.float_domain) (fun (k : Nat) => IROutcome.ret (ir_vl1 (IRScalar.float_ k))) o";

// ── the emitted module, transcribed ───────────────────────────────────
const SRC_IR_FM_B0: &str = "def ir_fm_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.binop IRBinOp.fmul ir_fm_tf64 ir_d1 ir_d2) ir_d3) (ir_nd (IRInst.ret (ir_nl1 ir_d3))))";
const SRC_IR_FM_FUNC: &str = "def ir_fm_func : IRFunc := IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0 (ir_blk ir_fm_b0 ir_blk0)";
const SRC_IR_FM_MODULE: &str = "def ir_fm_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_fm_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

// ── the machine ───────────────────────────────────────────────────────
const SRC_IR_FM_MACH0: &str = "def ir_fm_mach0 (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl3 ir_d0 ir_d1 ir_d2) (ir_vl3 p (IRScalar.float_ a) (IRScalar.float_ b)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";
const SRC_IR_FM_M1: &str = "def ir_fm_m1 (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) (o : IROption Nat) : IRConfig := ir_bind_result (ir_fm_mach0 p a b mem na) (ir_nl1 ir_d3) (ir_f64_result o)";
const SRC_IR_FM_ONE_STEP: &str = "def ir_fm_one_step (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_steps ir_d1 ir_fm_module (IRConfig.running (ir_fm_mach0 p a b mem na))) (ir_fm_m1 p a b mem na (env_reduce_float_mul a b)) := Eq.refl IRConfig (ir_fm_m1 p a b mem na (env_reduce_float_mul a b))";
const SRC_IR_FM_SPLIT: &str = "def ir_fm_split (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) (o : IROption Nat) : Eq IROutcome (ir_run ir_d1 ir_fm_module (ir_fm_m1 p a b mem na o)) (ir_fm_res o) := IROption.rec Nat (fun (o0 : IROption Nat) => Eq IROutcome (ir_run ir_d1 ir_fm_module (ir_fm_m1 p a b mem na o0)) (ir_fm_res o0)) (Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)) (fun (k : Nat) => Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) o";
const SRC_IR_FM_EXACT: &str = "def ir_fm_exact (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d2 ir_fm_module (IRConfig.running (ir_fm_mach0 p a b mem na))) (ir_fm_res (env_reduce_float_mul a b)) := Eq.trans IROutcome (ir_run ir_d2 ir_fm_module (IRConfig.running (ir_fm_mach0 p a b mem na))) (ir_run ir_d1 ir_fm_module (ir_steps ir_d1 ir_fm_module (IRConfig.running (ir_fm_mach0 p a b mem na)))) (ir_fm_res (env_reduce_float_mul a b)) (ir_run_steps_split ir_fm_module ir_d1 ir_d1 (IRConfig.running (ir_fm_mach0 p a b mem na))) (Eq.subst IRConfig (fun (c : IRConfig) => Eq IROutcome (ir_run ir_d1 ir_fm_module c) (ir_fm_res (env_reduce_float_mul a b))) (ir_fm_m1 p a b mem na (env_reduce_float_mul a b)) (ir_steps ir_d1 ir_fm_module (IRConfig.running (ir_fm_mach0 p a b mem na))) (Eq.symm IRConfig (ir_steps ir_d1 ir_fm_module (IRConfig.running (ir_fm_mach0 p a b mem na))) (ir_fm_m1 p a b mem na (env_reduce_float_mul a b)) (ir_fm_one_step p a b mem na)) (ir_fm_split p a b mem na (env_reduce_float_mul a b)))";

// ── fuel monotonicity for an outcome that may be a REFUSAL ────────────
const SRC_IR_FM_FUELOUT_ABSURD: &str = "def ir_fm_fuelout_absurd (o : IROption Nat) (C : Prop) : Eq IROutcome IROutcome.fuel_out (ir_fm_res o) -> C := IROption.rec Nat (fun (o0 : IROption Nat) => Eq IROutcome IROutcome.fuel_out (ir_fm_res o0) -> C) (fun (h : Eq IROutcome IROutcome.fuel_out (IROutcome.unmodelled IRFault.float_domain)) => ir_outcome_fuelout_ne_unmodelled_prop IRFault.float_domain C h) (fun (k : Nat) (h : Eq IROutcome IROutcome.fuel_out (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) => ir_outcome_fuelout_ne_ret_prop (ir_vl1 (IRScalar.float_ k)) C h) o";
const SRC_IR_FM_RUN_SUCC: &str = "def ir_fm_run_succ (f : Nat) : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fm_module c) (ir_fm_res o) -> Eq IROutcome (ir_run (Nat.succ f) ir_fm_module c) (ir_fm_res o) := Nat.rec (fun (k : Nat) => forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run k ir_fm_module c) (ir_fm_res o) -> Eq IROutcome (ir_run (Nat.succ k) ir_fm_module c) (ir_fm_res o)) (fun (c : IRConfig) (o : IROption Nat) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run Nat.zero ir_fm_module c0) (ir_fm_res o) -> Eq IROutcome (ir_run (Nat.succ Nat.zero) ir_fm_module c0) (ir_fm_res o)) (fun (s : IRMachine) (h : Eq IROutcome (ir_run Nat.zero ir_fm_module (IRConfig.running s)) (ir_fm_res o)) => ir_fm_fuelout_absurd o (Eq IROutcome (ir_run (Nat.succ Nat.zero) ir_fm_module (IRConfig.running s)) (ir_fm_res o)) h) (fun (x : IROutcome) (h : Eq IROutcome (ir_run Nat.zero ir_fm_module (IRConfig.halted x)) (ir_fm_res o)) => h) c) (fun (k : Nat) (ih : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run k ir_fm_module c) (ir_fm_res o) -> Eq IROutcome (ir_run (Nat.succ k) ir_fm_module c) (ir_fm_res o)) (c : IRConfig) (o : IROption Nat) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run (Nat.succ k) ir_fm_module c0) (ir_fm_res o) -> Eq IROutcome (ir_run (Nat.succ (Nat.succ k)) ir_fm_module c0) (ir_fm_res o)) (fun (s : IRMachine) => ih (ir_step ir_fm_module s) o) (fun (x : IROutcome) (h : Eq IROutcome (ir_run (Nat.succ k) ir_fm_module (IRConfig.halted x)) (ir_fm_res o)) => h) c) f";
const SRC_IR_FM_RUN_LE: &str = "def ir_fm_run_le (f : Nat) (g : Nat) (hle : Le f g) : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fm_module c) (ir_fm_res o) -> Eq IROutcome (ir_run g ir_fm_module c) (ir_fm_res o) := Le.rec f (fun (g0 : Nat) (_hg : Le f g0) => forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fm_module c) (ir_fm_res o) -> Eq IROutcome (ir_run g0 ir_fm_module c) (ir_fm_res o)) (fun (c : IRConfig) (o : IROption Nat) (h : Eq IROutcome (ir_run f ir_fm_module c) (ir_fm_res o)) => h) (fun (g2 : Nat) (_h2 : Le f g2) (ih : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fm_module c) (ir_fm_res o) -> Eq IROutcome (ir_run g2 ir_fm_module c) (ir_fm_res o)) (c : IRConfig) (o : IROption Nat) (h : Eq IROutcome (ir_run f ir_fm_module c) (ir_fm_res o)) => ir_fm_run_succ g2 c o (ih c o h)) g hle";

// ── A4, A5, and the corollaries ───────────────────────────────────────
const SRC_IR_FM_CORRECT: &str = "def ir_fm_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (ra : IRScalar) (rb : IRScalar) (a : Nat) (b : Nat) (ha : EncodesF64Val ra a) (hb : EncodesF64Val rb b) : Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fm_module ir_d0 (ir_vl3 p ra rb) mem na) (ir_fm_res (env_reduce_float_mul a b)) := EncodesF64Val.rec (fun (ra0 : IRScalar) (a0 : Nat) (_ : EncodesF64Val ra0 a0) => forall (rb0 : IRScalar) (b0 : Nat), EncodesF64Val rb0 b0 -> Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fm_module ir_d0 (ir_vl3 p ra0 rb0) mem na) (ir_fm_res (env_reduce_float_mul a0 b0))) (fun (x : Nat) => fun (rb0 : IRScalar) (b0 : Nat) (hb0 : EncodesF64Val rb0 b0) => EncodesF64Val.rec (fun (rb1 : IRScalar) (b1 : Nat) (_ : EncodesF64Val rb1 b1) => Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fm_module ir_d0 (ir_vl3 p (IRScalar.float_ x) rb1) mem na) (ir_fm_res (env_reduce_float_mul x b1))) (fun (y : Nat) (hle : Le ir_d2 fuel) => ir_fm_run_le ir_d2 fuel hle (IRConfig.running (ir_fm_mach0 p x y mem na)) (env_reduce_float_mul x y) (ir_fm_exact p x y mem na)) rb0 b0 hb0) ra a ha rb b hb";
const SRC_IR_FM_HEAD_FLOAT: &str = "def ir_fm_head_float (v : IRList IRScalar) : Nat := IRList.rec IRScalar (fun (_ : IRList IRScalar) => Nat) Nat.zero (fun (x : IRScalar) (_ : IRList IRScalar) (_ : Nat) => ir_scalar_code x) v";
const SRC_IR_FM_ANSWER: &str = "def ir_fm_answer (o : IROutcome) : IROption Nat := IROutcome.rec (fun (_ : IROutcome) => IROption Nat) (fun (v : IRList IRScalar) => IROption.some Nat (ir_fm_head_float v)) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (IROption.none Nat) o";
const SRC_IR_FM_ANSWER_RES: &str = "def ir_fm_answer_res (o : IROption Nat) : Eq (IROption Nat) (ir_fm_answer (ir_fm_res o)) o := IROption.rec Nat (fun (o0 : IROption Nat) => Eq (IROption Nat) (ir_fm_answer (ir_fm_res o0)) o0) (Eq.refl (IROption Nat) (IROption.none Nat)) (fun (k : Nat) => Eq.refl (IROption Nat) (IROption.some Nat k)) o";
// A5's inversion argument, over an OPAQUE classified answer. The eighth chain
// inlines this at `env_reduce_float_div a b`; that spelling does not work at
// this operator and the reason is measured rather than guessed — see the
// registration comment on `ir_fm_sound_gen`.
const SRC_IR_FM_SOUND_GEN: &str = "def ir_fm_sound_gen (o : IROption Nat) (x : IROutcome) (k : Nat) (hx : Eq IROutcome x (ir_fm_res o)) (hret : Eq IROutcome x (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) : Eq (IROption Nat) o (IROption.some Nat k) := Eq.trans (IROption Nat) o (ir_fm_answer (ir_fm_res o)) (IROption.some Nat k) (Eq.symm (IROption Nat) (ir_fm_answer (ir_fm_res o)) o (ir_fm_answer_res o)) (Eq.cong IROutcome (IROption Nat) ir_fm_answer (ir_fm_res o) (IROutcome.ret (ir_vl1 (IRScalar.float_ k))) (Eq.trans IROutcome (ir_fm_res o) x (IROutcome.ret (ir_vl1 (IRScalar.float_ k))) (Eq.symm IROutcome x (ir_fm_res o) hx) hret))";

const SRC_IR_FM_RES_IS_RET: &str = "def ir_fm_res_is_ret (o : IROption Nat) : Eq Bool (ir_outcome_is_ret (ir_fm_res o)) (ir_option_is_some o) := IROption.rec Nat (fun (o0 : IROption Nat) => Eq Bool (ir_outcome_is_ret (ir_fm_res o0)) (ir_option_is_some o0)) (Eq.refl Bool Bool.false) (fun (_ : Nat) => Eq.refl Bool Bool.true) o";
const SRC_IR_FM_BOOL_GEN: &str = "def ir_fm_bool_gen (o : IROption Nat) (x : IROutcome) (f : IROutcome -> Bool) (r : Bool) (hx : Eq IROutcome x (ir_fm_res o)) (hr : Eq Bool (f (ir_fm_res o)) r) : Eq Bool (f x) r := Eq.trans Bool (f x) (f (ir_fm_res o)) r (Eq.cong IROutcome Bool f x (ir_fm_res o) hx) hr";

const SRC_IR_FM_RES_NEVER_TRAPS: &str = "def ir_fm_res_never_traps (o : IROption Nat) : Eq Bool (ir_outcome_is_trap (ir_fm_res o)) Bool.false := IROption.rec Nat (fun (o0 : IROption Nat) => Eq Bool (ir_outcome_is_trap (ir_fm_res o0)) Bool.false) (Eq.refl Bool Bool.false) (fun (_ : Nat) => Eq.refl Bool Bool.false) o";

// ── kernel-EXECUTED witnesses ─────────────────────────────────────────
// The bit patterns, once, so the witnesses below read as numbers:
//   1.0        = 0x3FF0000000000000 = 4607182418800017408
//   2.0        = 0x4000000000000000 = 4611686018427387904
//   3.0        = 0x4008000000000000 = 4613937818241073152
//   6.0        = 0x4018000000000000 = 4618441417868443648
//   -2.0       = 0xC000000000000000 = 13835058055282163712
//   +0.0       = 0
//   -0.0       = 0x8000000000000000 = 9223372036854775808
//   +inf       = 0x7FF0000000000000 = 9218868437227405312
//   max normal = 0x7FEFFFFFFFFFFFFF = 9218868437227405311
//   a quiet NaN= 0x7FF8000000000000 = 9221120237041090560
const SRC_W_ONE_TIMES_TWO: &str = "def ir_fm_one_times_two : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 4611686018427387904))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 4611686018427387904)))";
const SRC_W_TWO_TIMES_THREE: &str = "def ir_fm_two_times_three : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4611686018427387904) (IRScalar.float_ 4613937818241073152)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 4618441417868443648))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 4618441417868443648)))";
const SRC_W_THREE_TIMES_TWO: &str = "def ir_fm_three_times_two : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4613937818241073152) (IRScalar.float_ 4611686018427387904)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 4618441417868443648))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 4618441417868443648)))";
const SRC_W_OVERFLOW: &str = "def ir_fm_overflow_to_inf : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405311) (IRScalar.float_ 4611686018427387904)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312)))";
const SRC_W_INF_TIMES_INF: &str = "def ir_fm_inf_times_inf : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 9218868437227405312)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312)))";
const SRC_W_TWO_TIMES_PLUS_ZERO: &str = "def ir_fm_two_times_plus_zero : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4611686018427387904) (IRScalar.float_ 0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 0)))";
const SRC_W_MINUS_TWO_TIMES_PLUS_ZERO: &str = "def ir_fm_minus_two_times_plus_zero : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 13835058055282163712) (IRScalar.float_ 0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 9223372036854775808))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 9223372036854775808)))";
const SRC_W_MINUS_ZERO_SQUARED: &str = "def ir_fm_minus_zero_times_minus_zero : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9223372036854775808) (IRScalar.float_ 9223372036854775808)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 0)))";
const SRC_W_ZERO_TIMES_INF: &str = "def ir_fm_zero_times_inf_refused : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 0) (IRScalar.float_ 9218868437227405312)) ir_mem0 ir_d0) (IROutcome.unmodelled IRFault.float_domain) := Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)";
const SRC_W_INF_TIMES_ZERO: &str = "def ir_fm_inf_times_zero_refused : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 0)) ir_mem0 ir_d0) (IROutcome.unmodelled IRFault.float_domain) := Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)";
const SRC_W_NAN: &str = "def ir_fm_nan_operand_refused : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9221120237041090560) (IRScalar.float_ 4607182418800017408)) ir_mem0 ir_d0) (IROutcome.unmodelled IRFault.float_domain) := Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)";
const SRC_W_INT_OPERAND: &str = "def ir_fm_integer_operand_is_a_type_error : Eq IRStepResult (ir_binop_eval IRBinOp.fmul ir_fm_tf64 (IRScalar.int_ 1) (IRScalar.int_ 0)) (IRStepResult.fault (IROutcome.type_error IRFault.not_float)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_float))";
const SRC_W_F32: &str = "def ir_fm_binary32_is_unmodelled : Eq IRStepResult (ir_binop_eval IRBinOp.fmul (IRTy.float_ 32) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";
const SRC_W_UMUL_CONTRAST: &str = "def ir_fm_umul_wraps_where_fmul_overflows : Eq IRStepResult (ir_binop_eval IRBinOp.mul (IRTy.uint_ 8) (IRScalar.int_ 16) (IRScalar.int_ 16)) (IRStepResult.value (IRScalar.int_ 0)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 0))";
const SRC_W_CORRECT_WITNESS: &str = "def ir_fm_correct_witness (a : Nat) (b : Nat) : Eq IROutcome (ir_eval ir_d2 ir_fm_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ a) (IRScalar.float_ b)) ir_mem0 ir_d0) (ir_fm_res (env_reduce_float_mul a b)) := ir_fm_correct ir_mem0 ir_d2 ir_d0 IRScalar.undef_ (IRScalar.float_ a) (IRScalar.float_ b) a b (EncodesF64Val.mk a) (EncodesF64Val.mk b) (Le.refl ir_d2)";

impl Specification {
    /// Register the ELEVENTH complete width-one chain, the second over float
    /// arithmetic and the first whose A4 returns a COMPUTED value on finite
    /// operands: `env::native_reducers_float::reduce_float_mul::{closure#0}`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_float_mul(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_IR_FM_TF64, "ir_fm_tf64: f64 -- binary64, the type the emitted fmul is at. ir_float_binop reads the width off it and DECIDES only 64, giving every other float width the tagged unmodelled outcome; ir_fm_binary32_is_unmodelled executes that on the same two operands the fin/fin witness answers on. A separate alias from ir_fd_tf64 rather than a reuse, because the CFG type lane resolves the alias declared beside its own chain. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ENV_REDUCE_FLOAT_MUL, "env_reduce_float_mul: the reflected env::native_reducers_float::reduce_float_mul::{closure#0} (native_reducers_float.rs:218), which is `|a, b| a * b` on f64. It is ir_f64_mul -- the classified binary64 multiplication of super::eval_ir_float, whose fin/fin cell is the rounded 106-bit product of super::eval_ir_float_fin -- and NOT a proof that ir_f64_mul is the hardware multiplier. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_RES, "ir_fm_res: the outcome a classified float answer produces -- the returned value when the fragment is modelled, and IROutcome.unmodelled IRFault.float_domain when it is not. \n\nThe eighth chain's device, at ir_f64_mul instead of ir_f64_div. Its two constructors are still both REACHABLE here: `some` on every finite pair and on the answering special-value cells, `none` on a NaN operand and on 0*inf. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_B0, "ir_fm_b0: THE WHOLE BODY, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/float_mul.trust-ir.txt). One fmul at f64 over %1 and %2 in that order into %3, then `ret %3`. \n\nThe operand ORDER is transcribed and gated structurally by the binops lane even though this operator is commutative on the modelled fragment: the gate compares the artifact, not the semantics. The TYPE (f64, not f32) and the RETURNED id (%3, the product -- not %1, the left operand) are the two lanes the eighth chain added. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_FUNC, "ir_fm_func: the closure as EvalIR -- THREE parameters (%0 the closure environment pointer, %1 and %2 the operands), entry block 0, one block. %0 is bound and never read, and A4 quantifies over it with no premise at all. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_MODULE, "ir_fm_module: the module for env::native_reducers_float::reduce_float_mul::{closure#0}, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir recorded at tests/fixtures/float_mul.trust-ir.txt and checked graph-for-graph and instruction-for-instruction, including the type and ret lanes, by tests/crystal_a1_lineage/float_mul.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_MACH0, "ir_fm_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds THREE parameters positionally. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_M1, "ir_fm_m1: the machine after the fmul, with the CLASSIFIED ANSWER ABSTRACTED to an IROption parameter. On symbolic bit patterns ir_f64_mul is stuck under ir_f64_class, so the machine is stuck there and no fuel unsticks it; at o := env_reduce_float_mul a b this term is DEFINITIONALLY one ir_step of ir_fm_mach0. The abstraction also keeps the finite arm out of the symbolic proofs entirely -- ir_f64_mul_fin never has to reduce for A4 to hold. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_ONE_STEP, "ir_fm_one_step: ONE step of the machine IS ir_fm_m1 at the real classified answer. Eq.refl -- both configurations carry the classification unreduced, so the check is bounded by the size of one instruction's semantics rather than by a 106-bit product. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_SPLIT, "ir_fm_split: THE CASE ANALYSIS, over the boundary of the modelled fragment. If the classified answer is `some k` the machine binds the float and the second step returns it; if it is `none` the fmul FAULTS and ir_bind_result halts immediately, so the remaining step is spent on an already-halted configuration. Both minors are Eq.refl. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_EXACT, "ir_fm_exact: the machine agrees with the reflected closure at EXACTLY 2 steps, for every pair of bit patterns. 2 = 1 + 1: ir_run_steps_split peels the first step, ir_fm_one_step identifies the resulting configuration, and the case analysis finishes the second. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_FUELOUT_ABSURD, "ir_fm_fuelout_absurd: nothing in the IMAGE of ir_fm_res is fuel_out. By IROption.rec: `none` lands on unmodelled and `some k` on ret, and each has its own discriminator -- ir_outcome_fuelout_ne_unmodelled_prop and ir_outcome_fuelout_ne_ret_prop, both already registered. This is what makes fuel monotonicity TRUE for this chain's outcome shape, since the unconditional statement is false (a run that exhausts at f may halt at succ f). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_RUN_SUCC, "ir_fm_run_succ: FUEL MONOTONICITY for an outcome that may be a REFUSAL. ir_run_le_ret is stated for IROutcome.ret and cannot be widened in place; this is the same Nat.rec-over-fuel with an IRConfig.rec convoy, at the ir_fm_res image. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_RUN_LE, "ir_fm_run_le: the same at a bound rather than a successor, by Le.rec iterating ir_fm_run_succ. Note Le's first argument is a PARAMETER, so Le.rec takes it before the motive. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_CORRECT, "ir_fm_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE, FOR FLOAT MULTIPLICATION. *** For every pair of binary64 bit patterns a and b, every pair of values representing them, every closure environment pointer, every heap, every next-address counter and every fuel at or above 2, ir_eval on ir_fm_module returns exactly ir_fm_res (env_reduce_float_mul a b). \n\nTOTAL, not restricted to the modelled fragment: where the classified multiplication answers -- which INCLUDES every finite/finite pair, unlike the eighth chain's division -- the machine returns that float; where it refuses (a NaN operand, 0*inf in either order), the machine returns the tagged unmodelled outcome and nothing else. \n\nA1 is gated by tests/crystal_a1_lineage/float_mul.rs. A0/A6 for THIS closure are NOT established: the eighth chain's evidence file records this body's def_index (15286) and lineage as a census row rather than a measurement of it, and the fixtures/float_mul.lineage.json a sibling lane landed is a body-lineage pin at ONE local build, not the derived_mir / markers_exact / interpreter-differential evidence assert_a0_a6 consumes. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_HEAD_FLOAT, "ir_fm_head_float: the bit pattern of the first returned value, through ir_scalar_code -- which is the identity on IRScalar.float_ n. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_ANSWER, "ir_fm_answer: read a classified answer back out of an outcome. A `ret` carries `some` of its float's bit pattern; every fault and exhaustion carries `none`. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_ANSWER_RES, "ir_fm_answer_res: ir_fm_answer INVERTS ir_fm_res, on the nose, at both constructors. Two Eq.refl. This is what makes A5 an inversion rather than a restatement. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_SOUND_GEN, "ir_fm_sound_gen: the inversion argument, over an OPAQUE classified answer -- if the outcome ir_fm_res builds from o is a returned float k, then o is `some k`. \n\nTHIS GENERIC FORM IS ALL THAT IS REGISTERED. The eighth chain also instantiates it, at env_reduce_float_div a b, to get ir_fd_machine_sound; the corresponding instantiation at env_reduce_float_mul a b does NOT elaborate and is therefore absent rather than approximated -- the module doc records the bisection that located the boundary, including the fdiv control that rules out the naked comparison and the delta unfold. So what this chain proves is the inversion itself, for every classified answer including this closure's; what it does not carry is the sentence naming that answer. \n\nThe device is ir_fm_m1's, one screen up, and it is why A4 itself was never at risk. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_RES_IS_RET, "ir_fm_res_is_ret: the outcome is a return exactly when the classified answer exists. Two Eq.refl. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_BOOL_GEN, "ir_fm_bool_gen: transport a Bool observation across A4, over an OPAQUE classified answer and an OPAQUE outcome. The eighth chain's ir_fd_returns_iff_modelled and ir_fd_never_traps are each one application of this at the closure's answer; both instantiations hit the same elaboration wall as A5's here (see ir_fm_sound_gen and the module doc), so the transport is registered and the two instantiated corollaries are not. ir_fm_res_is_ret and ir_fm_res_never_traps below supply its second premise for any answer. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FM_RES_NEVER_TRAPS, "ir_fm_res_never_traps: nothing in the image of ir_fm_res is a trap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ONE_TIMES_TWO, "*** CONCRETE EXECUTION WITNESS -- 1.0 * 2.0 = 2.0, AND THE WITNESS THE EIGHTH CHAIN CANNOT HAVE. *** The kernel runs the emitted module on two ORDINARY FINITE binary64 bit patterns for two steps and returns 0x4000000000000000. The sibling chain's theorem about this same input shape, ir_fd_two_over_one_refused, is a refusal, because ir_f64_div's fin/fin cell is IROption.none and ir_f64_mul's is the rounded product. This is the first A4 in the program whose value comes out of a rounding pipeline rather than out of a class table. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_TWO_TIMES_THREE, "CONCRETE EXECUTION WITNESS -- 2.0 * 3.0 = 6.0. Half of the commutativity pair below. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_THREE_TIMES_TWO, "CONCRETE EXECUTION WITNESS -- 3.0 * 2.0 = 6.0, THE SAME TWO OPERANDS THE OTHER WAY ROUND. The pair is what replaces the eighth chain's ir_fd_order_is_observable: division answers differently in the two orders and multiplication answers the same, so on THIS operator an operand swap is invisible to execution. It is not invisible to the GATE -- the binops lane compares (op, result, lhs, rhs) against the artifact -- and that separation is the point: the transcription is checked structurally, not semantically. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_OVERFLOW, "CONCRETE EXECUTION WITNESS -- max normal * 2.0 = +inf. OVERFLOW OUT OF THE FINITE ARM, through the emitted body: both operands classify fin_, so the machine enters ir_f64_mul_fin, and what comes back is the infinity bit pattern. Not a fault and not a refusal -- IEEE 754 §7.4 makes an overflow under roundTiesToEven the infinity of the result's sign. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_INF_TIMES_INF, "*** CONCRETE EXECUTION WITNESS -- (+inf) * (+inf) = +inf, WHERE inf / inf IS REFUSED. *** The cell of the class lattice where the two operators disagree most visibly: a product of infinities is determined by the sign rule alone, and a quotient of infinities is an invalid operation whose NaN payload is implementation-defined. ir_fd_inf_over_inf_refused is the same input to the sibling chain. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_TWO_TIMES_PLUS_ZERO, "CONCRETE EXECUTION WITNESS -- 2.0 * (+0.0) = +0.0. The fin/zero cell, at agreeing signs. Contrast the sibling chain: 2.0 / (+0.0) is an INFINITY. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_MINUS_TWO_TIMES_PLUS_ZERO, "*** CONCRETE EXECUTION WITNESS -- (-2.0) * (+0.0) = -0.0, THE SIGN RULE MADE OBSERVABLE. *** The same magnitudes as the witness above and one flipped sign bit, and the emitted body returns a DIFFERENT bit pattern: 0x8000000000000000, not 0. A model that treated the sign of a zero result as noise would return 0 twice, and it would agree with every other witness in this file that does not have a zero result. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_MINUS_ZERO_SQUARED, "CONCRETE EXECUTION WITNESS -- (-0.0) * (-0.0) = +0.0. The zero/zero cell, where the XOR of two set sign bits is clear: the product of two negative zeros is a POSITIVE zero. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ZERO_TIMES_INF, "CONCRETE REFUSAL WITNESS -- (+0.0) * (+inf) is REFUSED. An invalid operation: IEEE 754 makes it a quiet NaN, and the NaN's payload is implementation-defined, so there is no bit pattern to return. The machine says IROutcome.unmodelled IRFault.float_domain, which is not a value and cannot be mistaken for one. In the sibling chain this same pair ANSWERS -- 0 / inf is an exact zero. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_INF_TIMES_ZERO, "CONCRETE REFUSAL WITNESS -- (+inf) * (+0.0) is REFUSED TOO. The other order, registered because the zero/inf and inf/zero cells of ir_f64_mul_at are separate arms of two nested IRF64Class.rec and elaboration cannot tell one from the other. In the sibling chain the two orders answer DIFFERENTLY (0/inf is a zero, inf/0 is an infinity); here they both refuse, and both are executed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_NAN, "CONCRETE REFUSAL WITNESS -- a quiet NaN operand is REFUSED. 0x7FF8000000000000 has magnitude above the infinity boundary, so it classifies nan_ and the whole row is none. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_INT_OPERAND, "FAIL-CLOSED WITNESS -- an INTEGER operand at a float type is a TYPE ERROR, not a wrong number and not a refusal. ir_as_float declines IRScalar.int_ even though both constructors carry a Nat, which is exactly why EncodesF64Val cannot be EncodesU64Val. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_F32, "FAIL-CLOSED WITNESS -- the SAME operands at binary32 are UNMODELLED. 1.0 * 2.0 answers at f64 (ir_fm_one_times_two, one screen up) and is refused at f32, because binary32's exponent field is 8 bits wide and this module's boundary constants are binary64's. The width on the instruction is semantic input; a transcription that got it wrong would compute this instead of that. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_UMUL_CONTRAST, "*** THE CONTRAST WITNESS. *** Integer multiplication at u8 WRAPS: 16 * 16 is 256, and the canonical width-8 residue of 256 is 0, so the same ir_binop_eval that overflows fmul to an infinity (ir_fm_overflow_to_inf) answers ZERO here. Two lines apart in the same dispatch, on the same shape of instruction. Registered so that `float multiplication is not integer multiplication at another type` is a kernel-executed fact in this repository rather than a sentence in a module comment. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_CORRECT_WITNESS, "ir_fm_correct_witness: A4's premises are all SATISFIABLE, discharged concretely -- the empty heap, an undef closure environment pointer (which the body never reads), the exact fuel bound by Le.refl, and two EncodesF64Val.mk. Both bit patterns stay universally quantified. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
