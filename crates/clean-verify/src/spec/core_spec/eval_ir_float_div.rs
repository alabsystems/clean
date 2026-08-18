// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The EIGHTH complete width-one chain — and the first over FLOAT
//! ARITHMETIC: `env::native_reducers_float::reduce_float_div::{closure#0}`.**
//!
//! ```text
//! pub(crate) fn reduce_float_div(args: &[&Expr]) -> Option<Expr> {
//!     float_binary_op(args, |a, b| a / b)     // <- THIS closure
//! }
//! ```
//!
//! ```text
//! rustcc fn @env::native_reducers_float::reduce_float_div::{closure#0}(functy.551) {
//!     ; #producer: trust
//!     ; #names: %1="a", %2="b"
//! bb0(%0: ptr, %1: f64, %2: f64):
//!     %3 = fdiv f64 %1, %2  ; #loc: 354 222 33
//!     ret %3  ; #loc: 354 222 38
//! }
//! ```
//!
//! One block. Two instructions. Three parameters. It is **not** the smallest
//! chainable body — 106 of the 177 chainable bodies are ONE instruction, and
//! measured, every one of those is a bare `ret`. What makes this one small in
//! the way that matters is the OPERATOR census: across all 177, trust-ir emits
//! `const` 116 times, `extractfield` 37, `insertfield` 22, `load` 15, `icmp` 11,
//! `zext` 2, `trunc` 1, `and` 1, `or` 1 — and `fadd`/`fsub`/`fmul`/`fdiv`
//! EXACTLY ONE EACH. Float arithmetic is four instructions in the entire
//! chainable set, and this chain covers one of them.
//!
//! Being two instructions is still the reason it forced two new CFG lanes:
//! every one of the seven earlier chains would have passed a gate over this
//! body while the transcription said something else (§ below).
//!
//! ## Why this body and not `fadd` / `fsub` / `fmul`
//!
//! All four are structurally identical (1 block, 2 instrs, 6 canonical lines, 4
//! real marker lines, 64 interpreter samples, `unsupported: []`, 0 calls, and a
//! codegen flip whose lineage equals its coverage row's — measured, all four).
//! `fdiv` was chosen on semantic content, and the reasons are checkable rather
//! than aesthetic:
//!
//! 1. **It is the one float operator whose semantics CONTRADICTS its integer
//!    sibling in this very specification.** `ir_binop_eval IRBinOp.udiv` on a
//!    zero divisor is `IROutcome.ub IRFault.div_zero`; `IRBinOp.fdiv` on a zero
//!    divisor is a signed infinity. Registering it proves the float lane is not
//!    a rename of the integer lane. `ir_fd_udiv_traps_where_fdiv_answers` is
//!    that contrast, executed by the kernel, side by side.
//! 2. **It is non-commutative**, so the operand ORDER is semantically
//!    observable: `ir_fd_order_is_observable` runs the machine on the same two
//!    values in the two orders and gets `+inf` one way and `+0` the other.
//! 3. **Its exactly-determined fragment is the largest of the four.** Every one
//!    of the 4x4 class combinations has a determined answer except `0/0` and
//!    `inf/inf` (invalid operations, NaN payload implementation-defined) and
//!    `fin/fin` (rounding) — and the NaN rows, which no operator can answer.
//!
//! **2026-08-16: that third reason is now the reverse of what it was, and the
//! chain is unchanged by it.** The finite fragment landed for `fadd`, `fsub`
//! and `fmul` ([`super::eval_ir_float_fin`]) and NOT for `fdiv`, whose
//! significand is itself a division — so `fdiv` went from having the largest
//! determined fragment of the four to having the smallest. `env_reduce_float_div`
//! is still `ir_f64_div` and `ir_f64_div`'s `fin`/`fin` cell is still
//! `IROption.none`, so every theorem below states exactly what it stated
//! before: A4's domain boundary did not move for THIS operator. What moved is
//! the reason — `ir_fd_two_over_one_refused` is now refused for a measured
//! property of division rather than for a blanket property of rounding, and its
//! comment says so.
//!
//! ## The two NEW CFG lanes, and why a body this small needed them
//!
//! The emitted body's op token `fdiv` was already carried by the `binops` lane
//! (`ARITH` has listed `fadd`..`frem` since that lane existed). What was NOT
//! carried is what makes this body mean anything:
//!
//! * **the operand TYPE.** `fdiv f32 %1, %2` and `fdiv f64 %1, %2` differ in no
//!   lane the gate had, and they are different operations — binary32 has an
//!   8-bit exponent field and this semantics decides only binary64, so a
//!   transcription at `IRTy.float_ 32` computes `unmodelled` where the artifact
//!   computes a value. The `binop_tys` / `icmp_tys` lanes close it, for every
//!   chain at once (the earlier chains' `u8` / `u32` / `u64` were equally
//!   uncompared).
//! * **the RETURNED value id.** This body is one binop and one `ret`. A
//!   transcription that returned `%1` — the DIVIDEND — instead of `%3` agreed
//!   with every single lane the gate had: same block, same binop, same operands,
//!   same result id, no branch, no switch, no constant. The `rets` lane closes
//!   it, again for every chain at once.
//!
//! Both are gated by perturbation, both directions, in
//! `tests/crystal_a1_lineage/float_div.rs`.
//!
//! ## What the refinement theorem says, and the shape it had to take
//!
//! Every earlier chain's A4 concludes `IROutcome.ret …`. This one cannot and
//! must not: the float value domain is PARTIAL by construction
//! ([`super::eval_ir_float`] states which fragment and the measured reason for
//! the boundary), so for a NaN operand, for `0/0`, and for finite/finite the
//! machine's honest answer is `IROutcome.unmodelled IRFault.float_domain`.
//!
//! So `ir_fd_correct` is TOTAL over a richer right-hand side: for every pair of
//! bit patterns, every environment pointer, every heap and every fuel at or
//! above 2, the machine returns exactly `ir_fd_res (env_reduce_float_div a b)` —
//! **the value when the fragment is modelled and the tagged refusal when it is
//! not**. That is strictly stronger than a theorem restricted to the modelled
//! fragment: it proves the emitted body's refusals are the reflected function's
//! refusals, which is the only interesting content a partial semantics has.
//!
//! Getting there needed fuel monotonicity for a NON-`ret` outcome, which
//! `ir_run_le_ret` does not provide and cannot (it is stated for returns because
//! the unconditional form is false — a run that exhausts at `f` may halt at
//! `succ f`). `ir_fd_run_le` is the same induction with the same discriminator
//! discipline, over the two-constructor image of `ir_fd_res`: `IROption.rec`
//! shows that image never contains `fuel_out`, and that is what makes the
//! monotonicity true here.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! `env_reduce_float_div` is `ir_f64_div`, and `ir_f64_div` is **not proved to
//! be `f64::div`**. It is IEEE 754 on the classified fragment by construction
//! and by reading, and a tagged refusal elsewhere. The gap between it and the
//! hardware divider is stated in [`super::eval_ir_float`] and closed nowhere.
//! This is the same shape of gap [`super::eval_ir_valid_char`] states for
//! `env_is_valid_char` (a `u64`-level specification, not the Unicode predicate),
//! and it is LARGER, because a float format has more structure than an interval
//! test. A reader who wants "Clean proved the kernel's float division correct"
//! will not find it here and should not say it.
//!
//! The link between the proved module and the emitted one is STRUCTURAL —
//! `tests/crystal_a1_lineage/float_div.rs`. Everything past the flip seam is
//! downstream and covered by nothing here. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// `ir_nl3` / `ir_vl3` are NOT declared here. The FIFTH chain
// (`expr::bvar_in_range`, `eval_ir_bvar_range.rs`) already registers them — it
// also takes three parameters — and this stage runs after it. Re-declaring them
// was this chain's ONE real error, and it is worth the comment: the EvalIR
// bundle does not carry that stage, so the duplicate elaborated cleanly in every
// fast gate and failed only in the full `Specification::new()`, at 27 minutes an
// attempt. A name that already exists is a name to REUSE.
//
// The diagnosis route is worth recording too, because it is the one this
// repository already built for exactly this: with the stage temporarily
// disabled, `tests/spec_scratchpad.rs` elaborated all 45 declarations of this
// module against ONE full spec build and reported each independently —
// 45/45 PASS, 1.24 s of declaration time inside a 1,619 s build, the most
// expensive single declaration being `ir_fd_machine_sound` at 0.139 s.

// ── the reflected closure, its representation premise, its outcome ────
const SRC_IR_FD_TF64: &str = "def ir_fd_tf64 : IRTy := IRTy.float_ 64";
const SRC_ENV_REDUCE_FLOAT_DIV: &str =
    "def env_reduce_float_div (a : Nat) (b : Nat) : IROption Nat := ir_f64_div a b";
const SRC_ENCODESF64VAL: &str = "inductive EncodesF64Val : IRScalar -> Nat -> Type\n| mk : forall (n : Nat), EncodesF64Val (IRScalar.float_ n) n";
const SRC_IR_FD_RES: &str = "def ir_fd_res (o : IROption Nat) : IROutcome := IROption.rec Nat (fun (_ : IROption Nat) => IROutcome) (IROutcome.unmodelled IRFault.float_domain) (fun (k : Nat) => IROutcome.ret (ir_vl1 (IRScalar.float_ k))) o";

// ── the emitted module, transcribed ───────────────────────────────────
const SRC_IR_FD_B0: &str = "def ir_fd_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.binop IRBinOp.fdiv ir_fd_tf64 ir_d1 ir_d2) ir_d3) (ir_nd (IRInst.ret (ir_nl1 ir_d3))))";
const SRC_IR_FD_FUNC: &str = "def ir_fd_func : IRFunc := IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0 (ir_blk ir_fd_b0 ir_blk0)";
const SRC_IR_FD_MODULE: &str = "def ir_fd_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_fd_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

// ── the machine ───────────────────────────────────────────────────────
const SRC_IR_FD_MACH0: &str = "def ir_fd_mach0 (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl3 ir_d0 ir_d1 ir_d2) (ir_vl3 p (IRScalar.float_ a) (IRScalar.float_ b)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";
const SRC_IR_FD_M1: &str = "def ir_fd_m1 (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) (o : IROption Nat) : IRConfig := ir_bind_result (ir_fd_mach0 p a b mem na) (ir_nl1 ir_d3) (ir_f64_result o)";
const SRC_IR_FD_ONE_STEP: &str = "def ir_fd_one_step (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_steps ir_d1 ir_fd_module (IRConfig.running (ir_fd_mach0 p a b mem na))) (ir_fd_m1 p a b mem na (env_reduce_float_div a b)) := Eq.refl IRConfig (ir_fd_m1 p a b mem na (env_reduce_float_div a b))";
const SRC_IR_FD_SPLIT: &str = "def ir_fd_split (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) (o : IROption Nat) : Eq IROutcome (ir_run ir_d1 ir_fd_module (ir_fd_m1 p a b mem na o)) (ir_fd_res o) := IROption.rec Nat (fun (o0 : IROption Nat) => Eq IROutcome (ir_run ir_d1 ir_fd_module (ir_fd_m1 p a b mem na o0)) (ir_fd_res o0)) (Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)) (fun (k : Nat) => Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) o";
const SRC_IR_FD_EXACT: &str = "def ir_fd_exact (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d2 ir_fd_module (IRConfig.running (ir_fd_mach0 p a b mem na))) (ir_fd_res (env_reduce_float_div a b)) := Eq.trans IROutcome (ir_run ir_d2 ir_fd_module (IRConfig.running (ir_fd_mach0 p a b mem na))) (ir_run ir_d1 ir_fd_module (ir_steps ir_d1 ir_fd_module (IRConfig.running (ir_fd_mach0 p a b mem na)))) (ir_fd_res (env_reduce_float_div a b)) (ir_run_steps_split ir_fd_module ir_d1 ir_d1 (IRConfig.running (ir_fd_mach0 p a b mem na))) (Eq.subst IRConfig (fun (c : IRConfig) => Eq IROutcome (ir_run ir_d1 ir_fd_module c) (ir_fd_res (env_reduce_float_div a b))) (ir_fd_m1 p a b mem na (env_reduce_float_div a b)) (ir_steps ir_d1 ir_fd_module (IRConfig.running (ir_fd_mach0 p a b mem na))) (Eq.symm IRConfig (ir_steps ir_d1 ir_fd_module (IRConfig.running (ir_fd_mach0 p a b mem na))) (ir_fd_m1 p a b mem na (env_reduce_float_div a b)) (ir_fd_one_step p a b mem na)) (ir_fd_split p a b mem na (env_reduce_float_div a b)))";

// ── fuel monotonicity for an outcome that may be a REFUSAL ────────────
const SRC_FUELOUT_NE_UNMODELLED: &str = "def ir_outcome_fuelout_ne_unmodelled_prop (f : IRFault) (C : Prop) (h : Eq IROutcome IROutcome.fuel_out (IROutcome.unmodelled f)) : C := Eq.subst IROutcome (fun (o : IROutcome) => IROutcome.rec (fun (_ : IROutcome) => Prop) (fun (_ : IRList IRScalar) => (Eq Nat Nat.zero Nat.zero)) (fun (_ : IRFault) => (Eq Nat Nat.zero Nat.zero)) (fun (_ : IRFault) => (Eq Nat Nat.zero Nat.zero)) (fun (_ : IRFault) => C) (fun (_ : IRFault) => (Eq Nat Nat.zero Nat.zero)) (Eq Nat Nat.zero Nat.zero) o) IROutcome.fuel_out (IROutcome.unmodelled f) h (Eq.refl Nat Nat.zero)";
const SRC_IR_FD_FUELOUT_ABSURD: &str = "def ir_fd_fuelout_absurd (o : IROption Nat) (C : Prop) : Eq IROutcome IROutcome.fuel_out (ir_fd_res o) -> C := IROption.rec Nat (fun (o0 : IROption Nat) => Eq IROutcome IROutcome.fuel_out (ir_fd_res o0) -> C) (fun (h : Eq IROutcome IROutcome.fuel_out (IROutcome.unmodelled IRFault.float_domain)) => ir_outcome_fuelout_ne_unmodelled_prop IRFault.float_domain C h) (fun (k : Nat) (h : Eq IROutcome IROutcome.fuel_out (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) => ir_outcome_fuelout_ne_ret_prop (ir_vl1 (IRScalar.float_ k)) C h) o";
const SRC_IR_FD_RUN_SUCC: &str = "def ir_fd_run_succ (f : Nat) : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fd_module c) (ir_fd_res o) -> Eq IROutcome (ir_run (Nat.succ f) ir_fd_module c) (ir_fd_res o) := Nat.rec (fun (k : Nat) => forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run k ir_fd_module c) (ir_fd_res o) -> Eq IROutcome (ir_run (Nat.succ k) ir_fd_module c) (ir_fd_res o)) (fun (c : IRConfig) (o : IROption Nat) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run Nat.zero ir_fd_module c0) (ir_fd_res o) -> Eq IROutcome (ir_run (Nat.succ Nat.zero) ir_fd_module c0) (ir_fd_res o)) (fun (s : IRMachine) (h : Eq IROutcome (ir_run Nat.zero ir_fd_module (IRConfig.running s)) (ir_fd_res o)) => ir_fd_fuelout_absurd o (Eq IROutcome (ir_run (Nat.succ Nat.zero) ir_fd_module (IRConfig.running s)) (ir_fd_res o)) h) (fun (x : IROutcome) (h : Eq IROutcome (ir_run Nat.zero ir_fd_module (IRConfig.halted x)) (ir_fd_res o)) => h) c) (fun (k : Nat) (ih : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run k ir_fd_module c) (ir_fd_res o) -> Eq IROutcome (ir_run (Nat.succ k) ir_fd_module c) (ir_fd_res o)) (c : IRConfig) (o : IROption Nat) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run (Nat.succ k) ir_fd_module c0) (ir_fd_res o) -> Eq IROutcome (ir_run (Nat.succ (Nat.succ k)) ir_fd_module c0) (ir_fd_res o)) (fun (s : IRMachine) => ih (ir_step ir_fd_module s) o) (fun (x : IROutcome) (h : Eq IROutcome (ir_run (Nat.succ k) ir_fd_module (IRConfig.halted x)) (ir_fd_res o)) => h) c) f";
const SRC_IR_FD_RUN_LE: &str = "def ir_fd_run_le (f : Nat) (g : Nat) (hle : Le f g) : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fd_module c) (ir_fd_res o) -> Eq IROutcome (ir_run g ir_fd_module c) (ir_fd_res o) := Le.rec f (fun (g0 : Nat) (_hg : Le f g0) => forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fd_module c) (ir_fd_res o) -> Eq IROutcome (ir_run g0 ir_fd_module c) (ir_fd_res o)) (fun (c : IRConfig) (o : IROption Nat) (h : Eq IROutcome (ir_run f ir_fd_module c) (ir_fd_res o)) => h) (fun (g2 : Nat) (_h2 : Le f g2) (ih : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fd_module c) (ir_fd_res o) -> Eq IROutcome (ir_run g2 ir_fd_module c) (ir_fd_res o)) (c : IRConfig) (o : IROption Nat) (h : Eq IROutcome (ir_run f ir_fd_module c) (ir_fd_res o)) => ir_fd_run_succ g2 c o (ih c o h)) g hle";

// ── A4, A5, and the corollaries ───────────────────────────────────────
const SRC_IR_FD_CORRECT: &str = "def ir_fd_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (ra : IRScalar) (rb : IRScalar) (a : Nat) (b : Nat) (ha : EncodesF64Val ra a) (hb : EncodesF64Val rb b) : Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem na) (ir_fd_res (env_reduce_float_div a b)) := EncodesF64Val.rec (fun (ra0 : IRScalar) (a0 : Nat) (_ : EncodesF64Val ra0 a0) => forall (rb0 : IRScalar) (b0 : Nat), EncodesF64Val rb0 b0 -> Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra0 rb0) mem na) (ir_fd_res (env_reduce_float_div a0 b0))) (fun (x : Nat) => fun (rb0 : IRScalar) (b0 : Nat) (hb0 : EncodesF64Val rb0 b0) => EncodesF64Val.rec (fun (rb1 : IRScalar) (b1 : Nat) (_ : EncodesF64Val rb1 b1) => Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p (IRScalar.float_ x) rb1) mem na) (ir_fd_res (env_reduce_float_div x b1))) (fun (y : Nat) (hle : Le ir_d2 fuel) => ir_fd_run_le ir_d2 fuel hle (IRConfig.running (ir_fd_mach0 p x y mem na)) (env_reduce_float_div x y) (ir_fd_exact p x y mem na)) rb0 b0 hb0) ra a ha rb b hb";
const SRC_IR_FD_HEAD_FLOAT: &str = "def ir_fd_head_float (v : IRList IRScalar) : Nat := IRList.rec IRScalar (fun (_ : IRList IRScalar) => Nat) Nat.zero (fun (x : IRScalar) (_ : IRList IRScalar) (_ : Nat) => ir_scalar_code x) v";
const SRC_IR_FD_ANSWER: &str = "def ir_fd_answer (o : IROutcome) : IROption Nat := IROutcome.rec (fun (_ : IROutcome) => IROption Nat) (fun (v : IRList IRScalar) => IROption.some Nat (ir_fd_head_float v)) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (IROption.none Nat) o";
const SRC_IR_FD_ANSWER_RES: &str = "def ir_fd_answer_res (o : IROption Nat) : Eq (IROption Nat) (ir_fd_answer (ir_fd_res o)) o := IROption.rec Nat (fun (o0 : IROption Nat) => Eq (IROption Nat) (ir_fd_answer (ir_fd_res o0)) o0) (Eq.refl (IROption Nat) (IROption.none Nat)) (fun (k : Nat) => Eq.refl (IROption Nat) (IROption.some Nat k)) o";
const SRC_IR_FD_MACHINE_SOUND: &str = "def ir_fd_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (ra : IRScalar) (rb : IRScalar) (a : Nat) (b : Nat) (k : Nat) (ha : EncodesF64Val ra a) (hb : EncodesF64Val rb b) (hle : Le ir_d2 fuel) (hret : Eq IROutcome (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem na) (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) : Eq (IROption Nat) (env_reduce_float_div a b) (IROption.some Nat k) := Eq.trans (IROption Nat) (env_reduce_float_div a b) (ir_fd_answer (ir_fd_res (env_reduce_float_div a b))) (IROption.some Nat k) (Eq.symm (IROption Nat) (ir_fd_answer (ir_fd_res (env_reduce_float_div a b))) (env_reduce_float_div a b) (ir_fd_answer_res (env_reduce_float_div a b))) (Eq.cong IROutcome (IROption Nat) ir_fd_answer (ir_fd_res (env_reduce_float_div a b)) (IROutcome.ret (ir_vl1 (IRScalar.float_ k))) (Eq.trans IROutcome (ir_fd_res (env_reduce_float_div a b)) (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem na) (IROutcome.ret (ir_vl1 (IRScalar.float_ k))) (Eq.symm IROutcome (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem na) (ir_fd_res (env_reduce_float_div a b)) (ir_fd_correct mem fuel na p ra rb a b ha hb hle)) hret))";

// A5 REACHING PAST THE ANSWER, ONTO THE ARGUMENTS: division by zero.
const SRC_IR_FD_DIV_FIN_ZERO: &str = "def ir_f64_div_fin_zero (a : Nat) (b : Nat) (hfin : Eq IRF64Class (ir_f64_class a) IRF64Class.fin_) (hzero : Eq IRF64Class (ir_f64_class b) IRF64Class.zero_) : Eq (IROption Nat) (ir_f64_div a b) (IROption.some Nat (ir_f64_qinf a b)) := Eq.trans (IROption Nat) (ir_f64_div_at a b (ir_f64_class a) (ir_f64_class b)) (ir_f64_div_at a b IRF64Class.fin_ (ir_f64_class b)) (IROption.some Nat (ir_f64_qinf a b)) (Eq.cong IRF64Class (IROption Nat) (fun (c : IRF64Class) => ir_f64_div_at a b c (ir_f64_class b)) (ir_f64_class a) IRF64Class.fin_ hfin) (Eq.cong IRF64Class (IROption Nat) (fun (c : IRF64Class) => ir_f64_div_at a b IRF64Class.fin_ c) (ir_f64_class b) IRF64Class.zero_ hzero)";
const SRC_IR_OPTION_GET: &str = "def ir_option_get (o : IROption Nat) : Nat := IROption.rec Nat (fun (_ : IROption Nat) => Nat) Nat.zero (fun (k : Nat) => k) o";
const SRC_IR_FD_MACHINE_SOUND_DIVZERO: &str = "def ir_fd_machine_sound_divzero (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (ra : IRScalar) (rb : IRScalar) (a : Nat) (b : Nat) (k : Nat) (ha : EncodesF64Val ra a) (hb : EncodesF64Val rb b) (hle : Le ir_d2 fuel) (hfin : Eq IRF64Class (ir_f64_class a) IRF64Class.fin_) (hzero : Eq IRF64Class (ir_f64_class b) IRF64Class.zero_) (hret : Eq IROutcome (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem na) (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) : Eq Nat (ir_f64_qinf a b) k := Eq.cong (IROption Nat) Nat ir_option_get (IROption.some Nat (ir_f64_qinf a b)) (IROption.some Nat k) (Eq.trans (IROption Nat) (IROption.some Nat (ir_f64_qinf a b)) (env_reduce_float_div a b) (IROption.some Nat k) (Eq.symm (IROption Nat) (env_reduce_float_div a b) (IROption.some Nat (ir_f64_qinf a b)) (ir_f64_div_fin_zero a b hfin hzero)) (ir_fd_machine_sound mem fuel na p ra rb a b k ha hb hle hret))";

const SRC_IR_OPTION_IS_SOME: &str = "def ir_option_is_some (o : IROption Nat) : Bool := IROption.rec Nat (fun (_ : IROption Nat) => Bool) Bool.false (fun (_ : Nat) => Bool.true) o";
const SRC_IR_FD_RES_IS_RET: &str = "def ir_fd_res_is_ret (o : IROption Nat) : Eq Bool (ir_outcome_is_ret (ir_fd_res o)) (ir_option_is_some o) := IROption.rec Nat (fun (o0 : IROption Nat) => Eq Bool (ir_outcome_is_ret (ir_fd_res o0)) (ir_option_is_some o0)) (Eq.refl Bool Bool.false) (fun (_ : Nat) => Eq.refl Bool Bool.true) o";
const SRC_IR_FD_RETURNS_IFF_MODELLED: &str = "def ir_fd_returns_iff_modelled (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (ra : IRScalar) (rb : IRScalar) (a : Nat) (b : Nat) (ha : EncodesF64Val ra a) (hb : EncodesF64Val rb b) (hle : Le ir_d2 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem na)) (ir_option_is_some (env_reduce_float_div a b)) := Eq.trans Bool (ir_outcome_is_ret (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem na)) (ir_outcome_is_ret (ir_fd_res (env_reduce_float_div a b))) (ir_option_is_some (env_reduce_float_div a b)) (Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem na) (ir_fd_res (env_reduce_float_div a b)) (ir_fd_correct mem fuel na p ra rb a b ha hb hle)) (ir_fd_res_is_ret (env_reduce_float_div a b))";

const SRC_IR_OUTCOME_IS_TRAP: &str = "def ir_outcome_is_trap (o : IROutcome) : Bool := IROutcome.rec (fun (_ : IROutcome) => Bool) (fun (_ : IRList IRScalar) => Bool.false) (fun (_ : IRFault) => Bool.true) (fun (_ : IRFault) => Bool.true) (fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.true) Bool.true o";
const SRC_IR_FD_RES_NEVER_TRAPS: &str = "def ir_fd_res_never_traps (o : IROption Nat) : Eq Bool (ir_outcome_is_trap (ir_fd_res o)) Bool.false := IROption.rec Nat (fun (o0 : IROption Nat) => Eq Bool (ir_outcome_is_trap (ir_fd_res o0)) Bool.false) (Eq.refl Bool Bool.false) (fun (_ : Nat) => Eq.refl Bool Bool.false) o";
const SRC_IR_FD_NEVER_TRAPS: &str = "def ir_fd_never_traps (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (ra : IRScalar) (rb : IRScalar) (a : Nat) (b : Nat) (ha : EncodesF64Val ra a) (hb : EncodesF64Val rb b) (hle : Le ir_d2 fuel) : Eq Bool (ir_outcome_is_trap (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem na)) Bool.false := Eq.trans Bool (ir_outcome_is_trap (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem na)) (ir_outcome_is_trap (ir_fd_res (env_reduce_float_div a b))) Bool.false (Eq.cong IROutcome Bool ir_outcome_is_trap (ir_eval fuel ir_fd_module ir_d0 (ir_vl3 p ra rb) mem na) (ir_fd_res (env_reduce_float_div a b)) (ir_fd_correct mem fuel na p ra rb a b ha hb hle)) (ir_fd_res_never_traps (env_reduce_float_div a b))";

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
const SRC_W_ONE_OVER_PLUS_ZERO: &str = "def ir_fd_one_over_plus_zero : Eq IROutcome (ir_eval ir_d2 ir_fd_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312)))";
const SRC_W_ONE_OVER_MINUS_ZERO: &str = "def ir_fd_one_over_minus_zero : Eq IROutcome (ir_eval ir_d2 ir_fd_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 9223372036854775808)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 18442240474082181120))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 18442240474082181120)))";
const SRC_W_MINUS_ONE_OVER_PLUS_ZERO: &str = "def ir_fd_minus_one_over_plus_zero : Eq IROutcome (ir_eval ir_d2 ir_fd_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 13830554455654793216) (IRScalar.float_ 0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 18442240474082181120))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 18442240474082181120)))";
const SRC_W_ONE_OVER_INF: &str = "def ir_fd_one_over_inf : Eq IROutcome (ir_eval ir_d2 ir_fd_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 9218868437227405312)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 0)))";
const SRC_W_MINUS_ZERO_OVER_INF: &str = "def ir_fd_minus_zero_over_inf : Eq IROutcome (ir_eval ir_d2 ir_fd_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9223372036854775808) (IRScalar.float_ 9218868437227405312)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 9223372036854775808))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 9223372036854775808)))";
const SRC_W_INF_OVER_INF: &str = "def ir_fd_inf_over_inf_refused : Eq IROutcome (ir_eval ir_d2 ir_fd_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 9218868437227405312)) ir_mem0 ir_d0) (IROutcome.unmodelled IRFault.float_domain) := Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)";
const SRC_W_ZERO_OVER_ZERO: &str = "def ir_fd_zero_over_zero_refused : Eq IROutcome (ir_eval ir_d2 ir_fd_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 0) (IRScalar.float_ 0)) ir_mem0 ir_d0) (IROutcome.unmodelled IRFault.float_domain) := Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)";
const SRC_W_FIN_OVER_FIN: &str = "def ir_fd_two_over_one_refused : Eq IROutcome (ir_eval ir_d2 ir_fd_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4611686018427387904) (IRScalar.float_ 4607182418800017408)) ir_mem0 ir_d0) (IROutcome.unmodelled IRFault.float_domain) := Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)";
const SRC_W_NAN: &str = "def ir_fd_nan_operand_refused : Eq IROutcome (ir_eval ir_d2 ir_fd_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9221120237041090560) (IRScalar.float_ 4607182418800017408)) ir_mem0 ir_d0) (IROutcome.unmodelled IRFault.float_domain) := Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)";
const SRC_W_ORDER: &str = "def ir_fd_order_is_observable : Eq IROutcome (ir_eval ir_d2 ir_fd_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 0) (IRScalar.float_ 4607182418800017408)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 0)))";
const SRC_W_INT_OPERAND: &str = "def ir_fd_integer_operand_is_a_type_error : Eq IRStepResult (ir_binop_eval IRBinOp.fdiv ir_fd_tf64 (IRScalar.int_ 1) (IRScalar.int_ 0)) (IRStepResult.fault (IROutcome.type_error IRFault.not_float)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_float))";
const SRC_W_F32: &str = "def ir_fd_binary32_is_unmodelled : Eq IRStepResult (ir_binop_eval IRBinOp.fdiv (IRTy.float_ 32) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 0)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";
const SRC_W_UDIV_CONTRAST: &str = "def ir_fd_udiv_traps_where_fdiv_answers : Eq IRStepResult (ir_binop_eval IRBinOp.udiv (IRTy.uint_ 8) (IRScalar.int_ 1) (IRScalar.int_ 0)) (IRStepResult.fault (IROutcome.ub IRFault.div_zero)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.ub IRFault.div_zero))";
const SRC_W_CORRECT_WITNESS: &str = "def ir_fd_correct_witness (a : Nat) (b : Nat) : Eq IROutcome (ir_eval ir_d2 ir_fd_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ a) (IRScalar.float_ b)) ir_mem0 ir_d0) (ir_fd_res (env_reduce_float_div a b)) := ir_fd_correct ir_mem0 ir_d2 ir_d0 IRScalar.undef_ (IRScalar.float_ a) (IRScalar.float_ b) a b (EncodesF64Val.mk a) (EncodesF64Val.mk b) (Le.refl ir_d2)";
const SRC_W_DIVZERO_WITNESS: &str = "def ir_fd_machine_sound_divzero_witness : Eq Nat (ir_f64_qinf 4607182418800017408 0) 9218868437227405312 := ir_fd_machine_sound_divzero ir_mem0 ir_d2 ir_d0 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 0) 4607182418800017408 0 9218868437227405312 (EncodesF64Val.mk 4607182418800017408) (EncodesF64Val.mk 0) (Le.refl ir_d2) (Eq.refl IRF64Class IRF64Class.fin_) (Eq.refl IRF64Class IRF64Class.zero_) ir_fd_one_over_plus_zero";

impl Specification {
    /// Register the EIGHTH complete width-one chain, and the first over float
    /// arithmetic: `env::native_reducers_float::reduce_float_div::{closure#0}`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_float_div(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_IR_FD_TF64, "ir_fd_tf64: f64 -- binary64, the type the emitted fdiv is at. Not decoration and not a width that happens to be right: ir_float_binop reads the width off it and DECIDES only 64, giving every other float width the tagged unmodelled outcome, because binary32 has an 8-bit exponent field and a different infinity boundary. A transcription at IRTy.float_ 32 computes `unmodelled` where the artifact computes a value, and it is invisible to every CFG lane that existed before the binop_tys lane. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ENV_REDUCE_FLOAT_DIV, "env_reduce_float_div: the reflected env::native_reducers_float::reduce_float_div::{closure#0} (native_reducers_float.rs:222), which is `|a, b| a / b` on f64. It is ir_f64_div -- the classified binary64 division of super::eval_ir_float -- and NOT a proof that ir_f64_div is the hardware divider. That gap is stated in that module and closed nowhere; it is the same shape as env_is_valid_char's (a u64-level specification, not the Unicode predicate) and it is larger. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESF64VAL, "EncodesF64Val r n: the runtime value r is the binary64 bit pattern n. \n\nDeliberately NOT a reuse of EncodesU64Val, even though the two inductives have the same shape and the same width. That relation says the argument arrived as an INTEGER scalar; this one says it arrived as a FLOAT scalar, and the difference is load-bearing rather than nominal: ir_as_float declines IRScalar.int_ n, so with EncodesU64Val's conclusion in its place A4 would be FALSE -- the machine would answer type_error not_float where the theorem claims a value. It is the thinnest premise the program has, tied with EncodesU32Val and EncodesU64Val: one by-value scalar, no memory, no aggregate. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_RES, "ir_fd_res: the outcome a classified float answer produces -- the returned value when the fragment is modelled, and IROutcome.unmodelled IRFault.float_domain when it is not. \n\nThis is the declaration that lets the eighth chain's A4 be TOTAL. Every earlier chain concludes IROutcome.ret; a partial value domain cannot, and restricting A4 to the modelled fragment would have thrown away the more interesting half -- that the emitted body's REFUSALS are exactly the reflected function's refusals. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_B0, "ir_fd_b0: THE WHOLE BODY, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/float_div.trust-ir.txt). One fdiv at f64 over %1 and %2 in that order into %3, then `ret %3`. \n\nTwo things here are checked by CFG lanes that did not exist before this chain: the TYPE on the binop (f64, not f32 and not u64) and the RETURNED id (%3, the quotient -- not %1, the dividend). A transcription that returned %1 agreed with every lane the gate had, on a body with nothing else in it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_FUNC, "ir_fd_func: the closure as EvalIR -- THREE parameters (%0 the closure environment pointer, %1 and %2 the operands), entry block 0, one block. %0 is bound and never read, and that is not an assumption: the producer's own interpreter differential records `1 proven-never-read opaque param(s) as placeholders` for this body, and A4 quantifies over it with no premise at all. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_MODULE, "ir_fd_module: the module for env::native_reducers_float::reduce_float_div::{closure#0}, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel, recorded at tests/fixtures/float_div.trust-ir.txt and checked graph-for-graph and instruction-for-instruction, including the new type and ret lanes, by tests/crystal_a1_lineage/float_div.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_MACH0, "ir_fd_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds THREE parameters positionally. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_M1, "ir_fd_m1: the machine after the fdiv, with the CLASSIFIED ANSWER ABSTRACTED to an IROption parameter. The same device the fifth and sixth chains use for a condbr's scrutinee, at a different type and for the same reason: ir_f64_result dispatches with IROption.rec, and on symbolic bit patterns ir_f64_div is stuck under ir_f64_class, so the machine is stuck there and no fuel unsticks it. At o := env_reduce_float_div a b this term is DEFINITIONALLY one ir_step of ir_fd_mach0. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_ONE_STEP, "ir_fd_one_step: ONE step of the machine IS ir_fd_m1 at the real classified answer. Eq.refl -- the kernel runs one step and compares two configurations, both of which carry the classification unreduced, so the check is bounded by the size of one instruction's semantics rather than by a 64-bit residue. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_SPLIT, "ir_fd_split: THE CASE ANALYSIS, over the boundary of the modelled fragment. If the classified answer is `some k` the machine binds the float and the second step returns it; if it is `none` the fdiv FAULTS and ir_bind_result halts immediately, so the remaining step is spent on an already-halted configuration. Both minors are Eq.refl -- once the IROption is a constructor the machine computes. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_EXACT, "ir_fd_exact: the machine agrees with the reflected closure at EXACTLY 2 steps, for every pair of bit patterns. 2 = 1 + 1, and the proof is that split: ir_run_steps_split peels the first step, ir_fd_one_step identifies the resulting configuration, and the case analysis finishes the second. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_FUELOUT_NE_UNMODELLED, "ir_outcome_fuelout_ne_unmodelled_prop: fuel exhaustion is not an unmodelled verdict. The twin of ir_outcome_fuelout_ne_ret_prop at the fourth IROutcome constructor, and it exists because this chain's outcome may be a refusal rather than a return -- so the existing discriminator alone cannot carry the fuel induction. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_FUELOUT_ABSURD, "ir_fd_fuelout_absurd: nothing in the IMAGE of ir_fd_res is fuel_out. By IROption.rec: `none` lands on unmodelled and `some k` on ret, and each has its own discriminator. This is the fact that makes fuel monotonicity TRUE for this chain's outcome shape -- the unconditional monotonicity statement is false precisely because a run that exhausts at f may halt at succ f, and this rules exhaustion out of the conclusion rather than assuming it away. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_RUN_SUCC, "ir_fd_run_succ: FUEL MONOTONICITY for an outcome that may be a REFUSAL. ir_run_le_ret is stated for IROutcome.ret and cannot be widened in place; this is the same Nat.rec-over-fuel with an IRConfig.rec convoy, at the ir_fd_res image, with ir_fd_fuelout_absurd where the ret version uses ir_outcome_fuelout_ne_ret_prop. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_RUN_LE, "ir_fd_run_le: the same at a bound rather than a successor, by Le.rec iterating ir_fd_run_succ. Note Le's first argument is a PARAMETER, so Le.rec takes it before the motive. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_CORRECT, "ir_fd_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE, FOR FLOAT ARITHMETIC. *** For every pair of binary64 bit patterns a and b, every pair of values representing them, every closure environment pointer, every heap, every next-address counter and every fuel at or above 2, ir_eval on ir_fd_module returns exactly ir_fd_res (env_reduce_float_div a b). \n\nTOTAL, not restricted to the modelled fragment: where the classified division answers, the machine returns that float; where it refuses, the machine returns the tagged unmodelled outcome and nothing else. The first chain in this program whose A4 conclusion is not an IROutcome.ret, and the first over a body that computes with floats at all. \n\nA0 is measured on the SHIPPED kernel: lowered, spliced, unsupported [], derived_mir.verdict agreed (6 canonical lines identical), markers_exact TRUE over FOUR REAL MARKER LINES, the producer's own interpreter differential agreed on 64 sampled inputs, zero calls so the reachable closure is bodyful, and a codegen flip event whose A-LIN lineage equals the coverage row's. A1 is gated by tests/crystal_a1_lineage/float_div.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_HEAD_FLOAT, "ir_fd_head_float: the bit pattern of the first returned value, through ir_scalar_code -- which is the identity on IRScalar.float_ n. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_ANSWER, "ir_fd_answer: read a classified answer back out of an outcome. A `ret` carries `some` of its float's bit pattern; every fault and exhaustion carries `none`. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_ANSWER_RES, "ir_fd_answer_res: ir_fd_answer INVERTS ir_fd_res, on the nose, at both constructors. Two Eq.refl. This is what makes A5 an inversion rather than a restatement. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_MACHINE_SOUND, "ir_fd_machine_sound: *** A5, THE INVERSION. *** If the MACHINE running the emitted body returns the float k, then the reflected closure answers exactly `some k` -- so in particular it did not refuse, and it did not answer a different bit pattern. Goes through A4 rather than restating it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_DIV_FIN_ZERO, "ir_f64_div_fin_zero: a finite non-zero divided by a zero is the infinity at the XOR sign. Proved by rewriting the two class subterms with Eq.cong and letting the table compute -- which is exactly what the ir_f64_div_at / ir_f64_div split exists for. IEEE 754 §7.3: divideByZero, and the result is an exact infinity, not a NaN and not a trap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_OPTION_GET, "ir_option_get: the payload of an IROption Nat, zero at none. Used only to invert a `some`-equation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_MACHINE_SOUND_DIVZERO, "ir_fd_machine_sound_divzero: *** A5 REACHING PAST THE MACHINE'S ANSWER, ONTO THE ARGUMENTS. *** If the SHIPPED body's emitted fdiv answers k, and the dividend is finite non-zero, and the divisor is a ZERO -- of either sign -- then k is the infinity whose sign is the XOR of the operand signs. \n\nThis is the fact that makes float division a different operation from integer division rather than the same operation at a different type, stated about the artifact rather than about the source: one line above it in ir_binop_eval, IRBinOp.udiv on a zero divisor is IROutcome.ub IRFault.div_zero. Both are executed side by side in ir_fd_udiv_traps_where_fdiv_answers and ir_fd_one_over_plus_zero. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_IR_OPTION_IS_SOME,
            "ir_option_is_some: does this classified answer exist? DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_IR_FD_RES_IS_RET, "ir_fd_res_is_ret: the outcome is a return exactly when the classified answer exists. Two Eq.refl. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_RETURNS_IFF_MODELLED, "ir_fd_returns_iff_modelled: *** THE BOUNDARY OF THE MODELLED FRAGMENT, PROVED ABOUT THE SHIPPED BODY. *** The machine returns a value if and only if the classified division answers -- as an equality of Bools, for every input, so neither direction can be weakened. The earlier chains' `never_faults` corollary cannot be stated here and this is what replaces it: a total float semantics would be a lie, so what is proved instead is that the refusals are exactly where the specification says they are. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_OUTCOME_IS_TRAP, "ir_outcome_is_trap: is this outcome UB, a type error, a stuck machine, or fuel exhaustion? True on all four; false on ret and on the tagged unmodelled verdict, which is a deliberate refusal rather than a failure. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_RES_NEVER_TRAPS, "ir_fd_res_never_traps: nothing in the image of ir_fd_res is a trap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FD_NEVER_TRAPS, "ir_fd_never_traps: *** NO UB, NO TYPE ERROR, NO STUCK STATE, NO EXHAUSTION -- on ANY pair of binary64 bit patterns, including NaNs, infinities, signed zeros and patterns that are not valid f64 encodings at all. *** A corollary of A4. Concretely: the fdiv never faults not_float, the ret never runs off the end of the block, both operands are always found in the frame, and 2 steps always suffice. The one thing it may do is REFUSE, and ir_fd_returns_iff_modelled says exactly when. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ONE_OVER_PLUS_ZERO, "*** CONCRETE EXECUTION WITNESS -- 1.0 / +0.0 = +inf. *** The kernel runs the emitted module on two real binary64 bit patterns for two steps and returns 0x7FF0000000000000. The classification it decides on the way costs one native BigNat subtraction per test, which is the entire reason a witness at a 9.2e18 dividend is affordable at all: through ir_nat_ltb it would be 9.2e18 Nat.rec layers. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ONE_OVER_MINUS_ZERO, "CONCRETE EXECUTION WITNESS -- 1.0 / -0.0 = -inf. The companion to the one above, and the pair is the point: the two divisors are the same VALUE and different bit patterns, and the emitted body's answers differ. A model that treated the sign bit of a zero as noise would return the same infinity twice. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_MINUS_ONE_OVER_PLUS_ZERO, "CONCRETE EXECUTION WITNESS -- -1.0 / +0.0 = -inf. The sign comes from the DIVIDEND this time, so the pair with the previous witness pins the XOR rather than either operand's sign alone. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ONE_OVER_INF, "CONCRETE EXECUTION WITNESS -- 1.0 / +inf = +0.0. The other side of the infinity table: a finite divided by an infinity is an exact zero. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_MINUS_ZERO_OVER_INF, "CONCRETE EXECUTION WITNESS -- -0.0 / +inf = -0.0. A zero divided by an infinity, whose answer is a SIGNED zero, so the result is the sign bit alone and nothing else. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_INF_OVER_INF, "CONCRETE REFUSAL WITNESS -- inf / inf is REFUSED. An invalid operation: IEEE 754 makes it a quiet NaN, and the NaN's payload is implementation-defined, so there is no bit pattern to return. The machine says IROutcome.unmodelled IRFault.float_domain, which is not a value and cannot be mistaken for one. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ZERO_OVER_ZERO, "CONCRETE REFUSAL WITNESS -- 0.0 / 0.0 is REFUSED, for the same reason. Note it is refused where 1.0 / 0.0 ANSWERS: the zero divisor alone does not decide the arm, the dividend's class does too. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_FIN_OVER_FIN, "CONCRETE REFUSAL WITNESS -- 2.0 / 1.0 is REFUSED, and this is the honest one. The answer is exactly 2.0 and any reader can see it; this semantics still declines. \n\nUNTIL 2026-08-16 the reason was that round-to-nearest-even over a 53-bit significand was unaffordable for every operator. It is not: the same rounding runs for fadd, fsub and fmul, and `ir_f64_w_add_finite_finite_answers` one module over is the sibling of this witness, retired. The reason now is specific to DIVISION -- a quotient is not an exact integer, so its significand must be produced by a second division at guard precision, and the shared rounding tail names that argument enough times to turn a 0.13 s input into an unbounded one (measured in super::eval_ir_float_fin). Registering the case where the refusal is EMBARRASSING is the difference between a stated boundary and a hidden one, and this one has now been embarrassing enough to move three of its four neighbours. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_NAN, "CONCRETE REFUSAL WITNESS -- a quiet NaN operand is REFUSED. 0x7FF8000000000000 has magnitude above the infinity boundary, so it classifies nan_ and the whole row is none. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ORDER, "CONCRETE EXECUTION WITNESS -- OPERAND ORDER IS OBSERVABLE. 0.0 / 1.0 is +0.0 where 1.0 / 0.0 is +inf, same two values, same emitted body, opposite order. This is what makes the icmp-style operand-order discipline load-bearing for a binop lane too: a transcription that emitted `fdiv f64 %2, %1` computes a different function and every lane except the operand order agrees with it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_INT_OPERAND, "FAIL-CLOSED WITNESS -- an INTEGER operand at a float type is a TYPE ERROR, not a wrong number and not a refusal. ir_as_float declines IRScalar.int_ even though both constructors carry a Nat, which is exactly why EncodesF64Val cannot be EncodesU64Val. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_F32, "FAIL-CLOSED WITNESS -- the SAME operands at binary32 are UNMODELLED. 1.0 / +0.0 answers at f64 and is refused at f32, because binary32's exponent field is 8 bits wide and this module's boundary constants are binary64's. The width on the instruction is semantic input; a transcription that got it wrong would compute this instead of the witness above. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_UDIV_CONTRAST, "*** THE CONTRAST WITNESS. *** Integer division by zero is IROutcome.ub IRFault.div_zero -- undefined behaviour -- in the same ir_binop_eval, one arm away from the fdiv that answers +inf on the same divisor. Registered so that the claim `float division is not integer division at another type` is a kernel-executed fact in this repository rather than a sentence in a module comment. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_CORRECT_WITNESS, "ir_fd_correct_witness: A4's premises are all SATISFIABLE, discharged concretely -- the empty heap, an undef closure environment pointer (which the body never reads), the exact fuel bound by Le.refl, and two EncodesF64Val.mk. Both bit patterns stay universally quantified. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_DIVZERO_WITNESS, "ir_fd_machine_sound_divzero_witness: the division-by-zero A5's premises are SATISFIABLE, including the two CLASS premises -- which are discharged by Eq.refl, i.e. the kernel decides that 0x3FF0000000000000 is finite and 0 is a zero by running the classification. The observation premise is the concrete execution witness rather than an assumption, so nothing here is supposed. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

// The acceptance tests, moved to a sibling file VERBATIM on 2026-08-17 —
// module body unchanged, no assertion and no test name touched. This file
// stood at 521 lines against the 500-line convention that
// `data/paragon_ratchet.json`'s `files_over_500` enforces shrink-only, and
// the boundary is the one `eval_ir_float_fin_witnesses.rs` already used.
#[cfg(test)]
#[path = "eval_ir_float_div_tests.rs"]
mod tests;
