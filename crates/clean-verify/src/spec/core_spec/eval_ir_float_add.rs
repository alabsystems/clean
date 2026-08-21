// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **A complete width-one chain over FLOAT ADDITION — the first whose float
//! answers are COMPUTED rather than read off a classification table:
//! `env::native_reducers_float::reduce_float_add::{closure#0}`.**
//!
//! No ordinal is claimed here on purpose. Three sibling float lanes (`fadd`,
//! `fsub`, `fmul`) were written in parallel against the eighth chain's build
//! items, and which of them is the eleventh chain is decided by the order the
//! stages are entered in `bundles.rs`, not by any of their module docs.
//!
//! The source is `float_binary_op(args, |a, b| a + b)` — that closure, at
//! `native_reducers_float.rs:210` — and this is what trustc emits for it:
//!
//! ```text
//! rustcc fn @env::native_reducers_float::reduce_float_add::{closure#0}(functy.551) {
//!     ; #producer: trust
//!     ; #names: %1="a", %2="b"
//! bb0(%0: ptr, %1: f64, %2: f64):
//!     %3 = fadd f64 %1, %2  ; #loc: 354 210 33
//!     ret %3  ; #loc: 354 210 38
//! }
//! ```
//!
//! One block, two instructions, three parameters — structurally the EIGHTH
//! chain's body ([`super::eval_ir_float_div`]) with one token changed and the
//! `#loc` line moved from 222 to 210. That is deliberate: the eighth chain
//! paid for the two CFG lanes (`binop_tys`, `rets`) and for the whole binary64
//! value domain, and this chain is what those build items were supposed to make
//! cheap. The transcription, the machine lemmas, the fuel induction and A4 are
//! the eighth chain's, renamed `ir_fd_*` -> `ir_fa_*`.
//!
//! ## What is NEW, and it is the only reason to register a second float chain
//!
//! **`fdiv`'s modelled fragment excludes finite/finite; `fadd`'s does not.**
//! [`super::eval_ir_float_fin`] landed correctly-rounded binary64 addition on
//! 2026-08-16 for `fadd`/`fsub`/`fmul` and NOT for `fdiv`, so `ir_f64_add`'s
//! `fin`/`fin` cell is `ir_f64_add_fin` where `ir_f64_div`'s is `IROption.none`.
//! The headline is one line: `ir_fd_two_over_one_refused` — the eighth chain's
//! registered embarrassment, `2.0 / 1.0` declined by a semantics that could not
//! round — has as its sibling here `ir_fa_one_plus_two_answers`, the same shape
//! of witness with the kernel running the emitted body for two steps and
//! returning `0x4008000000000000` as a value.
//!
//! Everything else new here is addition's own semantics rather than division's:
//! the invalid operation is `inf + (-inf)` and not `inf / inf`, the signed-zero
//! rule is `(-0) + (-0) = -0` against every other zero pair's `+0` (IEEE
//! 754-2019 §6.3), a finite operand plus a zero is EXACT and unrounded, and a
//! finite sum can leave the finite range — `ir_fa_overflow_is_an_infinity` runs
//! the emitted body on two copies of the largest binary64 and gets `+inf`, which
//! is a value and not a fault (§7.4).
//!
//! `ir_fa_correct` is TOTAL over the richer right-hand side the eighth chain
//! introduced: for every pair of bit patterns, every environment pointer, heap,
//! next-address counter and fuel at or above 2, the machine returns exactly
//! `ir_fa_res (env_reduce_float_add a b)` — the value where the fragment is
//! modelled and `IROutcome.unmodelled IRFault.float_domain` where it is not. For
//! `fadd` the refusals are exactly two shapes (a NaN operand, two infinities of
//! opposite sign) instead of `fdiv`'s five.
//!
//! ## THE COST WALL THIS OPERATOR HAS AND THE EIGHTH CHAIN DOES NOT
//!
//! **A5 is registered at the IMAGE (`ir_fa_sound_gen`), not composed with A4,
//! and the two machine-level corollaries the eighth chain carries
//! (`ir_fd_returns_iff_modelled`, `ir_fd_never_traps`) are NOT registered here
//! at all.** That is a measured limit rather than an oversight. Any composition
//! that puts an APPLICATION of `ir_fa_correct` in a proof-argument position —
//! `Eq.symm … (ir_fa_correct …)`, `Eq.cong … (ir_fa_correct …)` — makes the
//! elaborator's unifier whnf `ir_fa_res (env_reduce_float_add a b)` at SYMBOLIC
//! operands, which unfolds into `ir_f64_add_at`'s `fin`/`fin` minor:
//! `ir_f64_add_fin a b`, the 2098-bit alignment pipeline of
//! [`super::eval_ir_float_fin`]. `ir_f64_div_at`'s minors are constant-size,
//! which is why the identical proof term costs `ir_fd_machine_sound` 0.139 s.
//!
//! Probed one declaration at a time against one `CoreSpecBundle::EvalIr` build,
//! 2026-08-20:
//!
//! ```text
//! ir_fa_correct                    (A4 itself)               0.184 s
//! ir_fa_correct_witness            (A4 applied, whole body)   0.012 s
//! identity at Eq … (env_reduce_float_add a b) (some k)       0.009 s
//! Eq.symm … h                      (h a HYPOTHESIS)          0.038 s
//! Eq.symm … (ir_fa_correct …)      (an APPLICATION)          > 250 s, killed
//! Eq.cong … (ir_fa_correct …)      (returns_iff_modelled)    > 250 s, killed
//! the eighth chain's A5 proof term, renamed                  > 25 min, killed
//! ```
//!
//! So the machine-level content lives in `ir_fa_correct`, and the outcome-level
//! content is stated GENERICALLY, where no float term appears and nothing can
//! explode: `ir_fa_sound_gen`, `ir_fa_res_is_ret`, `ir_fa_res_never_traps`.
//! Instantiating any of them at `env_reduce_float_add a b` is what does not
//! elaborate; a reader should not assume the composed statements hold here
//! because the eighth chain has them.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! `env_reduce_float_add` is `ir_f64_add`, and `ir_f64_add` is **not proved to
//! be `f64::add`**. On the classified fragment it is IEEE 754 by construction
//! and by reading; on the finite fragment it is [`super::eval_ir_float_fin`]'s
//! correctly-rounded pipeline, again by construction and by reading, checked
//! against the hardware only by witnesses — in that module, and by
//! `test_the_answering_witnesses_agree_with_real_f64` below. The gap between it
//! and the hardware adder is stated there and closed nowhere, and it is LARGER
//! than the eighth chain's, because more of this operator computes: a chain
//! whose float answers are refusals cannot get a bit pattern wrong.
//!
//! The A0/A6 evidence for this body is ALSO weaker than the eighth chain's and
//! the fixture says so: `tests/fixtures/float_add.lineage.json` records three
//! clean non-incremental builds with byte-identical `coverage.json` in its
//! reproduction stanza, but all three use one unsealed local-stage1 producer
//! rather than a sealed driver and there is no negative control. What it does
//! carry is a lowered, spliced body with `unsupported: []`, an agreed
//! derived-MIR verdict over 4 real marker lines, an agreed interpreter
//! differential on 64 sampled inputs, zero calls, a flip-event lineage equal to
//! the coverage-row lineage, and a run that reproduced the pinned `float_div`
//! artifact byte-for-byte. The gate pins that strength and no more.
//!
//! The link between the proved module and the emitted one is STRUCTURAL —
//! `tests/crystal_a1_lineage/float_add.rs`. Everything past the flip seam is
//! downstream and covered by nothing here. And this is width one.
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// NOTHING SHARED IS RE-DECLARED HERE, and the list is worth naming because a
// duplicate was the eighth chain's one real error — it elaborates cleanly in
// every fast gate and fails only in the full `Specification::new()`, at half an
// hour an attempt. Reused: `ir_nl3` / `ir_vl3` (the FIFTH chain),
// `ir_outcome_fuelout_ne_ret_prop` (`add_eval_ir_fuel`), `ir_outcome_is_ret`
// (`add_eval_ir_correct`), and — from the EIGHTH chain, which this stage runs
// after — `EncodesF64Val`, `ir_outcome_fuelout_ne_unmodelled_prop`,
// `ir_option_is_some` and `ir_outcome_is_trap`.
//
// Every declaration below was elaborated and kernel-checked INDIVIDUALLY before
// registration, on `tests/evalir_scratchpad.rs`'s contract (one
// `CoreSpecBundle::EvalIr` build, a verdict and a wall clock per candidate),
// with those eight supplied as scratch candidates because that bundle does not
// carry the stages that declare them: 47/47, 1.4 s of declaration time inside a
// 22.4 s run. From a private copy of the runner, not the shared one — three
// float lanes were writing `data/spec_scratch_evalir.json` at the same time.

// ── the reflected closure, its representation premise, its outcome ────
const SRC_IR_FA_TF64: &str = "def ir_fa_tf64 : IRTy := IRTy.float_ 64";
const SRC_ENV_REDUCE_FLOAT_ADD: &str =
    "def env_reduce_float_add (a : Nat) (b : Nat) : IROption Nat := ir_f64_add a b";
const SRC_IR_FA_RES: &str = "def ir_fa_res (o : IROption Nat) : IROutcome := IROption.rec Nat (fun (_ : IROption Nat) => IROutcome) (IROutcome.unmodelled IRFault.float_domain) (fun (k : Nat) => IROutcome.ret (ir_vl1 (IRScalar.float_ k))) o";

// ── the emitted module, transcribed ───────────────────────────────────
const SRC_IR_FA_B0: &str = "def ir_fa_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.binop IRBinOp.fadd ir_fa_tf64 ir_d1 ir_d2) ir_d3) (ir_nd (IRInst.ret (ir_nl1 ir_d3))))";
const SRC_IR_FA_FUNC: &str = "def ir_fa_func : IRFunc := IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0 (ir_blk ir_fa_b0 ir_blk0)";
const SRC_IR_FA_MODULE: &str = "def ir_fa_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_fa_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

// ── the machine ───────────────────────────────────────────────────────
const SRC_IR_FA_MACH0: &str = "def ir_fa_mach0 (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl3 ir_d0 ir_d1 ir_d2) (ir_vl3 p (IRScalar.float_ a) (IRScalar.float_ b)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";
const SRC_IR_FA_M1: &str = "def ir_fa_m1 (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) (o : IROption Nat) : IRConfig := ir_bind_result (ir_fa_mach0 p a b mem na) (ir_nl1 ir_d3) (ir_f64_result o)";
const SRC_IR_FA_ONE_STEP: &str = "def ir_fa_one_step (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_steps ir_d1 ir_fa_module (IRConfig.running (ir_fa_mach0 p a b mem na))) (ir_fa_m1 p a b mem na (env_reduce_float_add a b)) := Eq.refl IRConfig (ir_fa_m1 p a b mem na (env_reduce_float_add a b))";
const SRC_IR_FA_SPLIT: &str = "def ir_fa_split (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) (o : IROption Nat) : Eq IROutcome (ir_run ir_d1 ir_fa_module (ir_fa_m1 p a b mem na o)) (ir_fa_res o) := IROption.rec Nat (fun (o0 : IROption Nat) => Eq IROutcome (ir_run ir_d1 ir_fa_module (ir_fa_m1 p a b mem na o0)) (ir_fa_res o0)) (Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)) (fun (k : Nat) => Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) o";
const SRC_IR_FA_EXACT: &str = "def ir_fa_exact (p : IRScalar) (a : Nat) (b : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d2 ir_fa_module (IRConfig.running (ir_fa_mach0 p a b mem na))) (ir_fa_res (env_reduce_float_add a b)) := Eq.trans IROutcome (ir_run ir_d2 ir_fa_module (IRConfig.running (ir_fa_mach0 p a b mem na))) (ir_run ir_d1 ir_fa_module (ir_steps ir_d1 ir_fa_module (IRConfig.running (ir_fa_mach0 p a b mem na)))) (ir_fa_res (env_reduce_float_add a b)) (ir_run_steps_split ir_fa_module ir_d1 ir_d1 (IRConfig.running (ir_fa_mach0 p a b mem na))) (Eq.subst IRConfig (fun (c : IRConfig) => Eq IROutcome (ir_run ir_d1 ir_fa_module c) (ir_fa_res (env_reduce_float_add a b))) (ir_fa_m1 p a b mem na (env_reduce_float_add a b)) (ir_steps ir_d1 ir_fa_module (IRConfig.running (ir_fa_mach0 p a b mem na))) (Eq.symm IRConfig (ir_steps ir_d1 ir_fa_module (IRConfig.running (ir_fa_mach0 p a b mem na))) (ir_fa_m1 p a b mem na (env_reduce_float_add a b)) (ir_fa_one_step p a b mem na)) (ir_fa_split p a b mem na (env_reduce_float_add a b)))";

// ── fuel monotonicity for an outcome that may be a REFUSAL ────────────
const SRC_IR_FA_FUELOUT_ABSURD: &str = "def ir_fa_fuelout_absurd (o : IROption Nat) (C : Prop) : Eq IROutcome IROutcome.fuel_out (ir_fa_res o) -> C := IROption.rec Nat (fun (o0 : IROption Nat) => Eq IROutcome IROutcome.fuel_out (ir_fa_res o0) -> C) (fun (h : Eq IROutcome IROutcome.fuel_out (IROutcome.unmodelled IRFault.float_domain)) => ir_outcome_fuelout_ne_unmodelled_prop IRFault.float_domain C h) (fun (k : Nat) (h : Eq IROutcome IROutcome.fuel_out (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) => ir_outcome_fuelout_ne_ret_prop (ir_vl1 (IRScalar.float_ k)) C h) o";
const SRC_IR_FA_RUN_SUCC: &str = "def ir_fa_run_succ (f : Nat) : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fa_module c) (ir_fa_res o) -> Eq IROutcome (ir_run (Nat.succ f) ir_fa_module c) (ir_fa_res o) := Nat.rec (fun (k : Nat) => forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run k ir_fa_module c) (ir_fa_res o) -> Eq IROutcome (ir_run (Nat.succ k) ir_fa_module c) (ir_fa_res o)) (fun (c : IRConfig) (o : IROption Nat) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run Nat.zero ir_fa_module c0) (ir_fa_res o) -> Eq IROutcome (ir_run (Nat.succ Nat.zero) ir_fa_module c0) (ir_fa_res o)) (fun (s : IRMachine) (h : Eq IROutcome (ir_run Nat.zero ir_fa_module (IRConfig.running s)) (ir_fa_res o)) => ir_fa_fuelout_absurd o (Eq IROutcome (ir_run (Nat.succ Nat.zero) ir_fa_module (IRConfig.running s)) (ir_fa_res o)) h) (fun (x : IROutcome) (h : Eq IROutcome (ir_run Nat.zero ir_fa_module (IRConfig.halted x)) (ir_fa_res o)) => h) c) (fun (k : Nat) (ih : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run k ir_fa_module c) (ir_fa_res o) -> Eq IROutcome (ir_run (Nat.succ k) ir_fa_module c) (ir_fa_res o)) (c : IRConfig) (o : IROption Nat) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run (Nat.succ k) ir_fa_module c0) (ir_fa_res o) -> Eq IROutcome (ir_run (Nat.succ (Nat.succ k)) ir_fa_module c0) (ir_fa_res o)) (fun (s : IRMachine) => ih (ir_step ir_fa_module s) o) (fun (x : IROutcome) (h : Eq IROutcome (ir_run (Nat.succ k) ir_fa_module (IRConfig.halted x)) (ir_fa_res o)) => h) c) f";
const SRC_IR_FA_RUN_LE: &str = "def ir_fa_run_le (f : Nat) (g : Nat) (hle : Le f g) : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fa_module c) (ir_fa_res o) -> Eq IROutcome (ir_run g ir_fa_module c) (ir_fa_res o) := Le.rec f (fun (g0 : Nat) (_hg : Le f g0) => forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fa_module c) (ir_fa_res o) -> Eq IROutcome (ir_run g0 ir_fa_module c) (ir_fa_res o)) (fun (c : IRConfig) (o : IROption Nat) (h : Eq IROutcome (ir_run f ir_fa_module c) (ir_fa_res o)) => h) (fun (g2 : Nat) (_h2 : Le f g2) (ih : forall (c : IRConfig) (o : IROption Nat), Eq IROutcome (ir_run f ir_fa_module c) (ir_fa_res o) -> Eq IROutcome (ir_run g2 ir_fa_module c) (ir_fa_res o)) (c : IRConfig) (o : IROption Nat) (h : Eq IROutcome (ir_run f ir_fa_module c) (ir_fa_res o)) => ir_fa_run_succ g2 c o (ih c o h)) g hle";

// ── A4, and the outcome-level facts A5 is stated at ───────────────────
const SRC_IR_FA_CORRECT: &str = "def ir_fa_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (ra : IRScalar) (rb : IRScalar) (a : Nat) (b : Nat) (ha : EncodesF64Val ra a) (hb : EncodesF64Val rb b) : Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fa_module ir_d0 (ir_vl3 p ra rb) mem na) (ir_fa_res (env_reduce_float_add a b)) := EncodesF64Val.rec (fun (ra0 : IRScalar) (a0 : Nat) (_ : EncodesF64Val ra0 a0) => forall (rb0 : IRScalar) (b0 : Nat), EncodesF64Val rb0 b0 -> Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fa_module ir_d0 (ir_vl3 p ra0 rb0) mem na) (ir_fa_res (env_reduce_float_add a0 b0))) (fun (x : Nat) => fun (rb0 : IRScalar) (b0 : Nat) (hb0 : EncodesF64Val rb0 b0) => EncodesF64Val.rec (fun (rb1 : IRScalar) (b1 : Nat) (_ : EncodesF64Val rb1 b1) => Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_fa_module ir_d0 (ir_vl3 p (IRScalar.float_ x) rb1) mem na) (ir_fa_res (env_reduce_float_add x b1))) (fun (y : Nat) (hle : Le ir_d2 fuel) => ir_fa_run_le ir_d2 fuel hle (IRConfig.running (ir_fa_mach0 p x y mem na)) (env_reduce_float_add x y) (ir_fa_exact p x y mem na)) rb0 b0 hb0) ra a ha rb b hb";
const SRC_IR_FA_HEAD_FLOAT: &str = "def ir_fa_head_float (v : IRList IRScalar) : Nat := IRList.rec IRScalar (fun (_ : IRList IRScalar) => Nat) Nat.zero (fun (x : IRScalar) (_ : IRList IRScalar) (_ : Nat) => ir_scalar_code x) v";
const SRC_IR_FA_ANSWER: &str = "def ir_fa_answer (o : IROutcome) : IROption Nat := IROutcome.rec (fun (_ : IROutcome) => IROption Nat) (fun (v : IRList IRScalar) => IROption.some Nat (ir_fa_head_float v)) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (fun (_ : IRFault) => IROption.none Nat) (IROption.none Nat) o";
const SRC_IR_FA_ANSWER_RES: &str = "def ir_fa_answer_res (o : IROption Nat) : Eq (IROption Nat) (ir_fa_answer (ir_fa_res o)) o := IROption.rec Nat (fun (o0 : IROption Nat) => Eq (IROption Nat) (ir_fa_answer (ir_fa_res o0)) o0) (Eq.refl (IROption Nat) (IROption.none Nat)) (fun (k : Nat) => Eq.refl (IROption Nat) (IROption.some Nat k)) o";
const SRC_IR_FA_SOUND_GEN: &str = "def ir_fa_sound_gen (o : IROption Nat) (k : Nat) (h : Eq IROutcome (ir_fa_res o) (IROutcome.ret (ir_vl1 (IRScalar.float_ k)))) : Eq (IROption Nat) o (IROption.some Nat k) := Eq.trans (IROption Nat) o (ir_fa_answer (ir_fa_res o)) (IROption.some Nat k) (Eq.symm (IROption Nat) (ir_fa_answer (ir_fa_res o)) o (ir_fa_answer_res o)) (Eq.cong IROutcome (IROption Nat) ir_fa_answer (ir_fa_res o) (IROutcome.ret (ir_vl1 (IRScalar.float_ k))) h)";
const SRC_IR_FA_RES_IS_RET: &str = "def ir_fa_res_is_ret (o : IROption Nat) : Eq Bool (ir_outcome_is_ret (ir_fa_res o)) (ir_option_is_some o) := IROption.rec Nat (fun (o0 : IROption Nat) => Eq Bool (ir_outcome_is_ret (ir_fa_res o0)) (ir_option_is_some o0)) (Eq.refl Bool Bool.false) (fun (_ : Nat) => Eq.refl Bool Bool.true) o";
const SRC_IR_FA_RES_NEVER_TRAPS: &str = "def ir_fa_res_never_traps (o : IROption Nat) : Eq Bool (ir_outcome_is_trap (ir_fa_res o)) Bool.false := IROption.rec Nat (fun (o0 : IROption Nat) => Eq Bool (ir_outcome_is_trap (ir_fa_res o0)) Bool.false) (Eq.refl Bool Bool.false) (fun (_ : Nat) => Eq.refl Bool Bool.false) o";

// ── the signed-zero rule, about the ARGUMENTS ─────────────────────────
const SRC_IR_F64_ADD_ZERO_ZERO: &str = "def ir_f64_add_zero_zero (a : Nat) (b : Nat) (hza : Eq IRF64Class (ir_f64_class a) IRF64Class.zero_) (hzb : Eq IRF64Class (ir_f64_class b) IRF64Class.zero_) : Eq (IROption Nat) (ir_f64_add a b) (IROption.some Nat (ir_f64_pack (Bool.and (ir_f64_is_neg a) (ir_f64_is_neg b)) Nat.zero)) := Eq.trans (IROption Nat) (ir_f64_add_at a b (ir_f64_class a) (ir_f64_class b)) (ir_f64_add_at a b IRF64Class.zero_ (ir_f64_class b)) (IROption.some Nat (ir_f64_pack (Bool.and (ir_f64_is_neg a) (ir_f64_is_neg b)) Nat.zero)) (Eq.cong IRF64Class (IROption Nat) (fun (c : IRF64Class) => ir_f64_add_at a b c (ir_f64_class b)) (ir_f64_class a) IRF64Class.zero_ hza) (Eq.cong IRF64Class (IROption Nat) (fun (c : IRF64Class) => ir_f64_add_at a b IRF64Class.zero_ c) (ir_f64_class b) IRF64Class.zero_ hzb)";

// ── kernel-EXECUTED witnesses ─────────────────────────────────────────
// The bit patterns, once, so the witnesses below read as numbers:
//   1.0        = 0x3FF0000000000000 = 4607182418800017408
//   2.0        = 0x4000000000000000 = 4611686018427387904
//   3.0        = 0x4008000000000000 = 4613937818241073152
//   -1.0       = 0xBFF0000000000000 = 13830554455654793216
//   +0.0       = 0
//   -0.0       = 0x8000000000000000 = 9223372036854775808
//   max normal = 0x7FEFFFFFFFFFFFFF = 9218868437227405311
//   +inf       = 0x7FF0000000000000 = 9218868437227405312
//   -inf       = 0xFFF0000000000000 = 18442240474082181120
//   a quiet NaN= 0x7FF8000000000000 = 9221120237041090560
const SRC_W_INT_OPERAND: &str = "def ir_fa_integer_operand_is_a_type_error : Eq IRStepResult (ir_binop_eval IRBinOp.fadd ir_fa_tf64 (IRScalar.int_ 1) (IRScalar.int_ 0)) (IRStepResult.fault (IROutcome.type_error IRFault.not_float)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_float))";
const SRC_W_F32: &str = "def ir_fa_binary32_is_unmodelled : Eq IRStepResult (ir_binop_eval IRBinOp.fadd (IRTy.float_ 32) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_float_fault := Eq.refl IRStepResult ir_float_fault";
const SRC_W_WRAP_CONTRAST: &str = "def ir_fa_integer_add_wraps_where_fadd_overflows : Eq IRStepResult (ir_binop_eval IRBinOp.add (IRTy.uint_ 8) (IRScalar.int_ 255) (IRScalar.int_ 1)) (IRStepResult.value (IRScalar.int_ 0)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 0))";
const SRC_W_NAN: &str = "def ir_fa_nan_operand_refused : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9221120237041090560) (IRScalar.float_ 4607182418800017408)) ir_mem0 ir_d0) (IROutcome.unmodelled IRFault.float_domain) := Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)";
const SRC_W_OPPOSITE_INF: &str = "def ir_fa_opposite_infinities_refused : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 18442240474082181120)) ir_mem0 ir_d0) (IROutcome.unmodelled IRFault.float_domain) := Eq.refl IROutcome (IROutcome.unmodelled IRFault.float_domain)";
const SRC_W_INF_PLUS_INF: &str = "def ir_fa_inf_plus_inf_answers : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 9218868437227405312)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312)))";
const SRC_W_MINUS_ZEROS: &str = "def ir_fa_minus_zeros_are_minus_zero : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9223372036854775808) (IRScalar.float_ 9223372036854775808)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 9223372036854775808))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 9223372036854775808)))";
const SRC_W_MIXED_ZEROS: &str = "def ir_fa_mixed_zeros_are_plus_zero : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9223372036854775808) (IRScalar.float_ 0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 0)))";
const SRC_W_ZERO_PLUS_FIN: &str = "def ir_fa_zero_plus_finite_is_exact : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 0) (IRScalar.float_ 4607182418800017408)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 4607182418800017408))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 4607182418800017408)))";
const SRC_W_FIN_PLUS_MZERO: &str = "def ir_fa_finite_plus_minus_zero_is_exact : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 9223372036854775808)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 4607182418800017408))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 4607182418800017408)))";
const SRC_W_EXACT_ZERO_SUM: &str = "def ir_fa_exact_zero_sum : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 13830554455654793216)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 0)))";
const SRC_W_SIGNED_ZERO_SUM: &str = "def ir_fa_signed_zero_sum_witness : Eq (IROption Nat) (ir_f64_add 9223372036854775808 9223372036854775808) (IROption.some Nat 9223372036854775808) := ir_f64_add_zero_zero 9223372036854775808 9223372036854775808 (Eq.refl IRF64Class IRF64Class.zero_) (Eq.refl IRF64Class IRF64Class.zero_)";
const SRC_W_CORRECT_WITNESS: &str = "def ir_fa_correct_witness (a : Nat) (b : Nat) : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ a) (IRScalar.float_ b)) ir_mem0 ir_d0) (ir_fa_res (env_reduce_float_add a b)) := ir_fa_correct ir_mem0 ir_d2 ir_d0 IRScalar.undef_ (IRScalar.float_ a) (IRScalar.float_ b) a b (EncodesF64Val.mk a) (EncodesF64Val.mk b) (Le.refl ir_d2)";
const SRC_W_ONE_PLUS_TWO: &str = "def ir_fa_one_plus_two_answers : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4611686018427387904)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 4613937818241073152))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 4613937818241073152)))";
const SRC_W_TWO_PLUS_ONE: &str = "def ir_fa_two_plus_one_answers : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 4611686018427387904) (IRScalar.float_ 4607182418800017408)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 4613937818241073152))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 4613937818241073152)))";
const SRC_W_OVERFLOW: &str = "def ir_fa_overflow_is_an_infinity : Eq IROutcome (ir_eval ir_d2 ir_fa_module ir_d0 (ir_vl3 IRScalar.undef_ (IRScalar.float_ 9218868437227405311) (IRScalar.float_ 9218868437227405311)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.float_ 9218868437227405312)))";

impl Specification {
    /// Register the complete width-one chain over
    /// `env::native_reducers_float::reduce_float_add::{closure#0}` — the first
    /// chained body whose modelled fragment includes finite arithmetic.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_float_add(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_IR_FA_TF64, "ir_fa_tf64: f64 -- binary64, the type the emitted fadd is at. ir_float_binop reads the width off it and DECIDES only 64, giving every other float width the tagged unmodelled outcome, so this is semantic input and not decoration: a transcription at IRTy.float_ 32 computes `unmodelled` where the artifact computes 3.0. Checked against the artifact by the binop_tys lane. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ENV_REDUCE_FLOAT_ADD, "env_reduce_float_add: the reflected env::native_reducers_float::reduce_float_add::{closure#0} (native_reducers_float.rs:210), which is `|a, b| a + b` on f64. It is ir_f64_add -- the classified binary64 addition of super::eval_ir_float, whose fin/fin cell is super::eval_ir_float_fin's correctly-rounded ir_f64_add_fin -- and NOT a proof that ir_f64_add is the hardware adder. That gap is stated in those modules and closed nowhere, and it is larger than the eighth chain's, because more of this operator computes. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_RES, "ir_fa_res: the outcome a classified float answer produces -- the returned value when the fragment is modelled, and IROutcome.unmodelled IRFault.float_domain when it is not. The eighth chain's device, reused unchanged: it is what lets A4 be TOTAL over a partial value domain instead of restricted to the answering half. For fadd the refusing half is small (a NaN operand, or two infinities of opposite sign) but it is not empty, so the device is still needed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_B0, "ir_fa_b0: THE WHOLE BODY, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/float_add.trust-ir.txt). One fadd at f64 over %1 and %2 in that order into %3, then `ret %3`. The TYPE on the binop and the RETURNED id are both compared against the artifact by lanes the eighth chain added; without them a transcription that returned %1 -- an OPERAND instead of the sum -- agrees with every other lane on a body with nothing else in it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_FUNC, "ir_fa_func: the closure as EvalIR -- THREE parameters (%0 the closure environment pointer, %1 and %2 the operands), entry block 0, one block. %0 is bound and never read, and that is read off the artifact rather than assumed: the emitted body mentions %0 exactly once, in its parameter list (tests/fixtures/float_add.trust-ir.txt), which is asserted by the gate, and A4 quantifies over it with no premise at all. The `1 proven-never-read opaque param(s) as placeholders` note is the EIGHTH chain's fixture, about the sibling body; this body's fixture records its interpreter differential only as agreed on 64 sampled inputs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_MODULE, "ir_fa_module: the module for env::native_reducers_float::reduce_float_add::{closure#0}, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir recorded at tests/fixtures/float_add.trust-ir.txt and checked graph-for-graph and instruction-for-instruction, including the binop type and the returned id, by tests/crystal_a1_lineage/float_add.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_MACH0, "ir_fa_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds THREE parameters positionally, through the FIFTH chain's ir_nl3 / ir_vl3. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_M1, "ir_fa_m1: the machine after the fadd, with the CLASSIFIED ANSWER ABSTRACTED to an IROption parameter. Necessary for the same reason as in the eighth chain: ir_f64_result dispatches with IROption.rec, and on symbolic bit patterns ir_f64_add is stuck under ir_f64_class, so the machine is stuck there and no fuel unsticks it. At o := env_reduce_float_add a b this term is DEFINITIONALLY one ir_step of ir_fa_mach0. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_ONE_STEP, "ir_fa_one_step: ONE step of the machine IS ir_fa_m1 at the real classified answer. Eq.refl -- the kernel runs one step and compares two configurations, both of which carry the classification unreduced, so the check is bounded by the size of one instruction's semantics rather than by a 64-bit residue or by the rounding pipeline. 0.030 s. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_SPLIT, "ir_fa_split: THE CASE ANALYSIS, over the boundary of the modelled fragment. If the classified answer is `some k` the machine binds the float and the second step returns it; if it is `none` the fadd FAULTS and ir_bind_result halts immediately, so the remaining step is spent on an already-halted configuration. Both minors are Eq.refl -- once the IROption is a constructor the machine computes. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_EXACT, "ir_fa_exact: the machine agrees with the reflected closure at EXACTLY 2 steps, for every pair of bit patterns. 2 = 1 + 1, and the proof is that split: ir_run_steps_split peels the first step, ir_fa_one_step identifies the resulting configuration, and the case analysis finishes the second. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_FUELOUT_ABSURD, "ir_fa_fuelout_absurd: nothing in the IMAGE of ir_fa_res is fuel_out. By IROption.rec: `none` lands on unmodelled and `some k` on ret, and each has its own discriminator -- ir_outcome_fuelout_ne_unmodelled_prop from the eighth chain, ir_outcome_fuelout_ne_ret_prop from add_eval_ir_fuel, neither re-declared here. This is what makes fuel monotonicity TRUE for this chain's outcome shape. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_RUN_SUCC, "ir_fa_run_succ: FUEL MONOTONICITY for an outcome that may be a REFUSAL. ir_run_le_ret is stated for IROutcome.ret and cannot be widened in place -- the unconditional form is false, since a run that exhausts at f may halt at succ f -- so this is the same Nat.rec-over-fuel with an IRConfig.rec convoy, at the ir_fa_res image, with ir_fa_fuelout_absurd ruling exhaustion out of the conclusion. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_RUN_LE, "ir_fa_run_le: the same at a bound rather than a successor, by Le.rec iterating ir_fa_run_succ. Note Le's first argument is a PARAMETER, so Le.rec takes it before the motive. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_CORRECT, "ir_fa_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE, FOR FLOAT ADDITION. *** For every pair of binary64 bit patterns a and b, every pair of values representing them, every closure environment pointer, every heap, every next-address counter and every fuel at or above 2, ir_eval on ir_fa_module returns exactly ir_fa_res (env_reduce_float_add a b). \n\nTOTAL, not restricted to the modelled fragment: where the classified addition answers -- which now includes the FINITE fragment, correctly rounded -- the machine returns that float; where it refuses, the machine returns the tagged unmodelled outcome and nothing else. \n\nA0 for this body is recorded at tests/fixtures/float_add.lineage.json and is WEAKER than the eighth chain's: lowered, spliced, unsupported [], derived_mir agreed (6 canonical lines identical), markers_exact TRUE over four real marker lines, the producer's interpreter differential agreed on 64 sampled inputs, zero calls, and a flip-event lineage equal to the coverage-row lineage -- measured in three clean non-incremental builds with byte-identical coverage recorded by the reproduction stanza, but using one unsealed local-stage1 producer rather than a sealed driver and with no negative control. A1 is gated by tests/crystal_a1_lineage/float_add.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_HEAD_FLOAT, "ir_fa_head_float: the bit pattern of the first returned value, through ir_scalar_code -- which is the identity on IRScalar.float_ n. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_ANSWER, "ir_fa_answer: read a classified answer back out of an outcome. A `ret` carries `some` of its float's bit pattern; every fault and exhaustion carries `none`. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_ANSWER_RES, "ir_fa_answer_res: ir_fa_answer INVERTS ir_fa_res, on the nose, at both constructors. Two Eq.refl. This is what makes A5 an inversion rather than a restatement. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_SOUND_GEN, "ir_fa_sound_gen: *** A5, THE INVERSION -- STATED AT THE IMAGE RATHER THAN COMPOSED WITH A4. *** If the outcome ir_fa_res produces from a classified answer is a `ret` of the float k, then that answer was exactly `some k`: it did not refuse, and it was not a different bit pattern. \n\nThe eighth chain states the same fact ABOUT THE MACHINE, by composing it with A4. That composition does not elaborate for this operator and the reason is measured, not suspected: putting an APPLICATION of ir_fa_correct in a proof-argument position makes the unifier whnf `ir_fa_res (env_reduce_float_add a b)` at symbolic operands, which unfolds into ir_f64_add_at's fin/fin minor -- ir_f64_add_fin, the 2098-bit alignment pipeline -- where ir_f64_div_at's minors are constant-size. Killed at 25 minutes; the same term with a HYPOTHESIS in place of the application is 0.038 s. See this module's header for the probe table. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_RES_IS_RET, "ir_fa_res_is_ret: *** THE BOUNDARY OF THE MODELLED FRAGMENT, AS AN EQUALITY OF BOOLS. *** The outcome is a return exactly when the classified answer exists -- both directions, so neither can be weakened. Two Eq.refl. \n\nStated at the image for the same measured reason as ir_fa_sound_gen: the eighth chain's machine-level ir_fd_returns_iff_modelled is `Eq.cong ir_outcome_is_ret ... (ir_fd_correct ...)`, and that shape does not elaborate at this operator. A reader who wants the machine-level statement should compose it themselves and will discover the same wall. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FA_RES_NEVER_TRAPS, "ir_fa_res_never_traps: nothing in the image of ir_fa_res is a trap -- not UB, not a type error, not a stuck machine, not exhaustion. The one thing it may be is the tagged unmodelled verdict, which is a deliberate refusal rather than a failure, and ir_fa_res_is_ret says exactly when. Also stated at the image; see above. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_F64_ADD_ZERO_ZERO, "ir_f64_add_zero_zero: *** THE SIGNED-ZERO RULE, ABOUT THE ARGUMENTS. *** The sum of two ZEROS is the zero whose sign bit is the AND of the operands' sign bits. Proved by rewriting the two class subterms with Eq.cong and letting the table compute -- which is what the ir_f64_add_at / ir_f64_add split exists for. \n\nIEEE 754-2019 6.3: under roundTiesToEven the sum of two zeros of the same sign is that zero and of opposite signs is +0, which is exactly Bool.and, and it is the reason the zero arm of ir_f64_add_at is not the constant Nat.zero. It is the rule most models get wrong: three of the four zero pairs sum to +0 and only (-0) + (-0) is negative, so measured over all four zero pairs: the XOR rule MULTIPLICATION uses disagrees with the AND on three of the four (every mixed-or-negative pair except (-0)+(-0)), and a first-operand's-sign model disagrees on exactly one — (-0)+(+0). This witness pair (the all-negative pair and one mixed pair) separates the AND from both. The add-lane twin of the eighth chain's ir_f64_div_fin_zero. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_INT_OPERAND, "FAIL-CLOSED WITNESS -- an INTEGER operand at a float type is a TYPE ERROR, not a wrong number and not a refusal. ir_as_float declines IRScalar.int_ even though both constructors carry a Nat, which is exactly why EncodesF64Val cannot be EncodesU64Val: with that premise in its place A4 would be FALSE. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_F32, "FAIL-CLOSED WITNESS -- the SAME operands at binary32 are UNMODELLED. 1.0 + 2.0 answers 3.0 at f64 and is refused at f32, because binary32's exponent field is 8 bits wide and this module's boundary constants are binary64's. The width on the instruction is semantic input; a transcription that got it wrong would compute this instead of the headline witness. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_WRAP_CONTRAST, "*** THE CONTRAST WITNESS. *** Integer addition at width 8 WRAPS -- 255 + 1 is 0, a canonical residue and not an error -- in the same ir_binop_eval whose fadd, on operands at the top of ITS range, returns an infinity (ir_fa_overflow_is_an_infinity). Registered so that `float addition is not integer addition at another type` is a kernel-executed fact in this repository rather than a sentence in a module comment, exactly as the eighth chain did for udiv against fdiv. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_NAN, "CONCRETE REFUSAL WITNESS -- a quiet NaN operand is REFUSED. 0x7FF8000000000000 has magnitude above the infinity boundary, so it classifies nan_ and the whole row is none. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_OPPOSITE_INF, "CONCRETE REFUSAL WITNESS -- (+inf) + (-inf) is REFUSED. An invalid operation: IEEE 754 makes it a quiet NaN whose payload is implementation-defined, so there is no bit pattern to return. The machine says IROutcome.unmodelled IRFault.float_domain, which is not a value and cannot be mistaken for one. Note it is refused where (+inf) + (+inf) ANSWERS: the classes alone do not decide the arm, the SIGNS do too. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_INF_PLUS_INF, "CONCRETE EXECUTION WITNESS -- (+inf) + (+inf) = +inf. The infinity row's ANSWERING cell: two infinities whose signs agree sum to that infinity, exactly, with no NaN anywhere. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_MINUS_ZEROS, "*** CONCRETE EXECUTION WITNESS -- (-0.0) + (-0.0) = -0.0. *** THE signed-zero rule, run by the kernel on the EMITTED BODY rather than on the table alone: it is the one zero pair whose sum is negative. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_MIXED_ZEROS, "CONCRETE EXECUTION WITNESS -- (-0.0) + (+0.0) = +0.0. The companion to the one above, and the pair is the point: the two inputs differ only in the second operand's sign bit and the emitted body's answers differ. A model that treated the sign of a zero as noise, or that took the first operand's sign, returns -0.0 here. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ZERO_PLUS_FIN, "CONCRETE EXECUTION WITNESS -- (+0.0) + 1.0 = 1.0. Adding a zero to a finite operand is EXACT and returns that operand's own bit pattern, unrounded -- including, by the same arm, for a subnormal. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_FIN_PLUS_MZERO, "CONCRETE EXECUTION WITNESS -- 1.0 + (-0.0) = 1.0. The mirror of the one above with the zero on the right and NEGATIVE: x + (-0) is still x for a finite non-zero x, which is the rule that stops the signed-zero arm from leaking into the finite row. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_EXACT_ZERO_SUM, "CONCRETE EXECUTION WITNESS -- 1.0 + (-1.0) = +0.0. The one finite sum IEEE 754-2019 6.3 fixes with NO rounding: an exact zero sum is +0 under roundTiesToEven, positive whichever operand carried the sign. ir_f64_add_at tests ir_f64_opposite before the pipeline, so this input is answered by the exact classified rule; ir_f64_w_fin_exact_zero_sum is the executed proof that the pipeline would not disagree. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_SIGNED_ZERO_SUM, "ir_fa_signed_zero_sum_witness: the signed-zero rule's premises are SATISFIABLE, and both are discharged by the kernel COMPUTING -- Eq.refl decides that 0x8000000000000000 classifies zero_, twice, and the conclusion is ir_f64_pack applied to the AND of two sign bits, folded to 0x8000000000000000. So ir_f64_add_zero_zero is not a statement about an empty case. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_CORRECT_WITNESS, "ir_fa_correct_witness: A4's premises are all SATISFIABLE, discharged concretely -- the empty heap, an undef closure environment pointer (which the body never reads), the exact fuel bound by Le.refl, and two EncodesF64Val.mk. Both bit patterns stay universally quantified, so this is a non-vacuity witness for the theorem and not an instance of it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ONE_PLUS_TWO, "*** THE WITNESS THE EIGHTH CHAIN COULD NOT HAVE -- 1.0 + 2.0 = 3.0, RETURNED. *** The kernel runs the emitted module on two real binary64 bit patterns for two steps and gets 0x4008000000000000 back as a value, in 0.153 s. Its sibling one module over is ir_fd_two_over_one_refused, where the same shape of input at fdiv is declined, because super::eval_ir_float_fin landed correctly-rounded addition and not division. This is the whole reason a second float chain is worth registering: the fin/fin cell of this operator's table COMPUTES. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_TWO_PLUS_ONE, "CONCRETE EXECUTION WITNESS -- 2.0 + 1.0 = 3.0, the same two bit patterns in the opposite order. Paired with the witness above this is ONE PAIR on which the emitted body's answer does not depend on operand order; it is NOT a commutativity theorem and nothing here proves ir_f64_add commutes in general. The contrast is with fdiv, where the eighth chain's ir_fd_order_is_observable gets +inf one way and +0 the other. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_OVERFLOW, "CONCRETE EXECUTION WITNESS -- max normal + max normal = +inf. A finite sum that leaves the finite range: IEEE 754-2019 7.4 makes an overflow under roundTiesToEven the infinity of the result's sign, so the machine RETURNS a value here rather than faulting or refusing, and the value is the same bit pattern the classified infinity rules produce. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

// The acceptance tests live HERE rather than in a sibling file: `eval_ir_float_div.rs`
// moved its out only because it passed the 500-line convention that
// `data/paragon_ratchet.json`'s `files_over_500` enforces shrink-only.
#[cfg(test)]
mod tests {
    use super::*;

    /// The whole body: one `fadd` at f64 over `%1, %2` into `%3`, then `ret %3`
    /// — the SUM and not an operand, and no control flow. Every token in that
    /// sentence is a lane the CFG gate compares.
    #[test]
    fn test_the_body_is_one_typed_fadd_and_a_ret_of_its_result() {
        assert!(SRC_IR_FA_B0.contains("IRInst.binop IRBinOp.fadd ir_fa_tf64 ir_d1 ir_d2) ir_d3"));
        assert!(SRC_IR_FA_B0.contains("IRInst.ret (ir_nl1 ir_d3)"));
        assert!(!SRC_IR_FA_B0.contains("IRInst.ret (ir_nl1 ir_d1)"));
        assert_eq!(SRC_IR_FA_TF64.split(":= ").nth(1), Some("IRTy.float_ 64"));
        assert!(
            !SRC_IR_FA_B0.contains("condbr")
                && !SRC_IR_FA_B0.contains("switch")
                && !SRC_IR_FA_B0.contains("IRInst.br ")
        );
    }

    /// Every registered source, so a source cannot be added and left out of
    /// the two whole-set checks below.
    const ALL: &[&str] = &[
        SRC_IR_FA_TF64,
        SRC_ENV_REDUCE_FLOAT_ADD,
        SRC_IR_FA_RES,
        SRC_IR_FA_B0,
        SRC_IR_FA_FUNC,
        SRC_IR_FA_MODULE,
        SRC_IR_FA_MACH0,
        SRC_IR_FA_M1,
        SRC_IR_FA_ONE_STEP,
        SRC_IR_FA_SPLIT,
        SRC_IR_FA_EXACT,
        SRC_IR_FA_FUELOUT_ABSURD,
        SRC_IR_FA_RUN_SUCC,
        SRC_IR_FA_RUN_LE,
        SRC_IR_FA_CORRECT,
        SRC_IR_FA_HEAD_FLOAT,
        SRC_IR_FA_ANSWER,
        SRC_IR_FA_ANSWER_RES,
        SRC_IR_FA_SOUND_GEN,
        SRC_IR_FA_RES_IS_RET,
        SRC_IR_FA_RES_NEVER_TRAPS,
        SRC_IR_F64_ADD_ZERO_ZERO,
        SRC_W_INT_OPERAND,
        SRC_W_F32,
        SRC_W_WRAP_CONTRAST,
        SRC_W_NAN,
        SRC_W_OPPOSITE_INF,
        SRC_W_INF_PLUS_INF,
        SRC_W_MINUS_ZEROS,
        SRC_W_MIXED_ZEROS,
        SRC_W_ZERO_PLUS_FIN,
        SRC_W_FIN_PLUS_MZERO,
        SRC_W_EXACT_ZERO_SUM,
        SRC_W_SIGNED_ZERO_SUM,
        SRC_W_CORRECT_WITNESS,
        SRC_W_ONE_PLUS_TWO,
        SRC_W_TWO_PLUS_ONE,
        SRC_W_OVERFLOW,
    ];

    /// Nothing the earlier chains registered is re-declared: a duplicate
    /// elaborates cleanly in every fast gate and fails only in the full
    /// `Specification::new()`.
    #[test]
    fn test_no_shared_declaration_is_redeclared() {
        let all = ALL.join("\n");
        for shared in [
            "def ir_nl3",
            "def ir_vl3",
            "def ir_option_is_some",
            "def ir_outcome_is_trap",
            "def ir_outcome_is_ret",
            "def ir_outcome_fuelout_ne_unmodelled_prop",
            "def ir_outcome_fuelout_ne_ret_prop",
            "inductive EncodesF64Val",
        ] {
            assert!(
                !all.contains(shared),
                "{shared} must be REUSED, not declared"
            );
        }
    }

    /// A4 is TOTAL, quantified, and goes through the refusal-tolerant
    /// monotonicity rather than the ret-only one.
    #[test]
    fn test_a4_is_total_over_a_partial_value_domain() {
        let statement = SRC_IR_FA_CORRECT.split(":=").next().unwrap_or("");
        assert!(statement.contains("(a : Nat)") && statement.contains("(b : Nat)"));
        assert!(statement.contains("(mem : IRList IRMemSlot)"));
        assert!(statement.contains("Le ir_d2 fuel ->"));
        assert!(
            statement.contains("(ir_fa_res (env_reduce_float_add a b))"),
            "the conclusion must be the CLASSIFIED outcome, refusals included"
        );
        // A conclusion restricted to returns would throw away the half of this
        // theorem that says the emitted body's refusals are the reflected
        // function's refusals; a concrete heap would make it a witness rather
        // than a theorem; and a premise on `p` would weaken it for nothing,
        // since the body never reads the environment pointer.
        assert!(!statement.contains("IROutcome.ret"));
        assert!(!statement.contains("ir_mem0"));
        assert!(!statement.contains("EncodesF64Val p"));
        assert_eq!(SRC_IR_FA_CORRECT.matches("EncodesF64Val.rec").count(), 2);
        assert!(SRC_IR_FA_CORRECT.contains("ir_fa_run_le"));
        assert!(!SRC_IR_FA_CORRECT.contains("ir_run_le_ret"));
    }

    /// **A5 and the two boundary corollaries are stated at the IMAGE, and that
    /// is a measured limit rather than a stylistic choice.** If one of them ever
    /// mentions `env_reduce_float_add`, somebody has composed it with A4 — the
    /// shape that does not elaborate here (module header, probe table) — and
    /// this fails in a second instead of in twenty-five minutes.
    #[test]
    fn test_a5_and_the_boundary_are_stated_at_the_image() {
        for src in [
            SRC_IR_FA_SOUND_GEN,
            SRC_IR_FA_RES_IS_RET,
            SRC_IR_FA_RES_NEVER_TRAPS,
        ] {
            assert!(
                !src.contains("env_reduce_float_add") && !src.contains("ir_f64_add"),
                "this statement must quantify over the OUTCOME IMAGE, not over the add: {src}"
            );
            assert!(src.contains("(o : IROption Nat)"));
        }
        assert!(SRC_IR_FA_SOUND_GEN.contains("ir_fa_answer_res"));
        assert!(SRC_IR_FA_SOUND_GEN.contains(": Eq (IROption Nat) o (IROption.some Nat k)"));
        assert!(SRC_IR_FA_RES_IS_RET.contains("ir_option_is_some o"));
        assert!(SRC_IR_FA_RES_NEVER_TRAPS.contains("ir_outcome_is_trap"));
    }

    /// The signed-zero rule concludes about the ARGUMENTS' sign bits, with the
    /// AND that addition uses and not the XOR that multiplication does.
    #[test]
    fn test_the_signed_zero_rule_is_the_and_of_the_sign_bits() {
        assert!(SRC_IR_F64_ADD_ZERO_ZERO.contains("(ir_f64_class b) IRF64Class.zero_"));
        assert!(SRC_IR_F64_ADD_ZERO_ZERO.contains(
            ": Eq (IROption Nat) (ir_f64_add a b) (IROption.some Nat (ir_f64_pack (Bool.and \
             (ir_f64_is_neg a) (ir_f64_is_neg b)) Nat.zero))"
        ));
        // The XOR is MULTIPLICATION's rule: it agrees with addition's on three
        // of the four zero pairs and differs on (-0) + (-0).
        assert!(!SRC_IR_F64_ADD_ZERO_ZERO.contains("ir_f64_xsign"));
        // …and the witness discharges both class premises by computation.
        let refls = SRC_W_SIGNED_ZERO_SUM.matches("Eq.refl IRF64Class IRF64Class.zero_");
        assert_eq!(refls.count(), 2);
    }

    /// **The answering witnesses, re-derived from the HARDWARE.**
    ///
    /// Every expected bit pattern below is computed by `f64` itself rather than
    /// by reading IEEE 754 a second time. A table whose arms were in the wrong
    /// order, or a rounding mode that resolved ties the other way, type-checks
    /// exactly as well and fails here.
    #[test]
    fn test_the_answering_witnesses_agree_with_real_f64() {
        for (src, a, b) in [
            (
                SRC_W_ONE_PLUS_TWO,
                4607182418800017408u64,
                4611686018427387904u64,
            ),
            (SRC_W_TWO_PLUS_ONE, 4611686018427387904, 4607182418800017408),
            (
                SRC_W_EXACT_ZERO_SUM,
                4607182418800017408,
                13830554455654793216,
            ),
            (SRC_W_OVERFLOW, 9218868437227405311, 9218868437227405311),
            (SRC_W_INF_PLUS_INF, 9218868437227405312, 9218868437227405312),
            (SRC_W_MINUS_ZEROS, 9223372036854775808, 9223372036854775808),
            (SRC_W_MIXED_ZEROS, 9223372036854775808, 0),
            (SRC_W_ZERO_PLUS_FIN, 0, 4607182418800017408),
            (
                SRC_W_FIN_PLUS_MZERO,
                4607182418800017408,
                9223372036854775808,
            ),
        ] {
            let expected = (f64::from_bits(a) + f64::from_bits(b)).to_bits();
            assert!(
                src.contains(&format!(
                    "(IROutcome.ret (ir_vl1 (IRScalar.float_ {expected})))"
                )),
                "the hardware answers {expected} for {a} + {b}; the registered witness says \
                 something else: {src}"
            );
            assert!(src.contains("ir_eval ir_d2 ir_fa_module"));
            assert!(src.contains(&format!("(IRScalar.float_ {a}) (IRScalar.float_ {b})")));
        }
    }

    /// The refusing witnesses are TAGGED refusals and never values; the two
    /// answering contrasts are values. Together: the refusal set of this
    /// operator is the two shapes the module doc names, and finite/finite is
    /// not one of them.
    #[test]
    fn test_the_refusing_witnesses_are_tagged_refusals() {
        for src in [SRC_W_OPPOSITE_INF, SRC_W_NAN] {
            assert!(src.contains("ir_eval ir_d2 ir_fa_module"));
            assert!(src.contains("IROutcome.unmodelled IRFault.float_domain"));
            assert!(!src.contains("IROutcome.ret"));
        }
        assert!(SRC_W_ONE_PLUS_TWO.contains("IROutcome.ret"));
        // …and the float lane is measurably not the integer lane.
        assert!(SRC_W_WRAP_CONTRAST.contains("IRBinOp.add"));
        assert!(SRC_W_WRAP_CONTRAST.contains("IRStepResult.value (IRScalar.int_ 0)"));
        assert!(SRC_W_OVERFLOW.contains("IRScalar.float_ 9218868437227405312"));
        assert!(SRC_W_F32.contains("IRTy.float_ 32") && SRC_W_F32.contains("ir_float_fault"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        assert_eq!(
            ALL.len(),
            38,
            "every registered source must be checked here"
        );
        for src in ALL {
            let mut d: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => d += 1,
                    ')' => d -= 1,
                    _ => {}
                }
                assert!(d >= 0, "unbalanced parens in {src}");
            }
            assert_eq!(d, 0, "unbalanced parens in {src}");
            assert!(src.is_ascii(), "spec sources must be ASCII");
        }
    }
}
