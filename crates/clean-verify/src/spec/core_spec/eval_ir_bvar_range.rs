// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The FIFTH complete width-one chain — the first over a body with a
//! CONDITIONAL BRANCH and a short-circuit: `expr::bvar_in_range`.**
//!
//! ```text
//! pub(crate) fn bvar_in_range(idx: u32, start: u32, end: u32) -> bool {
//!     if end == u32::MAX { idx >= start } else { idx >= start && idx < end }
//! }
//! ```
//!
//! Seven blocks, four `icmp`s, **two `condbr`s**, two separate join blocks one
//! of which branches into the other, and a `const u32 4294967295`. Measured at
//! HEAD it is the most control-flow-carrying body in `clean-kernel` that is
//! fully chainable, and the ONLY one besides
//! `env::native_reducers_char::is_valid_char` that emits a `condbr` at all.
//!
//! ## What is new here, over all four earlier chains
//!
//! | axis | chains 1–4 | `bvar_in_range` |
//! |---|---|---|
//! | dispatch | `switch` on a discriminant (1–3), none (4) | **`condbr` — twice, nested** |
//! | proof shape | one `Eq.refl` per arm, no case analysis | **case analysis on a computed `Bool`, twice** |
//! | join blocks | one | **two, and one branches into the other** |
//! | parameters | 1 (1–3), 2 (4) | **3** |
//! | comparisons | 0 (1–3), 1 (4) | **4 — `eq`, `uge`, `uge`, `ult`** |
//! | interpreter differential | `not-run` on all four | **`agreed` on 125 sampled inputs** |
//! | `markers_exact` | vacuous on 1–3 (`0 marker line(s)`) | **true over 21 REAL marker lines** |
//!
//! The last two rows are measured coverage-row fields, not adjectives. Of the
//! 1,082 `markers_exact` rows in `clean-kernel` at this HEAD, only **27**
//! compare a non-empty marker sequence; this body has the longest such
//! sequence of any chained body (21 lines). And it is the first chain whose
//! body the producer's own INTERPRETER differential also exercised — 125
//! sampled inputs, THIR-trust-ir against MIR-trust-ir — where all four earlier
//! chains are `not-run`.
//!
//! ## The case analysis, and why the proof needed one at all
//!
//! The four earlier chains all reduce by `Eq.refl`: their scrutinee is a tag
//! the representation premise pins, so the machine takes a determined path. Here
//! the scrutinee of each `condbr` is a **computed** `Bool` — `ir_nat_eqb …` over
//! symbolic `u32` residues — and `ir_condbr_exec` is stuck on it. So:
//!
//! * `ir_br_m2 … b` is the machine two steps in, with the first comparison's
//!   result abstracted to the parameter `b`; at `b := ir_br_c1 e` it is
//!   *definitionally* the real machine, which is what makes the abstraction a
//!   rewriting device rather than a different program.
//! * `ir_br_split1` case-splits on `b` with `Bool.rec`. The `true` minor
//!   computes to the end (`bb1 → bb3`). The `false` minor lands on the SECOND
//!   `condbr` and hands off to `ir_br_split2`, which splits again.
//! * `ir_br_exact` instantiates at the real scrutinee. Every step count is
//!   exact: 9 from the entry, 7 from `ir_br_m2`, 5 from `ir_br_m4`.
//!
//! ## What actually blocked this chain — measured, and it was not the branch
//!
//! `ir_br_exact` was first written as the one-liner `ir_br_split1 i s e mem na
//! (ir_br_c1 e)` ascribed at `ir_run ir_d9`. It is TRUE, and the kernel had run
//! 3.5 minutes on it without returning when the module first landed, so the
//! stage was left UNREGISTERED rather than risk hanging every test that builds
//! `Specification::new()`. The obvious suspects — the `condbr`, the nine-step
//! run, the size of the stuck term — were all wrong. The cost was **one `Nat`
//! comparison**, and it reproduces with no machine in sight:
//!
//! ```text
//! Eq Nat (ir_wrap ir_dW <literal>) (ir_wrap ir_dW <the same value, named>)
//!   W =  8    0.021 s
//!   W = 12    0.431 s
//!   W = 16    6.586 s     (x15.3 per four bits — the 2^W law, measured)
//!   W = 32    ~5 days extrapolated; killed after 12 min, RSS flat
//! ```
//!
//! `ir_wrap w n` is `ir_nat_rem n (ir_nat_pow2 w)` and `ir_nat_div` is fuelled
//! by its own dividend, so deciding a residue at width `w` costs on the order of
//! `2^w` `Nat.rec` unfoldings — finite, and at `w = 32` finite the way a
//! five-day kernel run is finite. The kernel pays it only when the two sides are
//! not syntactically equal, which they were not: the machine materialises
//! `ir_wrap ir_d32 4294967295` from the emitted `IRInst.const_`, while the
//! reflected predicate said `ir_wrap ir_d32 ir_br_umax` for a definition
//! `ir_br_umax := 4294967295`. Unfolding that name AT THE LEAF is free
//! (`Eq Nat 4294967295 ir_br_umax` checks in 0.000 s); reaching the leaf from
//! inside `ir_wrap` is not, because the kernel reduces the two applications
//! rather than comparing their arguments.
//!
//! **So the fix is to say what the machine says.** `ir_br_c1` and `ir_br_m1`
//! carry the literal `4294967295` — the constant the emitted body actually
//! materialises, per `tests/fixtures/bvar_in_range.trust-ir.txt` — and
//! `ir_br_umax` is gone. This is strictly more faithful transcription, not less:
//! the name was the only thing in the reflected predicate that the emitted IR
//! did not contain. The two-step configuration lemma that would not return in
//! 12 minutes now checks in **0.006 s**.
//!
//! ## The 7+2 step split
//!
//! **Stated so nobody mistakes which change did the work: with the literal in
//! place the ONE-LINER checks too, in 0.010 s — measured, same probe, same
//! run.** The step split is not what unblocked this chain and is not presented
//! as such. It is kept because it makes the bound EVIDENT rather than merely
//! measured: `ir_run_steps_split` is a general lemma of the semantics, already
//! kernel-checked in `add_eval_ir_steps`, and `ir_br_two_steps` runs
//! `ir_steps ir_d2` — which stops before the first `condbr`. So no check in the
//! chain reduces past a symbolic scrutinee, and none depends on how large the
//! stuck term on the other side happens to be. Cost of the whole device:
//! 0.006 s + 0.013 s. The statement of `ir_br_exact` is character-for-character
//! the one that was there before.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! `ir_br_c1` compares against `ir_wrap ir_d32 (ir_wrap ir_d32 4294967295)` —
//! the residue is taken **twice**, once when `IRInst.const_` materialises the
//! literal and again when `ir_int_cmp` canonicalises the comparison's operands.
//! That double wrap is what the machine computes, so it is what the reflected
//! predicate says. Collapsing it needs `ir_wrap` idempotence, which is proved
//! nowhere here, and the kernel cannot decide it by computation either: that is
//! the same 2^32 residue measured above.
//!
//! **The consequence WAS measured, not predicted: this chain had NO concrete
//! `ir_eval` witness at ANY argument.** `ir_nat_eqb` recurses on its first
//! operand and then needs the second in `Nat.succ` form, and putting
//! `ir_wrap ir_d32 (ir_wrap ir_d32 4294967295)` in that form was the five-day
//! reduction, so the first `condbr`'s scrutinee was stuck however small the
//! arguments were. The first draft of this module carried five concrete
//! witnesses at `idx`/`start`/`end` of 0..7; they did not merely run slowly,
//! they **hung the spec build**, and they were replaced by the four PATH
//! witnesses — the machine executed along each emitted path with the branch
//! condition supplied as a literal `Bool`, which is exactly what the split
//! lemmas' minors are.
//!
//! ## 2026-08-15: the residue wall is gone, and three of those paths now RUN
//!
//! The `ir_wrap` literal-folding lemma (`ir_nat_ltb_sub_eq` in
//! [`super::eval_ir_state`]) replaces `ir_div_go`'s guard with a native
//! `Nat.sub` test and PROVES the two guards are the same predicate.
//! `ir_wrap ir_d32 (ir_wrap ir_d32 4294967295)` — the residue extrapolated at
//! ~9.6 days and never once measured — folds to its literal in **0.007 s**.
//! `ir_br_concrete_in_range`, `ir_br_concrete_above_end` and
//! `ir_br_concrete_below_start` are the first concrete executions this chain
//! has ever had: the kernel runs the emitted module on real `u32`s and decides
//! both `condbr` scrutinees itself.
//!
//! **The fourth path was still PATH-only, for a DIFFERENT reason that lemma
//! did not touch and did not pretend to.** Reaching the sentinel-true arm needs
//! `end = 4294967295`, and `ir_nat_eqb` walked its FIRST operand unary —
//! 4.29e9 `Nat.rec` steps with every residue already folded. The same technique
//! applied (`a == b` iff `a - b` and `b - a` are both zero), but the agreement
//! theorem for `ir_nat_eqb` was not proved there and that module claimed
//! nothing from it.
//!
//! ## 2026-08-15, later: the fourth path RUNS
//!
//! `ir_nat_eqb_walk_eq` ([`super::eval_ir_state`]) is that theorem: the
//! two-sided subtraction test and the paired unary walk (kept verbatim as
//! `ir_nat_eqb_walk`) are the SAME PREDICATE at every pair of arguments —
//! `Nat.rec` on the first operand with the motive generalized over the second,
//! `ir_nat_sub_zero_left` at zero, `nat_sub_succ_succ` twice at the successor
//! case. `ir_icmp_eq_walk` restates it at the `icmp eq` instruction this body's
//! `bb0` emits. Both operands of the sentinel test now go through one native
//! `BigNat` subtraction.
//!
//! `ir_br_concrete_unbounded` and `ir_br_concrete_unbounded_below_start` are
//! the result, and they are the **first executions of this edge at any
//! argument in the program's history**. The measurement is a kill, not a
//! ratio: on the pristine tree the identical declaration ran **47 min 37 s
//! without returning** and was killed; here it is **0.010 s**. All four emitted
//! paths of this chain are now covered concretely as well as by PATH witness.
//!
//! That fold is not free — it costs ~5.1 s per full `Specification::new()`, all
//! of it in the FOURTH chain (`flat_flags_contains`, whose A4 is an `Eq.refl`
//! at symbolic bytes over an `ir_nat_eqb`). The per-stage measurement and the
//! priced alternative are in [`super::eval_ir_state`]; this stage itself moved
//! 0.105 → 0.147 s while gaining the two executions.
//!
//! The link between the proved module and the emitted one is STRUCTURAL —
//! `tests/crystal_a1_lineage/bvar_in_range.rs`, now including a `condbr` lane
//! that no earlier chain exercised. Everything past the flip seam is
//! downstream and covered by nothing here. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_IR_D32: &str = "def ir_d32 : Nat := Nat.add ir_d16 ir_d16";

const SRC_IR_BR_TU32: &str = "def ir_br_tu32 : IRTy := IRTy.uint_ ir_d32";

const SRC_IR_BR_C1: &str = "def ir_br_c1 (e : Nat) : Bool := ir_nat_eqb (ir_wrap ir_d32 e) (ir_wrap ir_d32 (ir_wrap ir_d32 4294967295))";

const SRC_IR_BR_C2: &str =
    "def ir_br_c2 (i : Nat) (s : Nat) : Bool := ir_nat_leb (ir_wrap ir_d32 s) (ir_wrap ir_d32 i)";

const SRC_IR_BR_C3: &str =
    "def ir_br_c3 (i : Nat) (e : Nat) : Bool := ir_nat_ltb (ir_wrap ir_d32 i) (ir_wrap ir_d32 e)";

const SRC_EXPR_BVAR_IN_RANGE: &str = "def expr_bvar_in_range (i : Nat) (s : Nat) (e : Nat) : Bool := Bool.rec (fun (_ : Bool) => Bool) (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_br_c3 i e) (ir_br_c2 i s)) (ir_br_c2 i s) (ir_br_c1 e)";

const SRC_ENCODESU32VAL: &str = "inductive EncodesU32Val : IRScalar -> Nat -> Type\n| mk : forall (n : Nat), EncodesU32Val (IRScalar.int_ n) n";

const SRC_IR_NL3: &str =
    "def ir_nl3 (a : Nat) (b : Nat) (c : Nat) : IRList Nat := IRList.cons Nat a (ir_nl2 b c)";

const SRC_IR_VL3: &str = "def ir_vl3 (a : IRScalar) (b : IRScalar) (c : IRScalar) : IRList IRScalar := IRList.cons IRScalar a (ir_vl2 b c)";

const SRC_IR_BR_B0: &str = "def ir_br_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 4294967295)) ir_d5) (ir_nd1 (IRInst.icmp IRICmpOp.eq_ ir_br_tu32 ir_d2 ir_d5) ir_d6) (ir_nd (IRInst.condbr ir_d6 ir_d1 ir_nl0 ir_d2 ir_nl0)))";
const SRC_IR_BR_B1: &str = "def ir_br_b1 : IRBlock := IRBlock.mk ir_d1 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.icmp IRICmpOp.uge ir_br_tu32 ir_d0 ir_d1) ir_d7) (ir_nd (IRInst.br ir_d3 (ir_nl1 ir_d7))))";
const SRC_IR_BR_B2: &str = "def ir_br_b2 : IRBlock := IRBlock.mk ir_d2 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.icmp IRICmpOp.uge ir_br_tu32 ir_d0 ir_d1) ir_d8) (ir_nd (IRInst.condbr ir_d8 ir_d4 ir_nl0 ir_d5 ir_nl0)))";
const SRC_IR_BR_B3: &str = "def ir_br_b3 : IRBlock := IRBlock.mk ir_d3 (ir_nl1 ir_d3) (ir_bd1 (ir_nd (IRInst.ret (ir_nl1 ir_d3))))";
const SRC_IR_BR_B4: &str = "def ir_br_b4 : IRBlock := IRBlock.mk ir_d4 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d0 ir_d2) ir_d9) (ir_nd (IRInst.br ir_d6 (ir_nl1 ir_d9))))";
const SRC_IR_BR_B5: &str = "def ir_br_b5 : IRBlock := IRBlock.mk ir_d5 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ IRTy.bool_ (IRConst.bool_ Bool.false)) ir_d10) (ir_nd (IRInst.br ir_d6 (ir_nl1 ir_d10))))";
const SRC_IR_BR_B6: &str = "def ir_br_b6 : IRBlock := IRBlock.mk ir_d6 (ir_nl1 ir_d4) (ir_bd1 (ir_nd (IRInst.br ir_d3 (ir_nl1 ir_d4))))";

const SRC_IR_BR_FUNC: &str = "def ir_br_func : IRFunc := IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0 (ir_blk ir_br_b0 (ir_blk ir_br_b1 (ir_blk ir_br_b2 (ir_blk ir_br_b3 (ir_blk ir_br_b4 (ir_blk ir_br_b5 (ir_blk ir_br_b6 ir_blk0)))))))";

const SRC_IR_BR_MODULE: &str = "def ir_br_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_br_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

const SRC_IR_CFG_MACH: &str = "def ir_cfg_mach (c : IRConfig) (dflt : IRMachine) : IRMachine := IRConfig.rec (fun (_ : IRConfig) => IRMachine) (fun (m : IRMachine) => m) (fun (_ : IROutcome) => dflt) c";

const SRC_IR_BR_MACH0: &str = "def ir_br_mach0 (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl3 ir_d0 ir_d1 ir_d2) (ir_vl3 (IRScalar.int_ i) (IRScalar.int_ s) (IRScalar.int_ e)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_IR_BR_M1: &str = "def ir_br_m1 (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := ir_cfg_mach (ir_bind_result (ir_br_mach0 i s e mem na) (ir_nl1 ir_d5) (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d32 4294967295)))) (ir_br_mach0 i s e mem na)";

const SRC_IR_BR_M2: &str = "def ir_br_m2 (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) (b : Bool) : IRMachine := ir_cfg_mach (ir_bind_result (ir_br_m1 i s e mem na) (ir_nl1 ir_d6) (IRStepResult.value (IRScalar.bool_ b))) (ir_br_mach0 i s e mem na)";

const SRC_IR_BR_M3: &str = "def ir_br_m3 (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := ir_cfg_mach (ir_step ir_br_module (ir_br_m2 i s e mem na Bool.false)) (ir_br_mach0 i s e mem na)";

const SRC_IR_BR_M4: &str = "def ir_br_m4 (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) (b : Bool) : IRMachine := ir_cfg_mach (ir_bind_result (ir_br_m3 i s e mem na) (ir_nl1 ir_d8) (IRStepResult.value (IRScalar.bool_ b))) (ir_br_mach0 i s e mem na)";

const SRC_IR_BR_SPLIT2: &str = "def ir_br_split2 (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) (b : Bool) : Eq IROutcome (ir_run ir_d5 ir_br_module (IRConfig.running (ir_br_m4 i s e mem na b))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_br_c3 i e) b)))) := Bool.rec (fun (b0 : Bool) => Eq IROutcome (ir_run ir_d5 ir_br_module (IRConfig.running (ir_br_m4 i s e mem na b0))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_br_c3 i e) b0))))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (ir_br_c3 i e))))) b";

const SRC_IR_BR_SPLIT1: &str = "def ir_br_split1 (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) (b : Bool) : Eq IROutcome (ir_run ir_d7 ir_br_module (IRConfig.running (ir_br_m2 i s e mem na b))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (Bool.rec (fun (_ : Bool) => Bool) (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_br_c3 i e) (ir_br_c2 i s)) (ir_br_c2 i s) b)))) := Bool.rec (fun (b0 : Bool) => Eq IROutcome (ir_run ir_d7 ir_br_module (IRConfig.running (ir_br_m2 i s e mem na b0))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (Bool.rec (fun (_ : Bool) => Bool) (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_br_c3 i e) (ir_br_c2 i s)) (ir_br_c2 i s) b0))))) (ir_br_split2 i s e mem na (ir_br_c2 i s)) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (ir_br_c2 i s))))) b";

const SRC_IR_BR_TWO_STEPS: &str = "def ir_br_two_steps (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_steps ir_d2 ir_br_module (IRConfig.running (ir_br_mach0 i s e mem na))) (IRConfig.running (ir_br_m2 i s e mem na (ir_br_c1 e))) := Eq.refl IRConfig (IRConfig.running (ir_br_m2 i s e mem na (ir_br_c1 e)))";

const SRC_IR_BR_EXACT: &str = "def ir_br_exact (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d9 ir_br_module (IRConfig.running (ir_br_mach0 i s e mem na))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i s e)))) := Eq.trans IROutcome (ir_run ir_d9 ir_br_module (IRConfig.running (ir_br_mach0 i s e mem na))) (ir_run ir_d7 ir_br_module (ir_steps ir_d2 ir_br_module (IRConfig.running (ir_br_mach0 i s e mem na)))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i s e)))) (ir_run_steps_split ir_br_module ir_d7 ir_d2 (IRConfig.running (ir_br_mach0 i s e mem na))) (Eq.subst IRConfig (fun (k : IRConfig) => Eq IROutcome (ir_run ir_d7 ir_br_module k) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i s e))))) (IRConfig.running (ir_br_m2 i s e mem na (ir_br_c1 e))) (ir_steps ir_d2 ir_br_module (IRConfig.running (ir_br_mach0 i s e mem na))) (Eq.symm IRConfig (ir_steps ir_d2 ir_br_module (IRConfig.running (ir_br_mach0 i s e mem na))) (IRConfig.running (ir_br_m2 i s e mem na (ir_br_c1 e))) (ir_br_two_steps i s e mem na)) (ir_br_split1 i s e mem na (ir_br_c1 e)))";

const SRC_IR_BR_CORRECT: &str = "def ir_br_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (ra : IRScalar) (rb : IRScalar) (rc : IRScalar) (i : Nat) (s : Nat) (e : Nat) (ha : EncodesU32Val ra i) (hb : EncodesU32Val rb s) (hc : EncodesU32Val rc e) : Le ir_d9 fuel -> Eq IROutcome (ir_eval fuel ir_br_module ir_d0 (ir_vl3 ra rb rc) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i s e)))) := EncodesU32Val.rec (fun (ra0 : IRScalar) (i0 : Nat) (_ : EncodesU32Val ra0 i0) => forall (rb0 : IRScalar) (s0 : Nat), EncodesU32Val rb0 s0 -> forall (rc0 : IRScalar) (e0 : Nat), EncodesU32Val rc0 e0 -> Le ir_d9 fuel -> Eq IROutcome (ir_eval fuel ir_br_module ir_d0 (ir_vl3 ra0 rb0 rc0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i0 s0 e0))))) (fun (i1 : Nat) => fun (rb0 : IRScalar) (s0 : Nat) (hb0 : EncodesU32Val rb0 s0) => EncodesU32Val.rec (fun (rb1 : IRScalar) (s1 : Nat) (_ : EncodesU32Val rb1 s1) => forall (rc0 : IRScalar) (e0 : Nat), EncodesU32Val rc0 e0 -> Le ir_d9 fuel -> Eq IROutcome (ir_eval fuel ir_br_module ir_d0 (ir_vl3 (IRScalar.int_ i1) rb1 rc0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i1 s1 e0))))) (fun (s2 : Nat) => fun (rc0 : IRScalar) (e0 : Nat) (hc0 : EncodesU32Val rc0 e0) => EncodesU32Val.rec (fun (rc1 : IRScalar) (e1 : Nat) (_ : EncodesU32Val rc1 e1) => Le ir_d9 fuel -> Eq IROutcome (ir_eval fuel ir_br_module ir_d0 (ir_vl3 (IRScalar.int_ i1) (IRScalar.int_ s2) rc1) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i1 s2 e1))))) (fun (e2 : Nat) (hle : Le ir_d9 fuel) => ir_run_le_ret ir_br_module ir_d9 fuel hle (IRConfig.running (ir_br_mach0 i1 s2 e2 mem na)) (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i1 s2 e2))) (ir_br_exact i1 s2 e2 mem na)) rc0 e0 hc0) rb0 s0 hb0) ra i ha rb s hb rc e hc";

const SRC_IR_BR_MACHINE_SOUND: &str = "def ir_br_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (ra : IRScalar) (rb : IRScalar) (rc : IRScalar) (i : Nat) (s : Nat) (e : Nat) (c : Bool) (ha : EncodesU32Val ra i) (hb : EncodesU32Val rb s) (hc : EncodesU32Val rc e) (hle : Le ir_d9 fuel) (hret : Eq IROutcome (ir_eval fuel ir_br_module ir_d0 (ir_vl3 ra rb rc) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ c)))) : Eq Bool (expr_bvar_in_range i s e) c := Eq.cong IROutcome Bool ir_outcome_bool (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i s e)))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ c))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i s e)))) (ir_eval fuel ir_br_module ir_d0 (ir_vl3 ra rb rc) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ c))) (Eq.symm IROutcome (ir_eval fuel ir_br_module ir_d0 (ir_vl3 ra rb rc) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i s e)))) (ir_br_correct mem fuel na ra rb rc i s e ha hb hc hle)) hret)";

const SRC_IR_BR_MACHINE_SOUND_LOWER: &str = "def ir_br_machine_sound_lower (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (ra : IRScalar) (rb : IRScalar) (rc : IRScalar) (i : Nat) (s : Nat) (e : Nat) (ha : EncodesU32Val ra i) (hb : EncodesU32Val rb s) (hc : EncodesU32Val rc e) (hle : Le ir_d9 fuel) (hret : Eq IROutcome (ir_eval fuel ir_br_module ir_d0 (ir_vl3 ra rb rc) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))) : Eq Bool (ir_br_c2 i s) Bool.true := bvar_true_implies_lower i s e (ir_br_machine_sound mem fuel na ra rb rc i s e Bool.true ha hb hc hle hret)";

const SRC_BVAR_TRUE_IMPLIES_LOWER: &str = "def bvar_true_implies_lower (i : Nat) (s : Nat) (e : Nat) : Eq Bool (expr_bvar_in_range i s e) Bool.true -> Eq Bool (ir_br_c2 i s) Bool.true := Bool.rec (fun (b1 : Bool) => Eq Bool (Bool.rec (fun (_ : Bool) => Bool) (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_br_c3 i e) b1) b1 (ir_br_c1 e)) Bool.true -> Eq Bool b1 Bool.true) (Bool.rec (fun (b0 : Bool) => Eq Bool (Bool.rec (fun (_ : Bool) => Bool) Bool.false Bool.false b0) Bool.true -> Eq Bool Bool.false Bool.true) (fun (h : Eq Bool Bool.false Bool.true) => h) (fun (h : Eq Bool Bool.false Bool.true) => h) (ir_br_c1 e)) (fun (h : Eq Bool (Bool.rec (fun (_ : Bool) => Bool) (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_br_c3 i e) Bool.true) Bool.true (ir_br_c1 e)) Bool.true) => Eq.refl Bool Bool.true) (ir_br_c2 i s)";

const SRC_IR_BR_NEVER_FAULTS: &str = "def ir_br_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (ra : IRScalar) (rb : IRScalar) (rc : IRScalar) (i : Nat) (s : Nat) (e : Nat) (ha : EncodesU32Val ra i) (hb : EncodesU32Val rb s) (hc : EncodesU32Val rc e) (hle : Le ir_d9 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_br_module ir_d0 (ir_vl3 ra rb rc) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_br_module ir_d0 (ir_vl3 ra rb rc) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i s e)))) (ir_br_correct mem fuel na ra rb rc i s e ha hb hc hle)";

// ── execution witnesses, one per emitted PATH ─────────────────────────────
//
// NOT at concrete arguments, and the reason is a measured limit rather than a
// preference: the kernel cannot AFFORD to decide `ir_br_c1` at any argument.
// `ir_nat_eqb` recurses on its first operand and then needs the second in
// `Nat.succ` form; the second is `ir_nat_rem 4294967295 (ir_nat_pow2 ir_d32)`,
// whose `ir_div_go` is fuelled by its own dividend, so weak head normal form
// costs on the order of 2^32 `Nat.rec` unfoldings. The cost law was measured on
// the same shape at three widths (0.021 s / 0.431 s / 6.586 s at w = 8 / 12 /
// 16, x15.3 per four bits), which puts w = 32 at roughly five days. A concrete
// `ir_eval` witness for this body would not merely be slow. The first draft of
// this module had five such witnesses and they HUNG the spec build.
//
// What DOES execute, and what these witnesses are: the machine run along each
// emitted path with the branch condition supplied as a LITERAL. Each is the
// corresponding minor of a split lemma, and each minor is an `Eq.refl` the
// kernel discharges by running the body.
const SRC_IR_BR_PATH_UNBOUNDED: &str = "def ir_br_path_unbounded (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d7 ir_br_module (IRConfig.running (ir_br_m2 i s e mem na Bool.true))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (ir_br_c2 i s)))) := ir_br_split1 i s e mem na Bool.true";

const SRC_IR_BR_PATH_BOUNDED: &str = "def ir_br_path_bounded (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d7 ir_br_module (IRConfig.running (ir_br_m2 i s e mem na Bool.false))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_br_c3 i e) (ir_br_c2 i s))))) := ir_br_split1 i s e mem na Bool.false";

const SRC_IR_BR_PATH_UPPER: &str = "def ir_br_path_upper (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d5 ir_br_module (IRConfig.running (ir_br_m4 i s e mem na Bool.true))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (ir_br_c3 i e)))) := ir_br_split2 i s e mem na Bool.true";

const SRC_IR_BR_PATH_SHORT_CIRCUIT: &str = "def ir_br_path_short_circuit (i : Nat) (s : Nat) (e : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d5 ir_br_module (IRConfig.running (ir_br_m4 i s e mem na Bool.false))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := ir_br_split2 i s e mem na Bool.false";

const SRC_IR_BR_CORRECT_WITNESS: &str = "def ir_br_correct_witness (i : Nat) (s : Nat) (e : Nat) : Eq IROutcome (ir_eval ir_d9 ir_br_module ir_d0 (ir_vl3 (IRScalar.int_ i) (IRScalar.int_ s) (IRScalar.int_ e)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_bvar_in_range i s e)))) := ir_br_correct ir_mem0 ir_d9 ir_d0 (IRScalar.int_ i) (IRScalar.int_ s) (IRScalar.int_ e) i s e (EncodesU32Val.mk i) (EncodesU32Val.mk s) (EncodesU32Val.mk e) (Le.refl ir_d9)";

// ── CONCRETE execution witnesses (2026-08-15) ─────────────────────────────
//
// The comment above says this body has no concrete `ir_eval` witness at any
// argument. That was TRUE and MEASURED, and it is no longer true: the wall was
// the sentinel residue `ir_wrap ir_d32 (ir_wrap ir_d32 4294967295)`, which the
// `ir_wrap` literal-folding lemma (`ir_nat_ltb_sub_eq`, `eval_ir_state`) folds
// in 0.007 s. Three of the emitted paths now RUN at concrete arguments.
//
// The fourth did not, and the reason was NOT the residue: reaching the
// sentinel-true path needs `end = 4294967295`, and `ir_nat_eqb` then walked its
// FIRST operand 4.29e9 unary steps. That was named as a second lemma of the
// same shape, and it is now proved — `ir_nat_eqb_walk_eq` (`eval_ir_state`):
// `a == b` iff `a - b` and `b - a` are both zero, kernel-checked equal to the
// walk at every pair of arguments. The fourth path RUNS, twice, below.
const SRC_IR_BR_CONCRETE_IN_RANGE: &str = "def ir_br_concrete_in_range : Eq IROutcome (ir_eval ir_d9 ir_br_module ir_d0 (ir_vl3 (IRScalar.int_ 3) (IRScalar.int_ 1) (IRScalar.int_ 5)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";

const SRC_IR_BR_CONCRETE_ABOVE_END: &str = "def ir_br_concrete_above_end : Eq IROutcome (ir_eval ir_d9 ir_br_module ir_d0 (ir_vl3 (IRScalar.int_ 9) (IRScalar.int_ 1) (IRScalar.int_ 5)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";

const SRC_IR_BR_CONCRETE_BELOW_START: &str = "def ir_br_concrete_below_start : Eq IROutcome (ir_eval ir_d9 ir_br_module ir_d0 (ir_vl3 (IRScalar.int_ Nat.zero) (IRScalar.int_ 1) (IRScalar.int_ 5)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";

// ── The FOURTH path, unblocked by the equality lemma (2026-08-15, later) ──
//
// `end = 4294967295` makes the sentinel test true, so these two take
// bb0 -> bb1 -> bb3 — the arm with no upper bound, whose answer is the lower
// comparison alone. Both were impossible at ANY argument until
// `ir_nat_eqb_walk_eq`: deciding `ir_nat_eqb (ir_wrap 32 4294967295)
// (ir_wrap 32 (ir_wrap 32 4294967295))` by the paired walk is 4.29e9 `Nat.rec`
// steps with every residue already folded. Measured here: 0.010 s each.
const SRC_IR_BR_CONCRETE_UNBOUNDED: &str = "def ir_br_concrete_unbounded : Eq IROutcome (ir_eval ir_d9 ir_br_module ir_d0 (ir_vl3 (IRScalar.int_ 3) (IRScalar.int_ 1) (IRScalar.int_ 4294967295)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";

const SRC_IR_BR_CONCRETE_UNBOUNDED_BELOW_START: &str = "def ir_br_concrete_unbounded_below_start : Eq IROutcome (ir_eval ir_d9 ir_br_module ir_d0 (ir_vl3 (IRScalar.int_ Nat.zero) (IRScalar.int_ 1) (IRScalar.int_ 4294967295)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";

const SRC_IR_BR_MACHINE_SOUND_WITNESS: &str = "def ir_br_machine_sound_witness (i : Nat) (s : Nat) (e : Nat) : Eq Bool (expr_bvar_in_range i s e) (expr_bvar_in_range i s e) := ir_br_machine_sound ir_mem0 ir_d9 ir_d0 (IRScalar.int_ i) (IRScalar.int_ s) (IRScalar.int_ e) i s e (expr_bvar_in_range i s e) (EncodesU32Val.mk i) (EncodesU32Val.mk s) (EncodesU32Val.mk e) (Le.refl ir_d9) (ir_br_correct_witness i s e)";

impl Specification {
    /// Register the FIFTH complete width-one chain, and the first over a body
    /// with a conditional branch: `expr::bvar_in_range`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_bvar_range(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_IR_D32, "ir_d32: the machine width this body works at. The EvalIR numerals stop at 16 because no earlier chain needed more; a u32 body does. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_TU32, "ir_br_tu32: u32, the type every comparison in this body is at. Not decoration: ir_int_cmp reads the width off it and canonicalizes BOTH operands at that width, so a body transcribed at the wrong width computes a different function. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_C1, "ir_br_c1: the first comparison the emitted body performs -- `end == u32::MAX` at u32. \n\nThe residue is taken TWICE and that is not a slip: IRInst.const_ canonicalizes the literal through ir_const_int_eval, and ir_icmp_eq canonicalizes both operands again through ir_int_cmp. This is what the machine computes. Collapsing the double wrap needs ir_wrap idempotence, which is not proved anywhere in this repository, and at width 32 the kernel cannot afford to decide it by computation either -- ir_nat_div is fuelled by its dividend, so a width-w residue costs on the order of 2^w Nat.rec unfoldings (measured on this exact shape: 0.021s / 0.431s / 6.586s at w = 8 / 12 / 16, x15.3 per four bits, putting w = 32 at about five days). Writing the single wrap here would be a claim, not a transcription. 

The SENTINEL IS THE LITERAL 4294967295 AND MUST STAY THE LITERAL. This is the whole reason the chain sat unregistered on 2026-08-13: the predicate said ir_wrap ir_d32 ir_br_umax for a definition ir_br_umax := 4294967295, and against the machine's ir_wrap ir_d32 4294967295 the kernel reduces both residues instead of comparing arguments -- 3.5 minutes with no answer when it first landed, 12 more minutes here, RSS flat. Unfolding the name at the LEAF is free (Eq Nat 4294967295 ir_br_umax checks in 0.000s); reaching the leaf from inside ir_wrap is the five-day reduction. Carrying the literal the emitted IRInst.const_ carries is also the more faithful transcription: the name was the only thing in this predicate the emitted body does not contain. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_C2, "ir_br_c2: `idx >= start` at u32, i.e. IRICmpOp.uge, which ir_icmp_eval reads as ir_nat_leb with the operands EXCHANGED. The emitted body computes it TWICE, in two different blocks, on both sides of the sentinel test. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_C3, "ir_br_c3: `idx < end` at u32, IRICmpOp.ult. Reached only when the sentinel test failed AND the lower bound held -- it is the right-hand operand of the source's short-circuit &&, and the emitted CFG makes the short-circuit explicit as a branch rather than as an operator. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_EXPR_BVAR_IN_RANGE, "expr_bvar_in_range: the reflected expr::bvar_in_range (expr/mod.rs:102-108). \n\nWritten as nested Bool.rec, not as a Bool.and, and the shape is the point: the emitted body has no `and` instruction -- the short circuit is a CONTROL-FLOW fact, two condbrs and a false-materializing block, and the reflected function mirrors that. Bool.rec's minor order is (false, true), so the FIRST minor of the outer recursion is the else branch (bounded: lower AND upper) and the second is the then branch (unbounded: lower only). DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESU32VAL, "EncodesU32Val r n: the runtime value r is the integer n. \n\nThe thinnest representation premise in the program, and honestly so: this body takes three u32 arguments BY VALUE, performs no load, and touches no aggregate -- so the only thing a premise can say is that each argument arrived as an integer scalar rather than as a pointer, a bool or an undef. It is not decorative: ir_int2 faults type_error not_int on anything else, so without it A4 is false. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NL3, "ir_nl3: three-element id list -- the first three-parameter function in the program. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_IR_VL3,
            "ir_vl3: three-element value list. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_IR_BR_B0, "ir_br_b0: entry block, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/bvar_in_range.trust-ir.txt). Materialize u32::MAX into %5, compare end against it into %6, and CONDBR -- the first conditional branch any chain in this program has contained. Then-target bb1 (the unbounded case), else-target bb2. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_B1, "ir_br_b1: the unbounded arm. One comparison, `idx >= start`, straight into the outer join at bb3. Note it does NOT go through bb6: the two arms of the source `if` reach the return by different routes, and a transcription that funnelled both through the inner join would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_B2, "ir_br_b2: the bounded arm's FIRST half. It recomputes `idx >= start` into a DIFFERENT SSA id (%8, where bb1 used %7) and branches on it -- this is the short circuit: if the lower bound fails the upper bound is never evaluated. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_B3, "ir_br_b3: the OUTER join, taking a bool block parameter, and the only block that returns. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_B4, "ir_br_b4: the short circuit's taken side -- evaluate `idx < end` and carry it to the inner join. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_B5, "ir_br_b5: the short circuit's untaken side -- materialize `false` WITHOUT evaluating the upper bound. This block is the entire operational content of `&&` and it is the only place a constant appears in this body's answer path. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_B6, "ir_br_b6: the INNER join, taking a bool block parameter and immediately branching to the OUTER join with it. Two join blocks in a chain: a transcription that collapsed them into one would agree on every answer and be a different graph, which is why the branch lane compares bb6 -> bb3 explicitly. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_FUNC, "ir_br_func: expr::bvar_in_range as EvalIR -- THREE parameters (idx, start, end at SSA ids 0,1,2), entry block 0, seven blocks, matching the emitted control-flow graph exactly. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_MODULE, "ir_br_module: the module for expr::bvar_in_range, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel, recorded at tests/fixtures/bvar_in_range.trust-ir.txt and checked graph-for-graph and instruction-for-instruction, including the condbr lane, by tests/crystal_a1_lineage/bvar_in_range.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_CFG_MACH, "ir_cfg_mach: the machine inside a running configuration, with an explicit default for the halted case. A total projection rather than a partial one, so no premise is needed to use it; the default is never reached in this chain because the two steps it is applied to both bind a value. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_MACH0, "ir_br_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds THREE parameters positionally. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_M1, "ir_br_m1: the machine after ONE step, with the materialized u32::MAX bound at %5. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_M2, "ir_br_m2: the machine after TWO steps, with the first comparison's result ABSTRACTED to a Bool parameter. \n\nThis is the device the whole proof turns on. ir_condbr_exec dispatches with Bool.rec on the scrutinee, and this body's scrutinee is a computed Bool over symbolic u32 residues, so the machine is stuck there and no amount of fuel unsticks it. Abstracting the bound value makes the scrutinee a VARIABLE that Bool.rec can eliminate. It is not a different program: at b := ir_br_c1 e this term is DEFINITIONALLY ir_step applied twice to ir_br_mach0, which is exactly what ir_br_exact relies on. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_M3, "ir_br_m3: the machine at bb2 after the first condbr took its ELSE edge. Stated as ir_step of ir_br_m2 at Bool.false rather than as a literal, so it cannot drift from what the machine actually does. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_M4, "ir_br_m4: the machine at bb2 with the SECOND comparison's result abstracted -- the same device again, for the short circuit's condbr. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_SPLIT2, "ir_br_split2: the INNER case analysis. For either value of the short circuit's condition the machine runs to a return in exactly 5 steps: true goes bb4 -> bb6 -> bb3 evaluating the upper bound, false goes bb5 -> bb6 -> bb3 materializing Bool.false without evaluating it. Both minors are Eq.refl -- once the scrutinee is a literal the machine computes. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_SPLIT1, "ir_br_split1: the OUTER case analysis. The TRUE minor (the sentinel matched) computes to a return in 7 steps through bb1 and is Eq.refl; the FALSE minor is not, and cannot be -- it lands on the second condbr, so it hands off to ir_br_split2 instantiated at the real second condition. The two step counts differ (4 and 7 from this machine) and ir_run tolerates surplus fuel, which is why one bound covers both. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_TWO_STEPS, "ir_br_two_steps: the machine after exactly TWO steps IS ir_br_m2 at the real first condition -- the const_ and the icmp, and NOT the condbr. \n\nThe kernel runs two steps and compares two configurations, so the check is bounded by the size of two instructions' semantics rather than by whatever the machine gets stuck on afterwards. Measured 0.006s. It is NOT what unblocked this chain: see ir_br_c1: the blocker was the reflected predicate naming the sentinel instead of carrying the literal the emitted body materializes, which made the kernel decide a width-32 residue (~2^32 Nat.rec unfoldings). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_EXACT, "ir_br_exact: the machine agrees with the reflected bvar_in_range at EXACTLY 9 steps, for arbitrary idx, start and end. \n\n9 = 7 + 2, and the proof is exactly that split: ir_run_steps_split (a GENERAL lemma of the semantics, already kernel-checked in add_eval_ir_steps) peels the first two steps into ir_steps ir_d2, ir_br_two_steps identifies that configuration with ir_br_m2 at the real first condition, and the outer case analysis finishes the remaining 7. The reflected function is defined in the same nested-Bool.rec shape precisely so that instantiating ir_br_split1 at ir_br_c1 e is definitionally the goal. Measured 0.013s; the one-line instantiation checks in 0.010s and is not used, because a structural bound is worth more than a measured one. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_CORRECT, "ir_br_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE, FOR A BODY WITH BRANCHES. *** For every idx, start and end, every value representing them, every heap, every next-address counter and every fuel at or above 9, ir_eval on ir_br_module returns exactly IROutcome.ret [bool (expr_bvar_in_range idx start end)]. \n\nThe first chain in the program over a body that BRANCHES on a value it computed: two condbrs, four icmps, seven blocks, two join blocks. Proved by EncodesU32Val.rec three times, nested, one per parameter. \n\nA0 is measured on the SHIPPED kernel at clean c4e33541d: lowered, spliced, unsupported [], derived_mir.verdict agreed (10 canonical lines identical), markers_exact TRUE over TWENTY-ONE REAL MARKER LINES, the producer's own interpreter differential agreed on 125 sampled inputs, zero calls so the reachable closure is bodyful, and a codegen flip event whose A-LIN lineage equals the coverage row's. A1 is gated by tests/crystal_a1_lineage/bvar_in_range.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_MACHINE_SOUND, "ir_br_machine_sound: *** A5, THE INVERSION. *** If the MACHINE answers c, then the reflected bvar_in_range IS c -- for every c. Goes through A4 rather than restating it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_BVAR_TRUE_IMPLIES_LOWER, "bvar_true_implies_lower: if the reflected predicate holds then the LOWER BOUND held -- on both sides of the sentinel test, which is the content of the claim. By Bool.rec on the lower-bound condition: when it is false both branches of the outer recursion reduce to Bool.false, so the hypothesis is Eq Bool Bool.false Bool.true and is returned unchanged as the absurd-case witness; when it is true the goal is Eq.refl. The outer condition ir_br_c1 e is eliminated too, because the false case has to hold whichever way the sentinel test went. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_MACHINE_SOUND_LOWER, "ir_br_machine_sound_lower: *** A5 REACHING PAST THE MACHINE'S ANSWER. *** If the machine running the EMITTED body answers true, then idx >= start -- a fact about the ARGUMENTS, extracted from a fact about the OUTCOME. \n\nThis is the analogue of ir_ko_machine_sound_denot for a body with no denotational semantics to compose with: rather than stopping at 'the reflected function is true', it decides one of the two comparisons the body performs. It is one-directional and necessarily so -- idx >= start does not imply the predicate, because the upper bound may fail. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_NEVER_FAULTS, "ir_br_never_faults: *** NO UB, NO PANIC, NO EXHAUSTION -- on any represented triple. *** A corollary of A4. Concretely for this body: no comparison faults not_int, neither condbr faults not_bool, no block runs off its end, both joins bind their parameters, and 9 steps always suffice. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_PATH_UNBOUNDED, "PATH WITNESS: the sentinel matched -- bb0 -> bb1 -> bb3, the arm with no upper bound. The kernel RUNS the machine for seven steps with the first condition supplied as Bool.true and gets the lower-bound comparison back. \n\nThis is the ONE path that still has no concrete counterpart, and the reason changed on 2026-08-15. It WAS the residue: deciding ir_wrap ir_d32 of the sentinel cost on the order of its 4.29e9 dividend, and the first draft of this module had five concrete witnesses that hung the spec build. The ir_wrap literal-folding lemma (ir_nat_ltb_sub_eq, eval_ir_state) folds that residue in 0.007 s, and three concrete witnesses are now registered below. What blocks THIS path is a different walk: reaching it needs end = 4294967295, and ir_nat_eqb recurses on its FIRST operand, so the comparison itself is 4.29e9 Nat.rec steps whatever ir_wrap costs. An ir_nat_eqb lemma of the same shape would close it; that is a named build item, not a claim made here. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_PATH_BOUNDED, "PATH WITNESS: the sentinel did not match -- bb0 -> bb2, the arm that still has to decide the short circuit. Its answer is the nested case analysis, unresolved, which is exactly the shape the source's `&&` has. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_PATH_UPPER, "PATH WITNESS: the short circuit TAKEN -- bb2 -> bb4 -> bb6 -> bb3, evaluating the upper bound and carrying it through BOTH join blocks. Five steps, four of the seven blocks. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_PATH_SHORT_CIRCUIT, "PATH WITNESS: the short circuit NOT taken -- bb2 -> bb5 -> bb6 -> bb3, materializing Bool.false WITHOUT evaluating the upper bound. This is the arm bb5 exists for and the executable content of `&&`: the machine answers false having never touched `end`. A transcription that used a Bool.and instead of a branch would not have this path at all. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_CONCRETE_IN_RANGE, "*** CONCRETE EXECUTION WITNESS -- the first this chain has ever had. *** idx = 3, start = 1, end = 5: the kernel runs the emitted module for nine steps, DECIDES BOTH condbr scrutinees (including the sentinel test, whose right operand is the twice-wrapped u32::MAX literal), takes bb0 -> bb2 -> bb4 -> bb6 -> bb3, and returns Bool.true. \n\nUntil 2026-08-15 no such declaration could exist at ANY argument: putting ir_wrap ir_d32 (ir_wrap ir_d32 4294967295) in Nat.succ form was extrapolated at ~9.6 days, and the module's four PATH witnesses exist because of it. The ir_wrap literal-folding lemma folds it in 0.007 s. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_CONCRETE_ABOVE_END, "*** CONCRETE EXECUTION WITNESS: the upper bound REJECTS. *** idx = 9 against [1, 5): the lower test holds, the machine reaches bb4, evaluates 9 < 5 and answers false through the inner join. This is the arm the short circuit did NOT take, run at real numbers rather than at a supplied Bool. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_CONCRETE_BELOW_START, "*** CONCRETE EXECUTION WITNESS: the SHORT CIRCUIT, executed. *** idx = 0 against [1, 5): the lower test fails, so the machine goes bb2 -> bb5 -> bb6 -> bb3 and answers false having NEVER evaluated `idx < end`. The path witness for this edge supplies the condition as a literal Bool; this one makes the machine compute it, which is the difference between showing the edge exists and showing the body takes it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_CONCRETE_UNBOUNDED, "*** CONCRETE EXECUTION WITNESS: THE SENTINEL PATH, EXECUTED. *** end = u32::MAX, so the machine DECIDES the sentinel test itself, takes bb0 -> bb1 -> bb3 -- the arm with no upper bound -- evaluates 3 >= 1 and returns Bool.true in nine steps. \n\nThis is the path the module doc has called PATH-only since this chain landed, through two separate walls. It was the residue (~9.6 days, extrapolated); the ir_wrap folding lemma removed that on 2026-08-15 and the reason MOVED to ir_nat_eqb, which peeled the sentinel 4.29e9 unary steps -- that was written down as a named build item, not as a claim. ir_nat_eqb_walk_eq is that item: `a == b` iff `a - b` and `b - a` are both zero, kernel-checked equal to the walk at every pair of arguments, so both operands go through one native BigNat subtraction. Measured 0.010 s. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_CONCRETE_UNBOUNDED_BELOW_START, "*** CONCRETE EXECUTION WITNESS: the sentinel path ANSWERS FALSE. *** Same edge, idx = 0 against start = 1: the arm with no upper bound is not constant-true, it returns the lower comparison, and here that comparison fails. Registered next to its sibling for the reason the fourth chain's differential vectors exist -- a single true-answering witness on an arm cannot tell `returns the lower bound` from `returns true`. Measured 0.010 s. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_CORRECT_WITNESS, "ir_br_correct_witness: A4's premises are all SATISFIABLE, discharged concretely -- the empty heap, the exact fuel bound by Le.refl, and three EncodesU32Val.mk. The arguments stay universally quantified here so the witness is cheap; the concrete runs are ir_br_concrete_in_range and its two siblings. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_BR_MACHINE_SOUND_WITNESS, "ir_br_machine_sound_witness: A5's premises are SATISFIABLE, including the observation premise -- which is supplied by A4 itself rather than by an Eq.refl, because the machine's answer is not computable here. Its conclusion is reflexive and the description says so rather than dressing it up: this witnesses non-vacuity of the hypotheses, not an independent fact. The information-bearing consequence of A5 is ir_br_machine_sound_lower, whose conclusion is about the ARGUMENTS. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

// The acceptance tests, moved to a sibling file VERBATIM on 2026-08-17 —
// module body unchanged, no assertion and no test name touched. This file
// stood at 532 lines against the 500-line convention that
// `data/paragon_ratchet.json`'s `files_over_500` enforces shrink-only, and
// the boundary is the one `eval_ir_float_fin_witnesses.rs` already used.
#[cfg(test)]
#[path = "eval_ir_bvar_range_tests.rs"]
mod tests;
