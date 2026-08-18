// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The SIXTH complete width-one chain — the second and last body in
//! `clean-kernel` that BRANCHES: `env::native_reducers_char::is_valid_char`.**
//!
//! ```text
//! pub(crate) fn is_valid_char(n: u64) -> bool {
//!     n < 0xD800 || (0xDFFF < n && n < 0x0011_0000)
//! }
//! ```
//!
//! Seven blocks, three `icmp`s, **two `condbr`s**, two join blocks, three `u64`
//! constants and two `bool` constants. Measured at HEAD it is the ONLY
//! chainable body besides `expr::bvar_in_range` that emits a conditional branch
//! at all, and the more informative of the two on three axes stated below.
//!
//! ## What is new here, over all five earlier chains
//!
//! | axis | chains 1–5 | `is_valid_char` |
//! |---|---|---|
//! | integer width | 8 (`contains`), 32 (`bvar_in_range`) | **64** |
//! | constant operand position | always the RIGHT operand | **LEFT, once** (`icmp ult u64 %5, %0`) |
//! | short circuit | `&&` only (`bvar_in_range`) | **`||` AND `&&`, nested** |
//! | concrete `ir_eval` witness over a `condbr` (as of 2026-08-14) | **none exists** (`bvar_in_range`, measured) | **one, executed, 24.4 s** |
//! | …the same row on 2026-08-15, after the `ir_wrap` folding lemma | **three** (the sentinel path still walks `ir_nat_eqb`) | still one — every argument RUNS now, but a run costs its own code point (see below) |
//! | `markers_exact` | vacuous on 1–3, 8 and 21 lines on 4–5 | **12 real marker lines** |
//!
//! ### The left-hand constant is the structurally new thing
//!
//! `bb1` emits `icmp ult u64 %5, %0` — the materialised `0xDFFF` on the LEFT.
//! `ir_int_cmp` canonicalises both operands, so the reflected predicate
//! `ir_vc_c2` is `ir_nat_ltb (ir_wrap ir_d64 (ir_wrap ir_d64 57343)) (...)`:
//! the FIRST argument of `ir_nat_ltb` is concrete. `ir_nat_ltb` recurses on its
//! first argument, so unlike every earlier chain the kernel must actually
//! REDUCE a residue here rather than leave it stuck under a symbolic operand.
//! It costs 24 s in `ir_vc_split1`, measured, and it is paid once per spec
//! build. The alternative — writing the single wrap, or naming the constant —
//! is a claim rather than a transcription, and the second of those is exactly
//! what cost the fifth chain its registration.
//!
//! **Superseded 2026-08-15 for the definition, not for the measurement.** Both
//! laws below were measured on an `ir_div_go` whose guard was `ir_nat_ltb`, a
//! paired unary walk. That guard is now `ir_nat_ltb_sub` — proved equal to it
//! by `ir_nat_ltb_sub_eq` — and the cost is **linear in the QUOTIENT and
//! independent of the dividend**: this body's residues have quotient zero and
//! fold in ~0.01 s each. Read the two sections that follow as the history of a
//! wall that is gone, not as the current cost model. The 24 s figure above is
//! now 0.010 s, measured.
//!
//! ## The cost law, RE-MEASURED — and it is not the one on record
//!
//! `docs/CRYSTAL_STATUS.md` §3c, this repository's `bundles.rs`, and the fifth
//! chain's module doc all record a **`2^W` law**: "×15.3 per four bits",
//! measured at W = 8 / 12 / 16 on `Eq Nat (ir_wrap ir_dW k) (ir_wrap ir_dW k)`.
//! Those three timings are real. **The law read off them is wrong, and this
//! chain is where it had to be settled, because this chain is at width 64 —
//! twice the fifth chain's — and on the old law it could not have existed.**
//!
//! Measured here, at HEAD, in `evalir_scratchpad` (one declaration each,
//! per-declaration wall clock):
//!
//! ```text
//! Eq Nat (ir_wrap w n) n            w = 64   n =      3      0.010 s
//!                                   w = 64   n =  7,000      1.322 s
//!                                   w = 64   n = 14,000      2.644 s
//!                                   w = 64   n = 28,000      5.399 s
//!                                   w =  8   n =  7,000      1.356 s
//!                                   w = 32   n = 55,296     11.123 s
//!                                   w = 64   n = 55,296     10.909 s
//! ```
//!
//! **The cost is LINEAR IN THE DIVIDEND and independent of the WIDTH.**
//! Doubling `n` doubles the wall (1.322 → 2.644 → 5.399); moving `w` from 8 to
//! 64 at a fixed `n` changes nothing (1.356 vs 1.322). The reason is in the
//! definitions and not in the timings: `ir_wrap w n` is
//! `ir_nat_rem n (ir_nat_pow2 w)`, `ir_nat_div` is fuelled by its own DIVIDEND,
//! and `ir_div_go`'s guard is `ir_nat_ltb n (2^w)` which recurses on `n`.
//! `ir_nat_pow2 w` costs `w` additions and nothing more.
//!
//! The earlier W = 8 / 12 / 16 measurement varied the width **and the dividend
//! together** — its dividend was the sentinel `2^W - 1` each time, i.e. 255,
//! 4,095, 65,535 — so the ×15.3 it observed is the ×16 in the DIVIDEND. The
//! ~5-day extrapolation it drew for `ir_wrap ir_d32 4294967295` stands, and by
//! this law lands at ≈ 9.6 days (4,294,967,295 × 1.93e-4 s), the same order for
//! a different reason.
//!
//! **Why the correction matters operationally:** "wide type ⇒ unaffordable" is
//! false and would have refused this body. The rule is "large CONSTANT ⇒
//! unaffordable". `is_valid_char` is at width 64 with constants 55,296 / 57,343
//! / 1,114,112, and it chains.
//!
//! ## Witnesses: one CONCRETE execution, and the measured reason there is one
//!
//! The fifth chain has **no** concrete `ir_eval` witness at any argument — its
//! sentinel is `u32::MAX`, a ~4.3e9 dividend. Here the whole machine run is
//! affordable, so `ir_vc_concrete_ascii` is a real end-to-end execution of a
//! branching body by the kernel, deciding its own scrutinee — the first in this
//! program. Measured, one declaration each:
//!
//! ```text
//! ir_eval ir_d11 … (int_ 65)      -> ret [bool true]     24.4 s   REGISTERED
//! ir_eval ir_d11 … (int_ 0)       -> ret [bool true]     36.8 s
//! ir_eval ir_d11 … (int_ 55296)   -> ret [bool false]    73.8 s   (the surrogate arm)
//! Eq Bool (ir_vc_c1 ir_d0) Bool.true                     21.1 s
//! Eq Bool (ir_vc_c2 ir_d0) Bool.false                    22.5 s
//! Eq Bool (ir_vc_c3 ir_d0) Bool.true                    439.8 s   (dividend 1,114,112)
//! ```
//!
//! Exactly ONE was registered, and the reason was the cost column rather than a
//! preference: every argument whose emitted path reaches `bb4` had to decide
//! `ir_vc_c3`, i.e. pay ≈ 7.3 minutes on every `Specification::new()`. The four
//! PATH witnesses cover all four `condbr` edges at no such cost, exactly as the
//! fifth chain's do.
//!
//! ### 2026-08-15: the cost column collapsed, and the reason moved
//!
//! The `ir_wrap` literal-folding lemma (`ir_nat_ltb_sub_eq` in
//! [`super::eval_ir_state`]) replaces `ir_div_go`'s guard with a native
//! `Nat.sub` test and PROVES the two guards are the same predicate. The
//! residues this body forces stop being walks:
//! `ir_wrap ir_d64 (ir_wrap ir_d64 57343)` measured **24.973 s** before and
//! **0.009 s** after; deciding `ir_vc_c3` at an argument was **439.8 s** and is
//! **0.008 s**; `ir_vc_concrete_ascii` was 24.4 s and is **0.065 s**.
//!
//! **Every argument now RUNS, and this module still registers ONE concrete
//! witness. The reason is still the cost column — a different column.** With the
//! residue free, what a concrete execution costs is `ir_nat_ltb` peeling its
//! FIRST operand, and that operand is the CODE POINT. Measured, one declaration
//! each, on the full spec:
//!
//! ```text
//! ir_eval ir_d11 … (int_ 65)        -> ret [bool true]     0.065 s  REGISTERED
//! ir_eval ir_d11 … (int_ 0)         -> ret [bool true]     0.052 s
//! ir_eval ir_d11 … (int_ 55296)     -> ret [bool false]   19.106 s  declined
//! ir_eval ir_d11 … (int_ 70000)     -> ret [bool true]    31.404 s  declined
//! ir_eval ir_d11 … (int_ 1114112)   -> ret [bool false]  210.144 s  declined
//! ```
//!
//! Covering the remaining `condbr` edges concretely means an argument above
//! 0xD800 by construction, so it cannot cost less than ~55,296 peels. 260 s on
//! every `Specification::new()`, against a lemma that saves 33–107 s of one, is
//! the exact trade this lemma exists to stop making — so the three are recorded
//! with their measurements and not registered. The fifth chain's concrete
//! witnesses ARE registered, at 0.1 s each, because its arguments are small;
//! the honest reading is that the lemma unblocked both bodies and only one of
//! them is affordable. An `ir_nat_ltb` lemma of the same shape as
//! `ir_nat_ltb_sub_eq` — for the comparison rather than for the division guard
//! — is what would buy the rest.
//!
//! ### 2026-08-15, later: that lemma exists, and ALL FOUR EDGES now RUN
//!
//! `ir_nat_ltb_walk_eq` ([`super::eval_ir_state`]) is the named build item
//! above, proved: `ir_nat_ltb` decides through `Nat.sub` and is kernel-checked
//! equal to the paired unary walk (kept as `ir_nat_ltb_walk`) at every pair of
//! arguments, and `ir_icmp_ult_walk` restates that at the INSTRUCTION — the
//! `icmp ult` this body emits three times. All three of this module's
//! comparisons are `ult`, so all three fold, and the three declined witnesses
//! were re-run and registered:
//!
//! ```text
//!                                    walk (same box, same window)   folded
//! ir_eval … (int_ 55296)  -> false        3.071 s                   0.016 s
//! ir_eval … (int_ 70000)  -> true         5.045 s                   0.017 s
//! ir_eval … (int_ 1114112)-> false       33.752 s                   0.016 s
//! ```
//!
//! (The 19.106 / 31.404 / 210.144 s on record for the same three declarations
//! were measured on a box carrying six concurrent spec builds. The column above
//! re-measures the baseline in the same window as the folded run, so the ratio
//! is this box's and not a comparison across two of them.)
//!
//! With `ir_vc_concrete_ascii` that is **every emitted `condbr` edge, executed
//! at a real code point**: 65 takes bb0 → bb2, 55296 takes bb1 → bb5 (the short
//! circuit, never materializing 0x110000), 70000 takes bb1 → bb4 with the upper
//! bound holding, and 1114112 takes bb1 → bb4 with it rejecting. This stage
//! measured 0.651 s before the comparison lemmas and **0.512 s after, with the
//! three extra executions in it**; the +5.1 s those lemmas cost a full spec
//! build is paid entirely by the FOURTH chain, not by this one — see
//! [`super::eval_ir_state`] for the per-stage measurement.
//!
//! The PATH witnesses stay, and they still say something a concrete run does
//! not: that the edge is taken for EVERY argument reaching it. A concrete run
//! says something they do not — that the machine decides its own scrutinee
//! rather than being handed it. Now this chain has both, on all four edges.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! Every residue is taken TWICE (`IRInst.const_` canonicalises the literal and
//! `ir_int_cmp` canonicalises both operands again). That is what the machine
//! computes, so it is what the reflected predicate says; collapsing it needs
//! `ir_wrap` idempotence, which is proved nowhere here.
//!
//! `env_is_valid_char` is stated in the machine's own width-64 vocabulary. It is
//! a refinement of the emitted body against a `u64`-level specification, **not**
//! against the Unicode scalar-value predicate; "the surrogate block is
//! excluded" appears here only as `ir_vc_machine_sound_not_surrogate`, whose
//! conclusion is about `ir_vc_c1` / `ir_vc_c2` and not about Unicode.
//!
//! The link between the proved module and the emitted one is STRUCTURAL —
//! `tests/crystal_a1_lineage/is_valid_char.rs`. Everything past the flip seam is
//! downstream and covered by nothing here. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_IR_D64: &str = "def ir_d64 : Nat := Nat.add ir_d32 ir_d32";
const SRC_IR_VC_TU64: &str = "def ir_vc_tu64 : IRTy := IRTy.uint_ ir_d64";
const SRC_IR_VC_C1: &str = "def ir_vc_c1 (n : Nat) : Bool := ir_nat_ltb (ir_wrap ir_d64 n) (ir_wrap ir_d64 (ir_wrap ir_d64 55296))";
const SRC_IR_VC_C2: &str = "def ir_vc_c2 (n : Nat) : Bool := ir_nat_ltb (ir_wrap ir_d64 (ir_wrap ir_d64 57343)) (ir_wrap ir_d64 n)";
const SRC_IR_VC_C3: &str = "def ir_vc_c3 (n : Nat) : Bool := ir_nat_ltb (ir_wrap ir_d64 n) (ir_wrap ir_d64 (ir_wrap ir_d64 1114112))";
const SRC_ENV_IS_VALID_CHAR: &str = "def env_is_valid_char (n : Nat) : Bool := Bool.rec (fun (_ : Bool) => Bool) (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_vc_c3 n) (ir_vc_c2 n)) Bool.true (ir_vc_c1 n)";
const SRC_ENCODESU64VAL: &str = "inductive EncodesU64Val : IRScalar -> Nat -> Type\n| mk : forall (n : Nat), EncodesU64Val (IRScalar.int_ n) n";
const SRC_IR_VC_B0: &str = "def ir_vc_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 55296)) ir_d3) (ir_nd1 (IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d0 ir_d3) ir_d4) (ir_nd (IRInst.condbr ir_d4 ir_d2 ir_nl0 ir_d1 ir_nl0)))";
const SRC_IR_VC_B1: &str = "def ir_vc_b1 : IRBlock := IRBlock.mk ir_d1 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 57343)) ir_d5) (ir_nd1 (IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d5 ir_d0) ir_d6) (ir_nd (IRInst.condbr ir_d6 ir_d4 ir_nl0 ir_d5 ir_nl0)))";
const SRC_IR_VC_B2: &str = "def ir_vc_b2 : IRBlock := IRBlock.mk ir_d2 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ IRTy.bool_ (IRConst.bool_ Bool.true)) ir_d7) (ir_nd (IRInst.br ir_d3 (ir_nl1 ir_d7))))";
const SRC_IR_VC_B3: &str = "def ir_vc_b3 : IRBlock := IRBlock.mk ir_d3 (ir_nl1 ir_d1) (ir_bd1 (ir_nd (IRInst.ret (ir_nl1 ir_d1))))";
const SRC_IR_VC_B4: &str = "def ir_vc_b4 : IRBlock := IRBlock.mk ir_d4 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 1114112)) ir_d8) (ir_nd1 (IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d0 ir_d8) ir_d9) (ir_nd (IRInst.br ir_d6 (ir_nl1 ir_d9))))";
const SRC_IR_VC_B5: &str = "def ir_vc_b5 : IRBlock := IRBlock.mk ir_d5 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ IRTy.bool_ (IRConst.bool_ Bool.false)) ir_d10) (ir_nd (IRInst.br ir_d6 (ir_nl1 ir_d10))))";
const SRC_IR_VC_B6: &str = "def ir_vc_b6 : IRBlock := IRBlock.mk ir_d6 (ir_nl1 ir_d2) (ir_bd1 (ir_nd (IRInst.br ir_d3 (ir_nl1 ir_d2))))";
const SRC_IR_VC_FUNC: &str = "def ir_vc_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_vc_b0 (ir_blk ir_vc_b1 (ir_blk ir_vc_b2 (ir_blk ir_vc_b3 (ir_blk ir_vc_b4 (ir_blk ir_vc_b5 (ir_blk ir_vc_b6 ir_blk0)))))))";
const SRC_IR_VC_MODULE: &str = "def ir_vc_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_vc_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";
const SRC_IR_VC_MACH0: &str = "def ir_vc_mach0 (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 (IRScalar.int_ n)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";
const SRC_IR_VC_M1: &str = "def ir_vc_m1 (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := ir_cfg_mach (ir_bind_result (ir_vc_mach0 n mem na) (ir_nl1 ir_d3) (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d64 55296)))) (ir_vc_mach0 n mem na)";
const SRC_IR_VC_M2: &str = "def ir_vc_m2 (n : Nat) (mem : IRList IRMemSlot) (na : Nat) (b : Bool) : IRMachine := ir_cfg_mach (ir_bind_result (ir_vc_m1 n mem na) (ir_nl1 ir_d4) (IRStepResult.value (IRScalar.bool_ b))) (ir_vc_mach0 n mem na)";
const SRC_IR_VC_M3: &str = "def ir_vc_m3 (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := ir_cfg_mach (ir_step ir_vc_module (ir_vc_m2 n mem na Bool.false)) (ir_vc_mach0 n mem na)";
const SRC_IR_VC_M4: &str = "def ir_vc_m4 (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := ir_cfg_mach (ir_bind_result (ir_vc_m3 n mem na) (ir_nl1 ir_d5) (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d64 57343)))) (ir_vc_mach0 n mem na)";
const SRC_IR_VC_M5: &str = "def ir_vc_m5 (n : Nat) (mem : IRList IRMemSlot) (na : Nat) (c : Bool) : IRMachine := ir_cfg_mach (ir_bind_result (ir_vc_m4 n mem na) (ir_nl1 ir_d6) (IRStepResult.value (IRScalar.bool_ c))) (ir_vc_mach0 n mem na)";
const SRC_IR_VC_SPLIT2: &str = "def ir_vc_split2 (n : Nat) (mem : IRList IRMemSlot) (na : Nat) (c : Bool) : Eq IROutcome (ir_run ir_d6 ir_vc_module (IRConfig.running (ir_vc_m5 n mem na c))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_vc_c3 n) c)))) := Bool.rec (fun (c0 : Bool) => Eq IROutcome (ir_run ir_d6 ir_vc_module (IRConfig.running (ir_vc_m5 n mem na c0))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_vc_c3 n) c0))))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (ir_vc_c3 n))))) c";
const SRC_IR_VC_SPLIT1: &str = "def ir_vc_split1 (n : Nat) (mem : IRList IRMemSlot) (na : Nat) (b : Bool) : Eq IROutcome (ir_run ir_d9 ir_vc_module (IRConfig.running (ir_vc_m2 n mem na b))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (Bool.rec (fun (_ : Bool) => Bool) (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_vc_c3 n) (ir_vc_c2 n)) Bool.true b)))) := Bool.rec (fun (b0 : Bool) => Eq IROutcome (ir_run ir_d9 ir_vc_module (IRConfig.running (ir_vc_m2 n mem na b0))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (Bool.rec (fun (_ : Bool) => Bool) (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_vc_c3 n) (ir_vc_c2 n)) Bool.true b0))))) (ir_vc_split2 n mem na (ir_vc_c2 n)) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))) b";
const SRC_IR_VC_TWO_STEPS: &str = "def ir_vc_two_steps (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_steps ir_d2 ir_vc_module (IRConfig.running (ir_vc_mach0 n mem na))) (IRConfig.running (ir_vc_m2 n mem na (ir_vc_c1 n))) := Eq.refl IRConfig (IRConfig.running (ir_vc_m2 n mem na (ir_vc_c1 n)))";
const SRC_IR_VC_EXACT: &str = "def ir_vc_exact (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d11 ir_vc_module (IRConfig.running (ir_vc_mach0 n mem na))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (env_is_valid_char n)))) := Eq.trans IROutcome (ir_run ir_d11 ir_vc_module (IRConfig.running (ir_vc_mach0 n mem na))) (ir_run ir_d9 ir_vc_module (ir_steps ir_d2 ir_vc_module (IRConfig.running (ir_vc_mach0 n mem na)))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (env_is_valid_char n)))) (ir_run_steps_split ir_vc_module ir_d9 ir_d2 (IRConfig.running (ir_vc_mach0 n mem na))) (Eq.subst IRConfig (fun (k : IRConfig) => Eq IROutcome (ir_run ir_d9 ir_vc_module k) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (env_is_valid_char n))))) (IRConfig.running (ir_vc_m2 n mem na (ir_vc_c1 n))) (ir_steps ir_d2 ir_vc_module (IRConfig.running (ir_vc_mach0 n mem na))) (Eq.symm IRConfig (ir_steps ir_d2 ir_vc_module (IRConfig.running (ir_vc_mach0 n mem na))) (IRConfig.running (ir_vc_m2 n mem na (ir_vc_c1 n))) (ir_vc_two_steps n mem na)) (ir_vc_split1 n mem na (ir_vc_c1 n)))";
const SRC_IR_VC_CORRECT: &str = "def ir_vc_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (n : Nat) (h : EncodesU64Val r n) : Le ir_d11 fuel -> Eq IROutcome (ir_eval fuel ir_vc_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (env_is_valid_char n)))) := EncodesU64Val.rec (fun (r0 : IRScalar) (n0 : Nat) (_ : EncodesU64Val r0 n0) => Le ir_d11 fuel -> Eq IROutcome (ir_eval fuel ir_vc_module ir_d0 (ir_vl1 r0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (env_is_valid_char n0))))) (fun (n1 : Nat) (hle : Le ir_d11 fuel) => ir_run_le_ret ir_vc_module ir_d11 fuel hle (IRConfig.running (ir_vc_mach0 n1 mem na)) (ir_vl1 (IRScalar.bool_ (env_is_valid_char n1))) (ir_vc_exact n1 mem na)) r n h";
const SRC_IR_VC_MACHINE_SOUND: &str = "def ir_vc_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (n : Nat) (c : Bool) (h : EncodesU64Val r n) (hle : Le ir_d11 fuel) (hret : Eq IROutcome (ir_eval fuel ir_vc_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ c)))) : Eq Bool (env_is_valid_char n) c := Eq.cong IROutcome Bool ir_outcome_bool (IROutcome.ret (ir_vl1 (IRScalar.bool_ (env_is_valid_char n)))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ c))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (env_is_valid_char n)))) (ir_eval fuel ir_vc_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ c))) (Eq.symm IROutcome (ir_eval fuel ir_vc_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (env_is_valid_char n)))) (ir_vc_correct mem fuel na r n h hle)) hret)";
const SRC_VC_TRUE_IMPLIES_NOT_SURROGATE: &str = "def vc_true_implies_not_surrogate (n : Nat) : Eq Bool (env_is_valid_char n) Bool.true -> Eq Bool (Bool.or (ir_vc_c1 n) (ir_vc_c2 n)) Bool.true := Bool.rec (fun (b0 : Bool) => Eq Bool (Bool.rec (fun (_ : Bool) => Bool) (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_vc_c3 n) (ir_vc_c2 n)) Bool.true b0) Bool.true -> Eq Bool (Bool.or b0 (ir_vc_c2 n)) Bool.true) (Bool.rec (fun (b1 : Bool) => Eq Bool (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_vc_c3 n) b1) Bool.true -> Eq Bool (Bool.or Bool.false b1) Bool.true) (fun (h : Eq Bool Bool.false Bool.true) => h) (fun (_ : Eq Bool (ir_vc_c3 n) Bool.true) => Eq.refl Bool Bool.true) (ir_vc_c2 n)) (fun (_ : Eq Bool Bool.true Bool.true) => Bool.rec (fun (b1 : Bool) => Eq Bool (Bool.or Bool.true b1) Bool.true) (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true) (ir_vc_c2 n)) (ir_vc_c1 n)";
const SRC_IR_VC_MACHINE_SOUND_NOT_SURROGATE: &str = "def ir_vc_machine_sound_not_surrogate (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (n : Nat) (h : EncodesU64Val r n) (hle : Le ir_d11 fuel) (hret : Eq IROutcome (ir_eval fuel ir_vc_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))) : Eq Bool (Bool.or (ir_vc_c1 n) (ir_vc_c2 n)) Bool.true := vc_true_implies_not_surrogate n (ir_vc_machine_sound mem fuel na r n Bool.true h hle hret)";
const SRC_IR_VC_NEVER_FAULTS: &str = "def ir_vc_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (n : Nat) (h : EncodesU64Val r n) (hle : Le ir_d11 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_vc_module ir_d0 (ir_vl1 r) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_vc_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (env_is_valid_char n)))) (ir_vc_correct mem fuel na r n h hle)";
const SRC_IR_VC_PATH_ASCII: &str = "def ir_vc_path_ascii (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d9 ir_vc_module (IRConfig.running (ir_vc_m2 n mem na Bool.true))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := ir_vc_split1 n mem na Bool.true";
const SRC_IR_VC_PATH_ABOVE_SURROGATE_START: &str = "def ir_vc_path_above_surrogate_start (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d9 ir_vc_module (IRConfig.running (ir_vc_m2 n mem na Bool.false))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_vc_c3 n) (ir_vc_c2 n))))) := ir_vc_split1 n mem na Bool.false";
const SRC_IR_VC_PATH_UPPER: &str = "def ir_vc_path_upper (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d6 ir_vc_module (IRConfig.running (ir_vc_m5 n mem na Bool.true))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (ir_vc_c3 n)))) := ir_vc_split2 n mem na Bool.true";
const SRC_IR_VC_PATH_SURROGATE: &str = "def ir_vc_path_surrogate (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d6 ir_vc_module (IRConfig.running (ir_vc_m5 n mem na Bool.false))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := ir_vc_split2 n mem na Bool.false";
const SRC_IR_VC_CONCRETE_ASCII: &str = "def ir_vc_concrete_ascii : Eq IROutcome (ir_eval ir_d11 ir_vc_module ir_d0 (ir_vl1 (IRScalar.int_ 65)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";

// ── The three that were DECLINED on 2026-08-15, now REGISTERED ────────────
//
// They were written and kernel-checked then, and declined with their numbers:
// 19.106 s at 55296, 31.404 s at 70000, 210.144 s at 1114112 — 260 s on every
// `Specification::new()`, because `ir_int_cmp` compared through an
// `ir_nat_ltb` that peeled its FIRST operand, and that operand is the CODE
// POINT. The comparison-folding lemmas (`ir_nat_ltb_walk_eq` /
// `ir_nat_eqb_walk_eq`, `eval_ir_state`) remove exactly that peel, and the
// same three declarations now measure **0.016 / 0.017 / 0.016 s** — with the
// same-box baseline re-measured in the same window at 3.071 / 5.045 /
// 33.752 s, so the ratio is measured on this box and not carried over from
// another one.
//
// Together with `ir_vc_concrete_ascii` they cover ALL FOUR emitted `condbr`
// edges concretely: 65 goes bb0 -> bb2 (below the surrogate block), 55296 goes
// bb1 -> bb5 (inside it, short-circuiting), 70000 goes bb1 -> bb4 (above it,
// upper bound holds) and 1114112 goes bb1 -> bb4 (above it, upper bound
// REJECTS). The PATH witnesses stay: they say the edge is taken for EVERY
// argument reaching it, which no concrete run says.
const SRC_IR_VC_CONCRETE_SURROGATE: &str = "def ir_vc_concrete_surrogate : Eq IROutcome (ir_eval ir_d11 ir_vc_module ir_d0 (ir_vl1 (IRScalar.int_ 55296)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";

const SRC_IR_VC_CONCRETE_ABOVE_SURROGATE: &str = "def ir_vc_concrete_above_surrogate : Eq IROutcome (ir_eval ir_d11 ir_vc_module ir_d0 (ir_vl1 (IRScalar.int_ 70000)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";

const SRC_IR_VC_CONCRETE_OUT_OF_RANGE: &str = "def ir_vc_concrete_out_of_range : Eq IROutcome (ir_eval ir_d11 ir_vc_module ir_d0 (ir_vl1 (IRScalar.int_ 1114112)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";
const SRC_IR_VC_CORRECT_WITNESS: &str = "def ir_vc_correct_witness (n : Nat) : Eq IROutcome (ir_eval ir_d11 ir_vc_module ir_d0 (ir_vl1 (IRScalar.int_ n)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (env_is_valid_char n)))) := ir_vc_correct ir_mem0 ir_d11 ir_d0 (IRScalar.int_ n) n (EncodesU64Val.mk n) (Le.refl ir_d11)";
const SRC_IR_VC_MACHINE_SOUND_WITNESS: &str = "def ir_vc_machine_sound_witness (n : Nat) : Eq Bool (env_is_valid_char n) (env_is_valid_char n) := ir_vc_machine_sound ir_mem0 ir_d11 ir_d0 (IRScalar.int_ n) n (env_is_valid_char n) (EncodesU64Val.mk n) (Le.refl ir_d11) (ir_vc_correct_witness n)";

impl Specification {
    /// Register the SIXTH complete width-one chain, and the second (and last)
    /// over a body with a conditional branch:
    /// `env::native_reducers_char::is_valid_char`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_valid_char(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_IR_D64, "ir_d64: the machine width this body works at -- SIXTY-FOUR, twice the fifth chain's. Reachable only because the residue cost law is linear in the DIVIDEND and independent of the width (measured: 1.356 s at w=8 vs 1.322 s at w=64, same dividend 7000), which is the opposite of what this repository had on record. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_TU64, "ir_vc_tu64: u64, the type all three comparisons are at. ir_int_cmp reads the width off it and canonicalizes BOTH operands at that width, so a body transcribed at the wrong width computes a different function. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_C1, "ir_vc_c1: the first comparison the emitted body performs -- `n < 0xD800` at u64, IRICmpOp.ult with the constant on the RIGHT. The residue is taken twice because IRInst.const_ canonicalizes the literal and ir_int_cmp canonicalizes both operands again; that is what the machine computes and collapsing it needs ir_wrap idempotence, which is proved nowhere here. The sentinel is the LITERAL 55296 the emitted IRInst.const_ carries and must stay the literal -- naming it is what cost the fifth chain its registration. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_C2, "ir_vc_c2: `0xDFFF < n` at u64 -- and the STRUCTURALLY NEW declaration in this chain. The emitted instruction is `icmp ult u64 %5, %0`: the materialized constant is the LEFT operand, which no earlier chain has. ir_nat_ltb recurses on its FIRST argument, so this is the first reflected predicate whose residue the kernel must actually reduce rather than leave stuck under a symbolic operand. Measured cost: 24 s inside ir_vc_split1, paid once per spec build. Writing the single wrap instead would be a claim, not a transcription. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_C3, "ir_vc_c3: `n < 0x110000` at u64, reached only when the sentinel test failed AND the lower surrogate bound was cleared -- the right-hand operand of the source's short-circuit &&, made explicit as control flow by the emitted CFG. Its dividend is 1,114,112, which is why no concrete witness in this module reached it until 2026-08-15: deciding it at one argument measured 439.8 s and now measures 0.008 s, because the ir_wrap literal-folding lemma makes the residue independent of the dividend (its quotient is zero). What is still linear in the ARGUMENT is ir_nat_ltb's own peel, which is why the concrete runs that reach this comparison (31.4 s at 70000, 210.1 s at 1114112, both measured and both passing) are recorded in the module doc rather than registered. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ENV_IS_VALID_CHAR, "env_is_valid_char: the reflected env::native_reducers_char::is_valid_char (native_reducers_char.rs:111-113). \n\nWritten as nested Bool.rec, and the shape mirrors the emitted CFG rather than the source's `||` and `&&`: the emitted body contains no `or` and no `and` instruction, both short circuits are branches. Bool.rec's minor order is (false, true), so the FIRST minor of the outer recursion is the `n >= 0xD800` arm (which still has to decide the surrogate range) and the second is the plain `true` arm. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESU64VAL, "EncodesU64Val r n: the runtime value r is the integer n. \n\nDeliberately NOT a reuse of EncodesU32Val even though the two inductives have the same shape. That relation is named for a width and this body is at another; sharing it would make one of the two names false, and it is the naming -- not the shape -- that the vacuity firewall and the premise-witness gate audit. It is not decorative either: this body takes its argument BY VALUE, performs no load and touches no aggregate, so the only thing a premise can say is that the argument arrived as an integer scalar rather than as a pointer, a bool or an undef -- and ir_int2 faults type_error not_int on anything else, so without it A4 is false. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_B0, "ir_vc_b0: entry block, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/is_valid_char.trust-ir.txt). Materialize 0xD800 into %3, compare n against it into %4, and CONDBR. Then-target bb2 (the immediate `true`), else-target bb1 -- the OPPOSITE polarity to the fifth chain's entry condbr, which is precisely the drift the condbr lane of the CFG gate exists to catch. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_B1, "ir_vc_b1: the `||`'s right-hand side. Materialize 0xDFFF into %5 and compare it against n with the CONSTANT AS THE LEFT OPERAND (`icmp ult u64 %5, %0`), then branch. Swapping the two operands turns `0xDFFF < n` into `n < 0xDFFF` and changes the function; the icmp lane compares operand order and result id, so it fails here. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_B2, "ir_vc_b2: the first disjunct held -- materialize Bool.true and go straight to the OUTER join. It does not pass through bb6: the two sides of the `||` reach the return by different routes, and a transcription that funnelled both through the inner join would be a different CFG. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_B3, "ir_vc_b3: the OUTER join, taking a bool block parameter, and the only block that returns. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_B4, "ir_vc_b4: the `&&`'s taken side -- materialize 0x110000 and evaluate `n < 0x110000`, then carry the answer to the inner join. Reached only when both preceding branches went the long way. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_B5, "ir_vc_b5: the `&&`'s untaken side -- materialize Bool.false WITHOUT evaluating the upper bound. This block is the whole operational content of the short circuit, and the reason a concrete witness for the SURROGATE range is cheaper than one for the valid range above it: this path never touches the 1,114,112 constant. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_B6, "ir_vc_b6: the INNER join, taking a bool block parameter and immediately branching to the OUTER join with it. Two join blocks in a chain; collapsing them would agree on every answer and be a different graph, which is why the branch lane compares bb6 -> bb3 explicitly. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_FUNC, "ir_vc_func: is_valid_char as EvalIR -- one parameter (the code point, by value, SSA id 0), entry block 0, seven blocks, matching the emitted control-flow graph exactly. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_MODULE, "ir_vc_module: the module for env::native_reducers_char::is_valid_char, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel, recorded at tests/fixtures/is_valid_char.trust-ir.txt and checked graph-for-graph and instruction-for-instruction, including the condbr lane and both operand orders, by tests/crystal_a1_lineage/is_valid_char.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_MACH0, "ir_vc_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds ONE parameter positionally. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_M1, "ir_vc_m1: the machine after ONE step, with the materialized 0xD800 bound at %3. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_M2, "ir_vc_m2: the machine after TWO steps, with the first comparison's result ABSTRACTED to a Bool parameter. Same device as the fifth chain and for the same reason: ir_condbr_exec dispatches with Bool.rec on the scrutinee, and this body's scrutinee is a computed Bool over a symbolic u64 residue, so the machine is stuck there and no fuel unsticks it. At b := ir_vc_c1 n this term is DEFINITIONALLY ir_step applied twice to ir_vc_mach0. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_M3, "ir_vc_m3: the machine at bb1 after the first condbr took its ELSE edge. Stated as ir_step of ir_vc_m2 at Bool.false rather than as a literal, so it cannot drift from what the machine actually does. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_M4, "ir_vc_m4: the machine after bb1's const_, with the materialized 0xDFFF bound at %5. The fifth chain needed no analogue: its second block's first instruction was already the comparison. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_M5, "ir_vc_m5: the machine at bb1's condbr with the SECOND comparison's result abstracted -- the same device again, for the short circuit. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_SPLIT2, "ir_vc_split2: the INNER case analysis. For either value of the short circuit's condition the machine runs to a return in exactly 6 steps: true goes bb4 -> bb6 -> bb3 evaluating the upper bound, false goes bb5 -> bb6 -> bb3 materializing Bool.false without evaluating it. Both minors are Eq.refl -- once the scrutinee is a literal the machine computes. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_SPLIT1, "ir_vc_split1: the OUTER case analysis, and the declaration that pays this chain's one real cost. The TRUE minor (the code point is below the surrogate block) computes to a return in 4 steps through bb2 and is Eq.refl. The FALSE minor is not, and cannot be: it lands on bb1, whose icmp puts a MATERIALIZED CONSTANT in ir_nat_ltb's recursive argument, so the kernel reduces the width-64 residue of 57343 rather than leaving it stuck. Measured 24 s, once per spec build; the linear-in-the-dividend law says why, and the module doc says why the law on record was wrong. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_TWO_STEPS, "ir_vc_two_steps: the machine after exactly TWO steps IS ir_vc_m2 at the real first condition -- the const_ and the icmp, and NOT the condbr. The kernel runs two steps and compares two configurations, both of which carry the residue unreduced, so the check is bounded by the size of two instructions' semantics. Measured 0.027 s. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_EXACT, "ir_vc_exact: the machine agrees with the reflected is_valid_char at EXACTLY 11 steps, for every code point. 11 = 9 + 2, and the proof is that split: ir_run_steps_split (a general lemma of the semantics) peels the first two steps, ir_vc_two_steps identifies the resulting configuration, and the outer case analysis finishes the remaining 9. Measured 11.7 s. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_CORRECT, "ir_vc_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE, AT WIDTH 64. *** For every code point n, every value representing it, every heap, every next-address counter and every fuel at or above 11, ir_eval on ir_vc_module returns exactly IROutcome.ret [bool (env_is_valid_char n)]. \n\nThe second chain in the program over a body that BRANCHES, and the first at a width above 32 -- which the cost law on record said was impossible and the re-measurement says is free, because the cost is in the dividend and not in the width. \n\nA0 is measured on the SHIPPED kernel: lowered, spliced, unsupported [], derived_mir.verdict agreed (8 canonical lines identical), markers_exact TRUE over TWELVE REAL MARKER LINES, the producer's own interpreter differential agreed on 5 sampled inputs, zero calls so the reachable closure is bodyful, and a codegen flip event whose A-LIN lineage equals the coverage row's. A1 is gated by tests/crystal_a1_lineage/is_valid_char.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_MACHINE_SOUND, "ir_vc_machine_sound: *** A5, THE INVERSION. *** If the MACHINE answers c, then the reflected is_valid_char IS c -- for every c. Goes through A4 rather than restating it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_VC_TRUE_IMPLIES_NOT_SURROGATE, "vc_true_implies_not_surrogate: if the reflected predicate holds then the code point is OUTSIDE the surrogate block -- one of the two range tests succeeded. By Bool.rec on both conditions, four leaves: three are Eq.refl and the fourth is the absurd case, where both tests failed, the predicate is Bool.false and the hypothesis Eq Bool Bool.false Bool.true is returned unchanged. Both disjuncts are eliminated explicitly rather than relying on Bool.or's recursion argument, so the proof does not depend on which side Bool.or computes on. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_MACHINE_SOUND_NOT_SURROGATE, "ir_vc_machine_sound_not_surrogate: *** A5 REACHING PAST THE MACHINE'S ANSWER, ONTO THE ARGUMENT. *** If the machine running the EMITTED body answers true, then n < 0xD800 or 0xDFFF < n -- a fact about the code point, extracted from a fact about the outcome. This is what the body is FOR (excluding the UTF-16 surrogate block), stated about the shipped artifact rather than about the source. One-directional and necessarily so: being outside the surrogate block does not imply validity, because the upper bound may fail. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_NEVER_FAULTS, "ir_vc_never_faults: *** NO UB, NO PANIC, NO EXHAUSTION -- on any represented code point. *** A corollary of A4. Concretely: no comparison faults not_int, neither condbr faults not_bool, no block runs off its end, both joins bind their parameters, and 11 steps always suffice. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_PATH_ASCII, "PATH WITNESS: below the surrogate block -- bb0 -> bb2 -> bb3, the arm that answers true without evaluating anything else. The kernel RUNS the machine for nine steps with the first condition supplied as Bool.true. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_PATH_ABOVE_SURROGATE_START, "PATH WITNESS: not below the surrogate block -- bb0 -> bb1, the arm that still has to decide the second range test. Its answer is the nested case analysis, unresolved, which is exactly the shape the source's `&&` has. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_PATH_UPPER, "PATH WITNESS: above the surrogate block -- bb1 -> bb4 -> bb6 -> bb3, evaluating the upper bound and carrying it through BOTH join blocks. Six steps, four of the seven blocks. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_PATH_SURROGATE, "PATH WITNESS: INSIDE the surrogate block -- bb1 -> bb5 -> bb6 -> bb3, materializing Bool.false WITHOUT evaluating the upper bound. This is the arm bb5 exists for and the executable content of `&&`: the machine answers false having never touched 0x110000. A transcription that used a Bool.and instead of a branch would not have this path at all. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_CONCRETE_ASCII, "*** CONCRETE EXECUTION WITNESS -- the first in this program over a body that BRANCHES. *** The kernel runs the emitted module on the code point 65 ('A') for eleven steps, DECIDING ITS OWN SCRUTINEES (a width-64 residue of 55296 twice), and returns Bool.true. The fifth chain has no such witness at any argument, and that is measured rather than assumed: its sentinel is u32::MAX, a 4.29e9 dividend, and the residue cost is linear in the dividend. \n\nThe cost of THIS one is also measured and is the reason there is exactly one: 24.4 s at n = 65, 36.8 s at n = 0, and 439.8 s for any argument whose path reaches ir_vc_c3 (dividend 1,114,112). The surrogate-range and above-surrogate paths are therefore covered by PATH witnesses, which run the same machine along the same edges with the branch condition supplied as a literal. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_CONCRETE_SURROGATE, "*** CONCRETE EXECUTION WITNESS: INSIDE the surrogate block, executed. *** The code point 0xD800 itself: the kernel runs the emitted module for eleven steps, decides BOTH condbr scrutinees, goes bb0 -> bb1 -> bb5 -> bb6 -> bb3 and answers false HAVING NEVER MATERIALIZED 0x110000 -- the short circuit, run at a real number rather than at a supplied Bool. \n\nWritten, kernel-checked and DECLINED on 2026-08-15 at 19.106 s, because ir_int_cmp compared through an ir_nat_ltb that peeled its FIRST operand and that operand is the code point. It measures 0.016 s here, against a same-window same-box baseline of 3.071 s. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_CONCRETE_ABOVE_SURROGATE, "*** CONCRETE EXECUTION WITNESS: ABOVE the surrogate block, upper bound HOLDS. *** 70000 is past 0xDFFF and below 0x110000, so the machine takes bb0 -> bb1 -> bb4 -> bb6 -> bb3, materializes 0x110000, evaluates the upper bound and answers true through BOTH join blocks. This is the only registered witness that reaches bb4 with a TRUE answer. \n\nDeclined on 2026-08-15 at 31.404 s; 0.017 s here against a same-window baseline of 5.045 s. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_CONCRETE_OUT_OF_RANGE, "*** CONCRETE EXECUTION WITNESS: the UPPER BOUND REJECTS. *** 0x110000 is one past the last Unicode scalar value, so the machine reaches bb4, evaluates 1114112 < 1114112 and answers false. Its dividend is this body's largest constant and it was the most expensive declaration in the chain twice over: 439.8 s to decide ir_vc_c3 at one argument before the ir_wrap folding lemma, then 210.144 s for this whole execution after it, declined both times. It measures 0.016 s here against a same-window baseline of 33.752 s. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_CORRECT_WITNESS, "ir_vc_correct_witness: A4's premises are all SATISFIABLE, discharged concretely -- the empty heap, the exact fuel bound by Le.refl, and one EncodesU64Val.mk. The code point stays universally quantified; the concrete run is ir_vc_concrete_ascii. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VC_MACHINE_SOUND_WITNESS, "ir_vc_machine_sound_witness: A5's premises are SATISFIABLE, including the observation premise, which is supplied by A4 rather than by an Eq.refl so that the witness stays cheap at a symbolic argument. Its conclusion is reflexive and the description says so rather than dressing it up. The information-bearing consequence of A5 is ir_vc_machine_sound_not_surrogate, whose conclusion is about the ARGUMENT. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

// The acceptance tests, moved to a sibling file VERBATIM on 2026-08-17 —
// module body unchanged, no assertion and no test name touched. This file
// stood at 509 lines against the 500-line convention that
// `data/paragon_ratchet.json`'s `files_over_500` enforces shrink-only, and
// the boundary is the one `eval_ir_float_fin_witnesses.rs` already used.
#[cfg(test)]
#[path = "eval_ir_valid_char_tests.rs"]
mod tests;
