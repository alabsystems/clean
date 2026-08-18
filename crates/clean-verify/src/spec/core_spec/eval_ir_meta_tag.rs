// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The TENTH complete width-one chain — the first over a PANIC ARM, and the
//! first over a CTFE flip:
//! `tc::local_context::LocalContext::push_low_local::META_TAG`.**
//!
//! ```text
//! pub fn push_low_local(&mut self, name: Name, type_: Expr, bi: impl Into<BinderData>) -> FVarId {
//!     const META_TAG: u64 = 1u64 << 63;    // <- THIS
//! ```
//!
//! ```text
//! rustcc fn @tc::local_context::LocalContext::push_low_local::META_TAG::{const-init}(functy.130) {
//! bb0:
//!     %0 = const u64 1
//!     %1 = const i32 63
//!     %2 = bitcast i32 %1 to u32
//!     %3 = const u32 64
//!     %4 = icmp ult u32 %2, %3
//!     assert %4                      ; #proof: shift_in_range
//!     %5 = sext i32 %1 to u64
//!     %6 = shl u64 %0, %5
//!     ret %6
//! }
//! ```
//!
//! ## Why THIS body — the ground, and the population
//!
//! `docs/analysis/frontier-2026-08-16.md` §2 records the finding this chain is
//! built on, and it is a correction rather than a discovery: **"panic arms 0" is
//! a statement about CODEGEN flips only.** Of the crate's 32 CTFE flips, **21
//! carry an `Inst::Assert`**; of the 178 codegen flips, **0** do. Every one of
//! the nine existing chains is over a codegen flip and none covers a panic arm,
//! so both were unclaimed and both are available in the same body.
//!
//! The 21 were re-derived here from this lane's own whole-crate dump and fall
//! into exactly **two shapes**:
//!
//! * **`no_overflow`, 9 bodies** — `mul.overflow usize` + `select` + `assert`.
//!   **Refused, and the refusal is a gate rather than a preference:** every
//!   operand is `usize`, which the CFG type lane deliberately leaves as the loud
//!   `?usize` rather than deciding the target's pointer width, and
//!   `assert_lanes` refuses an unresolved type on either side. Chaining one
//!   would mean assuming a width; the ninth chain established that refusal and
//!   this lane inherits it rather than reopening it.
//! * **`shift_in_range`, 12 bodies** — the shape above. Every width is
//!   RESOLVED (`u64`, `i32`, `u32`), so no target assumption is needed.
//!
//! Within the twelve, seven are duplicates by shift amount (`1u64 << 8` twice,
//! `<< 16` twice, `<< 32` three times, `<< 9` twice) and three are unique:
//! `META_TAG` (`1u64 << 63`), `RAT_BLOWUP_LIT_THRESHOLD` (`<< 21`) and
//! `TWO_POW_127` (`1u128 << 127`). `META_TAG` is chosen on CONTENT:
//!
//! 1. **It sits exactly one below the assert's own boundary.** The panic arm
//!    fires at shift `>= 64`; this body shifts by 63. So the failing side is
//!    ADJACENT and the boundary can be pinned from both sides by execution —
//!    `ir_mt_exact` returns a value at 63, `ir_mt_oob_traps` panics at 64 — the
//!    same two-sided device the ninth chain used for `2^32 - 1` / `2^32`.
//! 2. **It is not the same body twice.** Seven of the twelve are duplicated
//!    shift amounts; this one is unique, which was the ninth chain's own
//!    criterion for preferring the `trunc` over the two `zext`s.
//! 3. **It is load-bearing in the kernel.** `META_TAG` is the metavariable tag
//!    bit of the type checker's local context, and `push_low_local`'s own
//!    printed contract quotes it: `ENSURES: result.as_u64() < (1u64 << 63)`.
//! 4. `TWO_POW_127` is `u128` and its shift is 127; `RAT_BLOWUP_LIT_THRESHOLD`
//!    is mid-range and adjacent to nothing.
//!
//! ## WAS THE ASSERT A BUILD ITEM? NO — and the build item was somewhere else
//!
//! Measured, not hoped. `IRInst.assert : Nat -> IRInst` has been a constructor
//! since the syntax was written; the machine has had a real case for it all
//! along — `IRInst.assert c => ir_assert_exec s (ir_getd s c)` — and
//! `ir_assert_exec` is not a stub: it reads the scrutinee through `ir_as_bool`,
//! faults `type_error not_bool` on anything that is not a Bool, and hands a
//! decided Bool to `ir_assert_b`, whose `false` minor is
//! `IRConfig.halted (IROutcome.ub IRFault.assert_failed)` and whose `true` minor
//! advances. That is the panic arm, and it was already exact.
//!
//! **The semantics build item was `IRCastOp.bitcast`**, which was
//! `ir_width_fault` for every operand. The reason recorded for that refusal — a
//! cell-addressed model has no representation to reinterpret — is still right
//! for the cases it was written about and does NOT cover the only bitcast the
//! shipped kernel emits: `i32 -> u32`, two integer types at the SAME width,
//! where `IRScalar.int_ n` already IS the canonical width-`w` bit pattern.
//! `ir_bitcast_eval` decides exactly that fragment and nothing else: a width
//! mismatch, a float or a pointer on either side is still `ir_width_fault`, and
//! `IRCastOp.transmute` — the `transmute::<f64, u64>` counterexample the
//! original refusal names — is a different constructor and is untouched. Four
//! kernel-executed theorems in `eval_ir_ops` pin all four of those statements.
//!
//! **The gate build item was the ASSERT LANE**, and it is the ninth chain's
//! failure mode exactly: `Inst::Assert` binds no result, carries no type and has
//! no branch target, so a transcription that DELETED the assert, or asserted a
//! different SSA id, differed from the artifact in nothing the CFG gate read.
//! Two more holes came with it and both are in `emitted_cfg.rs`: the three
//! constant VALUE lanes were one-per-BLOCK (this body materializes three
//! constants in one block, and the `no_overflow` shape four), and the program-
//! order lane's result slot was a single `u32` read with `unwrap_or(u32::MAX)`,
//! so a two-result node scored `MAX` on both sides whatever it bound.
//!
//! ## What LINK 2b means here, and it is WEAKER than the codegen form
//!
//! Stated plainly rather than claimed as parity. For the nine existing chains
//! link 2b is a CODEGEN flip: the derived MIR is what `inner_optimized_mir`
//! hands to codegen, so the machine instructions in the shipped artifact are
//! compiled from this trust-ir. For a CTFE flip the seam is `mir_for_ctfe`
//! (`trust_ir_flip.rs:194`), the consumer is the const-eval INTERPRETER, and
//! what the artifact receives is the interpreter's OUTPUT — a value. So:
//!
//! * **What link 2b still binds, and it is real.** The registry writer is the
//!   same (`record_green`, the sole writer, on `DerivedAgreed`), the gate is the
//!   same (`markers_exact` at `flip_registry.rs:641`), the event carries the
//!   same A-LIN lineage digest, and it equals this body's coverage-row digest.
//!   The constant every use site is given was computed by const-evaluating MIR
//!   re-derived from THIS module.
//! * **What it does NOT bind.** No machine code corresponds to these nine
//!   instructions. The shift, the comparison and the assert all ran at compile
//!   time; the artifact carries `1u64 << 63` as a baked value. A theorem about
//!   this module is a theorem about a computation that PRODUCED part of the
//!   artifact, not about one the artifact performs.
//! * **One thing it binds MORE tightly, and it is the panic arm's doing.** A
//!   flip on either seam runs `verify_assert_parity` (`flip.rs:1767`), which
//!   walks both bodies in canonical DFS preorder and requires the assert
//!   sequences to match in count, kind class and polarity. For all 178 codegen
//!   flips that check is VACUOUS — `asserts=0` on every one. Here it is
//!   `asserts=1`, so the event records one verified `Overflow`-class assert. The
//!   chain therefore rests on strictly more producer-side checking on that axis
//!   and strictly less artifact-shaped binding on the other, and neither
//!   sentence is a substitute for the other.
//!
//! ## The refinement theorem says what happens on the FAILING side
//!
//! Three statements, none of which is the other:
//!
//! * `ir_mt_assert_dichotomy` — for EVERY machine state and BOTH truth values:
//!   `true` advances, `false` is `IROutcome.ub IRFault.assert_failed`. Proved by
//!   `Bool.rec`, so neither arm is assumed.
//! * `ir_mt_oob_traps` / `ir_mt_neg_traps` — the failing arm EXECUTED on this
//!   body's own emitted shape, with one constant changed. At shift 64 the
//!   kernel runs nine steps and gets the panic; at shift `2^31` (a negative
//!   `i32`) it gets the panic too, because the `bitcast` ZERO-extends and the
//!   range check sees `2147483648 >= 64`.
//! * `ir_mt_oob_never_returns_at_any_fuel` — and NOTHING after the assert runs.
//!   For every `g`, at fuel `g + 6`, the outcome is still the panic: the `sext`,
//!   the `shl` and the `ret` are never reached.
//!
//! `ir_mt_cond_holds` is the other half: the kernel DECIDES this body's own
//! panic condition, by computation, and it is `Bool.true`. That is why the
//! artifact exists — a `false` there is a const-eval hard error and there is no
//! artifact to be about.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! `ir_mt_value` is `ir_wrap ir_d64 (ir_nat_mul ir_d1 (ir_nat_pow2 ir_mt_amt))`.
//! That IS what Rust's `1u64 << 63` computes, and this module does not prove it
//! — the same shape of gap `super::eval_ir_valid_char` states for
//! `env_is_valid_char` and `super::eval_ir_trunc` for `ir_wrap ir_d32`. The
//! value is deliberately left as an UNREDUCED application on both sides:
//! `ir_nat_mul` recurses on its SECOND argument, so normalizing
//! `ir_nat_mul 1 (ir_nat_pow2 63)` would cost `2^63` `Nat.rec` unfoldings. The
//! kernel decides every guard in the body and never computes the answer, which
//! is exactly the discipline `super::eval_ir_trunc` records for its residue.
//!
//! No general theorem over the shift amount is proved. The scrutinee is
//! symbolic in that generalization and `ir_nat_ltb` is stuck on it — the fifth
//! chain's recorded limit — and this body has TWO guards, the source-level
//! assert and the machine's own `shl` range check, so a per-`k` statement would
//! be a three-way split. What is proved generally is the assert dichotomy; what
//! is executed is the boundary, from both sides.
//!
//! ## THE COST, and why A5 had to be RESTATED to get it
//!
//! **The first version of this stage did not build.** `Specification::new()` ran
//! **2,572.7 s and then FAILED**, on A5, with
//!
//! ```text
//! expected Eq Nat env_push_low_local_meta_tag k
//! got      Eq Nat (ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ K))))
//!                 (ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ k))))
//! ```
//!
//! The mechanism is exact, and it is NOT that `ir_outcome_nat` fails to reduce.
//! That application weak-head-normalizes to `K` in a few iota steps — and **whnf
//! does not STOP at `K`**. `K` is a definition, so reduction continues, and
//! continuing means `ir_wrap ir_d64 (ir_nat_mul ir_d1 (ir_nat_pow2 63))`, whose
//! `ir_nat_mul` recurses on its SECOND argument. Every chain from the second
//! onward makes exactly this move inside its own A5 and every one of them gets
//! away with it, because its answer carries a FREE VARIABLE and whnf gets stuck
//! at once. This is the first chain whose answer is CLOSED.
//!
//! **A5 is therefore an INSTANCE of a lemma proved at two variables** —
//! `ir_ret_int_nat` (the read-back) and `ir_ret_int_inj` (the inversion) — so
//! the checker SUBSTITUTES where it used to REDUCE. The statement of
//! `ir_mt_machine_sound` is unchanged, character for character in its type; only
//! the proof term moved. Measured on one `CoreSpecBundle::EvalIr`-shaped build at
//! the same shape: the composed-at-the-constant proof is **232.62 s**, the
//! generalized lemma plus its instance is **0.04 s**, and the original
//! `Eq.cong`-at-the-constant does not finish (killed at 600 s in the probe; in
//! the full spec it burned ~2,300 s and then reported the mismatch above).
//!
//! **Repairing A5 exposed a SECOND declaration that had never been reached**,
//! because the build died at A5 first. `ir_mt_icmp_width_is_semantic` was
//! stated at width 8 on the operand `2147483648`, and `ir_int_cmp` canonicalizes
//! through `ir_wrap`, whose `ir_div_go` recursion is on the QUOTIENT: `2^31 / 2^8`
//! is 8,388,608 loop steps. It does not merely cost — **it does not elaborate**
//! (166.55 s in a full `Specification::new()`, then the elaborator gives up with
//! the left-hand side entirely unreduced). It is now stated at width 16, where
//! the quotient is 32,768, the contrast is identical (`2^31` is `0` modulo `2^16`
//! exactly as modulo `2^8`) and the measured cost is 10.06 s — and it is paired
//! with `ir_mt_icmp_at_the_bodys_width_is_false`, which executes the OTHER side
//! of the same contrast at the width the shipped body declares.
//!
//! **What remains is `ir_mt_exact`, and it is a WALL with a measurement rather
//! than an unexamined cost.** Four probes, one `CoreSpecBundle::EvalIr`-shaped
//! build each:
//!
//! * **The nine machine steps are FREE.** At fuel 6, 7 and 8 — through the
//!   assert, the `sext` and the `shl` — the run costs 0.04 / 0.05 / 0.06 s, at
//!   every shift amount tried. The whole cost is the LAST comparison, the one
//!   that matches the returned scalar against the reflected constant.
//! * **It is the shift amount that costs**: the same nine-node body at shift
//!   3 / 16 / 63 costs 0.07 / 8.94 / 316.95 s.
//! * **No spelling of the right-hand side can help, and this is now measured
//!   rather than inferred.** Two `ir_wrap` applications that are BYTE-IDENTICAL
//!   compare in 0.00 s; perturbing ONE argument into an equal-but-differently-
//!   spelled one costs 368.50 s, and doing it to another argument costs
//!   364.63 s. There is no congruence step and no lazy-delta short-circuit:
//!   comparing the term against a CONSTANT whose body IS that term still costs
//!   317.33 s. That closes the question the ninth-chain-style "three spellings,
//!   all ~360 s" observation left open.
//! * **The build item is therefore in the SUBSTRATE, and it is named.**
//!   `ir_shl_bits` produces `ir_wrap w (ir_nat_mul x (ir_nat_pow2 amount))`, and
//!   `ir_nat_mul` recurses on its second argument. `super::eval_ir_bits` already
//!   registers `ir_nat_shl` — `m * 2^k` as `k` STRICT doublings, linear in `k`
//!   where this is linear in `2^k` — but routing `ir_shl_bits` through it needs
//!   the GENERAL equation `ir_nat_shl m k = ir_nat_mul m (ir_nat_pow2 k)`, and
//!   what exists today is one kernel-executed witness at `(3, 10)`
//!   (`ir_nat_shl_mul_w`). That equation is a build item for its own lane; it is
//!   not a reason to retarget this proof, and this chain does not claim it.
//!
//! **A THIRD declaration was restated, and it was the expensive one nobody had
//! seen.** `ir_mt_w_heap_is_unread` is registered after the icmp, so no run had
//! ever reached it either; as a bare `Eq.refl` it cost **326.93 s** — the second
//! most expensive declaration in the WHOLE specification, within 2 s of
//! `ir_mt_exact` — because the checker matched the answer against the nine-step
//! run twice more. It is now A4 at the two heaps, and A4's own proof already IS
//! that run at a symbolic heap.
//!
//! **What the chain costs, end to end and with its sign.** Four replicates per
//! side — the four heavy gates launched TOGETHER at matched 4-way concurrency —
//! take one full `Specification::new()` from **1,650.4 s to 2,047.2 s: +396.9 s,
//! +24.0%**, every replicate agreeing in sign, with all eight processes GREEN.
//! The complete build with A5 repaired but the other two declarations untouched
//! is **1,518.7 → 2,198.0 s (+679.3 s)** at 2-way concurrency, so the two
//! restatements are most of the difference and `ir_mt_exact` is nearly all of
//! what is left. That remaining cost is not dressed down, and it is compared
//! against a GREEN tree rather than against the 2,572.7 s failure, because a
//! build that ends in a type error is not a baseline. `docs/CRYSTAL_STATUS.md`
//! §3i carries the table;
//! `test_the_measured_cost_of_the_restatement_has_a_negative_sign` below pins
//! every number as data.
//!
//! The link between the proved module and the emitted one is STRUCTURAL —
//! `tests/crystal_a1_lineage/meta_tag_shl.rs`. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// NOTHING already registered is re-declared. `ir_vc_tu64` (sixth chain),
// `ir_br_tu32` (fifth), `ir_d32` / `ir_d64`, `ir_nd` / `ir_nd1` / `ir_nl0` /
// `ir_nl1` / `ir_vl0` / `ir_vl1` / `ir_bd3` / `ir_bd6` / `ir_blk` / `ir_blk0` /
// `ir_mem0` (first chain), `ir_outcome_nat` (second), `ir_outcome_is_ret`
// (add_eval_ir_correct), `ir_run_le_ret` (add_eval_ir_fuel) and
// `ir_run_steps_split` / `ir_run_halted` (add_eval_ir_steps) all exist and this
// stage runs after every one of them. The eighth chain's one real error was
// re-declaring `ir_nl3`, which elaborated cleanly in every fast gate and failed
// only in the full `Specification::new()`.

// ── the one new type alias and the one new list builder ───────────────
const SRC_IR_MT_TI32: &str = "def ir_mt_ti32 : IRTy := IRTy.int_ ir_d32";
const SRC_IR_MT_BD9: &str = "def ir_mt_bd9 (a : IRNode) (b : IRNode) (c : IRNode) (d : IRNode) (e : IRNode) (f : IRNode) (g : IRNode) (h : IRNode) (i : IRNode) : IRList IRNode := IRList.cons IRNode a (IRList.cons IRNode b (IRList.cons IRNode c (ir_bd6 d e f g h i)))";

// ── the reflected constant and its two ingredients ────────────────────
const SRC_IR_MT_AMT: &str = "def ir_mt_amt : Nat := 63";
#[rustfmt::skip]
const SRC_ENV_META_TAG: &str = "def env_push_low_local_meta_tag : Nat := ir_wrap ir_d64 (ir_nat_mul ir_d1 (ir_nat_pow2 ir_mt_amt))";
const SRC_IR_MT_B0: &str = "def ir_mt_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_mt_bd9 (ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 1)) ir_d0) (ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 63)) ir_d1) (ir_nd1 (IRInst.cast IRCastOp.bitcast ir_mt_ti32 ir_br_tu32 ir_d1) ir_d2) (ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 64)) ir_d3) (ir_nd1 (IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3) ir_d4) (ir_nd (IRInst.assert ir_d4)) (ir_nd1 (IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d1) ir_d5) (ir_nd1 (IRInst.binop IRBinOp.shl ir_vc_tu64 ir_d0 ir_d5) ir_d6) (ir_nd (IRInst.ret (ir_nl1 ir_d6))))";
#[rustfmt::skip]
const SRC_IR_MT_FUNC: &str = "def ir_mt_func : IRFunc := IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk ir_mt_b0 ir_blk0)";
const SRC_IR_MT_MODULE: &str = "def ir_mt_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_mt_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

// ── the machine, and the emitted body's own panic condition ───────────
const SRC_IR_MT_MACH0: &str = "def ir_mt_mach0 (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params ir_nl0 ir_vl0 (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";
const SRC_IR_MT_INIT: &str = "def ir_mt_init_is_mach0 (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_init ir_mt_module ir_d0 ir_vl0 mem na) (IRConfig.running (ir_mt_mach0 mem na)) := Eq.refl IRConfig (IRConfig.running (ir_mt_mach0 mem na))";
#[rustfmt::skip]
const SRC_IR_MT_COND: &str = "def ir_mt_cond : Bool := ir_nat_ltb (ir_wrap ir_d32 (ir_wrap ir_d32 63)) (ir_wrap ir_d32 64)";
#[rustfmt::skip]
const SRC_IR_MT_COND_HOLDS: &str = "def ir_mt_cond_holds : Eq Bool ir_mt_cond Bool.true := Eq.refl Bool Bool.true";

// ── the exact run, A4, A5 ─────────────────────────────────────────────
const SRC_IR_MT_EXACT: &str = "def ir_mt_exact (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d9 ir_mt_module (IRConfig.running (ir_mt_mach0 mem na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ env_push_low_local_meta_tag))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ env_push_low_local_meta_tag)))";
const SRC_IR_MT_CORRECT: &str = "def ir_mt_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (hle : Le ir_d9 fuel) : Eq IROutcome (ir_eval fuel ir_mt_module ir_d0 ir_vl0 mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ env_push_low_local_meta_tag))) := ir_run_le_ret ir_mt_module ir_d9 fuel hle (IRConfig.running (ir_mt_mach0 mem na)) (ir_vl1 (IRScalar.int_ env_push_low_local_meta_tag)) (ir_mt_exact mem na)";
// ── THE READ-BACK, GENERALIZED — see the module doc's cost section ────
//
// Both are stated over a VARIABLE and instantiated afterwards. That is not a
// stylistic choice: `ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ n)))`
// weak-head-normalizes to `n`, and whnf does not STOP at `n` when `n` is a
// closed definition — it keeps unfolding, and unfolding this chain's constant
// means `ir_nat_mul ir_d1 (ir_nat_pow2 63)`, whose recursion is on its SECOND
// argument. At a free variable whnf gets stuck immediately and the same proof
// is free.
const SRC_IR_RET_INT_NAT: &str = "def ir_ret_int_nat (n : Nat) : Eq Nat (ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ n)))) n := Eq.refl Nat n";
const SRC_IR_RET_INT_INJ: &str = "def ir_ret_int_inj (a : Nat) (b : Nat) (h : Eq IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ a))) (IROutcome.ret (ir_vl1 (IRScalar.int_ b)))) : Eq Nat a b := Eq.trans Nat a (ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ b)))) b (Eq.trans Nat a (ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ a)))) (ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ b)))) (Eq.symm Nat (ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ a)))) a (ir_ret_int_nat a)) (Eq.cong IROutcome Nat ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ a))) (IROutcome.ret (ir_vl1 (IRScalar.int_ b))) h)) (ir_ret_int_nat b)";
const SRC_IR_MT_MACHINE_SOUND: &str = "def ir_mt_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (k : Nat) (hle : Le ir_d9 fuel) (hret : Eq IROutcome (ir_eval fuel ir_mt_module ir_d0 ir_vl0 mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ k)))) : Eq Nat env_push_low_local_meta_tag k := ir_ret_int_inj env_push_low_local_meta_tag k (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ env_push_low_local_meta_tag))) (ir_eval fuel ir_mt_module ir_d0 ir_vl0 mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ k))) (Eq.symm IROutcome (ir_eval fuel ir_mt_module ir_d0 ir_vl0 mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ env_push_low_local_meta_tag))) (ir_mt_correct mem fuel na hle)) hret)";
const SRC_IR_MT_NEVER_FAULTS: &str = "def ir_mt_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (hle : Le ir_d9 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_mt_module ir_d0 ir_vl0 mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_mt_module ir_d0 ir_vl0 mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ env_push_low_local_meta_tag))) (ir_mt_correct mem fuel na hle)";

// ── THE FAILING SIDE OF THE ASSERT, three ways ────────────────────────
const SRC_IR_MT_DICHOTOMY: &str = "def ir_mt_assert_dichotomy (s : IRMachine) (b : Bool) : Eq IRConfig (ir_assert_exec s (IRScalar.bool_ b)) (Bool.rec (fun (_ : Bool) => IRConfig) (IRConfig.halted (IROutcome.ub IRFault.assert_failed)) (ir_advance s) b) := Bool.rec (fun (b0 : Bool) => Eq IRConfig (ir_assert_exec s (IRScalar.bool_ b0)) (Bool.rec (fun (_ : Bool) => IRConfig) (IRConfig.halted (IROutcome.ub IRFault.assert_failed)) (ir_advance s) b0)) (Eq.refl IRConfig (IRConfig.halted (IROutcome.ub IRFault.assert_failed))) (Eq.refl IRConfig (ir_advance s)) b";
const SRC_IR_MT_NOT_BOOL: &str = "def ir_mt_assert_non_bool_is_a_type_error (s : IRMachine) (n : Nat) : Eq IRConfig (ir_assert_exec s (IRScalar.int_ n)) (IRConfig.halted (IROutcome.type_error IRFault.not_bool)) := Eq.refl IRConfig (IRConfig.halted (IROutcome.type_error IRFault.not_bool))";

// The SAME emitted shape with ONE constant changed: shift 64, the first amount
// the source-level check refuses.
const SRC_IR_MT_OOB_B0: &str = "def ir_mt_oob_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_mt_bd9 (ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 1)) ir_d0) (ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 64)) ir_d1) (ir_nd1 (IRInst.cast IRCastOp.bitcast ir_mt_ti32 ir_br_tu32 ir_d1) ir_d2) (ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 64)) ir_d3) (ir_nd1 (IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3) ir_d4) (ir_nd (IRInst.assert ir_d4)) (ir_nd1 (IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d1) ir_d5) (ir_nd1 (IRInst.binop IRBinOp.shl ir_vc_tu64 ir_d0 ir_d5) ir_d6) (ir_nd (IRInst.ret (ir_nl1 ir_d6))))";
#[rustfmt::skip]
const SRC_IR_MT_OOB_FUNC: &str = "def ir_mt_oob_func : IRFunc := IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk ir_mt_oob_b0 ir_blk0)";
const SRC_IR_MT_OOB_MODULE: &str = "def ir_mt_oob_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_mt_oob_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";
const SRC_IR_MT_OOB_MACH0: &str = "def ir_mt_oob_mach0 (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params ir_nl0 ir_vl0 (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";
const SRC_IR_MT_OOB_TRAPS: &str = "def ir_mt_oob_traps (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d9 ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na))) (IROutcome.ub IRFault.assert_failed) := Eq.refl IROutcome (IROutcome.ub IRFault.assert_failed)";
const SRC_IR_MT_OOB_SIX: &str = "def ir_mt_oob_halts_at_six (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_steps ir_d6 ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na))) (IRConfig.halted (IROutcome.ub IRFault.assert_failed)) := Eq.refl IRConfig (IRConfig.halted (IROutcome.ub IRFault.assert_failed))";
const SRC_IR_MT_OOB_ANY_FUEL: &str = "def ir_mt_oob_never_returns_at_any_fuel (mem : IRList IRMemSlot) (na : Nat) (g : Nat) : Eq IROutcome (ir_run (Nat.add g ir_d6) ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na))) (IROutcome.ub IRFault.assert_failed) := Eq.trans IROutcome (ir_run (Nat.add g ir_d6) ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na))) (ir_run g ir_mt_oob_module (ir_steps ir_d6 ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na)))) (IROutcome.ub IRFault.assert_failed) (ir_run_steps_split ir_mt_oob_module g ir_d6 (IRConfig.running (ir_mt_oob_mach0 mem na))) (Eq.trans IROutcome (ir_run g ir_mt_oob_module (ir_steps ir_d6 ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na)))) (ir_run g ir_mt_oob_module (IRConfig.halted (IROutcome.ub IRFault.assert_failed))) (IROutcome.ub IRFault.assert_failed) (Eq.cong IRConfig IROutcome (fun (c : IRConfig) => ir_run g ir_mt_oob_module c) (ir_steps ir_d6 ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na))) (IRConfig.halted (IROutcome.ub IRFault.assert_failed)) (ir_mt_oob_halts_at_six mem na)) (ir_run_halted ir_mt_oob_module (IROutcome.ub IRFault.assert_failed) g))";
const SRC_IR_MT_OOB_NOT_RET: &str = "def ir_mt_oob_is_not_a_return (mem : IRList IRMemSlot) (na : Nat) (g : Nat) : Eq Bool (ir_outcome_is_ret (ir_run (Nat.add g ir_d6) ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na)))) Bool.false := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_run (Nat.add g ir_d6) ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 mem na))) (IROutcome.ub IRFault.assert_failed) (ir_mt_oob_never_returns_at_any_fuel mem na g)";

// The same shape at a NEGATIVE i32 shift amount — the case that makes the
// bitcast semantic rather than decorative.
const SRC_IR_MT_NEG_B0: &str = "def ir_mt_neg_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_mt_bd9 (ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 1)) ir_d0) (ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 2147483648)) ir_d1) (ir_nd1 (IRInst.cast IRCastOp.bitcast ir_mt_ti32 ir_br_tu32 ir_d1) ir_d2) (ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 64)) ir_d3) (ir_nd1 (IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3) ir_d4) (ir_nd (IRInst.assert ir_d4)) (ir_nd1 (IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d1) ir_d5) (ir_nd1 (IRInst.binop IRBinOp.shl ir_vc_tu64 ir_d0 ir_d5) ir_d6) (ir_nd (IRInst.ret (ir_nl1 ir_d6))))";
#[rustfmt::skip]
const SRC_IR_MT_NEG_FUNC: &str = "def ir_mt_neg_func : IRFunc := IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk ir_mt_neg_b0 ir_blk0)";
const SRC_IR_MT_NEG_MODULE: &str = "def ir_mt_neg_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_mt_neg_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";
const SRC_IR_MT_NEG_TRAPS: &str = "def ir_mt_neg_traps (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d9 ir_mt_neg_module (IRConfig.running (ir_mt_mach0 mem na))) (IROutcome.ub IRFault.assert_failed) := Eq.refl IROutcome (IROutcome.ub IRFault.assert_failed)";

// ── the three operators, stated as theorems rather than as prose ──────
const SRC_IR_MT_BITCAST: &str = "def ir_mt_bitcast_is_the_identity (n : Nat) : Eq IRStepResult (ir_cast_eval IRCastOp.bitcast ir_mt_ti32 ir_br_tu32 (IRScalar.int_ n)) (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d32 n))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d32 n)))";
const SRC_IR_MT_BITCAST_ZERO_EXT: &str = "def ir_mt_bitcast_zero_extends_the_sign_bit : Eq IRStepResult (ir_cast_eval IRCastOp.bitcast ir_mt_ti32 ir_br_tu32 (IRScalar.int_ 2147483648)) (IRStepResult.value (IRScalar.int_ 2147483648)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 2147483648))";
const SRC_IR_MT_SEXT_SIGN_EXTENDS: &str = "def ir_mt_sext_sign_extends_the_same_pattern : Eq IRStepResult (ir_cast_eval IRCastOp.sext ir_mt_ti32 ir_vc_tu64 (IRScalar.int_ 2147483648)) (IRStepResult.value (IRScalar.int_ 18446744071562067968)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 18446744071562067968))";
const SRC_IR_MT_SHL_OOB: &str = "def ir_mt_shl_out_of_range_is_ub (x : Nat) : Eq IRStepResult (ir_binop_eval IRBinOp.shl ir_vc_tu64 (IRScalar.int_ x) (IRScalar.int_ 64)) (IRStepResult.fault (IROutcome.ub IRFault.shift_oob)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.ub IRFault.shift_oob))";
// THE WIDTH IS SEMANTIC, as a PAIR of executed theorems at the SAME two
// operands. The narrow one is stated at width 16 rather than at width 8, and
// that is a COST fact with a measurement behind it — see the description.
const SRC_IR_MT_ICMP_WIDTH: &str = "def ir_mt_icmp_width_is_semantic : Eq IRStepResult (ir_icmp_eval IRICmpOp.ult (IRTy.uint_ ir_d16) (IRScalar.int_ 2147483648) (IRScalar.int_ 64)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";
const SRC_IR_MT_ICMP_AT_THE_BODYS_WIDTH: &str = "def ir_mt_icmp_at_the_bodys_width_is_false : Eq IRStepResult (ir_icmp_eval IRICmpOp.ult ir_br_tu32 (IRScalar.int_ 2147483648) (IRScalar.int_ 64)) (IRStepResult.value (IRScalar.bool_ Bool.false)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.false))";

// ── kernel-EXECUTED witnesses on the shipped module ───────────────────
const SRC_W_RUNS: &str = "def ir_mt_w_runs : Eq IROutcome (ir_eval ir_d9 ir_mt_module ir_d0 ir_vl0 ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ env_push_low_local_meta_tag))) := ir_mt_correct ir_mem0 ir_d9 ir_d0 (Le.refl ir_d9)";
const SRC_W_HEAP_UNREAD: &str = "def ir_mt_w_heap_is_unread (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_eval ir_d9 ir_mt_module ir_d0 ir_vl0 ir_mem0 ir_d0) (ir_eval ir_d9 ir_mt_module ir_d0 ir_vl0 mem na) := Eq.trans IROutcome (ir_eval ir_d9 ir_mt_module ir_d0 ir_vl0 ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ env_push_low_local_meta_tag))) (ir_eval ir_d9 ir_mt_module ir_d0 ir_vl0 mem na) (ir_mt_correct ir_mem0 ir_d9 ir_d0 (Le.refl ir_d9)) (Eq.symm IROutcome (ir_eval ir_d9 ir_mt_module ir_d0 ir_vl0 mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ env_push_low_local_meta_tag))) (ir_mt_correct mem ir_d9 na (Le.refl ir_d9)))";
const SRC_W_SOUND: &str = "def ir_mt_machine_sound_witness : Eq Nat env_push_low_local_meta_tag env_push_low_local_meta_tag := ir_mt_machine_sound ir_mem0 ir_d9 ir_d0 env_push_low_local_meta_tag (Le.refl ir_d9) ir_mt_w_runs";
const SRC_W_BOUNDARY: &str = "def ir_mt_w_boundary_is_pinned_from_both_sides : Eq Bool (ir_outcome_is_ret (ir_run ir_d9 ir_mt_oob_module (IRConfig.running (ir_mt_oob_mach0 ir_mem0 ir_d0)))) Bool.false := Eq.refl Bool Bool.false";

impl Specification {
    /// Register the TENTH complete width-one chain — the first over a PANIC ARM
    /// and the first over a CTFE flip:
    /// `tc::local_context::LocalContext::push_low_local::META_TAG`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    #[allow(clippy::too_many_lines)]
    pub(super) fn add_eval_ir_meta_tag(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_IR_MT_TI32, "ir_mt_ti32: i32, the SIGNED 32-bit type the shift amount is materialized at. A new alias rather than a reuse because every earlier chain's integer types are unsigned, and the signedness is load-bearing twice in this body: the bitcast ZERO-extends the pattern for the range check while the sext SIGN-extends the same pattern for the shift, which is why a negative amount is refused by the assert rather than shifting by a huge number. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_BD9, "ir_mt_bd9: a nine-node block body, built on the existing ir_bd6. The longest block any chain has transcribed; the previous maximum was six. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_AMT, "ir_mt_amt: the shift amount, 63 -- one below the width, so the answer is the SIGN BIT of a u64 and the body sits exactly one step from the panic arm's boundary. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ENV_META_TAG, "env_push_low_local_meta_tag: the reflected `const META_TAG: u64 = 1u64 << 63` of tc::local_context::LocalContext::push_low_local (local_context.rs:157), whose own printed contract quotes it -- ENSURES: result.as_u64() < (1u64 << 63). It is ir_wrap ir_d64 (ir_nat_mul ir_d1 (ir_nat_pow2 63)) and NOT a proof that Rust's `1u64 << 63` is that expression; that gap is the same shape as env_is_valid_char's and env_get_char_val_closure's. Deliberately left UNREDUCED: ir_nat_mul recurses on its SECOND argument, so normalizing it would cost 2^63 Nat.rec unfoldings, and nothing in this chain needs the digits. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_B0, "ir_mt_b0: THE WHOLE BODY, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/meta_tag_shl.trust-ir.txt). NINE nodes in one block: two constants, a bitcast, a third constant, an icmp, THE ASSERT, a sext, a shl and a ret. The assert is the point -- it is the first panic arm any chain has covered, it binds no result and carries no type or target, and before the assert lane existed a transcription that simply DELETED it agreed with the artifact on every lane the CFG gate had. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_FUNC, "ir_mt_func: the const-initializer as EvalIR -- ZERO parameters, entry block 0, one block. Every earlier chain's function takes at least one argument; a const item takes none, which is what makes A4 quantify over nothing but the heap and the fuel. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_MODULE, "ir_mt_module: the module for tc::local_context::LocalContext::push_low_local::META_TAG, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel, recorded at tests/fixtures/meta_tag_shl.trust-ir.txt and checked graph-for-graph and instruction-for-instruction, including the new assert lane, by tests/crystal_a1_lineage/meta_tag_shl.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_MACH0, "ir_mt_mach0: the machine ir_init produces for this module. No parameters, so ir_bind_params over the empty lists is the empty locals list; the module declares no globals, so ir_mem_concat is the identity on the caller heap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_INIT, "ir_mt_init_is_mach0: the hand-written initial machine IS the one ir_init builds, for every heap and next-address counter, by computation. Registered rather than assumed so that a change to ir_init stops this reducing instead of silently making A4 a theorem about a different starting state. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_COND, "ir_mt_cond: THE EMITTED BODY'S OWN PANIC CONDITION, spelled exactly as the machine computes it -- ir_int_cmp canonicalizes both operands at the icmp's declared width 32, and the left operand is the bitcast's own width-32 canonicalization of the constant. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_COND_HOLDS, "ir_mt_cond_holds: *** THE KERNEL DECIDES THAT THE PANIC ARM DOES NOT FIRE. *** By computation, not by assumption: 63 < 64. This is why an artifact exists at all -- a false here is a const-eval hard error, the compile fails, and there is no constant to prove anything about. It is also the premise ir_mt_exact discharges without stating, and it is registered separately so that a transcription which changed the shift amount stops reducing here. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_EXACT, "ir_mt_exact: the machine agrees with the reflected constant at EXACTLY 9 steps, for every heap and every next-address counter. One Eq.refl, and what it costs is worth stating: the kernel DECIDES every guard in the body -- the bitcast's width equality, the icmp at width 32, the assert, the sext's sign bit and the shl's range check -- and never computes the answer, because ir_nat_mul recurses on its second argument and 2^63 unfoldings is not a proof strategy. The residue stays an unreduced application on both sides, exactly as the ninth chain records for ir_wrap ir_d32. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_CORRECT, "ir_mt_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE, FOR A BODY WITH A PANIC ARM. *** For every heap, every next-address counter and every fuel at or above 9, ir_eval on ir_mt_module returns exactly IROutcome.ret [int_ env_push_low_local_meta_tag]. \n\nA0 is measured on the SHIPPED kernel: lowered, spliced, unsupported [], derived_mir.verdict agreed (4 canonical lines identical), markers_exact TRUE, the producer's own interpreter differential agreed on 1 sampled input, zero calls so the reachable closure is bodyful, and a CTFE flip event whose A-LIN lineage equals the coverage row's and whose asserts=1 records ONE verified assert -- the parity check that is vacuous on all 178 codegen flips. A1 is gated by tests/crystal_a1_lineage/meta_tag_shl.rs. \n\nRead the module doc on what link 2b means for a CTFE flip: it binds the VALUE the artifact carries, not an instruction sequence the artifact executes, and that is weaker than the codegen form on that axis. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_RET_INT_NAT, "ir_ret_int_nat: the READ-BACK, stated over a VARIABLE. ir_outcome_nat of a one-value integer return IS that integer, for every Nat. Every chain from the second onward has made this move INSIDE its own A5, where it costs nothing because the value carries a free variable; at a CLOSED value it is not free at all, because whnf does not stop at a constant -- it unfolds it, and unfolding this chain's constant means ir_nat_mul ir_d1 (ir_nat_pow2 63), whose recursion is on its SECOND argument. Stated once here at a variable, where whnf gets stuck on the fvar and the proof is one Eq.refl. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_RET_INT_INJ, "ir_ret_int_inj: THE INVERSION, GENERALIZED. If two one-value integer returns are equal outcomes then the integers are equal -- for every pair of Nats, neither of them this chain's constant. This is the whole of A5's reasoning, discharged where both endpoints are free variables: ir_ret_int_nat on each side and one Eq.cong between them. A5 is then an INSTANCE of it, so the checker substitutes rather than reduces and never asks for a weak-head normal form of the reflected constant. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_MACHINE_SOUND, "ir_mt_machine_sound: *** A5, THE INVERSION. *** If the MACHINE running the emitted body answers k, then the reflected constant IS k -- for every k, not for a chosen one. Goes through A4 rather than restating it, and reads the answer back through ir_ret_int_inj -- an INSTANCE of a lemma proved at two free variables -- rather than by unfolding ir_outcome_nat at the constant. That is a cost restatement, not a weakening: the statement is the same one the other nine chains prove, and the proof no longer requires the kernel to weak-head-normalize ir_wrap ir_d64 (ir_nat_mul ir_d1 (ir_nat_pow2 63)). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_NEVER_FAULTS, "ir_mt_never_faults: *** NO UB, NO TYPE ERROR, NO STUCK STATE, NO EXHAUSTION -- and in particular THE PANIC ARM NEVER FIRES. *** A corollary of A4. Concretely: the bitcast is not a width fault, the icmp is not a type error, the ASSERT does not fail, the sext is in range, the shl is not shift_oob, the ret does not run off the end of the block, and 9 steps always suffice. On a body whose whole reason to exist is a compile-time overflow check, this is the statement that the check passes. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_DICHOTOMY, "ir_mt_assert_dichotomy: *** WHAT HAPPENS ON THE FAILING SIDE OF THE ASSERT, IN FULL GENERALITY. *** For EVERY machine state and BOTH truth values: a true scrutinee advances past the instruction, and a FALSE one halts the machine at IROutcome.ub IRFault.assert_failed. Proved by Bool.rec, so neither arm is assumed and neither is the one this body takes. This is the theorem the brief asks for: a refinement statement about a panic arm that says what the panic does, not only that it is avoided. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_NOT_BOOL, "ir_mt_assert_non_bool_is_a_type_error: FAIL-CLOSED. An INTEGER scrutinee is IROutcome.type_error IRFault.not_bool -- not `nonzero is true`, not a silent pass. ir_as_bool declines IRScalar.int_, so an assert cannot be satisfied by an integer that happens to be nonzero, and a transcription that fed it one is a fault rather than a proof. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_OOB_B0, "ir_mt_oob_b0: THE SAME EMITTED SHAPE WITH ONE CONSTANT CHANGED -- shift 64 instead of 63, the first amount the source-level check refuses. It is NOT a transcription of any shipped body and the CFG gate is not run against it; it is the instrument that makes the failing arm EXECUTABLE on this body's own nine-node shape. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_IR_MT_OOB_FUNC,
            "ir_mt_oob_func: the counterfactual's function. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_IR_MT_OOB_MODULE,
            "ir_mt_oob_module: the counterfactual's module. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_IR_MT_OOB_MACH0, "ir_mt_oob_mach0: the counterfactual's initial machine, identical in shape to the shipped body's. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_OOB_TRAPS, "ir_mt_oob_traps: *** THE PANIC ARM, EXECUTED. *** Nine steps of the emitted shape at shift amount 64, and the kernel returns IROutcome.ub IRFault.assert_failed. Together with ir_mt_exact this pins the boundary from BOTH sides -- 63 is a value, 64 is a panic -- which is the same two-sided device the ninth chain used at 2^32 - 1 and 2^32, applied to a control-flow arm instead of a residue. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_OOB_SIX, "ir_mt_oob_halts_at_six: the machine is ALREADY HALTED after six steps -- the assert is the sixth node, and its failing arm halts rather than advancing. This is the fact the any-fuel statement is built on. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_OOB_ANY_FUEL, "ir_mt_oob_never_returns_at_any_fuel: *** AND NOTHING AFTER THE ASSERT RUNS. *** For every g, at fuel g + 6, the outcome is still the panic -- the sext, the shl and the ret are never reached, at any fuel whatsoever. Proved by ir_run_steps_split plus ir_run_halted rather than by re-running: once a configuration is halted, ir_run returns its outcome unchanged at every fuel. This is the half of `what happens on the failing side` that a single fixed-fuel execution cannot state. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_OOB_NOT_RET, "ir_mt_oob_is_not_a_return: the failing arm is NOT a value at any fuel -- ir_outcome_is_ret is false. Registered because `ub` and `ret` are different constructors of IROutcome and a reader should not have to take that on trust: no theorem in this chain can mistake a panic for an answer. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_NEG_B0, "ir_mt_neg_b0: the same shape at a NEGATIVE i32 shift amount (bit pattern 2^31). This is the counterfactual that makes the BITCAST semantic rather than decorative: the range check sees the ZERO-extended pattern 2147483648, which is not less than 64, so the assert fails -- whereas the sext on the very same constant would have produced a huge u64. Two different casts of one operand, and the body needs both. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_NEG_FUNC, "ir_mt_neg_func: the negative counterfactual's function. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_NEG_MODULE, "ir_mt_neg_module: the negative counterfactual's module. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_NEG_TRAPS, "ir_mt_neg_traps: *** A NEGATIVE SHIFT AMOUNT PANICS, EXECUTED. *** Rust's `1u64 << (n as i32)` checks `(n as u32) < 64`, and the emitted body does exactly that with a bitcast; at bit pattern 2^31 the check sees 2147483648 and the assert fails. The kernel runs the nine nodes and returns the panic. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_BITCAST, "ir_mt_bitcast_is_the_identity: the bitcast instruction's semantics at THIS chain's exact widths, for EVERY operand -- i32 -> u32 is the canonical width-32 pattern. This is the build item this chain needed, stated as a theorem about the operator rather than only exercised through the machine. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_BITCAST_ZERO_EXT, "ir_mt_bitcast_zero_extends_the_sign_bit: at the i32 sign bit the bitcast answers 2147483648 -- the pattern is REINTERPRETED, not sign-extended. Paired with the sext theorem below it shows the two casts of the SAME operand disagree, which is what makes the body's two casts two different instructions rather than one repeated. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_SEXT_SIGN_EXTENDS, "ir_mt_sext_sign_extends_the_same_pattern: the sext on the SAME operand answers 18446744071562067968 -- the all-ones fill above bit 31. Executed, so `the bitcast and the sext are different functions of one constant` is a kernel-decided fact and not a comment. It is also why the source's range check must use the bitcast: the sext of a negative amount is far above 64 and the shl would be shift_oob. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_SHL_OOB, "ir_mt_shl_out_of_range_is_ub: the shl's OWN range check, independent of the source-level assert, for every operand -- shifting a u64 by 64 is IROutcome.ub IRFault.shift_oob. The body therefore carries TWO guards, and they are not the same guard: the assert is the Rust-level panic the compiler inserted, and this is the machine's. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_ICMP_WIDTH, "ir_mt_icmp_width_is_semantic: the icmp's declared WIDTH decides the answer. The same two operands the negative counterfactual panics on compare TRUE at width 16, because ir_int_cmp canonicalizes both through ir_wrap at the declared width and 2147483648 is 0 there. A transcription at the wrong width decides the opposite predicate, which is why the icmp type lane exists. \n\nWIDTH 16 AND NOT WIDTH 8, and the reason is measured rather than aesthetic: ir_wrap w n goes through ir_nat_rem -> ir_div_go, whose recursion is on the QUOTIENT, so the same theorem at width 8 asks for 2147483648 / 256 = 8,388,608 loop steps. It does not merely cost -- it does NOT ELABORATE: 166.55 s in a full Specification::new() and then the elaborator gives up with the left-hand side entirely unreduced. At width 16 the quotient is 32,768 and the contrast is identical, because 2^31 is 0 modulo 2^16 exactly as it is modulo 2^8. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_MT_ICMP_AT_THE_BODYS_WIDTH, "ir_mt_icmp_at_the_bodys_width_is_false: THE OTHER HALF OF THE SAME CONTRAST, at the width the SHIPPED body actually declares. The very operands that compare true at width 16 compare FALSE at width 32 -- 2147483648 is its own residue there, and it is not below 64. Registered as a theorem rather than left to the reader because `the width is semantic` is a claim about a DIFFERENCE, and a difference needs both sides executed. It is also the fact ir_mt_neg_traps depends on: the negative counterfactual panics precisely because the body's own width-32 comparison is this false. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_RUNS, "CONCRETE EXECUTION WITNESS -- A4's premises are all SATISFIABLE, discharged concretely at the empty heap with the fuel bound by Le.refl. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_HEAP_UNREAD, "CONCRETE WITNESS -- THE HEAP IS GENUINELY UNREAD. The emitted body on the empty heap and on an ARBITRARY heap with an arbitrary next-address counter produces the same outcome. \n\nDerived from A4 at the two heaps rather than re-executed at each, and that is a MEASURED restatement, not a stylistic one: as a bare Eq.refl this declaration cost 326.93 s -- the second most expensive in the whole specification, within 2 s of ir_mt_exact itself -- because the checker had to match the answer against the nine-step run twice more. A4's own proof already IS that run at a SYMBOLIC heap, so the two applications here are substitutions and cost nothing. The statement is unchanged character for character. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_SOUND, "ir_mt_machine_sound_witness: A5 is not vacuous, and its observation premise is an EXECUTION rather than an assumption -- ir_mt_w_runs, the run of the shipped module. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_BOUNDARY, "CONCRETE WITNESS -- the counterfactual at shift 64 is NOT a return, decided by the kernel running it. The boundary is pinned from both sides by execution: ir_mt_w_runs is a value at 63, this is not one at 64. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

// The acceptance tests, moved to a sibling file VERBATIM on 2026-08-17 —
// module body unchanged, no assertion and no test name touched. This file
// stood at 829 lines against the 500-line convention that
// `data/paragon_ratchet.json`'s `files_over_500` enforces shrink-only, and
// the boundary is the one `eval_ir_float_fin_witnesses.rs` already used.
#[cfg(test)]
#[path = "eval_ir_meta_tag_tests.rs"]
mod tests;
