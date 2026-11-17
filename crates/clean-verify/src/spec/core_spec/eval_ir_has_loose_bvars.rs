// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The call chain — `expr::meta::ExprMeta::has_loose_bvars` CALLING
//! `expr::meta::ExprMeta::loose_bvar_range`: the FIRST chain over a body with a
//! `call`, and the first A4 that composes across a call boundary.**
//!
//! ```text
//! pub fn loose_bvar_range(self) -> u32 { (self.0 >> 44) as u32 }   // meta.rs:131
//! pub fn has_loose_bvars(self) -> bool { self.loose_bvar_range() > 0 }  // meta.rs:137
//! ```
//!
//! Two emitted bodies, one module: the CALLER
//! (`tests/fixtures/has_loose_bvars.trust-ir.txt` — call, const u32 0,
//! icmp ugt, ret) and the CALLEE
//! (`tests/fixtures/loose_bvar_range_callee.trust-ir.txt` — extractfield u64,
//! const 44, const 64, icmp ult, assert `#proof: shift_in_range`, zext, lshr,
//! trunc u64->u32, ret). `ExprMeta` is a `u64` newtype passed BY VALUE
//! (`struct.765`), so NO heap premise appears anywhere in this chain.
//!
//! ## The composition IS the deliverable — how the proof is shaped
//!
//! `ir_hlb_correct` is NOT one flat `Eq.refl` over the thirteen-step
//! two-function execution. It is assembled at the call boundary from four
//! separately registered lemmas, each reusable on its own:
//!
//! 1. `ir_hlb_call_step` — ONE step of the caller: `ir_call_exec` resolves the
//!    callee BY FUNCTION ID through `ir_func_find`, resolves the argument in
//!    the CALLER frame, and pushes the callee frame (empty locals, dests = the
//!    call node's result ids, caller pc advanced NOW).
//! 2. `ir_lbr_activation` — THE CALLEE LEMMA, frame-generic: nine steps of the
//!    callee's body, on top of an ARBITRARY dests list and an ARBITRARY frame
//!    stack, end in exactly `ir_ret_to ds rest mem na [int_ (answer e)]`. This
//!    is the `ir_lzm_activation` shape, and it is what makes the lemma usable
//!    BOTH standalone (`ir_lbr_exact`, rest = nil) and under the caller
//!    (`ir_hlb_exact`, rest = the advanced caller frame). The spine pattern.
//! 3. `ir_hlb_resume` — THE SEAM, abstracted over the callee's answer: for
//!    EVERY `k`, if `ir_ret_to` hands the resumed caller `int_ k`, the
//!    remaining three steps return `bool_ (ir_hlb_gt k)`. "If the callee
//!    returns k, the caller returns k > 0" is a registered theorem, not a step
//!    inside an opaque computation.
//! 4. `ir_hlb_exact` — the composition: `ir_run_steps_split` at 13 = 12 + 1
//!    and 12 = 3 + 9, one `Eq.cong` per seam, `ir_hlb_resume` instantiated at
//!    `k := expr_meta_loose_bvar_range e`. No leg re-executes another leg's
//!    steps. (Flat defeq was NOT forced: each Eq.refl leg costs under 0.2 s at
//!    symbolic `e` because every guard the machine decides is concrete.)
//!
//! ## Evidence honesty — read before quoting
//!
//! From `tests/fixtures/has_loose_bvars.lineage.json` (trustc c4e667ca51, the
//! fixture era — the FIRST call-bearing clean-kernel body to flip) and the
//! tip-era `data/crystal_frontier_census_2026-08-21.json`: the CALLER's
//! verdict is `agreed`, `markers_exact` true over 4 REAL marker lines, flip
//! at -O3 and -O0 with lineage equal to its coverage row, asserts=0, one
//! resolved call and a bodyful closure; its interpreter differential is
//! NOT-RUN (a call-bearing body cannot run standalone). **`deferred_to_seam`
//! is TRUE for the caller**: the semantic differential defers to the
//! crate-finalize seam, whose baseline evidence is nearly empty
//! (seam_agreed 2 / samples 4) — recorded here, not hidden, and nothing in
//! this chain claims seam-level differential coverage. **The CALLEE does not
//! flip and its derived-MIR differential is REFUSED BY THE SHIM ("pending
//! local const awaiting finalizer eval") in BOTH producer eras** — its
//! evidence is the pinned emitted IR plus the reflected lemma, and nothing
//! here may claim a differential for it. The census records no flip row for
//! it, and the gate asserts that absence.
//!
//! ## What is proved, and what is deliberately NOT
//!
//! A4 twice (`ir_lbr_correct`, `ir_hlb_correct`): total over the
//! representation — every u64 bit pattern, every spine tail, every heap, every
//! next-address counter, every fuel at or above 9 / 13. A5 both ways
//! (`*_machine_sound`), `*_never_faults`, `ir_hlb_returns_iff`, and the seam
//! theorem `ir_hlb_agrees_with_callee`: the caller's Bool IS `ir_hlb_gt` of
//! the callee's Nat, across different heaps and fuels.
//!
//! The reflected functions are the machine's own vocabulary, transcribed:
//! `expr_meta_loose_bvar_range e = ir_wrap 32 ((e mod 2^64) / 2^44)` and
//! `expr_meta_has_loose_bvars = ir_hlb_gt` of it. NOT proved: that these equal
//! Rust's `(self.0 >> 44) as u32` and `> 0` (the same gap shape as every
//! chain); and the general identity `wrap32 (e >> 44) = e >> 44` — instead the
//! WHY is executed: 64 - 44 = 20, every reachable callee answer fits 20 bits
//! (`ir_hlb_w_top_fits_u32`, `ir_hlb_w_trunc_lossless_at_top`), the trunc IS
//! lossy above u32 (`ir_hlb_w_trunc_drops_above_u32`), and the caller's icmp
//! sees the TRUNCATED u32, not the mathematical k
//! (`ir_hlb_w_seam_sees_the_truncated_u32`: a counterfactual callee answer
//! 2^32 makes the caller answer FALSE at a nonzero k — an answer no real
//! callee run can produce).
//!
//! COST, measured in the private evalir scratchpad (dev profile): every
//! registered declaration below 0.7 s except the two 2^56 - 1 witnesses at
//! ~1.6 s each. The one refusal: `ir_nat_div` is O(quotient) per
//! `ir_div_go`'s fold-guarded loop, and u64::MAX >> 44 walks a
//! 1,048,575-step quotient, so the DECIDED callee answer at u64::MAX DID NOT
//! FINISH — killed after 24+ CPU-minutes (1,450+ s) with no verdict, the
//! `ir_mt_icmp_width` width-8 precedent (does not elaborate; the registered
//! form moves to an affordable point). The u64::MAX rows are pinned through
//! A4 instead (`ir_lbr_w_max_by_a4`, `ir_hlb_w_max_by_composition` — answers
//! left as the reflected residue, spelled as the instances' own types since
//! the closed answer re-pays the division on any defeq step), and the
//! highest DECIDED answers are at `2^56 - 1` (quotient 4,095:
//! `ir_lbr_w_high` = 4095, `ir_hlb_w_high` = true).
//!
//! The link to the emitted artifacts is STRUCTURAL
//! (`tests/crystal_a1_lineage/has_loose_bvars.rs` — both fixtures, plus the
//! cross-fixture callee-identity check). This is width one, times two bodies.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// NOTHING already registered is re-declared. `ir_d0..ir_d16`, `ir_d32`,
// `ir_d64`, `ir_br_tu32` (fifth chain), `ir_vc_tu64` (sixth), `ir_mt_bd9`
// (tenth), `ir_bd3`, `ir_nd`/`ir_nd1`, `ir_nl0`/`ir_nl1`, `ir_vl1`, `ir_sp0`/
// `ir_sp1`, `ir_blk`/`ir_blk0`, `ir_mem0`, `ir_run_le_ret` (fuel),
// `ir_run_steps_split`/`ir_run_halted`/`ir_run_of_steps`/`ir_config_outcome`
// (steps), `ir_outcome_bool`/`ir_outcome_is_ret` (correct), `ir_outcome_nat`
// (kind_ord) and `ir_ret_int_inj` (tenth) all exist, and this stage runs after
// every one of them. Re-declaring one is the eighth chain's recorded error.

// ── the reflected pair and its representation ─────────────────────────
const SRC_EXPRMETAR: &str = "inductive ExprMetaR : Type\n| mk : Nat -> ExprMetaR";
const SRC_EXPR_META_BITS: &str = "def expr_meta_bits (m : ExprMetaR) : Nat := @ExprMetaR.rec (fun (_ : ExprMetaR) => Nat) (fun (n : Nat) => n) m";
const SRC_IR_LBR_SHIFT: &str = "def ir_lbr_shift : Nat := 44";
const SRC_EXPR_META_LOOSE_BVAR_RANGE: &str = "def expr_meta_loose_bvar_range (e : Nat) : Nat := ir_wrap ir_d32 (ir_nat_div (ir_wrap ir_d64 e) (ir_nat_pow2 ir_lbr_shift))";
const SRC_IR_HLB_GT: &str = "def ir_hlb_gt (k : Nat) : Bool := ir_nat_ltb (ir_wrap ir_d32 (ir_wrap ir_d32 0)) (ir_wrap ir_d32 k)";
const SRC_EXPR_META_HAS_LOOSE_BVARS: &str =
    "def expr_meta_has_loose_bvars (e : Nat) : Bool := ir_hlb_gt (expr_meta_loose_bvar_range e)";
const SRC_ENCODESEXPRMETA: &str = "inductive EncodesExprMeta : IRScalar -> ExprMetaR -> Type\n| mk : forall (e : Nat) (rest : IRScalar), EncodesExprMeta (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) rest)) (ExprMetaR.mk e)";
const SRC_ENCODES_EXPR_META_INHABITED: &str = "def encodes_expr_meta_inhabited : EncodesExprMeta (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ Nat.zero) ir_sp0)) (ExprMetaR.mk Nat.zero) := EncodesExprMeta.mk Nat.zero ir_sp0";

// ── the two emitted bodies, MINTED, in ONE two-function module ────────
const SRC_IR_HLB_VAL: &str =
    "def ir_hlb_val (e : Nat) : IRScalar := IRScalar.aggv (ir_sp1 (IRScalar.int_ e))";

/// The MINTED module script, generated from the emitted artifact by
/// `ir_mint_gen` over `generated/ir_hlb.core.txt` + `generated/ir_hlb.tags.json`
/// (crystal A2). `tests/crystal_a2_mint_hlb.rs` fails closed if this committed
/// script is not what minting the committed core module produces.
///
/// **THE FIRST MINTED MODULE WITH TWO FUNCTIONS.** Reader A projected the
/// caller and its callee into ONE core module under ONE interning namespace
/// (`a2project … --with expr::meta::ExprMeta::loose_bvar_range`), so the
/// caller's `(call 1 …)` and the callee's `(func 1 …)` are the same numeral by
/// construction rather than by two agreeing hands. The chain's tag table names
/// the second body, its Clean name prefix and its own interface in the
/// `extra_bodies` lane, and `ir_mint::mint` refuses a module whose function
/// list is not exactly those bodies in that order.
///
/// The 2026-08-23 migration off the hand transcription found NO semantic
/// divergence: the two core modules are equal instruction for instruction and
/// the diff is entirely in three definitionally-equal NOTATION classes, printed
/// verbatim in `tests/crystal_a2_mint_hlb.rs`'s header before adoption — the
/// hand transcription's BORROWED sibling aliases (`ir_br_tu32`, `ir_vc_tu64`)
/// inlined to `(IRTy.uint_ 32)` / `(IRTy.uint_ 64)`, the borrowed nine-node
/// builder `ir_mt_bd9` and the `ir_bd3` tail spelled as raw `IRList.cons`
/// spines, and the hand literal `0` spelled `ir_d0`. `ir_hlb_tself`,
/// `ir_hlb_func`, `ir_lbr_func` and `ir_hlb_module` minted BYTE-IDENTICAL.
const MINTED_IR_HLB: &str = include_str!("generated/ir_hlb.defs.txt");

/// Registration rationales, one per minted line, in script order.
const MINTED_IR_HLB_DOCS: &[&str] = &[
    "ir_hlb_tself: struct.765, the receiver struct id BOTH emitted headers name -- an INTERFACE-ONLY pin, like ir_fc_tflags: it occurs in the two headers and in no instruction of either body. Minted from the tag table's structs lane; the value-addressed semantics never consults it. DerivedProved, zero axiom_deps.",
    "ir_hlb_b0: THE CALLER'S WHOLE BODY, MINTED FROM THE EMITTED ARTIFACT (generated/ir_hlb.core.txt, reader A over the laneREG wc-REG dump_O3 2026-08-21 binary; reader B's independent copy of the same body is tests/fixtures/has_loose_bvars.trust-ir.txt). Four nodes: call func 1 passing %0 and binding %1, const u32 0, icmp ugt %1 %2, ret %3. The call is the point -- the first IRInst.call any chain has registered, and the first the MINT produced rather than a hand. There is no ir_bd4, so the block is the generic IRList.cons spine. DerivedProved, zero axiom_deps.",
    "ir_hlb_func: has_loose_bvars as EvalIR -- own id 0, one by-value parameter, entry block 0. Minted BYTE-IDENTICAL to the hand line it replaces. DerivedProved, zero axiom_deps.",
    "ir_lbr_b0: THE CALLEE'S WHOLE BODY, MINTED FROM THE SAME CORE MODULE (reader B's copy is tests/fixtures/loose_bvar_range_callee.trust-ir.txt). Nine nodes: read self.0 at u64, materialize 44 and 64 at u32, icmp ult, THE ASSERT (#proof: shift_in_range), zext the amount to u64, lshr, trunc to u32, ret. Every token is a CFG lane in the A1 gate. DerivedProved, zero axiom_deps.",
    "ir_lbr_func: loose_bvar_range as EvalIR -- OWN id 1, one by-value parameter, entry block 0. Minted BYTE-IDENTICAL. The id is the one the caller's IRInst.call names, and under the mint it is the same numeral BY CONSTRUCTION: reader A interned the caller's own id first and the callee's second, in ONE namespace, so the level_is_zero collision (caller and callee ids interned from two counters, silently misrouting the call) cannot be reintroduced by a hand. DerivedProved, zero axiom_deps.",
    "ir_hlb_module: *** THE FIRST TWO-FUNCTION MODULE IN THE PROGRAM, AND THE FIRST MINTED ONE *** -- caller then callee, distinct ids 0 and 1, so ir_func_find resolves the call site's target to the callee and the entry-point lookup to whichever body a theorem names. Minted BYTE-IDENTICAL to the hand line. Three independent readers agree on it: the artifact binary (generated/ir_hlb.core.txt), the two emitted texts (tests/fixtures/), and this elaborated term (tests/crystal_a2_mint_hlb.rs M4). See crate::ir_mint. DerivedProved, zero axiom_deps.",
];

/// The minted script's lines, in registration order.
static MINTED_IR_HLB_LINES: std::sync::LazyLock<Vec<&'static str>> =
    std::sync::LazyLock::new(|| {
        MINTED_IR_HLB
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect()
    });

/// The minted `has_loose_bvars` module definitions, in registration order.
#[must_use]
pub fn ir_hlb_module_defs() -> &'static [&'static str] {
    &MINTED_IR_HLB_LINES
}

// ── machines and frames on both sides of the boundary ─────────────────
const SRC_IR_HLB_MACH0: &str = "def ir_hlb_mach0 (v : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 v) (@IRList.nil IRBinding)) (@IRList.nil Nat)) (@IRList.nil IRFrame)) mem na";
const SRC_IR_HLB_FRAME1: &str = "def ir_hlb_frame1 (v : IRScalar) : IRFrame := IRFrame.mk ir_d0 ir_d0 ir_d1 (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 v) (@IRList.nil IRBinding)) (@IRList.nil Nat)";
const SRC_IR_LBR_FRAME: &str = "def ir_lbr_frame (v : IRScalar) (ds : IRList Nat) : IRFrame := IRFrame.mk ir_d1 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 v) (@IRList.nil IRBinding)) ds";
const SRC_IR_LBR_MACH0: &str = "def ir_lbr_mach0 (v : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (ir_lbr_frame v (@IRList.nil Nat)) (@IRList.nil IRFrame)) mem na";
const SRC_IR_HLB_PUSHED: &str = "def ir_hlb_pushed (v : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (ir_lbr_frame v (ir_nl1 ir_d1)) (@IRList.cons IRFrame (ir_hlb_frame1 v) (@IRList.nil IRFrame))) mem na";
const SRC_IR_HLB_INIT: &str = "def ir_hlb_init_is_mach0 (v : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : @Eq IRConfig (ir_init ir_hlb_module ir_d0 (ir_vl1 v) mem na) (IRConfig.running (ir_hlb_mach0 v mem na)) := @Eq.refl IRConfig (IRConfig.running (ir_hlb_mach0 v mem na))";
const SRC_IR_LBR_INIT: &str = "def ir_lbr_init_is_mach0 (v : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : @Eq IRConfig (ir_init ir_hlb_module ir_d1 (ir_vl1 v) mem na) (IRConfig.running (ir_lbr_mach0 v mem na)) := @Eq.refl IRConfig (IRConfig.running (ir_lbr_mach0 v mem na))";

// ── the callee's own panic condition, kernel-decided ──────────────────
#[rustfmt::skip]
const SRC_IR_LBR_GUARD: &str = "def ir_lbr_guard : Bool := ir_nat_ltb (ir_wrap ir_d32 (ir_wrap ir_d32 44)) (ir_wrap ir_d32 (ir_wrap ir_d32 64))";
#[rustfmt::skip]
const SRC_IR_LBR_GUARD_HOLDS: &str = "def ir_lbr_guard_holds : @Eq Bool ir_lbr_guard Bool.true := @Eq.refl Bool Bool.true";

// ── the composition lemmas: call step, callee activation, seam ────────
const SRC_IR_HLB_CALL_STEP: &str = "def ir_hlb_call_step (v : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : @Eq IRConfig (ir_steps ir_d1 ir_hlb_module (IRConfig.running (ir_hlb_mach0 v mem na))) (IRConfig.running (ir_hlb_pushed v mem na)) := ir_call_push ir_hlb_module (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 v) (@IRList.nil IRBinding)) (@IRList.nil Nat)) (@IRList.nil IRFrame) mem na ir_hlb_func ir_hlb_b0 ir_d1 (ir_nl1 ir_d0) (ir_nl1 ir_d1) ir_lbr_func (@Eq.refl (IROption IRFunc) (@IROption.some IRFunc ir_hlb_func)) (@Eq.refl (IROption IRBlock) (@IROption.some IRBlock ir_hlb_b0)) (@Eq.refl (IROption IRNode) (@IROption.some IRNode (IRNode.mk (IRInst.call ir_d1 (ir_nl1 ir_d0)) (ir_nl1 ir_d1)))) (@Eq.refl (IROption IRFunc) (@IROption.some IRFunc ir_lbr_func))";
const SRC_IR_LBR_ACTIVATION: &str = "def ir_lbr_activation (e : Nat) (px : IRScalar) (ds : IRList Nat) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) : @Eq IRConfig (ir_steps ir_d9 ir_hlb_module (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (ir_lbr_frame (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) ds) rest) mem na))) (ir_ret_to ds rest mem na (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range e)))) := @Eq.refl IRConfig (ir_ret_to ds rest mem na (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range e))))";
const SRC_IR_HLB_RESUME: &str = "def ir_hlb_resume (k : Nat) (v : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : @Eq IROutcome (ir_run ir_d3 ir_hlb_module (ir_ret_to (ir_nl1 ir_d1) (@IRList.cons IRFrame (ir_hlb_frame1 v) (@IRList.nil IRFrame)) mem na (ir_vl1 (IRScalar.int_ k)))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (ir_hlb_gt k)))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (ir_hlb_gt k))))";

// ── the exact runs: callee standalone, caller composed ────────────────
const SRC_IR_LBR_EXACT: &str = "def ir_lbr_exact (e : Nat) (px : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : @Eq IROutcome (ir_run ir_d9 ir_hlb_module (IRConfig.running (ir_lbr_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range e)))) := Eq.trans IROutcome (ir_run ir_d9 ir_hlb_module (IRConfig.running (ir_lbr_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (ir_config_outcome (ir_steps ir_d9 ir_hlb_module (IRConfig.running (ir_lbr_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na)))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range e)))) (ir_run_of_steps ir_hlb_module ir_d9 (IRConfig.running (ir_lbr_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (Eq.cong IRConfig IROutcome ir_config_outcome (ir_steps ir_d9 ir_hlb_module (IRConfig.running (ir_lbr_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (ir_ret_to (@IRList.nil Nat) (@IRList.nil IRFrame) mem na (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range e)))) (ir_lbr_activation e px (@IRList.nil Nat) (@IRList.nil IRFrame) mem na))";
const SRC_IR_HLB_EXACT: &str = "def ir_hlb_exact (e : Nat) (px : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : @Eq IROutcome (ir_run ir_d13 ir_hlb_module (IRConfig.running (ir_hlb_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars e)))) := Eq.trans IROutcome (ir_run ir_d13 ir_hlb_module (IRConfig.running (ir_hlb_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (ir_run ir_d12 ir_hlb_module (ir_steps ir_d1 ir_hlb_module (IRConfig.running (ir_hlb_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na)))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars e)))) (ir_run_steps_split ir_hlb_module ir_d12 ir_d1 (IRConfig.running (ir_hlb_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (Eq.trans IROutcome (ir_run ir_d12 ir_hlb_module (ir_steps ir_d1 ir_hlb_module (IRConfig.running (ir_hlb_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na)))) (ir_run ir_d12 ir_hlb_module (IRConfig.running (ir_hlb_pushed (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars e)))) (Eq.cong IRConfig IROutcome (fun (c : IRConfig) => ir_run ir_d12 ir_hlb_module c) (ir_steps ir_d1 ir_hlb_module (IRConfig.running (ir_hlb_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (IRConfig.running (ir_hlb_pushed (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na)) (ir_hlb_call_step (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na)) (Eq.trans IROutcome (ir_run ir_d12 ir_hlb_module (IRConfig.running (ir_hlb_pushed (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (ir_run ir_d3 ir_hlb_module (ir_steps ir_d9 ir_hlb_module (IRConfig.running (ir_hlb_pushed (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na)))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars e)))) (ir_run_steps_split ir_hlb_module ir_d3 ir_d9 (IRConfig.running (ir_hlb_pushed (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (Eq.trans IROutcome (ir_run ir_d3 ir_hlb_module (ir_steps ir_d9 ir_hlb_module (IRConfig.running (ir_hlb_pushed (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na)))) (ir_run ir_d3 ir_hlb_module (ir_ret_to (ir_nl1 ir_d1) (@IRList.cons IRFrame (ir_hlb_frame1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px))) (@IRList.nil IRFrame)) mem na (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range e))))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars e)))) (Eq.cong IRConfig IROutcome (fun (c : IRConfig) => ir_run ir_d3 ir_hlb_module c) (ir_steps ir_d9 ir_hlb_module (IRConfig.running (ir_hlb_pushed (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))) (ir_ret_to (ir_nl1 ir_d1) (@IRList.cons IRFrame (ir_hlb_frame1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px))) (@IRList.nil IRFrame)) mem na (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range e)))) (ir_lbr_activation e px (ir_nl1 ir_d1) (@IRList.cons IRFrame (ir_hlb_frame1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px))) (@IRList.nil IRFrame)) mem na)) (ir_hlb_resume (expr_meta_loose_bvar_range e) (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na))))";

// ── A4, both sides of the boundary ────────────────────────────────────
const SRC_IR_LBR_CORRECT: &str = "def ir_lbr_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (v : IRScalar) (m : ExprMetaR) (h : EncodesExprMeta v m) : Le ir_d9 fuel -> @Eq IROutcome (ir_eval fuel ir_hlb_module ir_d1 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range (expr_meta_bits m))))) := @EncodesExprMeta.rec (fun (v0 : IRScalar) (m0 : ExprMetaR) (_ : EncodesExprMeta v0 m0) => Le ir_d9 fuel -> @Eq IROutcome (ir_eval fuel ir_hlb_module ir_d1 (ir_vl1 v0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range (expr_meta_bits m0)))))) (fun (e : Nat) (px : IRScalar) (hle : Le ir_d9 fuel) => ir_run_le_ret ir_hlb_module ir_d9 fuel hle (IRConfig.running (ir_lbr_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na)) (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range e))) (ir_lbr_exact e px mem na)) v m h";
const SRC_IR_HLB_CORRECT: &str = "def ir_hlb_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (v : IRScalar) (m : ExprMetaR) (h : EncodesExprMeta v m) : Le ir_d13 fuel -> @Eq IROutcome (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars (expr_meta_bits m))))) := @EncodesExprMeta.rec (fun (v0 : IRScalar) (m0 : ExprMetaR) (_ : EncodesExprMeta v0 m0) => Le ir_d13 fuel -> @Eq IROutcome (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars (expr_meta_bits m0)))))) (fun (e : Nat) (px : IRScalar) (hle : Le ir_d13 fuel) => ir_run_le_ret ir_hlb_module ir_d13 fuel hle (IRConfig.running (ir_hlb_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ e) px)) mem na)) (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars e))) (ir_hlb_exact e px mem na)) v m h";

// ── A5 and the corollaries ────────────────────────────────────────────
const SRC_IR_LBR_MACHINE_SOUND: &str = "def ir_lbr_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (v : IRScalar) (m : ExprMetaR) (k : Nat) (h : EncodesExprMeta v m) (hle : Le ir_d9 fuel) (hret : @Eq IROutcome (ir_eval fuel ir_hlb_module ir_d1 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ k)))) : @Eq Nat (expr_meta_loose_bvar_range (expr_meta_bits m)) k := ir_ret_int_inj (expr_meta_loose_bvar_range (expr_meta_bits m)) k (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range (expr_meta_bits m))))) (ir_eval fuel ir_hlb_module ir_d1 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ k))) (Eq.symm IROutcome (ir_eval fuel ir_hlb_module ir_d1 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range (expr_meta_bits m))))) (ir_lbr_correct mem fuel na v m h hle)) hret)";
const SRC_IR_HLB_MACHINE_SOUND: &str = "def ir_hlb_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (v : IRScalar) (m : ExprMetaR) (k : Bool) (h : EncodesExprMeta v m) (hle : Le ir_d13 fuel) (hret : @Eq IROutcome (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ k)))) : @Eq Bool (expr_meta_has_loose_bvars (expr_meta_bits m)) k := Eq.cong IROutcome Bool ir_outcome_bool (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars (expr_meta_bits m))))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ k))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars (expr_meta_bits m))))) (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ k))) (Eq.symm IROutcome (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars (expr_meta_bits m))))) (ir_hlb_correct mem fuel na v m h hle)) hret)";
const SRC_IR_LBR_NEVER_FAULTS: &str = "def ir_lbr_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (v : IRScalar) (m : ExprMetaR) (h : EncodesExprMeta v m) (hle : Le ir_d9 fuel) : @Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_hlb_module ir_d1 (ir_vl1 v) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_hlb_module ir_d1 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range (expr_meta_bits m))))) (ir_lbr_correct mem fuel na v m h hle)";
const SRC_IR_HLB_NEVER_FAULTS: &str = "def ir_hlb_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (v : IRScalar) (m : ExprMetaR) (h : EncodesExprMeta v m) (hle : Le ir_d13 fuel) : @Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars (expr_meta_bits m))))) (ir_hlb_correct mem fuel na v m h hle)";
const SRC_IR_HLB_RETURNS_IFF: &str = "def ir_hlb_returns_iff (mem : IRList IRMemSlot) (mem2 : IRList IRMemSlot) (fuel : Nat) (fuel2 : Nat) (na : Nat) (na2 : Nat) (v : IRScalar) (w : IRScalar) (m : ExprMetaR) (h1 : EncodesExprMeta v m) (h2 : EncodesExprMeta w m) (hle1 : Le ir_d13 fuel) (hle2 : Le ir_d9 fuel2) : @Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v) mem na)) (ir_outcome_is_ret (ir_eval fuel2 ir_hlb_module ir_d1 (ir_vl1 w) mem2 na2)) := Eq.trans Bool (ir_outcome_is_ret (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v) mem na)) Bool.true (ir_outcome_is_ret (ir_eval fuel2 ir_hlb_module ir_d1 (ir_vl1 w) mem2 na2)) (ir_hlb_never_faults mem fuel na v m h1 hle1) (Eq.symm Bool (ir_outcome_is_ret (ir_eval fuel2 ir_hlb_module ir_d1 (ir_vl1 w) mem2 na2)) Bool.true (ir_lbr_never_faults mem2 fuel2 na2 w m h2 hle2))";
const SRC_IR_HLB_AGREES: &str = "def ir_hlb_agrees_with_callee (mem : IRList IRMemSlot) (mem2 : IRList IRMemSlot) (fuel : Nat) (fuel2 : Nat) (na : Nat) (na2 : Nat) (v : IRScalar) (w : IRScalar) (m : ExprMetaR) (h1 : EncodesExprMeta v m) (h2 : EncodesExprMeta w m) (hle1 : Le ir_d13 fuel) (hle2 : Le ir_d9 fuel2) : @Eq Bool (ir_outcome_bool (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v) mem na)) (ir_hlb_gt (ir_outcome_nat (ir_eval fuel2 ir_hlb_module ir_d1 (ir_vl1 w) mem2 na2))) := Eq.trans Bool (ir_outcome_bool (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v) mem na)) (expr_meta_has_loose_bvars (expr_meta_bits m)) (ir_hlb_gt (ir_outcome_nat (ir_eval fuel2 ir_hlb_module ir_d1 (ir_vl1 w) mem2 na2))) (Eq.cong IROutcome Bool ir_outcome_bool (ir_eval fuel ir_hlb_module ir_d0 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars (expr_meta_bits m))))) (ir_hlb_correct mem fuel na v m h1 hle1)) (Eq.cong Nat Bool ir_hlb_gt (expr_meta_loose_bvar_range (expr_meta_bits m)) (ir_outcome_nat (ir_eval fuel2 ir_hlb_module ir_d1 (ir_vl1 w) mem2 na2)) (Eq.cong IROutcome Nat ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range (expr_meta_bits m))))) (ir_eval fuel2 ir_hlb_module ir_d1 (ir_vl1 w) mem2 na2) (Eq.symm IROutcome (ir_eval fuel2 ir_hlb_module ir_d1 (ir_vl1 w) mem2 na2) (IROutcome.ret (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range (expr_meta_bits m))))) (ir_lbr_correct mem2 fuel2 na2 w m h2 hle2))))";

// ── kernel-EXECUTED witnesses ─────────────────────────────────────────
//   0                       false / 0
//   2^44                    true / 1 — the boundary bit
//   2^44 - 1                false / 0 — one below it
//   100 * 2^44 + 7          true / 100 — a mid value
//   2^56 - 1                true / 4095 — the highest DECIDED answer afforded
//   u64::MAX                the range top, pinned through A4 (cost note above)
const SRC_W_HLB_ZERO: &str = "def ir_hlb_w_zero : @Eq IROutcome (ir_eval ir_d13 ir_hlb_module ir_d0 (ir_vl1 (ir_hlb_val 0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";
const SRC_W_LBR_ZERO: &str = "def ir_lbr_w_zero : @Eq IROutcome (ir_eval ir_d9 ir_hlb_module ir_d1 (ir_vl1 (ir_hlb_val 0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 0))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 0)))";
const SRC_W_HLB_BOUNDARY: &str = "def ir_hlb_w_boundary : @Eq IROutcome (ir_eval ir_d13 ir_hlb_module ir_d0 (ir_vl1 (ir_hlb_val 17592186044416)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";
const SRC_W_LBR_BOUNDARY: &str = "def ir_lbr_w_boundary : @Eq IROutcome (ir_eval ir_d9 ir_hlb_module ir_d1 (ir_vl1 (ir_hlb_val 17592186044416)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 1))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 1)))";
const SRC_W_HLB_BELOW: &str = "def ir_hlb_w_below_boundary : @Eq IROutcome (ir_eval ir_d13 ir_hlb_module ir_d0 (ir_vl1 (ir_hlb_val 17592186044415)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";
const SRC_W_LBR_BELOW: &str = "def ir_lbr_w_below_boundary : @Eq IROutcome (ir_eval ir_d9 ir_hlb_module ir_d1 (ir_vl1 (ir_hlb_val 17592186044415)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 0))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 0)))";
const SRC_W_HLB_MID: &str = "def ir_hlb_w_mid : @Eq IROutcome (ir_eval ir_d13 ir_hlb_module ir_d0 (ir_vl1 (ir_hlb_val 1759218604441607)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";
const SRC_W_LBR_MID: &str = "def ir_lbr_w_mid : @Eq IROutcome (ir_eval ir_d9 ir_hlb_module ir_d1 (ir_vl1 (ir_hlb_val 1759218604441607)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 100))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 100)))";
const SRC_W_LBR_HIGH: &str = "def ir_lbr_w_high : @Eq IROutcome (ir_eval ir_d9 ir_hlb_module ir_d1 (ir_vl1 (ir_hlb_val 72057594037927935)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 4095))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 4095)))";
const SRC_W_HLB_HIGH: &str = "def ir_hlb_w_high : @Eq IROutcome (ir_eval ir_d13 ir_hlb_module ir_d0 (ir_vl1 (ir_hlb_val 72057594037927935)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";
const SRC_W_LBR_MAX_BY_A4: &str = "def ir_lbr_w_max_by_a4 : @Eq IROutcome (ir_eval ir_d9 ir_hlb_module ir_d1 (ir_vl1 (ir_hlb_val 18446744073709551615)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range (expr_meta_bits (ExprMetaR.mk 18446744073709551615)))))) := ir_lbr_correct ir_mem0 ir_d9 ir_d0 (ir_hlb_val 18446744073709551615) (ExprMetaR.mk 18446744073709551615) (EncodesExprMeta.mk 18446744073709551615 ir_sp0) (@Le.refl ir_d9)";
const SRC_W_HLB_MAX_BY_COMPOSITION: &str = "def ir_hlb_w_max_by_composition : @Eq IROutcome (ir_eval ir_d13 ir_hlb_module ir_d0 (ir_vl1 (ir_hlb_val 18446744073709551615)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars (expr_meta_bits (ExprMetaR.mk 18446744073709551615)))))) := ir_hlb_correct ir_mem0 ir_d13 ir_d0 (ir_hlb_val 18446744073709551615) (ExprMetaR.mk 18446744073709551615) (EncodesExprMeta.mk 18446744073709551615 ir_sp0) (@Le.refl ir_d13)";

// ── seam honesty: the caller's icmp sees the TRUNCATED u32 ────────────
const SRC_W_TOP_FITS: &str = "def ir_hlb_w_top_fits_u32 : @Eq Bool (ir_nat_ltb 1048575 4294967296) Bool.true := @Eq.refl Bool Bool.true";
const SRC_W_TRUNC_LOSSLESS: &str = "def ir_hlb_w_trunc_lossless_at_top : @Eq Nat (ir_wrap ir_d32 1048575) 1048575 := @Eq.refl Nat 1048575";
const SRC_W_TRUNC_DROPS: &str =
    "def ir_hlb_w_trunc_drops_above_u32 : @Eq Nat (ir_wrap ir_d32 4294967296) 0 := @Eq.refl Nat 0";
const SRC_W_SEAM_TRUNCATED: &str = "def ir_hlb_w_seam_sees_the_truncated_u32 : @Eq IROutcome (ir_run ir_d3 ir_hlb_module (ir_ret_to (ir_nl1 ir_d1) (@IRList.cons IRFrame (ir_hlb_frame1 (ir_hlb_val 0)) (@IRList.nil IRFrame)) ir_mem0 ir_d0 (ir_vl1 (IRScalar.int_ 4294967296)))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";

// ── fail-closed witnesses, including the seam's own ───────────────────
const SRC_W_NOT_AGG: &str = "def ir_hlb_w_scalar_receiver_faults : @Eq IROutcome (ir_eval ir_d13 ir_hlb_module ir_d0 (ir_vl1 (IRScalar.int_ 7)) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_agg) := @Eq.refl IROutcome (IROutcome.type_error IRFault.not_agg)";
const SRC_W_BAD_FIELD: &str = "def ir_hlb_w_empty_spine_faults : @Eq IROutcome (ir_eval ir_d13 ir_hlb_module ir_d0 (ir_vl1 (IRScalar.aggv ir_sp0)) ir_mem0 ir_d0) (IROutcome.type_error IRFault.bad_field) := @Eq.refl IROutcome (IROutcome.type_error IRFault.bad_field)";
const SRC_IR_HLB_HEADLESS: &str = "def ir_hlb_headless_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_hlb_func (@IRList.nil IRFunc)) (@IRList.nil IRGlobal)";
const SRC_W_MISSING_CALLEE: &str = "def ir_hlb_w_missing_callee_is_stuck (e : Nat) : @Eq IROutcome (ir_eval ir_d13 ir_hlb_headless_module ir_d0 (ir_vl1 (ir_hlb_val e)) ir_mem0 ir_d0) (IROutcome.stuck IRFault.no_func) := @Eq.refl IROutcome (IROutcome.stuck IRFault.no_func)";

// ── premise-satisfiability and A5 non-vacuity witnesses ───────────────
const SRC_W_HLB_CORRECT: &str = "def ir_hlb_correct_witness (e : Nat) : @Eq IROutcome (ir_eval ir_d13 ir_hlb_module ir_d0 (ir_vl1 (ir_hlb_val e)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (expr_meta_has_loose_bvars e)))) := ir_hlb_correct ir_mem0 ir_d13 ir_d0 (ir_hlb_val e) (ExprMetaR.mk e) (EncodesExprMeta.mk e ir_sp0) (@Le.refl ir_d13)";
const SRC_W_LBR_CORRECT: &str = "def ir_lbr_correct_witness (e : Nat) : @Eq IROutcome (ir_eval ir_d9 ir_hlb_module ir_d1 (ir_vl1 (ir_hlb_val e)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ (expr_meta_loose_bvar_range e)))) := ir_lbr_correct ir_mem0 ir_d9 ir_d0 (ir_hlb_val e) (ExprMetaR.mk e) (EncodesExprMeta.mk e ir_sp0) (@Le.refl ir_d9)";
const SRC_W_HLB_SOUND: &str = "def ir_hlb_machine_sound_witness : @Eq Bool (expr_meta_has_loose_bvars 17592186044416) Bool.true := ir_hlb_machine_sound ir_mem0 ir_d13 ir_d0 (ir_hlb_val 17592186044416) (ExprMetaR.mk 17592186044416) Bool.true (EncodesExprMeta.mk 17592186044416 ir_sp0) (@Le.refl ir_d13) ir_hlb_w_boundary";
const SRC_W_LBR_SOUND: &str = "def ir_lbr_machine_sound_witness : @Eq Nat (expr_meta_loose_bvar_range 17592186044416) 1 := ir_lbr_machine_sound ir_mem0 ir_d9 ir_d0 (ir_hlb_val 17592186044416) (ExprMetaR.mk 17592186044416) 1 (EncodesExprMeta.mk 17592186044416 ir_sp0) (@Le.refl ir_d9) ir_lbr_w_boundary";
const SRC_W_AGREES: &str = "def ir_hlb_agrees_witness : @Eq Bool (ir_outcome_bool (ir_eval ir_d13 ir_hlb_module ir_d0 (ir_vl1 (ir_hlb_val 17592186044416)) ir_mem0 ir_d0)) (ir_hlb_gt (ir_outcome_nat (ir_eval ir_d9 ir_hlb_module ir_d1 (ir_vl1 (ir_hlb_val 17592186044416)) ir_mem0 ir_d0))) := ir_hlb_agrees_with_callee ir_mem0 ir_mem0 ir_d13 ir_d9 ir_d0 ir_d0 (ir_hlb_val 17592186044416) (ir_hlb_val 17592186044416) (ExprMetaR.mk 17592186044416) (EncodesExprMeta.mk 17592186044416 ir_sp0) (EncodesExprMeta.mk 17592186044416 ir_sp0) (@Le.refl ir_d13) (@Le.refl ir_d9)";

impl Specification {
    /// Register the call chain: `ExprMeta::has_loose_bvars` composed across
    /// the call boundary with `ExprMeta::loose_bvar_range`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    #[allow(clippy::too_many_lines)]
    pub(super) fn add_eval_ir_has_loose_bvars(&mut self) -> Result<(), SpecError> {
        self.add_inductive(SRC_EXPRMETAR, "ExprMetaR: the reflected ExprMeta (expr/meta.rs) -- a NEWTYPE over u64, one constructor carrying one Nat. A wrapper rather than a bare Nat because both emitted bodies take `self` by value as a one-field aggregate; the NodeIdR precedent. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_EXPR_META_BITS, "expr_meta_bits: the newtype projection, by ExprMetaR.rec. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_LBR_SHIFT, "ir_lbr_shift: the shift amount, 44 -- the bit where loose_bvar_range starts in the packed u64. 64 - 44 = 20 is why the callee's trunc to u32 is lossless on every reachable answer; that arithmetic is EXECUTED below, not asserted. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_EXPR_META_LOOSE_BVAR_RANGE, "expr_meta_loose_bvar_range: the reflected `(self.0 >> 44) as u32` (expr/meta.rs:131), in the machine's own vocabulary -- canonicalize the u64 carrier, divide by 2^44 (ir_lshr_bits' exact semantics), canonicalize the trunc at width 32. NOT a proof that Rust's shift-and-cast is this function; that gap is the same shape as every chain's. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_GT, "ir_hlb_gt: THE CALLER'S CONTINUATION as a function of the callee's answer k -- `0 < k` at the icmp's width-32 canonicalization, double-wrapped zero because IRInst.const_ canonicalizes the literal and ir_int_cmp canonicalizes both operands again. Naming it separately is what lets ir_hlb_resume abstract over the callee's answer: the spine pattern. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_EXPR_META_HAS_LOOSE_BVARS, "expr_meta_has_loose_bvars: the reflected `self.loose_bvar_range() > 0` (expr/meta.rs:137) -- LITERALLY the composition ir_hlb_gt of expr_meta_loose_bvar_range, so the reflected pair mirrors the Rust call graph. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESEXPRMETA, "EncodesExprMeta v m: the runtime VALUE v represents the ExprMeta m. By value, spine-agnostic past field 0, NO heap premise -- ExprMeta is a u64 newtype passed by value and neither body performs a load. Same open layout obligation as every chain: the integer sitting at slot 0 is a producer layout fact. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ENCODES_EXPR_META_INHABITED, "encodes_expr_meta_inhabited: the premise-satisfiability witness, registered beside the relation for the premise-witness ratchet. DerivedProved, zero axiom_deps.")?;
        // The module is REPLAYED from the minted script, line for line — the
        // eval_ir_contains.rs / eval_ir_flat_flags_with.rs posture. `ir_hlb_val`
        // is registered first because it is the chain's own vocabulary and not
        // part of the emitted module.
        self.add_recursive_def(SRC_IR_HLB_VAL, "ir_hlb_val: the runtime value of an ExprMeta -- a one-field aggregate carrying the u64. DerivedProved, zero axiom_deps.")?;
        let minted = ir_hlb_module_defs();
        if minted.len() != MINTED_IR_HLB_DOCS.len() {
            return Err(SpecError::EnvError(format!(
                "the minted ir_hlb script has {} definitions but {} rationales are declared; \
                 regenerate the docs table with the script rather than reusing it",
                minted.len(),
                MINTED_IR_HLB_DOCS.len()
            )));
        }
        for (line, doc) in minted.iter().zip(MINTED_IR_HLB_DOCS) {
            self.add_recursive_def(line, doc)?;
        }
        self.add_recursive_def(SRC_IR_HLB_MACH0, "ir_hlb_mach0: the machine ir_init produces for the CALLER entry -- definitionally equal to it (no globals). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_FRAME1, "ir_hlb_frame1: the caller's frame AFTER the call step -- same locals, pc advanced to 1. ir_push advances the caller NOW so the return resumes after the call; this is that frame, named so the seam lemmas can quantify over what sits under the callee. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_LBR_FRAME, "ir_lbr_frame: a callee frame with the dests ABSTRACT -- function 1, entry block, empty-start locals bound to one value, return destinations ds. The parameter that makes ir_lbr_activation frame-generic. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_LBR_MACH0, "ir_lbr_mach0: the machine ir_init produces for the CALLEE entry -- ir_lbr_frame with no dests, alone on the stack. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_PUSHED, "ir_hlb_pushed: the machine ONE STEP after the caller starts -- the callee frame (dests [1], the call node's result id) on top of the advanced caller frame. The state the composition splits at. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_INIT, "ir_hlb_init_is_mach0: the hand-written caller initial machine IS the one ir_init builds, for every value, heap and counter -- including that ir_func_find resolves entry id 0 to the FIRST function. Registered so a change to ir_init or to the module's function order stops reducing here. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_LBR_INIT, "ir_lbr_init_is_mach0: the same for the CALLEE entry -- ir_func_find must walk PAST the caller (ir_nat_eqb 0 1 is false) and match the callee's own id. The first init lemma in the program whose lookup skips a function. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_LBR_GUARD, "ir_lbr_guard: the callee's own panic condition, spelled exactly as the machine computes it -- the const's width-32 canonicalization of 44, re-canonicalized by ir_int_cmp, against the same for 64. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_LBR_GUARD_HOLDS, "ir_lbr_guard_holds: *** THE KERNEL DECIDES THAT THE ASSERT PASSES: 44 < 64. *** By computation. This is the `#proof: shift_in_range` obligation's runtime shadow, and why the callee never reaches ir_assert_b's false minor. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_CALL_STEP, "ir_hlb_call_step: *** THE CALL BOUNDARY, ONE STEP, AS A THEOREM. *** ir_call_exec resolves the callee BY FUNCTION ID via ir_func_find over the module's function list, resolves the argument in the CALLER frame, and pushes: callee locals start EMPTY then bind positionally, the call node's result ids travel as the callee's return destinations, and the caller's pc advances NOW. RE-DERIVED 2026-09-24 through the GENERIC call step ir_call_push (eval_ir_stack_split.rs), statement unchanged: the four lookups (caller function, its block 0, node 0 `call 1 [0]` with result id 1, callee ir_lbr_func) are each Eq.refl over the concrete module, and ir_steps ir_d1 on a running machine IS one ir_step. At a symbolic argument value. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_LBR_ACTIVATION, "ir_lbr_activation: *** THE CALLEE LEMMA, FRAME-GENERIC -- THE SPINE PATTERN. *** For every bit pattern, spine tail, DESTS LIST, UNDERLYING FRAME STACK, heap and counter: nine steps of the callee end in exactly ir_ret_to ds rest mem na [int_ (expr_meta_loose_bvar_range e)]. The ir_lzm_activation shape: because ds and rest are abstract, the SAME lemma discharges the standalone callee run (rest = nil) and the run under the caller (rest = the advanced caller frame) -- the composition never re-executes the callee. One Eq.refl; every guard the machine decides (the assert, both cast width checks, the lshr range check) is concrete. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_RESUME, "ir_hlb_resume: *** THE SEAM, ABSTRACTED OVER THE CALLEE'S ANSWER. *** For EVERY k: ir_ret_to pops to the caller and binds int_ k to %1 (the call node's declared result), and the remaining const/icmp/ret return bool_ (ir_hlb_gt k). This is `if the callee returns k, the caller returns k > 0` as a registered theorem -- the composition's load-bearing abstraction, and the exact lemma shape the checker spine needs at every future call boundary. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_LBR_EXACT, "ir_lbr_exact: the callee's standalone nine-step run, DERIVED from ir_lbr_activation at ds = nil, rest = nil (where ir_ret_to halts the machine) rather than proved by a second flat execution -- ir_run_of_steps plus one Eq.cong. The callee lemma used the first of its two ways. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_EXACT, "ir_hlb_exact: *** THE COMPOSED RUN -- THE PROOF GOES THROUGH THE CALL BOUNDARY, NOT AROUND IT. *** ir_run_steps_split at 13 = 12 + 1 isolates the call step (ir_hlb_call_step); split again at 12 = 3 + 9 hands the callee frames to ir_lbr_activation instantiated UNDER the advanced caller frame with dests [1]; ir_hlb_resume at k := expr_meta_loose_bvar_range e finishes the icmp. Four lemmas, two Eq.congs, no leg re-executes another's steps, and the final answer is ir_hlb_gt (expr_meta_loose_bvar_range e) = expr_meta_has_loose_bvars e by delta -- the reflected composition equals the machine composition. NOT one flat Eq.refl over the two-function execution: flat defeq was affordable here (measured), but the composition IS the deliverable and each piece is separately reusable. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_LBR_CORRECT, "ir_lbr_correct: *** A4 FOR THE CALLEE. *** For every ExprMetaR, every representing value (any tail), every heap, every counter, every fuel at or above 9: ir_eval on the TWO-function module at entry id 1 returns exactly int_ (expr_meta_loose_bvar_range bits). Evidence honesty: the callee does NOT flip and its derived-MIR differential is REFUSED BY THE SHIM ('pending local const awaiting finalizer eval') in both producer eras -- its evidence is the pinned emitted IR plus this lemma, and NOTHING here claims a differential for it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_CORRECT, "ir_hlb_correct: *** A4 FOR THE CALLER, THE FIRST COMPOSED-ACROSS-A-CALL EQUALITY THEOREM. *** For every ExprMetaR, every representing value, every heap, every counter, every fuel at or above 13: the two-function module at entry id 0 returns exactly bool_ (expr_meta_has_loose_bvars bits). Proved through ir_hlb_exact's boundary decomposition. Evidence (data/crystal_frontier_census_2026-08-21.json): verdict agreed, markers_exact TRUE over 4 real marker lines, flip at -O3 and -O0 with lineage sha256:446663ac... equal to the coverage row, asserts=0, ONE resolved call with a bodyful closure. deferred_to_seam is TRUE: the semantic differential defers to the crate-finalize seam whose baseline evidence is 2/4 -- recorded, not hidden, and no seam-level differential is claimed. A1 is gated by tests/crystal_a1_lineage/has_loose_bvars.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_LBR_MACHINE_SOUND, "ir_lbr_machine_sound: A5 for the callee -- if the machine answers k, the reflected function's value IS k, via the tenth chain's ir_ret_int_inj. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_MACHINE_SOUND, "ir_hlb_machine_sound: *** A5 FOR THE CALLER, THE INVERSION. *** If the machine running the composed module answers k, the reflected composition IS k -- for every Bool k, read back through ir_outcome_bool. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_LBR_NEVER_FAULTS, "ir_lbr_never_faults: the callee never faults on a represented ExprMeta -- in particular THE ASSERT EXECUTES TRUE (44 < 64, ir_lbr_guard_holds), the lshr amount is in range, and both casts pass their width guards. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_NEVER_FAULTS, "ir_hlb_never_faults: the COMPOSED run never faults -- no UB, no type error, no stuck state (in particular no no_func: the callee is IN the module), no exhaustion at fuel 13. The fail-closed witnesses below show each escape hatch is real. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_RETURNS_IFF, "ir_hlb_returns_iff: the caller returns a value exactly when the callee does -- stated across DIFFERENT heaps, counters and fuels for the two runs, both sides pinned to Bool.true through the two A4s. On this total pair the iff is two trues; it is the float chains' boundary statement specialized to a body with no refusals. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_AGREES, "ir_hlb_agrees_with_callee: *** THE SEAM THEOREM -- THE CALLER'S ANSWER IS DETERMINED BY THE CALLEE'S ANSWER. *** For any two representations of the SAME ExprMetaR, across different heaps, counters and fuels: ir_outcome_bool of the caller's run EQUALS ir_hlb_gt of ir_outcome_nat of the callee's run. The machine-level image of `has_loose_bvars = loose_bvar_range > 0`, proved by composing the two A4s at the reflected middle -- the statement the checker spine repeats at every caller/callee pair. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_HLB_ZERO, "CONCRETE EXECUTION WITNESS -- the composed run at 0 answers false. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_LBR_ZERO, "CONCRETE EXECUTION WITNESS -- the callee at 0 answers 0. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_HLB_BOUNDARY, "*** CONCRETE EXECUTION WITNESS -- 2^44, THE BOUNDARY: *** the lowest bit of the packed range field, and the composed run answers true. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_LBR_BOUNDARY, "CONCRETE EXECUTION WITNESS -- the callee at 2^44 answers exactly 1. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_HLB_BELOW, "CONCRETE EXECUTION WITNESS -- 2^44 - 1, every bit BELOW the range field set, and the composed run answers false: the boundary pinned from both sides. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_LBR_BELOW, "CONCRETE EXECUTION WITNESS -- the callee at 2^44 - 1 answers 0. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_HLB_MID, "CONCRETE EXECUTION WITNESS -- a mid value, 100 * 2^44 + 7: true. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_LBR_MID, "CONCRETE EXECUTION WITNESS -- the callee at the mid value answers 100: payload bits below 44 do not leak into the range. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_LBR_HIGH, "CONCRETE EXECUTION WITNESS -- 2^56 - 1, every bit through 55 set: the callee answers 2^12 - 1 = 4095, the HIGHEST decided answer this chain affords (ir_nat_div is O(quotient); see the module doc's cost note and the u64::MAX refusal beside it). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_HLB_HIGH, "CONCRETE EXECUTION WITNESS -- the composed run at 2^56 - 1 answers true, decided by the kernel through the call boundary. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_LBR_MAX_BY_A4, "ir_lbr_w_max_by_a4: *** u64::MAX, THE RANGE TOP -- PINNED THROUGH A4, WITH THE DECIDED FORM MEASURED AND REFUSED. *** Deciding the answer walks ir_div_go's 1,048,575-step quotient (see the module doc's measured refusal); the answer is therefore left as the reflected residue, and the statement spells it expr_meta_loose_bvar_range (expr_meta_bits (ExprMetaR.mk u64::MAX)) -- SYNTACTICALLY the A4 instance's own type, because at a CLOSED bit pattern the residue is computable and whnf does not stop at a definition (the tenth chain's closed-answer trap): any spelling that needs one defeq step here re-pays the whole division. The decided top-of-range facts live in ir_lbr_w_high (quotient 4095) and the seam-honesty trio. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_HLB_MAX_BY_COMPOSITION, "ir_hlb_w_max_by_composition: the COMPOSED run at u64::MAX, derived through ir_hlb_correct with the answer left as the reflected residue -- same closed-answer spelling discipline as ir_lbr_w_max_by_a4, same reason. Honest strength: an A4 instance, not a kernel-decided Bool.true. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_TOP_FITS, "SEAM HONESTY 1 -- WHY THE TRUNC IS LOSSLESS HERE: 2^20 - 1 < 2^32, kernel-decided. 64 - 44 = 20 <= 32, so every reachable callee answer fits the u32 the caller's icmp sees. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_TRUNC_LOSSLESS, "SEAM HONESTY 2 -- the trunc's wrap is the IDENTITY at the range top: ir_wrap 32 (2^20 - 1) = 2^20 - 1, executed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_TRUNC_DROPS, "SEAM HONESTY 3 -- the trunc lane is NOT vacuously lossless: ir_wrap 32 (2^32) = 0, executed. A 12-bit shift would have made the seam lossy; 44 does not, and that is arithmetic, not luck. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_SEAM_TRUNCATED, "*** SEAM HONESTY 4 -- THE CALLER'S ICMP SEES THE TRUNCATED u32, EXECUTED. *** Feed the resumed caller a COUNTERFACTUAL callee answer of 2^32 (no real callee run can produce it -- answers fit 20 bits) and the caller answers FALSE at a nonzero k, because ir_int_cmp canonicalizes %1 at width 32. The seam's weakness exhibited exactly where it lives, next to the three facts showing it is unreachable for this pair. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_NOT_AGG, "FAIL-CLOSED WITNESS -- a bare integer receiver faults not_agg INSIDE THE CALLEE FRAME: the caller pushes, the callee's extractfield refuses, the whole two-function machine halts. Faults propagate across the boundary; EncodesExprMeta cannot be weakened. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_BAD_FIELD, "FAIL-CLOSED WITNESS -- an empty aggregate spine is bad_field, again surfacing from the callee frame through the composed run. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_HLB_HEADLESS, "ir_hlb_headless_module: the caller WITHOUT its callee -- the instrument for the seam's own fail-closed witness. NOT a transcription of any shipped artifact; the CFG gate does not run against it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_MISSING_CALLEE, "*** FAIL-CLOSED WITNESS -- THE SEAM ITSELF: A MISSING CALLEE IS STUCK, NOT UB, at every bit pattern. *** ir_func_find returns none and ir_call_exec halts stuck no_func -- the fail-closed behaviour the level_is_zero lane documents for a non-bodyful closure, here EXECUTED rather than narrated. This is why ir_hlb_correct needs the callee IN the module and why a bodyful reachable closure is A0 criterion rather than pedantry. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_HLB_CORRECT, "ir_hlb_correct_witness: A4's premises are satisfiable, discharged concretely; the bit pattern stays universally quantified. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_LBR_CORRECT, "ir_lbr_correct_witness: the callee A4's premises are satisfiable, discharged concretely. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_HLB_SOUND, "ir_hlb_machine_sound_witness: A5 is not vacuous -- its observation premise is the executed boundary run, and the kernel decides the reflected composition equals true at 2^44. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_LBR_SOUND, "ir_lbr_machine_sound_witness: the callee A5 is not vacuous -- the executed boundary run pins the reflected value to exactly 1. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_AGREES, "ir_hlb_agrees_witness: the seam theorem's premises are satisfiable at the boundary value -- both runs executed, one heap, the agreement decided by instantiation. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

// The source-level assertions about the registered constants and the minted
// script — split out (rust_excellence 500-line rule) following the pattern the
// chain's own A1 evidence gates use.
#[cfg(test)]
#[path = "eval_ir_has_loose_bvars_tests.rs"]
mod tests;
