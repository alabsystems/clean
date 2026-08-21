// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The zext chain — `cert::builder::state::NodeId::index`, closing the
//! `zext` opcode lane (2026-08-20 tranche).**
//!
//! ```text
//! pub struct NodeId(pub(crate) u32);        // cert/builder/state.rs:19
//! pub(super) fn index(self) -> usize {
//!     self.0 as usize                       // cert/builder/state.rs:26
//! }
//! ```
//!
//! ```text
//! rustcc fn @cert::builder::state::NodeId::index(functy.97) {
//! bb0(%0: struct.323):
//!     %1 = extractfield u32 %0, 0
//!     %2 = zext u32 %1 to usize
//!     ret %2
//! }
//! ```
//!
//! ## Why this body, and which twin it is
//!
//! The ninth chain's census named two `zext u32 -> usize` bodies that are the
//! same instruction sequence twice — this one and
//! `env::persistent_ext::ExtensionIdx::index` (`struct.323` vs `struct.848`
//! and nothing else). This chain covers `NodeId::index` ONLY; the sibling
//! remains unchained, and nothing here transfers to it except the registered
//! cast semantics.
//!
//! ## THE `usize` DECISION — a target assumption, made loudly
//!
//! The ninth chain deliberately left `usize` UNRESOLVED (`?usize`) in the CFG
//! type lane and made `assert_lanes` refuse it on either side, so that the
//! first chain over a `zext u32 -> usize` body would have to decide the width
//! rather than inherit one. This is that decision: **`ir_ni_tusize` is
//! `IRTy.uint_ ir_d64` — `usize` is resolved to 64 bits.** It is a TARGET
//! assumption, not a theorem: the recorded producer is the local stage1
//! trustc on `aarch64-apple-darwin` (a 64-bit target, pinned in
//! `tests/fixtures/node_id_index.lineage.json` and asserted by the gate), and
//! on a 32-bit target the emitted body would be a different function. The
//! parser keeps refusing `?usize`; the resolution happens ONCE, in
//! `tests/crystal_a1_lineage/node_id_index.rs`, where it is asserted against
//! the raw `?usize` token first.
//!
//! ## Evidence honesty — read before quoting
//!
//! From the coherent 2026-08-20 dump (trustc `10130575c`): verdict `agreed`
//! (4 canonical lines identical), `markers_exact` true over 2 REAL marker
//! lines, flip event fired with lineage == coverage row. **The producer's
//! interpreter differential is NOT-RUN on this body — 0 samples** ("non-scalar
//! parameter type is non-interpretable": the argument is a by-value newtype
//! struct). Unlike the float chains' agreed/64, NOTHING here claims
//! interpreter agreement; the evidence is agreed + markers_exact +
//! flip-lineage equality + the kernel-executed witnesses below.
//!
//! ## What is proved, and what is deliberately NOT
//!
//! A4 (`ir_ni_correct`) is TOTAL over the representation: for every `NodeIdR`
//! — every Nat bit pattern `n`, via `NodeIdR.mk n` — every aggregate value
//! representing it (tail-agnostic past field 0), every heap, every
//! next-address counter and every fuel at or above 3, the machine returns
//! exactly `int_ (cert_node_id_index i)`. A5 is the inversion
//! (`ir_ni_machine_sound`) plus the argument-reaching form
//! (`ir_ni_low_word_decides`): the emitted body's outcome depends on the
//! stored pattern only through its canonical low word.
//!
//! `cert_node_id_index` is `ir_wrap ir_d64 (ir_wrap ir_d32 n)` — the
//! machine's own vocabulary, transcribed, not simplified. Deliberately NOT
//! proved: that this equals Rust's `as usize` (the same gap shape every chain
//! states); and the general identity law `n < 2^32 -> ir_wrap ir_d64
//! (ir_wrap ir_d32 n) = n`, which needs `ir_nat_rem` lemmas nobody has earned
//! — buying them with kernel-native accelerated constants would be speed
//! bought with trust, refused on the same ground as the eighth and ninth
//! chains. What IS registered generally is the conditional form (equal
//! reflected values give equal outcomes) and the exact cast semantics at this
//! chain's own types; the identity is EXECUTED at 0, 1, 2^31 and 2^32 - 1,
//! and the sext contrast is EXECUTED at the same patterns rather than argued.
//!
//! The link to the emitted artifact is STRUCTURAL
//! (`tests/crystal_a1_lineage/node_id_index.rs`); everything past the flip
//! seam is downstream and covered by nothing here. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// NOTHING is re-declared here. `ir_d8`/`ir_d32`/`ir_d64`, `ir_br_tu32` (fifth
// chain), `ir_tU8` (crystal), `ir_outcome_nat` (second), `ir_outcome_is_ret`,
// `ir_run_le_ret`, `ir_cast_eval`, `ir_sext_value`, `ir_wrap`, the list/spine
// builders and `ir_mem0` all already exist, and this stage runs after every
// one of them. `ir_gc_opcode_is_semantic` (ninth chain) already states that
// `zext u64 -> u32` faults; it is cited, not re-proved.

// ── the reflected function and its representation ─────────────────────
const SRC_NODEIDR: &str = "inductive NodeIdR : Type\n| mk : Nat -> NodeIdR";
const SRC_NODE_ID_BITS: &str = "def node_id_bits (i : NodeIdR) : Nat := NodeIdR.rec (fun (_ : NodeIdR) => Nat) (fun (n : Nat) => n) i";
const SRC_CERT_NODE_ID_INDEX: &str = "def cert_node_id_index (i : NodeIdR) : Nat := ir_wrap ir_d64 (ir_wrap ir_d32 (node_id_bits i))";
const SRC_ENCODESNODEID: &str = "inductive EncodesNodeId : IRScalar -> NodeIdR -> Type\n| mk : forall (n : Nat) (rest : IRScalar), EncodesNodeId (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n) rest)) (NodeIdR.mk n)";
const SRC_ENCODES_NODE_ID_INHABITED: &str = "def encodes_node_id_inhabited : EncodesNodeId (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ Nat.zero) ir_sp0)) (NodeIdR.mk Nat.zero) := EncodesNodeId.mk Nat.zero ir_sp0";

// ── the usize decision ────────────────────────────────────────────────
const SRC_IR_NI_TUSIZE: &str = "def ir_ni_tusize : IRTy := IRTy.uint_ ir_d64";

// ── the emitted module, transcribed ───────────────────────────────────
const SRC_IR_NI_TSELF: &str = "def ir_ni_tself : IRTy := IRTy.struct_ 323";
const SRC_IR_NI_B0: &str = "def ir_ni_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 (ir_nd1 (IRInst.extractfield ir_br_tu32 ir_d0 ir_d0) ir_d1) (ir_nd1 (IRInst.cast IRCastOp.zext ir_br_tu32 ir_ni_tusize ir_d1) ir_d2) (ir_nd (IRInst.ret (ir_nl1 ir_d2))))";
// `#[rustfmt::skip]`: the gate reads this declaration back with
// `clean_block_sources("…", "const SRC_IR_NI_FUNC")`, which collects LINES
// starting with that prefix — the tenth chain's `SRC_IR_MT_FUNC` precedent.
#[rustfmt::skip]
const SRC_IR_NI_FUNC: &str = "def ir_ni_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_ni_b0 ir_blk0)";
const SRC_IR_NI_MODULE: &str = "def ir_ni_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_ni_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";
const SRC_IR_NI_VAL: &str =
    "def ir_ni_val (n : Nat) : IRScalar := IRScalar.aggv (ir_sp1 (IRScalar.int_ n))";

// ── the machine ───────────────────────────────────────────────────────
const SRC_IR_NI_MACH0: &str = "def ir_ni_mach0 (v : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 v) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";
const SRC_IR_NI_EXACT: &str = "def ir_ni_exact (mem : IRList IRMemSlot) (na : Nat) (x : Nat) (px : IRScalar) : Eq IROutcome (ir_run ir_d3 ir_ni_module (IRConfig.running (ir_ni_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ x) px)) mem na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index (NodeIdR.mk x))))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index (NodeIdR.mk x)))))";

// ── A4, A5, and the corollaries ───────────────────────────────────────
const SRC_IR_NI_CORRECT: &str = "def ir_ni_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (v : IRScalar) (i : NodeIdR) (h : EncodesNodeId v i) : Le ir_d3 fuel -> Eq IROutcome (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index i)))) := EncodesNodeId.rec (fun (v0 : IRScalar) (i0 : NodeIdR) (_ : EncodesNodeId v0 i0) => Le ir_d3 fuel -> Eq IROutcome (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 v0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index i0))))) (fun (n : Nat) (rest : IRScalar) (hle : Le ir_d3 fuel) => ir_run_le_ret ir_ni_module ir_d3 fuel hle (IRConfig.running (ir_ni_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n) rest)) mem na)) (ir_vl1 (IRScalar.int_ (cert_node_id_index (NodeIdR.mk n)))) (ir_ni_exact mem na n rest)) v i h";
const SRC_IR_NI_MACHINE_SOUND: &str = "def ir_ni_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (v : IRScalar) (i : NodeIdR) (k : Nat) (h : EncodesNodeId v i) (hle : Le ir_d3 fuel) (hret : Eq IROutcome (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ k)))) : Eq Nat (cert_node_id_index i) k := Eq.cong IROutcome Nat ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index i)))) (IROutcome.ret (ir_vl1 (IRScalar.int_ k))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index i)))) (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ k))) (Eq.symm IROutcome (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index i)))) (ir_ni_correct mem fuel na v i h hle)) hret)";
const SRC_IR_NI_NEVER_FAULTS: &str = "def ir_ni_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (v : IRScalar) (i : NodeIdR) (h : EncodesNodeId v i) (hle : Le ir_d3 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 v) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index i)))) (ir_ni_correct mem fuel na v i h hle)";

// A5 REACHING PAST THE ANSWER, ONTO THE ARGUMENTS: the outcome depends on the
// stored pattern only through the reflected value.
const SRC_IR_NI_LOW_WORD_DECIDES: &str = "def ir_ni_low_word_decides (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (px : IRScalar) (py : IRScalar) (n : Nat) (m : Nat) (hle : Le ir_d3 fuel) (heq : Eq Nat (cert_node_id_index (NodeIdR.mk n)) (cert_node_id_index (NodeIdR.mk m))) : Eq IROutcome (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n) px))) mem na) (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ m) py))) mem na) := Eq.trans IROutcome (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n) px))) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index (NodeIdR.mk m))))) (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ m) py))) mem na) (Eq.trans IROutcome (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n) px))) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index (NodeIdR.mk n))))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index (NodeIdR.mk m))))) (ir_ni_correct mem fuel na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n) px)) (NodeIdR.mk n) (EncodesNodeId.mk n px) hle) (Eq.cong Nat IROutcome (fun (k : Nat) => IROutcome.ret (ir_vl1 (IRScalar.int_ k))) (cert_node_id_index (NodeIdR.mk n)) (cert_node_id_index (NodeIdR.mk m)) heq)) (Eq.symm IROutcome (ir_eval fuel ir_ni_module ir_d0 (ir_vl1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ m) py))) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index (NodeIdR.mk m))))) (ir_ni_correct mem fuel na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ m) py)) (NodeIdR.mk m) (EncodesNodeId.mk m py) hle))";

// ── CAST SEMANTICS, stated as theorems rather than as prose ───────────
const SRC_IR_NI_ZEXT_SEMANTICS: &str = "def ir_ni_zext_semantics (n : Nat) : Eq IRStepResult (ir_cast_eval IRCastOp.zext ir_br_tu32 ir_ni_tusize (IRScalar.int_ n)) (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d64 (ir_wrap ir_d32 n)))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d64 (ir_wrap ir_d32 n))))";
const SRC_IR_NI_SEXT_SEMANTICS: &str = "def ir_ni_sext_semantics (n : Nat) : Eq IRStepResult (ir_cast_eval IRCastOp.sext ir_br_tu32 ir_ni_tusize (IRScalar.int_ n)) (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d64 (ir_sext_value ir_d32 ir_d64 n)))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d64 (ir_sext_value ir_d32 ir_d64 n))))";
const SRC_IR_NI_NARROWER_DEST_FAULTS: &str = "def ir_ni_narrower_dest_is_a_fault (a : IRScalar) : Eq IRStepResult (ir_cast_eval IRCastOp.zext ir_br_tu32 ir_tU8 a) ir_width_fault := Eq.refl IRStepResult ir_width_fault";
const SRC_IR_NI_SOURCE_WIDTH: &str = "def ir_ni_source_width_is_the_canonicalizer (n : Nat) : Eq IRStepResult (ir_cast_eval IRCastOp.zext ir_tU8 ir_ni_tusize (IRScalar.int_ n)) (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d64 (ir_wrap ir_d8 n)))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d64 (ir_wrap ir_d8 n))))";
const SRC_IR_NI_NOT_INT: &str = "def ir_ni_non_integer_operand_is_a_type_error (b : Bool) : Eq IRStepResult (ir_cast_eval IRCastOp.zext ir_br_tu32 ir_ni_tusize (IRScalar.bool_ b)) (IRStepResult.fault (IROutcome.type_error IRFault.not_int)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_int))";

// ── kernel-EXECUTED witnesses ─────────────────────────────────────────
//   0, 1                    the bottom of the range, preserved exactly
//   2147483648 = 2^31       the sign-bit boundary, preserved by zext
//   4294967295 = 2^32 - 1   the top of the u32 range — THE zext/sext contrast
//   4294967296 = 2^32       a non-canonical pattern: wrapped at the SOURCE
const SRC_W_ZERO: &str = "def ir_ni_w_zero : Eq IROutcome (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (ir_ni_val 0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 0)))";
const SRC_W_ONE: &str = "def ir_ni_w_one : Eq IROutcome (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (ir_ni_val 1)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 1))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 1)))";
const SRC_W_MID: &str = "def ir_ni_w_sign_bit_survives : Eq IROutcome (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (ir_ni_val 2147483648)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 2147483648))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 2147483648)))";
const SRC_W_U32MAX: &str = "def ir_ni_w_u32max_survives : Eq IROutcome (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (ir_ni_val 4294967295)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 4294967295))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 4294967295)))";
const SRC_W_2P32: &str = "def ir_ni_w_2p32_wraps_at_the_source : Eq IROutcome (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (ir_ni_val 4294967296)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 0)))";
const SRC_W_COLLAPSE: &str = "def ir_ni_two_patterns_one_answer : Eq IROutcome (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (ir_ni_val 7)) ir_mem0 ir_d0) (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (ir_ni_val 4294967303)) ir_mem0 ir_d0) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 7)))";
const SRC_W_SEXT_U32MAX: &str = "def ir_ni_sext_would_differ_at_u32max : Eq IRStepResult (ir_cast_eval IRCastOp.sext ir_br_tu32 ir_ni_tusize (IRScalar.int_ 4294967295)) (IRStepResult.value (IRScalar.int_ 18446744073709551615)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 18446744073709551615))";
const SRC_W_SEXT_BELOW: &str = "def ir_ni_sext_agrees_below_the_sign_bit : Eq IRStepResult (ir_cast_eval IRCastOp.sext ir_br_tu32 ir_ni_tusize (IRScalar.int_ 2147483647)) (IRStepResult.value (IRScalar.int_ 2147483647)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 2147483647))";
const SRC_W_SEXT_AT_SIGN: &str = "def ir_ni_sext_diverges_at_the_sign_bit : Eq IRStepResult (ir_cast_eval IRCastOp.sext ir_br_tu32 ir_ni_tusize (IRScalar.int_ 2147483648)) (IRStepResult.value (IRScalar.int_ 18446744071562067968)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 18446744071562067968))";
const SRC_W_JUNK_TAIL: &str = "def ir_ni_w_junk_tail : Eq IROutcome (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (IRScalar.aggv (ir_sp2 (IRScalar.int_ 7) IRScalar.undef_))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 7))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 7)))";
const SRC_W_NOT_AGG: &str = "def ir_ni_w_scalar_receiver_faults : Eq IROutcome (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (IRScalar.int_ 7)) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_agg) := Eq.refl IROutcome (IROutcome.type_error IRFault.not_agg)";
const SRC_W_BAD_FIELD: &str = "def ir_ni_w_empty_spine_faults : Eq IROutcome (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (IRScalar.aggv ir_sp0)) ir_mem0 ir_d0) (IROutcome.type_error IRFault.bad_field) := Eq.refl IROutcome (IROutcome.type_error IRFault.bad_field)";
const SRC_W_CORRECT: &str = "def ir_ni_correct_witness (n : Nat) : Eq IROutcome (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (ir_ni_val n)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ (cert_node_id_index (NodeIdR.mk n))))) := ir_ni_correct ir_mem0 ir_d3 ir_d0 (ir_ni_val n) (NodeIdR.mk n) (EncodesNodeId.mk n ir_sp0) (Le.refl ir_d3)";
const SRC_W_SOUND: &str = "def ir_ni_machine_sound_witness : Eq Nat (cert_node_id_index (NodeIdR.mk 4294967295)) 4294967295 := ir_ni_machine_sound ir_mem0 ir_d3 ir_d0 (ir_ni_val 4294967295) (NodeIdR.mk 4294967295) 4294967295 (EncodesNodeId.mk 4294967295 ir_sp0) (Le.refl ir_d3) ir_ni_w_u32max_survives";
const SRC_W_LOW_WORD: &str = "def ir_ni_low_word_decides_witness : Eq IROutcome (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ 7) ir_sp0))) ir_mem0 ir_d0) (ir_eval ir_d3 ir_ni_module ir_d0 (ir_vl1 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ 4294967303) (ir_sp1 IRScalar.undef_)))) ir_mem0 ir_d0) := ir_ni_low_word_decides ir_mem0 ir_d3 ir_d0 ir_sp0 (ir_sp1 IRScalar.undef_) 7 4294967303 (Le.refl ir_d3) (Eq.refl Nat 7)";

impl Specification {
    /// Register the zext chain: `cert::builder::state::NodeId::index`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_node_id_index(&mut self) -> Result<(), SpecError> {
        self.add_inductive(SRC_NODEIDR, "NodeIdR: the reflected NodeId (cert/builder/state.rs:19) -- a NEWTYPE over u32, one constructor carrying one Nat. A wrapper rather than a bare Nat because the Rust type is a struct and the emitted body reads FIELD 0 of an aggregate; a bare Nat would make the representation relation lie about the shape the machine destructures. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_NODE_ID_BITS,
            "node_id_bits: the newtype projection, by NodeIdR.rec. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_CERT_NODE_ID_INDEX, "cert_node_id_index: the reflected NodeId::index (cert/builder/state.rs:26), which is `self.0 as usize`. It is ir_wrap ir_d64 (ir_wrap ir_d32 n) -- the machine's exact zext arithmetic, canonicalize at the source width then embed at the 64-bit `usize` width -- and NOT a proof that Rust's `as usize` is that function; that gap is the same shape as every chain's. The outer wrap is kept because dropping it needs a wrap-idempotence lemma nobody has earned; on a canonical u32 it is the identity, EXECUTED at 0, 1, 2^31 and 2^32-1 rather than proved in general. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESNODEID, "EncodesNodeId v i: the runtime VALUE v represents the NodeId i. By value, not through the heap -- the emitted body takes `self` by value and performs NO load, so this premise mentions no memory. Spine-agnostic past slot 0, deliberately: the body reads field 0 and nothing else, so `rest` is universally quantified and ir_ni_w_junk_tail runs the machine with IRScalar.undef_ in slot 1 to show the weakness is real. SAME OPEN LAYOUT OBLIGATION as every chain: `NodeId(u32)` being an aggregate with the integer at slot 0 is a producer layout fact, not proved here. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ENCODES_NODE_ID_INHABITED, "encodes_node_id_inhabited: the premise-satisfiability witness, registered BESIDE the relation -- a definition that CONCLUDES EncodesNodeId, so the premise-witness ratchet sees the premise is inhabited without a baseline change. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_TUSIZE, "ir_ni_tusize: *** THE usize DECISION -- A TARGET ASSUMPTION, MADE ONCE AND LOUDLY. *** `usize` resolved to IRTy.uint_ ir_d64. The ninth chain left `?usize` refused in the CFG type lane precisely so this chain would have to decide; the recorded producer is the aarch64-apple-darwin stage1 trustc (64-bit, pinned in the lineage fixture and asserted by the gate). On a 32-bit target the emitted body would be a different function and this module would NOT be its transcription. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_TSELF, "ir_ni_tself: struct.323, the struct id the emitted body names in `bb0(%0: struct.323)`. Transcribed for fidelity; the value-addressed semantics never consults it. It is ALSO what distinguishes this body from its unchained twin ExtensionIdx::index (struct.848). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_B0, "ir_ni_b0: THE WHOLE BODY, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/node_id_index.trust-ir.txt). Read self.0 (field 0, at u32) into %1, zero-extend %1 from u32 to `usize` into %2, return %2. Every token is a CFG lane: the field index, the extractfield type, the cast opcode (sext at the top half of the range is a DIFFERENT function -- executed below), both cast widths (the emitted destination is `usize`, resolved by ir_ni_tusize), the operand, and the returned id. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_FUNC, "ir_ni_func: NodeId::index as EvalIR -- ONE parameter (%0, self by value), entry block 0, one block. No closure environment: unlike the eighth and ninth chains this is a plain method, not a closure. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_MODULE, "ir_ni_module: the module for cert::builder::state::NodeId::index, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel, recorded at tests/fixtures/node_id_index.trust-ir.txt and checked lane for lane by tests/crystal_a1_lineage/node_id_index.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_VAL, "ir_ni_val: the runtime value of a NodeId -- a one-field aggregate carrying the u32. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_MACH0, "ir_ni_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds ONE parameter positionally. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_EXACT, "ir_ni_exact: the machine agrees with the reflected function at EXACTLY 3 steps, for every bit pattern x, every payload tail, every heap and every next-address counter. One Eq.refl, and affordable for the same measured reason as the fourth chain's: ir_ef_at destructures the SCALAR CONSTRUCTORS, not the Nat payload, and the zext result is IRStepResult.value immediately, so the whole body computes symbolically -- the residue ir_wrap ir_d64 (ir_wrap ir_d32 x) stays an UNREDUCED application on both sides and the kernel never computes it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_CORRECT, "ir_ni_correct: *** THE EQUALITY THEOREM (A4), OVER THE EMITTED SHAPE, FOR THE zext LANE. *** For every NodeIdR, every aggregate value representing it (any tail), every heap, every next-address counter and every fuel at or above 3, ir_eval on ir_ni_module returns exactly IROutcome.ret [int_ (cert_node_id_index i)]. \n\nA0 is measured on the SHIPPED kernel (2026-08-20 dump, trustc 10130575c): lowered, spliced, unsupported [], derived_mir.verdict agreed (4 canonical lines identical), markers_exact TRUE over TWO REAL MARKER LINES, zero calls, and a codegen flip event whose lineage equals the coverage row's. THE PRODUCER'S INTERPRETER DIFFERENTIAL IS NOT-RUN ON THIS BODY (0 samples) AND NOTHING HERE CLAIMS IT. A1 is gated by tests/crystal_a1_lineage/node_id_index.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_MACHINE_SOUND, "ir_ni_machine_sound: *** A5, THE INVERSION. *** If the MACHINE running the emitted body answers k, then the reflected function's value IS k -- for every k, not for a chosen one. Goes through A4 rather than restating it, reading the answer back with ir_outcome_nat (second chain, reused). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_NEVER_FAULTS, "ir_ni_never_faults: *** NO UB, NO TYPE ERROR, NO STUCK STATE, NO EXHAUSTION -- on any represented NodeId. *** A corollary of A4: the extractfield never faults not_agg or bad_field, the zext never faults (32 <= 64, so the width guard passes and a zero extension is TOTAL on integers), and 3 steps always suffice. Earned by EncodesNodeId's premise -- the two fail-closed witnesses below show what happens without it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_LOW_WORD_DECIDES, "ir_ni_low_word_decides: *** A5 REACHING PAST THE MACHINE'S ANSWER, ONTO THE ARGUMENTS. *** If two stored patterns have equal reflected values, the SHIPPED body's outcome on them is identical -- with DIFFERENT payload tails on the two sides, so it is simultaneously the executable form of tail-agnosticism. For canonical u32 patterns the premise is just equality; the collapse of NON-canonical partners (7 and 2^32+7, which no real NodeId can hold -- its field is a u32 -- but which the total model must answer on) is discharged CONCRETELY by Eq.refl at the witness, the kernel deciding both residues. The general below-2^32 identity law is deliberately NOT proved (it needs ir_nat_rem lemmas nobody has earned). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_ZEXT_SEMANTICS, "ir_ni_zext_semantics: the cast instruction's semantics at THIS chain's exact opcode and widths, for every operand -- canonicalize at the SOURCE width, embed at the 64-bit destination. Registered at ir_ni_tusize so the usize decision is IN the theorem, not beside it; ir_gc_zext_is_an_embedding (ninth chain) states the same computation at the ir_vc_tu64 spelling. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_SEXT_SEMANTICS, "ir_ni_sext_semantics: *** THE OPCODE IS SEMANTIC -- the general half. *** sext at the same widths computes ir_sext_value: identical to zext below the sign bit, larger by 2^64 - 2^32 at and above it. The two opcodes agree on HALF the range, so no single execution can separate them below the sign bit -- which is why the boundary is pinned by THREE executed witnesses (2^31 - 1 agrees, 2^31 and 2^32 - 1 differ) and why the CFG casts lane carries the opcode token. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_NARROWER_DEST_FAULTS, "ir_ni_narrower_dest_is_a_fault: *** THE DESTINATION WIDTH DECIDES FAULT VERSUS VALUE for a zero extension. *** zext requires sw <= dw, so zext u32 -> u8 is ir_width_fault for EVERY scalar where the chain's own zext u32 -> usize answers. The mirror of the ninth chain's source-width theorem: for trunc the SOURCE carries the guard, for zext the DESTINATION does. (The reversed direction, zext u64 -> u32, is already ir_gc_opcode_is_semantic.) DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_SOURCE_WIDTH, "ir_ni_source_width_is_the_canonicalizer: the SOURCE width decides the value -- zext u8 -> usize computes ir_wrap ir_d8 where the chain's instruction computes ir_wrap ir_d32, so at operand 256 they answer 0 and 256. Different functions of the same operand, which is why cast_tys carries the source independently of the destination. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_NI_NOT_INT, "ir_ni_non_integer_operand_is_a_type_error: FAIL-CLOSED. A Bool at the chain's integer cast is IROutcome.type_error IRFault.not_int -- not a silent 0/1. ir_int1 declines IRScalar.bool_, which is why EncodesNodeId's int_-at-slot-0 shape is load-bearing. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ZERO, "CONCRETE EXECUTION WITNESS -- 0 survives. The kernel runs the emitted module for three steps and returns the value unchanged. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_W_ONE,
            "CONCRETE EXECUTION WITNESS -- 1 survives. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_W_MID, "CONCRETE EXECUTION WITNESS -- 2^31, the mid-range pattern whose TOP BIT IS SET, survives unchanged: a zero extension ignores the sign bit exactly where ir_ni_sext_diverges_at_the_sign_bit shows a sign extension does not. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_U32MAX, "*** CONCRETE EXECUTION WITNESS -- u32::MAX. THE WITNESS THE CHAIN IS FOR: *** 2^32 - 1 zero-extends to ITSELF, where a sign extension of the same bit pattern is 2^64 - 1 (executed next to it). A transcription that swapped the opcode would be separated by exactly this input class, and by nothing below the sign bit. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_2P32, "CONCRETE EXECUTION WITNESS -- 2^32, a NON-CANONICAL pattern (a real NodeId field is a u32 and cannot hold it), wraps at the SOURCE width and returns 0: the model is total and answers with the canonical residue, stated rather than hidden. Pinned against u32::MAX from the other side of the boundary. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_COLLAPSE, "CONCRETE EXECUTION WITNESS -- TWO NON-CANONICALLY-RELATED PATTERNS, ONE OUTCOME: 7 and 2^32 + 7 produce the SAME IROutcome by Eq.refl, the kernel evaluating both runs. The instance that inhabits ir_ni_low_word_decides' premise with a genuinely distinct pair. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_SEXT_U32MAX, "*** CONTRAST WITNESS -- THE OTHER OPCODE, EXECUTED AT THE CHAIN'S KEY INPUT. *** sext of the u32::MAX pattern at the same widths is 18446744073709551615 (all 64 bits set), where the shipped zext answers 4294967295. The kernel computes both; `the opcode is semantic` is an executed pair, not a sentence. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_SEXT_BELOW, "CONTRAST WITNESS -- sext AGREES with zext at 2^31 - 1, the largest value below the sign bit. The boundary's lower side: an opcode swap is INVISIBLE to execution here, which is why the CFG lane carries the token. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_SEXT_AT_SIGN, "CONTRAST WITNESS -- sext DIVERGES at exactly 2^31: 18446744071562067968 (= 2^64 - 2^32 + 2^31), against the zext witness at the same input returning it unchanged. The boundary pinned from both sides. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_JUNK_TAIL, "CONCRETE WITNESS -- the aggregate carries IRScalar.undef_ in slot 1 and the machine still answers: the executable form of EncodesNodeId's spine-agnosticism. The body provably never reads past field 0. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_NOT_AGG, "FAIL-CLOSED WITNESS -- a bare integer where the struct should be is IROutcome.type_error IRFault.not_agg: ir_ef_at refuses a non-aggregate receiver. EncodesNodeId cannot be weakened to `the argument arrived somehow`. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_BAD_FIELD, "FAIL-CLOSED WITNESS -- an EMPTY aggregate spine is IROutcome.type_error IRFault.bad_field: field 0 must exist, so the vcons head in EncodesNodeId is load-bearing too. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_CORRECT, "ir_ni_correct_witness: A4's premises are all SATISFIABLE, discharged concretely -- the empty heap, the exact fuel bound by Le.refl, one EncodesNodeId.mk. The bit pattern stays universally quantified. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_SOUND, "ir_ni_machine_sound_witness: A5 is not vacuous, and its observation premise is an EXECUTION rather than an assumption -- the u32::MAX run. The conclusion is the reflected-value equation, decided by the kernel. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_LOW_WORD, "ir_ni_low_word_decides_witness: the argument-reaching A5's premises are SATISFIABLE at a pair that genuinely differs -- 7 with an empty tail against 2^32 + 7 with an undef-bearing tail -- with the value equality discharged by Eq.refl, the kernel computing both residues. Nothing here is supposed. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The whole body: one typed field read, one `zext` of its result at the
    /// resolved `usize` type, and a `ret` of the extension — not the argument.
    #[test]
    fn test_the_body_is_a_field_read_a_zext_and_a_ret_of_its_result() {
        assert!(SRC_IR_NI_B0.contains("IRInst.extractfield ir_br_tu32 ir_d0 ir_d0) ir_d1"));
        assert!(
            SRC_IR_NI_B0.contains("IRInst.cast IRCastOp.zext ir_br_tu32 ir_ni_tusize ir_d1) ir_d2")
        );
        assert!(SRC_IR_NI_B0.contains("IRInst.ret (ir_nl1 ir_d2)"));
        assert!(
            !SRC_IR_NI_B0.contains("IRInst.ret (ir_nl1 ir_d1)"),
            "it returns the EXTENDED value, not the raw field"
        );
        assert!(
            !SRC_IR_NI_B0.contains("condbr")
                && !SRC_IR_NI_B0.contains("switch")
                && !SRC_IR_NI_B0.contains("IRInst.br ")
                && !SRC_IR_NI_B0.contains("IRConst"),
            "one block, no control flow, no constant"
        );
    }

    /// The usize decision is a single named alias at 64 bits, and every other
    /// type name in the transcription is REUSED, not re-declared.
    #[test]
    fn test_the_usize_decision_is_one_named_64_bit_alias() {
        assert_eq!(
            SRC_IR_NI_TUSIZE,
            "def ir_ni_tusize : IRTy := IRTy.uint_ ir_d64"
        );
        assert!(SRC_IR_NI_B0.contains("ir_br_tu32 ir_ni_tusize"));
        assert!(
            !SRC_IR_NI_B0.contains("ir_ni_tusize ir_br_tu32"),
            "source then destination — the reverse is a narrowing, which faults"
        );
        for src in [
            SRC_IR_NI_B0,
            SRC_IR_NI_FUNC,
            SRC_IR_NI_MODULE,
            SRC_IR_NI_MACH0,
        ] {
            assert!(
                !src.contains("def ir_br_tu32")
                    && !src.contains("def ir_d32")
                    && !src.contains("def ir_d64")
                    && !src.contains("def ir_tU8"),
                "a name that already exists is a name to REUSE: {src}"
            );
        }
    }

    /// A4 is universally quantified — pattern, tail, heap, counter — with the
    /// fuel bound at exactly 3, and consumes its one representation premise.
    #[test]
    fn test_a4_quantifies_over_every_pattern_tail_and_heap() {
        let statement = SRC_IR_NI_CORRECT.split(":=").next().unwrap_or("");
        assert!(statement.contains("(i : NodeIdR)"));
        assert!(statement.contains("(mem : IRList IRMemSlot)"));
        assert!(statement.contains("Le ir_d3 fuel ->"));
        assert!(statement.contains("(cert_node_id_index i)"));
        assert!(
            !statement.contains("ir_mem0") && !statement.contains("NodeIdR.mk"),
            "a concrete heap or a concrete NodeId would make this a witness, not a theorem"
        );
        assert_eq!(
            SRC_IR_NI_CORRECT.matches("EncodesNodeId.rec").count(),
            1,
            "one recursor for the one parameter"
        );
        assert!(SRC_IR_NI_CORRECT.contains("ir_run_le_ret"));
        // …and the exact lemma stays symbolic in the pattern AND the tail.
        let exact = SRC_IR_NI_EXACT.split(":=").next().unwrap_or("");
        assert!(exact.contains("(x : Nat)") && exact.contains("(px : IRScalar)"));
    }

    /// The opcode contrast is a general theorem PLUS a three-witness boundary:
    /// agree below the sign bit, diverge at it and at the top.
    #[test]
    fn test_the_sext_contrast_pins_the_boundary_from_both_sides() {
        assert!(SRC_IR_NI_SEXT_SEMANTICS.contains("ir_sext_value ir_d32 ir_d64 n"));
        assert!(SRC_W_SEXT_BELOW.contains("2147483647"));
        assert!(SRC_W_SEXT_BELOW.contains("(IRScalar.int_ 2147483647)"));
        assert!(SRC_W_SEXT_AT_SIGN.contains("2147483648"));
        assert!(SRC_W_SEXT_AT_SIGN.contains("18446744071562067968"));
        assert!(SRC_W_SEXT_U32MAX.contains("4294967295"));
        assert!(SRC_W_SEXT_U32MAX.contains("18446744073709551615"));
        // …and the shipped opcode keeps all three unchanged.
        assert!(SRC_W_MID.contains("(IRScalar.int_ 2147483648)"));
        assert!(SRC_W_U32MAX.contains("(IRScalar.int_ 4294967295)"));
        // The width guards, each a fault for EVERY scalar.
        assert!(SRC_IR_NI_NARROWER_DEST_FAULTS.contains("(a : IRScalar)"));
        assert!(SRC_IR_NI_NARROWER_DEST_FAULTS.contains("ir_width_fault"));
        assert!(SRC_IR_NI_SOURCE_WIDTH.contains("ir_wrap ir_d8 n"));
    }

    /// Every execution witness runs the machine at exactly 3 steps over the
    /// pinned module, and the fail-closed ones are tagged faults.
    #[test]
    fn test_witnesses_execute_and_the_negative_ones_fault() {
        for src in [
            SRC_W_ZERO,
            SRC_W_ONE,
            SRC_W_MID,
            SRC_W_U32MAX,
            SRC_W_2P32,
            SRC_W_COLLAPSE,
            SRC_W_JUNK_TAIL,
        ] {
            assert!(src.contains("ir_eval ir_d3 ir_ni_module"));
            assert!(src.contains(":= Eq.refl IROutcome"));
        }
        assert!(SRC_W_NOT_AGG.contains("IROutcome.type_error IRFault.not_agg"));
        assert!(SRC_W_BAD_FIELD.contains("IROutcome.type_error IRFault.bad_field"));
        assert!(SRC_IR_NI_NOT_INT.contains("IROutcome.type_error IRFault.not_int"));
        // A5's argument-reaching form uses DIFFERENT tails on the two sides.
        assert!(SRC_W_LOW_WORD.contains("ir_sp0 (ir_sp1 IRScalar.undef_)"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [
            SRC_NODEIDR,
            SRC_NODE_ID_BITS,
            SRC_CERT_NODE_ID_INDEX,
            SRC_ENCODESNODEID,
            SRC_ENCODES_NODE_ID_INHABITED,
            SRC_IR_NI_TUSIZE,
            SRC_IR_NI_TSELF,
            SRC_IR_NI_B0,
            SRC_IR_NI_FUNC,
            SRC_IR_NI_MODULE,
            SRC_IR_NI_VAL,
            SRC_IR_NI_MACH0,
            SRC_IR_NI_EXACT,
            SRC_IR_NI_CORRECT,
            SRC_IR_NI_MACHINE_SOUND,
            SRC_IR_NI_NEVER_FAULTS,
            SRC_IR_NI_LOW_WORD_DECIDES,
            SRC_IR_NI_ZEXT_SEMANTICS,
            SRC_IR_NI_SEXT_SEMANTICS,
            SRC_IR_NI_NARROWER_DEST_FAULTS,
            SRC_IR_NI_SOURCE_WIDTH,
            SRC_IR_NI_NOT_INT,
            SRC_W_ZERO,
            SRC_W_ONE,
            SRC_W_MID,
            SRC_W_U32MAX,
            SRC_W_2P32,
            SRC_W_COLLAPSE,
            SRC_W_SEXT_U32MAX,
            SRC_W_SEXT_BELOW,
            SRC_W_SEXT_AT_SIGN,
            SRC_W_JUNK_TAIL,
            SRC_W_NOT_AGG,
            SRC_W_BAD_FIELD,
            SRC_W_CORRECT,
            SRC_W_SOUND,
            SRC_W_LOW_WORD,
        ] {
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
