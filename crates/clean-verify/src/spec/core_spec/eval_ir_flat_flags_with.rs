// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The WITH chain — `flat::types::FlatFlags::with`, the sibling of the
//! chained `FlatFlags::contains`, and the first chain whose returned aggregate
//! is BUILT rather than materialized whole.**
//!
//! ```text
//! pub const fn with(self, other: FlatFlags) -> Self {
//!     FlatFlags(self.0 | other.0)
//! }
//! ```
//!
//! ```text
//! bb0(%0: struct.1017, %1: struct.1017):
//!     %2 = extractfield u8 %0, 0
//!     %3 = extractfield u8 %1, 0
//!     %4 = or u8 %2, %3
//!     %5 = const struct.1017 { 0 }
//!     %6 = insertfield struct.1017 %5, 0, %4
//!     ret %6
//! }
//! ```
//!
//! Six instructions, one block, two parameters — `contains`' graph with the
//! `icmp` half replaced by a WRITE half. That replacement is what this chain
//! buys: `or`, `const <struct>` and `insertfield` were each in NO chained body
//! before it (measured in the 177-body operator census: `or` appears exactly
//! once, and the two write lanes landed in `emitted_cfg.rs` ahead of this
//! chain, with their discrimination proofs in `lane_matrix_writes.rs`). Every
//! earlier chain returns a scalar or a constant materialized in one piece;
//! this body materializes a one-field TEMPLATE (`const struct.1017 { 0 }`) and
//! writes a COMPUTED value into slot 0 of it. The returned spine is therefore
//! the template's, not either argument's — `ir_fw_on_junk_tail` executes that:
//! junk-tailed inputs, clean-tailed output.
//!
//! ## What is proved
//!
//! For EVERY pair of flag sets, every pair of values representing them
//! (payload tails free), every heap, every next-address counter and every fuel
//! at or above 6, the machine running the EMITTED module returns exactly the
//! one-field aggregate carrying `flat_flags_bits (flat_flags_with a b)`
//! (`ir_fw_correct`); if the machine answers the aggregate carrying `k`, then
//! `flat_flags_with a b` IS `FlatFlagsR.mk k` (`ir_fw_machine_sound`,
//! `ir_fw_machine_sound_flags`); on any represented pair it never faults and
//! never exhausts fuel (`ir_fw_never_faults`); and the value it returns
//! re-satisfies the representation premise (`ir_fw_ret_encodes`), which is
//! what lets `ir_fw_then_contains` feed it STRAIGHT INTO the chained
//! `contains` module's A4 — a two-body composition at the theorem level, with
//! the concrete `contains (with 0x01 0x02) 0x02 = true` run by the kernel in
//! `ir_fw_then_contains_witness`.
//!
//! Both A4 and A5 are at FULL symbolic strength (the `float_div` shape, not
//! the `float_add` split): `ir_fw_exact` is ONE `Eq.refl` over symbolic byte
//! payloads. Measured, not assumed — the whole body destructures scalar
//! CONSTRUCTORS only, so the `or`'s answer rides through `insertfield` as a
//! stuck `ir_nat_bitop` term and no case split is needed anywhere.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! * The reflected `flat_flags_with` is stated in the machine's own width-8
//!   vocabulary (`ir_nat_bitop Bool.or ir_d8`), exactly as its sibling
//!   `flat_flags_contains` is. It is a refinement of the EMITTED body against
//!   a `u8`-level specification, not an abstract set-union theorem. In
//!   particular `contains (with a b) b = Bool.true` is NOT proved universally
//!   — it needs `(x|y) & y = y` over `ir_nat_bitop_go`, which this program has
//!   not earned; it appears here only as a kernel-EXECUTED concrete witness.
//!   Commutativity likewise: executed both ways on concrete bytes, proved for
//!   neither operand order in general.
//! * **The producer's interpreter differential is NOT-RUN on this body — 0
//!   samples** (recorded in `tests/fixtures/flat_flags_with.lineage.json`).
//!   Unlike the float closures' agreed/64, NOTHING here claims interpreter
//!   agreement. The A0/A6 evidence is: derived-MIR `agreed`, `markers_exact`
//!   over 6 real marker lines, a codegen flip whose lineage equals the
//!   coverage row's, three byte-identical clean builds — plus the
//!   kernel-executed witnesses in this module. That list is exhaustive.
//! * The link between the proved module and the emitted one is STRUCTURAL —
//!   `tests/crystal_a1_lineage/flat_flags_with.rs` — and this module is
//!   hand-transcribed, not minted. The same open LAYOUT obligation as the
//!   sibling chain applies: that `FlatFlags(u8)`'s trust-ir value carries the
//!   byte at spine slot 0 is a producer fact, not proved here; a stored
//!   payload above 255 is outside that contract, and `ir_fw_on_width_wrap`
//!   shows both sides then agree on the width-8 residue rather than on the
//!   Rust value. Everything past the flip seam is downstream and covered by
//!   nothing here. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// Shared names deliberately REUSED, not re-declared (the eighth chain's one
// real error): `FlatFlagsR` / `flat_flags_bits` / `flat_flags_contains` /
// `EncodesFlatFlags` / `ir_vl2` / `ir_fc_tflags` / `ir_fc_val` / `ir_fc_module`
// / `ir_fc_correct` from `add_eval_ir_contains`; `ir_run_le_ret` from
// `add_eval_ir_fuel`; `ir_outcome_is_ret` from `add_eval_ir_correct`;
// `ir_outcome_disc` from `add_eval_ir_from_source`; `ir_cvar` / `ir_tU8` /
// numerals from `add_eval_ir`. This stage must therefore run AFTER
// `add_eval_ir_contains` (and transitively after the four stages above it).

// ── the reflected function ────────────────────────────────────────────
const SRC_FLAT_FLAGS_WITH: &str = "def flat_flags_with (a : FlatFlagsR) (b : FlatFlagsR) : FlatFlagsR := FlatFlagsR.mk (ir_nat_bitop Bool.or ir_d8 (flat_flags_bits a) (flat_flags_bits b))";

// ── the emitted module, transcribed ───────────────────────────────────
const SRC_IR_FW_B0: &str = "def ir_fw_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd6 (ir_nd1 (IRInst.extractfield ir_tU8 ir_d0 ir_d0) ir_d2) (ir_nd1 (IRInst.extractfield ir_tU8 ir_d1 ir_d0) ir_d3) (ir_nd1 (IRInst.binop IRBinOp.or_ ir_tU8 ir_d2 ir_d3) ir_d4) (ir_nd1 (IRInst.const_ ir_fc_tflags (ir_cvar ir_d0)) ir_d5) (ir_nd1 (IRInst.insertfield ir_fc_tflags ir_d5 ir_d0 ir_d4) ir_d6) (ir_nd (IRInst.ret (ir_nl1 ir_d6))))";

const SRC_IR_FW_FUNC: &str = "def ir_fw_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_fw_b0 ir_blk0)";

const SRC_IR_FW_MODULE: &str = "def ir_fw_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_fw_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

// ── the machine and the symbolic execution ────────────────────────────
const SRC_IR_FW_MACH0: &str = "def ir_fw_mach0 (u : IRScalar) (v : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl2 ir_d0 ir_d1) (ir_vl2 u v) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_IR_FW_EXACT: &str = "def ir_fw_exact (mem : IRList IRMemSlot) (na : Nat) (x : Nat) (y : Nat) (px : IRScalar) (py : IRScalar) : Eq IROutcome (ir_run ir_d6 ir_fw_module (IRConfig.running (ir_fw_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ x) px)) (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ y) py)) mem na))) (IROutcome.ret (ir_vl1 (ir_fc_val (flat_flags_bits (flat_flags_with (FlatFlagsR.mk x) (FlatFlagsR.mk y)))))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_fc_val (flat_flags_bits (flat_flags_with (FlatFlagsR.mk x) (FlatFlagsR.mk y))))))";

// ── A4, A5, and the corollaries ───────────────────────────────────────
const SRC_IR_FW_CORRECT: &str = "def ir_fw_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (u : IRScalar) (v : IRScalar) (a : FlatFlagsR) (b : FlatFlagsR) (hu : EncodesFlatFlags u a) (hv : EncodesFlatFlags v b) : Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_fw_module ir_d0 (ir_vl2 u v) mem na) (IROutcome.ret (ir_vl1 (ir_fc_val (flat_flags_bits (flat_flags_with a b))))) := EncodesFlatFlags.rec (fun (u0 : IRScalar) (a0 : FlatFlagsR) (_ : EncodesFlatFlags u0 a0) => forall (v0 : IRScalar) (b0 : FlatFlagsR), EncodesFlatFlags v0 b0 -> Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_fw_module ir_d0 (ir_vl2 u0 v0) mem na) (IROutcome.ret (ir_vl1 (ir_fc_val (flat_flags_bits (flat_flags_with a0 b0)))))) (fun (n : Nat) (px : IRScalar) => fun (v0 : IRScalar) (b0 : FlatFlagsR) (hv0 : EncodesFlatFlags v0 b0) => EncodesFlatFlags.rec (fun (v1 : IRScalar) (b1 : FlatFlagsR) (_ : EncodesFlatFlags v1 b1) => Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_fw_module ir_d0 (ir_vl2 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n) px)) v1) mem na) (IROutcome.ret (ir_vl1 (ir_fc_val (flat_flags_bits (flat_flags_with (FlatFlagsR.mk n) b1)))))) (fun (m : Nat) (py : IRScalar) (hle : Le ir_d6 fuel) => ir_run_le_ret ir_fw_module ir_d6 fuel hle (IRConfig.running (ir_fw_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n) px)) (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ m) py)) mem na)) (ir_vl1 (ir_fc_val (flat_flags_bits (flat_flags_with (FlatFlagsR.mk n) (FlatFlagsR.mk m))))) (ir_fw_exact mem na n m px py)) v0 b0 hv0) u a hu v b hv";

const SRC_IR_FW_MACHINE_SOUND: &str = "def ir_fw_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (u : IRScalar) (v : IRScalar) (a : FlatFlagsR) (b : FlatFlagsR) (k : Nat) (hu : EncodesFlatFlags u a) (hv : EncodesFlatFlags v b) (hle : Le ir_d6 fuel) (hret : Eq IROutcome (ir_eval fuel ir_fw_module ir_d0 (ir_vl2 u v) mem na) (IROutcome.ret (ir_vl1 (ir_fc_val k)))) : Eq Nat (flat_flags_bits (flat_flags_with a b)) k := Eq.cong IROutcome Nat ir_outcome_disc (IROutcome.ret (ir_vl1 (ir_fc_val (flat_flags_bits (flat_flags_with a b))))) (IROutcome.ret (ir_vl1 (ir_fc_val k))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (ir_fc_val (flat_flags_bits (flat_flags_with a b))))) (ir_eval fuel ir_fw_module ir_d0 (ir_vl2 u v) mem na) (IROutcome.ret (ir_vl1 (ir_fc_val k))) (Eq.symm IROutcome (ir_eval fuel ir_fw_module ir_d0 (ir_vl2 u v) mem na) (IROutcome.ret (ir_vl1 (ir_fc_val (flat_flags_bits (flat_flags_with a b))))) (ir_fw_correct mem fuel na u v a b hu hv hle)) hret)";

const SRC_IR_FW_MACHINE_SOUND_FLAGS: &str = "def ir_fw_machine_sound_flags (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (u : IRScalar) (v : IRScalar) (a : FlatFlagsR) (b : FlatFlagsR) (k : Nat) (hu : EncodesFlatFlags u a) (hv : EncodesFlatFlags v b) (hle : Le ir_d6 fuel) (hret : Eq IROutcome (ir_eval fuel ir_fw_module ir_d0 (ir_vl2 u v) mem na) (IROutcome.ret (ir_vl1 (ir_fc_val k)))) : Eq FlatFlagsR (flat_flags_with a b) (FlatFlagsR.mk k) := Eq.cong Nat FlatFlagsR (fun (n : Nat) => FlatFlagsR.mk n) (flat_flags_bits (flat_flags_with a b)) k (ir_fw_machine_sound mem fuel na u v a b k hu hv hle hret)";

const SRC_IR_FW_NEVER_FAULTS: &str = "def ir_fw_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (u : IRScalar) (v : IRScalar) (a : FlatFlagsR) (b : FlatFlagsR) (hu : EncodesFlatFlags u a) (hv : EncodesFlatFlags v b) (hle : Le ir_d6 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_fw_module ir_d0 (ir_vl2 u v) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_fw_module ir_d0 (ir_vl2 u v) mem na) (IROutcome.ret (ir_vl1 (ir_fc_val (flat_flags_bits (flat_flags_with a b))))) (ir_fw_correct mem fuel na u v a b hu hv hle)";

// ── the round trip into the SIBLING chain ─────────────────────────────
const SRC_IR_FW_RET_ENCODES: &str = "def ir_fw_ret_encodes (a : FlatFlagsR) (b : FlatFlagsR) : EncodesFlatFlags (ir_fc_val (flat_flags_bits (flat_flags_with a b))) (flat_flags_with a b) := EncodesFlatFlags.mk (ir_nat_bitop Bool.or ir_d8 (flat_flags_bits a) (flat_flags_bits b)) ir_sp0";

const SRC_IR_FW_THEN_CONTAINS: &str = "def ir_fw_then_contains (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (v : IRScalar) (a : FlatFlagsR) (b : FlatFlagsR) (hv : EncodesFlatFlags v b) (hle : Le ir_d6 fuel) : Eq IROutcome (ir_eval fuel ir_fc_module ir_d0 (ir_vl2 (ir_fc_val (flat_flags_bits (flat_flags_with a b))) v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (flat_flags_contains (flat_flags_with a b) b)))) := ir_fc_correct mem fuel na (ir_fc_val (flat_flags_bits (flat_flags_with a b))) v (flat_flags_with a b) b (ir_fw_ret_encodes a b) hv hle";

// ── kernel-EXECUTED witnesses ─────────────────────────────────────────
const SRC_IR_FW_ON_DISJOINT: &str = "def ir_fw_on_disjoint : Eq IROutcome (ir_eval ir_d6 ir_fw_module ir_d0 (ir_vl2 (ir_fc_val ir_d1) (ir_fc_val ir_d2)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_fc_val ir_d3))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_fc_val ir_d3)))";

const SRC_IR_FW_ON_OVERLAP: &str = "def ir_fw_on_overlap : Eq IROutcome (ir_eval ir_d6 ir_fw_module ir_d0 (ir_vl2 (ir_fc_val ir_d10) (ir_fc_val ir_d6)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_fc_val 14))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_fc_val 14)))";

const SRC_IR_FW_ON_IDENTITY: &str = "def ir_fw_on_identity : Eq IROutcome (ir_eval ir_d6 ir_fw_module ir_d0 (ir_vl2 (ir_fc_val ir_d10) (ir_fc_val ir_d0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_fc_val ir_d10))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_fc_val ir_d10)))";

const SRC_IR_FW_ON_SATURATION: &str = "def ir_fw_on_saturation : Eq IROutcome (ir_eval ir_d6 ir_fw_module ir_d0 (ir_vl2 (ir_fc_val ir_d10) (ir_fc_val 255)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_fc_val 255))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_fc_val 255)))";

const SRC_IR_FW_ON_SWAP: &str = "def ir_fw_on_swap : Eq IROutcome (ir_eval ir_d6 ir_fw_module ir_d0 (ir_vl2 (ir_fc_val ir_d2) (ir_fc_val ir_d1)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_fc_val ir_d3))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_fc_val ir_d3)))";

const SRC_IR_FW_ON_JUNK_TAIL: &str = "def ir_fw_on_junk_tail : Eq IROutcome (ir_eval ir_d6 ir_fw_module ir_d0 (ir_vl2 (IRScalar.aggv (ir_sp2 (IRScalar.int_ ir_d10) IRScalar.undef_)) (IRScalar.aggv (ir_sp2 (IRScalar.int_ ir_d2) IRScalar.undef_))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_fc_val ir_d10))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_fc_val ir_d10)))";

const SRC_IR_FW_ON_WIDTH_WRAP: &str = "def ir_fw_on_width_wrap : Eq IROutcome (ir_eval ir_d6 ir_fw_module ir_d0 (ir_vl2 (ir_fc_val 256) (ir_fc_val ir_d1)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_fc_val ir_d1))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_fc_val ir_d1)))";

const SRC_IR_FW_THEN_CONTAINS_WITNESS: &str = "def ir_fw_then_contains_witness : Eq IROutcome (ir_eval ir_d6 ir_fc_module ir_d0 (ir_vl2 (ir_fc_val (flat_flags_bits (flat_flags_with (FlatFlagsR.mk ir_d1) (FlatFlagsR.mk ir_d2)))) (ir_fc_val ir_d2)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";

const SRC_IR_FW_CORRECT_WITNESS: &str = "def ir_fw_correct_witness : Eq IROutcome (ir_eval ir_d6 ir_fw_module ir_d0 (ir_vl2 (ir_fc_val ir_d10) (ir_fc_val ir_d6)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_fc_val (flat_flags_bits (flat_flags_with (FlatFlagsR.mk ir_d10) (FlatFlagsR.mk ir_d6)))))) := ir_fw_correct ir_mem0 ir_d6 ir_d0 (ir_fc_val ir_d10) (ir_fc_val ir_d6) (FlatFlagsR.mk ir_d10) (FlatFlagsR.mk ir_d6) (EncodesFlatFlags.mk ir_d10 ir_sp0) (EncodesFlatFlags.mk ir_d6 ir_sp0) (Le.refl ir_d6)";

const SRC_IR_FW_MACHINE_SOUND_WITNESS: &str = "def ir_fw_machine_sound_witness : Eq Nat (flat_flags_bits (flat_flags_with (FlatFlagsR.mk ir_d1) (FlatFlagsR.mk ir_d2))) ir_d3 := ir_fw_machine_sound ir_mem0 ir_d6 ir_d0 (ir_fc_val ir_d1) (ir_fc_val ir_d2) (FlatFlagsR.mk ir_d1) (FlatFlagsR.mk ir_d2) ir_d3 (EncodesFlatFlags.mk ir_d1 ir_sp0) (EncodesFlatFlags.mk ir_d2 ir_sp0) (Le.refl ir_d6) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_fc_val ir_d3))))";

impl Specification {
    /// Register the WITH chain: `flat::types::FlatFlags::with`, the first
    /// chain whose returned aggregate is BUILT (`or` + `const <struct>` +
    /// `insertfield`) rather than materialized whole.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_flat_flags_with(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_FLAT_FLAGS_WITH, "flat_flags_with: the reflected FlatFlags::with (flat/types.rs) -- `FlatFlags(self.0 | other.0)` at u8, stated in the machine's own width-8 vocabulary: ir_nat_bitop Bool.or ir_d8 is the exact bitwise OR on width-8 residues, exactly as the sibling flat_flags_contains states its AND. The same LIMITATION applies and is named rather than hidden: this is the u8-level specification of the emitted body, not an abstract set-union operation, and no theorem here converts it into one. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_B0, "ir_fw_b0: THE WHOLE BODY, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/flat_flags_with.trust-ir.txt). Read self.0 into %2, read other.0 into %3, OR them into %4, materialize the one-field TEMPLATE struct.1017 { 0 } into %5, write %4 into field 0 of %5 giving %6, return %6. \n\nThe template-then-write shape is the compiler's, not a stylistic choice here: a transcription that skipped the const and 'constructed' the result directly would be a shorter body than the shipped artifact, and the agg_consts + insertfields lanes of tests/crystal_a1_lineage/flat_flags_with.rs are what make it fail. The insertfield's FIELD INDEX and its source/value operands are compared by the write lane that landed ahead of this chain (lane_matrix_writes.rs carries its discrimination proof). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_FUNC, "ir_fw_func: FlatFlags::with as EvalIR -- TWO parameters (self at SSA id 0, other at 1), entry block 0, a single block. Same signature shape as the sibling ir_fc_func. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_MODULE, "ir_fw_module: the module for FlatFlags::with, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel (irdump2, trustc 10130575c, 2026-08-20; three clean non-incremental builds, byte-identical coverage.json), recorded at tests/fixtures/flat_flags_with.trust-ir.txt and checked graph-for-graph AND instruction-for-instruction, including the NEW insertfields write lane, by tests/crystal_a1_lineage/flat_flags_with.rs. \n\nEVIDENCE BOUNDARY, stated where it can be quoted: the producer's interpreter differential is NOT-RUN on this body (0 samples, recorded in the lineage fixture). The chain's evidence is derived-MIR agreed + markers_exact + flip-lineage equality + the kernel-executed witnesses below -- NOT an interpreter differential, and nothing in this module claims one. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_MACH0, "ir_fw_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds TWO parameters positionally, exactly as the sibling ir_fc_mach0 does. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_EXACT, "ir_fw_exact: the machine agrees with the reflected `with` at EXACTLY 6 steps, for ARBITRARY bytes x and y and ARBITRARY payload tails. Eq.refl -- and that it is Eq.refl at SYMBOLIC x and y is the measured fact that gives this chain the float_div-strength A5 rather than the float_add split: ir_int2, ir_ef_at, ir_const_eval and ir_insert_field destructure SCALAR CONSTRUCTORS, never the Nat payloads, so the or's answer rides through the insertfield as a stuck ir_nat_bitop term and the whole body computes symbolically with no case split anywhere. The returned spine is the TEMPLATE's (ir_sp0-tailed), whatever the argument tails were. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_CORRECT, "ir_fw_correct: *** A4, THE EQUALITY THEOREM, OVER THE EMITTED SHAPE, FOR A BODY THAT BUILDS ITS ANSWER. *** For every pair of flag sets, every pair of values representing them, every heap, every next-address counter and every fuel at or above 6, ir_eval on ir_fw_module returns exactly IROutcome.ret [aggv [int (flat_flags_bits (flat_flags_with a b))]] -- the one-field aggregate carrying the width-8 OR. \n\nProved by EncodesFlatFlags.rec TWICE, nested, one per parameter, exactly as the sibling chain's A4 -- the conclusion differs: contains returns a SCALAR the icmp computed, this returns an AGGREGATE the insertfield BUILT, which is what carries the or / const-struct / insertfield lanes into a chained theorem for the first time. \n\nA0 is measured on the SHIPPED kernel (fixture flat_flags_with.lineage.json): lowered, spliced, unsupported [], derived_mir agreed (5 canonical lines identical), markers_exact TRUE over SIX REAL MARKER LINES, zero calls, codegen flip with flip-lineage == coverage-row lineage, three byte-identical clean builds. The interpreter differential is NOT-RUN (0 samples) and is NOT part of this claim. A1 is gated by tests/crystal_a1_lineage/flat_flags_with.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_MACHINE_SOUND, "ir_fw_machine_sound: *** A5, THE INVERSION, AT FULL SYMBOLIC STRENGTH. *** If the MACHINE running the emitted body returns the one-field aggregate carrying k, then flat_flags_bits (flat_flags_with a b) IS k -- for every k, not a chosen one. Goes through A4 and ir_outcome_disc (the slot-0 reader the from_source chain registered) rather than restating the computation: apply the projection to both sides with Eq.cong and let the kernel compute. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_MACHINE_SOUND_FLAGS, "ir_fw_machine_sound_flags: A5 lifted to the FLAG-SET level: the machine's answer k determines the reflected result as a FlatFlagsR -- flat_flags_with a b = FlatFlagsR.mk k. One Eq.cong over the constructor; definitional because flat_flags_with is itself a constructor application. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_NEVER_FAULTS, "ir_fw_never_faults: *** NO UB, NO PANIC, NO EXHAUSTION -- on any represented pair. *** A corollary of A4. Concretely for this body: the two extractfields never fault not_agg or bad_field, the OR never faults not_int, the const never faults not_agg (the template type is the struct the constant is built at), the insertfield never faults bad_field (slot 0 of a one-field template is in bounds), and 6 steps always suffice. Earned by EncodesFlatFlags's premise, not assumed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_RET_ENCODES, "ir_fw_ret_encodes: *** THE ROUND TRIP. *** The value A4 says the machine returns SATISFIES the representation premise for the reflected result -- EncodesFlatFlags (ir_fc_val (flat_flags_bits (flat_flags_with a b))) (flat_flags_with a b), by one constructor application, definitionally. This is the fact that makes the chain COMPOSABLE: with's output is admissible input to any theorem stated over EncodesFlatFlags, including the sibling chain's A4. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_THEN_CONTAINS, "ir_fw_then_contains: *** TWO EMITTED BODIES COMPOSED AT THE THEOREM LEVEL. *** Feed the value the WITH machine returns straight into the CONTAINS machine: for every a and b, every value representing b, every heap and every fuel at or above 6, ir_eval on ir_fc_module at (with's answer, b) returns exactly bool (flat_flags_contains (flat_flags_with a b) b). Discharged by the sibling's ir_fc_correct with ir_fw_ret_encodes as the first representation premise -- no new machine reasoning at all. \n\nHONESTY BOUNDARY: this does NOT prove the Bool is true. contains (with a b) b = Bool.true universally needs (x|y)&y = y over ir_nat_bitop_go, a bitwise-absorption lemma this program has not earned; the true-ness appears only as the kernel-EXECUTED concrete witness ir_fw_then_contains_witness. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_ON_DISJOINT, "GATE WITNESS: a DISJOINT pair -- 0x01 | 0x02 = 0x03. The kernel runs the emitted body for six steps: two field reads, an OR, a template const, a field WRITE, a return. The answer is not materialized anywhere in the body; it is built. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_ON_OVERLAP, "GATE WITNESS: an OVERLAPPING pair -- 0x0A | 0x06 = 0x0E. The shared bit (0x02) is counted once, which is what distinguishes OR from ADD on the same operands (10 + 6 = 16); a transcription at IRBinOp.add would return 0x10 here and the binops lane would already have refused it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_ON_IDENTITY, "GATE WITNESS: IDENTITY -- 0x0A | 0x00 = 0x0A. The empty flag set is a right identity, executed. (Executed, not proved: the general x|0=x needs bitop lemmas this program has not earned.) DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_ON_SATURATION, "GATE WITNESS: SATURATION -- 0x0A | 0xFF = 0xFF. The full byte absorbs, executed at the top of the u8 range. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_ON_SWAP, "GATE WITNESS: COMMUTATIVITY, EXECUTED BOTH WAYS -- 0x02 | 0x01 = 0x03, the same answer ir_fw_on_disjoint gets in the opposite order. Nothing in this repository proves ir_nat_bitop commutative in general, so execution is NOT what gates the operand order (the binops lane carries (op, result, lhs, rhs) and does); the pair of witnesses records that on these bytes the difference is unobservable, exactly as the float_add chain records its 1+2/2+1 pair. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_ON_JUNK_TAIL, "GATE WITNESS: both input aggregates carry IRScalar.undef_ in slot 1 -- and the machine still answers, with a CLEAN ir_sp0 tail on the output. The executable form of two facts at once: EncodesFlatFlags's spine-agnosticism is genuinely satisfiable (the body provably never reads past field 0 of either input), and the returned spine is the TEMPLATE's, not either argument's -- the junk does not propagate because the const, not the inputs, donates the result's shape. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_ON_WIDTH_WRAP, "GATE WITNESS: the WIDTH-8 BOUNDARY, executed -- a stored payload of 256 ORed with 0x01 answers 0x01, because ir_nat_bitop canonicalizes both operands to their width-8 residues before combining. This is the same open LAYOUT obligation the sibling chain names: nothing here proves a trust-ir FlatFlags value keeps its byte below 256; what IS proved (A4) is that machine and reflected function agree on the residue wherever the payload lands. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_THEN_CONTAINS_WITNESS, "GATE WITNESS: *** THE INTERPLAY, EXECUTED ACROSS TWO EMITTED BODIES. *** contains(with(0x01, 0x02), 0x02) = true: the kernel first computes with's OR (0x03) inside the argument, then runs the CONTAINS module's six steps on it. The concrete half of ir_fw_then_contains, and the only place the true-ness of the containment is claimed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_CORRECT_WITNESS, "ir_fw_correct_witness: A4 is not vacuous -- every premise discharged concretely at the overlapping pair, and the conclusion RUNS the machine. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FW_MACHINE_SOUND_WITNESS, "ir_fw_machine_sound_witness: A5 is not vacuous. Instantiated at the disjoint pair with the observation discharged by Eq.refl, which the kernel discharges by executing the body. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The answer is BUILT: a template constant plus a field write, not a
    /// materialized result and not a scalar return.
    #[test]
    fn test_the_answer_is_built_not_materialized() {
        assert!(SRC_IR_FW_B0.contains("IRInst.binop IRBinOp.or_ ir_tU8 ir_d2 ir_d3"));
        assert!(
            SRC_IR_FW_B0.contains("IRInst.const_ ir_fc_tflags (ir_cvar ir_d0)"),
            "the TEMPLATE: const struct.1017 {{ 0 }}, transcribed as the aggregate constant it is"
        );
        assert!(
            SRC_IR_FW_B0.contains("IRInst.insertfield ir_fc_tflags ir_d5 ir_d0 ir_d4"),
            "the WRITE: field 0 of the template %5 receives the computed %4"
        );
        assert!(
            SRC_IR_FW_B0.contains("IRInst.ret (ir_nl1 ir_d6)"),
            "the body returns the WRITTEN aggregate %6, not the template %5 and not the or %4"
        );
        assert!(
            !SRC_IR_FW_B0.contains("IRInst.icmp") && !SRC_IR_FW_B0.contains("IRInst.load"),
            "no comparison and no load: this is the sibling's graph with the read half swapped \
             for a write half"
        );
        assert!(
            !SRC_IR_FW_B0.contains("IRInst.switch") && !SRC_IR_FW_B0.contains("IRInst.condbr"),
            "straight line: one block, no dispatch"
        );
    }

    /// Both field reads are transcribed with their distinct sources and
    /// distinct result ids.
    #[test]
    fn test_both_field_reads_are_transcribed() {
        assert_eq!(
            SRC_IR_FW_B0.matches("IRInst.extractfield ir_tU8").count(),
            2,
            "self.0 and other.0, one read each"
        );
        assert!(SRC_IR_FW_B0.contains("ir_d0 ir_d0) ir_d2)"));
        assert!(SRC_IR_FW_B0.contains("ir_d1 ir_d0) ir_d3)"));
    }

    /// A4 stays universally quantified over both flag sets, both values, the
    /// heap and the fuel, and consumes BOTH representation premises.
    #[test]
    fn test_a4_shape() {
        let statement = SRC_IR_FW_CORRECT.split(":=").next().unwrap_or("");
        assert!(statement.contains("(a : FlatFlagsR)") && statement.contains("(b : FlatFlagsR)"));
        assert!(statement.contains("(mem : IRList IRMemSlot)"));
        assert!(SRC_IR_FW_CORRECT.contains("Le ir_d6 fuel ->"));
        assert!(SRC_IR_FW_CORRECT.contains("ir_run_le_ret"));
        assert!(
            !statement.contains("FlatFlagsR.mk"),
            "A4's STATEMENT must not name a concrete flag set, or it is a witness"
        );
        assert!(
            !statement.contains("ir_mem0"),
            "a concrete heap would make this a witness, not a theorem"
        );
        assert_eq!(
            SRC_IR_FW_CORRECT.matches("EncodesFlatFlags.rec").count(),
            2,
            "one recursor per parameter; a single one would leave a premise unused"
        );
    }

    /// The symbolic execution is ONE `Eq.refl` — the full-strength A5 shape,
    /// not the split.
    #[test]
    fn test_exact_is_fully_symbolic() {
        assert!(SRC_IR_FW_EXACT.contains("(x : Nat) (y : Nat)"));
        assert!(SRC_IR_FW_EXACT.contains("(px : IRScalar) (py : IRScalar)"));
        assert!(
            SRC_IR_FW_EXACT.contains(":= Eq.refl IROutcome"),
            "the whole six-step run must be definitional at symbolic bytes"
        );
        assert!(
            !SRC_IR_FW_EXACT.contains("Nat.rec") && !SRC_IR_FW_EXACT.contains("Bool.rec"),
            "no case split anywhere: the payloads are never destructured"
        );
    }

    /// A5 exists, inverts through `ir_outcome_disc`, lifts to the flag level,
    /// and is witnessed.
    #[test]
    fn test_a5_is_present_and_composes() {
        assert!(SRC_IR_FW_MACHINE_SOUND.contains("ir_eval fuel ir_fw_module"));
        assert!(
            SRC_IR_FW_MACHINE_SOUND.contains(": Eq Nat (flat_flags_bits (flat_flags_with a b)) k")
        );
        assert!(SRC_IR_FW_MACHINE_SOUND.contains("ir_outcome_disc"));
        assert!(SRC_IR_FW_MACHINE_SOUND.contains("ir_fw_correct mem fuel na u v a b hu hv hle"));
        assert!(SRC_IR_FW_MACHINE_SOUND_FLAGS
            .contains(": Eq FlatFlagsR (flat_flags_with a b) (FlatFlagsR.mk k)"));
        assert!(SRC_IR_FW_MACHINE_SOUND_WITNESS.contains("ir_fw_machine_sound ir_mem0"));
    }

    /// The composition corollary goes through the SIBLING chain's A4 and the
    /// round-trip encoding — no new machine reasoning.
    #[test]
    fn test_the_composition_reuses_the_sibling_a4() {
        assert!(SRC_IR_FW_THEN_CONTAINS.contains("ir_eval fuel ir_fc_module"));
        assert!(SRC_IR_FW_THEN_CONTAINS.contains(":= ir_fc_correct mem fuel na"));
        assert!(SRC_IR_FW_THEN_CONTAINS.contains("(ir_fw_ret_encodes a b)"));
        assert!(SRC_IR_FW_RET_ENCODES.contains(":= EncodesFlatFlags.mk"));
        // The universal statement carries the Bool UNDECIDED; only the concrete
        // witness claims true.
        assert!(SRC_IR_FW_THEN_CONTAINS
            .contains("IRScalar.bool_ (flat_flags_contains (flat_flags_with a b) b)"));
        assert!(SRC_IR_FW_THEN_CONTAINS_WITNESS.contains("IRScalar.bool_ Bool.true"));
    }

    /// Every execution witness runs a registered emitted module at exactly the
    /// step count its body takes, by `Eq.refl`.
    #[test]
    fn test_witnesses_run_the_emitted_modules() {
        for src in [
            SRC_IR_FW_ON_DISJOINT,
            SRC_IR_FW_ON_OVERLAP,
            SRC_IR_FW_ON_IDENTITY,
            SRC_IR_FW_ON_SATURATION,
            SRC_IR_FW_ON_SWAP,
            SRC_IR_FW_ON_JUNK_TAIL,
            SRC_IR_FW_ON_WIDTH_WRAP,
        ] {
            assert!(src.contains("ir_eval ir_d6 ir_fw_module ir_d0"));
            assert!(src.contains("Eq.refl IROutcome"));
        }
        assert!(
            SRC_IR_FW_THEN_CONTAINS_WITNESS.contains("ir_eval ir_d6 ir_fc_module ir_d0"),
            "the interplay witness runs the SIBLING module on with's computed answer"
        );
        assert!(SRC_IR_FW_THEN_CONTAINS_WITNESS.contains("Eq.refl IROutcome"));
    }

    /// The evidence boundary is stated in the registered text, not only in the
    /// module doc: NOTHING claims the interpreter differential.
    #[test]
    fn test_no_interpreter_claim_is_registered() {
        assert!(
            !SRC_IR_FW_CORRECT.contains("interpreter") && !SRC_IR_FW_MODULE.contains("interpreter"),
            "the registered SOURCES never mention the interpreter; the NOT-RUN record lives in \
             the lineage fixture and the registration descriptions state it as a boundary"
        );
    }
}
