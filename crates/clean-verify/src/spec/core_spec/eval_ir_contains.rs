// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The FOURTH complete width-one chain — and the first over a body that
//! COMPUTES: `flat::types::FlatFlags::contains`.**
//!
//! ```text
//! pub const fn contains(self, other: FlatFlags) -> bool {
//!     (self.0 & other.0) == other.0
//! }
//! ```
//!
//! One shipped kernel function carried the whole way from its real source to a
//! Clean-kernel-checked theorem, with every link a real mechanism: the emitted
//! trust-ir recorded verbatim, the proved module gated against that emission
//! instruction for instruction, the codegen flip and its A-LIN lineage digest
//! pinned, the semantics, the refinement theorem, and the kernel check.
//!
//! ## Why this body — measured at HEAD, not inherited
//!
//! Whole-crate release differential of `clean-kernel` at `c4e33541d`, sealed
//! stage1 trustc (trust `352aa0306d`), one non-incremental
//! `cargo rustc --release -p clean-kernel`:
//!
//! ```text
//! bodies                                                      13770
//! derived-MIR agreed                                           1541
//! markers_exact  (== the chainable set)                        1082
//!   ... with a flip event carrying a lineage digest              209   (177 codegen + 32 CTFE)
//!   ... flip-event lineage != coverage-row lineage                 0
//!   ... with any call at all                                       0
//! of the 177 codegen bodies: single-block                       157
//!   containing an icmp / arithmetic / a cast / a condbr          14
//!   containing a gep, a call, or a panic arm                      0
//! ```
//!
//! **Only 14 of the 177 fully-chainable bodies compute anything at all.** The
//! three chains that existed before this one — `has_cubical_layer`,
//! `Level::kind_ord`, `CleanMode::from_source_system` — are none of them:
//! every one is discriminant dispatch onto materialised constants. This is the
//! first chain whose returned value is PRODUCED BY AN OPERATION.
//!
//! | axis | the three earlier chains | `FlatFlags::contains` |
//! |---|---|---|
//! | how the answer is produced | `IRInst.const_` in an arm | **`binop and` then `icmp eq`** |
//! | instruction lanes exercised | load / extractfield / switch / br | **binop + icmp** |
//! | function parameters | 1 | **2** |
//! | representation premise applied | once | **twice, independently** |
//! | `markers_exact` | true, but **VACUOUS** (`0 marker line(s) identical`) | **true over 8 REAL marker lines** |
//!
//! That last row is worth stating plainly because it was measured rather than
//! assumed: at this HEAD **1,082** coverage rows carry `markers_exact: true`
//! and only **27** of them compare a non-empty marker sequence. All three
//! earlier chains are in the vacuous 1,055; this body is in the 27. Their
//! `markers_exact` is a comparison of two empty sequences — a true statement
//! about nothing. Here the derived side emits eight lifetime-marker lines and
//! they agree with built's line for line.
//!
//! ## What is proved
//!
//! For EVERY pair of byte values, EVERY heap, EVERY next-address counter and
//! EVERY fuel at or above 6, the machine running the EMITTED module returns
//! exactly `flat_flags_contains` of the two represented flag sets
//! (`ir_fc_correct`); if it answers `c` then the reflected function IS `c`
//! (`ir_fc_machine_sound`); and on any represented pair it never faults, never
//! traps and never exhausts fuel (`ir_fc_never_faults`). Six concrete
//! executions run the kernel over the body, including the empty flag set, a
//! strict subset, a disjoint pair and a junk-bearing payload spine.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! The reflected `flat_flags_contains` is stated in the machine's own
//! width-8 vocabulary (`ir_nat_bitop Bool.and`, `ir_wrap ir_d8`,
//! `ir_nat_eqb`). That is the honest reading of `(self.0 & other.0) ==
//! other.0` at `u8` — but it means the theorem is a refinement of the EMITTED
//! body against a `u8`-level specification, not against an abstract
//! set-theoretic "subset" predicate. Deriving `contains a a = Bool.true` from
//! it needs bitwise-idempotence lemmas over `ir_nat_bitop_go`, which this
//! program has not earned; the corresponding facts appear here only as
//! CONCRETE kernel-executed witnesses, which is what they are.
//!
//! The link between the proved module and the emitted one is STRUCTURAL —
//! `tests/crystal_a1_lineage/flat_flags_contains.rs` parses the recorded
//! emission and requires this module to encode the same graph, now including
//! the `binop`, `icmp` and `extractfield` lanes. Everything past the flip seam
//! (the MIR optimisation passes, LLVM, linking) is downstream and covered by
//! nothing here. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_FLATFLAGSR: &str = "inductive FlatFlagsR : Type\n| mk : Nat -> FlatFlagsR";

const SRC_FLAT_FLAGS_BITS: &str = "def flat_flags_bits (f : FlatFlagsR) : Nat := FlatFlagsR.rec (fun (_ : FlatFlagsR) => Nat) (fun (n : Nat) => n) f";

const SRC_FLAT_FLAGS_CONTAINS: &str = "def flat_flags_contains (a : FlatFlagsR) (b : FlatFlagsR) : Bool := ir_nat_eqb (ir_wrap ir_d8 (ir_nat_bitop Bool.and ir_d8 (flat_flags_bits a) (flat_flags_bits b))) (ir_wrap ir_d8 (flat_flags_bits b))";

const SRC_ENCODESFLATFLAGS: &str = "inductive EncodesFlatFlags : IRScalar -> FlatFlagsR -> Type\n| mk : forall (n : Nat) (rest : IRScalar), EncodesFlatFlags (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n) rest)) (FlatFlagsR.mk n)";

const SRC_IR_VL2: &str = "def ir_vl2 (a : IRScalar) (b : IRScalar) : IRList IRScalar := IRList.cons IRScalar a (ir_vl1 b)";

const SRC_IR_FC_TFLAGS: &str = "def ir_fc_tflags : IRTy := IRTy.struct_ 1012";

const SRC_IR_FC_B0: &str = "def ir_fc_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd6 (ir_nd1 (IRInst.extractfield ir_tU8 ir_d0 ir_d0) ir_d2) (ir_nd1 (IRInst.extractfield ir_tU8 ir_d1 ir_d0) ir_d3) (ir_nd1 (IRInst.binop IRBinOp.and_ ir_tU8 ir_d2 ir_d3) ir_d4) (ir_nd1 (IRInst.extractfield ir_tU8 ir_d1 ir_d0) ir_d5) (ir_nd1 (IRInst.icmp IRICmpOp.eq_ ir_tU8 ir_d4 ir_d5) ir_d6) (ir_nd (IRInst.ret (ir_nl1 ir_d6))))";

const SRC_IR_FC_FUNC: &str = "def ir_fc_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_fc_b0 ir_blk0)";

const SRC_IR_FC_MODULE: &str = "def ir_fc_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_fc_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

const SRC_IR_FC_VAL: &str =
    "def ir_fc_val (n : Nat) : IRScalar := IRScalar.aggv (ir_sp1 (IRScalar.int_ n))";

// ── execution witnesses: the kernel RUNS the emitted body ───────────────────
const SRC_IR_FC_ON_SELF: &str = "def ir_fc_on_self : Eq IROutcome (ir_eval ir_d6 ir_fc_module ir_d0 (ir_vl2 (ir_fc_val ir_d1) (ir_fc_val ir_d1)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";
const SRC_IR_FC_ON_ABSENT: &str = "def ir_fc_on_absent : Eq IROutcome (ir_eval ir_d6 ir_fc_module ir_d0 (ir_vl2 (ir_fc_val ir_d1) (ir_fc_val ir_d2)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";
const SRC_IR_FC_ON_SUBSET: &str = "def ir_fc_on_subset : Eq IROutcome (ir_eval ir_d6 ir_fc_module ir_d0 (ir_vl2 (ir_fc_val ir_d10) (ir_fc_val ir_d2)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";
const SRC_IR_FC_ON_EMPTY: &str = "def ir_fc_on_empty : Eq IROutcome (ir_eval ir_d6 ir_fc_module ir_d0 (ir_vl2 (ir_fc_val ir_d0) (ir_fc_val ir_d0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";
const SRC_IR_FC_ON_ANY_CONTAINS_EMPTY: &str = "def ir_fc_on_any_contains_empty : Eq IROutcome (ir_eval ir_d6 ir_fc_module ir_d0 (ir_vl2 (ir_fc_val ir_d10) (ir_fc_val ir_d0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";
const SRC_IR_FC_ON_JUNK_TAIL: &str = "def ir_fc_on_junk_tail : Eq IROutcome (ir_eval ir_d6 ir_fc_module ir_d0 (ir_vl2 (IRScalar.aggv (ir_sp2 (IRScalar.int_ ir_d10) IRScalar.undef_)) (IRScalar.aggv (ir_sp2 (IRScalar.int_ ir_d2) IRScalar.undef_))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";

// ── the refinement theorem and its A5 ──────────────────────────────────────
const SRC_IR_FC_MACH0: &str = "def ir_fc_mach0 (u : IRScalar) (v : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl2 ir_d0 ir_d1) (ir_vl2 u v) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_IR_FC_EXACT: &str = "def ir_fc_exact (mem : IRList IRMemSlot) (na : Nat) (x : Nat) (y : Nat) (px : IRScalar) (py : IRScalar) : Eq IROutcome (ir_run ir_d6 ir_fc_module (IRConfig.running (ir_fc_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ x) px)) (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ y) py)) mem na))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (flat_flags_contains (FlatFlagsR.mk x) (FlatFlagsR.mk y))))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (flat_flags_contains (FlatFlagsR.mk x) (FlatFlagsR.mk y)))))";

const SRC_IR_FC_CORRECT: &str = "def ir_fc_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (u : IRScalar) (v : IRScalar) (a : FlatFlagsR) (b : FlatFlagsR) (hu : EncodesFlatFlags u a) (hv : EncodesFlatFlags v b) : Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_fc_module ir_d0 (ir_vl2 u v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (flat_flags_contains a b)))) := EncodesFlatFlags.rec (fun (u0 : IRScalar) (a0 : FlatFlagsR) (_ : EncodesFlatFlags u0 a0) => forall (v0 : IRScalar) (b0 : FlatFlagsR), EncodesFlatFlags v0 b0 -> Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_fc_module ir_d0 (ir_vl2 u0 v0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (flat_flags_contains a0 b0))))) (fun (n : Nat) (px : IRScalar) => fun (v0 : IRScalar) (b0 : FlatFlagsR) (hv0 : EncodesFlatFlags v0 b0) => EncodesFlatFlags.rec (fun (v1 : IRScalar) (b1 : FlatFlagsR) (_ : EncodesFlatFlags v1 b1) => Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_fc_module ir_d0 (ir_vl2 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n) px)) v1) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (flat_flags_contains (FlatFlagsR.mk n) b1))))) (fun (m : Nat) (py : IRScalar) (hle : Le ir_d6 fuel) => ir_run_le_ret ir_fc_module ir_d6 fuel hle (IRConfig.running (ir_fc_mach0 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ n) px)) (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ m) py)) mem na)) (ir_vl1 (IRScalar.bool_ (flat_flags_contains (FlatFlagsR.mk n) (FlatFlagsR.mk m)))) (ir_fc_exact mem na n m px py)) v0 b0 hv0) u a hu v b hv";

const SRC_IR_FC_MACHINE_SOUND: &str = "def ir_fc_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (u : IRScalar) (v : IRScalar) (a : FlatFlagsR) (b : FlatFlagsR) (c : Bool) (hu : EncodesFlatFlags u a) (hv : EncodesFlatFlags v b) (hle : Le ir_d6 fuel) (hret : Eq IROutcome (ir_eval fuel ir_fc_module ir_d0 (ir_vl2 u v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ c)))) : Eq Bool (flat_flags_contains a b) c := Eq.cong IROutcome Bool ir_outcome_bool (IROutcome.ret (ir_vl1 (IRScalar.bool_ (flat_flags_contains a b)))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ c))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (flat_flags_contains a b)))) (ir_eval fuel ir_fc_module ir_d0 (ir_vl2 u v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ c))) (Eq.symm IROutcome (ir_eval fuel ir_fc_module ir_d0 (ir_vl2 u v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (flat_flags_contains a b)))) (ir_fc_correct mem fuel na u v a b hu hv hle)) hret)";

const SRC_IR_FC_NEVER_FAULTS: &str = "def ir_fc_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (u : IRScalar) (v : IRScalar) (a : FlatFlagsR) (b : FlatFlagsR) (hu : EncodesFlatFlags u a) (hv : EncodesFlatFlags v b) (hle : Le ir_d6 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_fc_module ir_d0 (ir_vl2 u v) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_fc_module ir_d0 (ir_vl2 u v) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (flat_flags_contains a b)))) (ir_fc_correct mem fuel na u v a b hu hv hle)";

const SRC_IR_FC_CORRECT_WITNESS: &str = "def ir_fc_correct_witness : Eq IROutcome (ir_eval ir_d6 ir_fc_module ir_d0 (ir_vl2 (ir_fc_val ir_d10) (ir_fc_val ir_d2)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (flat_flags_contains (FlatFlagsR.mk ir_d10) (FlatFlagsR.mk ir_d2))))) := ir_fc_correct ir_mem0 ir_d6 ir_d0 (ir_fc_val ir_d10) (ir_fc_val ir_d2) (FlatFlagsR.mk ir_d10) (FlatFlagsR.mk ir_d2) (EncodesFlatFlags.mk ir_d10 ir_sp0) (EncodesFlatFlags.mk ir_d2 ir_sp0) (Le.refl ir_d6)";

const SRC_IR_FC_MACHINE_SOUND_WITNESS: &str = "def ir_fc_machine_sound_witness : Eq Bool (flat_flags_contains (FlatFlagsR.mk ir_d10) (FlatFlagsR.mk ir_d2)) Bool.true := ir_fc_machine_sound ir_mem0 ir_d6 ir_d0 (ir_fc_val ir_d10) (ir_fc_val ir_d2) (FlatFlagsR.mk ir_d10) (FlatFlagsR.mk ir_d2) Bool.true (EncodesFlatFlags.mk ir_d10 ir_sp0) (EncodesFlatFlags.mk ir_d2 ir_sp0) (Le.refl ir_d6) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))))";

const SRC_IR_FC_MACHINE_SOUND_JUNK_WITNESS: &str = "def ir_fc_machine_sound_junk_witness : Eq Bool (flat_flags_contains (FlatFlagsR.mk ir_d10) (FlatFlagsR.mk ir_d2)) Bool.true := ir_fc_machine_sound ir_mem0 ir_d6 ir_d0 (IRScalar.aggv (ir_sp2 (IRScalar.int_ ir_d10) IRScalar.undef_)) (IRScalar.aggv (ir_sp2 (IRScalar.int_ ir_d2) IRScalar.undef_)) (FlatFlagsR.mk ir_d10) (FlatFlagsR.mk ir_d2) Bool.true (EncodesFlatFlags.mk ir_d10 (ir_sp1 IRScalar.undef_)) (EncodesFlatFlags.mk ir_d2 (ir_sp1 IRScalar.undef_)) (Le.refl ir_d6) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))))";

impl Specification {
    /// Register the FOURTH complete width-one chain, and the first over a body
    /// that computes: `flat::types::FlatFlags::contains`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_contains(&mut self) -> Result<(), SpecError> {
        self.add_inductive(SRC_FLATFLAGSR, "FlatFlagsR: the reflected FlatFlags (flat/types.rs:60) -- a NEWTYPE over u8, one constructor carrying one Nat. Reflected as a wrapper rather than as a bare Nat because the Rust type is a struct and the emitted body reads FIELD 0 of an aggregate; a bare Nat would make the representation relation lie about the shape the machine actually destructures. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_FLAT_FLAGS_BITS, "flat_flags_bits: the newtype projection, by FlatFlagsR.rec. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_FLAT_FLAGS_CONTAINS, "flat_flags_contains: the reflected FlatFlags::contains (flat/types.rs:89) -- `(self.0 & other.0) == other.0` at u8. \n\nStated in the machine's own width-8 vocabulary, and that is a LIMITATION worth naming rather than hiding: ir_nat_bitop Bool.and is the exact bitwise AND on width-8 residues and ir_wrap ir_d8 is the canonicalization ir_int_cmp performs on both operands, so this is what the shipped body computes -- but it is not an abstract subset predicate, and no theorem here converts it into one. The outer ir_wrap on the AND is present because ir_icmp_eq canonicalizes its left operand too; dropping it would need ir_wrap idempotence over ir_nat_bitop's already-canonical result, a lemma nobody has earned. It is the machine's arithmetic, transcribed, not simplified. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESFLATFLAGS, "EncodesFlatFlags v f: the runtime VALUE v represents the flag set f. \n\nBy value, not through the heap: the emitted body takes both arguments by value and performs NO load, so this premise mentions no memory at all -- the same heap-free shape EncodesSourceSystemVal has, for the same measured reason. \n\nSpine-agnostic beyond slot 0, deliberately: the body reads field 0 and nothing else (measured -- three extractfields, all at index 0), so `rest` is universally quantified and the relation says nothing about any later field. A relation that pinned the spine to ir_sp0 would smuggle in a fact the body never observes; ir_fc_on_junk_tail runs the machine with IRScalar.undef_ in slot 1 to show the weakness is real rather than decorative. \n\nSAME OPEN LAYOUT OBLIGATION as the other chains': `FlatFlags(u8)` is a one-field struct whose trust-ir value is an aggregate with the byte at slot 0. That correspondence is a layout fact about the producer, not something proved here. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VL2, "ir_vl2: two-element value list. The first chain in the program with TWO function parameters needs one, and there was none. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_TFLAGS, "ir_fc_tflags: struct.1012, the struct id the emitted body names in `bb0(%0: struct.1012, %1: struct.1012)`. Transcribed for fidelity; the value-addressed semantics never consults it, because ExtractField is a pure function of the VALUE. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_B0, "ir_fc_b0: the ONE block, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/flat_flags_contains.trust-ir.txt). Read self.0 into %2, read other.0 into %3, AND them into %4, read other.0 AGAIN into %5, compare %4 with %5 into %6, return %6. \n\nThe third extractfield is not a typo and must not be common-subexpression-eliminated: the compiler emits `extractfield u8 %1, 0` twice, once for the operand of the AND and once for the operand of the comparison, and the CFG gate's extractfield lane compares the three reads IN ORDER precisely so that a tidier transcription fails. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_FUNC, "ir_fc_func: FlatFlags::contains as EvalIR -- TWO parameters (self at SSA id 0, other at 1), entry block 0, a single block. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_MODULE, "ir_fc_module: the module for FlatFlags::contains, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel, recorded at tests/fixtures/flat_flags_contains.trust-ir.txt and checked graph-for-graph AND instruction-for-instruction against this module by tests/crystal_a1_lineage/flat_flags_contains.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_VAL, "ir_fc_val: the runtime value of a FlatFlags -- a one-field aggregate carrying the byte. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_ON_SELF, "GATE WITNESS: VERIFIED contains VERIFIED. The kernel RUNS the emitted body for six steps -- two field reads, an AND, a third field read, a comparison, a return -- and computes Bool.true. Unlike every witness in the three earlier chains, the answer here is not a constant the body materializes: it is the output of ir_nat_bitop and ir_nat_eqb. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_ON_ABSENT, "GATE WITNESS: VERIFIED does NOT contain HAS_FVAR -- 0x01 AND 0x02 is 0, which differs from 0x02. The FALSE arm, executed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_ON_SUBSET, "GATE WITNESS: 0x0A (HAS_FVAR|HAS_MVAR) contains 0x02 (HAS_FVAR) -- a STRICT subset, so the AND discards a bit and the comparison still holds. This is the case that distinguishes `contains` from equality, and it is the reason the body needs an AND at all. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_IR_FC_ON_EMPTY,
            "GATE WITNESS: the empty flag set contains itself. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_IR_FC_ON_ANY_CONTAINS_EMPTY, "GATE WITNESS: 0x0A contains the empty set -- the identity FlatFlags::empty() relies on. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_ON_JUNK_TAIL, "GATE WITNESS: both aggregates carry IRScalar.undef_ in slot 1 -- a value the semantics refuses to load through and cannot compare -- and the machine still answers true. The executable form of EncodesFlatFlags's spine-agnosticism: the body provably never reads past field 0. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_MACH0, "ir_fc_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds TWO parameters positionally. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_EXACT, "ir_fc_exact: the machine agrees with the reflected contains at EXACTLY 6 steps, for ARBITRARY bytes x and y and ARBITRARY payload tails. Eq.refl -- and that it is Eq.refl is the interesting part: ir_int2 and ir_ef_at destructure the SCALAR CONSTRUCTORS, not the Nat payloads, so the whole body computes symbolically and no case split is needed anywhere. Nothing about x and y is decided; the machine's answer is a term in them. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_CORRECT, "ir_fc_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE, FOR A BODY THAT COMPUTES. *** For every pair of flag sets, every value representing them, every heap, every next-address counter and every fuel at or above 6, ir_eval on ir_fc_module returns exactly IROutcome.ret [bool (flat_flags_contains a b)]. \n\nThe first chain in the program whose returned value is produced by an OPERATION -- a width-8 bitwise AND followed by a width-8 equality -- rather than selected from constants materialized in switch arms. Proved by EncodesFlatFlags.rec TWICE, nested, because the body has two parameters and each carries its own independent representation premise. \n\nA0 is measured on the SHIPPED kernel at clean c4e33541d: lowered, spliced, unsupported [], derived_mir.verdict agreed (5 canonical lines identical), markers_exact TRUE over EIGHT REAL MARKER LINES (not the vacuous zero-marker truth 1055 of the 1082 candidates carry), zero calls so the reachable closure is bodyful, and a codegen flip event whose A-LIN lineage equals the coverage row's. A1 is gated by tests/crystal_a1_lineage/flat_flags_contains.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_MACHINE_SOUND, "ir_fc_machine_sound: *** A5, THE INVERSION. *** If the MACHINE answers c, then the reflected contains of the two represented flag sets IS c -- for every c, not just for a chosen one. Goes through A4 rather than restating it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_NEVER_FAULTS, "ir_fc_never_faults: *** NO UB, NO PANIC, NO EXHAUSTION -- on any represented pair. *** A corollary of A4. Concretely for this body: the three extractfields never fault not_agg or bad_field, the AND never faults not_int, the comparison never faults, and 6 steps always suffice. Earned by EncodesFlatFlags's premise, not assumed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_CORRECT_WITNESS, "ir_fc_correct_witness: A4 is not vacuous -- every premise discharged concretely at the strict-subset pair, and the conclusion RUNS the machine. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_MACHINE_SOUND_WITNESS, "ir_fc_machine_sound_witness: A5 is not vacuous. Instantiated at the strict-subset pair with the observation discharged by Eq.refl, which the kernel discharges by executing the body. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FC_MACHINE_SOUND_JUNK_WITNESS, "ir_fc_machine_sound_junk_witness: A5 again, on aggregates whose SECOND field is IRScalar.undef_. The premises still discharge and the machine still answers, which is the executable proof that the payload-agnostic representation premise is genuinely satisfiable by values the body could not read past. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The emitted body reads `other.0` TWICE. A transcription that reuses the
    /// first read is one instruction shorter than the shipped artifact.
    #[test]
    fn test_the_duplicate_field_read_is_transcribed() {
        assert_eq!(
            SRC_IR_FC_B0
                .matches("IRInst.extractfield ir_tU8 ir_d1 ir_d0")
                .count(),
            2,
            "other.0 is read twice, once for the AND and once for the comparison"
        );
        assert_eq!(
            SRC_IR_FC_B0
                .matches("IRInst.extractfield ir_tU8 ir_d0 ir_d0")
                .count(),
            1,
            "self.0 is read once"
        );
        // …and they bind DIFFERENT SSA ids, which is what makes them two reads
        // rather than one written twice.
        assert!(SRC_IR_FC_B0.contains("ir_d1 ir_d0) ir_d3)"));
        assert!(SRC_IR_FC_B0.contains("ir_d1 ir_d0) ir_d5)"));
    }

    /// The answer is COMPUTED. No `IRConst` appears anywhere in this body —
    /// that is the whole reason this chain is different from the first three.
    #[test]
    fn test_the_answer_is_computed_not_materialized() {
        assert!(
            !SRC_IR_FC_B0.contains("IRConst"),
            "this body materializes no constant at all; its answer comes out of a binop and an \
             icmp"
        );
        assert!(SRC_IR_FC_B0.contains("IRInst.binop IRBinOp.and_ ir_tU8 ir_d2 ir_d3"));
        assert!(SRC_IR_FC_B0.contains("IRInst.icmp IRICmpOp.eq_ ir_tU8 ir_d4 ir_d5"));
        assert!(
            !SRC_IR_FC_B0.contains("IRInst.switch") && !SRC_IR_FC_B0.contains("IRInst.condbr"),
            "straight line: one block, no dispatch"
        );
        assert!(
            !SRC_IR_FC_B0.contains("IRInst.load"),
            "both arguments arrive BY VALUE; a load would mean a different body and a heap-bearing \
             premise"
        );
    }

    /// The representation premise must stay spine-agnostic past slot 0.
    #[test]
    fn test_representation_is_spine_agnostic() {
        assert!(SRC_ENCODESFLATFLAGS.contains("(rest : IRScalar)"));
        assert!(SRC_ENCODESFLATFLAGS.contains("IRScalar.vcons (IRScalar.int_ n) rest"));
        for pinned in ["ir_sp0", "ir_sp1", "ir_sp2", "IRScalar.vnil"] {
            assert!(
                !SRC_ENCODESFLATFLAGS.contains(pinned),
                "the payload tail must not be pinned to {pinned}"
            );
        }
        assert!(
            !SRC_ENCODESFLATFLAGS.contains("ir_mem_lookup"),
            "by-value arguments: this premise must constrain NO memory"
        );
        for bad in ["Exists", "Sigma"] {
            assert!(!SRC_ENCODESFLATFLAGS.contains(bad));
        }
    }

    /// A4 stays universally quantified over both flag sets, both values, the
    /// heap and the fuel.
    #[test]
    fn test_a4_shape() {
        let statement = SRC_IR_FC_CORRECT.split(":=").next().unwrap_or("");
        assert!(statement.contains("(a : FlatFlagsR)") && statement.contains("(b : FlatFlagsR)"));
        assert!(statement.contains("(mem : IRList IRMemSlot)"));
        assert!(SRC_IR_FC_CORRECT.contains("Le ir_d6 fuel ->"));
        assert!(SRC_IR_FC_CORRECT.contains("ir_run_le_ret"));
        assert!(
            !statement.contains("FlatFlagsR.mk"),
            "A4's STATEMENT must not name a concrete flag set, or it is a witness"
        );
        assert!(
            !statement.contains("ir_mem0"),
            "a concrete heap would make this a witness, not a theorem"
        );
        // BOTH representation premises are consumed — two nested recursors.
        assert_eq!(
            SRC_IR_FC_CORRECT.matches("EncodesFlatFlags.rec").count(),
            2,
            "one recursor per parameter; a single one would leave a premise unused"
        );
    }

    /// A5 exists and composes with A4 through `ir_outcome_bool`.
    #[test]
    fn test_a5_is_present_and_composes() {
        assert!(SRC_IR_FC_MACHINE_SOUND.contains("ir_eval fuel ir_fc_module"));
        assert!(SRC_IR_FC_MACHINE_SOUND.contains(": Eq Bool (flat_flags_contains a b) c"));
        assert!(SRC_IR_FC_MACHINE_SOUND.contains("ir_fc_correct mem fuel na u v a b hu hv hle"));
        assert!(SRC_IR_FC_MACHINE_SOUND.contains("ir_outcome_bool"));
        // …and it is witnessed, twice, once on a junk-bearing spine.
        assert!(SRC_IR_FC_MACHINE_SOUND_WITNESS.contains("ir_fc_machine_sound ir_mem0"));
        assert!(SRC_IR_FC_MACHINE_SOUND_JUNK_WITNESS.contains("IRScalar.undef_"));
    }

    /// Every emitted-arm witness runs the machine at exactly the step count the
    /// body takes, over the module the gate pins.
    #[test]
    fn test_witnesses_run_the_emitted_module() {
        for src in [
            SRC_IR_FC_ON_SELF,
            SRC_IR_FC_ON_ABSENT,
            SRC_IR_FC_ON_SUBSET,
            SRC_IR_FC_ON_EMPTY,
            SRC_IR_FC_ON_ANY_CONTAINS_EMPTY,
            SRC_IR_FC_ON_JUNK_TAIL,
        ] {
            assert!(src.contains("ir_eval ir_d6 ir_fc_module ir_d0"));
            assert!(src.contains("Eq.refl IROutcome"));
        }
    }
}
