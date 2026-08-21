// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The width-one chain, retargeted to a function the compiler already flips.**
//!
//! `CleanMode::has_cubical_layer` (`clean-kernel/src/mode.rs`) — the whole crystal
//! shape (reflected type, reflected function, representation relation, equality
//! theorem, witnesses) for a SHIPPED kernel function.
//!
//! ## Why retarget at all
//!
//! `eval_ir_correct` proves the same shape for `Level::is_zero`, and that theorem
//! stands. But the compiler still SHIMS that body: `Max`/`IMax` payloads are
//! `LevelArc` structs rather than scalars, so the by-ref payload recognizer
//! declines it (`trust:reports/t2-byref-enum-flip-2026-08-05.md` §5). Closing
//! that would be a ninth widening of the gate that authorizes replacing shipped
//! machine code — and the session that got eight deep had an adversarial audit
//! find one of those widenings UNSOUND, reverted, and recorded the next one as
//! an owner-level judgement rather than a patch.
//!
//! Beware the trap in that report's results table: the row that flips is
//! `Level::is_zero_shallow`, and **no such function exists in `clean-kernel`** —
//! it is a probe fixture. No shipped kernel function of that family flips.
//!
//! `has_cubical_layer` does sit in the class that flips. `CleanMode` is
//! FIELDLESS, so a value is its discriminant: no payload, no pointer to follow,
//! no recursion — a by-ref discriminant read, exactly what T2 measured reaching
//! `DerivedAgreed` at `-O` and `-O0`. Pinning it needed A0/A1 plumbing on a class
//! that already works, not new authorization surface.
//!
//! ## What is proved
//!
//! Proved: for EVERY `CleanMode`, every heap representing it, every fuel at or
//! above 6, the machine returns exactly `clean_mode_has_cubical m` (A4,
//! `ir_h2_correct`); if the machine ANSWERS true then the mode really does carry
//! the cubical layer (A5, `ir_h2_machine_sound`); and on any represented mode it
//! never faults, never traps and never exhausts fuel (`ir_h2_never_faults`). The
//! module is executed by the kernel on four of the six tags as witnesses.
//!
//! ## A5 was deleted once — 2026-08-12 note
//!
//! `ir_hcl_machine_sound` landed in `08d4c6cb1` and was removed by `9c37f0ef0`
//! when this module was re-authored from measured output. Nothing replaced it,
//! so for two days the chain stopped at the equality theorem while the design
//! docs described a six-rung A0–A6 and `bundles.rs` still explained the stage
//! ordering by "its A5-analogue consumes `ir_outcome_bool`" — a dependency that
//! no longer existed. It is restored above, renamed to the `ir_h2_` family and
//! re-typed against the transcribed module. `test_a5_is_present_and_composes`
//! below is what makes a silent re-deletion fail rather than pass.
//!
//! A5 here is an INVERSION (machine answer → reflected predicate), not the
//! denotational step `ir_lz_machine_sound` takes: that one composes with
//! `level_is_zero_sound` to reach `level_eval`, and this spec has no comparable
//! semantics of `CleanMode` to compose with. Said plainly so the two are not
//! quoted as equals.
//!
//! A0/A1/A6 are recorded for the shipped kernel body: the differential agrees,
//! the module is structurally checked against the recorded emitted trust-ir,
//! and the flip-event lineage equals the inspected artifact lineage. This is a
//! width-one chain; by itself it does not retire a kernel-wide trust assumption.
//!
//! ## CORRECTED 2026-08-11 — the module is now TRANSCRIBED FROM MEASURED OUTPUT
//!
//! A stage-1 trustc built this session reports, for the shipped body:
//! `derived_mir.verdict = agreed`, `markers_exact = True` — A0, with **no**
//! widening of the codegen-flip gate, exactly as a fieldless-enum discriminant
//! read should behave.
//!
//! Dumping the emitted trust-ir then showed the previous hand-authored module
//! was semantically equivalent but STRUCTURALLY DIFFERENT: six switch cases vs
//! two-plus-default, one shared true block vs two, direct returns vs a join
//! block taking a block PARAMETER, and an `unreachable` default vs a default
//! edge that simply carries `false`. A theorem about that module was not a
//! theorem about the shipped body. The module here is transcribed from
//! `docs/analysis/a0-has-cubical-layer-measured-2026-08-11.md`.
//!
//! A1 is checked by `tests/crystal_a1_lineage.rs`. It compares this module's CFG
//! with the recorded emitted artifact and pins the equality between that
//! artifact's lineage and the A6 flip-event lineage. It deliberately does not
//! recompute trust's lineage digest; that remains compiler-side evidence.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_CLEANMODER: &str = "inductive CleanModeR : Type\n| constructive : CleanModeR\n| impredicative : CleanModeR\n| cubical : CleanModeR\n| directed : CleanModeR\n| classical : CleanModeR\n| settheoretic : CleanModeR";

const SRC_CLEAN_MODE_HAS_CUBICAL: &str = "def clean_mode_has_cubical (m : CleanModeR) : Bool := CleanModeR.rec (fun (_ : CleanModeR) => Bool) Bool.false Bool.false Bool.true Bool.true Bool.false Bool.false m";

const SRC_CLEAN_MODE_TAG: &str = "def clean_mode_tag (m : CleanModeR) : Nat := CleanModeR.rec (fun (_ : CleanModeR) => Nat) ir_d0 ir_d1 ir_d2 ir_d3 ir_d4 ir_d5 m";

const SRC_ENCODESCLEANMODE: &str = "inductive EncodesCleanMode (mem : IRList IRMemSlot) : IRScalar -> CleanModeR -> Type\n| mk : forall (a : Nat) (m : CleanModeR), Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (clean_mode_tag m) ir_sp0) Bool.true)) -> EncodesCleanMode mem (IRScalar.ptr_ a) m";

/// **The module itself is GENERATED, not transcribed.**
///
/// `generated/ir_h2.defs.txt` is minted by [`crate::ir_mint`] from the trust-ir
/// the compiler emitted for this body, and `tests/crystal_a2_mint.rs` fails
/// closed if it is not exactly what minting the committed core module produces.
/// Seven of these eight definitions came out CHARACTER-IDENTICAL to the hand
/// transcription they replaced, including `ir_h2_tmode` and its `ir_d13` — the
/// mint agrees with the 2026-08-19 load-type correction below, independently,
/// from the artifact.
///
/// The eighth did not, and that is the point. The transcription carried
/// `Switch.exhaustive_enum_unreachable = Bool.true`; the artifact says
/// **false** — on three producer dumps, and in agreement with all four sibling
/// chains. `trust_ir`'s `Display` matches `Inst::Switch { .., .. }` and NEVER
/// PRINTS that field, so no reader of the emitted TEXT — the A1 lane
/// comparator and its `load_tys` / `extract_tys` lanes included — could ever
/// have seen it. It is the same class of defect the load type was, one slot
/// further out: a field the artifact carries, the model carries, and nothing
/// compared.
///
/// Nothing in `eval_ir_machine` dispatches on the flag (`IRInst.switch v dflt
/// dargs cases exh => ir_switch_exec m s (ir_getd s v) dflt dargs cases` drops
/// it), so no theorem moved when it was corrected — exactly as none moved when
/// the load type was. What moved is that `ir_h2_correct` is now a theorem about
/// a module the compiler emits.
///
/// ## Why `ir_d13` is still here, and how the gate avoids alarming on it
///
/// `enum.13` is a CRATE-LEVEL interning id. Measured across three producer
/// dumps of the shipped kernel, this one did not move — but
/// `expr_path_step_clone`'s moved 181 → 176 with no instruction changed, which
/// is exactly the false-alarm class a gate over emitted IR dies of. So the mint
/// splits the two facts apart: the CORE module the digest is taken over carries
/// the canonical FIRST-USE index (`(enum 0)`, producer-stable), and the
/// crate-level id lives in a committed per-chain tag table
/// (`generated/ir_h2.tags.json`) that the minter reads to emit this alias. A
/// re-interning therefore shows up as a one-line, reviewed change to that table
/// — which is what `data/crystal_enum_tag_pin.json` already exists to own —
/// and NOT as a module-identity failure. `crystal_a2_mint`'s `m7` is the check
/// that the table still describes the artifact.
const MINTED_IR_H2: &str = include_str!("generated/ir_h2.defs.txt");

// The type the entry block LOADS. It is `CleanMode`, enum id 13, and the
// emitted body names it: `%2 = load enum.13, ptr %0`
// (tests/fixtures/has_cubical_layer.trust-ir.txt).
//
// CORRECTED 2026-08-19. This slot read `ir_tLevel` -- `IRTy.enum_ ir_d0`, the
// alias belonging to the `Level::is_zero` module -- from the day the block was
// transcribed. It was a copy-paste, and it named a type this body does not
// touch, in a method on CleanMode. Nothing failed, in either of two ways that
// are worth separating:
//
//  * The A1 lineage gate never read the operand. `IRInst.load` carries a type
//    and the artifact prints one, and until the 2026-08-19 operand audit added
//    the `load_tys` lane NEITHER parser looked at the slot, so a transcription
//    at any type at all compared equal to the artifact.
//  * The downstream theorems never read it either, and STILL do not:
//    `ir_exec`'s arm is `IRInst.load t p vol => ir_bind_result s rs
//    (ir_load_eval s (ir_getd s p))`, which binds `t` and discards it. So
//    `ir_h2_correct`, `ir_h2_machine_sound` and `ir_h2_never_faults` are
//    unchanged by this correction -- they were true with the wrong type and are
//    true with the right one.
//
// That second point is the finding, not the reassurance. Clean's model is
// COARSER here than the artifact's own semantics, where the loaded type decides
// the read size, the alignment fault and the decode
// (trust-ir/src/interpret.rs::eval_load). A theorem that cannot tell `enum.13`
// from `enum.0` is not evidence that the difference does not matter; it is the
// statement that this model cannot see it. What can see it is the gate, and now
// does.
// The MINTED script carries both slots now; the account above is retained
// verbatim because it is the reason the load type is compared at all, and the
// mint reproducing `ir_d13` from the artifact is what turns that correction
// from a repair into a derivation.

/// The per-definition rationale for the minted script, in registration order.
/// One row per `def` line; the count is asserted below, so a regenerated script
/// with a different shape fails rather than silently reusing the wrong doc.
const MINTED_IR_H2_DOCS: &[&str] = &[
    "ir_h2_tmode: the CleanMode enum type, enum id 13 -- the id the emitted body names in `%2 = load enum.13, ptr %0`, and the same id `ir_fs_tmode` carries for the same Rust type in the from_source_system chain. CORRECTED 2026-08-19 from `ir_tLevel` (IRTy.enum_ 0), which was a copy-paste from the Level module and named a type this body does not touch; MINTED since 2026-08-20, so the corrected value is now derived from the artifact rather than repaired by hand -- the mint reproduced `ir_d13` independently, out of the committed tag table `generated/ir_h2.tags.json` that `m7` checks against the artifact. The load lane of the A1 gate compares this slot; the machine still does not read it, which is a fact about the model, not a licence. DerivedProved, zero axiom_deps.",
    "ir_h2_b0: entry block, MINTED FROM THE EMITTED ARTIFACT. Two switch cases (2 -> b1, 3 -> b2) and a default -- not a six-way table. The compiler emits only the true tags explicitly and routes everything else through the default edge. The exhaustive-enum flag is the MEASURED false, not the transcribed true. DerivedProved, zero axiom_deps.",
    "ir_h2_b1: Cubical => true, then br to the join. A SEPARATE block from Directed's, as emitted. DerivedProved, zero axiom_deps.",
    "ir_h2_b2: Directed => true. The emitted code does NOT share a block with Cubical, so neither does this. DerivedProved, zero axiom_deps.",
    "ir_h2_b3: the default edge => false. Note there is NO unreachable block in the emitted body: exhaustiveness is not expressed as a trap, it is expressed by the default edge carrying the false answer. DerivedProved, zero axiom_deps.",
    "ir_h2_b4: the JOIN block, taking a block PARAMETER. The emitted body funnels all three arms through br into bb4(%1: bool) and returns that parameter, rather than returning from each arm. DerivedProved, zero axiom_deps.",
    "ir_h2_func: CleanMode::has_cubical_layer as EvalIR, five blocks, matching the emitted body's control-flow graph exactly. DerivedProved, zero axiom_deps.",
    "ir_h2_module: the module for has_cubical_layer, MINTED from the emitted trust-ir rather than transcribed from it. Three independent readers agree on it (the artifact binary, the emitted text, and this elaborated term itself); see crate::ir_mint for what that establishes and what it does not. DerivedProved, zero axiom_deps.",
];

const SRC_IR_H2_ON_CUBICAL: &str = "def ir_h2_on_cubical : Eq IROutcome (ir_eval ir_d6 ir_h2_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d2 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";

const SRC_IR_H2_ON_DIRECTED: &str = "def ir_h2_on_directed : Eq IROutcome (ir_eval ir_d6 ir_h2_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";

const SRC_IR_H2_ON_CONSTRUCTIVE: &str = "def ir_h2_on_constructive : Eq IROutcome (ir_eval ir_d6 ir_h2_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";

const SRC_IR_H2_ON_SETTHEORETIC: &str = "def ir_h2_on_settheoretic : Eq IROutcome (ir_eval ir_d6 ir_h2_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d5 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";

const SRC_IR_H2_MACH0: &str = "def ir_h2_mach0 (mem : IRList IRMemSlot) (a : Nat) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 (IRScalar.ptr_ a)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_IR_H2_AFTER_LOAD: &str = "def ir_h2_after_load (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (o : (IROption IRMemSlot)) : IRConfig := ir_bind_result (ir_h2_mach0 mem a na) (ir_nl1 ir_d2) (ir_load_slot o)";

const SRC_IR_H2_EXACT: &str = "def ir_h2_exact (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (m : CleanModeR) : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (clean_mode_tag m) ir_sp0) Bool.true)) -> Eq IROutcome (ir_run ir_d6 ir_h2_module (IRConfig.running (ir_h2_mach0 mem a na))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (clean_mode_has_cubical m)))) := CleanModeR.rec (fun (m0 : CleanModeR) => Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (clean_mode_tag m0) ir_sp0) Bool.true)) -> Eq IROutcome (ir_run ir_d6 ir_h2_module (IRConfig.running (ir_h2_mach0 mem a na))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (clean_mode_has_cubical m0))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 ir_sp0) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_h2_module (ir_h2_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 ir_sp0) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 ir_sp0) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 ir_sp0) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_h2_module (ir_h2_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 ir_sp0) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 ir_sp0) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 ir_sp0) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_h2_module (ir_h2_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 ir_sp0) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 ir_sp0) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 ir_sp0) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_h2_module (ir_h2_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 ir_sp0) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 ir_sp0) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 ir_sp0) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_h2_module (ir_h2_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 ir_sp0) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 ir_sp0) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))))) (fun (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d5 ir_sp0) Bool.true))) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d5 ir_h2_module (ir_h2_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d5 ir_sp0) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d5 ir_sp0) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))))) m";

const SRC_IR_H2_CORRECT: &str = "def ir_h2_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (m : CleanModeR) (henc : EncodesCleanMode mem r m) : Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_h2_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (clean_mode_has_cubical m)))) := EncodesCleanMode.rec mem (fun (s0 : IRScalar) (m0 : CleanModeR) (_ : EncodesCleanMode mem s0 m0) => Le ir_d6 fuel -> Eq IROutcome (ir_eval fuel ir_h2_module ir_d0 (ir_vl1 s0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (clean_mode_has_cubical m0))))) (fun (a : Nat) (m0 : CleanModeR) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var (clean_mode_tag m0) ir_sp0) Bool.true))) (hle : Le ir_d6 fuel) => ir_run_le_ret ir_h2_module ir_d6 fuel hle (IRConfig.running (ir_h2_mach0 mem a na)) (ir_vl1 (IRScalar.bool_ (clean_mode_has_cubical m0))) (ir_h2_exact mem a na m0 h)) r m henc";

const SRC_IR_H2_MACHINE_SOUND: &str = "def ir_h2_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (m : CleanModeR) (henc : EncodesCleanMode mem r m) (hle : Le ir_d6 fuel) (hret : Eq IROutcome (ir_eval fuel ir_h2_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))) : Eq Bool (clean_mode_has_cubical m) Bool.true := Eq.cong IROutcome Bool ir_outcome_bool (IROutcome.ret (ir_vl1 (IRScalar.bool_ (clean_mode_has_cubical m)))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (clean_mode_has_cubical m)))) (ir_eval fuel ir_h2_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) (Eq.symm IROutcome (ir_eval fuel ir_h2_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (clean_mode_has_cubical m)))) (ir_h2_correct mem fuel na r m henc hle)) hret)";

const SRC_IR_H2_MACHINE_SOUND_WITNESS: &str = "def ir_h2_machine_sound_witness : Eq Bool (clean_mode_has_cubical CleanModeR.directed) Bool.true := ir_h2_machine_sound (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d6 ir_d1 (IRScalar.ptr_ ir_d0) CleanModeR.directed (EncodesCleanMode.mk (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d0 CleanModeR.directed (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d3 ir_sp0) Bool.true)))) (Le.refl ir_d6) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))))";

const SRC_IR_H2_NEVER_FAULTS: &str = "def ir_h2_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (m : CleanModeR) (henc : EncodesCleanMode mem r m) (hle : Le ir_d6 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_h2_module ir_d0 (ir_vl1 r) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_h2_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (clean_mode_has_cubical m)))) (ir_h2_correct mem fuel na r m henc hle)";

const SRC_IR_H2_CORRECT_WITNESS: &str = "def ir_h2_correct_witness : Eq IROutcome (ir_eval ir_d6 ir_h2_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (clean_mode_has_cubical CleanModeR.directed)))) := ir_h2_correct (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d6 ir_d1 (IRScalar.ptr_ ir_d0) CleanModeR.directed (EncodesCleanMode.mk (ir_cell ir_d0 (ir_var ir_d3 ir_sp0) ir_mem0) ir_d0 CleanModeR.directed (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d3 ir_sp0) Bool.true)))) (Le.refl ir_d6)";

/// The `has_cubical_layer` chain's MODULE definitions, in registration order.
///
/// ONE source of truth, shared by [`Specification::add_eval_ir_mode`] and the
/// GAP-2 encoding differential (`crate::ir_semdiff`). The differential must run
/// the machine on *the registered module*, not on a second transcription of it;
/// exporting the same lines is what makes drift between them impossible
/// rather than merely unlikely.
///
/// A FUNCTION over the minted script rather than an array of hand-written
/// constants as of 2026-08-20: the registered module is now generated
/// (`generated/ir_h2.defs.txt`), and the contract above is exactly the reason
/// the differential must read the generated lines too rather than a copy of
/// them. Same guarantee, one fewer transcription.
static MINTED_IR_H2_LINES: std::sync::LazyLock<Vec<&'static str>> =
    std::sync::LazyLock::new(|| {
        MINTED_IR_H2
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect()
    });

/// The minted `has_cubical_layer` module definitions, in registration order.
#[must_use]
pub fn ir_h2_module_defs() -> &'static [&'static str] {
    &MINTED_IR_H2_LINES
}

impl Specification {
    /// The width-one chain over the EMITTED shape of `CleanMode::has_cubical_layer`.
    pub(super) fn add_eval_ir_mode(&mut self) -> Result<(), SpecError> {
        self.add_inductive(SRC_CLEANMODER, "CleanModeR: the reflected CleanMode. Six FIELDLESS variants, so a value IS its discriminant -- which is exactly why the compiler's discriminant recognizer accepts this body and why it, not Level::is_zero, is the width-one target that can close. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CLEAN_MODE_HAS_CUBICAL, "clean_mode_has_cubical: the reflected has_cubical_layer. True on Cubical and Directed -- the 2LTT bridge -- matching mode.rs's three ENSURES clauses. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CLEAN_MODE_TAG, "clean_mode_tag: each variant's discriminant, 0..5 in declaration order. The ONE place the reflected type meets the emitted layout. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESCLEANMODE, "EncodesCleanMode mem p m: the heap at p represents mode m. One live cell whose payload is the tag -- no edges, no sharing, no child liveness, because the enum is fieldless. Stated as an EQUATION on ir_mem_lookup: membership would be satisfiable by a shadowed duplicate while the machine reads a different cell. DerivedProved, zero axiom_deps.")?;
        // The module is REPLAYED from the minted script, line for line. A
        // generated artifact registered by the same code that a gate
        // regenerates is the `kernel_core_red_env` posture: Clean's parser and
        // elaborator still turn the text into the term the theorems are about,
        // so this joins an existing trust class rather than opening a new one.
        let minted = ir_h2_module_defs();
        if minted.len() != MINTED_IR_H2_DOCS.len() {
            return Err(SpecError::EnvError(format!(
                "the minted ir_h2 script has {} definitions but {} rationales are declared; \
                 regenerate the docs table with the script rather than reusing it",
                minted.len(),
                MINTED_IR_H2_DOCS.len()
            )));
        }
        for (line, doc) in minted.iter().zip(MINTED_IR_H2_DOCS) {
            self.add_recursive_def(line, doc)?;
        }
        self.add_recursive_def(SRC_IR_H2_ON_CUBICAL, "GATE WITNESS: Cubical. Eq.refl -- the kernel runs the machine, 6 steps. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_H2_ON_DIRECTED, "GATE WITNESS: Directed, the 2LTT bridge, and the arm that exercises the SECOND true block. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_H2_ON_CONSTRUCTIVE, "GATE WITNESS: Constructive reaches the default edge and answers false. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_H2_ON_SETTHEORETIC, "GATE WITNESS: SetTheoretic, the last tag, also via the default edge. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_H2_MACH0, "ir_h2_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_H2_AFTER_LOAD, "ir_h2_after_load: the entry step with the heap lookup made SYNTACTIC, so Eq.subst has something to rewrite. Binds %2, matching the emitted SSA numbering. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_H2_EXACT, "ir_h2_exact: the machine agrees with the reflected predicate at EXACTLY 6 steps -- 3 in the entry block, 2 in an arm, 1 in the join. CleanModeR.rec with a convoy motive carrying the lookup hypothesis, so all six tags compute. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_H2_CORRECT, "ir_h2_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE. *** For every CleanMode, every heap representing it, and every fuel at or above 6, ir_eval on ir_h2_module returns exactly clean_mode_has_cubical m. \
\
Unlike its predecessor this is a statement about the module the compiler ACTUALLY emits, which is what makes it a candidate half of the crystal's link. A0 is measured: derived_mir.verdict = agreed, markers_exact = True, with no widening of the codegen-flip gate. \
\
A1 is pinned by tests/crystal_a1_lineage.rs: the registered CFG is checked against the recorded emitted trust-ir, and the artifact lineage must equal the A6 flip-event lineage. The test does not recompute trust's digest. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_H2_CORRECT_WITNESS, "ir_h2_correct_witness: not vacuous, and the witness RUNS THE MACHINE at Directed -- the tag whose arm is the second true block. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_H2_MACHINE_SOUND, "ir_h2_machine_sound: *** A5 FOR THIS CHAIN. *** If the MACHINE answers true, the mode really does carry the cubical layer -- it is Cubical or Directed. \
\
RESTORED 2026-08-12. This declaration landed in 08d4c6cb1 as ir_hcl_machine_sound and was DELETED by 9c37f0ef0 when the module was re-authored from measured output; nothing replaced it, so the chain that is supposed to close stopped at the equality theorem while the design docs went on describing a six-rung A0..A6. Here it is again, re-typed against the transcribed module (fuel ir_d6, not ir_d5) and renamed to the ir_h2_ family. \
\
STATED SCOPE, which must travel with it. This is an INVERSION -- from an observation about the running machine back to the reflected predicate -- and NOT the denotational step its counterpart ir_lz_machine_sound takes. That one composes with level_is_zero_sound to conclude a fact about level_eval under every assignment; there is no comparable semantics of CleanMode in this spec to compose with, so the honest conclusion here is the reflected predicate itself. Deeper would require a mode semantics that does not exist yet. \
\
The composition is an equality argument, not three injectivity lemmas: apply ir_outcome_bool to both sides with Eq.cong and let the kernel compute, since ir_outcome_bool (ret [bool b]) reduces to b. That is why this stage must run AFTER add_eval_ir_correct, which registers it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_H2_MACHINE_SOUND_WITNESS, "ir_h2_machine_sound_witness: A5 is not vacuous, and the witness RUNS THE MACHINE. Instantiated at the one-cell heap encoding Directed -- the 2LTT bridge, and the arm most easily lost to a misrouted Switch -- with every premise discharged concretely: the representation by EncodesCleanMode.mk, the fuel bound by Le.refl at exactly 6, and the observation by Eq.refl, which the kernel discharges by executing the body. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_H2_NEVER_FAULTS, "ir_h2_never_faults: *** NO UB, NO PANIC, NO EXHAUSTION -- on any represented mode. *** A corollary of ir_h2_correct, and the analogue of ir_lz_never_faults for this chain. IROutcome separates success from ub, type_error, unmodelled, stuck and fuel_out, so proving the outcome is a ret rules out all five at once. \
\
Concretely for the emitted body: the default edge is taken on four of the six tags and is a real answer rather than a trap, no load faults bad_addr or null_deref, and 6 steps always suffice. All of it is earned by EncodesCleanMode's premise -- one live cell whose payload is the tag -- rather than assumed. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// One minted definition, by name. Fails loudly rather than returning an
    /// empty string: a test that silently matched nothing would pass.
    fn minted(name: &str) -> &'static str {
        MINTED_IR_H2
            .lines()
            .map(str::trim)
            .find(|l| l.starts_with(&format!("def {name} ")))
            .unwrap_or_else(|| panic!("the minted ir_h2 script has no `{name}`"))
    }

    /// The script registered here is exactly the one the A2 gate regenerates.
    #[test]
    fn test_minted_script_is_the_registered_one() {
        assert_eq!(MINTED_IR_H2, crate::ir_mint::IR_H2_DEFS);
        assert_eq!(
            MINTED_IR_H2
                .lines()
                .filter(|l| !l.trim().is_empty())
                .count(),
            MINTED_IR_H2_DOCS.len()
        );
    }

    /// The switch must be TWO cases plus a default — the emitted shape — not a
    /// six-way table. This is the difference that made the old module wrong.
    #[test]
    fn test_switch_matches_emitted_two_cases_plus_default() {
        assert!(minted("ir_h2_b0").contains("(ir_sc ir_d2 ir_d1 (ir_sc ir_d3 ir_d2 ir_sc0))"));
        assert!(
            !minted("ir_h2_b0").contains("ir_sc ir_d4"),
            "the emitted switch lists no tag 4 case"
        );
    }

    /// The exhaustive-enum flag is the MEASURED one.
    ///
    /// This is the field trust-ir's `Display` never prints, so the A1 lane
    /// comparator cannot see it and the hand transcription carried the wrong
    /// value for it. Pinned here as well as in `tests/crystal_a2_mint.rs`
    /// because a regeneration from a mutated core module would otherwise only
    /// fail in the gate, not beside the declaration it changes.
    #[test]
    fn test_exhaustive_enum_flag_is_the_measured_false() {
        assert!(
            minted("ir_h2_b0").ends_with("Bool.false)))"),
            "b0's switch must end in the measured exhaustive flag: {}",
            minted("ir_h2_b0")
        );
    }

    /// The emitted body joins through a block PARAMETER; the Level module never
    /// did, and dropping it would silently re-introduce the old wrong shape.
    #[test]
    fn test_join_block_takes_a_parameter() {
        assert!(minted("ir_h2_b4").contains("IRBlock.mk ir_d4 (ir_nl1 ir_d1)"));
        assert!(minted("ir_h2_b1").contains("IRInst.br ir_d4"));
        assert!(minted("ir_h2_b2").contains("IRInst.br ir_d4"));
        assert!(minted("ir_h2_b3").contains("IRInst.br ir_d4"));
    }

    /// There is no `unreachable` in the emitted body — exhaustiveness shows up
    /// as the default edge carrying `false`.
    #[test]
    fn test_no_unreachable_block() {
        assert!(
            !MINTED_IR_H2.contains("IRInst.unreachable"),
            "the emitted body has no trap block"
        );
    }

    /// Two SEPARATE true blocks, as emitted.
    #[test]
    fn test_two_distinct_true_arms() {
        assert!(minted("ir_h2_b1").contains("IRConst.bool_ Bool.true"));
        assert!(minted("ir_h2_b2").contains("IRConst.bool_ Bool.true"));
        assert_ne!(minted("ir_h2_b1"), minted("ir_h2_b2"));
    }

    /// The theorem stays universal, carries the fuel bound, and keeps the heap
    /// arbitrary.
    #[test]
    fn test_theorem_shape() {
        assert!(SRC_IR_H2_CORRECT.contains("(m : CleanModeR)"));
        assert!(SRC_IR_H2_CORRECT.contains("Le ir_d6 fuel ->"));
        assert!(!SRC_IR_H2_CORRECT.contains("ir_cell"));
    }

    /// A5 exists, composes with A4 through `ir_outcome_bool`, and is witnessed.
    ///
    /// It was deleted once, silently, during a re-authoring. Nothing failed:
    /// the axiom ratchet does not notice a MISSING theorem and the vacuity
    /// firewall audits relations, not definitions. This test is the thing that
    /// notices.
    #[test]
    fn test_a5_is_present_and_composes() {
        assert!(SRC_IR_H2_MACHINE_SOUND.contains("def ir_h2_machine_sound"));
        // The hypothesis is an observation about the MACHINE…
        assert!(SRC_IR_H2_MACHINE_SOUND.contains("ir_eval fuel ir_h2_module"));
        // …and the conclusion is about the reflected predicate.
        assert!(SRC_IR_H2_MACHINE_SOUND.contains(": Eq Bool (clean_mode_has_cubical m) Bool.true"));
        // It must go through A4, not restate it.
        assert!(SRC_IR_H2_MACHINE_SOUND.contains("ir_h2_correct mem fuel na r m henc hle"));
        // The projection that makes this an equality argument rather than an
        // inversion through three injectivity lemmas — and the reason this
        // stage must be registered after `add_eval_ir_correct`.
        assert!(SRC_IR_H2_MACHINE_SOUND.contains("ir_outcome_bool"));
        assert!(SRC_IR_H2_NEVER_FAULTS.contains("ir_outcome_is_ret"));
        // Non-vacuity: every premise discharged concretely at Directed.
        assert!(SRC_IR_H2_MACHINE_SOUND_WITNESS.contains("CleanModeR.directed"));
        assert!(SRC_IR_H2_MACHINE_SOUND_WITNESS.contains("Le.refl ir_d6"));
        assert!(SRC_IR_H2_MACHINE_SOUND_WITNESS.contains("EncodesCleanMode.mk"));
    }

    /// A5's fuel bound must match the transcribed module's cost. The deleted
    /// version said `ir_d5`, for the module that had one fewer step.
    #[test]
    fn test_a5_fuel_bound_matches_the_transcribed_module() {
        assert!(SRC_IR_H2_MACHINE_SOUND.contains("Le ir_d6 fuel"));
        assert!(SRC_IR_H2_NEVER_FAULTS.contains("Le ir_d6 fuel"));
        assert!(SRC_IR_H2_CORRECT.contains("Le ir_d6 fuel"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [
            SRC_CLEANMODER,
            SRC_ENCODESCLEANMODE,
            MINTED_IR_H2,
            SRC_IR_H2_EXACT,
            SRC_IR_H2_CORRECT,
            SRC_IR_H2_MACHINE_SOUND,
            SRC_IR_H2_MACHINE_SOUND_WITNESS,
            SRC_IR_H2_NEVER_FAULTS,
        ] {
            assert!(src.is_ascii());
            assert_eq!(src.matches('(').count(), src.matches(')').count());
        }
    }
}
