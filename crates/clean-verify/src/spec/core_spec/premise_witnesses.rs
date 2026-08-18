// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Non-vacuity witnesses for the predicates the premise-satisfiability gate
//! reports as **assumed but never concluded**.
//!
//! The gate states the principle better than a comment could:
//!
//! > A conditional theorem whose premises cannot be satisfied is not a weak
//! > result, it is a NON-result — and it passes the axiom census, the
//! > domain-axiom count and the `DerivedProved`-debt count while looking green.
//!
//! Every predicate here is now **concluded by a real term**. Nothing is blessed
//! into `data/premise_witness_ratchet.json`; blessing is precisely the move the
//! gate exists to prevent.
//!
//! # Why these live together rather than in their home lanes
//!
//! They span three lanes — EvalIR (C3), the `ImplInfer` mode gate (C1), and the
//! faithful-whnf work — and each witness is a single constructor application or
//! one `Eq.refl`. Splitting them across three modules would put a terminal
//! registration order constraint on each of those lanes for no benefit. This
//! module is registered last and depends on all of them.
//!
//! # The two that are not one-liners
//!
//! `WhNormalizes` and `WhNormalizes3` are *derivations*, not data. Their `stuck`
//! constructors demand that the term take no step **at every fuel budget**, which
//! is a `forall (j : Nat)` premise. `KExpr.sort Level.zero` satisfies it because
//! `reduce_once_red_wh` pattern-matches a sort and returns `none` without ever
//! consulting the budget — so the proof is `fun j => Eq.refl …`, uniform in `j`.
//! `wh_fuel_adequacy.rs`'s own registration says as much ("sort 0 takes no step
//! at any budget, so `stuck` applies"); it was simply never written down, which
//! is exactly the gap this gate is built to surface.
//!
//! ZERO new axioms: every declaration is a valued definition, `DerivedProved`,
//! with an empty axiom closure.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

/// `(name, type, value, why)` for every witness that is a plain constructor
/// application.
const SIMPLE: &[(&str, &str, &str, &str)] = &[
    // ── the ImplInfer mode gate (C1) ────────────────────────────────────────
    (
        "cleanmodem_witness",
        "CleanModeM",
        "CleanModeM.constructive",
        "CleanModeM IS INHABITED, and at the constructor that matters: `constructive` is the \
         #[default] mode (mode.rs:29-36), the one every declaration is actually admitted \
         through, and the one the mode-gate side lemma is stated about. A mode model nothing \
         inhabits would make that lemma vacuous.",
    ),
    // ── EvalIR syntax (C3) ──────────────────────────────────────────────────
    (
        "irbinop_witness",
        "IRBinOp",
        "IRBinOp.add",
        "IRBinOp IS INHABITED.",
    ),
    (
        "irunop_witness",
        "IRUnOp",
        "IRUnOp.neg",
        "IRUnOp IS INHABITED.",
    ),
    (
        "ircastop_witness",
        "IRCastOp",
        "IRCastOp.trunc",
        "IRCastOp IS INHABITED.",
    ),
    (
        "iricmpop_witness",
        "IRICmpOp",
        "IRICmpOp.eq_",
        "IRICmpOp IS INHABITED.",
    ),
    (
        "irfcmpop_witness",
        "IRFCmpOp",
        "IRFCmpOp.oeq",
        "IRFCmpOp IS INHABITED.",
    ),
    (
        "iroverflowop_witness",
        "IROverflowOp",
        "IROverflowOp.addoverflow",
        "IROverflowOp IS INHABITED.",
    ),
    (
        "irconst_witness",
        "IRConst",
        "IRConst.int_ Nat.zero",
        "IRConst IS INHABITED.",
    ),
    (
        "irglobal_witness",
        "IRGlobal",
        "IRGlobal.mk Nat.zero (IRConst.int_ Nat.zero)",
        "IRGlobal IS INHABITED — a global with an integer initializer, the shape \
         `Inst::GlobalAddr` resolves against.",
    ),
    (
        "irswitchcase_witness",
        "IRSwitchCase",
        "IRSwitchCase.mk Nat.zero Nat.zero (IRList.nil Nat)",
        "IRSwitchCase IS INHABITED — one Switch arm with no block arguments.",
    ),
    (
        "irinst_witness",
        "IRInst",
        "IRInst.binop IRBinOp.add IRTy.bool_ Nat.zero Nat.zero",
        "IRInst IS INHABITED. This is the one that matters most of the EvalIR group: IRInst is \
         the instruction type the whole step relation is indexed by, so an uninhabited IRInst \
         would make every EvalIR execution theorem vacuous at once.",
    ),
    // ── EvalIR machine state (C3) ───────────────────────────────────────────
    (
        "irbinding_witness",
        "IRBinding",
        "IRBinding.mk Nat.zero IRScalar.undef_",
        "IRBinding IS INHABITED — one SSA binding. `undef_` is deliberate: it is the value a \
         freshly-minted binding actually holds before anything writes it.",
    ),
    (
        "irmemslot_witness",
        "IRMemSlot",
        "IRMemSlot.mk Nat.zero IRScalar.undef_ Bool.false",
        "IRMemSlot IS INHABITED — one memory cell. `undef_` again, and dead: exactly the state \
         Alloca creates, and loading it is UB.",
    ),
    (
        "irfault_witness",
        "IRFault",
        "IRFault.no_frame",
        "IRFault IS INHABITED. A fault type nothing inhabits would make every \
         does-not-fault claim trivially true.",
    ),
    (
        "irf64class_witness",
        "IRF64Class",
        "IRF64Class.fin_",
        "IRF64Class IS INHABITED, at the FINITE class — the one the eighth chain's \
         division-by-zero corollary assumes of its dividend. The binary64 value domain's whole \
         dispatch is indexed by this type, so an uninhabited one would make every classified \
         float table vacuous at once.",
    ),
    // ── the reflected ARGUMENT types of chains 3, 4 and 5 ───────────────────
    //
    // Each is the type a chain's A4 quantifies over. An uninhabited one makes
    // that A4 — and every A5 corollary that goes through it — vacuously true
    // with an impeccable axiom closure, which is the exact failure this gate
    // exists to catch. `SourceSystemR` had been assumed since the third chain
    // was registered and concluded by nothing; that is the gap, not a new one.
    (
        "sourcesystemr_witness",
        "SourceSystemR",
        "SourceSystemR.lean4",
        "SourceSystemR IS INHABITED, at `lean4` — the source system the import path this \
         reflects is actually built around, and the arm `CleanMode::from_source_system` maps \
         to the non-cubical constructive mode.",
    ),
    (
        "flatflagsr_witness",
        "FlatFlagsR",
        "FlatFlagsR.mk Nat.zero",
        "FlatFlagsR IS INHABITED, at the EMPTY flag set — `FlatFlags::empty()`, the value the \
         fourth chain's own `any-contains-empty` witness runs the emitted body on.",
    ),
    // The SEVENTH chain's reflected argument type. Registered with its chain
    // rather than after a gate found it missing, which is the whole point of
    // the lesson `SourceSystemR` cost: that one was assumed from the third
    // chain onward and concluded by nothing until a later lane noticed.
    (
        "exprpathstepr_witness",
        "ExprPathStepR",
        "ExprPathStepR.projexpr",
        "ExprPathStepR IS INHABITED, at `projexpr` — deliberately the variant on the emitted \
         switch's DEFAULT edge rather than one with an explicit case, so the witness names the \
         arm a case-table transcription is most likely to lose.",
    ),
];

impl Specification {
    /// Register a witness for every predicate the premise gate reports.
    pub(super) fn add_premise_witnesses(&mut self) -> Result<(), SpecError> {
        for (name, ty, val, why) in SIMPLE {
            self.add_definition(SpecDefinition {
                name: (*name).to_string(),
                type_src: (*ty).to_string(),
                value_src: Some((*val).to_string()),
                is_axiom: false,
                description: format!("{why} Zero axiom_deps."),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: None,
                axiom_deps: HashSet::new(),
            })?;
        }

        // ── the by-value representation premises of chains 3, 4 and 5 ──────
        //
        // All three constrain no memory at all: the bodies they belong to take
        // their arguments by value and perform no load. That is what makes them
        // the thinnest premises in the program and the ones most in need of a
        // witness — there is almost nothing left to remove before they say
        // nothing, and an empty one takes `ir_fs_correct` / `ir_fc_correct` /
        // `ir_br_correct` with it.
        self.add_definition(SpecDefinition {
            name: "encodessourcesystemval_witness".to_string(),
            type_src: "EncodesSourceSystemVal \
                       (ir_var (source_system_tag SourceSystemR.lean4) ir_sp0) \
                       SourceSystemR.lean4"
                .to_string(),
            value_src: Some("EncodesSourceSystemVal.mk SourceSystemR.lean4 ir_sp0".to_string()),
            is_axiom: false,
            description: concat!(
                "EncodesSourceSystemVal IS INHABITED. It is the third chain's representation ",
                "premise — \"this runtime value is this source system\" — and it had been ",
                "assumed since that chain was registered with nothing concluding it. The ",
                "witness is the tagged aggregate at `lean4` over the empty payload spine, ",
                "which is exactly the shape the constructor demands. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "EncodesSourceSystemVal.mk".to_string(),
                "source_system_tag".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "encodesflatflags_witness".to_string(),
            type_src: "EncodesFlatFlags \
                       (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ Nat.zero) ir_sp0)) \
                       (FlatFlagsR.mk Nat.zero)"
                .to_string(),
            value_src: Some("EncodesFlatFlags.mk Nat.zero ir_sp0".to_string()),
            is_axiom: false,
            description: concat!(
                "EncodesFlatFlags IS INHABITED. The fourth chain's representation premise, at ",
                "the empty flag set over the empty payload spine. The relation is ",
                "spine-agnostic past field 0 by design, so the witness pins the one field it ",
                "does constrain and leaves the rest where the relation leaves it. ",
                "Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["EncodesFlatFlags.mk".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "encodesu32val_witness".to_string(),
            type_src: "EncodesU32Val (IRScalar.int_ Nat.zero) Nat.zero".to_string(),
            value_src: Some("EncodesU32Val.mk Nat.zero".to_string()),
            is_axiom: false,
            description: concat!(
                "EncodesU32Val IS INHABITED. The fifth chain's representation premise and the ",
                "THINNEST in the whole program: it says only that a u32 argument arrived as an ",
                "integer scalar rather than as a pointer, a bool or an undef. Thin is not ",
                "empty, and this is the term that says so — without it `ir_br_correct` would ",
                "be a theorem about arguments nothing can supply. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["EncodesU32Val.mk".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "encodesu64val_witness".to_string(),
            type_src: "EncodesU64Val (IRScalar.int_ Nat.zero) Nat.zero".to_string(),
            value_src: Some("EncodesU64Val.mk Nat.zero".to_string()),
            is_axiom: false,
            description: concat!(
                "EncodesU64Val IS INHABITED. The sixth chain's representation premise, which ",
                "ties `EncodesU32Val` for thinnest in the program: it says only that a u64 ",
                "argument arrived as an integer scalar rather than as a pointer, a bool or an ",
                "undef. It is a separate relation rather than a reuse because that one is ",
                "named for a width and this body is at another, and a false name is what these ",
                "gates read. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["EncodesU64Val.mk".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "encodesf64val_witness".to_string(),
            type_src: "EncodesF64Val (IRScalar.float_ Nat.zero) Nat.zero".to_string(),
            value_src: Some("EncodesF64Val.mk Nat.zero".to_string()),
            is_axiom: false,
            description: concat!(
                "EncodesF64Val IS INHABITED, at `+0.0`. The eighth chain's representation ",
                "premise. It has the same shape as `EncodesU64Val` and is deliberately NOT a ",
                "reuse of it, and here the difference is not only naming discipline: that one ",
                "concludes at `IRScalar.int_`, `ir_as_float` DECLINES `IRScalar.int_`, and so ",
                "`ir_fd_correct` with `EncodesU64Val` in its place would be FALSE rather than ",
                "merely misnamed — the machine answers `type_error not_float` where the theorem ",
                "claims a value. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["EncodesF64Val.mk".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // ── the seventh chain's BY-REFERENCE representation premise ─────────
        //
        // Unlike the three above it constrains MEMORY: the derived clone body
        // takes `&self` and loads through it, so there is a cell to pin. The
        // heap equation is discharged by `Eq.refl`, so the KERNEL runs
        // `ir_mem_lookup` over a one-cell heap and compares — nothing is
        // asserted.
        let step_cell = "(ir_cell Nat.zero \
                          (ir_var (expr_path_step_tag ExprPathStepR.projexpr) ir_sp0) \
                          ir_mem0)";
        self.add_definition(SpecDefinition {
            name: "encodesexprpathstep_witness".to_string(),
            type_src: format!(
                "EncodesExprPathStep {step_cell} (IRScalar.ptr_ Nat.zero) ExprPathStepR.projexpr"
            ),
            value_src: Some(format!(
                "EncodesExprPathStep.mk {step_cell} Nat.zero ExprPathStepR.projexpr ir_sp0 \
                 (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk Nat.zero \
                 (ir_var (expr_path_step_tag ExprPathStepR.projexpr) ir_sp0) Bool.true)))"
            )),
            is_axiom: false,
            description: concat!(
                "EncodesExprPathStep IS INHABITED. The seventh chain's representation premise, ",
                "at the variant on the switch's default edge, over a one-cell heap holding it. ",
                "The heap condition is an equation on `ir_mem_lookup` rather than a membership ",
                "claim — a membership premise would be satisfiable by a SHADOWED duplicate ",
                "while the machine reads a different cell — and it is discharged by Eq.refl, so ",
                "the kernel runs the lookup. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "EncodesExprPathStep.mk".to_string(),
                "expr_path_step_tag".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── arrivals from the eval_ir mode lane, and one kernel builtin ─────
        let mode_cell = "(ir_cell Nat.zero \
                         (ir_var (clean_mode_tag CleanModeR.constructive) ir_sp0) \
                         (IRList.nil IRMemSlot))";
        self.add_definition(SpecDefinition {
            name: "cleanmoder_witness".to_string(),
            type_src: "CleanModeR".to_string(),
            value_src: Some("CleanModeR.constructive".to_string()),
            is_axiom: false,
            description: concat!(
                "CleanModeR IS INHABITED, at `constructive` — the same choice as ",
                "cleanmodem_witness and for the same reason: it is the mode every declaration ",
                "is actually admitted through. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "encodescleanmode_witness".to_string(),
            type_src: format!(
                "EncodesCleanMode {mode_cell} (IRScalar.ptr_ Nat.zero) CleanModeR.constructive"
            ),
            value_src: Some(format!(
                "EncodesCleanMode.mk {mode_cell} Nat.zero CleanModeR.constructive \
                 (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot \
                 (IRMemSlot.mk Nat.zero \
                 (ir_var (clean_mode_tag CleanModeR.constructive) ir_sp0) Bool.true)))"
            )),
            is_axiom: false,
            description: concat!(
                "EncodesCleanMode IS INHABITED. It is the representation premise the eval_ir ",
                "mode lane's theorems are conditional on — \"this pointer, in this memory, ",
                "encodes this mode\" — so nothing inhabiting it would make those theorems ",
                "claims about a machine state that cannot exist. ",
                "The witness is the smallest such state: a single LIVE cell (ir_cell builds ",
                "exactly the `IRMemSlot.mk a v Bool.true` the constructor demands) holding the ",
                "tag of the constructive mode at address zero. ir_mem_lookup finds it at the ",
                "head, so the premise COMPUTES and closes by Eq.refl. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "EncodesCleanMode.mk".to_string(),
                "ir_cell".to_string(),
                "ir_var".to_string(),
                "clean_mode_tag".to_string(),
                "ir_mem_lookup".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── the faithful-whnf derivations ───────────────────────────────────
        // `stuck` demands no step at EVERY budget. A sort is a leaf, so
        // `reduce_once_red_wh` returns `none` without consulting the budget and
        // the proof is uniform in `j`.
        self.add_definition(SpecDefinition {
            name: "whnormalizes_witness".to_string(),
            type_src: "WhNormalizes (KExpr.sort Level.zero) (KExpr.sort Level.zero)".to_string(),
            value_src: Some(
                concat!(
                    "WhNormalizes.stuck (KExpr.sort Level.zero) ",
                    "(fun (j : Nat) => Eq.refl (OptionType KExpr) (OptionType.none KExpr))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "WhNormalizes IS INHABITED. Its `stuck` constructor demands the term take no ",
                "step AT EVERY FUEL BUDGET — a `forall (j : Nat)` premise, not a single ",
                "check — and `KExpr.sort Level.zero` satisfies it because reduce_once_red_wh ",
                "pattern-matches a sort and returns `none` without ever consulting the budget. ",
                "So the proof is uniform in j and is one Eq.refl. ",
                "wh_fuel_adequacy.rs's own registration already says this (\"sort 0 takes no ",
                "step at any budget, so `stuck` applies\") — it was simply never written down, ",
                "which is exactly the gap the premise gate exists to surface: a relation whose ",
                "satisfiability is asserted in prose and nowhere in the environment. ",
                "Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "WhNormalizes.stuck".to_string(),
                "reduce_once_red_wh".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnormalizes3_witness".to_string(),
            type_src: "WhNormalizes3 (KExpr.sort Level.zero) (KExpr.sort Level.zero)".to_string(),
            value_src: Some(
                concat!(
                    "WhNormalizes3.stuck (KExpr.sort Level.zero) Nat.zero ",
                    "(Eq.refl WhStepR WhStepR.wstuck)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "WhNormalizes3 IS INHABITED. The level-three loop reports stuckness through a ",
                "THREE-VALUED result (WhStepR) rather than an OptionType, so its stuck premise ",
                "is `wh3_stuck_at j r` at a single budget rather than a forall — and at a sort ",
                "it computes to WhStepR.wstuck, closing by Eq.refl. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "WhNormalizes3.stuck".to_string(),
                "wh3_stuck_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "defeqfuelacceptswh_witness".to_string(),
            type_src: "DefEqFuelAcceptsWh (KExpr.sort Level.zero) (KExpr.sort Level.zero)"
                .to_string(),
            value_src: Some(
                concat!(
                    "DefEqFuelAcceptsWh.mk (KExpr.sort Level.zero) (KExpr.sort Level.zero) ",
                    "(Nat.succ (Nat.succ Nat.zero)) (Eq.refl Bool Bool.true)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "DefEqFuelAcceptsWh IS INHABITED. TWO units of fuel, not one, and the off-by-one is ",
                "the algorithm failing CLOSED as designed: def_eq_fuel spends one unit on its own ",
                "Nat.rec and hands `fuel - 1` to the whnf loop, so fuel 1 gives the loop ZERO and it              returns none -> false. At fuel 2 the loop has one unit, finds a sort takes no step,              and def_eq_struct compares them equal — so the checker COMPUTES to true and the              premise is Eq.refl. Without this, def_eq_fuel_wh_sound is a theorem about ",
                "an acceptance nothing exhibits. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEqFuelAcceptsWh.mk".to_string(),
                "def_eq_fuel_wh".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }
}
