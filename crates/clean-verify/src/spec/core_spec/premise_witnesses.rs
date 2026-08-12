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
