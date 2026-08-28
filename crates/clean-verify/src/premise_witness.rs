// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Premise satisfiability — the gate the axiom census structurally cannot be.
//!
//! # Why this exists
//!
//! The def-eq completeness capstone `def_eq_fuel_complete` passed a census of **0
//! axioms, 0 domain axioms, 0 `DerivedProved` debt**, with every declaration
//! `DerivedProved` and an empty axiom closure — and proved nothing at all,
//! because its `hnf` premise is false (`hnf_is_false`, `core_spec/hnf_refutation.rs`).
//! Nine declarations inherited that premise and are equally empty.
//!
//! **Zero axioms is not zero assumptions.** An axiom-closure walk answers "what
//! does this trust?"; it cannot answer "can anything satisfy what this assumes?"
//! A conditional theorem whose premise set is unsatisfiable is not a weak result,
//! it is a non-result, and it looks identical to a strong one in every metric the
//! repo currently reports.
//!
//! # What this checks, precisely
//!
//! For every registered constant, the top-level hypotheses of its type (the `Pi`
//! domains). For each hypothesis whose head is *predicate-like* — a registered
//! inductive, or a definition whose own type concludes in a `Sort` — we ask
//! whether **any registered definition concludes that predicate**.
//!
//! Constructors and recursors are deliberately **excluded** from the supply side.
//! A constructor is a way to build `P` *if you already have its fields*; it is not
//! evidence that anything can. `iota_neutral.const` made `iota_neutral` look
//! inhabited for as long as it existed, while its `const_whnf` field had no
//! supply anywhere in the tree.
//!
//! # Would it have caught the case that motivated it? YES — measured, not assumed
//!
//! `hnf`'s conclusion is `nf_head r`, and before `nf_head_neutral_app_witness`
//! **nothing in the tree concluded `nf_head`**: its consumers conclude `Eq Nat`
//! (`nf_head_star_preserves_tag`, `nf_join_same_tag`), a `*Shape`
//! (`nf_tag_forces_*`), a `StuckAppRedWitness` (`nf_app_leg_inv`),
//! `DefEqFuelAccepts` (`def_eq_dispatch`) or `Empty` (`cx_not_nf_head`) — never
//! `nf_head` itself, and constructors are excluded from the supply side. So
//! `nf_head` would have been flagged, on the exact predicate the false premise
//! concludes. `const_whnf` and `iota_neutral` would have been flagged too.
//!
//! # What this does NOT check — stated plainly
//!
//! Still a **necessary condition, not a sufficient one**, in two ways.
//!
//! *Head-only.* It asks whether `P` is concluded by something, not whether `P` is
//! concluded *at the argument shapes actually needed*. `iota_immune` passes,
//! because `iota_immune_sort_witness` concludes it at a **sort** — and a sort is
//! not an application, so `nf_head.neutral`'s `iota_immune (app f a)` field had no
//! supply regardless. A green run is not a non-vacuity proof.
//!
//! *Noisy.* `concludes_in_sort` admits ordinary **data** types as well as
//! judgments, so a `Type`-valued parameter like `BinderData` or `Char` is reported
//! alongside genuine open obligations like `red_env_good` and `typing_is_def_eq`.
//! Nothing constructs a `BinderData` by definition, and nothing should have to.
//! Discriminating them mechanically — a judgment's head is *applied* to indices in
//! hypothesis position, a data parameter is not — is a worthwhile refinement, not
//! yet made.
//!
//! The stronger rule is a positive witness per **constructor arm** of every
//! predicate used in hypothesis position: the Guard-4 non-vacuity discipline
//! lifted from environments to predicates. `nf_head_neutral_app_witness` is what
//! satisfying it looks like for one arm.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::ConstantKind;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::Name;

use crate::spec::Specification;

/// A hypothesis whose predicate nothing in the spec concludes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnwitnessedPremise {
    /// The predicate that is assumed but never supplied.
    pub predicate: String,
    /// Declarations that assume it, sorted.
    pub carriers: Vec<String>,
}

/// Strip `Pi` binders, then the `App` spine, and report the head `Const`.
fn conclusion_head(mut e: &Expr) -> Option<Name> {
    while let ExprKind::Pi(_, _, body) = e.kind() {
        e = body;
    }
    let mut head = e;
    while let ExprKind::App(f, _) = head.kind() {
        head = f;
    }
    match head.kind() {
        ExprKind::Const(n, _) => Some(n.clone()),
        _ => None,
    }
}

/// Does this type conclude in a `Sort`? Such a definition is predicate-like:
/// `iota_immune : KExpr -> Type` is the shape that matters here.
fn concludes_in_sort(mut e: &Expr) -> bool {
    loop {
        match e.kind() {
            ExprKind::Pi(_, _, body) => e = body,
            ExprKind::Sort(_) => return true,
            _ => return false,
        }
    }
}

/// The head of every top-level hypothesis (each `Pi` domain) of a type.
fn hypothesis_heads(mut e: &Expr) -> Vec<Name> {
    let mut out = Vec::new();
    loop {
        match e.kind() {
            ExprKind::Pi(_, dom, body) => {
                if let Some(h) = conclusion_head(dom) {
                    out.push(h);
                }
                e = body;
            }
            _ => return out,
        }
    }
}

/// Predicates assumed somewhere in the spec that no registered definition
/// concludes.
///
/// See the module docs for exactly how strong this is — it is a necessary
/// condition, head-only, and it is documented where it is blind.
#[must_use]
pub fn unwitnessed_premises(spec: &Specification) -> Vec<UnwitnessedPremise> {
    let env = spec.env();

    // Supply side: what does some DEFINITION conclude? Constructors and
    // recursors are excluded on purpose — see the module docs.
    let mut concluded: BTreeSet<Name> = BTreeSet::new();
    // Demand side: which predicates are assumed, and by whom?
    let mut assumed: BTreeMap<Name, BTreeSet<String>> = BTreeMap::new();
    // Which names are predicate-like at all.
    let mut predicate_like: BTreeSet<Name> = BTreeSet::new();

    for c in env.constants() {
        let is_ctor = env.get_constructor(&c.name).is_some();
        let is_ind = env.get_inductive(&c.name).is_some();
        let is_rec = c.name.to_string().ends_with(".rec");

        if is_ind || concludes_in_sort(&c.type_) {
            predicate_like.insert(c.name.clone());
        }

        // A value-less constant assumes rather than supplies.
        let supplies = c.kind != ConstantKind::Axiom && !is_ctor && !is_rec && !is_ind;
        if supplies {
            if let Some(h) = conclusion_head(&c.type_) {
                concluded.insert(h);
            }
        }

        for h in hypothesis_heads(&c.type_) {
            assumed.entry(h).or_default().insert(c.name.to_string());
        }
    }

    let mut out: Vec<UnwitnessedPremise> = assumed
        .into_iter()
        .filter(|(p, _)| predicate_like.contains(p) && !concluded.contains(p))
        .map(|(p, carriers)| UnwitnessedPremise {
            predicate: p.to_string(),
            carriers: carriers.into_iter().collect(),
        })
        .collect();
    out.sort();
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    use clean_kernel::expr::BinderInfo;
    use clean_kernel::LevelVec;

    fn c(n: &str) -> Expr {
        Expr::const_(Name::from_string(n), LevelVec::new())
    }
    fn arrow(dom: Expr, cod: Expr) -> Expr {
        Expr::pi(BinderInfo::Default, dom, cod)
    }

    /// `conclusion_head` must look through both `Pi` binders and the `App` spine.
    /// Reporting the applied predicate rather than its head is the mistake that
    /// would make the whole gate silently pass everything.
    #[test]
    fn test_conclusion_head_strips_pis_and_spine() {
        // A -> P x  ==>  head is P
        let ty = arrow(c("A"), Expr::app(c("P"), Expr::bvar(0)));
        assert_eq!(
            conclusion_head(&ty).map(|n| n.to_string()),
            Some("P".to_string())
        );
    }

    /// A hypothesis is a `Pi` DOMAIN; the conclusion is not a hypothesis.
    #[test]
    fn test_hypothesis_heads_are_domains_only() {
        let ty = arrow(c("H"), c("G"));
        let heads: Vec<String> = hypothesis_heads(&ty)
            .iter()
            .map(|n| n.to_string())
            .collect();
        assert_eq!(heads, vec!["H".to_string()], "G is concluded, not assumed");
    }

    /// `iota_immune : KExpr -> Type` is predicate-like; `f : KExpr -> KExpr` is not.
    /// Without this distinction the gate would demand witnesses for every
    /// function type in the spec and drown in noise.
    #[test]
    fn test_concludes_in_sort_distinguishes_predicates_from_functions() {
        assert!(
            concludes_in_sort(&arrow(c("KExpr"), Expr::type_())),
            "KExpr -> Type is predicate-like"
        );
        assert!(
            !concludes_in_sort(&arrow(c("KExpr"), c("KExpr"))),
            "KExpr -> KExpr is not"
        );
    }

    /// THE GATE MUST SEE THE WITNESS — not merely that one was written.
    ///
    /// `unwitnessed_premises` is HEAD-ONLY and purely syntactic, so a witness
    /// counts only if the predicate survives as the head of its stored type.
    /// `outParam` is the standing counterexample: two attempts to witness it
    /// both stayed flagged. These five were the 2026-08-24 finding against the
    /// CandModel ladder; each now has a registered conclusion in its own rung
    /// (`candCr3_whnfAcc`, `piSet_id_witness`, `candStepInv_const` +
    /// `candStepInv_interp_witness`, `simpleTy_arrow_witness`,
    /// `hk_nonpi_flag_witness`), and this pins that the gate agrees.
    ///
    /// The three typing judgments are here for the same reason and NOT because
    /// they were ever flagged: each is assumed by its own fundamental
    /// theorem and capstones, and each is concluded only by registered
    /// definitions (`synTy_id` / `synTy_sort_witness` / `synTy_app_witness`;
    /// `synTyT_id` / `synTyT_sort_witness` / `synTyT_app_witness` /
    /// `synTyT_lam_redex_witness`; `synTyL_id` / `synTyL_sort_witness` /
    /// `synTyL_var_lift_witness` / `synTyL_pi_formation_witness` /
    /// `synTyL_let_witness`; `synTyC_id` / `synTyC_sort_witness` /
    /// `synTyC_konst_dead_witness`; `synTyP_id` / `synTyP_sort_witness` /
    /// `synTyP_konst_pi_witness` / `synTyP_convI_witness` / `synTyC_to_synTyP` /
    /// `r11_synTyP_unlift_type`) — a CONSTRUCTOR is not a witness on the
    /// supply side, so deleting any of those definitions would silently make
    /// the rung's capstone unsatisfiable-in-hypothesis. `CtxSimple` (R8) is a
    /// `def`, so it has no constructors at all and every witness must be a
    /// registered definition: `ctxSimple_nil` and `ctxSimple_cons`.
    #[test]
    fn test_candmodel_ladder_premises_are_witnessed() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();
        let live: BTreeSet<String> = unwitnessed_premises(&spec)
            .into_iter()
            .map(|u| u.predicate)
            .collect();
        for predicate in [
            "candCr1",
            "candCr2",
            "candCr3",
            "PiSet",
            "candStepInv",
            "SimpleTy",
            "hk_nonpi_flag",
            "SynTy",
            "SynTyT",
            "SynTyL",
            "SynTyC",
            "SynTyP",
            "CtxSimple",
            "HeadInert",
            "candCr3HI",
            "IsCandHI",
            // R12 (the shape / denotation split), every predicate it introduces
            // in hypothesis position. `Sk` is concluded by `domSk`, `Val` by
            // `valJunk`, `WK` by `r12_wk_sort_witness` / `r12_wk_id_witness` /
            // `r12_wk_pi_witness`, `VD` by `junkD`, `VEnvD` by `r12_junkEnv`,
            // `GoodSet` by `goodSet_whnfAcc`, `GoodD` by `goodD_junkD`,
            // `GoodEnvD` by `goodEnvD_junk`, `vcarD` by
            // `r12_sval_pi_var_witness`, `valGood` by `valGood_junk`,
            // `piCodDepIdx` by `piCodDepIdx_var_witness`, `piCodDep` by
            // `piCodDep_intro`, `piCandDep` by `piCandDep_intro`, `wkPiDep` by
            // `wkPiDep_intro` and `piCandV` by `piCandV_intro`. All fifteen are
            // `def`s or inductives whose CONSTRUCTORS do not count on the supply
            // side, so each witness is a registered definition.
            // `test_candmodel_r12_introduces_no_unwitnessed_premise` is the
            // drift-proof form of the same check: it derives the name set from
            // the rung's own source tables instead of this hand-written list.
            "Sk",
            "Val",
            "WK",
            "VD",
            "VEnvD",
            "GoodSet",
            "GoodD",
            "GoodEnvD",
            "vcarD",
            "valGood",
            "piCodDepIdx",
            "piCodDep",
            "piCandDep",
            "wkPiDep",
            "piCandV",
            // R13 (funext, DERIVED). `spec_fneq` is assumed by `spec_fnapp`'s
            // respect-proof binder and concluded by `spec_fneq_intro`.
            // `Quot` is the one this rung newly puts in hypothesis position —
            // `spec_fnapp`'s own `q` binder, and `Quot.lift`/`Quot.ind`'s — and
            // it is a value-less CIC type former, which the gate excludes from
            // the supply side, so it needs the concluding DEFINITION
            // `spec_quot_fn`. `test_candmodel_r13_introduces_no_unwitnessed_
            // premise` is the drift-proof form of the same check.
            "spec_fneq",
            "Quot",
            // R14 (the weakening and substitution OPERATIONS). This rung puts
            // no NEW predicate in hypothesis position: every hypothesis it
            // introduces is headed by `WK` (`wk_up`/`wk_psub`/`wk_inst`'s
            // shape-typing premises), by `VEnvD` (every valuation binder) or by
            // `Eq`. `WK` is concluded here by the operations themselves —
            // `wk_lift`, `wk_lift0`, `wk_up`, `wk_psub`, `wk_inst`,
            // `r14_scons_typed`, `r14_wk_lift_var` and the two registered
            // witnesses `r14_wk_lift_witness` / `r14_wk_inst_witness`, all
            // `def`s — and `VEnvD` by `venvLiftD` / `venvSubD` beside R12's
            // `r12_junkEnv`. Both names are already listed above, so the entry
            // for this rung is the re-assertion rather than a new row;
            // `test_candmodel_r14_introduces_no_unwitnessed_premise` is the
            // drift-proof form, deriving the set from R14's own table so a
            // later edit that DOES introduce one cannot slip past this list.
            //
            // R15 (SUBJECT REDUCTION for shapes). Same situation, re-asserted
            // rather than extended: every hypothesis this rung introduces is
            // headed by `WK` (`wk_step`'s subject, `r15_wk_lam_inv`'s and
            // `r15_sval_lam_inv`'s continuations, and `r15_val_step_sem`'s),
            // by `HeadFree` (`r15_beta_stepT_inv` / `r15_whnf_stepT_inv`), by
            // `whnf_step` / `beta_reduces` / `whnfStar`, by `VEnvD`, by `vcarD`
            // or by `Eq`. `WK` gains a further CONCLUDING `def` here —
            // `wk_step` itself, beside `r15_wk_lam_inv`, `r15_instDeriv`,
            // `r15_piCodDeriv`, `r15_piRedexDeriv`, `r15_piReductDeriv` and
            // `r15_wk_step_witness`; `HeadFree` is concluded by
            // `r15_headFree_wk` (and already by R5's `headFree_app`);
            // `whnf_step` by `r15_piCongr_step` beside R14's `r14_beta_step`;
            // and `whnfStar` by R1's own constructors. The computed-motive
            // types `r15_stepT` / `r15_wkLamT` / `r15_svalLamT` are never in
            // hypothesis position — they are RESULT types.
            // `test_candmodel_r15_introduces_no_unwitnessed_premise` is the
            // drift-proof form.
            //
            // R16 (SVAL DERIVATION IRRELEVANCE). This rung puts exactly ONE new
            // predicate in hypothesis position: `PropBox`, the Prop-to-Type
            // bridge `r16_unbox` consumes, which exists because R15's
            // `r15_val_step_sem` / `r15_val_star_sem` quantify their continuation
            // over `C : Type` while the forall-form of `val_step` concludes an
            // `Eq` — a Prop — and the kernel is NON-CUMULATIVE. Its constructor
            // `PropBox.mk` does not count on the supply side (the R12 rule), so
            // the concluding DEFINITION `r16_propBox_intro` is what witnesses it.
            // Everything else this rung assumes is headed by `WK` (concluded here
            // by `r16_wkCastS`, `r16_convDeriv2` and already by R12/R14/R15), by
            // `VEnvD`, by `whnfStar` (concluded by `r16_convStar1` /
            // `r16_convStar2`), by `whnf_step` (by `r16_convStep2`), by `vcarD`
            // or by `Eq`. The computed-motive type `r16_wkT` and the shape
            // function `r16_shapeOf` are never in hypothesis position — they are
            // RESULT types. `test_candmodel_r16_introduces_no_unwitnessed_premise`
            // is the drift-proof form.
            "PropBox",
            // R17 (THE CONSTRUCTOR GAP: `const` and `let_` on the `WK`/`sval`
            // lineage). This rung puts exactly TWO new predicates in hypothesis
            // position, and both are inductives whose CONSTRUCTORS do not count
            // on the supply side (the R12 rule), so each needs a concluding
            // DEFINITION.
            //
            // `WKC` — the seven-constructor shape system — is assumed by every
            // operation (`wkc_lift`, `wkc_up`, `wkc_psub`, `wkc_inst`,
            // `wkc_step`), by `xval`, by the inversion's continuations and by
            // `r17_xval_irrel`; it is concluded here by those same operations
            // (all `def`s), by the embedding `r17_wk_wkc`, by the transports
            // `r17_wkcCastS` / `r17_wkcCastT`, by `r17_wkc_lift_var` /
            // `r17_scons_typed`, and by the registered witnesses
            // `r17_konst_witness`, `r17_let_witness`,
            // `r17_wkc_step_let_witness` and `r17_wkc_lift_konst_witness`.
            //
            // `WKV` — the conversion-rule PROBE — is assumed by
            // `r17_wkv_shape_correct`, `r17_conv_shape_unique` and
            // `r17_wkv_tag`, and is concluded by the definition
            // `r17_convDeriv`. It exists to SETTLE the question (shape
            // uniqueness survives a conversion rule; derivation uniqueness does
            // not) and is deliberately not built on.
            //
            // Everything else this rung assumes is headed by `HeadFree` /
            // `HeadInert` (already listed, and concluded here by
            // `r17_headFree_wkc_arr` / `r17_headInert_wkc`), by `whnf_step`, by
            // `VEnvD`, by `vcarD`, by `Empty` or by `Eq`. The computed-motive
            // types `r17_wkcT` / `r17_wkcLamT`, the discriminators
            // `r17_notArrT` / `r17_zeroT` and the shape function `r17_shapeOf`
            // are never in hypothesis position — they are RESULT types.
            // `test_candmodel_r17_introduces_no_unwitnessed_premise` is the
            // drift-proof form.
            "WKC",
            "WKV",
        ] {
            assert!(
                !live.contains(predicate),
                "{predicate} is assumed in the spec and concluded by nothing the gate can see. \
                 A witness whose stored type does not keep {predicate} as its syntactic head \
                 does not count — see the outParam entry in \
                 data/premise_witness_ratchet.json."
            );
        }
    }

    /// Nested hypotheses: `H1 -> H2 -> G` assumes two things.
    #[test]
    fn test_multiple_hypotheses_are_all_collected() {
        let ty = arrow(c("H1"), arrow(c("H2"), c("G")));
        let heads: Vec<String> = hypothesis_heads(&ty)
            .iter()
            .map(|n| n.to_string())
            .collect();
        assert_eq!(heads, vec!["H1".to_string(), "H2".to_string()]);
        assert_eq!(
            conclusion_head(&ty).map(|n| n.to_string()),
            Some("G".to_string())
        );
    }
}
