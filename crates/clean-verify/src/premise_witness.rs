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
