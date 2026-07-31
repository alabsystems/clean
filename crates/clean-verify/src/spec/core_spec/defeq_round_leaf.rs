// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Completeness rounds at the **leaf** heads: `sort`, `lit`, `const`.
//!
//! ```text
//! def_eq_round_sort :
//!   (hnf) -> whnf_fuel_red the_red_env n x = some (sort u1)
//!         -> whnf_fuel_red the_red_env n bb = some nb
//!         -> par_strips_witness_cd_star the_red_env (sort u1) nb
//!         -> DefEqFuelAccepts x bb
//! ```
//!
//! ## No recursion parameter
//!
//! These take no `recur`. There is nothing below a `sort`, `lit` or `const` to
//! recurse into, so unlike the binder and application rounds they close outright.
//! That asymmetry is real and worth keeping visible: a leaf round that carried a
//! recursion hypothesis would suggest it descends, which it does not.
//!
//! ## Where the payload equality comes from
//!
//! `def_eq_complete_leaf_*` needs the two payloads to agree, and this is where
//! that is discharged. Both normal forms reduce to a common `w`; each is rigid,
//! so its star inversion pins `w` to be *that very term*. Two descriptions of
//! one `w`, composed, give `sort u1 = sort u2` — and constructor injectivity
//! gives `u1 = u2`.
//!
//! `lit` needed a new injectivity (`kexpr_lit_inj`); the tree had `sort`,
//! `bvar`, `lam`, `pi` and both `const` projections but not `lit`. It is built
//! here by the same `KExpr.rec`-projection pattern the `proj` injectivities use.
//!
//! ## The `const` case pays for itself
//!
//! `par_reduces_cd_star_const_dead_inv_eq` needs δ-deadness of the constant, and
//! the shape witness does not carry it — `ConstShape` says only *that* the term
//! is a constant. It is recovered instead from the loop: a successful
//! `whnf_fuel_red` has no executable step (`whnf_fuel_red_no_redex`), and on a
//! constant that is exactly δ-deadness (`reduce_once_red_none_delta_none`).
//!
//! So the fact is derived from the algorithm having *stopped there*, not assumed
//! — which is the honest source for it.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The hereditary normal-form-head hypothesis, as in the other rounds.
const HNF: &str = "(hnf : forall (m : Nat) (e : KExpr) (r : KExpr), \
     Eq (OptionType KExpr) (whnf_fuel_red the_red_env m e) (OptionType.some KExpr r) -> \
     nf_head r) ";

impl Specification {
    /// Rounds at the component-free heads.
    pub(super) fn add_defeq_round_leaf(&mut self) -> Result<(), SpecError> {
        self.add_lit_injectivity()?;
        self.add_leaf_rounds()?;
        Ok(())
    }

    /// The one missing constructor injectivity.
    fn add_lit_injectivity(&mut self) -> Result<(), SpecError> {
        let default = "Nat.zero";
        self.add_recursive_def(
            &format!(
                "def kexpr_lit_inj (v1 : Nat) (v2 : Nat) \
                 (h : Eq KExpr (KExpr.lit v1) (KExpr.lit v2)) : Eq Nat v1 v2 := \
                 Eq.cong KExpr Nat \
                 (fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => Nat) \
                 (fun (_ : Level) => {default}) \
                 (fun (_ : Nat) => {default}) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : Nat) (_ : Nat) => {default}) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : Nat) (_ : Nat) => {default}) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : Nat) (_ : Nat) => {default}) \
                 (fun (_ : Name) (_ : ListType Level) => {default}) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Nat) (_ : Nat) (_ : Nat) => \
                 {default}) \
                 (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Nat) => {default}) \
                 (fun (lv : Nat) => lv) e) \
                 (KExpr.lit v1) (KExpr.lit v2) h"
            ),
            "kexpr_lit_inj: literal injectivity. The tree had sort, bvar, lam, pi and both const \
             projections but not lit, so it is built here by the same KExpr.rec-projection pattern \
             the proj injectivities use (expr_model_discrimination_let.rs:361): read the payload \
             off with a total function whose other eight arms return a default, then Eq.cong. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_leaf_rounds(&mut self) -> Result<(), SpecError> {
        for (src, desc) in Self::leaf_round_decls() {
            self.add_recursive_def(&src, &desc)?;
        }
        Ok(())
    }

    fn leaf_round_decls() -> Vec<(String, String)> {
        // (head, left binders, left form, shape witness, forcing lemma,
        //  shape-arm binders, right form, star inversion + extra args,
        //  payload equality derivation, leaf step application)
        let sort = (
            "sort",
            "(u1 : Level)",
            "(KExpr.sort u1)",
            "SortShape",
            "nf_tag_forces_sort u1",
            "(u2 : Level)",
            "(KExpr.sort u2)",
            "par_reduces_cd_star_sort_inv_eq the_red_env",
            "kexpr_sort_inj u1 u2",
            "def_eq_complete_leaf_sort n x bb u1 u2",
            "",
        );
        let lit = (
            "lit",
            "(v1 : Nat)",
            "(KExpr.lit v1)",
            "LitShape",
            "nf_tag_forces_lit v1",
            "(v2 : Nat)",
            "(KExpr.lit v2)",
            "par_reduces_cd_star_lit_inv_eq the_red_env",
            "kexpr_lit_inj v1 v2",
            "def_eq_complete_leaf_lit n x bb v1 v2",
            "",
        );
        vec![sort, lit]
            .into_iter()
            .map(
                |(head, lbind, lform, shape, forces, rbind, rform, inv, inj, step, _extra)| {
                    // The two descriptions of w, composed.
                    let same = format!(
                        "(Eq.trans KExpr {lform} w {rform} \
                         (Eq.symm KExpr w {lform} ({inv} {lpayload} w hlw)) \
                         ({inv} {rpayload} w hrw2))",
                        lpayload = lbind.trim_start_matches('(').split(' ').next().unwrap(),
                        rpayload = rbind.trim_start_matches('(').split(' ').next().unwrap(),
                    );
                    // The b-side leg and its reduction, transported onto the shape.
                    let hb2 = format!(
                        "(Eq.substType KExpr \
                         (fun (z : KExpr) => Eq (OptionType KExpr) \
                         (whnf_fuel_red the_red_env n bb) (OptionType.some KExpr z)) \
                         nb {rform} hshape hb)"
                    );
                    let src = format!(
                        "def def_eq_round_{head} {HNF}(n : Nat) (x : KExpr) (bb : KExpr) \
                         (nb : KExpr) {lbind} \
                         (hx : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
                         (OptionType.some KExpr {lform})) \
                         (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n bb) \
                         (OptionType.some KExpr nb)) \
                         (hj : par_strips_witness_cd_star the_red_env {lform} nb) : \
                         DefEqFuelAccepts x bb := \
                         @par_strips_witness_cd_star.rec the_red_env {lform} nb \
                         (fun (_j : par_strips_witness_cd_star the_red_env {lform} nb) => \
                         DefEqFuelAccepts x bb) \
                         (fun (w : KExpr) \
                         (hlw : par_reduces_cd_star the_red_env {lform} w) \
                         (hrw : par_reduces_cd_star the_red_env nb w) => \
                         {shape}.rec nb (fun (_s : {shape} nb) => DefEqFuelAccepts x bb) \
                         (fun {rbind} (hshape : Eq KExpr nb {rform}) => \
                         (fun (hrw2 : par_reduces_cd_star the_red_env {rform} w) => \
                         {step} hx {hb2} ({inj} {same})) \
                         (Eq.substType KExpr \
                         (fun (z : KExpr) => par_reduces_cd_star the_red_env z w) \
                         nb {rform} hshape hrw)) \
                         ({forces} nb (hnf n bb nb hb) \
                         (nf_join_same_tag {lform} nb w (hnf n x {lform} hx) \
                         (hnf n bb nb hb) hlw hrw))) hj"
                    );
                    let desc = format!(
                        "def_eq_round_{head}: the completeness round at a {head} head. Takes NO \
                         recursion parameter — there is nothing below a {head} to descend into, so \
                         unlike the binder and application rounds this closes outright. That \
                         asymmetry is kept visible: a leaf round carrying a recursion hypothesis \
                         would suggest it descends, which it does not. \
                         \
                         The payload equality that def_eq_complete_leaf_{head} needs is discharged \
                         HERE, and this is where it comes from: both normal forms reduce to a \
                         common w, each is rigid so its star inversion pins w to be that very \
                         term, and composing the two descriptions of one w gives the constructor \
                         equation that {inj} splits. DerivedProved, zero axiom_deps."
                    );
                    (src, desc)
                },
            )
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn terms() -> Vec<String> {
        Specification::leaf_round_decls()
            .into_iter()
            .map(|(src, _)| src)
            .collect()
    }

    /// No leaf round may take a recursion parameter. If one ever did, it would
    /// be claiming to descend at a head with nothing below it.
    #[test]
    fn test_leaf_rounds_take_no_recursion() {
        for src in terms() {
            assert!(
                !src.contains("recur"),
                "a leaf head has nothing below it; a recursion parameter here would be \
                 misleading at best\nterm: {src}"
            );
            assert!(
                !src.contains("whnf_component_below") && !src.contains("whnf_component_acc"),
                "no descent premises at a leaf"
            );
        }
    }

    /// The payload equality must be DERIVED from the two meet descriptions, not
    /// taken as a hypothesis — that is the whole content of a leaf round.
    ///
    /// Checked by naming the inversion, not by counting a prefix: my first
    /// version counted `par_reduces_cd_star_` and expected 6, but that prefix
    /// matches only the two inversion NAMES — the leg binders spell
    /// `par_reduces_cd_star the_red_env` with a space. The count was wrong, not
    /// the term.
    #[test]
    fn test_payload_equality_is_derived_from_the_meet() {
        for (inv, inj) in [
            ("par_reduces_cd_star_sort_inv_eq", "kexpr_sort_inj"),
            ("par_reduces_cd_star_lit_inv_eq", "kexpr_lit_inj"),
        ] {
            let src = terms()
                .into_iter()
                .find(|s| s.contains(inv))
                .unwrap_or_else(|| panic!("no leaf round uses {inv}"));
            assert_eq!(
                src.matches(inv).count(),
                2,
                "both legs must be inverted at the meet with {inv}"
            );
            assert!(
                src.contains("Eq.trans KExpr"),
                "the two descriptions of w must be composed"
            );
            assert!(
                src.contains(inj),
                "constructor injectivity ({inj}) must split the composed equation"
            );
        }
    }

    /// The shape witness fixes `nb`, so both the b-side leg and its reduction
    /// must be transported onto that form. Checked by the two transport MOTIVES;
    /// counting `hshape` occurrences also catches its binding occurrence, which
    /// is how the first version of this test expected 2 and found 3.
    #[test]
    fn test_shape_is_transported_into_leg_and_reduction() {
        for src in terms() {
            assert!(
                src.contains("(fun (z : KExpr) => par_reduces_cd_star the_red_env z w)"),
                "the b-side REDUCTION must be transported onto the shape\nterm: {src}"
            );
            assert!(
                src.contains(
                    "(fun (z : KExpr) => Eq (OptionType KExpr) (whnf_fuel_red the_red_env n bb) \
                     (OptionType.some KExpr z))"
                ),
                "the b-side LEG must be transported onto the shape\nterm: {src}"
            );
            assert_eq!(
                src.matches("hshape").count(),
                3,
                "one binding occurrence plus one use per transport\nterm: {src}"
            );
        }
    }

    #[test]
    fn test_leaf_round_terms_parens_balanced() {
        for src in terms() {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in: {src}");
            }
            assert_eq!(depth, 0, "unbalanced: {src}");
        }
    }
}
