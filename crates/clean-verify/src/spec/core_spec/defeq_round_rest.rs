// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The last two completeness rounds: `const` and `proj`.
//!
//! ## `const` — where δ-deadness comes from
//!
//! `par_reduces_cd_star_const_dead_inv_eq` needs the constant not to unfold, and
//! the shape witness cannot supply it: `ConstShape` records only *that* the term
//! is a constant.
//!
//! It is recovered from the algorithm instead. A successful `whnf_fuel_red` has
//! no executable step left (`whnf_fuel_red_no_redex`, unconditional), and on a
//! constant an executable step is precisely a δ-unfolding
//! (`reduce_once_red_none_delta_none`). So the constant is δ-dead **because the
//! loop stopped there** — derived from the algorithm's own behaviour rather than
//! assumed of the environment.
//!
//! That matters beyond tidiness: assuming δ-deadness would have quietly
//! restricted the theorem to environments where the constant happens not to be
//! defined, which is a different and much weaker statement.
//!
//! ## `proj` — the name and index are not given
//!
//! `nf_tag_forces_proj` says only that both sides are projections; their struct
//! names and field indices could differ a priori, and
//! `def_eq_complete_step_proj` fixes both on each side. `proj_join_components`
//! returns the two equalities alongside the subject join precisely so this round
//! can transport the second leg onto the first's name and index before applying
//! the step.
//!
//! `DerivedProved`, empty axiom closures.

use super::nf_head::HNF;
use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The recursion hypothesis (`proj` only — `const` is a leaf).
const RECUR: &str = "(recur : forall (c1 : KExpr) (c2 : KExpr), rbelow_plus c1 x -> \
     DefEq c1 c2 -> rbelow_plus_acc c2 -> DefEqFuelAccepts c1 c2) ";

impl Specification {
    /// The `const` and `proj` rounds.
    pub(super) fn add_defeq_round_rest(&mut self) -> Result<(), SpecError> {
        self.add_const_round()?;
        self.add_proj_round()?;
        Ok(())
    }

    fn add_const_round(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(&Self::const_round_src(), Self::CONST_ROUND_DESC)?;
        Ok(())
    }

    const CONST_ROUND_DESC: &'static str =
        "def_eq_round_const: the completeness round at a constant head. Its delta-deadness \
         obligation is DERIVED, not assumed: a successful whnf_fuel_red has no executable step \
         left (whnf_fuel_red_no_redex, which is unconditional), and on a constant an executable \
         step is precisely a delta-unfolding (reduce_once_red_none_delta_none) — so the constant \
         is delta-dead BECAUSE THE LOOP STOPPED THERE. That is more than tidiness: assuming \
         delta-deadness would have quietly restricted the theorem to environments where the \
         constant happens to be undefined, a different and much weaker statement. Both payload \
         equalities then come from composing the two descriptions of the common reduct, split by \
         the const injectivities. No recursion parameter — a constant has nothing below it. \
         DerivedProved, zero axiom_deps.";

    fn const_round_src() -> String {
        // The composed equation is BOUND, not inlined per injectivity. Both
        // const projections consume it, and splicing it twice would duplicate
        // the whole delta-deadness derivation — four loop lookups where two
        // suffice. The shape test counts those lookups, which is how the
        // duplication was noticed.
        //
        // delta-deadness of a normal form, straight from the loop.
        let dead = |leg: &str, form: &str| {
            format!(
                "(reduce_once_red_none_delta_none the_red_env {form} \
                 (whnf_fuel_red_no_redex the_red_env n {which} {form} {leg}))",
                which = if leg == "hx" { "x" } else { "bb" }
            )
        };
        let left = "(KExpr.const cn1 cus1)";
        let right = "(KExpr.const cn2 cus2)";
        let hb2 = format!(
            "(Eq.substType KExpr \
             (fun (z : KExpr) => Eq (OptionType KExpr) \
             (whnf_fuel_red the_red_env n bb) (OptionType.some KExpr z)) \
             nb {right} hshape hb)"
        );
        let same = format!(
            "(Eq.trans KExpr {left} w {right} \
             (Eq.symm KExpr w {left} \
             (par_reduces_cd_star_const_dead_inv_eq cn1 cus1 w {dl} hlw)) \
             (par_reduces_cd_star_const_dead_inv_eq cn2 cus2 w {dr} hrw2))",
            dl = dead("hx", left),
            dr = dead("hb2", right),
        );
        format!(
            "def def_eq_round_const {HNF}(n : Nat) (x : KExpr) (bb : KExpr) (nb : KExpr) \
             (cn1 : Name) (cus1 : ListType Level) \
             (hx : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
             (OptionType.some KExpr {left})) \
             (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n bb) \
             (OptionType.some KExpr nb)) \
             (hj : par_strips_witness_cd_star the_red_env {left} nb) : \
             DefEqFuelAccepts x bb := \
             @par_strips_witness_cd_star.rec the_red_env {left} nb \
             (fun (_j : par_strips_witness_cd_star the_red_env {left} nb) => \
             DefEqFuelAccepts x bb) \
             (fun (w : KExpr) \
             (hlw : par_reduces_cd_star the_red_env {left} w) \
             (hrw : par_reduces_cd_star the_red_env nb w) => \
             ConstShape.rec nb (fun (_s : ConstShape nb) => DefEqFuelAccepts x bb) \
             (fun (cn2 : Name) (cus2 : ListType Level) (hshape : Eq KExpr nb {right}) => \
             (fun (hb2 : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n bb) \
             (OptionType.some KExpr {right})) \
             (hrw2 : par_reduces_cd_star the_red_env {right} w) => \
             (fun (hsame : Eq KExpr {left} {right}) => \
             def_eq_complete_leaf_const n x bb cn1 cus1 cn2 cus2 hx hb2 \
             (kexpr_const_inj_name cn1 cus1 cn2 cus2 hsame) \
             (kexpr_const_inj_ulist cn1 cus1 cn2 cus2 hsame)) {same}) \
             {hb2} \
             (Eq.substType KExpr \
             (fun (z : KExpr) => par_reduces_cd_star the_red_env z w) \
             nb {right} hshape hrw)) \
             (nf_tag_forces_const cn1 cus1 nb (hnf n bb nb hb) \
             (nf_join_same_tag {left} nb w (hnf n x {left} hx) (hnf n bb nb hb) \
             hlw hrw))) hj"
        )
    }

    fn add_proj_round(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(&Self::proj_round_src(), Self::PROJ_ROUND_DESC)?;
        Ok(())
    }

    const PROJ_ROUND_DESC: &'static str =
        "def_eq_round_proj: the completeness round at a projection head. nf_tag_forces_proj \
         establishes only that both sides ARE projections — their struct names and field indices \
         could differ a priori — while def_eq_complete_step_proj fixes both on each side. \
         proj_join_components returns those two equalities alongside the subject join precisely so \
         this round can transport the second leg onto the first's name and index before applying \
         the step. One component, so one recursive call. DerivedProved, zero axiom_deps.";

    fn proj_round_src() -> String {
        let left = "(KExpr.proj s1 i1 u1)";
        let right = "(KExpr.proj s2 i2 u2)";
        let hb2 = format!(
            "(Eq.substType KExpr \
             (fun (z : KExpr) => Eq (OptionType KExpr) \
             (whnf_fuel_red the_red_env n bb) (OptionType.some KExpr z)) \
             nb {right} hshape hb)"
        );
        // Move the second leg onto the FIRST side's name and index, which is
        // what the step demands.
        let hb3 = format!(
            "(Eq.substType Name \
             (fun (z : Name) => Eq (OptionType KExpr) \
             (whnf_fuel_red the_red_env n bb) \
             (OptionType.some KExpr (KExpr.proj z i1 u2))) \
             s2 s1 (Eq.symm Name s1 s2 hnm) \
             (Eq.substType Nat \
             (fun (z : Nat) => Eq (OptionType KExpr) \
             (whnf_fuel_red the_red_env n bb) \
             (OptionType.some KExpr (KExpr.proj s2 z u2))) \
             i2 i1 (Eq.symm Nat i1 i2 hix) {hb2}))"
        );
        format!(
            "def def_eq_round_proj {HNF}(n : Nat) (x : KExpr) (bb : KExpr) (nb : KExpr) \
             (s1 : Name) (i1 : Nat) (u1 : KExpr) \
             (hx : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
             (OptionType.some KExpr {left})) \
             (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n bb) \
             (OptionType.some KExpr nb)) \
             (hj : par_strips_witness_cd_star the_red_env {left} nb) \
             (accb : rbelow_plus_acc bb) {RECUR}: DefEqFuelAccepts x bb := \
             @par_strips_witness_cd_star.rec the_red_env {left} nb \
             (fun (_j : par_strips_witness_cd_star the_red_env {left} nb) => \
             DefEqFuelAccepts x bb) \
             (fun (w : KExpr) \
             (hlw : par_reduces_cd_star the_red_env {left} w) \
             (hrw : par_reduces_cd_star the_red_env nb w) => \
             ProjShape.rec nb (fun (_s : ProjShape nb) => DefEqFuelAccepts x bb) \
             (fun (s2 : Name) (i2 : Nat) (u2 : KExpr) (hshape : Eq KExpr nb {right}) => \
             ProjJoinComponents.rec s1 i1 u1 s2 i2 u2 \
             (fun (_c : ProjJoinComponents s1 i1 u1 s2 i2 u2) => DefEqFuelAccepts x bb) \
             (fun (hnm : Eq Name s1 s2) (hix : Eq Nat i1 i2) \
             (jsub : par_strips_witness_cd_star the_red_env u1 u2) => \
             def_eq_complete_step_proj n x bb s1 i1 u1 u2 hx {hb3} \
             (recur u1 u2 \
             (whnf_component_below n x {left} u1 hx (subexpr_step.proj_sub s1 i1 u1)) \
             (join_to_def_eq u1 u2 jsub) \
             (whnf_component_acc n bb {right} u2 {hb2} \
             (subexpr_step.proj_sub s2 i2 u2) accb))) \
             (proj_join_components s1 i1 u1 s2 i2 u2 \
             (Eq.substType KExpr \
             (fun (z : KExpr) => par_strips_witness_cd_star the_red_env {left} z) \
             nb {right} hshape hj))) \
             (nf_tag_forces_proj s1 i1 u1 nb (hnf n bb nb hb) \
             (nf_join_same_tag {left} nb w (hnf n x {left} hx) (hnf n bb nb hb) \
             hlw hrw))) hj"
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// δ-deadness must be DERIVED from the loop having stopped, never taken as a
    /// premise. A `const` round with a δ-deadness hypothesis would silently be a
    /// theorem about environments where the constant is undefined.
    #[test]
    fn test_const_derives_delta_deadness_from_the_loop() {
        let src = Specification::const_round_src();
        assert_eq!(
            src.matches("whnf_fuel_red_no_redex the_red_env n").count(),
            2,
            "each side's delta-deadness comes from ITS OWN loop result"
        );
        assert_eq!(
            src.matches("reduce_once_red_none_delta_none").count(),
            2,
            "and each no-redex fact must be converted to delta-deadness"
        );
        assert!(
            !src.contains("(hdd"),
            "delta-deadness must not be a parameter — deriving it is the point"
        );
    }

    /// `const` is a leaf: no recursion, no descent premises.
    #[test]
    fn test_const_round_is_a_leaf() {
        let src = Specification::const_round_src();
        for descent in ["recur", "whnf_component_below", "whnf_component_acc"] {
            assert!(
                !src.contains(descent),
                "a constant has nothing below it; {descent} must not appear"
            );
        }
        assert!(src.contains("def_eq_complete_leaf_const"));
    }

    /// `proj` must transport the second leg onto the FIRST side's name and
    /// index. `def_eq_complete_step_proj` fixes both, so without the transports
    /// it cannot be applied — and the equalities exist only because
    /// `proj_join_components` returns them.
    #[test]
    fn test_proj_transports_name_and_index_before_the_step() {
        let src = Specification::proj_round_src();
        assert!(
            src.contains("Eq.substType Name") && src.contains("Eq.substType Nat"),
            "both the struct name and the field index must be transported"
        );
        assert!(
            src.contains("Eq.symm Name s1 s2 hnm") && src.contains("Eq.symm Nat i1 i2 hix"),
            "the transports run from the second side onto the first's payload"
        );
        assert!(
            src.contains("def_eq_complete_step_proj n x bb s1 i1 u1 u2"),
            "the step is applied at the FIRST side's name and index"
        );
        assert!(
            src.contains("proj_join_components s1 i1 u1 s2 i2 u2"),
            "the equalities come from the component splitter, not from the shape witness"
        );
    }

    /// One component, one recursive call.
    #[test]
    fn test_proj_round_recurses_once() {
        let src = Specification::proj_round_src();
        assert_eq!(
            src.matches("recur u1 u2").count(),
            1,
            "a projection has exactly one component"
        );
        assert_eq!(src.matches("subexpr_step.proj_sub").count(), 2);
    }

    #[test]
    fn test_rest_round_terms_parens_balanced() {
        for (label, src) in [
            ("const", Specification::const_round_src()),
            ("proj", Specification::proj_round_src()),
        ] {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "{label}: close paren before its open");
            }
            assert_eq!(depth, 0, "{label}: unbalanced parens");
        }
    }
}
