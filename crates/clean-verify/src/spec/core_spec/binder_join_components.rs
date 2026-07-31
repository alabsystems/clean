// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Splitting a binder-head join into its **component** joins.
//!
//! ```text
//! pi_join_components :
//!   par_strips_witness_cd_star the_red_env (pi t1 b1) (pi t2 b2)
//!     -> BinderJoinComponents t1 b1 t2 b2
//! ```
//!
//! and the same for `lam`. The witness packages
//! `par_strips_witness_cd_star t1 t2` and `par_strips_witness_cd_star b1 b2`.
//!
//! ## Why this is the last piece of real content
//!
//! The capstone has the two normal forms joinable (`def_eq_whnf_join`) and knows
//! they share a head (`nf_join_same_tag` + `nf_tag_forces_*`). To recurse it
//! needs the **components** related — and that is not immediate, because the two
//! legs reach the common reduct independently.
//!
//! The argument: invert each leg with the binder inversion, obtaining
//! `w = pi w1 w2` from the left and `w = pi w1' w2'` from the right. Those are
//! two descriptions of the *same* `w`, so constructor injectivity gives
//! `w1 = w1'` and `w2 = w2'`. Transport, and the two component reductions now
//! land on a shared target — which is exactly a component join.
//!
//! Injectivity is where this bites: without it the two inversions would give
//! unrelated meets and nothing would compose. `kexpr_pi_inj_fst`/`_snd` and the
//! `lam` pair were already in tree.
//!
//! ## Universe note
//!
//! The binder inversions take their answer type as `C : Type`
//! (`par_reduces_cd_injectivity.rs:264`), and the answer here is a `Type`-valued
//! witness — so unlike the tag lemmas, **no `LiftP` wrap is needed**. That the
//! wrap was needed there and not here is a property of the goal, not of the
//! inversion.
//!
//! `DerivedProved`, empty axiom closures; the witness is census-neutral.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// `(head, constructor, first-injectivity lemma, second-injectivity lemma,
/// star inversion)`.
const BINDERS: [(&str, &str, &str, &str, &str); 2] = [
    (
        "pi",
        "KExpr.pi",
        "kexpr_pi_inj_fst",
        "kexpr_pi_inj_snd",
        "par_reduces_cd_star_pi_inv_eq",
    ),
    (
        "lam",
        "KExpr.lam",
        "kexpr_lam_inj_fst",
        "kexpr_lam_inj_snd",
        "par_reduces_cd_star_lam_inv_eq",
    ),
];

impl Specification {
    /// Component joins for the two binder heads.
    pub(super) fn add_binder_join_components(&mut self) -> Result<(), SpecError> {
        self.add_component_witness()?;
        for (src, desc) in Self::binder_component_decls() {
            self.add_recursive_def(&src, &desc)?;
        }
        Ok(())
    }

    fn add_component_witness(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive BinderJoinComponents (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) \
             (b2 : KExpr) : Type\n\
             | mk : par_strips_witness_cd_star the_red_env t1 t2 -> \
             par_strips_witness_cd_star the_red_env b1 b2 -> \
             BinderJoinComponents t1 b1 t2 b2",
            "BinderJoinComponents t1 b1 t2 b2: both component pairs of a binder head are \
             joinable. What the completeness recursion needs in order to descend: the two normal \
             forms being joinable does not immediately relate their components, because each leg \
             reaches the common reduct independently. Census-neutral.",
        )?;
        Ok(())
    }

    fn binder_component_decls() -> Vec<(String, String)> {
        BINDERS
            .iter()
            .map(|(head, ctor, inj_fst, inj_snd, inv)| {
                // Inner: both legs inverted, injectivity aligns the two meets.
                let src = format!(
                    "def {head}_join_components (t1 : KExpr) (b1 : KExpr) (t2 : KExpr) \
                     (b2 : KExpr) \
                     (hj : par_strips_witness_cd_star the_red_env ({ctor} t1 b1) \
                     ({ctor} t2 b2)) : BinderJoinComponents t1 b1 t2 b2 := \
                     @par_strips_witness_cd_star.rec the_red_env ({ctor} t1 b1) ({ctor} t2 b2) \
                     (fun (_j : par_strips_witness_cd_star the_red_env ({ctor} t1 b1) \
                     ({ctor} t2 b2)) => BinderJoinComponents t1 b1 t2 b2) \
                     (fun (w : KExpr) \
                     (hlw : par_reduces_cd_star the_red_env ({ctor} t1 b1) w) \
                     (hrw : par_reduces_cd_star the_red_env ({ctor} t2 b2) w) => \
                     {inv} the_red_env t1 b1 w (BinderJoinComponents t1 b1 t2 b2) hlw \
                     (fun (w1 : KExpr) (w2 : KExpr) \
                     (hwl : Eq KExpr w ({ctor} w1 w2)) \
                     (ht1 : par_reduces_cd_star the_red_env t1 w1) \
                     (hb1 : par_reduces_cd_star the_red_env b1 w2) => \
                     {inv} the_red_env t2 b2 w (BinderJoinComponents t1 b1 t2 b2) hrw \
                     (fun (v1 : KExpr) (v2 : KExpr) \
                     (hwr : Eq KExpr w ({ctor} v1 v2)) \
                     (ht2 : par_reduces_cd_star the_red_env t2 v1) \
                     (hb2 : par_reduces_cd_star the_red_env b2 v2) => \
                     (fun (hsame : Eq KExpr ({ctor} w1 w2) ({ctor} v1 v2)) => \
                     BinderJoinComponents.mk t1 b1 t2 b2 \
                     (par_strips_witness_cd_star.intro the_red_env t1 t2 w1 ht1 \
                     (Eq.substType KExpr \
                     (fun (z : KExpr) => par_reduces_cd_star the_red_env t2 z) \
                     v1 w1 (Eq.symm KExpr w1 v1 ({inj_fst} w1 w2 v1 v2 hsame)) ht2)) \
                     (par_strips_witness_cd_star.intro the_red_env b1 b2 w2 hb1 \
                     (Eq.substType KExpr \
                     (fun (z : KExpr) => par_reduces_cd_star the_red_env b2 z) \
                     v2 w2 (Eq.symm KExpr w2 v2 ({inj_snd} w1 w2 v1 v2 hsame)) hb2))) \
                     (Eq.trans KExpr ({ctor} w1 w2) w ({ctor} v1 v2) \
                     (Eq.symm KExpr w ({ctor} w1 w2) hwl) hwr)))) hj"
                );
                let desc = format!(
                    "{head}_join_components: a joinable pair of {head} heads has joinable \
                     COMPONENTS. This is what lets the completeness recursion descend, and it is \
                     not immediate: the two normal forms being joinable says only that each \
                     reaches the common reduct, independently. \
                     \
                     Inverting each leg gives w = {ctor} w1 w2 from the left and w = {ctor} v1 v2 \
                     from the right — two descriptions of the SAME w — so constructor injectivity \
                     ({inj_fst} / {inj_snd}) forces w1 = v1 and w2 = v2. Transporting the right \
                     leg's component reductions onto the left's targets makes each component pair \
                     land on a shared term, which is exactly a component join. Injectivity is \
                     where the argument bites: without it the two inversions would yield unrelated \
                     meets and nothing would compose. \
                     \
                     Note no LiftP wrap, unlike the tag lemmas that use the same inversions: the \
                     answer here is a Type-valued witness, so it instantiates C : Type directly. \
                     The wrap was a property of the goal, not of the inversion. DerivedProved, \
                     zero axiom_deps."
                );
                (src, desc)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn terms() -> Vec<String> {
        Specification::binder_component_decls()
            .into_iter()
            .map(|(src, _)| src)
            .collect()
    }

    /// One lemma per binder head, each using ITS OWN inversion and injectivity
    /// pair. Crossing them — `pi`'s lemma with `lam`'s injectivity — would fail
    /// only inside a 21-minute build.
    #[test]
    fn test_each_head_uses_its_own_inversion_and_injectivity() {
        for ((head, ctor, inj_fst, inj_snd, inv), src) in BINDERS.iter().zip(terms()) {
            assert!(
                src.contains(&format!("def {head}_join_components")),
                "missing lemma for {head}"
            );
            assert_eq!(
                src.matches(inv).count(),
                2,
                "{head}: both legs must be inverted with {inv}"
            );
            assert!(src.contains(inj_fst), "{head}: must use {inj_fst}");
            assert!(src.contains(inj_snd), "{head}: must use {inj_snd}");
            // The other head's machinery must not leak in.
            for (other_head, _, other_fst, _, other_inv) in BINDERS.iter() {
                if other_head != head {
                    assert!(!src.contains(other_fst), "{head}: leaked {other_fst}");
                    assert!(!src.contains(other_inv), "{head}: leaked {other_inv}");
                }
            }
            assert!(src.contains(ctor), "{head}: must mention its constructor");
        }
    }

    /// THE LOAD-BEARING STEP. Injectivity must be applied to an equation between
    /// the TWO descriptions of the common reduct. Without that `Eq.trans` the two
    /// inversions describe unrelated meets and the components do not compose —
    /// and a term that skipped it could still typecheck by picking one leg's
    /// meet twice.
    #[test]
    fn test_injectivity_aligns_the_two_meets() {
        for ((head, ctor, _, _, _), src) in BINDERS.iter().zip(terms()) {
            assert!(
                src.contains(&format!("Eq.trans KExpr ({ctor} w1 w2) w ({ctor} v1 v2)")),
                "{head}: the two meet descriptions must be composed through w itself"
            );
            assert_eq!(
                src.matches("Eq.substType KExpr").count(),
                2,
                "{head}: one transport per component, moving the right leg onto the left's target"
            );
            assert_eq!(
                src.matches("par_strips_witness_cd_star.intro the_red_env")
                    .count(),
                2,
                "{head}: one component join built per component"
            );
        }
    }

    /// No `LiftP`: the answer is `Type`-valued, so it instantiates the
    /// inversion's `C : Type` directly. If a wrap ever appears here it means the
    /// witness was accidentally made `Prop`-valued.
    #[test]
    fn test_no_liftp_wrap_needed() {
        for ((head, _, _, _, _), src) in BINDERS.iter().zip(terms()) {
            assert!(
                !src.contains("LiftP"),
                "{head}: the witness is Type-valued and instantiates C : Type directly; a LiftP \
                 wrap here would mean the witness had become Prop-valued"
            );
        }
    }

    #[test]
    fn test_component_terms_parens_balanced() {
        for ((head, _, _, _, _), src) in BINDERS.iter().zip(terms()) {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "{head}: close paren before its open");
            }
            assert_eq!(depth, 0, "{head}: unbalanced parens");
        }
    }
}
