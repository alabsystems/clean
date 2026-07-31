// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The two whnf results of definitionally equal terms are **joinable**.
//!
//! ```text
//! def_eq_whnf_join :
//!   i1..i8 -> DefEq a b
//!     -> whnf_fuel_red the_red_env n a = some na
//!     -> whnf_fuel_red the_red_env n b = some nb
//!     -> par_strips_witness_cd_star the_red_env na nb
//! ```
//!
//! ## Why this, and not the tag
//!
//! `def_eq_nf_head_agree` concludes a tag equality, which is what the head
//! *dispatch* needs. But the capstone needs more than the head: at `sort`,
//! `lit` and `const` heads the two normal forms must agree on their **payload**,
//! and at `pi`/`lam`/`app`/`proj` it needs the **components** related. All of
//! that lives in the common reduct, which a tag equality has already discarded.
//!
//! So this lemma keeps the join itself. It is strictly more informative, and it
//! needs **no** `nf_head` hypothesis at all — joinability of the two results
//! follows from `DefEq` plus confluence alone. `nf_head` is only needed later,
//! to turn a join into a head agreement.
//!
//! Recognising that the answer is exactly `par_strips_witness_cd_star na nb` —
//! the existing join witness, not a new type — is what keeps this three lines of
//! plumbing over the three diamonds rather than a new development.
//!
//! `whnf_component_below` is also here: the `rbelow_plus` fact hiding inside
//! `whnf_component_acc`. The capstone's recursion needs the *relation* to invoke
//! its induction hypothesis, not just the accessibility that `whnf_component_acc`
//! returns, so it is exposed rather than re-derived.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The eight faithful-interface binders, in `def_eq_joinable`'s order.
const I_BINDERS: &str = "(i1 : RecEnvReductNotRedex (red_rec the_red_env)) \
     (i2 : RecEnvCtorNoRecMeta (red_rec the_red_env)) \
     (i3 : RecEnvClosed (red_rec the_red_env)) \
     (i4 : RecEnvLiftClosed (red_rec the_red_env)) \
     (i5 : DefEnvClosed (red_def the_red_env)) \
     (i6 : DefEnvLiftClosed (red_def the_red_env)) \
     (i7 : RecEnvDefEnvDisjoint the_red_env) \
     (i8 : RecEnvCtorNoDefVal the_red_env) ";

impl Specification {
    /// Joinability of the two whnf results, and the descent relation.
    pub(super) fn add_defeq_whnf_join(&mut self) -> Result<(), SpecError> {
        self.add_component_below()?;
        self.add_whnf_join()?;
        Ok(())
    }

    /// The `rbelow_plus` relation the capstone's induction hypothesis consumes.
    fn add_component_below(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def whnf_component_below (n : Nat) (a : KExpr) (r : KExpr) (c : KExpr) \
             (hr : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n a) \
             (OptionType.some KExpr r)) \
             (hc : subexpr_step c r) : rbelow_plus c a := \
             rbelow_plus_of_step_rtc c r a (rbelow.sub c r hc) \
             (whnf_fuel_red_rbelow_rtc n a r hr)",
            "whnf_component_below: an immediate subexpression of a whnf result is STRICTLY BELOW \
             the original term in the algorithm's order. This is the relation that was already \
             being computed inside whnf_component_acc and then thrown away in favour of the \
             accessibility it implies. The capstone's recursion needs the relation itself, to \
             invoke its induction hypothesis; exposing it here is cheaper and clearer than \
             re-deriving it at the call site. Strictness comes from the subexpr_step, since the \
             reduction leg may be empty. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_whnf_join(&mut self) -> Result<(), SpecError> {
        // Three diamonds again, but the conclusion keeps the meet instead of
        // reading a tag off it.
        let body = "\
             @par_strips_witness_cd_star.rec the_red_env a b \
             (fun (_w0 : par_strips_witness_cd_star the_red_env a b) => \
             par_strips_witness_cd_star the_red_env na nb) \
             (fun (m : KExpr) (ham : par_reduces_cd_star the_red_env a m) \
             (hbm : par_reduces_cd_star the_red_env b m) => \
             @par_strips_witness_cd_star.rec the_red_env na m \
             (fun (_w1 : par_strips_witness_cd_star the_red_env na m) => \
             par_strips_witness_cd_star the_red_env na nb) \
             (fun (p1 : KExpr) (hnap1 : par_reduces_cd_star the_red_env na p1) \
             (hmp1 : par_reduces_cd_star the_red_env m p1) => \
             @par_strips_witness_cd_star.rec the_red_env nb m \
             (fun (_w2 : par_strips_witness_cd_star the_red_env nb m) => \
             par_strips_witness_cd_star the_red_env na nb) \
             (fun (p2 : KExpr) (hnbp2 : par_reduces_cd_star the_red_env nb p2) \
             (hmp2 : par_reduces_cd_star the_red_env m p2) => \
             @par_strips_witness_cd_star.rec the_red_env p1 p2 \
             (fun (_w3 : par_strips_witness_cd_star the_red_env p1 p2) => \
             par_strips_witness_cd_star the_red_env na nb) \
             (fun (w : KExpr) (hp1w : par_reduces_cd_star the_red_env p1 w) \
             (hp2w : par_reduces_cd_star the_red_env p2 w) => \
             par_strips_witness_cd_star.intro the_red_env na nb w \
             (par_reduces_cd_star_trans the_red_env na p1 w hnap1 hp1w) \
             (par_reduces_cd_star_trans the_red_env nb p2 w hnbp2 hp2w)) \
             (par_reduces_cd_star_diamond the_red_env i1 i2 i3 i4 i5 i6 i7 i8 m p1 p2 \
             hmp1 hmp2)) \
             (par_reduces_cd_star_diamond the_red_env i1 i2 i3 i4 i5 i6 i7 i8 b nb m \
             (whnf_fuel_red_par_leg n b nb hb) hbm)) \
             (par_reduces_cd_star_diamond the_red_env i1 i2 i3 i4 i5 i6 i7 i8 a na m \
             (whnf_fuel_red_par_leg n a na ha) ham)) \
             (def_eq_joinable i1 i2 i3 i4 i5 i6 i7 i8 a b hde)";

        self.add_recursive_def(
            &format!(
                "def def_eq_whnf_join {I_BINDERS}(n : Nat) (a : KExpr) (b : KExpr) \
                 (na : KExpr) (nb : KExpr) (hde : DefEq a b) \
                 (ha : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n a) \
                 (OptionType.some KExpr na)) \
                 (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n b) \
                 (OptionType.some KExpr nb)) : \
                 par_strips_witness_cd_star the_red_env na nb := {body}"
            ),
            "def_eq_whnf_join: if a and b are definitionally equal, the two results the executable \
             whnf loop returns at a common fuel are JOINABLE. \
             \
             This is the form the completeness capstone needs, and it is strictly more informative \
             than the tag agreement: at sort, lit and const heads the two normal forms must agree \
             on their PAYLOAD, and at pi / lam / app / proj their COMPONENTS must be related — all \
             of which lives in the common reduct that a tag equality has already discarded. \
             \
             Note it needs NO nf_head hypothesis. Joinability of the two results follows from \
             DefEq plus confluence alone; nf_head is required only later, to turn a join into a \
             head agreement. And the answer is exactly par_strips_witness_cd_star na nb — the \
             join witness that already exists, not a new type — which is what keeps this three \
             diamonds and a constructor rather than a development. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Three diamonds, four join eliminations, both legs bridged — the same
    /// skeleton as the tag version, differing only in what it keeps.
    #[test]
    fn test_join_uses_three_diamonds_and_keeps_the_meet() {
        let src = include_str!("defeq_whnf_join.rs");
        let body_start = src.find("let body = \"\\").expect("body present");
        let body_end = src[body_start..].find("\";").expect("body terminates") + body_start;
        let body = &src[body_start..body_end];
        assert_eq!(
            body.matches("par_reduces_cd_star_diamond").count(),
            3,
            "three diamonds: a-legs, b-legs, then the two m-legs"
        );
        assert_eq!(
            body.matches("@par_strips_witness_cd_star.rec").count(),
            4,
            "four join eliminations: the DefEq join plus one per diamond"
        );
        assert_eq!(
            body.matches("whnf_fuel_red_par_leg").count(),
            2,
            "both fuel legs must be bridged into parallel reduction"
        );
        assert!(
            body.contains("par_strips_witness_cd_star.intro the_red_env na nb w"),
            "the meet must be KEPT — that is the entire difference from the tag version"
        );
    }

    /// No `nf_head` hypothesis: joinability is confluence, not head analysis.
    /// If one ever appears here it means the two concerns have been conflated.
    #[test]
    fn test_join_needs_no_head_hypothesis() {
        let src = include_str!("defeq_whnf_join.rs");
        let decl_start = src
            .find("def def_eq_whnf_join")
            .expect("declaration present");
        let decl = &src[decl_start..decl_start + 700];
        assert!(
            !decl.contains("nf_head"),
            "joinability follows from DefEq plus confluence alone; a head hypothesis here would \
             conflate the join with the head agreement that consumes it"
        );
        assert!(
            decl.contains("par_strips_witness_cd_star the_red_env na nb"),
            "the conclusion is the existing join witness, not a new type"
        );
    }

    /// The descent lemma must produce the RELATION, not the accessibility — that
    /// is the whole reason it is separate from `whnf_component_acc`.
    #[test]
    fn test_component_below_produces_the_relation() {
        let src = include_str!("defeq_whnf_join.rs");
        let decl_start = src
            .find("def whnf_component_below")
            .expect("declaration present");
        let decl = &src[decl_start..decl_start + 500];
        assert!(
            decl.contains(": rbelow_plus c a"),
            "must conclude the rbelow_plus RELATION; whnf_component_acc already gives the \
             accessibility, and the capstone's induction hypothesis needs the relation"
        );
        assert!(
            decl.contains("rbelow.sub c r hc"),
            "strictness comes from the subexpr_step, since the reduction leg may be empty"
        );
    }
}
