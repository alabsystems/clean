// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One round of def-eq completeness, over the **algorithm's own** whnf legs.
//!
//! ```text
//! def_eq_nf_head_agree :
//!   i1..i8 -> DefEq a b
//!     -> whnf_fuel_red the_red_env n a = some na
//!     -> whnf_fuel_red the_red_env n b = some nb
//!     -> nf_head na -> nf_head nb
//!     -> Eq Nat (kexpr_tag na) (kexpr_tag nb)
//! ```
//!
//! ## How this differs from the landed `def_eq_whnf_complete`
//!
//! `def_eq_whnf_complete` (`wall_a_completeness.rs:2998`) proves the same round,
//! but over the **relational** `whnf_to` and with two `iota_whnf` premises. Those
//! premises are the problem: nothing in the tree establishes that a genuine
//! kernel whnf result is ι-immune, so the lemma has never had a consumer.
//!
//! This version:
//!
//! * takes its legs from `whnf_fuel_red` — the function the algorithm actually
//!   runs — instead of the relation, and
//! * replaces `iota_whnf` with `nf_head`, which **is** obtainable, because ι/δ
//!   immunity for those shapes was proved structurally (`stuck_immunity.rs`,
//!   `rigid_app_head.rs`) rather than assumed.
//!
//! So it is the same round with dischargeable hypotheses.
//!
//! ## The proof
//!
//! Exactly the skeleton `def_eq_whnf_complete` uses, with the legs swapped:
//!
//! 1. `def_eq_joinable` turns `DefEq a b` into a common reduct `m`.
//! 2. Each fuel leg becomes a parallel-reduction leg —
//!    `whnf_fuel_red_reaches_sound` then `red_step_star_to_whnf_red_step_star`
//!    then `whnf_red_step_star_to_par_cd_star`. All three are unconditional.
//! 3. Three applications of `par_reduces_cd_star_diamond` push `na` and `nb`
//!    down to a common meet `w`.
//! 4. `nf_join_same_tag` reads off the tag equality.
//!
//! Step 4 is where the tag factoring pays: the conclusion is one arithmetic
//! equation rather than a `HeadMatch`, so the six `nf_tag_forces_*` lemmas can
//! turn it into shapes without a grid over head pairs.
//!
//! `i1..i8` are carried, as everywhere in this family; they are dischargeable at
//! `the_red_env` via `the_red_env_faithful`.
//!
//! `DerivedProved`, empty axiom closure.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The eight faithful-interface binders, in the order `def_eq_joinable` expects
/// (`def_eq_joinable.rs:51-58`).
const I_BINDERS: &str = "(i1 : RecEnvReductNotRedex (red_rec the_red_env)) \
     (i2 : RecEnvCtorNoRecMeta (red_rec the_red_env)) \
     (i3 : RecEnvClosed (red_rec the_red_env)) \
     (i4 : RecEnvLiftClosed (red_rec the_red_env)) \
     (i5 : DefEnvClosed (red_def the_red_env)) \
     (i6 : DefEnvLiftClosed (red_def the_red_env)) \
     (i7 : RecEnvDefEnvDisjoint the_red_env) \
     (i8 : RecEnvCtorNoDefVal the_red_env) ";

impl Specification {
    /// One round of completeness over the executable legs.
    pub(super) fn add_defeq_nf_agree(&mut self) -> Result<(), SpecError> {
        self.add_fuel_leg_bridge()?;
        self.add_nf_head_agree()?;
        Ok(())
    }

    /// A successful fuel run is a parallel-reduction leg. Three unconditional
    /// bridges, composed once so the capstone does not repeat them per side.
    fn add_fuel_leg_bridge(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def whnf_fuel_red_par_leg (n : Nat) (e : KExpr) (r : KExpr) \
             (h : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n e) \
             (OptionType.some KExpr r)) : par_reduces_cd_star the_red_env e r := \
             whnf_red_step_star_to_par_cd_star the_red_env e r \
             (red_step_star_to_whnf_red_step_star the_red_env e r \
             (whnf_fuel_red_reaches_sound the_red_env n e r h))",
            "whnf_fuel_red_par_leg: whatever the executable whnf loop returns is reachable from \
             its input by parallel reduction. Composes three unconditional bridges — the loop's \
             reach-soundness, the snoc/cons closure bridge, and the embedding of the algorithm's \
             step relation into par_reduces_cd_star. Stated once so each consumer does not repeat \
             it per side; this is the form that feeds the confluence diamonds. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }

    fn add_nf_head_agree(&mut self) -> Result<(), SpecError> {
        // Three diamonds, then the tag. Written with the join witnesses
        // eliminated in sequence: m from the DefEq join, p1 from the a-legs,
        // p2 from the b-legs, w from the two m-legs.
        let body = "\
             @par_strips_witness_cd_star.rec the_red_env a b \
             (fun (_w0 : par_strips_witness_cd_star the_red_env a b) => \
             Eq Nat (kexpr_tag na) (kexpr_tag nb)) \
             (fun (m : KExpr) (ham : par_reduces_cd_star the_red_env a m) \
             (hbm : par_reduces_cd_star the_red_env b m) => \
             @par_strips_witness_cd_star.rec the_red_env na m \
             (fun (_w1 : par_strips_witness_cd_star the_red_env na m) => \
             Eq Nat (kexpr_tag na) (kexpr_tag nb)) \
             (fun (p1 : KExpr) (hnap1 : par_reduces_cd_star the_red_env na p1) \
             (hmp1 : par_reduces_cd_star the_red_env m p1) => \
             @par_strips_witness_cd_star.rec the_red_env nb m \
             (fun (_w2 : par_strips_witness_cd_star the_red_env nb m) => \
             Eq Nat (kexpr_tag na) (kexpr_tag nb)) \
             (fun (p2 : KExpr) (hnbp2 : par_reduces_cd_star the_red_env nb p2) \
             (hmp2 : par_reduces_cd_star the_red_env m p2) => \
             @par_strips_witness_cd_star.rec the_red_env p1 p2 \
             (fun (_w3 : par_strips_witness_cd_star the_red_env p1 p2) => \
             Eq Nat (kexpr_tag na) (kexpr_tag nb)) \
             (fun (w : KExpr) (hp1w : par_reduces_cd_star the_red_env p1 w) \
             (hp2w : par_reduces_cd_star the_red_env p2 w) => \
             nf_join_same_tag na nb w hna hnb \
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
                "def def_eq_nf_head_agree {I_BINDERS}(n : Nat) (a : KExpr) (b : KExpr) \
                 (na : KExpr) (nb : KExpr) (hde : DefEq a b) \
                 (ha : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n a) \
                 (OptionType.some KExpr na)) \
                 (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n b) \
                 (OptionType.some KExpr nb)) \
                 (hna : nf_head na) (hnb : nf_head nb) : \
                 Eq Nat (kexpr_tag na) (kexpr_tag nb) := {body}"
            ),
            "def_eq_nf_head_agree: ONE ROUND of def-eq completeness, over the legs the ALGORITHM \
             actually produces. If a and b are definitionally equal and the executable whnf loop \
             returns na and nb at a common fuel, and both results have normal-form heads, then \
             those heads agree — as an arithmetic equation on tags. \
             \
             This supersedes the landed def_eq_whnf_complete for practical purposes. That lemma \
             proves the same round but over the RELATIONAL whnf_to and with two iota_whnf \
             premises that nothing in the tree establishes, which is why it has no consumer. Here \
             the legs come from whnf_fuel_red — the function the algorithm runs — and iota_whnf is \
             replaced by nf_head, which IS obtainable, because iota/delta immunity for those \
             shapes was proved structurally rather than assumed. Same round, dischargeable \
             hypotheses. \
             \
             Proof: def_eq_joinable gives a common reduct m; each fuel leg becomes a parallel \
             leg via whnf_fuel_red_par_leg; three applications of par_reduces_cd_star_diamond \
             push na and nb to a common meet w; nf_join_same_tag reads off the tag equality. The \
             conclusion is deliberately an arithmetic equation rather than a HeadMatch, so the six \
             nf_tag_forces_* lemmas can turn it into shapes with no grid over head pairs. \
             i1..i8 are carried and are dischargeable at the_red_env via the_red_env_faithful. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Eight faithful interfaces, in `def_eq_joinable`'s order. A permutation
    /// here still elaborates — they are distinct types, but a wrong order makes
    /// the application fail deep inside a 21-minute build.
    #[test]
    fn test_i_binders_are_the_canonical_eight_in_order() {
        let expected = [
            "RecEnvReductNotRedex",
            "RecEnvCtorNoRecMeta",
            "RecEnvClosed",
            "RecEnvLiftClosed",
            "DefEnvClosed",
            "DefEnvLiftClosed",
            "RecEnvDefEnvDisjoint",
            "RecEnvCtorNoDefVal",
        ];
        let mut cursor = 0usize;
        for (position, iface) in expected.iter().enumerate() {
            let found = I_BINDERS[cursor..].find(iface).unwrap_or_else(|| {
                panic!("interface {position} ({iface}) missing or out of order")
            });
            cursor += found + iface.len();
        }
        assert_eq!(
            I_BINDERS.matches(" : ").count(),
            8,
            "exactly eight interface binders"
        );
    }

    /// Three diamonds, four join eliminations: the DefEq join plus one per
    /// diamond. Fewer would mean a leg was never pushed to the meet.
    #[test]
    fn test_agreement_uses_three_diamonds_and_four_joins() {
        let src = include_str!("defeq_nf_agree.rs");
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
    }

    /// The conclusion must be the tag equation, not a HeadMatch — that is what
    /// keeps the downstream shape analysis linear.
    #[test]
    fn test_conclusion_is_the_tag_equation() {
        let src = include_str!("defeq_nf_agree.rs");
        let decl_start = src
            .find("def def_eq_nf_head_agree")
            .expect("declaration present");
        let decl = &src[decl_start..decl_start + 900];
        assert!(
            decl.contains("Eq Nat (kexpr_tag na) (kexpr_tag nb)"),
            "the conclusion must be the tag equation"
        );
        assert!(
            !decl.contains("HeadMatch"),
            "deliberately NOT HeadMatch: an arithmetic conclusion is what lets \
             nf_tag_forces_* avoid a grid over head pairs"
        );
        assert!(
            decl.contains("nf_head na") && decl.contains("nf_head nb"),
            "both normal forms need a normal-form-head hypothesis"
        );
        assert!(
            !decl.contains("iota_whnf"),
            "the whole point is replacing iota_whnf — which nothing discharges — with nf_head"
        );
    }
}
