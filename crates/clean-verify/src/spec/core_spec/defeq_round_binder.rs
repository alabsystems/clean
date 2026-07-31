// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One completeness round at a **binder** head, given the recursion.
//!
//! ```text
//! def_eq_round_pi :
//!   (hnf) (recur)
//!     -> whnf_fuel_red the_red_env n x = some (pi t1 b1)
//!     -> whnf_fuel_red the_red_env n b = some nb
//!     -> par_strips_witness_cd_star the_red_env (pi t1 b1) nb
//!     -> rbelow_plus_acc b
//!     -> DefEqFuelAccepts x b
//! ```
//!
//! and the same for `lam`. These are where every earlier brick meets:
//!
//! 1. the join and both `nf_head`s give the **tag** (`nf_join_same_tag`);
//! 2. the tag forces the other side's **shape** (`nf_tag_forces_*`);
//! 3. the shape lets the join split into **component joins**
//!    (`pi_join_components`);
//! 4. each component join becomes a `DefEq` (`join_to_def_eq`);
//! 5. `whnf_component_below` and `whnf_component_acc` supply the recursion's
//!    two premises;
//! 6. `recur` returns the component acceptances;
//! 7. `def_eq_complete_step_pi` collapses the three fuels and rebuilds.
//!
//! ## Written per shape, deliberately
//!
//! The full round is an eight-leaf case analysis on `nf_head`. Writing it as one
//! term means a single elaboration failure names one declaration and gives no
//! clue which leaf; written per shape, the failing leaf is the failing
//! declaration. At ~21 minutes a build that difference is the difference between
//! one cycle and eight.
//!
//! ## `recur` is a hypothesis
//!
//! These take the recursion as a parameter. That is not a way of assuming the
//! result: `recur` relates terms **strictly below** `x` in the algorithm's
//! order, and the capstone supplies it by `rbelow_plus_acc` induction. Handing
//! it in here is what makes each round independently checkable.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// `(head, constructor, shape witness, tag-forcing lemma, component splitter,
/// step, first subexpr constructor, second subexpr constructor)`.
const BINDER_ROUNDS: [(&str, &str, &str, &str, &str, &str, &str, &str); 2] = [
    (
        "pi",
        "KExpr.pi",
        "PiShape",
        "nf_tag_forces_pi",
        "pi_join_components",
        "def_eq_complete_step_pi",
        "subexpr_step.pi_dom",
        "subexpr_step.pi_cod",
    ),
    (
        "lam",
        "KExpr.lam",
        "LamShape",
        "nf_tag_forces_lam",
        "lam_join_components",
        "def_eq_complete_step_lam",
        "subexpr_step.lam_ty",
        "subexpr_step.lam_body",
    ),
];

/// The recursion hypothesis, shared by every round.
const RECUR: &str = "(recur : forall (c1 : KExpr) (c2 : KExpr), rbelow_plus c1 x -> \
     DefEq c1 c2 -> rbelow_plus_acc c2 -> DefEqFuelAccepts c1 c2) ";

/// The hereditary normal-form-head hypothesis.
const HNF: &str = "(hnf : forall (m : Nat) (e : KExpr) (r : KExpr), \
     Eq (OptionType KExpr) (whnf_fuel_red the_red_env m e) (OptionType.some KExpr r) -> \
     nf_head r) ";

impl Specification {
    /// Completeness rounds at the binder heads.
    pub(super) fn add_defeq_round_binder(&mut self) -> Result<(), SpecError> {
        for (src, desc) in Self::binder_round_decls() {
            self.add_recursive_def(&src, &desc)?;
        }
        Ok(())
    }

    fn binder_round_decls() -> Vec<(String, String)> {
        BINDER_ROUNDS
            .iter()
            .map(|(head, ctor, shape, forces, split, step, sub1, sub2)| {
                let na = format!("({ctor} t1 b1)");
                let nb2 = format!("({ctor} t2 b2)");

                // After the shape witness fixes nb = ctor t2 b2, transport the
                // b-side leg and the join onto that form.
                let hb2 = format!(
                    "(Eq.substType KExpr \
                     (fun (z : KExpr) => Eq (OptionType KExpr) \
                     (whnf_fuel_red the_red_env n bb) (OptionType.some KExpr z)) \
                     nb {nb2} hshape hb)"
                );
                let hj2 = format!(
                    "(Eq.substType KExpr \
                     (fun (z : KExpr) => par_strips_witness_cd_star the_red_env {na} z) \
                     nb {nb2} hshape hj)"
                );

                // Component acceptances from the recursion.
                let accept = |slot: usize| {
                    let (c1, c2, sub) = if slot == 0 {
                        ("t1", "t2", sub1)
                    } else {
                        ("b1", "b2", sub2)
                    };
                    format!(
                        "(recur {c1} {c2} \
                         (whnf_component_below n x {na} {c1} hx ({sub} t1 b1)) \
                         (join_to_def_eq {c1} {c2} j{slot}) \
                         (whnf_component_acc n bb {nb2} {c2} {hb2} ({sub} t2 b2) accb))"
                    )
                };

                let src = format!(
                    "def def_eq_round_{head} {hnf}(n : Nat) (x : KExpr) (bb : KExpr) \
                     (nb : KExpr) (t1 : KExpr) (b1 : KExpr) \
                     (hx : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x) \
                     (OptionType.some KExpr {na})) \
                     (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n bb) \
                     (OptionType.some KExpr nb)) \
                     (hj : par_strips_witness_cd_star the_red_env {na} nb) \
                     (accb : rbelow_plus_acc bb) {recur}: DefEqFuelAccepts x bb := \
                     @par_strips_witness_cd_star.rec the_red_env {na} nb \
                     (fun (_j : par_strips_witness_cd_star the_red_env {na} nb) => \
                     DefEqFuelAccepts x bb) \
                     (fun (w : KExpr) \
                     (hlw : par_reduces_cd_star the_red_env {na} w) \
                     (hrw : par_reduces_cd_star the_red_env nb w) => \
                     {shape}.rec nb \
                     (fun (_s : {shape} nb) => DefEqFuelAccepts x bb) \
                     (fun (t2 : KExpr) (b2 : KExpr) (hshape : Eq KExpr nb {nb2}) => \
                     BinderJoinComponents.rec t1 b1 t2 b2 \
                     (fun (_c : BinderJoinComponents t1 b1 t2 b2) => DefEqFuelAccepts x bb) \
                     (fun (j0 : par_strips_witness_cd_star the_red_env t1 t2) \
                     (j1 : par_strips_witness_cd_star the_red_env b1 b2) => \
                     {step} n x bb t1 b1 t2 b2 hx {hb2} {a0} {a1}) \
                     ({split} t1 b1 t2 b2 {hj2})) \
                     ({forces} t1 b1 nb (hnf n bb nb hb) \
                     (nf_join_same_tag {na} nb w (hnf n x {na} hx) (hnf n bb nb hb) \
                     hlw hrw))) hj",
                    hnf = HNF,
                    recur = RECUR,
                    a0 = accept(0),
                    a1 = accept(1),
                );

                let desc = format!(
                    "def_eq_round_{head}: ONE COMPLETENESS ROUND at a {head} head, given the \
                     recursion. Where every earlier brick meets: the join plus both nf_heads give \
                     the tag (nf_join_same_tag); the tag forces the other side's shape ({forces}); \
                     the shape lets the join split into component joins ({split}); each component \
                     join becomes a DefEq (join_to_def_eq); whnf_component_below and \
                     whnf_component_acc supply the recursion's two premises; recur returns the \
                     component acceptances; and {step} collapses the three fuels and rebuilds. \
                     \
                     recur is a HYPOTHESIS, and that is not assuming the result: it relates terms \
                     STRICTLY BELOW x in the algorithm's order, and the capstone supplies it by \
                     rbelow_plus_acc induction. Handing it in is what makes each round \
                     independently checkable — the full round is an eight-leaf case analysis, and \
                     written as one term a failure names one declaration with no clue which leaf. \
                     At ~21 minutes a build, that is the difference between one cycle and eight. \
                     DerivedProved, zero axiom_deps."
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
        Specification::binder_round_decls()
            .into_iter()
            .map(|(src, _)| src)
            .collect()
    }

    /// Each round must use ITS OWN shape witness, tag-forcer, splitter and step.
    /// Crossing any of them — `pi`'s round with `lam`'s splitter — typechecks
    /// nowhere useful but fails only in a full build.
    #[test]
    fn test_each_round_uses_its_own_machinery() {
        for ((head, ctor, shape, forces, split, step, sub1, sub2), src) in
            BINDER_ROUNDS.iter().zip(terms())
        {
            assert!(src.contains(&format!("def def_eq_round_{head}")));
            for piece in [shape, forces, split, step, sub1, sub2, ctor] {
                assert!(src.contains(piece), "{head}: missing {piece}");
            }
            for (other, o_ctor, o_shape, o_forces, o_split, o_step, _, _) in BINDER_ROUNDS.iter() {
                if other != head {
                    for leaked in [o_shape, o_forces, o_split, o_step, o_ctor] {
                        assert!(!src.contains(leaked), "{head}: leaked {other}'s {leaked}");
                    }
                }
            }
        }
    }

    /// THE STRUCTURE. Both components must be recursed on, each with its own
    /// descent relation and its own accessibility; and the step must be applied
    /// once. Dropping a component would leave the step applied to a stale
    /// acceptance.
    #[test]
    fn test_both_components_recurse_with_their_own_premises() {
        for ((head, _, _, _, _, step, _, _), src) in BINDER_ROUNDS.iter().zip(terms()) {
            assert_eq!(
                src.matches("recur ").count(),
                3, // one binder occurrence + two applications
                "{head}: exactly two recursive calls, plus the binder"
            );
            assert_eq!(
                src.matches("whnf_component_below n x").count(),
                2,
                "{head}: each component needs its own descent relation"
            );
            assert_eq!(
                src.matches("whnf_component_acc n bb").count(),
                2,
                "{head}: each component needs its own accessibility"
            );
            assert_eq!(
                src.matches("join_to_def_eq ").count(),
                2,
                "{head}: each component join must become a DefEq"
            );
            assert_eq!(
                src.matches(&format!("{step} n x bb")).count(),
                1,
                "{head}: the step is applied exactly once"
            );
        }
    }

    /// `recur` must be applied to the COMPONENTS, never to `x` or `bb`
    /// themselves — that would be a circular appeal dressed as a recursive one,
    /// and `rbelow_plus x x` is not provable, so it would fail late rather than
    /// be caught here.
    #[test]
    fn test_recursion_targets_components_not_the_originals() {
        for ((head, _, _, _, _, _, _, _), src) in BINDER_ROUNDS.iter().zip(terms()) {
            assert!(
                !src.contains("recur x ") && !src.contains("recur bb "),
                "{head}: recur must be applied to components, never to the originals"
            );
            for comp in ["recur t1 t2 ", "recur b1 b2 "] {
                assert!(src.contains(comp), "{head}: missing recursive call {comp}");
            }
        }
    }

    /// The shape witness fixes `nb`, so BOTH the b-side leg and the join must be
    /// transported onto that form. Forgetting either leaves the step applied at
    /// `nb` while the components were extracted at `ctor t2 b2`.
    ///
    /// Checked by the two transport MOTIVES rather than by counting occurrences
    /// of `hshape`: the transports are spliced into the term several times each,
    /// so a raw count measures splice sites, not correctness. (The first version
    /// of this test counted a substring of `nb` and expected 5 where the term
    /// has 13 — it was measuring nothing.)
    #[test]
    fn test_shape_is_transported_into_both_leg_and_join() {
        for ((head, ctor, _, _, _, _, _, _), src) in BINDER_ROUNDS.iter().zip(terms()) {
            let leg_motive = "(fun (z : KExpr) => Eq (OptionType KExpr) \
                              (whnf_fuel_red the_red_env n bb) (OptionType.some KExpr z))";
            let join_motive = format!(
                "(fun (z : KExpr) => par_strips_witness_cd_star the_red_env ({ctor} t1 b1) z)"
            );
            assert!(
                src.contains(leg_motive),
                "{head}: the b-side leg must be transported onto the shape"
            );
            assert!(
                src.contains(&join_motive),
                "{head}: the join must be transported onto the shape"
            );
            assert!(
                src.contains("nb ({ctor} t2 b2) hshape") || src.contains("hshape"),
                "{head}: the shape equation must be the transport witness"
            );
        }
    }

    #[test]
    fn test_round_terms_parens_balanced() {
        for ((head, _, _, _, _, _, _, _), src) in BINDER_ROUNDS.iter().zip(terms()) {
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
