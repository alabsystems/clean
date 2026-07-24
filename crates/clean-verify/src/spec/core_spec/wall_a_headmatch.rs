// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Wall-A completeness statement machinery (Aristotle port, strategy guide
//! `/tmp/ari-walla/project_aristotle/WallA.lean`, namespace `WallA`,
//! [propext, Quot.sound]-only closure there).
//!
//! The mirror's two targets map to the in-tree world as follows:
//!
//!  1. `def_eq_joinable_mirror` (DefEq -> multi-step join) — ALREADY IN-TREE:
//!     `def_eq_joinable` (`def_eq_joinable.rs`, Brick 6 of the
//!     church_rosser_whnf retirement) is EXACTLY this statement over the live
//!     vocabulary: `DefEq e1 e2 -> par_strips_witness_cd_star the_red_env e1
//!     e2`, carrying the i1..i8 faithful interfaces (the mirror's `DenvClosed`
//!     = i5/i6). Mapped, NOT re-ported.
//!  2. `def_eq_whnf_complete` (DefEq + WhnfTo both sides -> HeadMatch of the
//!     normal forms) — the algorithmic-completeness half. This module lands
//!     its STATEMENT MACHINERY: the `HeadMatch` inductive (the success
//!     condition of one round of the kernel's structural comparison on two
//!     WHNF results — heads match, components are DefEq), non-vacuity
//!     witnesses, and the soundness anchor `head_match_reflects` (HeadMatch
//!     na nb -> DefEq na nb — the converse sanity direction, tying HeadMatch
//!     to the declarative judgment).
//!
//!     The completeness theorem itself is LANDED: `def_eq_whnf_complete`
//!     (`wall_a_completeness.rs`, the WallAIota β+ι+δ mirror port, zeta-
//!     extended for the genuine `KExpr.let_` constructor per the ConfZeta
//!     guide) proves it over the FULL beta+iota+delta+zeta
//!     `par_reduces_cd_star`, together with the
//!     previously-missing head-rigidity star-inversion family (dead-const +
//!     iota-aware neutral-spine inversions; sort/lam/pi reused from
//!     `par_reduces_cd_injectivity.rs`) and the iota-aware WHNF vocabulary
//!     (`iota_immune`/`iota_neutral`/`iota_whnf` — PARALLEL predicates; this
//!     module's trusted `is_neutral`/`is_whnf` surface stays untouched).
//!
//! Zero new axioms: `HeadMatch` lowers to Inductive/Constructor/Recursor;
//! every lemma here is DerivedProved with an explicit term and empty closure.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the Wall-A `HeadMatch` statement machinery.
    pub(super) fn add_wall_a_headmatch(&mut self) -> Result<(), SpecError> {
        // HeadMatch a b: one round of the kernel is_def_eq structural
        // comparison succeeds on the two whnf results a/b — matching heads,
        // DefEq components. The const arm carries const_whnf (the in-tree
        // "this const head does not delta-unfold" neutrality condition —
        // mirror `denv c = none`); app matches neutral spines pointwise.
        self.add_inductive(
            concat!(
                "inductive HeadMatch : KExpr -> KExpr -> Type\n",
                "| sort : forall (n : Level), HeadMatch (KExpr.sort n) (KExpr.sort n)\n",
                "| const : forall (n : Name) (us : ListType Level), const_whnf n us -> ",
                "HeadMatch (KExpr.const n us) (KExpr.const n us)\n",
                "| lam : forall (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr), ",
                "DefEq A A2 -> DefEq b b2 -> ",
                "HeadMatch (KExpr.lam A b) (KExpr.lam A2 b2)\n",
                "| pi : forall (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr), ",
                "DefEq A A2 -> DefEq B B2 -> ",
                "HeadMatch (KExpr.pi A B) (KExpr.pi A2 B2)\n",
                "| app : forall (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr), ",
                "HeadMatch f f2 -> DefEq a a2 -> ",
                "HeadMatch (KExpr.app f a) (KExpr.app f2 a2)"
            ),
            "Success condition of one round of the kernel's structural def-eq comparison on two \
             WHNF results (mirror WallA.HeadMatch): heads match, components are DefEq (the \
             comparator recurses into components — carried here as DefEq subgoals). const \
             requires const_whnf (a whnf-neutral const head does not delta-unfold); app matches \
             neutral spines pointwise. Deliberately NO let_ arm: a genuine KExpr.let_ node is \
             never a WHNF result (it always zeta-steps), so a let_ head cannot appear on either \
             side. Statement machinery for the def_eq_whnf_complete \
             follow-up; the join half is the landed def_eq_joinable.",
        )?;

        // Non-vacuity witnesses (Guard 4 discipline): the family is inhabited
        // at a rigid head and at a binder head with genuine DefEq components.
        self.add_definition(SpecDefinition {
            name: "headmatch_sort_witness".to_string(),
            type_src: "HeadMatch (KExpr.sort Level.zero) (KExpr.sort Level.zero)".to_string(),
            value_src: Some("HeadMatch.sort Level.zero".to_string()),
            is_axiom: false,
            description: "Non-vacuity witness: HeadMatch holds at a sort head. DerivedProved. \
                          Wall-A statement machinery."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["HeadMatch".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "headmatch_lam_witness".to_string(),
            type_src: concat!(
                "HeadMatch (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) ",
                "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "HeadMatch.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero) ",
                    "(KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) ",
                    "(DefEq.refl (KExpr.sort Level.zero)) ",
                    "(DefEq.refl (KExpr.bvar Nat.zero))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Non-vacuity witness: HeadMatch holds at a lam head with DefEq \
                          components. DerivedProved. Wall-A statement machinery."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "HeadMatch".to_string(),
                "DefEq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // head_match_reflects: the SOUNDNESS anchor — a successful structural
        // head comparison implies declarative DefEq of the two normal forms
        // (the converse direction of the def_eq_whnf_complete target; ties
        // HeadMatch to the in-tree judgment so the statement machinery is
        // semantically grounded, not free-floating).
        self.add_definition(SpecDefinition {
            name: "head_match_reflects".to_string(),
            type_src: "forall (a : KExpr) (b : KExpr), HeadMatch a b -> DefEq a b".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : KExpr) (b : KExpr) (h : HeadMatch a b) => ",
                    "HeadMatch.rec ",
                    "(fun (x : KExpr) (y : KExpr) (_ : HeadMatch x y) => DefEq x y) ",
                    "(fun (n : Level) => DefEq.refl (KExpr.sort n)) ",
                    "(fun (n : Name) (us : ListType Level) (_ : const_whnf n us) => ",
                    "DefEq.refl (KExpr.const n us)) ",
                    "(fun (A : KExpr) (A2 : KExpr) (b0 : KExpr) (b2 : KExpr) ",
                    "(hA : DefEq A A2) (hb : DefEq b0 b2) => ",
                    "DefEq.lam_cong A A2 b0 b2 hA hb) ",
                    "(fun (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr) ",
                    "(hA : DefEq A A2) (hB : DefEq B B2) => ",
                    "DefEq.pi_cong A A2 B B2 hA hB) ",
                    "(fun (f : KExpr) (f2 : KExpr) (a0 : KExpr) (a2 : KExpr) ",
                    "(_hm : HeadMatch f f2) (ha : DefEq a0 a2) ",
                    "(ihf : DefEq f f2) => ",
                    "DefEq.app_cong f f2 a0 a2 ihf ha) ",
                    "a b h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Soundness anchor: HeadMatch a b -> DefEq a b (one comparison round's \
                          success implies declarative DefEq — the converse direction of the \
                          def_eq_whnf_complete farm target). DerivedProved via HeadMatch.rec + \
                          the DefEq congruences. Wall-A statement machinery."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "HeadMatch".to_string(),
                "HeadMatch.rec".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.lam_cong".to_string(),
                "DefEq.pi_cong".to_string(),
                "DefEq.app_cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::build_spec_with_stack;

    /// The HeadMatch machinery registers, is DerivedProved with empty axiom
    /// closure, and re-typechecks against the live kernel environment.
    #[test]
    fn test_wall_a_headmatch_registers_and_reverifies() {
        let spec = build_spec_with_stack();
        for name in [
            "HeadMatch",
            "HeadMatch.rec",
            "HeadMatch.sort",
            "HeadMatch.const",
            "HeadMatch.lam",
            "HeadMatch.pi",
            "HeadMatch.app",
        ] {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the Wall-A HeadMatch stage"
            );
        }
        for name in [
            "headmatch_sort_witness",
            "headmatch_lam_witness",
            "head_match_reflects",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(!def.is_axiom, "{name} must not be an axiom");
            assert!(def.value_src.is_some(), "{name} must carry a proof term");
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must declare empty axiom closure: {:?}",
                def.axiom_deps
            );
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} should re-typecheck in the spec env: {e:?}"));
        }
    }
}
