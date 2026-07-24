// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! TypePreservation Packet A — Pi/Sort/Lam propositional-equality specializers
//! (Part of #464).
//!
//! These lemmas transport `DefEq` into propositional `Eq` at Sort- and
//! Lam-shaped contexts without invoking the generic `def_eq_to_eq` HelperAxiom.
//! They mirror `pi_def_eq_eq` in `pi_injectivity_confluence.rs` and are proved
//! by the same confluence-backed recipe:
//!
//!   church_rosser_whnf + value_in_whnf + is_value.{sort,lam}
//!     → {sort,lam}_def_eq_eq  (Eq-level equality from DefEq)
//!
//! A third specializer, `def_eq_instantiate_both`, avoids the propositional
//! bridge entirely: it combines `def_eq_respects_subst` with
//! `def_eq_instantiate_arg_congr` via `DefEq.trans`, yielding the joint
//! body/argument congruence that `lam_typing_body_subst` needs (the second
//! `def_eq_to_eq` call site at `type_preservation_cases.rs:~220`).
//!
//! Packet A introduces these lemmas only. Packets B and C rewrite existing
//! call sites to consume them; Packet D removes the now-orphan
//! `def_eq_to_eq` declaration.
//!
//! Frontier update: `church_rosser_whnf` and `def_eq_to_eq` are both RETIRED
//! (#2859 / Brick 9). `def_eq_respects_subst` graduated to DerivedProved in
//! #2872 and `def_eq_instantiate_arg_congr` graduated with the proved
//! `def_eq_instantiate_arg_congr_at` leaf (#3221), so this file's registrations
//! are now all DerivedProved with zero axiom_deps.
//!
//! Design reference: `designs/2026-04-20-typepreservation-constructive-derivation.md`
//! (Section "Packet A — Pi/Sort propositional-equality specializers").

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the Packet-A propositional-equality specializers.
    ///
    /// Must run after:
    /// - `add_pi_injectivity_confluence` (registers `church_rosser_whnf`),
    /// - `add_whnf_lemmas` (registers `value_in_whnf`),
    /// - `add_substitution_def_eq_lemmas` (registers `def_eq_respects_subst`),
    /// - `add_type_preservation_subst` (registers `def_eq_instantiate_arg_congr`).
    pub(super) fn add_type_preservation_eq_specializers(&mut self) -> Result<(), SpecError> {
        // ---------------------------------------------------------------
        // sort_def_eq_eq: DefEq (Sort n) (Sort m) -> Eq (Sort n) (Sort m)
        // ---------------------------------------------------------------
        //
        // Analog of `pi_def_eq_eq` for Sort values. Sort n is a value
        // (`is_value.sort`), so `value_in_whnf` gives it as its own WHNF;
        // `church_rosser_whnf` then lifts DefEq into syntactic Eq.
        self.add_definition(SpecDefinition {
            name: "sort_def_eq_eq".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) (n : Level) (m : Level), ",
                "DefEq (KExpr.sort n) (KExpr.sort m) -> ",
                "Eq KExpr (KExpr.sort n) (KExpr.sort m)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) (n : Level) (m : Level) ",
                    "(h : DefEq (KExpr.sort n) (KExpr.sort m)) => ",
                    "par_cd_sort_injectivity the_red_env n m ",
                    "(def_eq_joinable ",
                    "(redenv_faithful_i1 the_red_env hf) (redenv_faithful_i2 the_red_env hf) ",
                    "(redenv_faithful_i3 the_red_env hf) (redenv_faithful_i4 the_red_env hf) ",
                    "(redenv_faithful_i5 the_red_env hf) (redenv_faithful_i6 the_red_env hf) ",
                    "(redenv_faithful_i7 the_red_env hf) (redenv_faithful_i8 the_red_env hf) ",
                    "(KExpr.sort n) (KExpr.sort m) h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Sort injectivity (DefEq -> Eq) via 3-way (β+ι+δ) confluence: DefEq (Sort n) (Sort m) ",
                "implies Eq (Sort n) (Sort m) because Sort is rigid. Re-pointed through ",
                "par_cd_sort_injectivity ∘ def_eq_joinable (carries RedEnvFaithful the_red_env). ",
                "ZERO axiom_deps — church_rosser_whnf retired. Part of #464, #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_cd_sort_injectivity".to_string(),
                "def_eq_joinable".to_string(),
                "RedEnvFaithful".to_string(),
                "redenv_faithful_i1".to_string(),
                "redenv_faithful_i2".to_string(),
                "redenv_faithful_i3".to_string(),
                "redenv_faithful_i4".to_string(),
                "redenv_faithful_i5".to_string(),
                "redenv_faithful_i6".to_string(),
                "redenv_faithful_i7".to_string(),
                "redenv_faithful_i8".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ---------------------------------------------------------------
        // lam_def_eq_eq: DefEq (Lam A b) (Lam A' b') -> Eq (Lam ..) (Lam ..)
        // ---------------------------------------------------------------
        //
        // Analog of `pi_def_eq_eq` for Lam values. Lam is a value
        // (`is_value.lam`). Packet C may consume this to rewrite the first
        // `def_eq_to_eq` call in `lam_typing_body_subst`.
        // lam_def_eq_eq RETIRED: it asserted DefEq (λA.b)(λA'.b') -> syntactic Eq,
        // which is FALSE under untyped beta (the components may be β-equal yet
        // syntactically distinct). It had zero proof-term consumers. Deleted with
        // church_rosser_whnf.

        // ---------------------------------------------------------------
        // def_eq_instantiate_both: joint body+argument substitution congruence
        // ---------------------------------------------------------------
        //
        // Given DefEq B B' and DefEq a a', produce
        //   DefEq (instantiate B a) (instantiate B' a')
        // without a propositional-equality detour. Packet B uses this to
        // rewrite the second `def_eq_to_eq` call site in `lam_typing_body_subst`
        // (`type_preservation_cases.rs:~220`).
        //
        // Proof is a single `DefEq.trans`:
        //   def_eq_respects_subst B B' a       : DefEq (inst B a)  (inst B' a)
        //   def_eq_instantiate_arg_congr B' a a' : DefEq (inst B' a) (inst B' a')
        //   DefEq.trans ...                     : DefEq (inst B a)  (inst B' a')
        //
        // Axiom-dep inheritance: both legs are DerivedProved with empty
        // axiom_deps — `def_eq_respects_subst` graduated in #2872 (the
        // `def_eq_to_eq` leaf it formerly carried is deleted, #2859) and
        // `def_eq_instantiate_arg_congr` graduated with the proved
        // `def_eq_instantiate_arg_congr_at` leaf (#3221) — so this lemma is
        // DerivedProved with zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "def_eq_instantiate_both".to_string(),
            type_src: concat!(
                "forall (B : KExpr) (B' : KExpr) (a : KExpr) (a' : KExpr), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "RedEnvFaithful the_red_env -> ",
                "DefEq B B' -> DefEq a a' -> ",
                "DefEq (instantiate B a) (instantiate B' a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (B : KExpr) (B' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(hf : RedEnvFaithful the_red_env) ",
                    "(hB : DefEq B B') (ha : DefEq a a') => ",
                    "DefEq.trans ",
                    "(instantiate B a) (instantiate B' a) (instantiate B' a') ",
                    "(def_eq_respects_subst B B' a wd wr hB) ",
                    "(def_eq_instantiate_arg_congr B' a a' hf ha)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Joint substitution congruence: if B ≡ B' and a ≡ a', then ",
                "B[a/0] ≡ B'[a'/0]. Proof: one DefEq.trans chaining ",
                "def_eq_respects_subst (body) with def_eq_instantiate_arg_congr ",
                "(argument). Avoids the propositional-Eq bridge used by ",
                "def_eq_to_eq. Packet B consumes this at the second call site ",
                "in lam_typing_body_subst. Part of #464 Packet A."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            // DerivedProved: both legs (def_eq_respects_subst #2872,
            // def_eq_instantiate_arg_congr #3221) are DerivedProved; the
            // church_rosser_whnf leaf it formerly inherited is retired (#2859).
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq.trans".to_string(),
                "def_eq_respects_subst".to_string(),
                "def_eq_instantiate_arg_congr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "type_preservation_eq_specializers_tests.rs"]
mod type_preservation_eq_specializers_tests;
