// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pi injectivity at the DefEq level (Part of #464, #2851, #2859)
//!
//! If two Pi types are definitionally equal, their domains and codomains are
//! definitionally equal. Required for beta_preservation and the type-preservation
//! chain.
//!
//! **church_rosser_whnf retirement (the re-point):** derived through the
//! 3-way (β+ι+δ) confluence route instead of the FALSE `church_rosser_whnf`:
//!   def_eq_joinable (DefEq -> join witness) -> par_cd_pi_injectivity_{dom,cod}
//!   (join on Π descends to a join on the component) -> join_to_def_eq
//!   (join witness -> DefEq).
//!
//! The diamond underlying def_eq_joinable carries the eight faithful
//! RecEnv/DefEnv interfaces; here they are supplied as the SINGLE carried
//! hypothesis `RedEnvFaithful the_red_env` (projected into def_eq_joinable's
//! i1..i8). This keeps pi injectivity CONDITIONAL on the env's faithfulness
//! (the honest residual, dischargeable to the real kernel env at end-of-track)
//! — NOT discharged over the_red_env's placeholder value. ZERO axiom_deps: no
//! church_rosser_whnf, no domain axioms.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The eight `def_eq_joinable` interface arguments, recovered from the single
/// carried `hf : RedEnvFaithful the_red_env` via the projectors.
const HF_PROJ: &str = concat!(
    "(redenv_faithful_i1 the_red_env hf) (redenv_faithful_i2 the_red_env hf) ",
    "(redenv_faithful_i3 the_red_env hf) (redenv_faithful_i4 the_red_env hf) ",
    "(redenv_faithful_i5 the_red_env hf) (redenv_faithful_i6 the_red_env hf) ",
    "(redenv_faithful_i7 the_red_env hf) (redenv_faithful_i8 the_red_env hf) "
);

impl Specification {
    pub(super) fn add_pi_injectivity_def_eq(&mut self) -> Result<(), SpecError> {
        // Pi domain injectivity: DefEq (Pi A B) (Pi A' B') -> DefEq A A'
        // via the 3-way confluence route (carries RedEnvFaithful the_red_env).
        self.add_definition(SpecDefinition {
            name: "pi_injectivity_def_eq_dom".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr), ",
                "DefEq (KExpr.pi A B) (KExpr.pi A' B') -> DefEq A A'"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) ",
                    "(h : DefEq (KExpr.pi A B) (KExpr.pi A' B')) => ",
                    "join_to_def_eq A A' ",
                    "(par_cd_pi_injectivity_dom the_red_env A B A' B' ",
                    "(def_eq_joinable {hf}",
                    "(KExpr.pi A B) (KExpr.pi A' B') h))"
                ),
                hf = HF_PROJ,
            )),
            is_axiom: false,
            description: concat!(
                "Pi domain injectivity at DefEq level: if Π(A).B ≡ Π(A').B' then A ≡ A'. ",
                "Re-pointed through 3-way (β+ι+δ) confluence: def_eq_joinable -> ",
                "par_cd_pi_injectivity_dom -> join_to_def_eq. Carries RedEnvFaithful the_red_env ",
                "(projected into the diamond's i1..i8). ZERO axiom_deps — church_rosser_whnf retired. ",
                "Part of #464, #2851, #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "join_to_def_eq".to_string(),
                "par_cd_pi_injectivity_dom".to_string(),
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

        // Pi codomain injectivity: DefEq (Pi A B) (Pi A' B') -> DefEq B B'
        self.add_definition(SpecDefinition {
            name: "pi_injectivity_def_eq_cod".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr), ",
                "DefEq (KExpr.pi A B) (KExpr.pi A' B') -> DefEq B B'"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) ",
                    "(h : DefEq (KExpr.pi A B) (KExpr.pi A' B')) => ",
                    "join_to_def_eq B B' ",
                    "(par_cd_pi_injectivity_cod the_red_env A B A' B' ",
                    "(def_eq_joinable {hf}",
                    "(KExpr.pi A B) (KExpr.pi A' B') h))"
                ),
                hf = HF_PROJ,
            )),
            is_axiom: false,
            description: concat!(
                "Pi codomain injectivity at DefEq level: if Π(A).B ≡ Π(A').B' then B ≡ B'. ",
                "Re-pointed through 3-way (β+ι+δ) confluence: def_eq_joinable -> ",
                "par_cd_pi_injectivity_cod -> join_to_def_eq. Carries RedEnvFaithful the_red_env. ",
                "ZERO axiom_deps — church_rosser_whnf retired. Part of #464, #2851, #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "join_to_def_eq".to_string(),
                "par_cd_pi_injectivity_cod".to_string(),
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

        // ── pi_never_defeq_sort : THE head-constructor discrimination that
        // ctx_canonical_forms.rs:24 documents as missing — a Pi type is never
        // definitionally equal to a Sort. Same 3-way (β+ι+δ) confluence route as
        // the pi-injectivity siblings: def_eq_joinable strips DefEq to a common
        // reduct, the pi/sort star-inversion lemmas pin the reduct's head both
        // ways, and sort_ne_pi closes the contradiction. Ported from the
        // Aristotle-proven canonical-cond guide (its CR hypothesis is exactly the
        // in-tree def_eq_joinable + RedEnvFaithful the_red_env — no new assumption).
        // ZERO axiom_deps.
        self.add_definition(SpecDefinition {
            name: "pi_never_defeq_sort".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(A : KExpr) (B : KExpr) (u : Level), ",
                "DefEq (KExpr.pi A B) (KExpr.sort u) -> Empty"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(A : KExpr) (B : KExpr) (u : Level) ",
                    "(h : DefEq (KExpr.pi A B) (KExpr.sort u)) => ",
                    "par_strips_witness_cd_star.rec the_red_env (KExpr.pi A B) (KExpr.sort u) ",
                    "(fun (_w : par_strips_witness_cd_star the_red_env (KExpr.pi A B) (KExpr.sort u)) => Empty) ",
                    "(fun (c : KExpr) (l1 : par_reduces_cd_star the_red_env (KExpr.pi A B) c) (l2 : par_reduces_cd_star the_red_env (KExpr.sort u) c) => ",
                    "par_reduces_cd_star_pi_inv_eq the_red_env A B c Empty l1 ",
                    "(fun (A2 : KExpr) (B2 : KExpr) (heqpi : Eq KExpr c (KExpr.pi A2 B2)) (_lA : par_reduces_cd_star the_red_env A A2) (_lB : par_reduces_cd_star the_red_env B B2) => ",
                    "sort_ne_pi u A2 B2 Empty ",
                    "(Eq.trans KExpr (KExpr.sort u) c (KExpr.pi A2 B2) ",
                    "(Eq.symm KExpr c (KExpr.sort u) (par_reduces_cd_star_sort_inv_eq the_red_env u c l2)) ",
                    "heqpi))) ",
                    "(def_eq_joinable {hf}",
                    "(KExpr.pi A B) (KExpr.sort u) h)"
                ),
                hf = HF_PROJ,
            )),
            is_axiom: false,
            description: concat!(
                "A Pi type is never definitionally equal to a Sort — the head-constructor ",
                "discrimination ctx_canonical_forms.rs:24 documents as missing. Discharged through ",
                "3-way (β+ι+δ) confluence: def_eq_joinable -> pi/sort star-inversion -> sort_ne_pi. ",
                "Carries RedEnvFaithful the_red_env. ZERO axiom_deps. Ported from the canonical-cond ",
                "Aristotle guide (whose CR hypothesis is the in-tree def_eq_joinable)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "def_eq_joinable".to_string(),
                "par_strips_witness_cd_star".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star_pi_inv_eq".to_string(),
                "par_reduces_cd_star_sort_inv_eq".to_string(),
                "sort_ne_pi".to_string(),
                "Empty".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
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

        // sort_injectivity (DefEq (sort u)(sort v) -> u = v) is drafted but needs
        // kexpr_sort_inj, which registers at a LATER stage than this module —
        // re-homed to the univ_poly terminal layer (which runs after kexpr_beq_sound).

        Ok(())
    }
}
