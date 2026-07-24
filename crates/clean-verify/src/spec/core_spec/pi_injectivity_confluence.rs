// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Confluence-backed Pi injectivity infrastructure (Part of #464, #2851, #2859)
//!
//! HISTORICAL: this module formerly registered the `church_rosser_whnf`
//! HelperAxiom and its `pi_def_eq_eq` corollary. Both are now RETIRED.
//!
//! `church_rosser_whnf` was formally adjudicated FALSE-as-stated
//! (`designs/2026-06-14-church-rosser-whnf-verdict.md`): WHNF is weak, so two
//! pi-headed values can be DefEq yet syntactically distinct. With `DefEq.beta`
//! now untyped, that counterexample is constructible, so the axiom could not be
//! left registered. The TRUE component-injectivity lemmas the consumers actually
//! need (`pi_injectivity_def_eq_{dom,cod}`, `sort_def_eq_eq`) are now derived
//! constructively from confluence via `join_to_def_eq` ∘ the cd-relation
//! injectivity lemmas ∘ `def_eq_joinable` (carrying a `RedEnvFaithful the_red_env`
//! hypothesis, NOT an axiom) — see `par_reduces_cd_sound.rs`,
//! `pi_injectivity_def_eq.rs`, and `type_preservation_eq_specializers.rs`.
//!
//! This module retains only the (now empty) registration hook so the bundle
//! staging order is unchanged. `pi_def_eq_eq` / `lam_def_eq_eq` (false Eqs) are
//! deleted; `sort_def_eq_eq` (a true Eq) survives, re-pointed off the axiom.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_pi_injectivity_confluence(&mut self) -> Result<(), SpecError> {
        // church_rosser_whnf + pi_def_eq_eq retired (#2859): the false WHNF
        // Church-Rosser axiom and its pi corollary are deleted. The consumers
        // are re-pointed onto the constructive confluence tower
        // (join_to_def_eq ∘ par_cd_*_injectivity ∘ def_eq_joinable). Nothing is
        // registered here anymore; the hook is kept for bundle-order stability.
        Ok(())
    }
}
