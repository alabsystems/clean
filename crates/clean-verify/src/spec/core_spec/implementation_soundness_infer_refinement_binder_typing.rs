// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Binder-typing step projections — RETIRED (#461).
//!
//! This module formerly held the five skolem-named lam/pi typing-step
//! projections (kernel_infer_lam_domain_sort, kernel_infer_lam_body_typing,
//! kernel_infer_pi_domain_sort, kernel_infer_pi_codomain_sort,
//! kernel_infer_pi_imax_result_step). Their TYPES named the six retired infer
//! Skolems (KernelLamBodyType / KernelLamDomainLevel / KernelPiDomainLevel /
//! KernelPiCodomainLevel), so once those Skolems are packaged inside the
//! Lam/PiInferWitness existential inductives they can no longer be stated. Their
//! sole consumers were `kernel_infer_lam_sound` / `kernel_infer_pi_sound`, which
//! now recover the domain-sort / body-typing / codomain-sort / imax-result
//! evidence DIRECTLY inside their Lam/PiInferWitness.rec elimination (the bound
//! witness fields), so the standalone projections are no longer needed. The
//! function is kept (empty) so its registration call site is unchanged.

use crate::spec::error::SpecError;
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_infer_refinement_binder_typing(
        &mut self,
    ) -> Result<(), SpecError> {
        // All five skolem-named binder typing-step projections are retired; the
        // Lam/PiInferWitness.rec elimination in the *_sound bridges supplies the
        // typing evidence internally. Nothing to register here.
        Ok(())
    }
}
