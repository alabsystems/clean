// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::ay_types::{
    verify_strict_logic_behavior, verify_strict_proof_profile, StrictLogicBehavior,
};
use super::{
    AyBackend, AyConfig, AyLogic, AyProofBackend, ProofProfile, SmtLibTranslator, SmtSolver,
    SmtVerifyPolicy, TrustBudget, VariableMapping,
};

impl SmtSolver {
    /// Direct-proof trust budget derived from the public verify policy and the
    /// selected logic. The current bounded rollout enforces zero trust for the
    /// strict proof-producing fragments with positive evidence:
    /// `VerifyStrict + QF_UF`, `VerifyStrict + QF_LIA`, and
    /// `VerifyStrict + QF_LRA`. Every other combination keeps the legacy
    /// unlimited budget until the repository has positive evidence to widen it
    /// further.
    pub(in super::super) fn direct_reconstruction_budget(
        policy: SmtVerifyPolicy,
        logic: AyLogic,
    ) -> TrustBudget {
        match policy {
            SmtVerifyPolicy::VerifyStrict
                if verify_strict_logic_behavior(logic)
                    == StrictLogicBehavior::SupportedZeroTrust =>
            {
                TrustBudget::ZeroTrust
            }
            _ => TrustBudget::Unlimited,
        }
    }

    /// Create an SMT solver based on configuration and verify policy
    ///
    /// Policy selection:
    /// - `TrustSolver`: Uses Fast (AyBackend)
    /// - Other policies: Uses Verifiable (AyProofBackend) with proof production
    ///
    /// # Contract
    ///
    /// REQUIRES: `logic` is a valid Ay logic for the problem domain
    /// ENSURES: `TrustSolver` policy produces `SmtSolver::Fast`
    /// ENSURES: Non-`TrustSolver` policies produce `SmtSolver::Verifiable` with `produce_proofs == true`
    pub(crate) fn from_config(config: &AyConfig, logic: AyLogic) -> Self {
        let backend_config = config.to_backend_config(logic);
        let reconstruction_budget =
            Self::direct_reconstruction_budget(config.verify_policy(), logic);

        match config.verify_policy() {
            SmtVerifyPolicy::TrustSolver => SmtSolver::Fast(AyBackend::with_config(backend_config)),
            SmtVerifyPolicy::ExtractOnly => new_verifiable_solver(
                AyProofBackend::with_config(backend_config.enable_proofs()),
                SmtVerifyPolicy::ExtractOnly,
                reconstruction_budget,
            ),
            SmtVerifyPolicy::VerifyCarcara => {
                let proof_config = backend_config.proof_profile(ProofProfile::carcara_verified());
                new_verifiable_solver(
                    AyProofBackend::with_config(proof_config),
                    SmtVerifyPolicy::VerifyCarcara,
                    reconstruction_budget,
                )
            }
            SmtVerifyPolicy::VerifyStrict => {
                let proof_config = backend_config.proof_profile(verify_strict_proof_profile());
                new_verifiable_solver(
                    AyProofBackend::with_config(proof_config),
                    SmtVerifyPolicy::VerifyStrict,
                    reconstruction_budget,
                )
            }
        }
    }
}

pub(super) fn create_smt_backend(config: &AyConfig, logic: AyLogic) -> SmtSolver {
    SmtSolver::from_config(config, logic)
}

fn new_verifiable_solver(
    backend: AyProofBackend,
    policy: SmtVerifyPolicy,
    reconstruction_budget: TrustBudget,
) -> SmtSolver {
    #[cfg(not(test))]
    let _ = policy;

    SmtSolver::Verifiable {
        backend,
        translator: SmtLibTranslator::new(),
        var_map: VariableMapping::new(),
        exists_bindings: Vec::new(),
        next_exists_placeholder_fvar: 0,
        #[cfg(test)]
        policy,
        reconstruction_budget,
    }
}
