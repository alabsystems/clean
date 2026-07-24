// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AyBackend solver methods: backend construction and satisfiability checking.

use super::translator::LeanExprTranslator;
use super::{
    AyBackend, AyBackendConfig, AyError, AyLogic, AyProofCertificateInfo, AySolveEnvelope,
    AySolveResult, AySolveVerification, AyUnknownReason,
};
use ay::{ConsumerAcceptanceError, SolveResult, Solver, SolverError};
use ay_translate::TranslationState;

impl AyBackend {
    /// Create a new Ay backend with the specified logic
    pub fn new(logic: AyLogic) -> Self {
        Self::with_config(AyBackendConfig::new(logic))
    }

    /// Create a new Ay backend with full configuration
    ///
    /// This is the preferred constructor for customized settings.
    pub fn with_config(config: AyBackendConfig) -> Self {
        let logic = config.logic();
        let mut solver = Solver::try_new(logic.to_ay_logic())
            .expect("invariant: supported logic must produce a valid solver");

        // Apply timeout if configured
        if let Some(ms) = config.timeout_ms() {
            solver.set_timeout(Some(std::time::Duration::from_millis(ms)));
        }

        // Note: produce_proofs is handled by AyProofBackend, not AyBackend
        // AyBackend uses Solver which doesn't produce proofs. For proofs,
        // use AyProofBackend::with_config(AyBackendConfig::with_proofs(logic))

        Self {
            solver,
            state: TranslationState::new(),
            logic,
            last_consumer_sat: false,
            translator: LeanExprTranslator::default(),
        }
    }

    /// Get the logic this backend is configured for
    pub fn logic(&self) -> AyLogic {
        self.logic
    }

    pub(super) fn map_quantifier_error(error: SolverError) -> AyError {
        match error {
            SolverError::SortMismatch { expected, got, .. } => AyError::TypeMismatch {
                expected: expected.to_string(),
                got: got
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
            },
            SolverError::InvalidArgument { operation, message }
            | SolverError::InvalidTrigger { operation, message } => {
                AyError::InvalidInput { operation, message }
            }
            SolverError::SolverPanic(message) => AyError::SolverPanic(message),
            other => AyError::ScriptError(other.to_string()),
        }
    }

    fn envelope_from_solve_details(details: ay::SolveDetails) -> AySolveEnvelope {
        let (result, proof_certificate, forced_unknown_reason) = match details.accept_for_consumer()
        {
            Ok(solve_result) => {
                let cert_info = match solve_result {
                    SolveResult::Unsat(cert) => Some(AyProofCertificateInfo {
                        is_complete: cert.sat_certificate().is_complete(),
                    }),
                    _ => None,
                };
                (solve_result.into(), cert_info, None)
            }
            Err(ConsumerAcceptanceError::SatModelNotValidated) => (
                AySolveResult::Unknown,
                None,
                Some(AyUnknownReason::InternalError),
            ),
            Err(_) => (
                AySolveResult::Unknown,
                None,
                Some(AyUnknownReason::InternalError),
            ),
        };
        let unknown_reason =
            forced_unknown_reason.or_else(|| details.unknown_reason.map(Into::into));
        let verification = AySolveVerification {
            summary: details.verification.into(),
            level: details.verification_level.into(),
        };
        AySolveEnvelope::Solved {
            result,
            unknown_reason,
            verification,
            proof_certificate,
        }
    }

    pub(super) fn clear_last_consumer_sat(&mut self) {
        self.last_consumer_sat = false;
    }

    /// Check satisfiability
    ///
    /// Uses ay's panic-safe detailed solve path so clean preserves verification
    /// metadata and degrades consumer-rejected SAT results to Unknown/InternalError.
    pub fn check_sat(&mut self) -> AySolveEnvelope {
        let report = match self.solver.try_check_sat_with_details() {
            Ok(details) => Self::envelope_from_solve_details(details),
            Err(SolverError::SolverPanic(message)) => AySolveEnvelope::PanicUnknown {
                panic_reason: message,
            },
            Err(error) => AySolveEnvelope::PanicUnknown {
                panic_reason: error.to_string(),
            },
        };
        self.last_consumer_sat = report.is_sat();
        report
    }
}
