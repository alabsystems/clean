// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Alethe proof certificate verification for external SMT proof submission.
//!
//! Enables external callers (ay, other SMT solvers) to submit Alethe proofs
//! for verification via the JSON-RPC certificate API (Part of #1195).

use super::error::ExternalCertError;
use super::verify::ensure_version;
use serde::{Deserialize, Serialize};

/// An external Alethe proof certificate submitted for verification.
///
/// Contains an SMT-LIB2 problem and its Alethe proof of unsatisfiability.
/// Verification delegates to Carcara when the `ay-smt` feature is enabled.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExternalAletheCert {
    pub version: String,
    pub problem: String,
    pub proof: String,
}

/// Verify an Alethe certificate by checking its proof against the problem.
///
/// Delegates to the Carcara proof checker (via clean-auto) when the `ay-smt`
/// feature is enabled. Returns an error when the verifier is unavailable.
///
/// # REQUIRES
/// - `cert.version == "1.0"`
/// - `cert.problem` is a non-empty SMT-LIB2 problem string
/// - `cert.proof` is a non-empty Alethe proof string
///
/// # ENSURES
/// - On `Ok(true)`: Carcara accepted the proof with no holes
/// - On `Ok(false)`: Carcara only accepted the proof as holey/incomplete
///
/// # Errors
/// - `InvalidSchema`: version mismatch or empty problem/proof
/// - `VerifierNotAvailable`: ay-smt feature not enabled
/// - `ProofVerificationFailed`: Carcara encountered an error
pub fn verify_alethe_certificate(cert: &ExternalAletheCert) -> Result<bool, ExternalCertError> {
    verify_alethe_certificate_until(cert, None)
}

/// [`verify_alethe_certificate`], refused once `deadline` passes.
///
/// Carcara's resource budget bounds what one proof step builds, not how long a proof takes, so a
/// caller checking certificates it does not trust gives a deadline: the checker reads it before
/// and after every command and its comparisons as they go
/// (`third-party/carcara/DOWNSTREAM.md`, "The checker stops at a deadline").
///
/// # Errors
/// - those of [`verify_alethe_certificate`]
/// - `Timeout`: the check reached `deadline` before it ended (the proof is not accepted)
pub fn verify_alethe_certificate_until(
    cert: &ExternalAletheCert,
    deadline: Option<std::time::Instant>,
) -> Result<bool, ExternalCertError> {
    ensure_version(&cert.version)?;
    if cert.problem.is_empty() {
        return Err(ExternalCertError::invalid_schema(
            "problem text must not be empty".to_string(),
        ));
    }
    if cert.proof.is_empty() {
        return Err(ExternalCertError::invalid_schema(
            "proof text must not be empty".to_string(),
        ));
    }

    #[cfg(all(feature = "ay-smt", not(target_arch = "wasm32")))]
    {
        use clean_auto::bridge::ay_contract::verify_alethe_proof_until;
        match verify_alethe_proof_until(&cert.problem, &cert.proof, deadline) {
            Ok(valid) => Ok(valid),
            #[cfg(feature = "carcara-verify")]
            Err(e @ clean_auto::bridge::ay_contract::VerifyError::CarcaraDeadline(_)) => {
                Err(ExternalCertError {
                    code: super::error::ExternalCertErrorCode::Timeout,
                    detail: e.to_string(),
                })
            }
            Err(e) => Err(ExternalCertError::proof_verification_failed(e.to_string())),
        }
    }

    // The vendored checker is native: the wasm32 contract links none.
    #[cfg(all(feature = "ay-smt", target_arch = "wasm32"))]
    {
        let _ = deadline;
        Err(ExternalCertError::verifier_not_available(
            "no Alethe proof checker is linked on wasm32".to_string(),
        ))
    }

    #[cfg(not(feature = "ay-smt"))]
    {
        let _ = deadline;
        Err(ExternalCertError::verifier_not_available(
            "ay-smt feature required for Alethe proof verification".to_string(),
        ))
    }
}
