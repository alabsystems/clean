// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! External certificate types for cross-tool integration.
//!
//! This module provides JSON-serializable certificate formats for external
//! tools to submit proofs that clean can verify. Used for cross-tool
//! integration with systems like gamma-crown.

pub mod external;

pub use external::{
    verify_entailment_certificate, verify_farkas_certificate, ConstraintKind, ExternalCertError,
    ExternalCertErrorCode, ExternalCertificate, ExternalEntailmentCert, ExternalFarkasCert,
    ExternalLinearConstraint, ExternalRational,
};
