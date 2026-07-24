// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! External certificate formats for linear arithmetic and SMT proof verification.

mod alethe;
mod error;
mod rational;
mod verify;

pub use alethe::{verify_alethe_certificate, ExternalAletheCert};
pub use error::{ExternalCertError, ExternalCertErrorCode};
pub use rational::ExternalRational;
pub use verify::{
    verify_entailment_certificate, verify_farkas_certificate, ConstraintKind, ExternalCertificate,
    ExternalEntailmentCert, ExternalFarkasCert, ExternalLinearConstraint,
};

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_fixtures;
#[cfg(test)]
mod tests_source_hygiene;
