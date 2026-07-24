// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification of Rust FFI boundary contracts for `extern` declarations.
//!
//! This checker is intentionally conservative:
//! - raw pointers are allowed only with explicit validity contracts
//! - Rust references are rejected at the FFI boundary
//! - named composite types must be declared locally and use `#[repr(C)]`
//! - unwind-capable ABIs are rejected
//!
//! ## Module structure
//!
//! - [`types`]: Core data structures (specs, contracts, type refs)
//! - [`checker`]: Structural checker deriving safety obligations
//! - [`verifier`]: Rule-based verifier with focused safety rules
//! - [`parser`]: `syn`-based Rust source parsing
//! - [`error`]: Error and violation types
//! - [`helpers`]: Shared predicate functions

pub mod checker;
pub mod error;
pub(crate) mod helpers;
pub mod parser;
#[cfg(test)]
mod tests;
pub mod types;
pub mod verifier;
pub(crate) mod verifier_type_rules;

pub use checker::FfiBoundaryChecker;
pub use error::{FfiBoundaryParseError, FfiBoundaryViolation};
pub use types::{
    FfiBoundarySpec, FfiEnumVariant, FfiExternBlock, FfiField, FfiFunctionContract, FfiParam,
    FfiPostcondition, FfiPrecondition, FfiSafetyCheck, FfiTypeDecl, FfiTypeDeclKind, FfiTypeRef,
    FfiValueTarget,
};
pub use verifier::{FfiRule, FfiVerifier, FfiViolation, FfiViolationSeverity};
