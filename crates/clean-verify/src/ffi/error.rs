// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Error types for FFI boundary verification.

/// Parsing failures while building an [`FfiBoundarySpec`](super::FfiBoundarySpec).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum FfiBoundaryParseError {
    /// The Rust source did not parse.
    #[error("failed to parse Rust source: {0}")]
    ParseSource(String),
    /// A local type name was declared more than once.
    #[error("duplicate FFI type declaration `{0}`")]
    DuplicateTypeDecl(String),
    /// An attribute could not be interpreted.
    #[error("malformed attribute on `{item}`: {detail}")]
    MalformedAttribute { item: String, detail: String },
}

/// FFI boundary violations reported by [`FfiBoundaryChecker`](super::FfiBoundaryChecker).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, thiserror::Error)]
pub enum FfiBoundaryViolation {
    /// Raw pointer parameter lacks the required validity contract.
    #[error(
        "extern fn `{function}` parameter `{param}` is missing pointer validity preconditions"
    )]
    MissingPointerPrecondition { function: String, param: String },
    /// Raw pointer result lacks the required validity contract.
    #[error("extern fn `{function}` return value is missing pointer validity postconditions")]
    MissingPointerPostcondition { function: String },
    /// The callee lacks an explicit no-unwind contract.
    #[error("extern fn `{function}` is missing a no-unwind postcondition")]
    MissingNoUnwind { function: String },
    /// The ABI itself permits unwinding across the boundary.
    #[error("extern fn `{function}` uses ABI `{abi}` which may unwind across the FFI boundary")]
    UnwindAbi { function: String, abi: String },
    /// Rust references cannot be carried across a C boundary.
    #[error("extern fn `{function}` uses Rust reference `{ty}` in {position}")]
    ReferenceAcrossFfi {
        function: String,
        position: String,
        ty: String,
    },
    /// The type is Rust-specific or otherwise unsupported for FFI.
    #[error("extern fn `{function}` uses non-FFI-safe type `{ty}` in {position}: {reason}")]
    NonFfiSafeType {
        function: String,
        position: String,
        ty: String,
        reason: String,
    },
    /// The type is opaque to the verifier and therefore not trusted.
    #[error("extern fn `{function}` uses `{ty}` in {position} without a verified FFI layout")]
    UnknownType {
        function: String,
        position: String,
        ty: String,
    },
    /// A named composite type lacks `#[repr(C)]`.
    #[error("extern fn `{function}` uses `{ty}` in {position} without #[repr(C)]")]
    MissingReprC {
        function: String,
        position: String,
        ty: String,
    },
}
