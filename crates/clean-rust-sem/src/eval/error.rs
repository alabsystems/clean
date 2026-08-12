// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::ownership::BorrowError as OwnershipBorrowError;
use thiserror::Error;

/// Typed evaluator errors for the core expression interpreter.
///
/// This sits alongside the crate-wide error type so the evaluator can migrate
/// hot paths away from raw strings without forcing a whole-module conversion.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum EvalError {
    #[error("type error in {context}: expected {expected}, got {actual}")]
    TypeError {
        expected: String,
        actual: String,
        context: String,
    },

    #[error("unbound variable `{name}`")]
    UnboundVariable { name: String },

    #[error("field `{field}` not found on {struct_name}")]
    FieldNotFound { struct_name: String, field: String },

    #[error("unsupported operation `{op}`: {context}")]
    UnsupportedOperation { op: String, context: String },

    #[error("division by zero")]
    DivisionByZero,

    #[error("index {index} out of bounds for length {len}")]
    IndexOutOfBounds { index: usize, len: usize },

    #[error("overflow during `{op}`")]
    OverflowError { op: String },

    #[error("borrow error [{kind}]: {context}")]
    BorrowError { kind: String, context: String },

    #[error("deref failed: {detail}")]
    DerefFailed { detail: String },

    #[error("deref write failed: {detail}")]
    DerefWriteFailed { detail: String },

    #[error("{0}")]
    Other(String),
}

impl From<String> for EvalError {
    fn from(value: String) -> Self {
        Self::Other(value)
    }
}

impl From<&str> for EvalError {
    fn from(value: &str) -> Self {
        Self::Other(value.to_string())
    }
}

impl From<crate::error::RustSemError> for EvalError {
    fn from(value: crate::error::RustSemError) -> Self {
        Self::Other(value.to_string())
    }
}

impl From<OwnershipBorrowError> for EvalError {
    fn from(value: OwnershipBorrowError) -> Self {
        Self::BorrowError {
            kind: borrow_error_kind(&value).to_string(),
            context: value.to_string(),
        }
    }
}

fn borrow_error_kind(error: &OwnershipBorrowError) -> &'static str {
    match error {
        OwnershipBorrowError::MoveWhileBorrowed { .. } => "move_while_borrowed",
        OwnershipBorrowError::MutBorrowWhileSharedBorrow { .. } => "mut_borrow_while_shared_borrow",
        OwnershipBorrowError::MutBorrowWhileMutBorrow { .. } => "mut_borrow_while_mut_borrow",
        OwnershipBorrowError::SharedBorrowWhileMutBorrow { .. } => "shared_borrow_while_mut_borrow",
        OwnershipBorrowError::UseAfterMove { .. } => "use_after_move",
        OwnershipBorrowError::UseOfUninitialized { .. } => "use_of_uninitialized",
        OwnershipBorrowError::AssignToImmutable { .. } => "assign_to_immutable",
        OwnershipBorrowError::AssignWhileBorrowed { .. } => "assign_while_borrowed",
        OwnershipBorrowError::LifetimeTooShort { .. } => "lifetime_too_short",
        OwnershipBorrowError::ReturnLocalRef { .. } => "return_local_ref",
        OwnershipBorrowError::AliasingLocationMissing { .. } => "aliasing_location_missing",
        OwnershipBorrowError::AliasingParentMissing { .. } => "aliasing_parent_missing",
        OwnershipBorrowError::AliasingUnknownTag { .. } => "aliasing_unknown_tag",
        OwnershipBorrowError::AliasingInvalidAccess { .. } => "aliasing_invalid_access",
        OwnershipBorrowError::AliasingProtected { .. } => "aliasing_protected",
    }
}

#[cfg(test)]
mod tests {
    use super::EvalError;
    use crate::ownership::{BorrowError as OwnershipBorrowError, Place};

    #[test]
    fn wraps_legacy_string_errors() {
        let error = EvalError::from("legacy evaluator failure".to_string());

        assert_eq!(
            error,
            EvalError::Other("legacy evaluator failure".to_string())
        );
        assert_eq!(error.to_string(), "legacy evaluator failure");
    }

    #[test]
    fn displays_structured_errors() {
        let type_error = EvalError::TypeError {
            expected: "bool".to_string(),
            actual: "i32".to_string(),
            context: "if condition".to_string(),
        };
        assert_eq!(
            type_error.to_string(),
            "type error in if condition: expected bool, got i32"
        );
    }

    #[test]
    fn converts_borrow_errors_with_kind() {
        let error = EvalError::from(OwnershipBorrowError::AssignToImmutable {
            place: Place::Local(0),
        });

        assert_eq!(
            error.to_string(),
            "borrow error [assign_to_immutable]: cannot assign to `Local(0)`: not mutable"
        );
    }
}
