// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed error definitions for the clean-rust-sem crate.
//!
//! Replaces `Result<_, String>` with structured, matchable error variants.

use crate::memory::MemoryError;
use crate::ownership::{BorrowError, Place};
use crate::types::RustType;

/// Error type for the Rust semantics evaluator and supporting modules.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum RustSemError {
    /// An evaluation error with a descriptive message.
    ///
    /// Covers general interpreter errors (undefined variables, type mismatches,
    /// unsupported operations, etc.) that do not fit a more specific variant.
    #[error("{0}")]
    Eval(String),

    /// `format!` intrinsic was called without a template argument.
    #[error("format! intrinsic expects at least one argument")]
    FormatIntrinsicMissingArgument,

    /// `format!` intrinsic expected a string template as its first argument.
    #[error("format! intrinsic expects a string template argument")]
    FormatIntrinsicTemplateMustBeString,

    /// Runtime format rendering failed inside the `format!` intrinsic.
    #[error("format! failed: {source}")]
    FormatIntrinsicFailed {
        /// Underlying format renderer failure.
        #[source]
        source: Box<RustSemError>,
    },

    /// Intrinsic method/function received the wrong number of arguments.
    #[error("method `{method}` takes {expected} {arg_word}, got {got}")]
    IntrinsicArityMismatch {
        /// Method or intrinsic name.
        method: String,
        /// Expected number of arguments.
        expected: usize,
        /// Actual number of arguments received.
        got: usize,
        /// `arg` or `args` for exact historical wording.
        arg_word: &'static str,
    },

    /// Intrinsic expected a string argument.
    #[error("{intrinsic} expects a string argument")]
    IntrinsicStringArgumentRequired {
        /// Intrinsic or method name.
        intrinsic: String,
    },

    /// Intrinsic expected a char argument.
    #[error("{intrinsic} expects a char argument")]
    IntrinsicCharArgumentRequired {
        /// Intrinsic or method name.
        intrinsic: String,
    },

    /// Intrinsic expected an unsigned-integer (index) argument.
    #[error("{intrinsic} expects a usize index argument")]
    IntrinsicUsizeArgumentRequired {
        /// Intrinsic or method name.
        intrinsic: String,
    },

    /// Memory allocation or access error.
    #[error("memory error: {0}")]
    Memory(#[from] MemoryError),

    /// Borrow checker / stacked-borrows violation.
    #[error("borrow error: {0}")]
    Borrow(#[from] BorrowError),

    /// Failed to reserve a two-phase mutable borrow for a method receiver.
    #[error("two-phase receiver reservation failed for `{receiver_expr}`: {source}")]
    TwoPhaseReceiverReservation {
        /// Receiver expression debug rendering.
        receiver_expr: String,
        /// Underlying borrow-checking violation.
        #[source]
        source: BorrowError,
    },

    /// Failed to activate a deferred two-phase mutable receiver borrow.
    #[error("two-phase receiver activation failed for `{param_name}`: {source}")]
    TwoPhaseReceiverActivation {
        /// Parameter name being bound.
        param_name: String,
        /// Underlying borrow-checking violation.
        #[source]
        source: BorrowError,
    },

    /// Failed to install a call-duration protector for a reference parameter.
    #[error("protected borrow setup failed for `{param_name}`: {source}")]
    ProtectedBorrowSetup {
        /// Parameter name being bound.
        param_name: String,
        /// Underlying borrow-checking violation.
        #[source]
        source: BorrowError,
    },

    /// Failed to validate a stacked-borrows read through a local binding.
    #[error("stacked borrows read rejected for `{name}`: {source}")]
    StackedBorrowsReadRejected {
        /// Binding name being read.
        name: String,
        /// Underlying borrow-checking violation.
        #[source]
        source: BorrowError,
    },

    /// Attempted an unsafe operation outside of an `unsafe` block.
    #[error("{operation} is an unsafe operation and requires an unsafe block or function")]
    UnsafeRequired {
        /// Description of the operation that requires unsafe.
        operation: String,
    },

    /// Format string error (mismatched placeholders, unsupported values, etc.).
    #[error("format error: {0}")]
    Format(String),

    /// A tracked place could not be resolved or projected.
    #[error("place error: {0}")]
    Place(String),

    /// A tracked index place could not be concretized to a local index.
    #[error("tracked index place is not concrete")]
    TrackedIndexPlaceNotConcrete,

    /// A tracked local index did not fit into the platform `usize`.
    #[error("tracked index {index} does not fit in usize")]
    TrackedIndexTooLarge {
        /// The tracked local index.
        index: u32,
    },

    /// Tracked place projection does not support dereference nodes.
    #[error("tracked deref place is not supported")]
    TrackedDerefUnsupported,

    /// Tracked place projection does not support downcast nodes.
    #[error("tracked downcast place is not supported")]
    TrackedDowncastUnsupported,

    /// Failed to determine the tracked root for a projected place.
    #[error("cannot resolve tracked place root for `{place:?}`")]
    TrackedPlaceRootUnresolved {
        /// The place whose root could not be found.
        place: Place,
    },

    /// Struct field lookup failed.
    #[error("field `{field}` not found on struct")]
    StructFieldMissing {
        /// Missing field name.
        field: String,
    },

    /// Active enum-variant struct payload field lookup failed.
    #[error("field `{field}` not found on active enum variant")]
    EnumFieldMissing {
        /// Missing field name.
        field: String,
    },

    /// Attempted field access on an enum payload that is not struct-shaped.
    #[error("field access on enum variant without struct payload")]
    FieldAccessRequiresStructPayload,

    /// Attempted field access on a value that is not struct-shaped.
    #[error("field access on non-struct value")]
    FieldAccessOnNonStructValue,

    /// Attempted field assignment on an enum payload that is not struct-shaped.
    #[error("field assignment on enum variant without struct payload")]
    FieldAssignmentRequiresStructPayload,

    /// Attempted field assignment on a value that is not struct-shaped.
    #[error("field assignment on non-struct value")]
    FieldAssignmentOnNonStructValue,

    /// Indexed access was outside the bounds of the active container.
    #[error("index {index} out of bounds")]
    IndexOutOfBounds {
        /// Out-of-bounds index.
        index: usize,
    },

    /// Attempted indexed access on an enum payload that is not tuple-shaped.
    #[error("index access on enum variant without tuple payload")]
    IndexAccessRequiresTuplePayload,

    /// Attempted indexed access on a value that does not support indexing.
    #[error("index access on non-array value")]
    IndexAccessOnNonArrayValue,

    /// Attempted indexed assignment on an enum payload that is not tuple-shaped.
    #[error("index assignment on enum variant without tuple payload")]
    IndexAssignmentRequiresTuplePayload,

    /// Attempted indexed assignment on a value that does not support indexing.
    #[error("index assignment on non-array value")]
    IndexAssignmentOnNonArrayValue,

    /// Failed to read a tracked root value because it is no longer bound.
    #[error("cannot read unbound tracked root `{root:?}`")]
    UnboundTrackedRootRead {
        /// Root place that was expected to be bound.
        root: Place,
    },

    /// Failed to write a tracked root value because it is no longer bound.
    #[error("cannot assign to unbound tracked root `{root:?}`")]
    UnboundTrackedRootWrite {
        /// Root place that was expected to be bound.
        root: Place,
    },

    /// A for-loop received a non-iterable value or mismatched range bounds.
    #[error("iteration error: {0}")]
    Iteration(String),

    /// The interpreter could not topologically resolve scoped const/static initializers.
    #[error("unresolved const/static items in scope: {unresolved}")]
    UnresolvedConstStaticItems {
        /// Comma-separated unresolved item descriptions.
        unresolved: String,
    },

    /// Const/static initializer evaluation failed with a regular interpreter error.
    #[error("failed to resolve const/static `{name}`: {detail}")]
    ConstStaticResolutionFailed {
        /// Const/static item name.
        name: String,
        /// Underlying interpreter detail.
        detail: String,
    },

    /// Const/static initializer attempted to return from its scope.
    #[error("failed to resolve const/static `{name}`: initializer returned from scope")]
    ConstStaticInitializerReturned {
        /// Const/static item name.
        name: String,
    },

    /// Const/static initializer attempted to break from a loop.
    #[error("failed to resolve const/static `{name}`: initializer broke out of scope")]
    ConstStaticInitializerBrokeOut {
        /// Const/static item name.
        name: String,
    },

    /// Const/static initializer attempted to continue a loop.
    #[error("failed to resolve const/static `{name}`: initializer continued a loop")]
    ConstStaticInitializerContinued {
        /// Const/static item name.
        name: String,
    },

    /// Const/static initializer panicked during evaluation.
    #[error("failed to resolve const/static `{name}`: initializer panicked: {message}")]
    ConstStaticInitializerPanicked {
        /// Const/static item name.
        name: String,
        /// Panic payload rendered by the interpreter.
        message: String,
    },

    /// `for` loop input was not an array, tuple, or bounded integer range.
    #[error("for loop requires an array, tuple, or bounded integer range")]
    ForLoopRequiresIterable,

    /// `for` loop range endpoints used different integer types.
    #[error("for loop range bounds must use the same integer type")]
    ForLoopRangeTypeMismatch,

    /// `for` loop range did not have both bounds.
    #[error("for loop ranges must have both start and end bounds")]
    ForLoopRangeMissingBounds,

    /// `for` loop range bounds were not integer values.
    #[error("for loop range bounds must be signed or unsigned integers")]
    ForLoopRangeNonIntegerBounds,

    /// `for` loop range iteration overflowed while incrementing.
    #[error("for loop range iteration overflowed")]
    ForLoopRangeOverflow,

    /// Impl method parameter count disagrees with the corresponding trait method.
    #[error("impl method `{impl_fn_name}` has {impl_param_count} params, trait method `{trait_method_name}` expects {expected_params}{expected_suffix}")]
    ImplMethodParamCountMismatch {
        /// Impl function name being validated.
        impl_fn_name: String,
        /// Trait method name being validated against.
        trait_method_name: String,
        /// Actual impl parameter count.
        impl_param_count: usize,
        /// Expected trait parameter count before any `self` adjustment.
        expected_params: usize,
        /// Either `""` or `" (+ self)"` to preserve current wording.
        expected_suffix: &'static str,
    },

    /// Impl method parameter type disagrees with the corresponding trait method.
    #[error("impl method `{impl_fn_name}` param {param_index} has type {actual:?}, trait expects {expected:?}")]
    ImplMethodParamTypeMismatch {
        /// Impl function name being validated.
        impl_fn_name: String,
        /// 1-based parameter index after any receiver.
        param_index: usize,
        /// Actual parameter type after materialization.
        actual: RustType,
        /// Expected trait parameter type after materialization.
        expected: RustType,
    },

    /// Impl method return type disagrees with the corresponding trait method.
    #[error("impl method `{impl_fn_name}` returns {actual:?}, trait expects {expected:?}")]
    ImplMethodReturnTypeMismatch {
        /// Impl function name being validated.
        impl_fn_name: String,
        /// Actual return type after materialization.
        actual: RustType,
        /// Expected trait return type after materialization.
        expected: RustType,
    },

    /// A generic type parameter cannot be soundly hoisted to a `Π`/`∀` binder.
    ///
    /// Emitted by `translate::translate_generic_type` to fail closed on
    /// parameter shapes whose hoisting would require machinery not yet
    /// implemented (associated-type bounds, etc.). Failing closed here mirrors
    /// `trust-mir-extract`'s rejection of `TyKind::Param`: a missed translation
    /// only costs coverage, whereas emitting a wrong sort would be unsound.
    #[error("cannot hoist generic parameter `{param}`: {reason}")]
    GenericHoistUnsupported {
        /// Name of the offending type parameter.
        param: String,
        /// Why the parameter cannot be hoisted (e.g. associated-type bound).
        reason: String,
    },
}

impl RustSemError {
    /// Create an [`Eval`](RustSemError::Eval) error from a displayable value.
    #[must_use]
    pub fn eval(msg: impl Into<String>) -> Self {
        Self::Eval(msg.into())
    }

    /// Create a `format!` intrinsic wrapper error from an underlying formatter error.
    #[must_use]
    pub fn format_intrinsic_failed(source: RustSemError) -> Self {
        Self::FormatIntrinsicFailed {
            source: Box::new(source),
        }
    }

    /// Create an intrinsic arity mismatch while preserving `arg` vs `args`.
    #[must_use]
    pub fn intrinsic_arity(method: impl Into<String>, expected: usize, got: usize) -> Self {
        Self::IntrinsicArityMismatch {
            method: method.into(),
            expected,
            got,
            arg_word: if expected == 1 { "arg" } else { "args" },
        }
    }

    /// Create an intrinsic string-argument type error.
    #[must_use]
    pub fn intrinsic_string_argument(intrinsic: impl Into<String>) -> Self {
        Self::IntrinsicStringArgumentRequired {
            intrinsic: intrinsic.into(),
        }
    }

    /// Create an intrinsic char-argument type error.
    #[must_use]
    pub fn intrinsic_char_argument(intrinsic: impl Into<String>) -> Self {
        Self::IntrinsicCharArgumentRequired {
            intrinsic: intrinsic.into(),
        }
    }

    /// Create an intrinsic usize-index-argument type error.
    #[must_use]
    pub fn intrinsic_usize_argument(intrinsic: impl Into<String>) -> Self {
        Self::IntrinsicUsizeArgumentRequired {
            intrinsic: intrinsic.into(),
        }
    }

    /// Create a [`Format`](RustSemError::Format) error from a displayable value.
    #[must_use]
    pub fn format(msg: impl Into<String>) -> Self {
        Self::Format(msg.into())
    }

    /// Create a [`Place`](RustSemError::Place) error from a displayable value.
    #[must_use]
    pub fn place(msg: impl Into<String>) -> Self {
        Self::Place(msg.into())
    }

    /// Create an [`Iteration`](RustSemError::Iteration) error from a displayable value.
    #[must_use]
    pub fn iteration(msg: impl Into<String>) -> Self {
        Self::Iteration(msg.into())
    }

    /// Create an impl/trait parameter-count mismatch.
    #[must_use]
    pub fn impl_method_param_count_mismatch(
        impl_fn_name: impl Into<String>,
        trait_method_name: impl Into<String>,
        impl_param_count: usize,
        expected_params: usize,
        has_self_receiver: bool,
    ) -> Self {
        Self::ImplMethodParamCountMismatch {
            impl_fn_name: impl_fn_name.into(),
            trait_method_name: trait_method_name.into(),
            impl_param_count,
            expected_params,
            expected_suffix: if has_self_receiver { " (+ self)" } else { "" },
        }
    }
}
