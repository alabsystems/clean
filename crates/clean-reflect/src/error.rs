// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The reflector's typed error surface.
//!
//! `Unsupported` is the fail-closed variant: any trust-ir construct outside
//! Fragment-1 (branching/CFG/loops/atomics/closures/memory-model/...) MUST
//! produce `Unsupported` rather than a wrong or placeholder `Expr`.

use trust_ir::ValueId;

/// Errors produced while reflecting a trust-ir construct into a clean `Expr`.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReflectError {
    /// Construct is outside Fragment-1: the reflector fails closed rather than
    /// emit an `Expr` whose soundness the Lean proofs do not cover.
    #[error("unsupported construct for Fragment-1 reflection: {construct}")]
    Unsupported {
        /// Human-readable name of the rejected construct.
        construct: String,
    },
    /// The input trust-ir is structurally invalid for the requested arm.
    #[error("malformed trust-ir: {0}")]
    Malformed(String),
    /// An operand could not be resolved to a reflected value term.
    #[error("operand {0:?} not resolvable to a bvVar/bvConst")]
    UnresolvedOperand(ValueId),
    /// The construct is IN-fragment but structurally wrong in a way a correct
    /// lowering can never produce (a `Load` of a never-written cell — an
    /// uninitialized read, UB in trust-ir semantics — a `Dealloc` of a
    /// reference-counted `CleanHeap` cell, likewise UB, a self-inconsistent
    /// recorded struct layout, or a Fragment-5 body that breaks the
    /// ownership balance: a use after free, a count underflow or a leak).
    /// Distinct from `Unsupported` so the mint gate escalates it to a REFUSAL
    /// (detected wrong-code emission) instead of an out-of-fragment skip; it
    /// must never fall back to a denotation.
    #[error("wrong emission (in-fragment structural violation): {0}")]
    WrongEmission(String),
}

impl ReflectError {
    /// Construct an [`ReflectError::Unsupported`] from any displayable label.
    #[must_use]
    pub fn unsupported(construct: impl Into<String>) -> Self {
        Self::Unsupported {
            construct: construct.into(),
        }
    }
}
