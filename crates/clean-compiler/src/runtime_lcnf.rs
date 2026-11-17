// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Diagnostic lowering of captured runtime bodies, with no logical Environment.
//!
//! This route does not register partial definitions, construct source admission,
//! infer executable closure from a stored body, or certify the resulting LCNF.
//! Its local type checks are conditional on the exact captured declaration
//! headers and family metadata. Missing context and unsupported syntax remain
//! typed errors; there are no synthetic `_` types or fabricated unit bodies.
//! All raw parts/rows remain accessible, including unselected snapshots/errors.
//! Existing Environment-based compiler passes are not a runtime adapter.

mod catalog;
mod context;
#[cfg(feature = "trust-ir-backend")]
mod emission;
mod ir;
mod lower;
mod matcher;
mod source;
mod source_scoped;
pub use source_scoped::RuntimeScopedEnvironmentCapture;
#[cfg(test)]
mod source_tests;
#[cfg(test)]
mod tests;
mod typing;

pub use catalog::RuntimeCatalogDeclaration;
use clean_kernel::{Expr, Name};
pub use context::{
    RuntimeContext, RuntimeModuleCapture, RuntimeModuleInput, RuntimeProvenance, RuntimeRowOrigin,
};
#[cfg(feature = "trust-ir-backend")]
pub use emission::{
    RuntimeCallEdge, RuntimeCallKind, RuntimeEmission, RuntimeEmissionError, RuntimeEmissionOutput,
    RuntimeImport,
};
pub use ir::{RuntimeIrOutput, RuntimeIrRow, RuntimeIrSpecialization, RuntimeIrStatus};
pub use source::{
    RuntimeEnvironmentCapture, RuntimeEnvironmentPopulation, RuntimeEnvironmentRow,
    RuntimeEnvironmentRowFailure, RuntimeSourceCaptureLimits, RuntimeSourceRecord,
};

#[derive(Clone, Copy, Debug)]
pub struct RuntimeLimits {
    pub steps: usize,
    pub depth: usize,
    pub declarations: usize,
}

impl Default for RuntimeLimits {
    fn default() -> Self {
        Self {
            steps: 100_000,
            depth: 128,
            declarations: 1_024,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum RuntimeLowerError {
    #[error("captured context is incomplete: {0}")]
    Capture(String),
    #[error("required exact declaration is absent: {0:?}")]
    Missing(Name),
    #[error("required exact declaration has ambiguous occurrences: {0:?}")]
    Ambiguous(Name),
    #[error("declaration fields are incomplete: {name:?}: {detail}")]
    Incomplete { name: Name, detail: String },
    #[error("unsupported declaration metadata: {name:?}: {detail}")]
    Family { name: Name, detail: String },
    #[error("required stored body is unavailable: {0:?}")]
    MissingBody(Name),
    #[error("universe arity mismatch: {name:?}, expected {expected}, found {found}")]
    UniverseArity {
        name: Name,
        expected: usize,
        found: usize,
    },
    #[error("unbound universe parameter: {0:?}")]
    UniverseParameter(Name),
    #[error("unbound source/local variable")]
    UnboundVariable,
    #[error("expected a function type, found {0:?}")]
    ExpectedFunction(Expr),
    #[error("expected a sort, found {0:?}")]
    ExpectedSort(Expr),
    #[error("type mismatch: expected {expected:?}, found {found:?}")]
    TypeMismatch { expected: Expr, found: Expr },
    #[error("unsupported runtime expression: {0}")]
    Unsupported(&'static str),
    #[error("runtime lowering resource bound exhausted: {0}")]
    Resource(&'static str),
}

#[derive(Clone, Debug)]
pub struct RuntimeLcnfOutput {
    pub declaration: crate::lcnf::Decl,
    pub origin: RuntimeRowOrigin,
    /// Exact dependency-closed captured rows, including stored bodies and all
    /// family/constructor/recursor RHS metadata. Not an executable population.
    pub dependencies: Vec<RuntimeRowOrigin>,
}
