// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HOL Light proof-object import.
//!
//! This module parses a small JSON encoding of HOL Light proof objects and
//! translates them into clean kernel declarations plus any support axioms
//! required for referenced HOL Light symbols.

mod ast;
mod parse;
mod translate;

#[cfg(test)]
mod verified_e2e_tests;

pub use ast::{
    HolProof, HolProofObject, HolTerm, HolTermSubstitution, HolType, HolTypeSubstitution, HolVar,
};
pub use parse::parse_proof_object;

use crate::{CleanMode, Declaration, Expr, Name, SourceSystem};

/// Result of translating one HOL Light proof object.
#[derive(Clone, Debug)]
pub struct TranslatedProofObject {
    /// Original HOL Light theorem name.
    pub source_name: String,
    /// clean theorem name used in the generated declaration.
    pub theorem_name: Name,
    /// Imported source system metadata.
    pub source_system: SourceSystem,
    /// clean mode required for the imported declaration.
    pub required_mode: CleanMode,
    /// The translated HOL theorem assumptions.
    pub assumptions: Vec<Expr>,
    /// The translated HOL theorem conclusion.
    pub conclusion: Expr,
    /// Closed theorem type: ambient binders, assumptions, then conclusion.
    pub theorem_type: Expr,
    /// Closed theorem proof term.
    pub proof: Expr,
    /// Support declarations for referenced HOL Light type operators/constants.
    pub support_declarations: Vec<Declaration>,
}

impl TranslatedProofObject {
    /// Convert the translated theorem into a kernel theorem declaration.
    #[must_use]
    pub fn theorem_declaration(&self) -> Declaration {
        Declaration::Theorem {
            name: self.theorem_name.clone(),
            level_params: Vec::new(),
            type_: self.theorem_type.clone(),
            value: self.proof.clone(),
        }
    }
}

/// Errors raised while importing HOL Light proof objects.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum HolLightImportError {
    /// JSON parse failure.
    #[error("failed to parse HOL Light proof object JSON: {0}")]
    Json(#[from] serde_json::Error),
    /// A type variable was referenced outside the current scope.
    #[error("unbound HOL type variable `{name}`")]
    UnboundTypeVariable { name: String },
    /// A term variable was referenced outside the current scope.
    #[error("unbound HOL term variable `{name}` with type {ty:?}")]
    UnboundTermVariable { name: String, ty: HolType },
    /// A function application had a non-function head type.
    #[error("expected function type in application, found {ty:?}")]
    ExpectedFunctionType { ty: HolType },
    /// A term's inferred type did not match the required type.
    #[error("type mismatch: expected {expected:?}, found {actual:?}")]
    TypeMismatch { expected: HolType, actual: HolType },
    /// A proof rule expected an equality conclusion.
    #[error("{rule} expects an equality conclusion")]
    ExpectedEquality { rule: &'static str },
    /// A proof rule expected a proposition (`bool`) term.
    #[error("{rule} expects a proposition of HOL type bool, found {ty:?}")]
    ExpectedProposition { rule: &'static str, ty: HolType },
    /// A proof rule expected a specific discharged assumption.
    #[error("{rule} could not find discharged assumption {term:?}")]
    MissingAssumption { rule: &'static str, term: HolTerm },
    /// The HOL ABS rule cannot abstract over assumptions that mention the binder.
    #[error("ABS binder `{name}` appears free in an assumption")]
    BinderEscapesAssumption { name: String },
    /// A substitution targeted a variable that is not in scope.
    #[error("substitution target `{name}` is not in scope")]
    InvalidSubstitutionTarget { name: String },
    /// Two free variables with the same name carried different HOL types.
    #[error("free variable `{name}` appears with inconsistent HOL types")]
    InconsistentFreeVariable { name: String },
}

/// Parse and translate a HOL Light proof object in one step.
pub fn import_proof_object_json(input: &str) -> Result<TranslatedProofObject, HolLightImportError> {
    let object = parse_proof_object(input)?;
    translate::translate_proof_object(&object)
}

/// Translate a parsed HOL Light proof object into clean kernel declarations.
pub fn translate_proof_object(
    object: &HolProofObject,
) -> Result<TranslatedProofObject, HolLightImportError> {
    translate::translate_proof_object(object)
}
