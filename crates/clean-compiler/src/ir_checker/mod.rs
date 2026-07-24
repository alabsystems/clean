// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! L5IR Validity Checker
//!
//! Validates IR before code generation to catch malformed IR early.
//! Prevents invalid IR from generating incorrect code or crashing backends.
//!
//! # Validation Rules
//!
//! - **V1**: Variables must be defined before use
//! - **V2**: No duplicate variable definitions
//! - **J1**: Join points must be defined before jump
//! - **J2**: Join point arguments must match declaration arity
//! - **T1**: RC operations require object types
//! - **T2**: Projection index must be valid
//! - **F1**: Full application arity must match
//! - **F2**: Partial application must have fewer args than arity
//! - **C1**: Constructor tag and field limits
//! - **C2**: Constructor field_types length consistency
//! - **C3**: Constructor arg count matches declared fields
//! - **T3**: Reset/Reuse slot must be object type
//!
//! # Reference
//!
//! Lean 4: `src/Lean/Compiler/IR/Checker.lean` (255 lines)
//! Author: Leonardo de Moura
//!
//! Part of #996

mod checker;
#[cfg(test)]
mod tests;

use crate::compiler_env::CompilerEnv;
use crate::ir::{IRDecl, IRType, JoinPointId, VarId};
use clean_kernel::Name;
use std::collections::HashMap;
use thiserror::Error;

use checker::IRChecker;

/// Runtime limits from Lean 4 object system.
pub(crate) const MAX_CTOR_TAG: u32 = 65535;
pub(crate) const MAX_CTOR_FIELDS: u32 = 256;

/// IR validation error.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum IRError {
    #[error("undefined variable: x{}", _0.0)]
    UndefinedVariable(VarId),

    #[error("undefined join point: jp{}", _0.0)]
    UndefinedJoinPoint(JoinPointId),

    #[error("duplicate definition: index {0}")]
    DuplicateDefinition(u32),

    #[error("join point jp{jp} arity mismatch: expected {expected}, got {actual}", jp = .jp.0)]
    JoinPointArityMismatch {
        jp: JoinPointId,
        expected: usize,
        actual: usize,
    },

    #[error("function {function} arity mismatch: expected {expected}, got {actual}")]
    ArityMismatch {
        function: Name,
        expected: usize,
        actual: usize,
    },

    #[error("type mismatch: expected {expected}, got {actual:?} in {context}")]
    TypeMismatch {
        expected: &'static str,
        actual: IRType,
        context: &'static str,
    },

    #[error("box type mismatch: expected {expected:?}, got {actual:?}")]
    BoxTypeMismatch { expected: IRType, actual: IRType },

    #[error("invalid projection index {idx} on type {ty:?}")]
    InvalidProjection { idx: u32, ty: IRType },

    #[error("constructor {name} tag {tag} exceeds max {max}")]
    CtorTagTooLarge { name: Name, tag: u32, max: u32 },

    #[error("constructor {name} has {count} fields, max is {max}")]
    CtorTooManyFields { name: Name, count: u32, max: u32 },

    #[error("unknown function: {0}")]
    UnknownFunction(Name),

    #[error(
        "too many args for partial application of {function}: arity {arity}, provided {provided}"
    )]
    TooManyArgs {
        function: Name,
        arity: usize,
        provided: usize,
    },

    #[error(
        "partial application arity {arity} is less than captured arg count {num_captured} for {function}"
    )]
    PartialApplyArityTooSmall {
        function: Name,
        arity: u16,
        num_captured: usize,
    },

    #[error(
        "partial application arity {arity} does not match function {function} parameter count {expected}"
    )]
    PartialApplyArityMismatch {
        function: Name,
        arity: u16,
        expected: usize,
    },

    #[error("invalid scalar type {ty:?} in {op}")]
    InvalidScalarType { ty: IRType, op: &'static str },

    #[error("unexpected body form in {context}")]
    UnexpectedBodyForm { context: &'static str },

    #[error("duplicate constructor tag {tag} in case alternatives")]
    DuplicateCaseTag { tag: u32 },

    #[error(
        "constructor {name} field count mismatch: num_scalars ({num_scalars}) + num_objects ({num_objects}) != field_types.len() ({field_types_len})"
    )]
    CtorFieldCountMismatch {
        name: Name,
        num_scalars: u32,
        num_objects: u32,
        field_types_len: usize,
    },

    #[error(
        "constructor {name} arg count mismatch: {num_args} args provided, but num_scalars ({num_scalars}) + num_objects ({num_objects}) = {expected}"
    )]
    CtorArgCountMismatch {
        name: Name,
        num_args: usize,
        num_scalars: u32,
        num_objects: u32,
        expected: u32,
    },
}

/// Entry type for variable tracking.
#[derive(Clone, Debug)]
pub(crate) enum LocalEntry {
    /// Function parameter with type.
    Param(IRType),
    /// Local variable with type.
    Local(IRType),
}

/// Tracks what's in scope during IR checking.
#[derive(Clone, Debug, Default)]
pub(crate) struct LocalContext {
    /// Variable entries (params and locals), keyed by VarId.
    var_entries: HashMap<u32, LocalEntry>,
    /// Join point entries, keyed by JoinPointId.
    jp_entries: HashMap<u32, Vec<(VarId, IRType)>>,
}

impl LocalContext {
    /// Add a parameter to the context.
    pub fn add_param(&mut self, var: VarId, ty: IRType) {
        self.var_entries.insert(var.0, LocalEntry::Param(ty));
    }

    /// Add a local variable to the context.
    pub fn add_local(&mut self, var: VarId, ty: IRType) {
        self.var_entries.insert(var.0, LocalEntry::Local(ty));
    }

    /// Add a join point to the context.
    pub fn add_jp(&mut self, jp: JoinPointId, params: Vec<(VarId, IRType)>) {
        self.jp_entries.insert(jp.0, params);
    }

    /// Check if a join point is defined.
    pub fn is_jp(&self, jp: JoinPointId) -> bool {
        self.jp_entries.contains_key(&jp.0)
    }

    /// Get the type of a variable (param or local).
    pub fn get_type(&self, var: VarId) -> Option<&IRType> {
        match self.var_entries.get(&var.0) {
            Some(LocalEntry::Param(ty)) | Some(LocalEntry::Local(ty)) => Some(ty),
            _ => None,
        }
    }

    /// Get the parameters of a join point.
    pub fn get_jp_params(&self, jp: JoinPointId) -> Option<&[(VarId, IRType)]> {
        self.jp_entries.get(&jp.0).map(|v| v.as_slice())
    }

    /// Check if a variable is in scope (param or local).
    pub fn is_in_scope(&self, var: VarId) -> bool {
        matches!(
            self.var_entries.get(&var.0),
            Some(LocalEntry::Param(_)) | Some(LocalEntry::Local(_))
        )
    }
}

/// Check if a type is an object type (can be inc/dec'd).
///
/// Delegates to `IRType::is_object()` to avoid duplicating the variant list.
/// Includes `Struct` and `Union` which are represented as `clean_obj*`.
pub(crate) fn is_object_type(ty: &IRType) -> bool {
    ty.is_object()
}

// ════════════════════════════════════════════════════════════════════════════
// Public entry points
// ════════════════════════════════════════════════════════════════════════════

/// Validate an IR declaration.
pub fn check_decl(decl: &IRDecl, all_decls: &[IRDecl]) -> Result<(), IRError> {
    let mut checker = IRChecker::new(decl, all_decls);
    checker.check()
}

/// Validate multiple IR declarations.
pub fn check_decls(decls: &[IRDecl]) -> Result<(), IRError> {
    let decl_index: HashMap<&Name, usize> = decls
        .iter()
        .enumerate()
        .map(|(i, d)| (&d.name, i))
        .collect();
    for decl in decls {
        let mut checker = IRChecker::new_with_index(decl, decls, decl_index.clone());
        checker.check()?;
    }
    Ok(())
}

/// Validate an IR declaration using a unified `CompilerEnv`. Part of #1970.
pub fn check_decl_with_env(
    decl: &IRDecl,
    all_decls: &[IRDecl],
    env: &CompilerEnv,
) -> Result<(), IRError> {
    let mut checker = IRChecker::new_with_env(decl, all_decls, env);
    checker.check()
}

/// Validate multiple IR declarations using a unified `CompilerEnv`. Part of #1970.
pub fn check_decls_with_env(decls: &[IRDecl], env: &CompilerEnv) -> Result<(), IRError> {
    for decl in decls {
        let mut checker = IRChecker::new_with_env(decl, decls, env);
        checker.check()?;
    }
    Ok(())
}
