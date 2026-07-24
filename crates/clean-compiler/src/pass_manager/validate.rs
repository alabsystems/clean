// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LCNF validation pass — checks structural invariants between pipeline stages.
//!
//! Malformed IR can propagate silently through the optimization pipeline if
//! invariants are violated. This module provides a validation pass that checks:
//!
//! 1. **Scope correctness** — all FVar references resolve to an in-scope binding
//!    (parameter, let, fun, or join point)
//! 2. **Join point discipline** — `Jmp` targets must reference in-scope join points,
//!    not arbitrary functions or variables
//! 3. **Case completeness** — case expressions must have at least one alternative
//! 4. **No duplicate bindings** — each FVarId is bound at most once in any scope chain
//!
//! # Usage
//!
//! Enable validation on a `PassManager` via the builder method:
//!
//! ```rust,no_run
//! use clean_compiler::pass_manager::PassManager;
//!
//! let manager = PassManager::default_pipeline().with_validation();
//! ```
//!
//! Part of #2009.

use crate::lcnf::{Alt, Arg, Code, Decl, DeclValue, LetValue};
use clean_kernel::FVarId;
use std::collections::HashSet;

/// Errors discovered by the LCNF validation pass.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ValidationError {
    /// An FVar reference is not in scope.
    UnboundFVar { fvar: FVarId, context: &'static str },
    /// A `Jmp` targets an FVar that is not a join point.
    JmpToNonJoinPoint { fvar: FVarId },
    /// A `Cases` expression has zero alternatives.
    EmptyCases,
    /// An FVarId is bound more than once in the same scope chain.
    DuplicateBinding { fvar: FVarId },
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValidationError::UnboundFVar { fvar, context } => {
                write!(f, "unbound FVar {:?} in {}", fvar, context)
            }
            ValidationError::JmpToNonJoinPoint { fvar } => {
                write!(f, "Jmp targets non-join-point {:?}", fvar)
            }
            ValidationError::EmptyCases => {
                write!(f, "case expression has no alternatives")
            }
            ValidationError::DuplicateBinding { fvar } => {
                write!(f, "duplicate binding for {:?}", fvar)
            }
        }
    }
}

/// Validation context tracking what is in scope.
struct ValidateCtx {
    /// All FVarIds currently in scope (params + let + fun + join point bindings).
    scope: HashSet<FVarId>,
    /// FVarIds that are join points (subset of scope).
    join_points: HashSet<FVarId>,
    /// Accumulated errors.
    errors: Vec<ValidationError>,
}

impl ValidateCtx {
    fn new() -> Self {
        Self {
            scope: HashSet::new(),
            join_points: HashSet::new(),
            errors: Vec::new(),
        }
    }

    /// Try to bind an FVarId. Reports duplicate if already bound.
    fn bind(&mut self, fvar: FVarId) {
        if !self.scope.insert(fvar) {
            self.errors.push(ValidationError::DuplicateBinding { fvar });
        }
    }

    /// Bind an FVarId as a join point.
    fn bind_join_point(&mut self, fvar: FVarId) {
        self.bind(fvar);
        self.join_points.insert(fvar);
    }

    /// Check that an FVarId is in scope.
    fn check_fvar(&mut self, fvar: FVarId, context: &'static str) {
        if !self.scope.contains(&fvar) {
            self.errors
                .push(ValidationError::UnboundFVar { fvar, context });
        }
    }

    /// Check that an FVarId is a valid join point target.
    fn check_jmp_target(&mut self, fvar: FVarId) {
        if !self.scope.contains(&fvar) {
            self.errors.push(ValidationError::UnboundFVar {
                fvar,
                context: "jmp target",
            });
        } else if !self.join_points.contains(&fvar) {
            self.errors
                .push(ValidationError::JmpToNonJoinPoint { fvar });
        }
    }

    /// Check FVar references inside an Arg.
    fn check_arg(&mut self, arg: &Arg, context: &'static str) {
        if let Arg::FVar(fvar) = arg {
            self.check_fvar(*fvar, context);
        }
    }

    /// Save and restore scope for nested scopes (case alternatives, function bodies).
    fn scoped<F>(&mut self, f: F)
    where
        F: FnOnce(&mut Self),
    {
        let saved_scope = self.scope.clone();
        let saved_jps = self.join_points.clone();
        f(self);
        self.scope = saved_scope;
        self.join_points = saved_jps;
    }
}

/// Validate a single LCNF declaration.
///
/// Returns a list of validation errors (empty if the declaration is well-formed).
pub(crate) fn validate_decl(decl: &Decl) -> Vec<ValidationError> {
    let mut ctx = ValidateCtx::new();

    // Bind declaration parameters into scope.
    for param in &decl.params {
        ctx.bind(param.fvar_id);
    }

    // Validate the body if it has code.
    if let DeclValue::Code(code) = &decl.body {
        validate_code(&mut ctx, code);
    }

    ctx.errors
}

/// Validate a Code block recursively.
fn validate_code(ctx: &mut ValidateCtx, code: &Code) {
    match code {
        Code::Let(decl, body) => {
            validate_let_value(ctx, &decl.value);
            ctx.bind(decl.fvar_id);
            validate_code(ctx, body);
        }
        Code::Fun(fun_decl, body) => {
            // The function itself is in scope for the continuation.
            ctx.bind(fun_decl.fvar_id);

            // Validate the function body in a nested scope with its params.
            ctx.scoped(|ctx| {
                for param in &fun_decl.params {
                    ctx.bind(param.fvar_id);
                }
                validate_code(ctx, &fun_decl.body);
            });

            validate_code(ctx, body);
        }
        Code::JoinPoint(jp_decl, body) => {
            // The join point is in scope for the continuation.
            ctx.bind_join_point(jp_decl.fvar_id);

            // Validate the join point body in a nested scope with its params.
            ctx.scoped(|ctx| {
                for param in &jp_decl.params {
                    ctx.bind(param.fvar_id);
                }
                validate_code(ctx, &jp_decl.body);
            });

            validate_code(ctx, body);
        }
        Code::Cases(cases) => {
            // Scrutinee must be in scope.
            ctx.check_fvar(cases.scrutinee, "cases scrutinee");

            // Must have at least one alternative.
            if cases.alts.is_empty() {
                ctx.errors.push(ValidationError::EmptyCases);
            }

            // Validate each alternative in its own scope.
            for alt in &cases.alts {
                validate_alt(ctx, alt);
            }
        }
        Code::Jmp { jp, args } => {
            ctx.check_jmp_target(*jp);
            for arg in args {
                ctx.check_arg(arg, "jmp argument");
            }
        }
        Code::Return(fvar) => {
            ctx.check_fvar(*fvar, "return");
        }
        Code::Unreachable(_) => {
            // Nothing to validate — type is a kernel Expr, not an FVar.
        }
    }
}

/// Validate FVar references inside a LetValue.
fn validate_let_value(ctx: &mut ValidateCtx, value: &LetValue) {
    match value {
        LetValue::Lit(_) | LetValue::Erased => {}
        LetValue::Proj { structure, .. } => {
            ctx.check_fvar(*structure, "projection structure");
        }
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for arg in args {
                ctx.check_arg(arg, "const/ctor argument");
            }
        }
        LetValue::FVar { fvar, args } => {
            ctx.check_fvar(*fvar, "fvar application");
            for arg in args {
                ctx.check_arg(arg, "fvar application argument");
            }
        }
        LetValue::Reuse { slot, args, .. } => {
            ctx.check_fvar(*slot, "reuse slot");
            for arg in args {
                ctx.check_arg(arg, "reuse argument");
            }
        }
    }
}

/// Validate a case alternative.
fn validate_alt(ctx: &mut ValidateCtx, alt: &Alt) {
    match alt {
        Alt::Ctor { params, body, .. } => {
            ctx.scoped(|ctx| {
                for param in params {
                    ctx.bind(param.fvar_id);
                }
                validate_code(ctx, body);
            });
        }
        Alt::Default(body) => {
            ctx.scoped(|ctx| {
                validate_code(ctx, body);
            });
        }
    }
}
