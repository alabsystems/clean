// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Closure Creation and Capture for Compiled Lean 4 Code
//!
//! Provides an alternative to lambda lifting for handling local functions:
//! instead of hoisting local functions to the top level with extra parameters,
//! this module creates explicit closure objects that capture free variables
//! from the enclosing scope.
//!
//! # When to use closures vs lambda lifting
//!
//! - **Lambda lifting** (in `opt/lambda_lift`): Transforms local functions into
//!   top-level declarations. Best for static dispatch and C code generation.
//! - **Closures** (this module): Creates runtime closure objects with captured
//!   environments. Necessary for higher-order functions, partial application,
//!   and dynamic dispatch.
//!
//! Lean 4 uses both strategies:
//! - Lambda lifting during LCNF optimization
//! - Closure objects at runtime for higher-order values
//!
//! # Architecture
//!
//! ```text
//! Code (with local Fun) ──► ClosureBuilder ──► ClosureEnv + converted Code
//!                              │
//!                              ├─ free_variables(): static analysis
//!                              └─ closure_convert(): transform lambdas
//! ```
//!
//! # References
//!
//! - Lean 4: `src/Lean/Compiler/IR/EmitC.lean` (closure emission)
//! - Lean 4: `src/Lean/Compiler/LCNF/LambdaLifting.lean`
//! - Appel (1992), "Compiling with Continuations", Chapter 10
//!
//! Part of #3084 - Runtime closure support.

use crate::lcnf::{Alt, Code, FunDecl, Param};
use crate::opt::lambda_lift::free_vars_in_code;
use clean_kernel::{Expr, FVarId, Name};
use std::collections::{HashMap, HashSet};

// ════════════════════════════════════════════════════════════════════════════
// Types
// ════════════════════════════════════════════════════════════════════════════

/// How a variable is captured from the enclosing scope.
///
/// Lean 4's runtime uses by-value captures for all closure variables (since
/// values are reference-counted, "by value" means copying the pointer and
/// incrementing the reference count). `ByRef` is provided for potential
/// future optimization of borrowed captures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CaptureMode {
    /// Capture by value (copy + inc refcount for objects).
    ByValue,
    /// Capture by reference (borrow, no refcount change).
    /// Only valid when the closure does not outlive the captured binding.
    ByRef,
}

/// A single captured variable from the enclosing scope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CapturedVar {
    /// The original FVarId of the captured variable.
    pub(crate) fvar_id: FVarId,
    /// User-visible name (for debugging / emission).
    pub(crate) name: Name,
    /// Index of this capture in the closure environment.
    pub(crate) index: usize,
    /// How this variable is captured.
    pub(crate) capture_mode: CaptureMode,
}

/// A closure environment: the captured variables plus the body function.
///
/// At runtime, a closure is an object containing:
/// 1. A function pointer to the closure body
/// 2. The captured environment (array of values)
///
/// The body function takes the environment as its first implicit argument
/// and then the declared parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClosureEnv {
    /// Variables captured from the enclosing scope, ordered by index.
    pub(crate) captures: Vec<CapturedVar>,
    /// The FVarId of the original local function this closure was created from.
    pub(crate) body_fvar: FVarId,
    /// Number of declared parameters (excluding capture parameters).
    pub(crate) param_count: usize,
}

impl ClosureEnv {
    /// Total number of values stored in the environment.
    #[must_use]
    pub(crate) fn capture_count(&self) -> usize {
        self.captures.len()
    }

    /// Look up a capture by its original FVarId.
    #[must_use]
    pub(crate) fn find_capture(&self, fvar_id: FVarId) -> Option<&CapturedVar> {
        self.captures.iter().find(|c| c.fvar_id == fvar_id)
    }

    /// Iterator over captures in environment order.
    pub(crate) fn iter(&self) -> impl Iterator<Item = &CapturedVar> {
        self.captures.iter()
    }

    /// Check whether all captures are by-value.
    #[must_use]
    pub(crate) fn all_by_value(&self) -> bool {
        self.captures
            .iter()
            .all(|c| c.capture_mode == CaptureMode::ByValue)
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Builder
// ════════════════════════════════════════════════════════════════════════════

/// Builder for constructing closure environments from LCNF local functions.
///
/// Usage:
/// ```text
/// let builder = ClosureBuilder::from_fun_decl(&fun_decl, &bound_in_scope);
/// let env = builder.build();
/// ```
#[derive(Clone, Debug)]
#[must_use]
pub(crate) struct ClosureBuilder {
    /// Accumulated captured variables.
    captures: Vec<CapturedVar>,
    /// The FVarId of the function being closed over.
    body_fvar: FVarId,
    /// Number of declared parameters.
    param_count: usize,
    /// Set of FVarIds of parameters that are borrowed.
    borrowed_params: HashSet<FVarId>,
}

impl ClosureBuilder {
    /// Create a new builder for a function with the given parameter count.
    pub(crate) fn new(body_fvar: FVarId, param_count: usize) -> Self {
        Self {
            captures: Vec::new(),
            body_fvar,
            param_count,
            borrowed_params: HashSet::new(),
        }
    }

    /// Create a builder from a `FunDecl`, automatically computing free variables.
    ///
    /// `bound` is the set of variables bound in the enclosing scope. These are
    /// used to distinguish "true globals" (top-level constants etc.) from
    /// capturable locals. Variables in `bound` that appear free in the function
    /// body are exactly the ones that need to be captured.
    pub(crate) fn from_fun_decl(fun_decl: &FunDecl, bound: &HashSet<FVarId>) -> Self {
        let mut builder = Self::new(fun_decl.fvar_id, fun_decl.params.len());

        // Collect which params are borrowed for capture mode decisions
        for param in &fun_decl.params {
            if param.borrow {
                builder.borrowed_params.insert(param.fvar_id);
            }
        }

        // Compute free variables in the function body.
        // Only the function's own parameters and self-reference are "bound"
        // for this analysis — enclosing scope variables are NOT included
        // because those are exactly what we want to capture.
        let mut fn_bound = HashSet::new();
        fn_bound.insert(fun_decl.fvar_id); // recursive self-reference
        for param in &fun_decl.params {
            fn_bound.insert(param.fvar_id);
        }
        let free = free_vars_in_code(&fun_decl.body, &fn_bound);

        // Only capture variables that are actually from the enclosing scope
        // (present in `bound`). Variables not in `bound` are references to
        // top-level constants or truly unbound — not our concern here.
        let capturable: HashSet<FVarId> = free.intersection(bound).copied().collect();

        // Build captures from the free variables, in deterministic order.
        let mut free_sorted: Vec<FVarId> = capturable.into_iter().collect();
        free_sorted.sort_by_key(|fvar| fvar.as_u64());

        for (index, fvar_id) in free_sorted.into_iter().enumerate() {
            builder.add_capture(fvar_id, Name::anon(), index, CaptureMode::ByValue);
        }

        builder
    }

    /// Add a captured variable to the environment.
    pub(crate) fn add_capture(
        &mut self,
        fvar_id: FVarId,
        name: Name,
        index: usize,
        mode: CaptureMode,
    ) {
        self.captures.push(CapturedVar {
            fvar_id,
            name,
            index,
            capture_mode: mode,
        });
    }

    /// Finalize and produce the closure environment.
    pub(crate) fn build(self) -> ClosureEnv {
        ClosureEnv {
            captures: self.captures,
            body_fvar: self.body_fvar,
            param_count: self.param_count,
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Free Variable Analysis (delegates to lambda_lift::analysis)
// ════════════════════════════════════════════════════════════════════════════

/// Compute free variables in an LCNF `Code` block.
///
/// Wrapper around the lambda lifting free variable analysis for
/// use in closure conversion.
///
/// Returns the set of `FVarId`s that are referenced but not bound
/// within `code`, relative to the given `bound` set.
#[must_use]
pub(crate) fn free_variables(code: &Code, bound: &HashSet<FVarId>) -> HashSet<FVarId> {
    free_vars_in_code(code, bound)
}

// ════════════════════════════════════════════════════════════════════════════
// Closure Conversion
// ════════════════════════════════════════════════════════════════════════════

/// Result of closure-converting a Code block.
#[derive(Debug, Clone)]
pub(crate) struct ClosureConvertResult {
    /// The transformed code with local functions replaced by closure creation.
    pub(crate) code: Code,
    /// Closure environments for each converted local function.
    pub(crate) closures: Vec<ClosureEnv>,
}

/// Convert local functions in a `Code` block to explicit closures.
///
/// For each `Code::Fun(fun_decl, body)`:
/// 1. Compute free variables of `fun_decl`
/// 2. Build a `ClosureEnv` capturing those variables
/// 3. Replace the function body with one that receives captures as extra params
/// 4. The continuation sees the function as a closure value
///
/// This is the dual of lambda lifting: instead of moving functions up and
/// adding parameters, we keep them local and package captured variables
/// into an environment.
pub(crate) fn closure_convert(code: &Code, bound: &HashSet<FVarId>) -> ClosureConvertResult {
    let mut closures = Vec::new();
    let converted = convert_code(code, bound, &mut closures);
    ClosureConvertResult {
        code: converted,
        closures,
    }
}

/// Recursively convert local functions to closures.
fn convert_code(code: &Code, bound: &HashSet<FVarId>, closures: &mut Vec<ClosureEnv>) -> Code {
    match code {
        Code::Fun(fun_decl, continuation) => {
            // Build closure env for this local function
            let builder = ClosureBuilder::from_fun_decl(fun_decl, bound);
            let env = builder.build();

            // Create extra params for captured variables
            let capture_params: Vec<Param> = env
                .captures
                .iter()
                .map(|cap| Param::new(cap.fvar_id, cap.name.clone(), Expr::prop()))
                .collect();

            // Build new function with captures prepended to params
            let mut new_params = capture_params;
            new_params.extend(fun_decl.params.clone());

            // Recursively convert the function body
            let mut inner_bound = bound.clone();
            inner_bound.insert(fun_decl.fvar_id);
            for param in &new_params {
                inner_bound.insert(param.fvar_id);
            }
            let converted_body = convert_code(&fun_decl.body, &inner_bound, closures);

            let new_fun_decl = FunDecl::new(
                fun_decl.fvar_id,
                fun_decl.name.clone(),
                new_params,
                fun_decl.ty.clone(),
                converted_body,
            );

            closures.push(env);

            // Recursively convert the continuation
            let mut cont_bound = bound.clone();
            cont_bound.insert(fun_decl.fvar_id);
            let converted_continuation = convert_code(continuation, &cont_bound, closures);

            Code::Fun(new_fun_decl, Box::new(converted_continuation))
        }

        Code::Let(decl, body) => {
            let mut new_bound = bound.clone();
            new_bound.insert(decl.fvar_id);
            let converted_body = convert_code(body, &new_bound, closures);
            Code::Let(decl.clone(), Box::new(converted_body))
        }

        Code::JoinPoint(jp_decl, body) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(jp_decl.fvar_id);
            for param in &jp_decl.params {
                inner_bound.insert(param.fvar_id);
            }
            let converted_jp_body = convert_code(&jp_decl.body, &inner_bound, closures);

            let new_jp = FunDecl::new(
                jp_decl.fvar_id,
                jp_decl.name.clone(),
                jp_decl.params.clone(),
                jp_decl.ty.clone(),
                converted_jp_body,
            );

            let mut cont_bound = bound.clone();
            cont_bound.insert(jp_decl.fvar_id);
            let converted_body = convert_code(body, &cont_bound, closures);

            Code::JoinPoint(new_jp, Box::new(converted_body))
        }

        Code::Cases(cases) => {
            let converted_alts: Vec<Alt> = cases
                .alts
                .iter()
                .map(|alt| match alt {
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body,
                    } => {
                        let mut alt_bound = bound.clone();
                        for param in params {
                            alt_bound.insert(param.fvar_id);
                        }
                        let converted_body = convert_code(body, &alt_bound, closures);
                        Alt::ctor(ctor_name.clone(), params.clone(), converted_body)
                    }
                    Alt::Default(body) => {
                        let converted_body = convert_code(body, bound, closures);
                        Alt::default(converted_body)
                    }
                })
                .collect();

            Code::cases(
                cases.type_name.clone(),
                cases.result_type.clone(),
                cases.scrutinee,
                converted_alts,
            )
        }

        // Terminal nodes: no local functions to convert
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => code.clone(),
    }
}

/// Compute the type mapping for captured variables given the types of
/// bindings in scope.
///
/// Returns a vector of (FVarId, Expr) pairs for each capture, useful
/// for emitting typed closure environment structs.
#[must_use]
pub(crate) fn capture_types(
    env: &ClosureEnv,
    type_map: &HashMap<FVarId, Expr>,
) -> Vec<(FVarId, Expr)> {
    env.captures
        .iter()
        .filter_map(|cap| {
            type_map
                .get(&cap.fvar_id)
                .map(|ty| (cap.fvar_id, ty.clone()))
        })
        .collect()
}

#[cfg(test)]
#[path = "closure_tests.rs"]
mod closure_tests;
