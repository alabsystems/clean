// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lambda Lifting Pass
//!
//! Transforms local function definitions into top-level functions by
//! capturing free variables as explicit parameters.
//!
//! # Overview
//!
//! Lambda lifting converts nested function definitions into top-level
//! declarations, making explicit which variables are captured from the
//! enclosing scope. This is necessary for:
//!
//! 1. Compilation to languages without closures (C)
//! 2. Efficient code generation (avoid closure allocation)
//! 3. Enabling further optimizations on lifted functions
//!
//! # Algorithm
//!
//! 1. **Free Variable Analysis**: Compute variables referenced but not
//!    bound by a local function.
//!
//! 2. **Lifting**: For each local function `f`:
//!    - Add captured free variables as extra parameters
//!    - Create a new top-level declaration with modified signature
//!    - Replace local references to `f` with calls to lifted version
//!
//! 3. **Closure Conversion** (alternative): Instead of lifting, could
//!    convert to explicit closure objects. Not implemented here.
//!
//! # References
//!
//! - Lean 4: `src/Lean/Compiler/LCNF/LambdaLifting.lean`
//! - Johnsson, "Lambda Lifting: Transforming Programs to Recursive Equations"
//!
//! Part of #1003 - Lambda lifting implementation.

mod analysis;
mod remap;

#[cfg(test)]
mod tests;

pub use analysis::free_vars_in_code;

use analysis::{code_references_fvar, collect_free_vars_from_expr};
use remap::{remap_fvars_in_code, remap_fvars_in_expr, remap_fvars_in_params};

use crate::lcnf::{Alt, Arg, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};
use std::collections::{HashMap, HashSet};

type BoundTypes = HashMap<FVarId, Expr>;

// ════════════════════════════════════════════════════════════════════════════
// Lambda Lifting
// ════════════════════════════════════════════════════════════════════════════

/// Result of lambda lifting a declaration.
#[derive(Debug, Clone)]
pub struct LiftResult {
    /// The transformed declaration (local functions removed).
    pub decl: Decl,
    /// Newly created top-level declarations from lifted functions.
    pub lifted: Vec<Decl>,
}

/// Configuration for lambda lifting.
#[derive(Debug, Clone)]
pub struct LiftConfig {
    /// Prefix for generated function names.
    pub prefix: String,
}

impl Default for LiftConfig {
    fn default() -> Self {
        Self {
            prefix: "_lifted".to_string(),
        }
    }
}

/// State for lambda lifting.
struct LiftState {
    /// Counter for generating unique names.
    next_id: u32,
    /// Counter for generating unique FVarIds for capture parameters.
    next_fvar_id: u64,
    /// Prefix for names.
    prefix: String,
    /// Enclosing declaration name, qualifying every lifted name. Without it,
    /// two decls compiled into ONE module would both lift their first
    /// anonymous lambda to `_lifted._lambda.0` — colliding function names
    /// with (in general) different signatures, which trust-ir's
    /// `validate_module` refuses (C4: previously masked because decls with
    /// motive-typed lambdas failed earlier, at `to_ir` return-type
    /// conversion). Lifting runs per-decl, so the decl name is the natural
    /// uniqueness scope — the same scoping `to_lcnf_ext`'s
    /// `{parent}_lifted_{n}` lifter already uses.
    scope: Name,
    /// Collected lifted declarations.
    lifted: Vec<Decl>,
    /// Mapping from original local function FVarId to lifted function name.
    lift_map: HashMap<FVarId, Name>,
    /// Mapping from original local function FVarId to captured variables.
    /// These must be passed as extra arguments at call sites.
    capture_map: HashMap<FVarId, Vec<FVarId>>,
}

impl LiftState {
    fn new(prefix: &str, scope: &Name) -> Self {
        Self {
            next_id: 0,
            next_fvar_id: 1_000_000, // Start high to avoid conflicts
            prefix: prefix.to_string(),
            scope: scope.clone(),
            lifted: Vec::new(),
            lift_map: HashMap::new(),
            capture_map: HashMap::new(),
        }
    }

    fn fresh_name(&mut self, base: &Name) -> Name {
        let id = self.next_id;
        self.next_id += 1;
        Name::from_string(&format!("{}.{}.{}.{}", self.prefix, self.scope, base, id))
    }

    fn fresh_fvar(&mut self) -> FVarId {
        let id = self.next_fvar_id;
        self.next_fvar_id += 1;
        FVarId::new(id)
    }
}

/// Lift all local functions in a declaration.
///
/// Local functions that don't capture any free variables are lifted directly.
/// Functions that capture variables have those variables added as parameters.
///
/// # Returns
///
/// A `LiftResult` containing:
/// - The modified declaration with local functions replaced
/// - A vector of new top-level declarations for lifted functions
pub fn lambda_lift(decl: &Decl, config: &LiftConfig) -> LiftResult {
    let mut state = LiftState::new(&config.prefix, &decl.name);

    // Compute the set of parameters (these are bound at the top level)
    let mut bound: HashSet<FVarId> = HashSet::new();
    let mut bound_types = BoundTypes::new();
    for param in &decl.params {
        bound.insert(param.fvar_id);
        bound_types.insert(param.fvar_id, param.ty.clone());
    }

    let body = match &decl.body {
        DeclValue::Code(code) => {
            let lifted_code = lift_code(code, &bound, &bound_types, &mut state);
            DeclValue::Code(Box::new(lifted_code))
        }
        DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
    };

    let new_decl = Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body,
        recursive: decl.recursive,
    };

    LiftResult {
        decl: new_decl,
        lifted: state.lifted,
    }
}

/// Lift local functions in code.
fn lift_code(
    code: &Code,
    bound: &HashSet<FVarId>,
    bound_types: &BoundTypes,
    state: &mut LiftState,
) -> Code {
    match code {
        Code::Return(fvar) => Code::Return(*fvar),

        Code::Let(decl, body) => {
            let new_value = lift_value(&decl.value, state);
            let mut new_bound = bound.clone();
            new_bound.insert(decl.fvar_id);
            let mut new_bound_types = bound_types.clone();
            new_bound_types.insert(decl.fvar_id, decl.ty.clone());

            Code::Let(
                LetDecl {
                    fvar_id: decl.fvar_id,
                    name: decl.name.clone(),
                    ty: decl.ty.clone(),
                    value: new_value,
                },
                Box::new(lift_code(body, &new_bound, &new_bound_types, state)),
            )
        }

        Code::Fun(fun_decl, body) => {
            // Compute free variables of the function body AND type annotations.
            // Include function name for recursive self-reference.
            let mut param_bound: HashSet<FVarId> = HashSet::new();
            param_bound.insert(fun_decl.fvar_id); // Function can reference itself
            for param in &fun_decl.params {
                param_bound.insert(param.fvar_id);
            }

            let mut free = free_vars_in_code(&fun_decl.body, &param_bound);

            // Also collect free variables from parameter types and return type.
            // These are checked against param_bound (not outer bound) so that
            // outer-scope variables referenced in types appear as "free" and
            // can be captured by the lifted function.
            for param in &fun_decl.params {
                collect_free_vars_from_expr(&param.ty, &param_bound, &mut free);
            }
            collect_free_vars_from_expr(&fun_decl.ty, &param_bound, &mut free);

            // Filter to variables that are actually in scope (bound in outer context)
            // Sort to ensure deterministic ordering across builds
            let mut captured: Vec<FVarId> = free
                .iter()
                .filter(|fv| bound.contains(fv))
                .copied()
                .collect();
            captured.sort_by_key(|fv| fv.as_u64());

            // Check if the function is recursive (references itself in its body)
            let is_recursive = code_references_fvar(&fun_decl.body, fun_decl.fvar_id);

            if captured.is_empty() {
                // No captures - lift directly
                let lifted_name = state.fresh_name(&fun_decl.name);
                state.lift_map.insert(fun_decl.fvar_id, lifted_name.clone());

                // Create the lifted declaration
                let lifted_decl = Decl {
                    name: lifted_name.clone(),
                    level_params: vec![],
                    ty: fun_decl.ty.clone(),
                    params: fun_decl.params.clone(),
                    body: DeclValue::Code(Box::new(lift_code(
                        &fun_decl.body,
                        &param_bound,
                        &params_to_bound_types(&fun_decl.params),
                        state,
                    ))),
                    recursive: is_recursive,
                };
                state.lifted.push(lifted_decl);

                // Continue with body, direct calls are now references to the lifted version.
                let mut new_bound = bound.clone();
                new_bound.insert(fun_decl.fvar_id);
                let lifted_body = lift_code(body, &new_bound, bound_types, state);
                bind_lifted_function_value_if_needed(body, fun_decl, lifted_name, &[], lifted_body)
            } else {
                // Has captures - lift with captured vars as extra parameters
                let lifted_name = state.fresh_name(&fun_decl.name);
                state.lift_map.insert(fun_decl.fvar_id, lifted_name.clone());
                state.capture_map.insert(fun_decl.fvar_id, captured.clone());

                // Create new parameters for captured variables
                let mut capture_params: Vec<Param> = Vec::new();
                let mut capture_remap: HashMap<FVarId, FVarId> = HashMap::new();

                for &cap_fvar in &captured {
                    let new_fvar = state.fresh_fvar();
                    capture_remap.insert(cap_fvar, new_fvar);
                    // Unknown-typed captures (locals bound at the `_`
                    // placeholder, e.g. inferred-failure lets) become
                    // `Object` parameters — the boxed closure convention
                    // this lifter already uses for closure values. `_` is
                    // NOT a runtime type and is fail-closed rejected by
                    // `to_ir` in parameter position.
                    let capture_ty = match bound_types.get(&cap_fvar) {
                        Some(ty) if !is_placeholder_type(ty) => ty.clone(),
                        _ => Expr::const_str("Object"),
                    };
                    capture_params.push(Param::new(
                        new_fvar,
                        Name::from_string(&format!("_cap{}", new_fvar.as_u64())),
                        capture_ty,
                    ));
                }

                // Combine: captured params first, then original params (with remapped types)
                let mut all_params = capture_params;
                all_params.extend(remap_fvars_in_params(&fun_decl.params, &capture_remap));

                // Update param_bound to include capture params (new FVarIds)
                for new in capture_remap.values() {
                    param_bound.insert(*new);
                }

                // Remap the function body to use new FVarIds for captured vars
                let remapped_body = remap_fvars_in_code(&fun_decl.body, &capture_remap);
                let lifted_bound_types = params_to_bound_types(&all_params);

                // While lifting the (remapped) body, a RECURSIVE self-call
                // must prepend the REMAPPED capture ids — inside the lifted
                // declaration the captures are its own fresh parameters; the
                // original outer fvars are not in scope there. The
                // continuation (below) still needs the ORIGINAL ids, so swap
                // the capture_map entry around the body lift. (R1: the
                // synthesized-eliminator `go` functions are the first
                // recursive local functions with captures to reach this
                // path — previously the self-call args dangled.)
                let remapped_captures: Vec<FVarId> =
                    captured.iter().map(|cap| capture_remap[cap]).collect();
                state
                    .capture_map
                    .insert(fun_decl.fvar_id, remapped_captures);
                let lifted_body_code =
                    lift_code(&remapped_body, &param_bound, &lifted_bound_types, state);
                state.capture_map.insert(fun_decl.fvar_id, captured.clone());

                // Create the lifted declaration
                let lifted_decl = Decl {
                    name: lifted_name.clone(),
                    level_params: vec![],
                    ty: remap_fvars_in_expr(&fun_decl.ty, &capture_remap),
                    params: all_params,
                    body: DeclValue::Code(Box::new(lifted_body_code)),
                    recursive: is_recursive,
                };
                state.lifted.push(lifted_decl);

                // Continue with body, direct calls are now references to the lifted version.
                let mut new_bound = bound.clone();
                new_bound.insert(fun_decl.fvar_id);
                let lifted_body = lift_code(body, &new_bound, bound_types, state);
                bind_lifted_function_value_if_needed(
                    body,
                    fun_decl,
                    lifted_name,
                    &captured,
                    lifted_body,
                )
            }
        }

        Code::JoinPoint(jp_decl, body) => {
            // Don't lift join points - they're handled differently
            // Join point params AND the join point itself are bound in its body
            // (join point can recursively reference itself)
            let mut param_bound = bound.clone();
            param_bound.insert(jp_decl.fvar_id); // Allow recursive self-reference
            for param in &jp_decl.params {
                param_bound.insert(param.fvar_id);
            }
            let param_bound_types = extend_bound_types(bound_types, &jp_decl.params);

            let mut new_bound = bound.clone();
            new_bound.insert(jp_decl.fvar_id);

            Code::JoinPoint(
                FunDecl {
                    fvar_id: jp_decl.fvar_id,
                    name: jp_decl.name.clone(),
                    params: jp_decl.params.clone(),
                    ty: jp_decl.ty.clone(),
                    body: Box::new(lift_code(
                        &jp_decl.body,
                        &param_bound,
                        &param_bound_types,
                        state,
                    )),
                },
                Box::new(lift_code(body, &new_bound, bound_types, state)),
            )
        }

        Code::Cases(cases) => {
            let new_alts: Vec<Alt> = cases
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
                        let alt_bound_types = extend_bound_types(bound_types, params);
                        Alt::Ctor {
                            ctor_name: ctor_name.clone(),
                            params: params.clone(),
                            body: Box::new(lift_code(body, &alt_bound, &alt_bound_types, state)),
                        }
                    }
                    Alt::Default(body) => {
                        Alt::Default(Box::new(lift_code(body, bound, bound_types, state)))
                    }
                })
                .collect();

            Code::Cases(crate::lcnf::Cases {
                type_name: cases.type_name.clone(),
                scrutinee: cases.scrutinee,
                result_type: cases.result_type.clone(),
                alts: new_alts,
            })
        }

        Code::Jmp { jp, args } => {
            // Note: Jmp arguments are values, but they don't contain function calls
            // (args are FVar, Type, or Erased). If a lifted function is used as
            // a first-class value passed to a join point, it would be bound to
            // a let first and passed as FVar. No transformation needed here.
            Code::Jmp {
                jp: *jp,
                args: args.clone(),
            }
        }

        Code::Unreachable(expr) => Code::Unreachable(expr.clone()),
    }
}

fn bind_lifted_function_value_if_needed(
    original_continuation: &Code,
    fun_decl: &FunDecl,
    lifted_name: Name,
    captured: &[FVarId],
    lifted_body: Code,
) -> Code {
    if !code_references_fvar_as_value(original_continuation, fun_decl.fvar_id) {
        return lifted_body;
    }

    let closure_args = captured.iter().copied().map(Arg::FVar).collect();
    let closure = LetDecl {
        fvar_id: fun_decl.fvar_id,
        name: fun_decl.name.clone(),
        ty: Expr::const_str("Object"),
        value: LetValue::Const {
            name: lifted_name,
            levels: vec![],
            args: closure_args,
        },
    };
    Code::let_bind(closure, lifted_body)
}

fn code_references_fvar_as_value(code: &Code, target: FVarId) -> bool {
    match code {
        Code::Return(fvar) => *fvar == target,
        Code::Let(decl, body) => {
            value_references_fvar_as_value(&decl.value, target)
                || code_references_fvar_as_value(body, target)
        }
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            code_references_fvar_as_value(&fun_decl.body, target)
                || code_references_fvar_as_value(body, target)
        }
        Code::Cases(cases) => {
            cases.scrutinee == target
                || cases.alts.iter().any(|alt| match alt {
                    Alt::Ctor { body, .. } | Alt::Default(body) => {
                        code_references_fvar_as_value(body, target)
                    }
                })
        }
        Code::Jmp { jp, args } => {
            *jp == target || args.iter().any(|arg| arg_references_fvar(arg, target))
        }
        Code::Unreachable(_) => false,
    }
}

fn value_references_fvar_as_value(value: &LetValue, target: FVarId) -> bool {
    match value {
        LetValue::Lit(_) | LetValue::Erased => false,
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            args.iter().any(|arg| arg_references_fvar(arg, target))
        }
        LetValue::Proj { structure, .. } => *structure == target,
        LetValue::FVar { args, .. } => args.iter().any(|arg| arg_references_fvar(arg, target)),
        LetValue::Reuse { slot, args, .. } => {
            *slot == target || args.iter().any(|arg| arg_references_fvar(arg, target))
        }
    }
}

fn arg_references_fvar(arg: &Arg, target: FVarId) -> bool {
    match arg {
        Arg::FVar(fvar) => *fvar == target,
        Arg::Type(expr) => expr_references_fvar(expr, target),
        Arg::Erased | Arg::Index(_) => false,
    }
}

fn expr_references_fvar(expr: &Expr, target: FVarId) -> bool {
    matches!(expr.kind(), clean_kernel::ExprKind::FVar(fvar) if *fvar == target)
}

fn params_to_bound_types(params: &[Param]) -> BoundTypes {
    params
        .iter()
        .map(|param| (param.fvar_id, param.ty.clone()))
        .collect()
}

fn extend_bound_types(bound_types: &BoundTypes, params: &[Param]) -> BoundTypes {
    let mut extended = bound_types.clone();
    for param in params {
        extended.insert(param.fvar_id, param.ty.clone());
    }
    extended
}

/// Lift values - replace references to lifted functions with calls to top-level versions.
fn lift_value(value: &LetValue, state: &LiftState) -> LetValue {
    match value {
        LetValue::FVar { fvar, args } => {
            // Check if this fvar was lifted
            if let Some(lifted_name) = state.lift_map.get(fvar) {
                // Get captured variables that need to be passed as extra arguments
                let captured = state.capture_map.get(fvar);

                // Build argument list: captured vars first, then original args
                let mut all_args: Vec<Arg> = Vec::new();
                if let Some(captures) = captured {
                    for &cap_fvar in captures {
                        all_args.push(Arg::FVar(cap_fvar));
                    }
                }
                all_args.extend(args.clone());

                // Replace with a call to the lifted function
                LetValue::Const {
                    name: lifted_name.clone(),
                    levels: vec![],
                    args: all_args,
                }
            } else {
                value.clone()
            }
        }
        _ => value.clone(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Public API
// ════════════════════════════════════════════════════════════════════════════

/// Whether a type expression is the synthetic `_` placeholder (inference
/// failure marker) — not a runtime type.
fn is_placeholder_type(ty: &Expr) -> bool {
    matches!(ty.kind(), clean_kernel::ExprKind::Const(name, _) if name.to_string() == "_")
}

/// Lambda lift multiple declarations.
pub fn lambda_lift_decls(decls: &[Decl], config: &LiftConfig) -> Vec<Decl> {
    let mut result = Vec::new();

    for decl in decls {
        let lift_result = lambda_lift(decl, config);
        result.push(lift_result.decl);
        result.extend(lift_result.lifted);
    }

    result
}

/// Lambda lift with default configuration.
pub fn lambda_lift_default(decl: &Decl) -> LiftResult {
    lambda_lift(decl, &LiftConfig::default())
}
