// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Monomorphization Pass (ToMono) - Part of #1038
//!
//! Converts polymorphic LCNF to monomorphic form by erasing type parameters
//! and transforming type-dependent constructs.
//!
//! Based on Lean 4's `src/Lean/Compiler/LCNF/ToMono.lean`.

mod args;
mod cases;
mod let_code;
mod names;
#[cfg(test)]
mod tests;

use crate::lcnf::{Code, Decl, DeclValue};
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, FVarId, Name};
use std::collections::{HashMap, HashSet};

// Re-export sub-module public items to maintain flat namespace
pub use args::{
    arg_to_mono, args_to_mono, args_to_mono_red_arg, args_to_mono_with_fn_type, ctor_app_to_mono,
    param_to_mono,
};
pub use cases::cases_to_mono;
pub use let_code::{code_to_mono, letvalue_to_mono, LetValueTransform};
pub use names::{has_trivial_structure, prop_valued_const, TrivialStructureInfo};

/// Maximum recursion depth for ToMono traversal to avoid stack overflow.
pub(crate) const MAX_TO_MONO_STACK_DEPTH: usize = 2048;

/// State for monomorphization transformation.
#[derive(Clone, Debug)]
pub struct MonoRedArgCall {
    /// Specialized callee discovered in the mono declaration body.
    pub callee: Name,
    /// Argument pattern passed to the specialized callee.
    pub args: Vec<crate::lcnf::Arg>,
}

/// Cached mono declaration metadata used by later declarations.
#[derive(Clone, Debug)]
pub struct MonoDeclInfo {
    /// Mono declaration type for type-guided argument erasure.
    pub ty: Expr,
    /// Mono declaration parameters for `_redArg` pattern matching.
    pub params: Vec<crate::lcnf::Param>,
    /// Optional `_redArg` forwarding shape from the mono declaration body.
    pub red_arg_call: Option<MonoRedArgCall>,
}

/// State for monomorphization transformation.
#[derive(Default)]
pub struct ToMonoState {
    /// FVarIds bound to type-former parameters.
    /// These produce erased arguments when used.
    type_params: HashSet<FVarId>,
    /// Cached mono declarations from earlier top-level transforms.
    mono_decls: HashMap<Name, MonoDeclInfo>,
}

impl ToMonoState {
    /// Create a new empty state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Clear declaration-local type parameter tracking before a new top-level transform.
    pub fn clear_type_params(&mut self) {
        self.type_params.clear();
    }

    /// Check if an FVarId is a type parameter.
    pub fn is_type_param(&self, fvar: FVarId) -> bool {
        self.type_params.contains(&fvar)
    }

    /// Register an FVarId as a type parameter.
    pub fn add_type_param(&mut self, fvar: FVarId) {
        self.type_params.insert(fvar);
    }

    /// Get cached mono declaration metadata for a constant.
    pub fn get_mono_decl(&self, name: &Name) -> Option<&MonoDeclInfo> {
        self.mono_decls.get(name)
    }

    /// Save a transformed mono declaration for later const fallback rewriting.
    pub fn save_mono_decl(&mut self, decl: &Decl) {
        self.mono_decls.insert(
            decl.name.clone(),
            MonoDeclInfo {
                ty: decl_fn_type(decl),
                params: decl.params.clone(),
                red_arg_call: extract_red_arg_call(decl),
            },
        );
    }
}

fn extract_red_arg_call(decl: &Decl) -> Option<MonoRedArgCall> {
    let DeclValue::Code(code) = &decl.body else {
        return None;
    };
    let Code::Let(result_decl, body) = code.as_ref() else {
        return None;
    };
    let crate::lcnf::LetValue::Const { name, args, .. } = &result_decl.value else {
        return None;
    };
    let Code::Return(ret_fvar) = body.as_ref() else {
        return None;
    };
    if *ret_fvar != result_decl.fvar_id {
        return None;
    }

    Some(MonoRedArgCall {
        callee: name.clone(),
        args: args.clone(),
    })
}

fn decl_fn_type(decl: &Decl) -> Expr {
    decl.params
        .iter()
        .rev()
        .fold(decl.ty.clone(), |body, param| {
            Expr::pi(BinderInfo::Default, param.ty.clone(), body)
        })
}

// ═══════════════════════════════════════════════════════════════════════════
// LCNF Type Constants (lcErased, lcAny)
// ═══════════════════════════════════════════════════════════════════════════

/// Name for the erased marker type.
///
/// In Lean 4, `lcErased` marks values whose types have been erased
/// (proofs, type parameters, etc). These values exist at compile time
/// but have no runtime representation.
pub fn lc_erased_name() -> Name {
    Name::from_string("lcErased")
}

/// Name for the any marker type.
///
/// In Lean 4, `lcAny` marks type dependencies that cannot be determined
/// statically. This is the fallback when type information is lost.
pub fn lc_any_name() -> Name {
    Name::from_string("lcAny")
}

/// Create the lcErased expression.
///
/// Returns `Const(lcErased, [])` - a nullary constant.
pub fn erased_expr() -> Expr {
    Expr::const_(lc_erased_name(), vec![])
}

/// Create the lcAny expression.
///
/// Returns `Const(lcAny, [])` - a nullary constant.
pub fn any_expr() -> Expr {
    Expr::const_(lc_any_name(), vec![])
}

pub(crate) fn impl_name(name: &Name) -> Name {
    Name::append(name, "_impl")
}

pub(crate) fn red_arg_name(name: &Name) -> Name {
    Name::append(name, "_redArg")
}

/// Check if an expression is the lcErased marker.
///
/// Returns true if `e` is `Const(lcErased, _)`.
pub fn is_erased(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(name, _) if *name == lc_erased_name())
}

/// Check if an expression is the lcAny marker.
///
/// Returns true if `e` is `Const(lcAny, _)`.
pub fn is_any(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(name, _) if *name == lc_any_name())
}

/// Check if a type is a type-former (Sort, Prop, or produces one).
///
/// A type is "type-former" if:
/// - It is `Sort u` or `Type u`
/// - It is `Prop` (Sort 0)
/// - It's a forall/Pi that returns a type-former
pub fn is_type_former_type(ty: &Expr) -> bool {
    is_type_former_type_with_depth(ty, 0)
}

/// Internal implementation with depth tracking for stack protection.
///
/// Returns `false` if depth limit exceeded. This is conservative: treating
/// a type-former as non-type-former may miss some erasure optimizations,
/// but won't cause incorrect code generation.
fn is_type_former_type_with_depth(ty: &Expr, depth: usize) -> bool {
    // Stack protection: return false (conservative) if too deep
    if depth > MAX_TO_MONO_STACK_DEPTH {
        return false;
    }

    match ty.kind() {
        ExprKind::Sort(_) => true,
        // Pi types: check if the body returns a type-former
        ExprKind::Pi(_, _, body) => is_type_former_type_with_depth(body, depth + 1),
        _ => false,
    }
}

/// Convert a type to monomorphic form.
///
/// Based on Lean 4's `toMonoType` in `Lean/Compiler/LCNF/MonoTypes.lean`.
///
/// LCNF types in the mono phase:
/// - Have no dependencies (universe levels erased)
/// - Contain only `→` and constants
/// - Sort types become `lcErased`
/// - Unknown types become `lcAny`
///
/// # Semantics
/// - `Sort _` → `lcErased` (types have no runtime representation)
/// - `Pi _ d b` where `to_mono_type(b) = lcErased` → `lcErased`
/// - `Pi _ d b` → `d → b` (preserve function structure)
/// - `Const lcErased _` → `lcErased` (preserve erased marker)
/// - `Const lcAny _` → `lcAny` (preserve any marker)
/// - `Const Decidable _` → `Bool` (runtime representation)
/// - Other → `lcAny` (unknown types)
pub fn to_mono_type(ty: &Expr) -> Expr {
    to_mono_type_with_depth(ty, 0)
}

/// Perform head beta reduction on an expression if it is a lambda application.
///
/// Reduces only at the head position (no recursive normalization).
fn head_beta(expr: &Expr) -> Expr {
    if !matches!(expr.kind(), ExprKind::App(_, _)) {
        return expr.clone();
    }

    let mut args_rev: clean_kernel::AppArgs<'_> = clean_kernel::AppArgs::new();
    let mut current = expr;
    while let ExprKind::App(f, a) = current.kind() {
        args_rev.push(a);
        current = f;
    }

    let head = current.strip_mdata();
    if !matches!(head.kind(), ExprKind::Lam(_, _, _)) {
        return expr.clone();
    }

    let mut reduced = head.clone();
    let mut did_reduce = false;
    for arg in args_rev.iter().rev() {
        if let ExprKind::Lam(_, _, body) = reduced.kind() {
            reduced = body.instantiate(arg);
            did_reduce = true;
        } else {
            reduced = Expr::app(reduced, (*arg).clone());
        }
    }

    if did_reduce {
        reduced
    } else {
        expr.clone()
    }
}

fn to_mono_type_with_depth(ty: &Expr, depth: usize) -> Expr {
    // Stack protection
    if depth > MAX_TO_MONO_STACK_DEPTH {
        return any_expr();
    }

    // Lean 4 performs head beta reduction here.
    let ty = head_beta(ty);

    match ty.kind() {
        // Sort types are erased
        ExprKind::Sort(_) => erased_expr(),

        // Pi/forall types: check if body is erased
        ExprKind::Pi(bi, domain, body) => {
            // Substitute body with lcAny to simulate instantiation
            let mono_body = to_mono_type_with_depth(body, depth + 1);

            // If body is erased, the whole type is erased
            if is_erased(&mono_body) {
                return erased_expr();
            }

            // Otherwise, preserve function structure
            let mono_domain = to_mono_type_with_depth(domain, depth + 1);
            Expr::pi(*bi, mono_domain, mono_body)
        }

        // MData/Squash: propagate through transparent wrappers
        ExprKind::MData(data, inner) => {
            Expr::mdata(data.clone(), to_mono_type_with_depth(inner, depth + 1))
        }
        ExprKind::Squash(inner) => Expr::from_kind(ExprKind::Squash(std::sync::Arc::new(
            to_mono_type_with_depth(inner, depth + 1),
        ))),
        // Constants: handle special cases
        ExprKind::Const(name, _) => {
            // lcErased stays lcErased
            if *name == lc_erased_name() {
                return erased_expr();
            }
            // lcAny stays lcAny
            if *name == lc_any_name() {
                return any_expr();
            }
            // Decidable becomes Bool at runtime
            if *name == Name::from_string("Decidable") {
                return Expr::const_(Name::from_string("Bool"), vec![]);
            }
            // Other constants: preserve for now
            // Full implementation would handle trivial structures
            ty.clone()
        }

        // Applications: handle special constants in head position
        ExprKind::App(_, _) => {
            let head = ty.get_app_fn();
            if let ExprKind::Const(name, _) = head.kind() {
                // lcErased application stays erased
                if *name == lc_erased_name() {
                    return erased_expr();
                }
                // lcAny application stays any
                if *name == lc_any_name() {
                    return any_expr();
                }
                // Decidable becomes Bool
                if *name == Name::from_string("Decidable") {
                    return Expr::const_(Name::from_string("Bool"), vec![]);
                }
            }
            // Default: treat as lcAny (unknown applied type)
            any_expr()
        }

        // Other expressions: default to lcAny
        _ => any_expr(),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Top-level Entry Points
// ═══════════════════════════════════════════════════════════════════════════

/// Transform a top-level declaration to monomorphic form.
///
/// # Arguments
/// * `decl` - The declaration to transform
/// * `env` - Environment for type lookups (used by cases handlers)
pub fn to_mono(decl: &Decl, env: &Environment) -> Decl {
    let mut state = ToMonoState::new();
    to_mono_with_state(decl, env, &mut state)
}

fn to_mono_with_state(decl: &Decl, env: &Environment, state: &mut ToMonoState) -> Decl {
    state.clear_type_params();
    let mut next_fvar = compute_max_fvar(decl) + 1;

    let ty = to_mono_type(&decl.ty);
    let params: Vec<_> = decl
        .params
        .iter()
        .map(|p| param_to_mono(p, state))
        .collect();

    let body = match &decl.body {
        DeclValue::Code(code) => {
            DeclValue::Code(Box::new(code_to_mono(code, state, &mut next_fvar, env)))
        }
        DeclValue::Extern(e) => DeclValue::Extern(e.clone()),
    };

    let mono_decl = Decl {
        name: decl.name.clone(),
        level_params: vec![],
        ty,
        params,
        body,
        recursive: decl.recursive,
    };
    state.save_mono_decl(&mono_decl);
    mono_decl
}

/// Compute the maximum FVarId used in a declaration.
fn compute_max_fvar(decl: &Decl) -> u64 {
    let mut max_id = 0u64;

    for p in &decl.params {
        max_id = max_id.max(p.fvar_id.as_u64());
    }

    if let DeclValue::Code(code) = &decl.body {
        max_id = max_id.max(compute_max_fvar_code(code, 0));
    }

    max_id
}

/// Compute max FVarId in code.
///
/// Uses depth tracking to prevent stack overflow on deeply nested code.
fn compute_max_fvar_code(code: &Code, depth: usize) -> u64 {
    // Stack protection: return 0 if too deep
    if depth > MAX_TO_MONO_STACK_DEPTH {
        return 0;
    }

    match code {
        Code::Let(decl, body) => {
            let mut max_id = decl.fvar_id.as_u64();
            max_id = max_id.max(compute_max_fvar_code(body, depth + 1));
            max_id
        }
        Code::Fun(decl, body) | Code::JoinPoint(decl, body) => {
            let mut max_id = decl.fvar_id.as_u64();
            for p in &decl.params {
                max_id = max_id.max(p.fvar_id.as_u64());
            }
            max_id = max_id.max(compute_max_fvar_code(&decl.body, depth + 1));
            max_id = max_id.max(compute_max_fvar_code(body, depth + 1));
            max_id
        }
        Code::Cases(cases) => {
            let mut max_id = cases.scrutinee.as_u64();
            for alt in &cases.alts {
                max_id = max_id.max(compute_max_fvar_alt(alt, depth + 1));
            }
            max_id
        }
        Code::Jmp { jp, args } => {
            let mut max_id = jp.as_u64();
            for arg in args {
                if let crate::lcnf::Arg::FVar(fvar) = arg {
                    max_id = max_id.max(fvar.as_u64());
                }
            }
            max_id
        }
        Code::Return(fvar) => fvar.as_u64(),
        Code::Unreachable(_) => 0,
    }
}

/// Compute max FVarId in alternative.
fn compute_max_fvar_alt(alt: &crate::lcnf::Alt, depth: usize) -> u64 {
    match alt {
        crate::lcnf::Alt::Ctor { params, body, .. } => {
            let mut max_id = compute_max_fvar_code(body, depth);
            for p in params {
                max_id = max_id.max(p.fvar_id.as_u64());
            }
            max_id
        }
        crate::lcnf::Alt::Default(body) => compute_max_fvar_code(body, depth),
    }
}

/// Transform multiple declarations to monomorphic form.
///
/// # Arguments
/// * `decls` - The declarations to transform
/// * `env` - Environment for type lookups
pub fn to_mono_decls(decls: Vec<Decl>, env: &Environment) -> Vec<Decl> {
    let mut state = ToMonoState::new();
    decls
        .iter()
        .map(|decl| to_mono_with_state(decl, env, &mut state))
        .collect()
}
