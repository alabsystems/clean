// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PullLetDecls (pullInstances) — Hoist typeclass instance bindings.
//!
//! Hoists let-bound typeclass instance values out of nested scopes (loops,
//! function bodies, join-point bodies, case alternatives) to avoid redundant
//! allocation on each iteration.
//!
//! This is loop-invariant code motion specialized for instance dictionaries.
//! In Lean 4, this corresponds to `PullLetDecls` (formerly `pullInstances`)
//! in `src/Lean/Compiler/LCNF/PullLetDecls.lean`.
//!
//! # Algorithm
//!
//! 1. **Collect**: Walk the Code tree. For each let-binding whose type is a
//!    typeclass instance (detected via type head or value name), record it as
//!    a hoist candidate if it only depends on variables visible at the
//!    enclosing declaration scope.
//!
//! 2. **Remove**: On a second pass (combined with step 1 for efficiency),
//!    strip the hoisted bindings from their original positions.
//!
//! 3. **Prepend**: Insert the hoisted bindings at the top of the declaration
//!    body, in dependency order.
//!
//! # Example
//!
//! Before:
//! ```text
//! fun loop (n : Nat) : Nat :=
//!   let _inst := @instAddNat    // typeclass instance — re-allocated each call
//!   let _result := @Add.add _inst n n
//!   return _result
//! let _out := loop 42
//! return _out
//! ```
//!
//! After:
//! ```text
//! let _inst := @instAddNat      // hoisted to outer scope
//! fun loop (n : Nat) : Nat :=
//!   let _result := @Add.add _inst n n
//!   return _result
//! let _out := loop 42
//! return _out
//! ```
//!
//! Part of #1111 - PullLetDecls compiler pass.

use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
use clean_kernel::expr::ExprKind;
use clean_kernel::FVarId;
use std::collections::{HashSet, VecDeque};

// ============================================================================
// Instance type detection
// ============================================================================

/// Check if a let-binding looks like a typeclass instance.
///
/// Uses two heuristics (matching Lean 4's approach):
///
/// 1. **Type-based**: The type's head constant (after peeling `App` nodes)
///    has a name commonly associated with typeclasses (e.g., `Add`, `Mul`,
///    `Monad`, `BEq`, `Hashable`, `Inhabited`, `ToString`, etc.).
///
/// 2. **Value-based**: The binding's value is a `LetValue::Const` whose name
///    contains "inst" (Lean's naming convention for instance constructors,
///    e.g., `instAddNat`, `instBEqString`).
fn is_instance_binding(decl: &LetDecl) -> bool {
    is_instance_by_value(decl) || is_instance_by_type(decl)
}

/// Check if the binding's value references a constant whose name looks like
/// an instance constructor (contains "inst" as a component).
fn is_instance_by_value(decl: &LetDecl) -> bool {
    match &decl.value {
        LetValue::Const { name, .. } => {
            let s = name.to_string();
            s.contains("inst") || s.contains("Inst")
        }
        LetValue::Ctor { name, .. } => {
            let s = name.to_string();
            s.contains("inst") || s.contains("Inst")
        }
        _ => false,
    }
}

/// Check if the binding's type is a typeclass application.
///
/// Peels `App` nodes from the type to find the head constant, then checks
/// if it is a known typeclass name pattern. This is a conservative heuristic;
/// with full environment access we could check `env.is_class()` directly.
fn is_instance_by_type(decl: &LetDecl) -> bool {
    let head = decl.ty.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        let s = name.to_string();
        // Common Lean 4 typeclass names
        is_known_class_name(&s)
    } else {
        false
    }
}

/// Conservative list of known typeclass name patterns.
///
/// In production this should delegate to the environment's class registry.
/// For now we use naming conventions that cover the most common Lean 4 / Mathlib
/// typeclasses.
fn is_known_class_name(name: &str) -> bool {
    // Exact-match common typeclasses
    let known = [
        "Add",
        "Sub",
        "Mul",
        "Div",
        "Mod",
        "Neg",
        "Pow",
        "HAdd",
        "HSub",
        "HMul",
        "HDiv",
        "HMod",
        "HPow",
        "BEq",
        "Ord",
        "LT",
        "LE",
        "Hashable",
        "Inhabited",
        "Nonempty",
        "ToString",
        "Repr",
        "DecidableEq",
        "Monad",
        "Functor",
        "Applicative",
        "MonadLift",
        "MonadExcept",
        "MonadState",
        "MonadReader",
        "MonadIO",
        "Pure",
        "Bind",
        "Append",
        "Membership",
        "EmptyCollection",
        "Singleton",
        "Insert",
        "GetElem",
        "Stream",
        "ForIn",
        "ToFormat",
        "Zero",
        "One",
        "OfNat",
        "OfScientific",
        "Coe",
        "CoeSort",
        "CoeFun",
        "CoeHTCT",
        "CoeHead",
        "CoeTail",
        "Decidable",
        "Fintype",
        "Countable",
        "Encodable",
        "SizeOf",
        "Lean.ToJson",
        "Lean.FromJson",
    ];

    // Check the last component of a dotted name (e.g., "Nat.Add" -> "Add")
    let last = name.rsplit('.').next().unwrap_or(name);
    if known.contains(&last) {
        return true;
    }

    // Prefix heuristic: names starting with "inst" are instance constructors
    if last.starts_with("inst") || last.starts_with("Inst") {
        return true;
    }

    false
}

// ============================================================================
// Free variable collection
// ============================================================================

/// Collect FVarIds that a LetValue depends on.
fn let_value_free_vars(value: &LetValue) -> HashSet<FVarId> {
    let mut fvars = HashSet::new();
    match value {
        LetValue::Lit(_) | LetValue::Erased => {}
        LetValue::Proj { structure, .. } => {
            fvars.insert(*structure);
        }
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for arg in args {
                if let Arg::FVar(id) = arg {
                    fvars.insert(*id);
                }
            }
        }
        LetValue::FVar { fvar, args } => {
            fvars.insert(*fvar);
            for arg in args {
                if let Arg::FVar(id) = arg {
                    fvars.insert(*id);
                }
            }
        }
        LetValue::Reuse { slot, args, .. } => {
            fvars.insert(*slot);
            for arg in args {
                if let Arg::FVar(id) = arg {
                    fvars.insert(*id);
                }
            }
        }
    }
    fvars
}

// ============================================================================
// Core pull algorithm
// ============================================================================

/// Pull typeclass instance let-bindings out of nested scopes.
///
/// `outer_scope` is the set of FVarIds visible at the hoist target (the
/// declaration's parameter list plus any bindings already at the outer level).
/// Only bindings whose free variables are all in `outer_scope` can be hoisted.
///
/// Returns `(hoisted_bindings, rewritten_code)`.
fn pull_instances_from_code(code: &Code, outer_scope: &HashSet<FVarId>) -> (Vec<LetDecl>, Code) {
    let mut hoisted: Vec<LetDecl> = Vec::new();
    let rewritten = pull_impl(code, outer_scope, &mut hoisted, false);
    (hoisted, rewritten)
}

/// Recursive traversal that collects hoistable instance bindings and rewrites
/// the code tree.
///
/// `in_nested` is true when we are inside a Fun, JoinPoint, or Cases body —
/// only bindings inside nested scopes are candidates for hoisting.
fn pull_impl(
    code: &Code,
    outer_scope: &HashSet<FVarId>,
    hoisted: &mut Vec<LetDecl>,
    in_nested: bool,
) -> Code {
    match code {
        Code::Let(decl, body) => {
            // Check if this binding should be hoisted
            if in_nested && is_instance_binding(decl) && can_hoist(decl, outer_scope, hoisted) {
                // Record the hoisted binding; it will be prepended at the outer level
                hoisted.push(decl.clone());
                // Skip this let node in the rewritten tree; recurse into body
                // The body may still reference the hoisted FVarId — that's correct
                // because we prepend it at the outer scope.
                pull_impl(body, outer_scope, hoisted, in_nested)
            } else {
                // Not hoisting: keep the let, recurse into body
                let new_body = pull_impl(body, outer_scope, hoisted, in_nested);
                Code::Let(decl.clone(), Box::new(new_body))
            }
        }

        Code::Fun(fun_decl, body) => {
            // Process the function's own body in nested mode
            let new_fun_body = pull_impl(&fun_decl.body, outer_scope, hoisted, true);
            let new_fun_decl = FunDecl {
                fvar_id: fun_decl.fvar_id,
                name: fun_decl.name.clone(),
                params: fun_decl.params.clone(),
                ty: fun_decl.ty.clone(),
                body: Box::new(new_fun_body),
            };
            // Process continuation
            let new_body = pull_impl(body, outer_scope, hoisted, in_nested);
            Code::Fun(new_fun_decl, Box::new(new_body))
        }

        Code::JoinPoint(jp_decl, body) => {
            // Process the join point's own body in nested mode
            let new_jp_body = pull_impl(&jp_decl.body, outer_scope, hoisted, true);
            let new_jp_decl = FunDecl {
                fvar_id: jp_decl.fvar_id,
                name: jp_decl.name.clone(),
                params: jp_decl.params.clone(),
                ty: jp_decl.ty.clone(),
                body: Box::new(new_jp_body),
            };
            // Process continuation
            let new_body = pull_impl(body, outer_scope, hoisted, in_nested);
            Code::JoinPoint(new_jp_decl, Box::new(new_body))
        }

        Code::Cases(cases) => {
            let new_alts = cases
                .alts
                .iter()
                .map(|alt| match alt {
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body,
                    } => {
                        let new_body = pull_impl(body, outer_scope, hoisted, true);
                        Alt::Ctor {
                            ctor_name: ctor_name.clone(),
                            params: params.clone(),
                            body: Box::new(new_body),
                        }
                    }
                    Alt::Default(body) => {
                        let new_body = pull_impl(body, outer_scope, hoisted, true);
                        Alt::Default(Box::new(new_body))
                    }
                })
                .collect();
            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee: cases.scrutinee,
                alts: new_alts,
            })
        }

        // Terminals: pass through unchanged
        Code::Jmp { jp, args } => Code::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        Code::Return(fvar) => Code::Return(*fvar),
        Code::Unreachable(ty) => Code::Unreachable(ty.clone()),
    }
}

/// Check if a let-binding can be hoisted to the outer scope.
///
/// A binding can be hoisted if all of its free variables are either:
/// - In the outer scope (parameters and earlier outer-scope bindings), or
/// - Defined by an already-hoisted binding (transitive dependency).
fn can_hoist(decl: &LetDecl, outer_scope: &HashSet<FVarId>, hoisted: &[LetDecl]) -> bool {
    let deps = let_value_free_vars(&decl.value);
    let hoisted_ids: HashSet<FVarId> = hoisted.iter().map(|d| d.fvar_id).collect();
    deps.iter()
        .all(|fvar| outer_scope.contains(fvar) || hoisted_ids.contains(fvar))
}

/// Prepend hoisted bindings before the given code, in order.
///
/// Performs a topological sort to ensure that if binding A depends on binding
/// B, then B appears before A.
fn prepend_hoisted(mut hoisted: Vec<LetDecl>, code: Code) -> Code {
    // Topological sort: stable ordering where dependencies come first.
    let mut sorted: VecDeque<LetDecl> = VecDeque::new();
    let all_ids: HashSet<FVarId> = hoisted.iter().map(|d| d.fvar_id).collect();

    // Simple insertion sort: for each binding, find the earliest position
    // where all its dependencies are already placed.
    for decl in hoisted.drain(..) {
        let deps = let_value_free_vars(&decl.value);
        let internal_deps: HashSet<FVarId> = deps.intersection(&all_ids).copied().collect();

        // Find the last position of any dependency
        let insert_after = sorted
            .iter()
            .rposition(|d| internal_deps.contains(&d.fvar_id));

        match insert_after {
            Some(pos) => sorted.insert(pos + 1, decl),
            None => sorted.push_front(decl),
        }
    }

    // Build the code chain from the sorted bindings
    let mut result = code;
    for decl in sorted.into_iter().rev() {
        result = Code::Let(decl, Box::new(result));
    }
    result
}

// ============================================================================
// Public API
// ============================================================================

/// Pull typeclass instance let-bindings out of nested scopes in a Code block.
///
/// Hoists instance-typed let-bindings that only depend on outer-scope variables
/// to the top of the code block, reducing redundant allocation in loops and
/// function bodies.
#[must_use]
pub fn pull_let_decls_in_code(code: &Code) -> Code {
    pull_let_decls_in_code_with_params(code, &[])
}

/// Pull typeclass instance let-bindings with an explicit outer scope
/// derived from function parameters.
#[must_use]
pub(crate) fn pull_let_decls_in_code_with_params(code: &Code, param_fvars: &[FVarId]) -> Code {
    let mut outer_scope: HashSet<FVarId> = param_fvars.iter().copied().collect();

    // Also include any top-level let-bindings as part of the outer scope,
    // since they are already at the outermost level and don't need hoisting.
    collect_top_level_lets(code, &mut outer_scope);

    let (hoisted, rewritten) = pull_instances_from_code(code, &outer_scope);

    if hoisted.is_empty() {
        return rewritten;
    }

    prepend_hoisted(hoisted, rewritten)
}

/// Collect FVarIds of top-level let-bindings (the linear chain before any
/// Fun/JoinPoint/Cases).
fn collect_top_level_lets(code: &Code, scope: &mut HashSet<FVarId>) {
    let mut current = code;
    while let Code::Let(decl, body) = current {
        scope.insert(decl.fvar_id);
        current = body;
    }
}

/// Pull typeclass instance let-bindings from a declaration.
#[must_use]
pub fn pull_let_decls(decl: &Decl) -> Decl {
    let new_body = match &decl.body {
        DeclValue::Code(code) => {
            let param_fvars: Vec<FVarId> = decl.params.iter().map(|p| p.fvar_id).collect();
            DeclValue::Code(Box::new(pull_let_decls_in_code_with_params(
                code,
                &param_fvars,
            )))
        }
        DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
    };

    Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body: new_body,
        recursive: decl.recursive,
    }
}

/// Pull typeclass instance let-bindings from all declarations in a batch.
#[must_use]
pub fn pull_let_decls_all(decls: &[Decl]) -> Vec<Decl> {
    decls.iter().map(pull_let_decls).collect()
}

// ============================================================================
// Tests
// ============================================================================
