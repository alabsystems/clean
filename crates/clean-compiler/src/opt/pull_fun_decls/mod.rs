// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PullFunDecls — pull local functions/join points to outermost valid scope.
//!
//! Moves `Code::Fun` and `Code::JoinPoint` nodes upward in the code tree
//! to the earliest scope where all their free variables are bound. Based on
//! Lean 4's `src/Lean/Compiler/LCNF/PullFunDecls.lean`.
//!
//! Part of #1085 - PullFunDecls compiler pass.

use crate::lcnf::{Alt, Arg, Code, Decl, DeclValue, FunDecl, LetValue};
use clean_kernel::FVarId;
use std::collections::HashSet;

/// A local function or join point being pulled upward.
struct ToPull {
    /// Whether this is a `Code::Fun` (true) or `Code::JoinPoint` (false).
    is_fun: bool,
    /// The function/join-point declaration.
    decl: FunDecl,
    /// Set of FVarIds that the declaration's body, params, and type reference.
    used: HashSet<FVarId>,
}

impl ToPull {
    /// Wrap the given continuation code with this declaration.
    fn attach(self, k: Code) -> Code {
        if self.is_fun {
            Code::Fun(self.decl, Box::new(k))
        } else {
            Code::JoinPoint(self.decl, Box::new(k))
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Used-FVarId Collection
// ════════════════════════════════════════════════════════════════════════════

/// Collect all FVarIds referenced by a FunDecl (body, params, return type).
///
/// This captures the complete set of external dependencies so we know
/// which bindings must be in scope before the declaration can be placed.
fn collect_used_fvars(decl: &FunDecl) -> HashSet<FVarId> {
    let mut used = HashSet::new();
    // Collect from the body
    collect_fvars_in_code(&decl.body, &mut used);
    // Collect from parameter types
    for param in &decl.params {
        collect_fvars_in_expr(&param.ty, &mut used);
    }
    // Collect from return type
    collect_fvars_in_expr(&decl.ty, &mut used);
    // Remove self-reference (function can refer to itself recursively)
    used.remove(&decl.fvar_id);
    // Remove own parameters (they are bound internally)
    for param in &decl.params {
        used.remove(&param.fvar_id);
    }
    used
}

/// Collect all FVarIds mentioned in a Code block (without any bound-set filtering).
fn collect_fvars_in_code(code: &Code, out: &mut HashSet<FVarId>) {
    match code {
        Code::Return(fvar) => {
            out.insert(*fvar);
        }
        Code::Let(decl, body) => {
            collect_fvars_in_let_value(&decl.value, out);
            collect_fvars_in_expr(&decl.ty, out);
            collect_fvars_in_code(body, out);
        }
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            collect_fvars_in_code(&fun_decl.body, out);
            for param in &fun_decl.params {
                collect_fvars_in_expr(&param.ty, out);
            }
            collect_fvars_in_expr(&fun_decl.ty, out);
            collect_fvars_in_code(body, out);
        }
        Code::Cases(cases) => {
            out.insert(cases.scrutinee);
            collect_fvars_in_expr(&cases.result_type, out);
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, params, .. } => {
                        for param in params {
                            collect_fvars_in_expr(&param.ty, out);
                        }
                        collect_fvars_in_code(body, out);
                    }
                    Alt::Default(body) => {
                        collect_fvars_in_code(body, out);
                    }
                }
            }
        }
        Code::Jmp { jp, args } => {
            out.insert(*jp);
            for arg in args {
                collect_fvars_in_arg(arg, out);
            }
        }
        Code::Unreachable(expr) => {
            collect_fvars_in_expr(expr, out);
        }
    }
}

/// Collect FVarIds from a LetValue.
fn collect_fvars_in_let_value(value: &LetValue, out: &mut HashSet<FVarId>) {
    match value {
        LetValue::Lit(_) | LetValue::Erased => {}
        LetValue::Proj { structure, .. } => {
            out.insert(*structure);
        }
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for arg in args {
                collect_fvars_in_arg(arg, out);
            }
        }
        LetValue::FVar { fvar, args } => {
            out.insert(*fvar);
            for arg in args {
                collect_fvars_in_arg(arg, out);
            }
        }
        LetValue::Reuse { slot, args, .. } => {
            out.insert(*slot);
            for arg in args {
                collect_fvars_in_arg(arg, out);
            }
        }
    }
}

/// Collect FVarIds from an Arg.
fn collect_fvars_in_arg(arg: &Arg, out: &mut HashSet<FVarId>) {
    match arg {
        Arg::FVar(fvar) => {
            out.insert(*fvar);
        }
        Arg::Type(expr) => {
            collect_fvars_in_expr(expr, out);
        }
        Arg::Erased | Arg::Index(_) => {}
    }
}

/// Collect FVarIds from a kernel expression (conservative walk).
fn collect_fvars_in_expr(expr: &clean_kernel::Expr, out: &mut HashSet<FVarId>) {
    use clean_kernel::expr::ExprKind;
    match expr.kind() {
        ExprKind::FVar(fvar) => {
            out.insert(*fvar);
        }
        ExprKind::App(f, arg) => {
            collect_fvars_in_expr(f, out);
            collect_fvars_in_expr(arg, out);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_fvars_in_expr(ty, out);
            collect_fvars_in_expr(body, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_fvars_in_expr(ty, out);
            collect_fvars_in_expr(val, out);
            collect_fvars_in_expr(body, out);
        }
        ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) | ExprKind::Squash(inner) => {
            collect_fvars_in_expr(inner, out);
        }
        _ => {}
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Pull State
// ════════════════════════════════════════════════════════════════════════════

/// Mutable state for the pull pass.
struct PullState {
    /// Declarations being pulled upward.
    pending: Vec<ToPull>,
}

impl PullState {
    fn new() -> Self {
        Self {
            pending: Vec::new(),
        }
    }

    /// Extract from pending any declarations that directly depend on `fvar_id`.
    fn find_direct_deps(&mut self, fvar_id: FVarId) -> Vec<ToPull> {
        let mut deps = Vec::new();
        let mut keep = Vec::new();
        for item in self.pending.drain(..) {
            if item.used.contains(&fvar_id) {
                deps.push(item);
            } else {
                keep.push(item);
            }
        }
        self.pending = keep;
        deps
    }

    /// Find all transitive dependencies of `fvar_id`: any pending declaration
    /// that depends on `fvar_id`, plus any that depend on those, etc.
    fn find_deps(&mut self, fvar_id: FVarId) -> Vec<ToPull> {
        let direct = self.find_direct_deps(fvar_id);
        self.find_deps_fixpoint(direct)
    }

    /// Transitively close a set of pulled declarations: for each declaration
    /// in `todo`, find anything else in `pending` that depends on it.
    fn find_deps_fixpoint(&mut self, todo: Vec<ToPull>) -> Vec<ToPull> {
        let mut acc: Vec<ToPull> = Vec::new();
        let mut worklist = todo;
        while let Some(item) = worklist.pop() {
            let more = self.find_direct_deps(item.decl.fvar_id);
            worklist.extend(more);
            acc.push(item);
        }
        acc
    }

    /// Find all pending declarations that depend on any of the given parameter FVarIds.
    fn find_params_deps(&mut self, param_fvars: &[FVarId]) -> Vec<ToPull> {
        let mut acc = Vec::new();
        for &fvar_id in param_fvars {
            acc.extend(self.find_deps(fvar_id));
        }
        acc
    }

    /// Extract all pending join points (not fun declarations).
    fn extract_join_points(&mut self) -> Vec<ToPull> {
        let mut jps = Vec::new();
        let mut keep = Vec::new();
        for item in self.pending.drain(..) {
            if item.is_fun {
                keep.push(item);
            } else {
                jps.push(item);
            }
        }
        self.pending = keep;
        // Also find transitive deps among the extracted JPs
        self.find_deps_fixpoint(jps)
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Attach Helpers
// ════════════════════════════════════════════════════════════════════════════

/// Attach an array of pulled declarations to code `k`, respecting
/// inter-declaration dependency ordering.
///
/// Uses a topological visit: before attaching declaration `i`, first
/// attach any declaration `j` whose FVarId is used by `i`.
fn attach(pulled: Vec<ToPull>, k: Code) -> Code {
    if pulled.is_empty() {
        return k;
    }
    let len = pulled.len();
    let mut visited = vec![false; len];
    let mut result = k;

    // Process in reverse so that the first declaration ends up outermost.
    // We visit forward, but attach wraps from inside out, so we need to
    // accumulate in reverse dependency order.
    let mut attach_order: Vec<usize> = Vec::with_capacity(len);

    fn visit(i: usize, pulled: &[ToPull], visited: &mut [bool], attach_order: &mut Vec<usize>) {
        if visited[i] {
            return;
        }
        visited[i] = true;
        let pi = &pulled[i];
        // Before attaching `i`, attach anything that `i` depends on
        for j in 0..pulled.len() {
            if !visited[j] && pi.used.contains(&pulled[j].decl.fvar_id) {
                visit(j, pulled, visited, attach_order);
            }
        }
        attach_order.push(i);
    }

    for i in 0..len {
        visit(i, &pulled, &mut visited, &mut attach_order);
    }

    // Wrap from innermost to outermost: last in attach_order wraps first
    // Convert pulled into an indexable vec where we can take ownership
    let mut slots: Vec<Option<ToPull>> = pulled.into_iter().map(Some).collect();
    for &idx in attach_order.iter().rev() {
        if let Some(item) = slots[idx].take() {
            result = item.attach(result);
        }
    }

    result
}

// ════════════════════════════════════════════════════════════════════════════
// Core Pull Algorithm
// ════════════════════════════════════════════════════════════════════════════

/// Add a local function or join point declaration to the pull state.
///
/// Before adding, recursively processes the declaration's body, and
/// re-attaches any pulled declarations that depend on its parameters.
/// For `Code::Fun`, also re-attaches pending join points (local functions
/// cannot jump to join points defined outside their scope).
fn add_to_pull(is_fun: bool, decl: &FunDecl, state: &mut PullState) {
    // Save current pending state, then clear it so the recursive `pull`
    // of the declaration's body starts fresh.
    let saved = std::mem::take(&mut state.pending);

    // Recursively pull within the declaration's body
    let mut new_body = pull(&decl.body, state);

    // Re-attach any pulled declarations that depend on this decl's parameters
    let param_fvars: Vec<FVarId> = decl.params.iter().map(|p| p.fvar_id).collect();
    let param_deps = state.find_params_deps(&param_fvars);
    new_body = attach(param_deps, new_body);

    // For `fun` declarations, re-attach any pending join points.
    // A local function cannot jump to join points from an outer scope.
    if is_fun {
        let jps = state.extract_join_points();
        let jp_deps = state.find_deps_fixpoint(jps);
        new_body = attach(jp_deps, new_body);
    }

    // Build the updated declaration
    let updated_decl = FunDecl {
        fvar_id: decl.fvar_id,
        name: decl.name.clone(),
        params: decl.params.clone(),
        ty: decl.ty.clone(),
        body: Box::new(new_body),
    };

    // Compute the used FVarIds of the updated declaration
    let used = collect_used_fvars(&updated_decl);

    // Add to pending, then restore saved state after it
    let to_pull = ToPull {
        is_fun,
        decl: updated_decl,
        used,
    };
    state.pending.push(to_pull);
    state.pending.extend(saved);
}

/// Main recursive pull function.
///
/// Walks the code tree, removing `Code::Fun` and `Code::JoinPoint` nodes
/// into the pull state, and re-attaching them at the optimal scope.
fn pull(code: &Code, state: &mut PullState) -> Code {
    match code {
        Code::Let(decl, k) => {
            // Recursively pull in the continuation
            let new_k = pull(k, state);
            // Re-attach any pulled declarations that depend on this let binding
            let deps = state.find_deps(decl.fvar_id);
            let new_k = attach(deps, new_k);
            // Rebuild the let with original decl
            Code::Let(decl.clone(), Box::new(new_k))
        }

        Code::Fun(fun_decl, k) => {
            // Remove the fun declaration from the tree and add to pull state
            add_to_pull(true, fun_decl, state);
            // Continue processing the continuation
            pull(k, state)
        }

        Code::JoinPoint(jp_decl, k) => {
            // Remove the join point from the tree and add to pull state
            add_to_pull(false, jp_decl, state);
            // Continue processing the continuation
            pull(k, state)
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
                        let new_body = pull(body, state);
                        // Re-attach pulled declarations that depend on alt params
                        let param_fvars: Vec<FVarId> = params.iter().map(|p| p.fvar_id).collect();
                        let param_deps = state.find_params_deps(&param_fvars);
                        let new_body = attach(param_deps, new_body);
                        Alt::Ctor {
                            ctor_name: ctor_name.clone(),
                            params: params.clone(),
                            body: Box::new(new_body),
                        }
                    }
                    Alt::Default(body) => {
                        let new_body = pull(body, state);
                        Alt::Default(Box::new(new_body))
                    }
                })
                .collect();

            Code::Cases(crate::lcnf::Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee: cases.scrutinee,
                alts: new_alts,
            })
        }

        // Terminal nodes pass through unchanged
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => code.clone(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Public API
// ════════════════════════════════════════════════════════════════════════════

/// Pull local function declarations to their optimal scope in a Code block.
///
/// Moves `Code::Fun` and `Code::JoinPoint` nodes upward to the outermost
/// position where all their free variables are still in scope.
///
/// # Example
///
/// Before:
/// ```text
/// let x := 1
/// let y := 2
/// fun f (a : Nat) := return a  // f doesn't use x or y
/// let z := f x
/// return z
/// ```
///
/// After:
/// ```text
/// fun f (a : Nat) := return a  // pulled to top (no deps)
/// let x := 1
/// let y := 2
/// let z := f x
/// return z
/// ```
pub fn pull_fun_decls_in_code(code: &Code) -> Code {
    let mut state = PullState::new();
    let result = pull(code, &mut state);
    // Attach any remaining pulled declarations at the top
    attach(state.pending, result)
}

/// Pull local function declarations in an LCNF declaration.
pub fn pull_fun_decls(decl: &Decl) -> Decl {
    let new_body = match &decl.body {
        DeclValue::Code(code) => DeclValue::Code(Box::new(pull_fun_decls_in_code(code))),
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

/// Pull local function declarations in multiple LCNF declarations.
pub fn pull_fun_decls_all(decls: &[Decl]) -> Vec<Decl> {
    decls.iter().map(pull_fun_decls).collect()
}
