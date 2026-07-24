// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level do-notation desugaring.
//!
//! Complements `do_notation.rs` (surface-level) by providing desugaring that
//! operates directly on kernel `Expr` trees. This is used in post-elaboration
//! passes where do-blocks have already been partially lowered to kernel terms
//! but still need monadic bind/pure structure.
//!
//! Control flow constructs (for loops, try/catch, repeat) are in the sibling
//! module [`do_notation_desugar_control`].
//!
//! # Key differences from `do_notation.rs`
//!
//! - Works on `clean_kernel::Expr` (de Bruijn indices) not `SurfaceExpr`
//! - Produces `Expr::app`, `Expr::lam`, `Expr::let_named` directly
//! - Tracks mutable variable usage and bind counts for diagnostics
//! - Configurable monad class name and auto-pure behavior
//!
//! Reference: Lean 4 `src/Lean/Elab/Do/Basic.lean`

use crate::ElabError;
use clean_kernel::expr::BinderInfo;
use clean_kernel::{Expr, ExprKind, FVarId, Name};
use std::sync::atomic::{AtomicU64, Ordering};

// Re-export control flow desugaring for callers that use the main module.
pub(crate) use crate::do_notation_desugar_control::{
    desugar_for_loop, desugar_repeat, desugar_try_catch,
};

/// Counter for generating fresh FVarIds during kernel-level do-notation desugaring.
/// Uses a high range (starting at 0x8000_0000_0000_0000) to avoid collisions
/// with FVarIds allocated by the elaboration context.
static DO_DESUGAR_FVAR_COUNTER: AtomicU64 = AtomicU64::new(0x8000_0000_0000_0000);

/// Generate a fresh FVarId for use in kernel-level do-notation desugaring.
pub(crate) fn fresh_fvar_id() -> FVarId {
    FVarId::new(DO_DESUGAR_FVAR_COUNTER.fetch_add(1, Ordering::Relaxed))
}

// ---------------------------------------------------------------------------
// DoStmt: kernel-level do statement representation
// ---------------------------------------------------------------------------

/// A single statement in a kernel-level do-notation block.
///
/// Each variant corresponds to a monadic do-notation construct and desugars
/// into kernel `Expr` nodes using `Bind.bind`, `Pure.pure`, etc.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) enum DoStmt {
    /// Monadic bind: `let pat ← val` → `Bind.bind val (fun pat => rest)`
    Bind { pat: Name, val: Expr },
    /// Pure let binding: `let name := val` → `let name := val in rest`
    Let { name: Name, val: Expr },
    /// Mutable let binding: `let mut name := val`
    /// Surface desugaring identical to `Let`; tracked in `mut_vars`.
    LetMut { name: Name, val: Expr },
    /// Mutable reassignment: `name := val`
    /// Desugars to let-shadowing at the kernel level.
    Assign { name: Name, val: Expr },
    /// Bare expression statement.
    /// Non-terminal: `Bind.bind expr (fun _ => rest)`. Terminal: expr itself.
    Action(Expr),
    /// Return: `return expr` → `Pure.pure expr`
    Return(Option<Expr>),
    /// Conditional: `if cond then ... else ...`
    If {
        cond: Expr,
        then_: Vec<DoStmt>,
        else_: Vec<DoStmt>,
    },
    /// For-in loop: `for var in iter do body`
    For {
        var: Name,
        iter: Expr,
        body: Vec<DoStmt>,
    },
    /// Try/catch: `try ... catch var => ...`
    TryCatch {
        try_body: Vec<DoStmt>,
        catch_var: Name,
        catch_body: Vec<DoStmt>,
    },
    /// Unless guard: `unless cond do body`
    Unless { cond: Expr, body: Vec<DoStmt> },
    /// Repeat loop: `repeat body` with optional `until` condition
    Repeat {
        body: Vec<DoStmt>,
        until: Option<Expr>,
    },
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for kernel-level do-notation desugaring.
#[derive(Debug, Clone)]
pub(crate) struct DoDesugarConfig {
    /// Monad type class name (default: `"Monad"`).
    pub(crate) monad_class: Name,
    /// Whether mutable variable bindings (`let mut`) are allowed.
    pub(crate) allow_mut: bool,
    /// Whether the last statement is automatically wrapped in `Pure.pure`.
    pub(crate) auto_pure_last: bool,
}

impl Default for DoDesugarConfig {
    fn default() -> Self {
        Self {
            monad_class: Name::from_string("Monad"),
            allow_mut: true,
            auto_pure_last: true,
        }
    }
}

// ---------------------------------------------------------------------------
// Result
// ---------------------------------------------------------------------------

/// Result of kernel-level do-notation desugaring.
#[derive(Debug, Clone)]
pub(crate) struct DoDesugarResult {
    /// The desugared kernel expression.
    pub(crate) desugared: Expr,
    /// Number of `Bind.bind` nodes introduced.
    pub(crate) bind_count: usize,
    /// Mutable variables encountered during desugaring.
    pub(crate) mut_vars: Vec<Name>,
}

// ---------------------------------------------------------------------------
// Kernel expression constructors (pub(crate) for control module)
// ---------------------------------------------------------------------------

/// Build `Bind.bind val (fun pat => body)` as a kernel `Expr`.
///
/// If `fvar` is `Some(id)`, abstracts `FVar(id)` in `body` to produce
/// a proper de Bruijn `BVar(0)` reference inside the lambda. This is
/// necessary for chained binds where later statements reference variables
/// introduced by earlier binds.
///
/// If `fvar` is `None`, the body is used as-is (legacy behavior for cases
/// where no variable substitution was performed).
pub(crate) fn make_bind(val: Expr, pat: &Name, body: Expr) -> Expr {
    make_bind_with_fvar(val, pat, body, None)
}

/// Build `Bind.bind val (fun pat => body)` with explicit FVar abstraction.
pub(crate) fn make_bind_with_fvar(
    val: Expr,
    _pat: &Name,
    body: Expr,
    fvar: Option<FVarId>,
) -> Expr {
    let bind_const = Expr::const_str("Bind.bind");
    let abstracted_body = if let Some(id) = fvar {
        body.abstract_fvar(id)
    } else {
        body
    };
    let lam = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("_hole"),
        abstracted_body,
    );
    Expr::app(Expr::app(bind_const, val), lam)
}

/// Build `Pure.pure val` as a kernel `Expr`.
pub(crate) fn make_pure(val: Expr) -> Expr {
    Expr::app(Expr::const_str("Pure.pure"), val)
}

/// Build `let name : _ := val in body` as a kernel `Expr`.
pub(crate) fn make_let(name: &Name, val: Expr, body: Expr) -> Expr {
    Expr::let_named(name.clone(), Expr::const_str("_hole"), val, body, false)
}

/// Build a kernel-level if-then-else expression.
pub(crate) fn make_ite(cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr {
    let ite = Expr::const_str("ite");
    Expr::app(Expr::app(Expr::app(ite, cond), then_expr), else_expr)
}

/// Build `PUnit.unit` constant.
pub(crate) fn make_unit() -> Expr {
    Expr::const_str("PUnit.unit")
}

// ---------------------------------------------------------------------------
// Variable substitution helpers for proper de Bruijn abstraction
// ---------------------------------------------------------------------------

/// Replace all occurrences of `Const(name, [])` with `FVar(id)` in an expression.
///
/// This is used during kernel-level do-notation desugaring to introduce temporary
/// free variables that will later be abstracted into `BVar` by `abstract_fvar`.
fn subst_const_to_fvar(expr: &Expr, name: &Name, id: FVarId) -> Expr {
    match expr.kind() {
        ExprKind::Const(n, levels) if n == name && levels.is_empty() => Expr::fvar(id),
        ExprKind::App(f, a) => {
            let new_f = subst_const_to_fvar(f, name, id);
            let new_a = subst_const_to_fvar(a, name, id);
            Expr::app(new_f, new_a)
        }
        ExprKind::Lam(bd, ty, body) => {
            let new_ty = subst_const_to_fvar(ty, name, id);
            let new_body = subst_const_to_fvar(body, name, id);
            Expr::lam(*bd, new_ty, new_body)
        }
        ExprKind::Pi(bd, ty, body) => {
            let new_ty = subst_const_to_fvar(ty, name, id);
            let new_body = subst_const_to_fvar(body, name, id);
            Expr::pi(*bd, new_ty, new_body)
        }
        ExprKind::Let(n, ty, val, body, non_dep) => {
            let new_ty = subst_const_to_fvar(ty, name, id);
            let new_val = subst_const_to_fvar(val, name, id);
            let new_body = subst_const_to_fvar(body, name, id);
            Expr::let_named(n.clone(), new_ty, new_val, new_body, *non_dep)
        }
        _ => expr.clone(),
    }
}

/// Replace `Const(name, [])` with `FVar(id)` throughout a sequence of `DoStmt`.
pub(crate) fn subst_stmts(stmts: &[DoStmt], name: &Name, id: FVarId) -> Vec<DoStmt> {
    stmts.iter().map(|s| subst_do_stmt(s, name, id)).collect()
}

/// Replace `Const(name, [])` with `FVar(id)` in a single `DoStmt`.
fn subst_do_stmt(stmt: &DoStmt, name: &Name, id: FVarId) -> DoStmt {
    match stmt {
        DoStmt::Bind { pat, val } => DoStmt::Bind {
            pat: pat.clone(),
            val: subst_const_to_fvar(val, name, id),
        },
        DoStmt::Let { name: n, val } => DoStmt::Let {
            name: n.clone(),
            val: subst_const_to_fvar(val, name, id),
        },
        DoStmt::LetMut { name: n, val } => DoStmt::LetMut {
            name: n.clone(),
            val: subst_const_to_fvar(val, name, id),
        },
        DoStmt::Assign { name: n, val } => DoStmt::Assign {
            name: n.clone(),
            val: subst_const_to_fvar(val, name, id),
        },
        DoStmt::Action(expr) => DoStmt::Action(subst_const_to_fvar(expr, name, id)),
        DoStmt::Return(opt_expr) => {
            DoStmt::Return(opt_expr.as_ref().map(|e| subst_const_to_fvar(e, name, id)))
        }
        DoStmt::If { cond, then_, else_ } => DoStmt::If {
            cond: subst_const_to_fvar(cond, name, id),
            then_: subst_stmts(then_, name, id),
            else_: subst_stmts(else_, name, id),
        },
        DoStmt::For { var, iter, body } => DoStmt::For {
            var: var.clone(),
            iter: subst_const_to_fvar(iter, name, id),
            body: subst_stmts(body, name, id),
        },
        DoStmt::TryCatch {
            try_body,
            catch_var,
            catch_body,
        } => DoStmt::TryCatch {
            try_body: subst_stmts(try_body, name, id),
            catch_var: catch_var.clone(),
            catch_body: subst_stmts(catch_body, name, id),
        },
        DoStmt::Unless { cond, body } => DoStmt::Unless {
            cond: subst_const_to_fvar(cond, name, id),
            body: subst_stmts(body, name, id),
        },
        DoStmt::Repeat { body, until } => DoStmt::Repeat {
            body: subst_stmts(body, name, id),
            until: until.as_ref().map(|e| subst_const_to_fvar(e, name, id)),
        },
    }
}

// ---------------------------------------------------------------------------
// Mutable variable collection
// ---------------------------------------------------------------------------

/// Collect all mutable variable names from a statement sequence.
pub(crate) fn collect_mut_vars(stmts: &[DoStmt]) -> Vec<Name> {
    let mut vars = Vec::new();
    collect_mut_vars_inner(stmts, &mut vars);
    vars
}

fn collect_mut_vars_inner(stmts: &[DoStmt], vars: &mut Vec<Name>) {
    for stmt in stmts {
        match stmt {
            DoStmt::LetMut { name, .. } => {
                if !vars.iter().any(|v| v == name) {
                    vars.push(name.clone());
                }
            }
            DoStmt::If { then_, else_, .. } => {
                collect_mut_vars_inner(then_, vars);
                collect_mut_vars_inner(else_, vars);
            }
            DoStmt::For { body, .. }
            | DoStmt::Unless { body, .. }
            | DoStmt::Repeat { body, .. } => {
                collect_mut_vars_inner(body, vars);
            }
            DoStmt::TryCatch {
                try_body,
                catch_body,
                ..
            } => {
                collect_mut_vars_inner(try_body, vars);
                collect_mut_vars_inner(catch_body, vars);
            }
            DoStmt::Bind { .. }
            | DoStmt::Let { .. }
            | DoStmt::Assign { .. }
            | DoStmt::Action(_)
            | DoStmt::Return(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Core desugaring
// ---------------------------------------------------------------------------

/// Desugar a do-block (sequence of `DoStmt`) into a kernel `Expr`.
///
/// # Errors
///
/// Returns `ElabError::NotImplemented` if the block is empty or contains
/// disallowed constructs per the config.
pub(crate) fn desugar_do_block(
    stmts: &[DoStmt],
    config: &DoDesugarConfig,
) -> Result<DoDesugarResult, ElabError> {
    if stmts.is_empty() {
        return Err(ElabError::NotImplemented("empty do block".into()));
    }
    let mut_vars = collect_mut_vars(stmts);
    if !config.allow_mut && !mut_vars.is_empty() {
        return Err(ElabError::NotImplemented(
            "mutable variables not allowed in this context".into(),
        ));
    }
    let mut bind_count = 0;
    let expr = desugar_stmts(stmts, config, &mut bind_count)?;
    Ok(DoDesugarResult {
        desugared: expr,
        bind_count,
        mut_vars,
    })
}

/// Desugar a statement sequence, accumulating bind count.
pub(crate) fn desugar_stmts(
    stmts: &[DoStmt],
    config: &DoDesugarConfig,
    bind_count: &mut usize,
) -> Result<Expr, ElabError> {
    match stmts {
        [] => Err(ElabError::NotImplemented("empty do block".into())),
        [single] => desugar_terminal(single, config, bind_count),
        [first, rest @ ..] => desugar_stmt(first, rest, config, bind_count),
    }
}

/// Desugar a terminal (last) statement.
fn desugar_terminal(
    stmt: &DoStmt,
    config: &DoDesugarConfig,
    bind_count: &mut usize,
) -> Result<Expr, ElabError> {
    match stmt {
        DoStmt::Action(expr) => {
            if config.auto_pure_last {
                Ok(make_pure(expr.clone()))
            } else {
                Ok(expr.clone())
            }
        }
        DoStmt::Return(Some(expr)) => Ok(make_pure(expr.clone())),
        DoStmt::Return(None) => Ok(make_pure(make_unit())),
        DoStmt::Bind { val, .. } => Ok(val.clone()),
        DoStmt::Let { .. } | DoStmt::LetMut { .. } | DoStmt::Assign { .. } => Err(
            ElabError::NotImplemented("do block cannot end with a let/assign binding".into()),
        ),
        DoStmt::If { cond, then_, else_ } => {
            let then_expr = desugar_stmts(then_, config, bind_count)?;
            let else_expr = if else_.is_empty() {
                make_pure(make_unit())
            } else {
                desugar_stmts(else_, config, bind_count)?
            };
            Ok(make_ite(cond.clone(), then_expr, else_expr))
        }
        DoStmt::For { var, iter, body } => {
            desugar_for_loop(var, iter, body, &[], config, bind_count)
        }
        DoStmt::TryCatch {
            try_body,
            catch_var,
            catch_body,
        } => desugar_try_catch(try_body, catch_var, catch_body, &[], config, bind_count),
        DoStmt::Unless { cond, body } => {
            let body_expr = desugar_stmts(body, config, bind_count)?;
            Ok(make_ite(cond.clone(), make_pure(make_unit()), body_expr))
        }
        DoStmt::Repeat { body, until } => desugar_repeat(body, until.as_ref(), config, bind_count),
    }
}

/// Desugar a non-terminal statement with its continuation.
///
/// For `Bind`, `Let`, `LetMut`, and `Assign` statements that introduce named
/// variables, this function creates a fresh FVar, substitutes the variable name
/// in all remaining statements, desugars the continuation, and then abstracts
/// the FVar to produce proper de Bruijn indices. This ensures that chained binds
/// like `do let n <- f; g n; pure n` produce closed continuation lambdas where
/// `n` is properly captured as `BVar(0)`.
pub(crate) fn desugar_stmt(
    stmt: &DoStmt,
    rest: &[DoStmt],
    config: &DoDesugarConfig,
    bind_count: &mut usize,
) -> Result<Expr, ElabError> {
    match stmt {
        DoStmt::Bind { pat, val } => {
            // Create a fresh FVar for the pattern variable
            let fvar_id = fresh_fvar_id();
            // Substitute Const(pat) -> FVar(fvar_id) in all rest statements
            let subst_rest = subst_stmts(rest, pat, fvar_id);
            let rest_expr = desugar_stmts(&subst_rest, config, bind_count)?;
            *bind_count += 1;
            Ok(make_bind_with_fvar(
                val.clone(),
                pat,
                rest_expr,
                Some(fvar_id),
            ))
        }
        DoStmt::Let { name, val } | DoStmt::LetMut { name, val } => {
            // Create a fresh FVar for the let-bound variable
            let fvar_id = fresh_fvar_id();
            let subst_rest = subst_stmts(rest, name, fvar_id);
            let rest_expr = desugar_stmts(&subst_rest, config, bind_count)?;
            // Abstract FVar -> BVar in body for proper de Bruijn
            let body_abs = rest_expr.abstract_fvar(fvar_id);
            Ok(make_let(name, val.clone(), body_abs))
        }
        DoStmt::Assign { name, val } => {
            // Assign desugars to let-shadowing
            let fvar_id = fresh_fvar_id();
            let subst_rest = subst_stmts(rest, name, fvar_id);
            let rest_expr = desugar_stmts(&subst_rest, config, bind_count)?;
            let body_abs = rest_expr.abstract_fvar(fvar_id);
            Ok(make_let(name, val.clone(), body_abs))
        }
        DoStmt::Action(expr) => {
            let rest_expr = desugar_stmts(rest, config, bind_count)?;
            *bind_count += 1;
            let wildcard = Name::from_string("_");
            Ok(make_bind(expr.clone(), &wildcard, rest_expr))
        }
        DoStmt::Return(Some(expr)) => Ok(make_pure(expr.clone())),
        DoStmt::Return(None) => Ok(make_pure(make_unit())),
        DoStmt::If { cond, then_, else_ } => {
            let rest_expr = desugar_stmts(rest, config, bind_count)?;
            let then_expr = desugar_stmts(then_, config, bind_count)?;
            let else_expr = if else_.is_empty() {
                make_pure(make_unit())
            } else {
                desugar_stmts(else_, config, bind_count)?
            };
            let if_expr = make_ite(cond.clone(), then_expr, else_expr);
            *bind_count += 1;
            let wildcard = Name::from_string("_");
            Ok(make_bind(if_expr, &wildcard, rest_expr))
        }
        DoStmt::For { var, iter, body } => {
            desugar_for_loop(var, iter, body, rest, config, bind_count)
        }
        DoStmt::TryCatch {
            try_body,
            catch_var,
            catch_body,
        } => desugar_try_catch(try_body, catch_var, catch_body, rest, config, bind_count),
        DoStmt::Unless { cond, body } => {
            let rest_expr = desugar_stmts(rest, config, bind_count)?;
            let body_expr = desugar_stmts(body, config, bind_count)?;
            let unless_expr = make_ite(cond.clone(), make_pure(make_unit()), body_expr);
            *bind_count += 1;
            let wildcard = Name::from_string("_");
            Ok(make_bind(unless_expr, &wildcard, rest_expr))
        }
        DoStmt::Repeat { body, until } => {
            let rest_expr = desugar_stmts(rest, config, bind_count)?;
            let repeat_expr = desugar_repeat(body, until.as_ref(), config, bind_count)?;
            *bind_count += 1;
            let wildcard = Name::from_string("_");
            Ok(make_bind(repeat_expr, &wildcard, rest_expr))
        }
    }
}
