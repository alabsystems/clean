// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Deep targeted conv rewriting (#3082)
//!
//! Provides a stateful conv mode navigator for Lean 4-style deep targeted
//! rewriting. The caller can navigate into subexpressions using `enter_lhs`,
//! `enter_rhs`, `enter_arg`, `enter_fun`, and `ext`, apply rewrites at the
//! focused position, then `close()` to produce the final rewritten expression
//! together with a list of applied rewrites.
//!
//! This module builds on the `ConvPosition` and `ConvState` types from
//! `conv.rs`, adding:
//! - `ConvRewrite` — records a single rewrite applied during conv
//! - `DeepConvState` — stateful navigator with ergonomic enter/exit methods
//!
//! ## Example
//!
//! ```text
//! // Goal: f (a + b) = f (b + a)
//! let mut dcs = DeepConvState::new(&goal_expr)?;
//! dcs.enter_lhs()?;          // focus on f (a + b)
//! dcs.enter_arg(0)?;         // focus on (a + b)
//! dcs.apply_rewrite(b_plus_a, proof_add_comm)?;
//! let (new_expr, rewrites) = dcs.close()?;
//! ```

use clean_kernel::expr::ExprKind;
use clean_kernel::Expr;

use super::conv::{ConvPath, ConvPosition, ConvState};
use super::{match_equality, TacticError};

// ============================================================================
// ConvRewrite — record of a single rewrite applied during conv mode
// ============================================================================

/// A single rewrite applied at a specific position during conv mode.
///
/// Records the navigation path at the time of the rewrite, plus the
/// before/after expressions and the proof that `before = after`.
#[derive(Debug, Clone)]
pub struct ConvRewrite {
    /// Navigation path at the time of the rewrite
    pub position: ConvPath,
    /// Expression before the rewrite
    pub before: Expr,
    /// Expression after the rewrite
    pub after: Expr,
    /// Proof that `before = after`
    pub proof: Expr,
}

// ============================================================================
// DeepConvState — stateful conv-mode navigator
// ============================================================================

/// State for deep conv-mode navigation and rewriting.
///
/// Wraps a `ConvState` with higher-level navigation methods that mirror
/// the Lean 4 conv DSL (`lhs`, `rhs`, `arg N`, `ext x`, `enter`).
/// Tracks all rewrites applied during the session so callers can build
/// composite congruence proofs.
pub struct DeepConvState {
    /// Inner conv state (handles position tracking and expression replacement)
    inner: ConvState,
    /// History of rewrites applied during this conv session
    rewrites: Vec<ConvRewrite>,
    /// Bound variable names introduced by `ext` (for documentation/debugging)
    ext_vars: Vec<String>,
}

impl DeepConvState {
    /// Create a new deep conv state from an equality goal.
    ///
    /// The input expression must be an equality `a = b`. The conv state is
    /// initialized at the root of the entire equality expression.
    ///
    /// REQUIRES: `goal` is `@Eq α a b`
    ///
    /// ENSURES: on Ok, `current_expr()` returns `goal`, navigation depth is 0,
    /// no rewrites have been applied
    ///
    /// ENSURES: on Err, `goal` is not a well-formed equality
    pub fn new(goal: &Expr) -> Result<Self, TacticError> {
        // Validate that this is an equality
        let _eq = match_equality(goal)?;
        Ok(DeepConvState {
            inner: ConvState::new(goal.clone()),
            rewrites: Vec::new(),
            ext_vars: Vec::new(),
        })
    }

    /// Create a deep conv state from an arbitrary expression (not necessarily
    /// an equality). Use this when navigating within a non-equality context.
    ///
    /// ENSURES: `current_expr()` returns `expr`, navigation depth is 0
    pub fn new_unchecked(expr: Expr) -> Self {
        DeepConvState {
            inner: ConvState::new(expr),
            rewrites: Vec::new(),
            ext_vars: Vec::new(),
        }
    }

    /// Navigate to the left-hand side of an equality.
    ///
    /// For goal `a = b`, focuses on `a`.
    ///
    /// REQUIRES: current focus is an equality expression
    ///
    /// ENSURES: on Ok, focus is the LHS of the equality; on Err, state unchanged
    pub fn enter_lhs(&mut self) -> Result<(), TacticError> {
        self.inner.go(ConvPosition::EqLhs)
    }

    /// Navigate to the right-hand side of an equality.
    ///
    /// For goal `a = b`, focuses on `b`.
    ///
    /// REQUIRES: current focus is an equality expression
    ///
    /// ENSURES: on Ok, focus is the RHS of the equality; on Err, state unchanged
    pub fn enter_rhs(&mut self) -> Result<(), TacticError> {
        self.inner.go(ConvPosition::EqRhs)
    }

    /// Navigate into the nth argument of the current application.
    ///
    /// For expression `f a0 a1 ... an`, `enter_arg(i)` focuses on `ai`.
    ///
    /// The argument index counts from 0 among the n-ary application arguments
    /// (after unfolding the binary App spine). For a simple `f x`, arg 0 is `x`.
    ///
    /// REQUIRES: current focus is an application with at least `n + 1` arguments
    ///
    /// ENSURES: on Ok, focus is the nth argument; on Err, state unchanged
    pub fn enter_arg(&mut self, n: usize) -> Result<(), TacticError> {
        // Compute arg count and steps_down before mutating self.inner
        let (_total_args, steps_down) = {
            let args = self.inner.focus.get_app_args();
            if args.len() <= n {
                return Err(TacticError::InvalidTarget {
                    tactic: "conv enter_arg".into(),
                    detail: format!(
                        "cannot navigate to argument {n}: expression has {} argument(s)",
                        args.len()
                    ),
                });
            }
            let total = args.len();
            // For n-ary `(((f a0) a1) ... ak)`:
            //   arg k   = AppArg at root
            //   arg k-1 = AppFn then AppArg
            //   arg 0   = AppFn^k then AppArg
            (total, total - 1 - n)
        };
        for _ in 0..steps_down {
            self.inner.go(ConvPosition::AppFn)?;
        }
        self.inner.go(ConvPosition::AppArg)
    }

    /// Navigate into the function part of an application.
    ///
    /// For expression `f x`, focuses on `f`.
    ///
    /// REQUIRES: current focus is an application
    ///
    /// ENSURES: on Ok, focus is the function head; on Err, state unchanged
    pub fn enter_fun(&mut self) -> Result<(), TacticError> {
        self.inner.go(ConvPosition::AppFn)
    }

    /// Enter the body of a binder, introducing a bound variable name.
    ///
    /// For expression `fun (x : T) => body` or `forall (x : T), body`,
    /// focuses on `body` (with BVar(0) as the placeholder for `x`).
    ///
    /// REQUIRES: current focus is a Lambda or Pi expression
    ///
    /// ENSURES: on Ok, focus is the binder body; on Err, state unchanged
    pub fn ext(&mut self, name: &str) -> Result<(), TacticError> {
        match self.inner.focus.kind() {
            ExprKind::Lam(_, _, _) | ExprKind::Pi(_, _, _) => {
                self.ext_vars.push(name.to_string());
                self.inner.go(ConvPosition::BinderBody)
            }
            _ => Err(TacticError::InvalidTarget {
                tactic: "conv ext".into(),
                detail: "cannot enter binder: expression is not a lambda or forall".into(),
            }),
        }
    }

    /// Apply a rewrite at the current focused position.
    ///
    /// Replaces the current focus with `new_expr` and records the rewrite
    /// with its proof.
    ///
    /// REQUIRES: `proof` is a valid proof that `current_focus = new_expr`
    /// (caller is responsible for proof validity)
    ///
    /// ENSURES: on Ok, focus is `new_expr` and the rewrite is recorded;
    /// on Err(NoProgress), `new_expr` equals current focus (no change)
    pub fn apply_rewrite(&mut self, new_expr: Expr, proof: Expr) -> Result<(), TacticError> {
        let before = self.inner.focus.clone();
        if before == new_expr {
            return Err(TacticError::NoProgress {
                tactic: "conv apply_rewrite".into(),
            });
        }
        let position = self.inner.path.clone();
        self.inner.focus = new_expr.clone();
        self.rewrites.push(ConvRewrite {
            position,
            before,
            after: new_expr,
            proof,
        });
        Ok(())
    }

    /// Get a reference to the current focused expression.
    pub fn current_expr(&self) -> &Expr {
        &self.inner.focus
    }

    /// Get the current navigation depth (number of position steps from root).
    #[must_use]
    pub fn depth(&self) -> usize {
        self.inner.path.len()
    }

    /// Get the current navigation path.
    #[must_use]
    pub fn path(&self) -> &ConvPath {
        &self.inner.path
    }

    /// Get the list of rewrites applied so far.
    #[must_use]
    pub fn rewrites(&self) -> &[ConvRewrite] {
        &self.rewrites
    }

    /// Get the bound variable names introduced via `ext`.
    #[must_use]
    pub fn ext_vars(&self) -> &[String] {
        &self.ext_vars
    }

    /// Get a reference to the original (root) expression.
    pub fn original(&self) -> &Expr {
        &self.inner.original
    }

    /// Close the conv session and produce the final rewritten expression
    /// plus the list of all rewrites applied.
    ///
    /// ENSURES: the returned expression is the original with all focused
    /// rewrites applied at their respective positions. The rewrite list
    /// can be used to build composite congruence proofs.
    pub fn close(self) -> (Expr, Vec<ConvRewrite>) {
        let result = self.inner.finish();
        (result, self.rewrites)
    }

    /// Navigate into the binder type.
    ///
    /// For `fun (x : T) => body` or `forall (x : T), body`, focuses on `T`.
    ///
    /// REQUIRES: current focus is a Lambda or Pi expression
    ///
    /// ENSURES: on Ok, focus is the binder type; on Err, state unchanged
    pub fn enter_binder_type(&mut self) -> Result<(), TacticError> {
        match self.inner.focus.kind() {
            ExprKind::Lam(_, _, _) | ExprKind::Pi(_, _, _) => {
                self.inner.go(ConvPosition::BinderType)
            }
            _ => Err(TacticError::InvalidTarget {
                tactic: "conv enter_binder_type".into(),
                detail: "cannot enter binder type: expression is not a lambda or forall".into(),
            }),
        }
    }

    /// Navigate into a let-binding value.
    ///
    /// For `let x : T := v in body`, focuses on `v`.
    ///
    /// REQUIRES: current focus is a Let expression
    ///
    /// ENSURES: on Ok, focus is the let value; on Err, state unchanged
    pub fn enter_let_value(&mut self) -> Result<(), TacticError> {
        match self.inner.focus.kind() {
            ExprKind::Let(_, _, _, _, _) => self.inner.go(ConvPosition::LetValue),
            _ => Err(TacticError::InvalidTarget {
                tactic: "conv enter_let_value".into(),
                detail: "cannot enter let value: expression is not a let binding".into(),
            }),
        }
    }

    /// Navigate into a let-binding body.
    ///
    /// For `let x : T := v in body`, focuses on `body`.
    ///
    /// REQUIRES: current focus is a Let expression
    ///
    /// ENSURES: on Ok, focus is the let body; on Err, state unchanged
    pub fn enter_let_body(&mut self) -> Result<(), TacticError> {
        match self.inner.focus.kind() {
            ExprKind::Let(_, _, _, _, _) => self.inner.go(ConvPosition::LetBody),
            _ => Err(TacticError::InvalidTarget {
                tactic: "conv enter_let_body".into(),
                detail: "cannot enter let body: expression is not a let binding".into(),
            }),
        }
    }
}

/// Create a simple `@Eq α a b` expression for use in tests and conv state
/// initialization.
///
/// Builds `(((Eq α) a) b)` as a 3-argument application.
pub(crate) fn mk_eq_app(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(Expr::app(Expr::app(Expr::const_str("Eq"), ty), lhs), rhs)
}

/// Create a simple binary application `f x`.
pub(crate) fn mk_app2(f: Expr, x: Expr) -> Expr {
    Expr::app(f, x)
}

/// Create a ternary application `f x y` = `((f x) y)`.
pub(crate) fn mk_app3(f: Expr, x: Expr, y: Expr) -> Expr {
    Expr::app(Expr::app(f, x), y)
}
