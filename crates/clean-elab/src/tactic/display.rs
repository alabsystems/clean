// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pretty printing for tactic state, goals, and proof contexts.
//!
//! Provides human-readable formatting of proof goals and state, similar to
//! Lean 4's interactive tactic display. Used by the server for editor feedback
//! and by debugging tactics like `trace_state`.
//!
//! # Output Format
//!
//! A single goal displays as:
//! ```text
//! case intro
//! x : Nat
//! h : x > 0
//! ⊢ x + 1 > 1
//! ```
//!
//! Multiple goals display as:
//! ```text
//! 2 goals
//! case left
//! h : P
//! ⊢ Q
//!
//! case right
//! h : Q
//! ⊢ P
//! ```

use std::fmt::Write;

use crate::stack_safe;
use crate::tactic::core::{Goal, LocalDecl, ProofState};
use clean_kernel::expr::ExprKind;
use clean_kernel::{BinderInfo, Environment, Expr, Level, Literal};

// =============================================================================
// ExprFormatter — configurable expression pretty-printing
// =============================================================================

/// Configuration for expression pretty-printing.
///
/// Controls how verbose the output is, whether implicit arguments are shown,
/// whether universe levels are printed, and layout parameters.
#[derive(Debug, Clone)]
pub(crate) struct ExprFormatter {
    /// Show implicit arguments (like Lean 4's `set_option pp.all true`)
    pub pp_all: bool,
    /// Use mathematical notation where possible (e.g., `→` for Pi)
    pub pp_notation: bool,
    /// Show universe levels on Sort/Const
    pub pp_universes: bool,
    /// Maximum recursion depth for nested expressions
    pub max_depth: usize,
    /// Target line width for wrapping (advisory, not enforced)
    pub line_width: usize,
}

impl Default for ExprFormatter {
    fn default() -> Self {
        Self {
            pp_all: false,
            pp_notation: true,
            pp_universes: false,
            max_depth: 64,
            line_width: 100,
        }
    }
}

// =============================================================================
// Expression formatting
// =============================================================================

/// Pretty-print a kernel expression to a human-readable string.
///
/// The `env` parameter is available for future name resolution but is not
/// currently used (the formatter works purely structurally).
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed kernel expression
/// ENSURES: returned string is non-empty for any valid expression
/// ENSURES: recursion is bounded by `config.max_depth`
#[must_use]
pub(crate) fn format_expr(expr: &Expr, _env: &Environment, config: &ExprFormatter) -> String {
    let mut buf = String::new();
    format_expr_inner(expr, config, 0, false, &mut buf);
    buf
}

/// Core recursive formatter. `depth` tracks current nesting for the depth
/// bound. `parens` indicates whether the result should be parenthesised
/// when it is a compound expression (applications, lambdas, etc.).
fn format_expr_inner(
    expr: &Expr,
    config: &ExprFormatter,
    depth: usize,
    parens: bool,
    buf: &mut String,
) {
    if depth >= config.max_depth {
        buf.push_str("...");
        return;
    }

    stack_safe(|| match expr.kind() {
        // --- atoms ---
        ExprKind::BVar(idx) => {
            write!(buf, "#B{idx}").expect("infallible: write to String");
        }
        ExprKind::FVar(id) => {
            write!(buf, "#F{}", id.as_u64()).expect("infallible: write to String");
        }
        ExprKind::Sort(level) => {
            format_sort(level, config, buf);
        }
        ExprKind::Const(name, levels) => {
            write!(buf, "{name}").expect("infallible: write to String");
            if config.pp_universes && !levels.is_empty() {
                buf.push_str(".{");
                for (i, l) in levels.iter().enumerate() {
                    if i > 0 {
                        buf.push_str(", ");
                    }
                    write!(buf, "{l}").expect("infallible: write to String");
                }
                buf.push('}');
            }
        }
        ExprKind::Lit(lit) => match lit {
            Literal::Nat(n) => {
                write!(buf, "{n}").expect("infallible: write to String");
            }
            Literal::String(s) => {
                write!(buf, "\"{s}\"").expect("infallible: write to String");
            }
        },

        // --- binders ---
        ExprKind::Lam(bd, ty, body) => {
            let needs_parens = parens;
            if needs_parens {
                buf.push('(');
            }
            buf.push_str("fun ");
            format_binder_prefix(bd.info, buf);
            buf.push_str(": ");
            format_expr_inner(ty, config, depth + 1, false, buf);
            format_binder_suffix(bd.info, buf);
            buf.push_str(" => ");
            format_expr_inner(body, config, depth + 1, false, buf);
            if needs_parens {
                buf.push(')');
            }
        }
        ExprKind::Pi(bd, ty, body) => {
            let is_arrow = config.pp_notation && !body.has_loose_bvars();
            if is_arrow {
                // Non-dependent: display as A → B
                let needs_parens = parens;
                if needs_parens {
                    buf.push('(');
                }
                format_expr_inner(ty, config, depth + 1, true, buf);
                buf.push_str(" → ");
                format_expr_inner(body, config, depth + 1, false, buf);
                if needs_parens {
                    buf.push(')');
                }
            } else {
                // Dependent: display as ∀ (x : A), B
                let needs_parens = parens;
                if needs_parens {
                    buf.push('(');
                }
                buf.push_str("∀ ");
                format_binder_prefix(bd.info, buf);
                buf.push_str(": ");
                format_expr_inner(ty, config, depth + 1, false, buf);
                format_binder_suffix(bd.info, buf);
                buf.push_str(", ");
                format_expr_inner(body, config, depth + 1, false, buf);
                if needs_parens {
                    buf.push(')');
                }
            }
        }
        ExprKind::Let(name, ty, val, body, _) => {
            let needs_parens = parens;
            if needs_parens {
                buf.push('(');
            }
            buf.push_str("let ");
            write!(buf, "{name}").expect("infallible: write to String");
            buf.push_str(" : ");
            format_expr_inner(ty, config, depth + 1, false, buf);
            buf.push_str(" := ");
            format_expr_inner(val, config, depth + 1, false, buf);
            buf.push_str("; ");
            format_expr_inner(body, config, depth + 1, false, buf);
            if needs_parens {
                buf.push(')');
            }
        }

        // --- application ---
        ExprKind::App(f, a) => {
            if !config.pp_all {
                // Collect application spine for compact display
                let (head, args) = collect_app_spine(expr);
                if args.len() > 1 {
                    let needs_parens = parens;
                    if needs_parens {
                        buf.push('(');
                    }
                    format_expr_inner(&head, config, depth + 1, true, buf);
                    for arg in &args {
                        buf.push(' ');
                        format_expr_inner(arg, config, depth + 1, true, buf);
                    }
                    if needs_parens {
                        buf.push(')');
                    }
                    return;
                }
            }
            let needs_parens = parens;
            if needs_parens {
                buf.push('(');
            }
            format_expr_inner(f, config, depth + 1, true, buf);
            buf.push(' ');
            format_expr_inner(a, config, depth + 1, true, buf);
            if needs_parens {
                buf.push(')');
            }
        }

        // --- projections / metadata ---
        ExprKind::Proj(name, idx, inner) => {
            format_expr_inner(inner, config, depth + 1, true, buf);
            write!(buf, ".{name}.{idx}").expect("infallible: write to String");
        }
        ExprKind::MData(_, inner) => {
            // Metadata is transparent — just format the inner expression
            format_expr_inner(inner, config, depth + 1, parens, buf);
        }
        ExprKind::Squash(inner) => {
            buf.push_str("Squash ");
            format_expr_inner(inner, config, depth + 1, true, buf);
        }
        ExprKind::SProp => {
            buf.push_str("SProp");
        }

        // --- cubical / set-theoretic extensions: generic fallback ---
        _ => {
            write!(buf, "{expr:?}").expect("infallible: write to String");
        }
    });
}

/// Collect the head function and argument spine of a curried application.
fn collect_app_spine(expr: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut cur = expr.clone();
    while let ExprKind::App(f, a) = cur.kind() {
        args.push((**a).clone());
        cur = (**f).clone();
    }
    args.reverse();
    (cur, args)
}

/// Format a Sort expression. `Sort 0` = Prop, `Sort 1` = Type, `Sort (n+1)` = Type n.
fn format_sort(level: &Level, config: &ExprFormatter, buf: &mut String) {
    if config.pp_universes {
        write!(buf, "Sort {level}").expect("infallible: write to String");
        return;
    }
    match level {
        Level::Zero => buf.push_str("Prop"),
        Level::Succ(inner) if !config.pp_universes => {
            // Count successors
            let mut n: u64 = 1;
            let mut cur = inner.as_ref();
            while let Level::Succ(next) = cur {
                n += 1;
                cur = next.as_ref();
            }
            if matches!(cur, Level::Zero) {
                if n == 1 {
                    buf.push_str("Type");
                } else {
                    write!(buf, "Type {}", n - 1).expect("infallible: write to String");
                }
            } else {
                write!(buf, "Sort {level}").expect("infallible: write to String");
            }
        }
        _ => {
            if config.pp_universes {
                write!(buf, "Sort {level}").expect("infallible: write to String");
            } else {
                buf.push_str("Sort _");
            }
        }
    }
}

/// Write the opening delimiter for a binder based on its info.
fn format_binder_prefix(info: BinderInfo, buf: &mut String) {
    match info {
        BinderInfo::Default => buf.push('('),
        BinderInfo::Implicit => buf.push('{'),
        BinderInfo::StrictImplicit => buf.push_str("{{"),
        BinderInfo::InstImplicit => buf.push('['),
    }
}

/// Write the closing delimiter for a binder based on its info.
fn format_binder_suffix(info: BinderInfo, buf: &mut String) {
    match info {
        BinderInfo::Default => buf.push(')'),
        BinderInfo::Implicit => buf.push('}'),
        BinderInfo::StrictImplicit => buf.push_str("}}"),
        BinderInfo::InstImplicit => buf.push(']'),
    }
}

// =============================================================================
// Local context formatting
// =============================================================================

/// Format a slice of local declarations as a hypothesis list.
///
/// Each declaration is rendered as `name : type` on its own line. Let-bindings
/// additionally show `:= value`.
///
/// # Contract
///
/// ENSURES: empty `decls` produces empty string
/// ENSURES: each declaration occupies exactly one line (no trailing newline)
#[must_use]
pub(crate) fn format_local_context(
    decls: &[LocalDecl],
    env: &Environment,
    config: &ExprFormatter,
) -> String {
    let mut lines = Vec::with_capacity(decls.len());
    for decl in decls {
        let ty_str = format_expr(&decl.ty, env, config);
        if let Some(val) = &decl.value {
            let val_str = format_expr(val, env, config);
            lines.push(format!("{} : {} := {}", decl.name, ty_str, val_str));
        } else {
            lines.push(format!("{} : {}", decl.name, ty_str));
        }
    }
    lines.join("\n")
}

// =============================================================================
// Goal formatting
// =============================================================================

/// Format a single goal in Lean 4 interactive style.
///
/// Output:
/// ```text
/// case <tag>
/// h1 : T1
/// h2 : T2
/// ⊢ target
/// ```
///
/// # Contract
///
/// REQUIRES: `goal` is a valid Goal from a ProofState
/// ENSURES: returned string always contains the `⊢` turnstile line
#[must_use]
pub(crate) fn format_goal(goal: &Goal, env: &Environment) -> String {
    let config = ExprFormatter::default();
    format_goal_with_config(goal, env, &config)
}

/// Format a goal with explicit formatter configuration.
#[must_use]
pub(crate) fn format_goal_with_config(
    goal: &Goal,
    env: &Environment,
    config: &ExprFormatter,
) -> String {
    let mut buf = String::new();

    // Case tag (if present)
    if let Some(tag) = &goal.tag {
        writeln!(buf, "case {tag}").expect("infallible: write to String");
    }

    // Local context
    let ctx = format_local_context(&goal.local_ctx, env, config);
    if !ctx.is_empty() {
        writeln!(buf, "{ctx}").expect("infallible: write to String");
    }

    // Turnstile + target
    let target_str = format_expr(&goal.target, env, config);
    write!(buf, "\u{22a2} {target_str}").expect("infallible: write to String");

    buf
}

// =============================================================================
// Proof state formatting
// =============================================================================

/// Format the full proof state showing all remaining goals.
///
/// Output for multiple goals:
/// ```text
/// 2 goals
/// case left
/// h : P
/// ⊢ Q
///
/// case right
/// h : Q
/// ⊢ P
/// ```
///
/// # Contract
///
/// REQUIRES: `state` is a valid ProofState
/// ENSURES: completed states produce `"no goals"`
/// ENSURES: single-goal states omit the count header
#[must_use]
pub(crate) fn format_proof_state(state: &ProofState, env: &Environment) -> String {
    let config = ExprFormatter::default();
    format_proof_state_with_config(state, env, &config)
}

/// Format proof state with explicit formatter configuration.
#[must_use]
pub(crate) fn format_proof_state_with_config(
    state: &ProofState,
    env: &Environment,
    config: &ExprFormatter,
) -> String {
    let goals = state.goals();

    if goals.is_empty() {
        return "no goals".to_string();
    }

    let mut buf = String::new();

    // Goal count header (only for 2+ goals)
    if goals.len() > 1 {
        writeln!(buf, "{} goals", goals.len()).expect("infallible: write to String");
    }

    for (i, goal) in goals.iter().enumerate() {
        if i > 0 {
            buf.push('\n');
        }
        let goal_str = format_goal_with_config(goal, env, config);
        buf.push_str(&goal_str);
        // Add newline between goals, but not after the last one
        if i + 1 < goals.len() {
            buf.push('\n');
        }
    }

    buf
}
