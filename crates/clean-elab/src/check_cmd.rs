// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enhanced `#check` command implementation.
//!
//! Provides richer type checking output with support for:
//! - Expression type inference with formatted display
//! - Universe parameter display for polymorphic expressions
//! - Name lookup for constants/inductives in the environment
//!
//! This module builds on the basic `elab_check` in `commands.rs` with
//! structured result types and constant-name lookup.

use crate::error::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, TypeChecker};

/// Result of a `#check` command.
///
/// Contains the elaborated expression, its inferred type, and a
/// formatted display string. Universe parameters are included when
/// the expression is universe-polymorphic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckResult {
    /// The elaborated kernel expression.
    pub elaborated: Expr,
    /// The inferred type of the expression.
    pub type_: Expr,
    /// Formatted display string (e.g., `expr : type`).
    pub display: String,
}

impl std::fmt::Display for CheckResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display)
    }
}

/// Check the type of an already-elaborated kernel expression.
///
/// Creates a fresh [`TypeChecker`], infers the type, and formats the
/// result as `expr : type`. For universe-polymorphic constants, the
/// universe parameters are included in the display.
///
/// # Errors
///
/// Returns [`ElabError::KernelCheckFailed`] if type inference fails.
pub fn check_expression(expr: &Expr, env: &Environment) -> Result<CheckResult, ElabError> {
    let tc = TypeChecker::new(env);
    let ty = tc
        .infer_type(expr)
        .map_err(|e| ElabError::KernelCheckFailed {
            name: Name::anon(),
            detail: e.to_string(),
        })?;

    let display = format!("{expr} : {ty}");

    Ok(CheckResult {
        elaborated: expr.clone(),
        type_: ty,
        display,
    })
}

/// Check a constant by name in the environment.
///
/// Looks up the name as a constant, inductive, constructor, or recursor,
/// and returns a [`CheckResult`] with the declaration's type.
///
/// # Errors
///
/// Returns [`ElabError::UnknownIdent`] if the name is not found.
pub fn check_name(name: &str, env: &Environment) -> Result<CheckResult, ElabError> {
    let n = Name::from_string(name);

    // Try constant lookup.
    if let Some(info) = env.get_const(&n) {
        let display = format_const_check(name, info);
        return Ok(CheckResult {
            elaborated: Expr::const_(
                n,
                info.level_params
                    .iter()
                    .map(|_| clean_kernel::Level::zero())
                    .collect::<Vec<_>>(),
            ),
            type_: info.type_.clone(),
            display,
        });
    }

    // Try inductive lookup.
    if let Some(ind) = env.get_inductive(&n) {
        let display = format!("{name} : {}", ind.type_);
        return Ok(CheckResult {
            elaborated: Expr::const_(
                n,
                ind.level_params
                    .iter()
                    .map(|_| clean_kernel::Level::zero())
                    .collect::<Vec<_>>(),
            ),
            type_: ind.type_.clone(),
            display,
        });
    }

    // Try constructor lookup.
    if let Some(ctor) = env.get_constructor(&n) {
        let display = format!("{name} : {}", ctor.type_);
        return Ok(CheckResult {
            elaborated: Expr::const_(
                n,
                ctor.level_params
                    .iter()
                    .map(|_| clean_kernel::Level::zero())
                    .collect::<Vec<_>>(),
            ),
            type_: ctor.type_.clone(),
            display,
        });
    }

    // Try recursor lookup.
    if let Some(rec) = env.get_recursor(&n) {
        let display = format!("{name} : {}", rec.type_);
        return Ok(CheckResult {
            elaborated: Expr::const_(
                n,
                rec.level_params
                    .iter()
                    .map(|_| clean_kernel::Level::zero())
                    .collect::<Vec<_>>(),
            ),
            type_: rec.type_.clone(),
            display,
        });
    }

    Err(ElabError::UnknownIdent(name.to_owned()))
}

/// Format a constant check result with universe parameters.
fn format_const_check(name: &str, info: &clean_kernel::ConstantInfo) -> String {
    let mut display = String::new();
    display.push_str(name);

    if !info.level_params.is_empty() {
        display.push_str(".{");
        for (i, p) in info.level_params.iter().enumerate() {
            if i > 0 {
                display.push_str(", ");
            }
            display.push_str(&format!("{p}"));
        }
        display.push('}');
    }

    display.push_str(" : ");
    display.push_str(&format!("{}", info.type_));
    display
}

#[cfg(test)]
#[path = "check_cmd_tests.rs"]
mod tests;
