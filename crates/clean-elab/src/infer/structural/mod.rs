// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural recursion analysis and compilation
//!
//! Detects recursive function definitions and compiles them to recursor
//! applications. This is Phase 1 of recursive function elaboration (#378).
//!
//! # Overview
//!
//! A recursive function like:
//! ```lean
//! def map (f : A -> B) (xs : List A) : List B :=
//!   match xs with
//!   | [] => []
//!   | x :: xs' => f x :: map f xs'
//! ```
//!
//! Is compiled to:
//! ```lean
//! def map := fun f => List.rec
//!   []                                    -- nil case
//!   (fun x xs' ih => f x :: ih)           -- cons case
//! ```
//!
//! # Algorithm
//!
//! 1. Detect recursive calls (self-references to the function being defined)
//! 2. Track which arguments are passed at each call site
//! 3. Identify the decreasing argument (structurally smaller in all calls)
//! 4. Transform match expressions to recursor applications

mod detect;
#[cfg(test)]
mod tests;

use clean_parser::{Projection, SurfaceExpr, SurfacePattern};

use crate::stack_safe;

#[cfg(test)]
pub(crate) use detect::detect_recursion;
pub use detect::{
    body_mentions_call, detect_recursion_with_params, whole_body_match_rebinds_param,
};

/// Information about a recursive call detected in the function body
#[derive(Debug, Clone)]
pub struct RecursiveCall {
    /// Arguments passed to the recursive call (by position)
    pub args: Vec<RecursiveArg>,
}

/// An argument in a recursive call
#[derive(Debug, Clone)]
pub enum RecursiveArg {
    /// Argument is a variable reference with given name
    Var(String),
    /// Argument is some other expression
    Other,
}

/// Result of recursion detection
#[derive(Debug)]
pub struct RecursionInfo {
    /// True if the body contains recursive calls
    pub is_recursive: bool,
    /// All detected recursive calls
    pub calls: Vec<RecursiveCall>,
    /// Index of the decreasing argument (0-indexed), if found
    pub decreasing_arg: Option<usize>,
}

// =========================================================================
// Helpers shared between detect.rs and tests.rs
// =========================================================================

/// Pre-computed parts of a function name for recursion detection
#[derive(Debug)]
struct RecursionNameParts {
    normalized_full: String,
    short: String,
    base: Option<String>,
}

impl RecursionNameParts {
    fn new(full: &str) -> Self {
        let normalized_full = normalize_root_prefix(full).to_string();
        let short = normalized_full
            .rsplit_once('.')
            .map(|(_, tail)| tail.to_string())
            .unwrap_or_else(|| normalized_full.clone());
        let base = normalized_full
            .split_once('.')
            .map(|(head, _)| head.to_string());
        Self {
            normalized_full,
            short,
            base,
        }
    }

    fn normalized_full(&self) -> &str {
        &self.normalized_full
    }

    fn short(&self) -> &str {
        &self.short
    }

    fn base(&self) -> Option<&str> {
        self.base.as_deref()
    }
}

fn normalize_root_prefix(name: &str) -> &str {
    let mut current = name;
    while let Some(stripped) = current.strip_prefix("_root_.") {
        current = stripped;
    }
    current
}

pub(super) fn qualified_name_from_proj(expr: &SurfaceExpr) -> Option<String> {
    stack_safe(|| match expr {
        SurfaceExpr::Ident(_, name) => Some(name.clone()),
        SurfaceExpr::Paren(_, inner) => qualified_name_from_proj(inner),
        // Unwrap wrappers that don't change the identity of the expression (#388)
        SurfaceExpr::Explicit(_, inner) => qualified_name_from_proj(inner),
        SurfaceExpr::Ascription(_, inner, _) => qualified_name_from_proj(inner),
        SurfaceExpr::UniverseInst(_, inner, _) => qualified_name_from_proj(inner),
        SurfaceExpr::OutParam(_, inner) => qualified_name_from_proj(inner),
        SurfaceExpr::SemiOutParam(_, inner) => qualified_name_from_proj(inner),
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            let mut base_name = qualified_name_from_proj(base)?;
            base_name.push('.');
            base_name.push_str(field);
            Some(base_name)
        }
        _ => None,
    })
}

fn binder_shadows_name(binder: &clean_parser::SurfaceBinder, func_name: &str) -> bool {
    binder.name != "_" && binder.name == func_name
}

fn pattern_binds_name(pattern: &SurfacePattern, name: &str) -> bool {
    stack_safe(|| match pattern {
        SurfacePattern::Var(var) => var == name,
        SurfacePattern::Ctor(_, sub_pats) => sub_pats.iter().any(|p| pattern_binds_name(p, name)),
        SurfacePattern::Wildcard => false,
        SurfacePattern::Ellipsis => false,
        SurfacePattern::Inaccessible(_) => false,
        SurfacePattern::Lit(_) => false,
        SurfacePattern::NumeralAdd(inner, _) => pattern_binds_name(inner, name),
        SurfacePattern::As(var, inner) => var == name || pattern_binds_name(inner, name),
        SurfacePattern::Or(left, right) => {
            pattern_binds_name(left, name) || pattern_binds_name(right, name)
        }
        SurfacePattern::QPattern(_) => false,
    })
}
