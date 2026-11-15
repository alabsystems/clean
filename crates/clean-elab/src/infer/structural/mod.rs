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

mod descent;
mod detect;
mod dot_receiver;
mod hoist;
#[cfg(test)]
mod tests;

use clean_parser::{Projection, SurfaceExpr, SurfaceName, SurfacePattern};

use crate::stack_safe;

pub(crate) use descent::{choose_decreasing_position, classify_descent, Descent, DescentRow};
#[cfg(test)]
pub(crate) use detect::detect_recursion;
pub(crate) use detect::{
    body_mentions_call, detect_recursion_with_params, detect_recursion_with_receiver,
    whole_body_match_rebinds_param,
};
pub(crate) use hoist::hoist_recursive_match;

/// Information about a recursive call detected in the function body
#[derive(Debug, Clone)]
pub(crate) struct RecursiveCall {
    /// Arguments passed to the recursive call (by position)
    pub(crate) args: Vec<RecursiveArg>,
}

/// An argument in a recursive call
#[derive(Debug, Clone)]
pub(crate) enum RecursiveArg {
    /// Argument is a variable reference with given name
    Var(SurfaceName),
    /// Application headed by a potential function-valued constructor field.
    AppliedField,
    /// Argument is some other expression
    Other,
}

/// Result of recursion detection
#[derive(Debug)]
pub(crate) struct RecursionInfo {
    /// True if the body contains recursive calls
    pub(crate) is_recursive: bool,
    /// All detected recursive calls
    pub(crate) calls: Vec<RecursiveCall>,
    /// Index of the decreasing argument (0-indexed), if found
    pub(crate) decreasing_arg: Option<usize>,
}

// =========================================================================
// Helpers shared between detect.rs and tests.rs
// =========================================================================

/// Pre-computed parts of a function name for recursion detection
#[derive(Debug)]
struct RecursionNameParts {
    normalized_full: SurfaceName,
    short: SurfaceName,
    base: Option<SurfaceName>,
    /// Explicit-argument position a method-dot self-call's receiver takes
    /// (`recv.f a…` is `f a… recv …`, Lean's `addLValArg`), when the caller
    /// knows it from the declaration's binder types. `None` keeps the legacy
    /// reading of such a call.
    receiver_pos: Option<usize>,
}

impl RecursionNameParts {
    fn new(full: &SurfaceName) -> Self {
        let normalized_full = normalize_root_prefix(full);
        let short = normalized_full.last_component();
        let base = normalized_full
            .split_first()
            .and_then(|(first, rest)| (!rest.is_anonymous()).then_some(first));
        Self {
            normalized_full,
            short,
            base,
            receiver_pos: None,
        }
    }

    fn with_receiver_pos(full: &SurfaceName, receiver_pos: Option<usize>) -> Self {
        Self {
            receiver_pos,
            ..Self::new(full)
        }
    }

    fn receiver_pos(&self) -> Option<usize> {
        self.receiver_pos
    }

    fn normalized_full(&self) -> &SurfaceName {
        &self.normalized_full
    }

    fn short(&self) -> &SurfaceName {
        &self.short
    }

    fn base(&self) -> Option<&SurfaceName> {
        self.base.as_ref()
    }
}

/// Strip every `_root_.` prefix from a name.
///
/// Shared with `infer::elab_core`'s recursion-aware unknown-identifier
/// refusal, which must decide "is this identifier the name being defined?"
/// under exactly the normalization recursion DETECTION already uses — two
/// answers to that question would let the diagnostic and the lowering
/// disagree about what a self-reference is.
pub(super) fn normalize_root_prefix(name: &SurfaceName) -> SurfaceName {
    name.qualify_under(&SurfaceName::default())
}

pub(super) fn qualified_name_from_proj(expr: &SurfaceExpr) -> Option<SurfaceName> {
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
            let base_name = qualified_name_from_proj(base)?;
            Some(base_name.append(field))
        }
        _ => None,
    })
}

fn binder_shadows_name(binder: &clean_parser::SurfaceBinder, func_name: &SurfaceName) -> bool {
    !binder.name.is_unescaped_component("_") && &binder.name == func_name
}

fn pattern_binds_name(pattern: &SurfacePattern, name: &SurfaceName) -> bool {
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
        SurfacePattern::StructInst { fields, .. } => {
            fields.iter().any(|(_, pat)| pattern_binds_name(pat, name))
        }
    })
}
