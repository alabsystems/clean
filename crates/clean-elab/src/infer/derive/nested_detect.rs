// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Detect nested inductive containers in surface constructor types.
//!
//! When a constructor field has type `C T1 .. Tn` where `C` is an existing
//! inductive (e.g. `List`) AND some argument mentions the type being
//! defined, the kernel's `eliminate_nested_inductives` transform (see
//! `clean-kernel::env::inductive_nested_elim`) expands the declaration
//! into a mutual block with auxiliary inductives (e.g. `Ty._List`). The
//! generated `ind.casesOn` therefore takes motives/minors for ALL types
//! in the block, not just the originally-declared one. This module
//! provides a pre-add-inductive detection used by derive handlers to
//! avoid emitting single-motive `ind.casesOn` applications that would
//! fail strict kernel type checking (#3434).

use clean_kernel::name::Name;
use clean_kernel::Environment;
use clean_parser::{SurfaceArg, SurfaceCtor, SurfaceExpr};

/// Returns `true` iff any constructor in `ctors` has a field that uses a
/// nested container application referencing the type being defined.
pub(super) fn any_ctor_has_nested_container(
    env: &Environment,
    ind_name: &str,
    ctors: &[SurfaceCtor],
) -> bool {
    ctors
        .iter()
        .any(|c| ctor_has_nested_container(env, ind_name, &c.ty))
}

/// Walk a surface expression looking for an identifier whose name matches
/// `ind_name`. Used to detect `List Ty` where `Ty` is the type being defined.
fn surface_mentions_name(expr: &SurfaceExpr, ind_name: &str) -> bool {
    match expr {
        SurfaceExpr::Ident(_, n) => n == ind_name,
        SurfaceExpr::App(_, head, args) => {
            surface_mentions_name(head, ind_name)
                || args
                    .iter()
                    .any(|a| surface_mentions_name(&a.expr, ind_name))
        }
        SurfaceExpr::Pi(_, binders, body) | SurfaceExpr::Lambda(_, binders, body) => {
            binders.iter().any(|b| {
                b.ty.as_ref()
                    .map(|t| surface_mentions_name(t, ind_name))
                    .unwrap_or(false)
            }) || surface_mentions_name(body, ind_name)
        }
        SurfaceExpr::Arrow(_, l, r) => {
            surface_mentions_name(l, ind_name) || surface_mentions_name(r, ind_name)
        }
        SurfaceExpr::Paren(_, inner)
        | SurfaceExpr::Ascription(_, inner, _)
        | SurfaceExpr::OutParam(_, inner)
        | SurfaceExpr::SemiOutParam(_, inner)
        | SurfaceExpr::Explicit(_, inner) => surface_mentions_name(inner, ind_name),
        _ => false,
    }
}

/// Walk the Pi/Arrow chain of a constructor type, inspecting each domain
/// for nested-container applications.
fn ctor_has_nested_container(env: &Environment, ind_name: &str, expr: &SurfaceExpr) -> bool {
    match expr {
        SurfaceExpr::Pi(_, binders, body) => {
            for b in binders {
                if let Some(ty) = &b.ty {
                    if ty_is_nested_container(env, ind_name, ty) {
                        return true;
                    }
                }
            }
            ctor_has_nested_container(env, ind_name, body)
        }
        SurfaceExpr::Arrow(_, dom, cod) => {
            ty_is_nested_container(env, ind_name, dom)
                || ctor_has_nested_container(env, ind_name, cod)
        }
        SurfaceExpr::Paren(_, inner) => ctor_has_nested_container(env, ind_name, inner),
        _ => false,
    }
}

/// Check whether the given type expression IS a nested-container
/// application: `App(Ident(C), args)` where `C != ind_name`, `C` is a
/// registered inductive, and some argument mentions `ind_name`.
fn ty_is_nested_container(env: &Environment, ind_name: &str, ty: &SurfaceExpr) -> bool {
    let ty = match ty {
        SurfaceExpr::Paren(_, inner) => inner.as_ref(),
        other => other,
    };
    if let SurfaceExpr::Arrow(_, dom, cod) = ty {
        return ty_is_nested_container(env, ind_name, dom)
            || ty_is_nested_container(env, ind_name, cod);
    }
    if let SurfaceExpr::App(_, head, args) = ty {
        let head = match head.as_ref() {
            SurfaceExpr::Paren(_, inner) => inner.as_ref(),
            other => other,
        };
        if let SurfaceExpr::Ident(_, container_name) = head {
            if container_name != ind_name
                && env
                    .get_inductive(&Name::from_string(container_name))
                    .is_some()
                && args
                    .iter()
                    .any(|a: &SurfaceArg| surface_mentions_name(&a.expr, ind_name))
            {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_parser::parse_decl_with_tactics;

    /// Parse a surface inductive declaration and extract its constructor list.
    fn parse_ctors(src: &str) -> (String, Vec<SurfaceCtor>) {
        let patterns = crate::tactic::builtins::builtin_tactic_patterns();
        let decl = parse_decl_with_tactics(src, &patterns).expect("should parse");
        match decl {
            clean_parser::SurfaceDecl::Inductive { name, ctors, .. } => (name, ctors),
            other => panic!("expected inductive, got {other:?}"),
        }
    }

    #[test]
    fn detect_list_self_nested() {
        let env = Environment::with_prelude();
        let (name, ctors) = parse_ctors(
            r"inductive Ty
| I32 : Ty
| Bool : Ty
| Tuple : List Ty -> Ty",
        );
        assert!(
            any_ctor_has_nested_container(&env, &name, &ctors),
            "Tuple : List Ty -> Ty should register as nested"
        );
    }

    #[test]
    fn no_nesting_for_simple_enum() {
        let env = Environment::with_prelude();
        let (name, ctors) = parse_ctors(
            r"inductive Color
| red
| green
| blue",
        );
        assert!(!any_ctor_has_nested_container(&env, &name, &ctors));
    }

    #[test]
    fn no_nesting_for_direct_self_recursion() {
        let env = Environment::with_prelude();
        // Direct self-reference (e.g. node : NodeList -> Tree) is a mutual/
        // recursive case handled separately — we only flag nested-container
        // forms like `List Tree`.
        let (name, ctors) = parse_ctors(
            r"inductive Peano
| zero : Peano
| succ : Peano -> Peano",
        );
        assert!(!any_ctor_has_nested_container(&env, &name, &ctors));
    }
}
