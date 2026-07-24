// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared conversion helpers for `from_syntax` — patterns, binders, args.

use clean_macro::Syntax;
use clean_parser::{
    Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceLit, SurfaceMatchArm, SurfacePattern,
};

use super::syntax_to_surface;

pub(super) fn syntax_to_arg(syntax: &Syntax) -> Option<SurfaceArg> {
    if let Syntax::Node(node) = syntax {
        if node.kind.name_str() == "namedArg" && node.children.len() == 2 {
            let name = node.children[0].as_ident()?.to_string();
            let expr = syntax_to_surface(&node.children[1])?;
            return Some(SurfaceArg::named(name, expr));
        }
    }
    // Default: convert as a positional argument
    syntax_to_surface(syntax).map(SurfaceArg::positional)
}

/// Convert syntax to a match arm
pub(super) fn syntax_to_match_arm(syntax: &Syntax) -> Option<SurfaceMatchArm> {
    match syntax {
        Syntax::Node(node) if node.kind.name_str() == "matchArm" => {
            if node.children.len() != 2 {
                return None;
            }
            let pattern = syntax_to_pattern(&node.children[0])?;
            let body = syntax_to_surface(&node.children[1])?;
            Some(SurfaceMatchArm {
                span: Span::dummy(),
                pattern,
                body,
            })
        }
        _ => None,
    }
}

/// Convert syntax to a pattern
pub(in crate::macro_integration) fn syntax_to_pattern(syntax: &Syntax) -> Option<SurfacePattern> {
    match syntax {
        Syntax::Ident(_, name) if name == "_" => Some(SurfacePattern::Wildcard),
        Syntax::Ident(_, name) => Some(SurfacePattern::Var(name.clone())),
        Syntax::Node(node) => {
            let kind_name = node.kind.name_str();
            match kind_name {
                "ctorPattern" => {
                    if node.children.is_empty() {
                        return None;
                    }
                    let name = node.children[0].as_ident()?.to_string();
                    let args: Option<Vec<_>> =
                        node.children[1..].iter().map(syntax_to_pattern).collect();
                    Some(SurfacePattern::Ctor(name, args?))
                }
                "num" => {
                    let value = super::parse_nat_atom(node.children.first()?.as_atom()?)?;
                    Some(SurfacePattern::Lit(SurfaceLit::nat(value)))
                }
                "str" => {
                    let value = node.children.first()?.as_atom()?.to_string();
                    Some(SurfacePattern::Lit(SurfaceLit::String(value)))
                }
                "scientific" => {
                    let text = node.children.first()?.as_atom()?.to_string();
                    Some(SurfacePattern::Lit(SurfaceLit::Float(text)))
                }
                "char" => {
                    let atom = node.children.first()?.as_atom()?;
                    let mut chars = atom.chars();
                    let c = chars.next()?;
                    if chars.next().is_some() {
                        return None;
                    }
                    Some(SurfacePattern::Lit(SurfaceLit::Char(c)))
                }
                "numeralAddPattern" => {
                    if node.children.len() != 2 {
                        return None;
                    }
                    let pat = syntax_to_pattern(&node.children[0])?;
                    let n = node.children[1]
                        .children()
                        .first()?
                        .as_atom()?
                        .parse()
                        .ok()?;
                    Some(SurfacePattern::NumeralAdd(Box::new(pat), n))
                }
                "qPattern" => {
                    // Q-pattern: q(expr) - convert syntax back to QPattern
                    // Part of #23: Qq Phase 4 - Runtime pattern matching
                    if node.children.is_empty() {
                        return None;
                    }
                    let inner = syntax_to_surface(&node.children[0])?;
                    Some(SurfacePattern::QPattern(Box::new(inner)))
                }
                "inaccessiblePattern" => {
                    if node.children.len() != 1 {
                        return None;
                    }
                    let inner = syntax_to_surface(&node.children[0])?;
                    Some(SurfacePattern::Inaccessible(Box::new(inner)))
                }
                "asPattern" => {
                    // As-pattern: name@pat — fix for #2211 round-trip gap
                    if node.children.len() != 2 {
                        return None;
                    }
                    let name = node.children[0].as_ident()?.to_string();
                    let pat = syntax_to_pattern(&node.children[1])?;
                    Some(SurfacePattern::As(name, Box::new(pat)))
                }
                "orPattern" => {
                    // Or-pattern: pat1 | pat2 — fix for #2211 round-trip gap
                    if node.children.len() != 2 {
                        return None;
                    }
                    let left = syntax_to_pattern(&node.children[0])?;
                    let right = syntax_to_pattern(&node.children[1])?;
                    Some(SurfacePattern::Or(Box::new(left), Box::new(right)))
                }
                _ => {
                    // Try as constructor with arguments
                    if node.children.is_empty() {
                        Some(SurfacePattern::Var(kind_name.to_string()))
                    } else {
                        let args: Option<Vec<_>> =
                            node.children.iter().map(syntax_to_pattern).collect();
                        Some(SurfacePattern::Ctor(kind_name.to_string(), args?))
                    }
                }
            }
        }
        _ => None,
    }
}

/// Convert syntax to a binder
pub(super) fn syntax_to_binder(syntax: &Syntax) -> Option<SurfaceBinder> {
    // Handle both simple identifiers and typed binders
    match syntax {
        Syntax::Ident(_, name) => Some(SurfaceBinder {
            span: Span::dummy(),
            name: name.clone(),
            ty: None,
            default: None,
            info: SurfaceBinderInfo::Explicit,
        }),

        Syntax::Node(node) => {
            let kind_name = node.kind.name_str();
            let info = match kind_name {
                "binderImplicit" => SurfaceBinderInfo::Implicit,
                "binderInstance" => SurfaceBinderInfo::Instance,
                "binderStrictImplicit" => SurfaceBinderInfo::StrictImplicit,
                _ => SurfaceBinderInfo::Explicit,
            };

            if node.children.is_empty() {
                return None;
            }

            let name = node.children[0].as_ident()?.to_string();
            let ty = if node.children.len() > 1 && !node.children[1].is_missing() {
                Some(Box::new(syntax_to_surface(&node.children[1])?))
            } else {
                None
            };

            Some(SurfaceBinder {
                span: Span::dummy(),
                name,
                ty,
                default: None,
                info,
            })
        }

        _ => None,
    }
}
