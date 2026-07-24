// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conversion from macro `Syntax` back to `SurfaceExpr`.
//!
//! This is the reverse direction: after macro expansion, the generic `Syntax`
//! AST is converted back to `SurfaceExpr` for elaboration.

mod do_notation;
mod helpers;

pub(super) use helpers::syntax_to_pattern;

use do_notation::syntax_to_do_elem;
use helpers::{syntax_to_arg, syntax_to_binder, syntax_to_match_arm};

use crate::stack_safe;
use clean_macro::Syntax;
use clean_parser::{
    Projection, QAntiquotContent, QQuotationKind, Span, SurfaceBinder, SurfaceBinderInfo,
    SurfaceExpr, SurfaceFieldAssign, SurfaceLit, UniverseExpr,
};

use super::syntax_to_level;

/// Parse a numeral atom (as produced by `Syntax::mk_num`/`mk_num_str`) back into
/// an arbitrary-precision `clean_kernel::BigNat`. Handles the `0x`/`0b`/`0o`
/// base prefixes and underscore separators, mirroring the lexer, so a `>= 2^64`
/// literal survives the macro `Syntax` roundtrip losslessly (the `BigNat` hex
/// form emitted by `mk_num_str` re-parses to the same value). Returns `None` for
/// non-numeric atoms (identifiers, operator atoms), which fall back to strings.
pub(super) fn parse_nat_atom(s: &str) -> Option<clean_kernel::BigNat> {
    let (radix, digits) = if let Some(rest) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X"))
    {
        (16, rest)
    } else if let Some(rest) = s.strip_prefix("0b").or_else(|| s.strip_prefix("0B")) {
        (2, rest)
    } else if let Some(rest) = s.strip_prefix("0o").or_else(|| s.strip_prefix("0O")) {
        (8, rest)
    } else {
        (10, s)
    };
    clean_kernel::BigNat::from_radix_str(digits, radix)
}

/// Convert macro syntax back to a surface expression
///
/// This is used after macro expansion to continue with elaboration.
/// Returns None if the syntax cannot be converted.
pub fn syntax_to_surface(syntax: &Syntax) -> Option<SurfaceExpr> {
    stack_safe(|| match syntax {
        Syntax::Ident(_, name) => match name.as_str() {
            "Type" => Some(SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Type)),
            "Prop" => Some(SurfaceExpr::Universe(Span::dummy(), UniverseExpr::Prop)),
            _ => Some(SurfaceExpr::Ident(Span::dummy(), name.clone())),
        },

        Syntax::Atom(_, value) => {
            // Try to parse as number
            if let Ok(n) = value.parse::<u64>() {
                Some(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(n)))
            } else if !value.is_empty() && value.bytes().all(|b| b.is_ascii_digit()) {
                // Decimal literal too large for a u64: keep the exact value.
                match parse_nat_atom(value) {
                    Some(big) => Some(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::nat(big))),
                    None => Some(SurfaceExpr::Lit(
                        Span::dummy(),
                        SurfaceLit::String(value.clone()),
                    )),
                }
            } else {
                Some(SurfaceExpr::Lit(
                    Span::dummy(),
                    SurfaceLit::String(value.clone()),
                ))
            }
        }

        Syntax::Missing(_) => Some(SurfaceExpr::Hole(Span::dummy())),

        Syntax::Node(node) => {
            let kind_name = node.kind.name_str();

            match kind_name {
                "app" => {
                    if node.children.is_empty() {
                        return None;
                    }
                    let func = syntax_to_surface(&node.children[0])?;
                    let args: Option<Vec<_>> =
                        node.children[1..].iter().map(syntax_to_arg).collect();
                    Some(SurfaceExpr::App(Span::dummy(), Box::new(func), args?))
                }

                "fun" | "lambda" => {
                    if node.children.is_empty() {
                        return None;
                    }
                    let body_idx = node.children.len() - 1;
                    let binders: Option<Vec<_>> = node.children[..body_idx]
                        .iter()
                        .map(syntax_to_binder)
                        .collect();
                    let body = syntax_to_surface(&node.children[body_idx])?;
                    Some(SurfaceExpr::Lambda(Span::dummy(), binders?, Box::new(body)))
                }

                "forall" | "Pi" => {
                    if node.children.is_empty() {
                        return None;
                    }
                    let body_idx = node.children.len() - 1;
                    let binders: Option<Vec<_>> = node.children[..body_idx]
                        .iter()
                        .map(syntax_to_binder)
                        .collect();
                    let body = syntax_to_surface(&node.children[body_idx])?;
                    Some(SurfaceExpr::Pi(Span::dummy(), binders?, Box::new(body)))
                }

                "arrow" => {
                    if node.children.len() != 2 {
                        return None;
                    }
                    let from = syntax_to_surface(&node.children[0])?;
                    let to = syntax_to_surface(&node.children[1])?;
                    Some(SurfaceExpr::Arrow(
                        Span::dummy(),
                        Box::new(from),
                        Box::new(to),
                    ))
                }

                "let" => {
                    if node.children.len() < 3 {
                        return None;
                    }
                    let name = node.children[0].as_ident()?.to_string();
                    let (ty, val_idx) = if node.children.len() == 4 {
                        (Some(Box::new(syntax_to_surface(&node.children[1])?)), 2)
                    } else {
                        (None, 1)
                    };
                    let val = syntax_to_surface(&node.children[val_idx])?;
                    let body = syntax_to_surface(&node.children[val_idx + 1])?;
                    Some(SurfaceExpr::Let(
                        Span::dummy(),
                        SurfaceBinder {
                            span: Span::dummy(),
                            name,
                            ty,
                            default: None,
                            info: SurfaceBinderInfo::Explicit,
                        },
                        Box::new(val),
                        Box::new(body),
                    ))
                }

                "letRec" => {
                    if node.children.len() < 3 {
                        return None;
                    }
                    let name = node.children[0].as_ident()?.to_string();
                    let (ty, val_idx) = if node.children.len() == 4 {
                        (Some(Box::new(syntax_to_surface(&node.children[1])?)), 2)
                    } else {
                        (None, 1)
                    };
                    let val = syntax_to_surface(&node.children[val_idx])?;
                    let body = syntax_to_surface(&node.children[val_idx + 1])?;
                    Some(SurfaceExpr::LetRec(
                        Span::dummy(),
                        SurfaceBinder {
                            span: Span::dummy(),
                            name,
                            ty,
                            default: None,
                            info: SurfaceBinderInfo::Explicit,
                        },
                        Box::new(val),
                        Box::new(body),
                    ))
                }

                "num" => {
                    let value = parse_nat_atom(node.children.first()?.as_atom()?)?;
                    Some(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::nat(value)))
                }

                "str" => {
                    let value = node.children.first()?.as_atom()?.to_string();
                    Some(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::String(value)))
                }

                "scientific" => {
                    // Float literal: the atom carries the exact source text.
                    let text = node.children.first()?.as_atom()?.to_string();
                    Some(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Float(text)))
                }

                "char" => {
                    // Char literal: the atom is the single scalar value rendered
                    // as text; require exactly one `char`.
                    let atom = node.children.first()?.as_atom()?;
                    let mut chars = atom.chars();
                    let c = chars.next()?;
                    if chars.next().is_some() {
                        return None;
                    }
                    Some(SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Char(c)))
                }

                "paren" => {
                    let inner = syntax_to_surface(node.children.first()?)?;
                    Some(SurfaceExpr::Paren(Span::dummy(), Box::new(inner)))
                }

                // Recover the hole's source span preserved through the macro
                // roundtrip (see `to_syntax`'s `mk_hole_with_info`). A dummy
                // `(0, 0)` info means the span was never recorded.
                "hole" => {
                    let info = &node.info;
                    let span = if info.start == 0 && info.end == 0 {
                        Span::dummy()
                    } else {
                        Span::new(info.start, info.end)
                    };
                    Some(SurfaceExpr::Hole(span))
                }

                "syntheticSorry" => Some(SurfaceExpr::SyntheticSorry(Span::dummy())),

                "universe" => {
                    let tag = node.children.first()?.as_ident()?;
                    let univ = match tag {
                        "Prop" => UniverseExpr::Prop,
                        "Type" => UniverseExpr::Type,
                        "TypeLevel" => UniverseExpr::TypeLevel(Box::new(syntax_to_level(
                            node.children.get(1)?,
                        )?)),
                        "TypeImplicit" => UniverseExpr::TypeImplicit,
                        "Sort" => {
                            UniverseExpr::Sort(Box::new(syntax_to_level(node.children.get(1)?)?))
                        }
                        "SortImplicit" => UniverseExpr::SortImplicit,
                        "SortStar" => UniverseExpr::SortStar,
                        _ => return None,
                    };
                    Some(SurfaceExpr::Universe(Span::dummy(), univ))
                }

                "ifThenElse" => {
                    if node.children.len() != 3 {
                        return None;
                    }
                    let cond = syntax_to_surface(&node.children[0])?;
                    let then_br = syntax_to_surface(&node.children[1])?;
                    let else_br = syntax_to_surface(&node.children[2])?;
                    Some(SurfaceExpr::If(
                        Span::dummy(),
                        Box::new(cond),
                        Box::new(then_br),
                        Box::new(else_br),
                    ))
                }

                "ascription" => {
                    if node.children.len() != 2 {
                        return None;
                    }
                    let expr = syntax_to_surface(&node.children[0])?;
                    let ty = syntax_to_surface(&node.children[1])?;
                    Some(SurfaceExpr::Ascription(
                        Span::dummy(),
                        Box::new(expr),
                        Box::new(ty),
                    ))
                }

                "explicit" => {
                    let inner = syntax_to_surface(node.children.first()?)?;
                    Some(SurfaceExpr::Explicit(Span::dummy(), Box::new(inner)))
                }

                "namedArg" => {
                    if node.children.len() != 2 {
                        return None;
                    }
                    let name = node.children[0].as_ident()?.to_string();
                    let expr = syntax_to_surface(&node.children[1])?;
                    Some(SurfaceExpr::NamedArg(Span::dummy(), name, Box::new(expr)))
                }

                "outParam" => {
                    let inner = syntax_to_surface(node.children.first()?)?;
                    Some(SurfaceExpr::OutParam(Span::dummy(), Box::new(inner)))
                }

                "semiOutParam" => {
                    let inner = syntax_to_surface(node.children.first()?)?;
                    Some(SurfaceExpr::SemiOutParam(Span::dummy(), Box::new(inner)))
                }

                "universeInst" => {
                    // Universe instantiation: first child is expression, rest are levels
                    if node.children.is_empty() {
                        return None;
                    }
                    let expr = syntax_to_surface(&node.children[0])?;
                    let levels: Option<Vec<_>> =
                        node.children[1..].iter().map(syntax_to_level).collect();
                    Some(SurfaceExpr::UniverseInst(
                        Span::dummy(),
                        Box::new(expr),
                        levels?,
                    ))
                }

                "patternMatchLambda" => {
                    // Pattern match lambda: binders then body (last child)
                    if node.children.is_empty() {
                        return None;
                    }
                    let body_idx = node.children.len() - 1;
                    let binders: Option<Vec<_>> = node.children[..body_idx]
                        .iter()
                        .map(syntax_to_binder)
                        .collect();
                    let body = syntax_to_surface(&node.children[body_idx])?;
                    Some(SurfaceExpr::PatternMatchLambda(
                        Span::dummy(),
                        binders?,
                        Box::new(body),
                    ))
                }

                "projection" => {
                    if node.children.len() != 2 {
                        return None;
                    }
                    let expr = syntax_to_surface(&node.children[0])?;
                    let proj = if let Some(name) = node.children[1].as_ident() {
                        Projection::Named(name.to_string())
                    } else {
                        let idx_str = node.children[1].as_atom()?;
                        Projection::Index(idx_str.parse().ok()?)
                    };
                    Some(SurfaceExpr::Proj(Span::dummy(), Box::new(expr), proj))
                }

                "match" => {
                    if node.children.is_empty() {
                        return None;
                    }
                    // Optional leading `matchDiscrHyp` node: the annotated
                    // discriminant's hypothesis name (`match h : e with`),
                    // as emitted by `surface_to_syntax`.
                    let (hyp, rest) = match &node.children[0] {
                        Syntax::Node(hyp_node) if hyp_node.kind.name_str() == "matchDiscrHyp" => {
                            match hyp_node.children.first() {
                                Some(Syntax::Ident(_, h)) => (Some(h.clone()), &node.children[1..]),
                                _ => return None,
                            }
                        }
                        _ => (None, &node.children[..]),
                    };
                    if rest.is_empty() {
                        return None;
                    }
                    let scrutinee = syntax_to_surface(&rest[0])?;
                    let arms: Option<Vec<_>> = rest[1..].iter().map(syntax_to_match_arm).collect();
                    Some(SurfaceExpr::Match(
                        Span::dummy(),
                        hyp,
                        Box::new(scrutinee),
                        arms?,
                    ))
                }

                "ifLet" => {
                    // if let pat := scrutinee then then_br else else_br
                    if node.children.len() != 4 {
                        return None;
                    }
                    let pat = syntax_to_pattern(&node.children[0])?;
                    let scrutinee = syntax_to_surface(&node.children[1])?;
                    let then_br = syntax_to_surface(&node.children[2])?;
                    let else_br = syntax_to_surface(&node.children[3])?;
                    Some(SurfaceExpr::IfLet(
                        Span::dummy(),
                        pat,
                        Box::new(scrutinee),
                        Box::new(then_br),
                        Box::new(else_br),
                    ))
                }

                "ifDecidable" => {
                    // if h : p then t else e
                    if node.children.len() != 4 {
                        return None;
                    }
                    let witness_name = node.children[0].as_ident()?.to_string();
                    let prop = syntax_to_surface(&node.children[1])?;
                    let then_br = syntax_to_surface(&node.children[2])?;
                    let else_br = syntax_to_surface(&node.children[3])?;
                    Some(SurfaceExpr::IfDecidable(
                        Span::dummy(),
                        witness_name,
                        Box::new(prop),
                        Box::new(then_br),
                        Box::new(else_br),
                    ))
                }

                "letPattern" => {
                    // let q($pat) := scrutinee | fallback in body
                    // Part of #23: Qq Phase 4 - let-pattern support
                    // Part of #751: Non-q-pattern let-pattern elaboration
                    if node.children.len() != 4 {
                        return None;
                    }
                    let pattern = syntax_to_pattern(&node.children[0])?;
                    let scrutinee = syntax_to_surface(&node.children[1])?;
                    let fallback = syntax_to_surface(&node.children[2])?;
                    let body = syntax_to_surface(&node.children[3])?;
                    Some(SurfaceExpr::LetPattern(
                        Span::dummy(),
                        pattern,
                        Box::new(scrutinee),
                        Box::new(fallback),
                        Box::new(body),
                    ))
                }

                // Qq quotations - Part of #16
                "QQuotation" => {
                    // Children: [kind_tag, inner, optional_type_annot]
                    if node.children.is_empty() {
                        return None;
                    }
                    let kind_tag = node.children[0].as_ident()?;
                    let kind = match kind_tag {
                        "Q" => QQuotationKind::Type,
                        "q" => QQuotationKind::Value,
                        _ => return None,
                    };
                    let inner = syntax_to_surface(node.children.get(1)?)?;
                    let type_annot = if node.children.len() > 2 {
                        Some(Box::new(syntax_to_surface(&node.children[2])?))
                    } else {
                        None
                    };
                    Some(SurfaceExpr::QQuotation {
                        span: Span::dummy(),
                        kind,
                        inner: Box::new(inner),
                        type_annot,
                    })
                }

                // Antiquotations - Part of #16
                "antiquot" => {
                    // Simple antiquotation: $x
                    let name = node.children.first()?.as_ident()?.to_string();
                    Some(SurfaceExpr::QAntiquot {
                        span: Span::dummy(),
                        content: QAntiquotContent::Simple(name),
                    })
                }

                "antiquotExpr" => {
                    // Expression antiquotation: $(e)
                    let inner = syntax_to_surface(node.children.first()?)?;
                    Some(SurfaceExpr::QAntiquot {
                        span: Span::dummy(),
                        content: QAntiquotContent::Expr(Box::new(inner)),
                    })
                }

                "antiquotTyped" => {
                    // Typed antiquotation: $(x : τ)
                    if node.children.len() < 2 {
                        return None;
                    }
                    let name = node.children[0].as_ident()?.to_string();
                    let ty = syntax_to_surface(&node.children[1])?;
                    Some(SurfaceExpr::QAntiquot {
                        span: Span::dummy(),
                        content: QAntiquotContent::Typed {
                            name,
                            ty: Box::new(ty),
                        },
                    })
                }

                "antiquotSplice" => {
                    // Splice antiquotation: $[xs]* or $[xs]+
                    // Children: name, separator (some/none), at_least_one (true/false)
                    if node.children.len() < 3 {
                        return None;
                    }
                    let name = node.children[0].as_ident()?.to_string();

                    // Parse separator: either "none" ident or "some" node with string child
                    let separator = match &node.children[1] {
                        Syntax::Ident(_, s) if s == "none" => None,
                        Syntax::Node(sep_node)
                            if sep_node.kind.name_str() == "some"
                                && !sep_node.children.is_empty() =>
                        {
                            sep_node.children[0].as_atom().map(|s| s.to_string())
                        }
                        _ => None,
                    };

                    // Parse at_least_one flag
                    let at_least_one = match &node.children[2] {
                        Syntax::Ident(_, s) => s == "true",
                        _ => false,
                    };

                    Some(SurfaceExpr::QAntiquot {
                        span: Span::dummy(),
                        content: QAntiquotContent::Splice {
                            name,
                            separator,
                            at_least_one,
                        },
                    })
                }

                // Macros that expand to standard forms
                "showMacro" | "haveMacro" | "letMacro" => {
                    // These should have been expanded by the macro system
                    // If we see them here, return None to signal need for expansion
                    None
                }

                // Opaque nodes: children (tactics/calc steps) are lost in
                // to_syntax (encoded with empty children). Return the correct
                // variant with empty content to preserve the node type identity
                // during round-trips, rather than returning None which breaks
                // the entire conversion chain. Part of #2060.
                "byTactic" => Some(SurfaceExpr::ByTactic(Span::dummy(), vec![])),
                "calcBlock" => Some(SurfaceExpr::CalcBlock(Span::dummy(), vec![])),

                // Do notation (structured): round-trips through surface_to_syntax
                // SyntaxKind::do_notation() = app("do")
                "do" => {
                    let elems: Option<Vec<_>> =
                        node.children.iter().map(syntax_to_do_elem).collect();
                    Some(SurfaceExpr::Do(Span::dummy(), elems?))
                }

                // Structure literal: { x := val, y := val2 }
                // or with base: { s with x := val }
                // Children are structField, structType, or structBase nodes
                "structLit" => {
                    let mut struct_type = None;
                    let mut base = None;
                    let mut fields = Vec::new();

                    for child in &node.children {
                        if let Syntax::Node(field_node) = child {
                            let field_kind = field_node.kind.name_str();
                            if field_kind == "structType" {
                                // Explicit type annotation: { ... : Foo }
                                struct_type = Some(Box::new(syntax_to_surface(
                                    field_node.children.first()?,
                                )?));
                            } else if field_kind == "structBase" {
                                // Base expression for "with" syntax: { s with ... }
                                base = Some(Box::new(syntax_to_surface(
                                    field_node.children.first()?,
                                )?));
                            } else if field_kind == "structField" {
                                // Field assignment: x := val
                                // Require exactly 2 children (name and value)
                                if field_node.children.len() < 2 {
                                    return None; // Malformed field - signal error
                                }
                                let name = field_node.children[0].as_ident()?.to_string();
                                let val = syntax_to_surface(&field_node.children[1])?;
                                fields.push(SurfaceFieldAssign {
                                    span: Span::dummy(),
                                    name,
                                    val,
                                });
                            }
                        }
                    }

                    Some(SurfaceExpr::StructLit {
                        span: Span::dummy(),
                        struct_type,
                        base,
                        fields,
                    })
                }

                "liftMethod" => {
                    // Nested action lift: <- expr
                    let inner = syntax_to_surface(node.children.first()?)?;
                    Some(SurfaceExpr::LiftMethod(Span::dummy(), Box::new(inner)))
                }

                _ => {
                    // Unknown node type - try to convert as application if it has children
                    if node.children.is_empty() {
                        Some(SurfaceExpr::Ident(Span::dummy(), kind_name.to_string()))
                    } else {
                        let func = Syntax::ident(kind_name);
                        let func_expr = syntax_to_surface(&func)?;
                        let args: Option<Vec<_>> =
                            node.children.iter().map(syntax_to_arg).collect();
                        Some(SurfaceExpr::App(Span::dummy(), Box::new(func_expr), args?))
                    }
                }
            }
        }
    })
}
