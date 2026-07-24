// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conversion from `SurfaceExpr` to macro `Syntax`.
//!
//! This is the forward direction: surface expressions are converted to the
//! generic `Syntax` AST that the macro system operates on.

use crate::stack_safe;
use clean_macro::quotation::parse_quotation;
use clean_macro::{Syntax, SyntaxKind};
use clean_parser::{
    Projection, QAntiquotContent, QQuotationKind, SurfaceExpr, SurfaceLit, UniverseExpr,
};

use super::level_to_syntax;
pub(super) use super::to_syntax_helpers::surface_pattern_to_syntax;
use super::to_syntax_helpers::{
    do_elem_to_syntax, surface_arg_to_syntax, surface_binder_to_syntax,
};

/// Convert a surface expression to macro syntax
pub fn surface_to_syntax(expr: &SurfaceExpr) -> Syntax {
    stack_safe(|| match expr {
        SurfaceExpr::Ident(_, name) => Syntax::ident(name),

        SurfaceExpr::SyntheticSorry(_) => {
            Syntax::node(SyntaxKind::app("syntheticSorry"), Vec::new())
        }

        SurfaceExpr::Universe(_, univ) => {
            let mut children = Vec::new();
            let tag = match univ {
                UniverseExpr::Prop => "Prop",
                UniverseExpr::Type => "Type",
                UniverseExpr::TypeLevel(level) => {
                    children.push(level_to_syntax(level));
                    "TypeLevel"
                }
                UniverseExpr::TypeImplicit => "TypeImplicit",
                UniverseExpr::Sort(level) => {
                    children.push(level_to_syntax(level));
                    "Sort"
                }
                UniverseExpr::SortImplicit => "SortImplicit",
                UniverseExpr::SortStar => "SortStar",
            };
            let mut all_children = Vec::with_capacity(1 + children.len());
            all_children.push(Syntax::ident(tag));
            all_children.extend(children);
            Syntax::node(SyntaxKind::app("universe"), all_children)
        }

        SurfaceExpr::App(_, func, args) => {
            let func_syn = surface_to_syntax(func);
            let args_syn: Vec<_> = args.iter().map(surface_arg_to_syntax).collect();
            Syntax::mk_app(func_syn, args_syn)
        }

        SurfaceExpr::Lambda(_, binders, body) => {
            let binders_syn: Vec<_> = binders.iter().map(surface_binder_to_syntax).collect();
            let body_syn = surface_to_syntax(body);
            Syntax::mk_lambda(binders_syn, body_syn)
        }

        SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            // Pattern match lambda - distinct node kind to preserve round-trip
            let mut children: Vec<_> = binders.iter().map(surface_binder_to_syntax).collect();
            children.push(surface_to_syntax(body));
            Syntax::node(SyntaxKind::app("patternMatchLambda"), children)
        }

        SurfaceExpr::Pi(_, binders, body) => {
            let binders_syn: Vec<_> = binders.iter().map(surface_binder_to_syntax).collect();
            let body_syn = surface_to_syntax(body);
            Syntax::mk_forall(binders_syn, body_syn)
        }

        SurfaceExpr::Arrow(_, from, to) => {
            let from_syn = surface_to_syntax(from);
            let to_syn = surface_to_syntax(to);
            Syntax::mk_arrow(from_syn, to_syn)
        }

        SurfaceExpr::Let(_, binder, val, body) => {
            let name_syn = Syntax::ident(&binder.name);
            let ty_syn = binder.ty.as_ref().map(|t| surface_to_syntax(t));
            let val_syn = surface_to_syntax(val);
            let body_syn = surface_to_syntax(body);
            Syntax::mk_let(name_syn, ty_syn, val_syn, body_syn)
        }

        SurfaceExpr::Lit(_, lit) => match lit {
            SurfaceLit::Nat(n) => Syntax::mk_num(*n),
            SurfaceLit::BigNat(n) => Syntax::mk_num_str(&n.to_string()),
            SurfaceLit::String(s) => Syntax::mk_str(s),
            SurfaceLit::Float(s) => Syntax::mk_scientific(s),
            SurfaceLit::Char(c) => Syntax::mk_char(*c),
        },

        SurfaceExpr::Paren(_, inner) => Syntax::mk_paren(surface_to_syntax(inner)),

        // Preserve the hole's source span through the macro roundtrip so IDE
        // surfaces can recover the `_` position after expansion (the span would
        // otherwise be reset to a dummy `(0, 0)` by `syntax_to_surface`).
        SurfaceExpr::Hole(span) => {
            Syntax::mk_hole_with_info(clean_macro::SourceInfo::new(span.start, span.end))
        }

        // The macro `Syntax` hole node carries no name, so a `?name` degrades to
        // an anonymous hole across a macro roundtrip. This is only reachable for
        // named holes that flow *through* macro expansion; `refine`'s named-hole
        // path intercepts `NamedHole` in `elaborate()` before expansion, so its
        // goal tag is never lost. Degrading to an anonymous hole here is sound —
        // the goal is still created and must be closed.
        SurfaceExpr::NamedHole(span, _) => {
            Syntax::mk_hole_with_info(clean_macro::SourceInfo::new(span.start, span.end))
        }

        SurfaceExpr::Ascription(_, expr, ty) => {
            let expr_syn = surface_to_syntax(expr);
            let ty_syn = surface_to_syntax(ty);
            Syntax::node(SyntaxKind::app("ascription"), vec![expr_syn, ty_syn])
        }

        SurfaceExpr::OutParam(_, inner) => {
            let inner_syn = surface_to_syntax(inner);
            Syntax::node(SyntaxKind::app("outParam"), vec![inner_syn])
        }

        SurfaceExpr::SemiOutParam(_, inner) => {
            let inner_syn = surface_to_syntax(inner);
            Syntax::node(SyntaxKind::app("semiOutParam"), vec![inner_syn])
        }

        SurfaceExpr::If(_, cond, then_br, else_br) => {
            let cond_syn = surface_to_syntax(cond);
            let then_syn = surface_to_syntax(then_br);
            let else_syn = surface_to_syntax(else_br);
            Syntax::node(
                SyntaxKind::if_then_else(),
                vec![cond_syn, then_syn, else_syn],
            )
        }

        SurfaceExpr::Match(_, hyp, scrutinee, arms) => {
            let scrutinee_syn = surface_to_syntax(scrutinee);
            let mut children = Vec::with_capacity(arms.len() + 2);
            // Annotated discriminant (`match h : e with`): encode the
            // hypothesis name as a dedicated leading node so the macro-syntax
            // round-trip preserves it — dropping it here would silently turn
            // a dependent match into a plain one.
            if let Some(h) = hyp {
                children.push(Syntax::node(
                    SyntaxKind::app("matchDiscrHyp"),
                    vec![Syntax::ident(h)],
                ));
            }
            children.push(scrutinee_syn);
            for arm in arms {
                children.push(Syntax::node(
                    SyntaxKind::match_arm(),
                    vec![
                        surface_pattern_to_syntax(&arm.pattern),
                        surface_to_syntax(&arm.body),
                    ],
                ));
            }
            Syntax::node(SyntaxKind::match_expr(), children)
        }

        SurfaceExpr::Proj(_, expr, proj) => {
            let expr_syn = surface_to_syntax(expr);
            let field_syn = match proj {
                Projection::Named(name) => Syntax::ident(name),
                Projection::Index(idx) => Syntax::atom(&idx.to_string()),
            };
            Syntax::node(SyntaxKind::app("projection"), vec![expr_syn, field_syn])
        }

        SurfaceExpr::UniverseInst(_, expr, levels) => {
            // Universe instantiation: encode expression + level arguments
            let mut children = vec![surface_to_syntax(expr)];
            children.extend(levels.iter().map(level_to_syntax));
            Syntax::node(SyntaxKind::app("universeInst"), children)
        }

        SurfaceExpr::NamedArg(_, name, expr) => {
            let name_syn = Syntax::ident(name);
            let expr_syn = surface_to_syntax(expr);
            Syntax::node(SyntaxKind::app("namedArg"), vec![name_syn, expr_syn])
        }

        SurfaceExpr::SyntaxQuote(_, content) => {
            parse_quotation(&format!("`{content}")).map_or_else(|_| Syntax::missing(), |q| q.syntax)
        }

        SurfaceExpr::LetRec(_, binder, val, body) => {
            // Similar to Let, but marked as recursive
            let name_syn = Syntax::ident(&binder.name);
            let ty_syn = binder.ty.as_ref().map(|t| surface_to_syntax(t));
            let val_syn = surface_to_syntax(val);
            let body_syn = surface_to_syntax(body);
            // For now, use the same let representation with a "rec" marker
            Syntax::node(
                SyntaxKind::app("letRec"),
                if let Some(ty) = ty_syn {
                    vec![name_syn, ty, val_syn, body_syn]
                } else {
                    vec![name_syn, val_syn, body_syn]
                },
            )
        }

        SurfaceExpr::IfLet(_, pat, scrutinee, then_br, else_br) => {
            let pat_syn = surface_pattern_to_syntax(pat);
            let scrutinee_syn = surface_to_syntax(scrutinee);
            let then_syn = surface_to_syntax(then_br);
            let else_syn = surface_to_syntax(else_br);
            Syntax::node(
                SyntaxKind::app("ifLet"),
                vec![pat_syn, scrutinee_syn, then_syn, else_syn],
            )
        }

        SurfaceExpr::IfDecidable(_, witness_name, prop, then_br, else_br) => {
            let witness_syn = Syntax::ident(witness_name);
            let prop_syn = surface_to_syntax(prop);
            let then_syn = surface_to_syntax(then_br);
            let else_syn = surface_to_syntax(else_br);
            Syntax::node(
                SyntaxKind::app("ifDecidable"),
                vec![witness_syn, prop_syn, then_syn, else_syn],
            )
        }

        SurfaceExpr::Explicit(_, inner) => {
            // Explicit application marker: @f
            // Wrap the inner syntax in an "explicit" node
            let inner_syn = surface_to_syntax(inner);
            Syntax::node(SyntaxKind::app("explicit"), vec![inner_syn])
        }

        SurfaceExpr::QQuotation {
            kind,
            inner,
            type_annot,
            ..
        } => {
            // Qq quotation: Q(α) or q(e)
            let kind_tag = match kind {
                QQuotationKind::Type => "Q",
                QQuotationKind::Value => "q",
            };
            let inner_syn = surface_to_syntax(inner);
            let mut children = vec![Syntax::ident(kind_tag), inner_syn];
            if let Some(annot) = type_annot {
                children.push(surface_to_syntax(annot));
            }
            Syntax::node(SyntaxKind::app("QQuotation"), children)
        }

        SurfaceExpr::QAntiquot { content, .. } => {
            // Antiquotation: $x, $(e), $(x : τ), $[xs]*
            match content {
                QAntiquotContent::Simple(name) => {
                    Syntax::node(SyntaxKind::app("antiquot"), vec![Syntax::ident(name)])
                }
                QAntiquotContent::Expr(inner) => {
                    let inner_syn = surface_to_syntax(inner);
                    Syntax::node(SyntaxKind::app("antiquotExpr"), vec![inner_syn])
                }
                QAntiquotContent::Typed { name, ty } => {
                    let ty_syn = surface_to_syntax(ty);
                    Syntax::node(
                        SyntaxKind::app("antiquotTyped"),
                        vec![Syntax::ident(name), ty_syn],
                    )
                }
                QAntiquotContent::Splice {
                    name,
                    separator,
                    at_least_one,
                } => {
                    // Splice antiquotation: $[xs]* or $[xs]+
                    let sep_node = separator.as_ref().map_or_else(
                        || Syntax::ident("none"),
                        |s| Syntax::node(SyntaxKind::app("some"), vec![Syntax::atom(s)]),
                    );
                    let one_node = if *at_least_one {
                        Syntax::ident("true")
                    } else {
                        Syntax::ident("false")
                    };
                    Syntax::node(
                        SyntaxKind::app("antiquotSplice"),
                        vec![Syntax::ident(name), sep_node, one_node],
                    )
                }
            }
        }

        SurfaceExpr::LetPattern(_, pattern, scrutinee, fallback, body) => {
            // Let pattern: let q($pat) := scrutinee | fallback in body
            // Part of #23: Qq Phase 4 - let-pattern support
            let pat_syn = surface_pattern_to_syntax(pattern);
            let scrutinee_syn = surface_to_syntax(scrutinee);
            let fallback_syn = surface_to_syntax(fallback);
            let body_syn = surface_to_syntax(body);
            Syntax::node(
                SyntaxKind::app("letPattern"),
                vec![pat_syn, scrutinee_syn, fallback_syn, body_syn],
            )
        }

        SurfaceExpr::StructLit {
            struct_type,
            base,
            fields,
            ..
        } => {
            // Structure literal: { x := val, y := val2 }
            // or with base: { s with x := val }
            // or with type annotation: ({ x := val } : T)
            let mut children = Vec::new();

            // Add type annotation if present
            if let Some(ty) = struct_type {
                children.push(Syntax::node(
                    SyntaxKind::app("structType"),
                    vec![surface_to_syntax(ty)],
                ));
            }

            // Add base expression if present (for "with" syntax)
            if let Some(b) = base {
                children.push(Syntax::node(
                    SyntaxKind::app("structBase"),
                    vec![surface_to_syntax(b)],
                ));
            }

            // Add field assignments
            for field in fields {
                children.push(Syntax::node(
                    SyntaxKind::app("structField"),
                    vec![Syntax::ident(&field.name), surface_to_syntax(&field.val)],
                ));
            }

            Syntax::node(SyntaxKind::app("structLit"), children)
        }

        SurfaceExpr::Do(_, elems) => {
            // Do notation: convert each element to a child syntax node
            let children: Vec<_> = elems.iter().map(do_elem_to_syntax).collect();
            Syntax::node(SyntaxKind::do_notation(), children)
        }

        SurfaceExpr::ByTactic(_, _tactics) => {
            // By-tactic blocks: preserve as opaque node for macro system
            Syntax::node(SyntaxKind::app("byTactic"), vec![])
        }

        SurfaceExpr::CalcBlock(_, _steps) => {
            // Calc blocks: preserve as opaque node for macro system
            Syntax::node(SyntaxKind::app("calcBlock"), vec![])
        }

        SurfaceExpr::LiftMethod(_, inner) => {
            // Nested action lift: <- expr
            // Preserve as opaque node; the elaborator pre-pass handles desugaring
            let inner_syn = surface_to_syntax(inner);
            Syntax::node(SyntaxKind::app("liftMethod"), vec![inner_syn])
        }

        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            // Interpolated string: desugar to function application chain for macro syntax
            let desugared =
                clean_parser::interpolation::desugar_prefixed_interpolation_parts(*kind, parts);
            surface_to_syntax(&desugared)
        }

        SurfaceExpr::OpenIn { body, .. } => {
            // `open X in <term>`: preserve as an opaque wrapper around the
            // sub-term's syntax. The opened namespaces affect elaboration-time
            // name resolution only and carry no meaning for macro-pattern
            // matching, so the body syntax is what the macro system sees.
            let body_syn = surface_to_syntax(body);
            Syntax::node(SyntaxKind::app("openIn"), vec![body_syn])
        }
    })
}
