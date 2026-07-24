// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Helper converters used by `surface_to_syntax`.

use clean_macro::{Syntax, SyntaxKind};
use clean_parser::{
    DoElem, DoLetExprKind, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceLit, SurfacePattern,
};

use super::to_syntax::surface_to_syntax;

/// Convert a do-element to a syntax node for macro processing.
pub(super) fn do_elem_to_syntax(elem: &DoElem) -> Syntax {
    match elem {
        DoElem::Bind(_, binder, action) => Syntax::node(
            SyntaxKind::do_bind(),
            vec![Syntax::ident(&binder.name), surface_to_syntax(action)],
        ),
        DoElem::Let(_, binder, val) => Syntax::node(
            SyntaxKind::do_let(),
            vec![Syntax::ident(&binder.name), surface_to_syntax(val)],
        ),
        DoElem::LetMut(_, binder, val) => Syntax::node(
            SyntaxKind::app("doLetMut"),
            vec![Syntax::ident(&binder.name), surface_to_syntax(val)],
        ),
        DoElem::LetRec(_, decls) => {
            let children: Vec<_> = decls
                .iter()
                .flat_map(|(binder, val)| vec![Syntax::ident(&binder.name), surface_to_syntax(val)])
                .collect();
            Syntax::node(SyntaxKind::app("doLetRec"), children)
        }
        DoElem::Return(_, expr) => {
            Syntax::node(SyntaxKind::do_return(), vec![surface_to_syntax(expr)])
        }
        DoElem::Expr(_, expr) => Syntax::node(SyntaxKind::do_elem(), vec![surface_to_syntax(expr)]),
        DoElem::If(_, cond, then_elems, else_elems) => {
            let mut children = vec![surface_to_syntax(cond)];
            let then_children: Vec<_> = then_elems.iter().map(do_elem_to_syntax).collect();
            children.push(Syntax::node(SyntaxKind::app("doSeq"), then_children));
            if let Some(else_elems) = else_elems {
                let else_children: Vec<_> = else_elems.iter().map(do_elem_to_syntax).collect();
                children.push(Syntax::node(SyntaxKind::app("doSeq"), else_children));
            }
            Syntax::node(SyntaxKind::app("doIf"), children)
        }
        DoElem::IfLet(_, pat, scrutinee, then_elems, else_elems) => {
            let mut children = vec![surface_pattern_to_syntax(pat), surface_to_syntax(scrutinee)];
            let then_children: Vec<_> = then_elems.iter().map(do_elem_to_syntax).collect();
            children.push(Syntax::node(SyntaxKind::app("doSeq"), then_children));
            if let Some(else_elems) = else_elems {
                let else_children: Vec<_> = else_elems.iter().map(do_elem_to_syntax).collect();
                children.push(Syntax::node(SyntaxKind::app("doSeq"), else_children));
            }
            Syntax::node(SyntaxKind::app("doIfLet"), children)
        }
        DoElem::IfDecidable(_, witness, prop, then_elems, else_elems) => {
            let mut children = vec![Syntax::ident(witness), surface_to_syntax(prop)];
            let then_children: Vec<_> = then_elems.iter().map(do_elem_to_syntax).collect();
            children.push(Syntax::node(SyntaxKind::app("doSeq"), then_children));
            if let Some(else_elems) = else_elems {
                let else_children: Vec<_> = else_elems.iter().map(do_elem_to_syntax).collect();
                children.push(Syntax::node(SyntaxKind::app("doSeq"), else_children));
            }
            Syntax::node(SyntaxKind::app("doIfDecidable"), children)
        }
        DoElem::For(_, binder, collection, body_elems) => {
            let body_children: Vec<_> = body_elems.iter().map(do_elem_to_syntax).collect();
            Syntax::node(
                SyntaxKind::app("doFor"),
                vec![
                    Syntax::ident(&binder.name),
                    surface_to_syntax(collection),
                    Syntax::node(SyntaxKind::app("doSeq"), body_children),
                ],
            )
        }
        DoElem::Match(_, discrs, arms) => {
            let mut children: Vec<_> = discrs.iter().map(surface_to_syntax).collect();
            for arm in arms {
                let pats: Vec<_> = arm.patterns.iter().map(surface_pattern_to_syntax).collect();
                let body_children: Vec<_> = arm.body.iter().map(do_elem_to_syntax).collect();
                children.push(Syntax::node(
                    SyntaxKind::app("doMatchArm"),
                    vec![
                        Syntax::node(SyntaxKind::app("patterns"), pats),
                        Syntax::node(SyntaxKind::app("doSeq"), body_children),
                    ],
                ));
            }
            Syntax::node(SyntaxKind::app("doMatch"), children)
        }
        DoElem::TryCatch(_, try_body, catches, finally_body) => {
            let mut children = Vec::new();
            let try_children: Vec<_> = try_body.iter().map(do_elem_to_syntax).collect();
            children.push(Syntax::node(SyntaxKind::app("doSeq"), try_children));
            for catch in catches {
                let mut catch_children = vec![Syntax::ident(&catch.binder)];
                if let Some(exc_ty) = &catch.exc_type {
                    catch_children.push(surface_to_syntax(exc_ty));
                }
                let body_children: Vec<_> = catch.body.iter().map(do_elem_to_syntax).collect();
                catch_children.push(Syntax::node(SyntaxKind::app("doSeq"), body_children));
                children.push(Syntax::node(SyntaxKind::app("doCatch"), catch_children));
            }
            if let Some(fin_elems) = finally_body {
                let fin_children: Vec<_> = fin_elems.iter().map(do_elem_to_syntax).collect();
                // Wrap in doSeq for consistency with doCatch body, doRepeat, etc.
                // from_syntax calls syntax_to_do_seq which expects "doSeq" kind.
                children.push(Syntax::node(
                    SyntaxKind::app("doFinally"),
                    vec![Syntax::node(SyntaxKind::app("doSeq"), fin_children)],
                ));
            }
            Syntax::node(SyntaxKind::app("doTry"), children)
        }
        DoElem::LetElse(_, pat, action, fallback) => {
            let fallback_children: Vec<_> = fallback.iter().map(do_elem_to_syntax).collect();
            Syntax::node(
                SyntaxKind::app("doLetElse"),
                vec![
                    surface_pattern_to_syntax(pat),
                    surface_to_syntax(action),
                    Syntax::node(SyntaxKind::app("doSeq"), fallback_children),
                ],
            )
        }
        DoElem::LetExpr(_, pat, discr, kind, fallback) => {
            let fallback_children: Vec<_> = fallback.iter().map(do_elem_to_syntax).collect();
            let kind_name = match kind {
                DoLetExprKind::Pure => "doLetExpr",
                DoLetExprKind::Bind => "doLetExprBind",
            };
            Syntax::node(
                SyntaxKind::app(kind_name),
                vec![
                    surface_pattern_to_syntax(pat),
                    surface_to_syntax(discr),
                    Syntax::node(SyntaxKind::app("doSeq"), fallback_children),
                ],
            )
        }
        DoElem::Repeat(_, body_elems) => {
            let body_children: Vec<_> = body_elems.iter().map(do_elem_to_syntax).collect();
            Syntax::node(
                SyntaxKind::app("doRepeat"),
                vec![Syntax::node(SyntaxKind::app("doSeq"), body_children)],
            )
        }
        DoElem::While(_, cond, body_elems) => {
            let body_children: Vec<_> = body_elems.iter().map(do_elem_to_syntax).collect();
            Syntax::node(
                SyntaxKind::app("doWhile"),
                vec![
                    surface_to_syntax(cond),
                    Syntax::node(SyntaxKind::app("doSeq"), body_children),
                ],
            )
        }
        DoElem::DbgTrace(_, msg) => {
            Syntax::node(SyntaxKind::app("doDbgTrace"), vec![surface_to_syntax(msg)])
        }
        DoElem::Break(_) => Syntax::node(SyntaxKind::app("doBreak"), vec![]),
        DoElem::Continue(_) => Syntax::node(SyntaxKind::app("doContinue"), vec![]),
        DoElem::Reassign(_, name, val) => Syntax::node(
            SyntaxKind::app("doReassign"),
            vec![Syntax::ident(name), surface_to_syntax(val)],
        ),
        DoElem::PatternReassign(_, pat, val) => Syntax::node(
            SyntaxKind::app("doReassignPat"),
            vec![surface_pattern_to_syntax(pat), surface_to_syntax(val)],
        ),
    }
}

/// Convert a surface pattern to syntax.
pub(super) fn surface_pattern_to_syntax(pattern: &SurfacePattern) -> Syntax {
    match pattern {
        SurfacePattern::Wildcard => Syntax::ident("_"),
        // `..` constructor-field ellipsis: render back to the surface token so a
        // syntax round-trip preserves it.
        SurfacePattern::Ellipsis => Syntax::ident(".."),
        SurfacePattern::Inaccessible(inner) => Syntax::node(
            SyntaxKind::app("inaccessiblePattern"),
            vec![surface_to_syntax(inner)],
        ),
        SurfacePattern::Var(name) => Syntax::ident(name),
        SurfacePattern::Ctor(name, args) => {
            let mut children = vec![Syntax::ident(name)];
            children.extend(args.iter().map(surface_pattern_to_syntax));
            Syntax::node(SyntaxKind::app("ctorPattern"), children)
        }
        SurfacePattern::Lit(lit) => match lit {
            SurfaceLit::Nat(n) => Syntax::mk_num(*n),
            SurfaceLit::BigNat(n) => Syntax::mk_num_str(&n.to_string()),
            SurfaceLit::String(s) => Syntax::mk_str(s),
            SurfaceLit::Float(s) => Syntax::mk_scientific(s),
            SurfaceLit::Char(c) => Syntax::mk_char(*c),
        },
        SurfacePattern::NumeralAdd(pat, n) => {
            let pat_syn = surface_pattern_to_syntax(pat);
            let n_syn = Syntax::mk_num(*n);
            Syntax::node(SyntaxKind::app("numeralAddPattern"), vec![pat_syn, n_syn])
        }
        SurfacePattern::As(name, pat) => {
            let name_syn = Syntax::ident(name);
            let pat_syn = surface_pattern_to_syntax(pat);
            Syntax::node(SyntaxKind::app("asPattern"), vec![name_syn, pat_syn])
        }
        SurfacePattern::Or(left, right) => {
            let left_syn = surface_pattern_to_syntax(left);
            let right_syn = surface_pattern_to_syntax(right);
            Syntax::node(SyntaxKind::app("orPattern"), vec![left_syn, right_syn])
        }
        SurfacePattern::QPattern(inner) => {
            let inner_syn = surface_to_syntax(inner);
            Syntax::node(SyntaxKind::app("qPattern"), vec![inner_syn])
        }
    }
}

/// Convert a surface argument to syntax.
pub(super) fn surface_arg_to_syntax(arg: &SurfaceArg) -> Syntax {
    let expr_syn = surface_to_syntax(&arg.expr);
    if let Some(name) = &arg.name {
        Syntax::node(
            SyntaxKind::app("namedArg"),
            vec![Syntax::ident(name), expr_syn],
        )
    } else {
        expr_syn
    }
}

/// Convert a surface binder to syntax.
pub(super) fn surface_binder_to_syntax(binder: &SurfaceBinder) -> Syntax {
    let name = Syntax::ident(&binder.name);
    let ty = binder
        .ty
        .as_ref()
        .map_or_else(Syntax::missing, |t| surface_to_syntax(t));

    let kind_name = match binder.info {
        SurfaceBinderInfo::Explicit => "binderDefault",
        SurfaceBinderInfo::Implicit => "binderImplicit",
        SurfaceBinderInfo::Instance => "binderInstance",
        SurfaceBinderInfo::StrictImplicit => "binderStrictImplicit",
    };

    Syntax::node(SyntaxKind::app(kind_name), vec![name, ty])
}
