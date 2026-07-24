// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Do-notation syntax conversion helpers.
//!
//! Converts macro `Syntax` nodes representing do-notation elements
//! back into `DoElem` surface AST nodes.

use clean_macro::Syntax;
use clean_parser::{
    DoCatchClause, DoElem, DoLetExprKind, DoMatchArm, Span, SurfaceBinder, SurfaceBinderInfo,
    SurfacePattern,
};

use super::syntax_to_pattern;
use super::syntax_to_surface;

/// Convert a syntax node to a do-element for round-tripping through macro expansion
pub(super) fn syntax_to_do_elem(syntax: &Syntax) -> Option<DoElem> {
    let node = match syntax {
        Syntax::Node(n) => n,
        _ => return None,
    };
    let kind_name = node.kind.name_str();
    match kind_name {
        // Kind names must match SyntaxKind builtins: do_bind()="doBind",
        // do_let()="doLet", do_return()="doReturn", do_elem()="doElem".
        // Pre-existing bug: these were snake_case, never caught because
        // Do blocks bypass expand_macros. Fixed as part of #2211.
        "doBind" if node.children.len() == 2 => {
            let name = node.children[0].as_ident()?.to_string();
            let action = syntax_to_surface(&node.children[1])?;
            let binder = SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit);
            Some(DoElem::Bind(Span::dummy(), binder, Box::new(action)))
        }
        "doLet" if node.children.len() == 2 => {
            let name = node.children[0].as_ident()?.to_string();
            let val = syntax_to_surface(&node.children[1])?;
            let binder = SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit);
            Some(DoElem::Let(Span::dummy(), binder, Box::new(val)))
        }
        "doReturn" if node.children.len() == 1 => {
            let expr = syntax_to_surface(&node.children[0])?;
            Some(DoElem::Return(Span::dummy(), Box::new(expr)))
        }
        "doLetMut" if node.children.len() == 2 => {
            let name = node.children[0].as_ident()?.to_string();
            let val = syntax_to_surface(&node.children[1])?;
            let binder = SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit);
            Some(DoElem::LetMut(Span::dummy(), binder, Box::new(val)))
        }
        "doElem" if node.children.len() == 1 => {
            let expr = syntax_to_surface(&node.children[0])?;
            Some(DoElem::Expr(Span::dummy(), Box::new(expr)))
        }
        "doIf" if node.children.len() >= 2 => {
            let cond = syntax_to_surface(&node.children[0])?;
            let then_seq = syntax_to_do_seq(&node.children[1])?;
            let else_seq = if node.children.len() >= 3 {
                Some(syntax_to_do_seq(&node.children[2])?)
            } else {
                None
            };
            Some(DoElem::If(
                Span::dummy(),
                Box::new(cond),
                then_seq,
                else_seq,
            ))
        }
        "doIfLet" if node.children.len() >= 3 => {
            let pat = syntax_to_pattern(&node.children[0])?;
            let scrutinee = syntax_to_surface(&node.children[1])?;
            let then_seq = syntax_to_do_seq(&node.children[2])?;
            let else_seq = if node.children.len() >= 4 {
                Some(syntax_to_do_seq(&node.children[3])?)
            } else {
                None
            };
            Some(DoElem::IfLet(
                Span::dummy(),
                pat,
                Box::new(scrutinee),
                then_seq,
                else_seq,
            ))
        }
        "doIfDecidable" if node.children.len() >= 3 => {
            let witness = node.children[0].as_ident()?.to_string();
            let prop = syntax_to_surface(&node.children[1])?;
            let then_seq = syntax_to_do_seq(&node.children[2])?;
            let else_seq = if node.children.len() >= 4 {
                Some(syntax_to_do_seq(&node.children[3])?)
            } else {
                None
            };
            Some(DoElem::IfDecidable(
                Span::dummy(),
                witness,
                Box::new(prop),
                then_seq,
                else_seq,
            ))
        }
        "doFor" if node.children.len() == 3 => {
            let name = node.children[0].as_ident()?.to_string();
            let collection = syntax_to_surface(&node.children[1])?;
            let body = syntax_to_do_seq(&node.children[2])?;
            let binder = SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit);
            Some(DoElem::For(
                Span::dummy(),
                binder,
                Box::new(collection),
                body,
            ))
        }
        "doMatch" => {
            // Children: discriminees..., then doMatchArm nodes
            let mut discrs = Vec::new();
            let mut arms = Vec::new();
            for child in &node.children {
                if let Syntax::Node(n) = child {
                    if n.kind.name_str() == "doMatchArm" && n.children.len() == 2 {
                        let patterns = syntax_to_do_match_patterns(&n.children[0])?;
                        let body = syntax_to_do_seq(&n.children[1])?;
                        arms.push(DoMatchArm {
                            span: Span::dummy(),
                            patterns,
                            body,
                        });
                        continue;
                    }
                }
                discrs.push(syntax_to_surface(child)?);
            }
            Some(DoElem::Match(Span::dummy(), discrs, arms))
        }
        "doTry" => {
            // Children: doSeq (try body), then doCatch/doFinally nodes
            let mut children_iter = node.children.iter();
            let try_body = syntax_to_do_seq(children_iter.next()?)?;
            let mut catches = Vec::new();
            let mut finally_body = None;
            for child in children_iter {
                if let Syntax::Node(n) = child {
                    match n.kind.name_str() {
                        "doCatch" if n.children.len() >= 2 => {
                            let binder = n.children[0].as_ident()?.to_string();
                            let (exc_type, body_idx) = if n.children.len() >= 3 {
                                // May have exc_type between binder and body
                                if let Some(ty) = syntax_to_surface(&n.children[1]) {
                                    (Some(Box::new(ty)), 2)
                                } else {
                                    (None, 1)
                                }
                            } else {
                                (None, 1)
                            };
                            let body = syntax_to_do_seq(&n.children[body_idx])?;
                            catches.push(DoCatchClause {
                                span: Span::dummy(),
                                binder,
                                exc_type,
                                body,
                            });
                        }
                        "doFinally" if !n.children.is_empty() => {
                            // doFinally wraps its body in a doSeq child
                            let fin = syntax_to_do_seq(&n.children[0])?;
                            finally_body = Some(fin);
                        }
                        _ => {}
                    }
                }
            }
            Some(DoElem::TryCatch(
                Span::dummy(),
                try_body,
                catches,
                finally_body,
            ))
        }
        "doLetElse" if node.children.len() == 3 => {
            let pat = syntax_to_pattern(&node.children[0])?;
            let action = syntax_to_surface(&node.children[1])?;
            let fallback = syntax_to_do_seq(&node.children[2])?;
            Some(DoElem::LetElse(
                Span::dummy(),
                pat,
                Box::new(action),
                fallback,
            ))
        }
        "doLetRec" if node.children.len() >= 2 && node.children.len() % 2 == 0 => {
            // Encoded as flat pairs: [name1, val1, name2, val2, ...]
            let mut decls = Vec::new();
            for pair in node.children.chunks(2) {
                let name = pair[0].as_ident()?.to_string();
                let val = syntax_to_surface(&pair[1])?;
                let binder = SurfaceBinder {
                    span: Span::dummy(),
                    name,
                    ty: None,
                    default: None,
                    info: SurfaceBinderInfo::Explicit,
                };
                decls.push((binder, Box::new(val)));
            }
            Some(DoElem::LetRec(Span::dummy(), decls))
        }
        "doLetExpr" if node.children.len() == 3 => {
            let pat = syntax_to_pattern(&node.children[0])?;
            let discr = syntax_to_surface(&node.children[1])?;
            let fallback = syntax_to_do_seq(&node.children[2])?;
            Some(DoElem::LetExpr(
                Span::dummy(),
                pat,
                Box::new(discr),
                DoLetExprKind::Pure,
                fallback,
            ))
        }
        "doLetExprBind" if node.children.len() == 3 => {
            let pat = syntax_to_pattern(&node.children[0])?;
            let discr = syntax_to_surface(&node.children[1])?;
            let fallback = syntax_to_do_seq(&node.children[2])?;
            Some(DoElem::LetExpr(
                Span::dummy(),
                pat,
                Box::new(discr),
                DoLetExprKind::Bind,
                fallback,
            ))
        }
        "doRepeat" if node.children.len() == 1 => {
            let body = syntax_to_do_seq(&node.children[0])?;
            Some(DoElem::Repeat(Span::dummy(), body))
        }
        "doWhile" if node.children.len() == 2 => {
            let cond = syntax_to_surface(&node.children[0])?;
            let body = syntax_to_do_seq(&node.children[1])?;
            Some(DoElem::While(Span::dummy(), Box::new(cond), body))
        }
        "doDbgTrace" if node.children.len() == 1 => {
            let msg = syntax_to_surface(&node.children[0])?;
            Some(DoElem::DbgTrace(Span::dummy(), Box::new(msg)))
        }
        "doBreak" => Some(DoElem::Break(Span::dummy())),
        "doContinue" => Some(DoElem::Continue(Span::dummy())),
        "doReassign" if node.children.len() == 2 => {
            let name = node.children[0].as_ident()?.to_string();
            let val = syntax_to_surface(&node.children[1])?;
            Some(DoElem::Reassign(Span::dummy(), name, Box::new(val)))
        }
        "doReassignPat" if node.children.len() == 2 => {
            let pat = syntax_to_pattern(&node.children[0])?;
            let val = syntax_to_surface(&node.children[1])?;
            Some(DoElem::PatternReassign(Span::dummy(), pat, Box::new(val)))
        }
        _ => None,
    }
}

/// Convert a doSeq syntax node to a Vec<DoElem>.
fn syntax_to_do_seq(syntax: &Syntax) -> Option<Vec<DoElem>> {
    let node = match syntax {
        Syntax::Node(n) if n.kind.name_str() == "doSeq" => n,
        _ => return None,
    };
    node.children.iter().map(syntax_to_do_elem).collect()
}

/// Convert a patterns syntax node to a Vec<SurfacePattern>.
fn syntax_to_do_match_patterns(syntax: &Syntax) -> Option<Vec<SurfacePattern>> {
    let node = match syntax {
        Syntax::Node(n) if n.kind.name_str() == "patterns" => n,
        _ => return None,
    };
    node.children.iter().map(syntax_to_pattern).collect()
}
