// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nested action lifting at EVERY `doSeq` of a `do` block.
//!
//! Lean's `doSeqToCode` (`src/Lean/Elab/Do.lean`) runs `expandLiftMethod` on
//! each element of each sequence it compiles — the top-level one, and every
//! nested one (an `if` branch, a `match` alternative, a `for`/`repeat` body,
//! a `try`/`catch`/`finally` body, a `let … | fallback`). The lifted
//! `let a ← e` binds go immediately before the element that contained them,
//! INSIDE that element's own sequence, so the action runs only when (and as
//! often as) that element does.
//!
//! Clean ran the pre-pass on the top-level sequence only, so a `(← e)` in a
//! branch or a loop body was never lifted (refused "nested action outside a
//! do block", G30) and a `while` condition's lift was hoisted ahead of the
//! loop and evaluated once (G53).

use super::*;
use clean_parser::DoCatchClause;

/// Lean 4.8.0's message for a `(← e)` under a binder it never lifts over
/// (`expandLiftMethodAux`, `src/Lean/Elab/Do.lean`).
pub(super) fn lift_over_binder_error() -> ElabError {
    ElabError::DoNotation {
        message: "cannot lift `(<- ...)` over a binder, this error usually happens when you are \
                  trying to lift a method nested in a `fun`, `let`, or `match`-alternative, and \
                  it can often be fixed by adding a missing `do`"
            .into(),
    }
}

/// Lean 4.8.0's message for a `return`, `break` or `continue` followed by
/// more elements of its sequence (`ensureEOS`, `src/Lean/Elab/Do.lean`).
fn not_last_element_error() -> ElabError {
    ElabError::DoNotation {
        message: "must be last element in a `do` sequence".into(),
    }
}

/// Whether `expr` holds a `(← e)` that a `do` element containing it would
/// have to lift: every sub-term up to a nested `do` (a `liftMethodDelimiter`).
/// Quotations and tactic blocks are not entered.
pub(super) fn has_lift_method(expr: &SurfaceExpr) -> bool {
    stack_safe(|| match expr {
        SurfaceExpr::LiftMethod(..) => true,
        SurfaceExpr::Do(..)
        | SurfaceExpr::Ident(..)
        | SurfaceExpr::SyntheticSorry(..)
        | SurfaceExpr::Universe(..)
        | SurfaceExpr::Lit(..)
        | SurfaceExpr::Hole(..)
        | SurfaceExpr::NamedHole(..)
        | SurfaceExpr::SyntaxQuote(..)
        | SurfaceExpr::QQuotation { .. }
        | SurfaceExpr::QAntiquot { .. }
        | SurfaceExpr::ByTactic(..)
        | SurfaceExpr::CalcBlock(..) => false,
        SurfaceExpr::App(_, func, args) => {
            has_lift_method(func) || args.iter().any(|arg| has_lift_method(&arg.expr))
        }
        SurfaceExpr::Lambda(_, binders, body)
        | SurfaceExpr::PatternMatchLambda(_, binders, body)
        | SurfaceExpr::Pi(_, binders, body) => {
            binders.iter().any(binder_has_lift_method) || has_lift_method(body)
        }
        SurfaceExpr::Let(_, binder, val, body)
        | SurfaceExpr::Have(_, binder, val, body)
        | SurfaceExpr::LetRec(_, binder, val, body) => {
            binder_has_lift_method(binder) || has_lift_method(val) || has_lift_method(body)
        }
        SurfaceExpr::LetPattern(_, _, ty, val, body) => {
            has_lift_method(ty) || has_lift_method(val) || has_lift_method(body)
        }
        SurfaceExpr::Arrow(_, a, b) | SurfaceExpr::Ascription(_, a, b) => {
            has_lift_method(a) || has_lift_method(b)
        }
        SurfaceExpr::If(_, c, t, e)
        | SurfaceExpr::IfLet(_, _, c, t, e)
        | SurfaceExpr::IfDecidable(_, _, c, t, e) => {
            has_lift_method(c) || has_lift_method(t) || has_lift_method(e)
        }
        SurfaceExpr::Match(_, _, discr, arms) => {
            has_lift_method(discr) || arms.iter().any(|arm| has_lift_method(&arm.body))
        }
        SurfaceExpr::Paren(_, e)
        | SurfaceExpr::OutParam(_, e)
        | SurfaceExpr::SemiOutParam(_, e)
        | SurfaceExpr::Explicit(_, e)
        | SurfaceExpr::NamedArg(_, _, e)
        | SurfaceExpr::Proj(_, e, _)
        | SurfaceExpr::UniverseInst(_, e, _) => has_lift_method(e),
        SurfaceExpr::StructLit {
            struct_type,
            base,
            fields,
            ..
        } => {
            struct_type.as_deref().is_some_and(has_lift_method)
                || base.as_deref().is_some_and(has_lift_method)
                || fields.iter().any(|field| has_lift_method(&field.val))
        }
        SurfaceExpr::InterpolatedStr { parts, .. } => parts.iter().any(|part| match part {
            clean_parser::InterpolationPart::Expr(e) => has_lift_method(e),
            _ => false,
        }),
        SurfaceExpr::OpenIn { body, .. } => has_lift_method(body),
    })
}

/// Whether a binder's type or default value holds a `(← e)`.
pub(super) fn binder_has_lift_method(binder: &SurfaceBinder) -> bool {
    binder.ty.as_deref().is_some_and(has_lift_method)
        || binder.default.as_deref().is_some_and(has_lift_method)
}

impl<'a> ElabCtx<'a> {
    /// Lean's `expandLiftMethod`, run on each element of `elems` and of every
    /// do-sequence nested in them. `counter` is shared so every lifted name
    /// of one block is distinct.
    pub(crate) fn expand_seq_nested_actions(
        elems: &[DoElem],
        counter: &mut usize,
    ) -> Result<Vec<DoElem>, ElabError> {
        let mut result = Vec::with_capacity(elems.len());
        for (index, elem) in elems.iter().enumerate() {
            // `return e; more` — Lean refuses the sequence; Clean used to
            // elaborate `return e` as `pure e` and drop `more` (G54).
            if index + 1 < elems.len()
                && matches!(
                    elem,
                    DoElem::Return(..) | DoElem::Break(..) | DoElem::Continue(..)
                )
            {
                return Err(not_last_element_error());
            }
            // `while c do b` with a lifting condition is Lean's macro
            // `repeat if c then b else break`: its lifts run inside the loop,
            // once per iteration (G53). A condition that lifts nothing keeps
            // the direct `while` lowering.
            if let DoElem::While(span, cond, body) = elem {
                if has_lift_method(cond) {
                    let guarded = DoElem::If(
                        *span,
                        cond.clone(),
                        body.clone(),
                        Some(vec![DoElem::Break(*span)]),
                    );
                    let body = Self::expand_seq_nested_actions(&[guarded], counter)?;
                    result.push(DoElem::Repeat(*span, body));
                    continue;
                }
            }
            // Lean refuses an exit point in a `finally` body (`doTry`:
            // "`finally` currently does `return`, `break`, nor `continue`",
            // sic); a loop inside it keeps its own `break`/`continue`.
            if let DoElem::TryCatch(_, _, _, Some(finally_body)) = elem {
                let info = elab_do_control::infer_control_info_seq(finally_body);
                if info.returns_early || info.breaks || info.continues {
                    return Err(ElabError::DoNotation {
                        message: "`finally` currently does `return`, `break`, nor `continue`"
                            .into(),
                    });
                }
            }
            let (lifted, new_elem) = Self::expand_do_elem_actions(elem, counter)?;
            result.extend(lifted);
            result.push(Self::expand_nested_sequences(new_elem, counter)?);
        }
        Ok(result)
    }

    /// Run [`Self::expand_seq_nested_actions`] on every do-sequence directly
    /// nested in `elem`.
    fn expand_nested_sequences(elem: DoElem, counter: &mut usize) -> Result<DoElem, ElabError> {
        let mut seq = |elems: Vec<DoElem>| Self::expand_seq_nested_actions(&elems, counter);
        Ok(match elem {
            DoElem::If(span, cond, then_branch, else_branch) => DoElem::If(
                span,
                cond,
                seq(then_branch)?,
                else_branch.map(&mut seq).transpose()?,
            ),
            DoElem::IfLet(span, pat, scrutinee, then_branch, else_branch) => DoElem::IfLet(
                span,
                pat,
                scrutinee,
                seq(then_branch)?,
                else_branch.map(&mut seq).transpose()?,
            ),
            DoElem::IfDecidable(span, witness, prop, then_branch, else_branch) => {
                DoElem::IfDecidable(
                    span,
                    witness,
                    prop,
                    seq(then_branch)?,
                    else_branch.map(&mut seq).transpose()?,
                )
            }
            DoElem::For(span, binder, collection, body) => {
                DoElem::For(span, binder, collection, seq(body)?)
            }
            DoElem::Match(span, discrs, arms) => {
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        Ok(DoMatchArm {
                            span: arm.span,
                            patterns: arm.patterns,
                            body: seq(arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, ElabError>>()?;
                DoElem::Match(span, discrs, arms)
            }
            DoElem::TryCatch(span, try_body, catches, finally_body) => {
                let try_body = seq(try_body)?;
                let catches = catches
                    .into_iter()
                    .map(|clause| {
                        Ok(DoCatchClause {
                            span: clause.span,
                            binder: clause.binder,
                            exc_type: clause.exc_type,
                            body: seq(clause.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, ElabError>>()?;
                let finally_body = finally_body.map(&mut seq).transpose()?;
                DoElem::TryCatch(span, try_body, catches, finally_body)
            }
            DoElem::LetElse(span, pat, action, fallback) => {
                DoElem::LetElse(span, pat, action, seq(fallback)?)
            }
            DoElem::LetExpr(span, pat, discr, kind, fallback) => {
                DoElem::LetExpr(span, pat, discr, kind, seq(fallback)?)
            }
            DoElem::Repeat(span, body) => DoElem::Repeat(span, seq(body)?),
            DoElem::While(span, cond, body) => DoElem::While(span, cond, seq(body)?),
            other @ (DoElem::Bind(..)
            | DoElem::Let(..)
            | DoElem::Have(..)
            | DoElem::LetMut(..)
            | DoElem::LetRec(..)
            | DoElem::Return(..)
            | DoElem::Expr(..)
            | DoElem::DbgTrace(..)
            | DoElem::Break(..)
            | DoElem::Continue(..)
            | DoElem::Reassign(..)
            | DoElem::PatternReassign(..)) => other,
        })
    }
}
