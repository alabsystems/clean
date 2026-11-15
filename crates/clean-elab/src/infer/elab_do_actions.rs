// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nested action lifting for do-notation.
//!
//! Extracts `<- expr` (LiftMethod) nodes from within do-element sub-expressions
//! and hoists them into explicit `let __do_lift_N <- expr` bindings.
//!
//! Reference: Lean 4 `expandNestedActions` in src/Lean/Elab/Do/Basic.lean:687-741

use super::elab_do_actions_seq::{binder_has_lift_method, has_lift_method, lift_over_binder_error};
use super::*;
use clean_parser::SurfaceBinderInfo;

impl<'a> ElabCtx<'a> {
    /// Expand a do-element by extracting any `LiftMethod` (`<- expr`) nodes from
    /// its sub-expressions. Returns the lifted `let __do_lift_N <- expr` bindings
    /// and the rewritten element.
    ///
    /// If no `LiftMethod` nodes are found, the returned Vec is empty and the
    /// element is unchanged. Nested do-sequences (branches, loop and `try`
    /// bodies, match arms) are NOT entered here; `expand_seq_nested_actions`
    /// (`elab_do_actions_seq.rs`) runs this per element of every sequence.
    ///
    /// A `(← e)` under a binder Lean forbids lifting over is refused with
    /// Lean's message (`liftMethodForbiddenBinder`: `fun`, match
    /// alternatives, `let rec`), never hoisted out of it (G52).
    pub(super) fn expand_do_elem_actions(
        elem: &DoElem,
        counter: &mut usize,
    ) -> Result<(Vec<DoElem>, DoElem), ElabError> {
        Ok(match elem {
            DoElem::Expr(span, expr) => {
                let mut lifted = Vec::new();
                let new_expr = Self::expand_nested_actions_expr(expr, counter, &mut lifted)?;
                (lifted, DoElem::Expr(*span, Box::new(new_expr)))
            }
            DoElem::Return(span, expr) => {
                let mut lifted = Vec::new();
                let new_expr = Self::expand_nested_actions_expr(expr, counter, &mut lifted)?;
                (lifted, DoElem::Return(*span, Box::new(new_expr)))
            }
            DoElem::Bind(span, binder, action) => {
                let mut lifted = Vec::new();
                let new_action = Self::expand_nested_actions_expr(action, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::Bind(*span, binder.clone(), Box::new(new_action)),
                )
            }
            DoElem::Let(span, binder, val) => {
                let mut lifted = Vec::new();
                let new_val = Self::expand_nested_actions_expr(val, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::Let(*span, binder.clone(), Box::new(new_val)),
                )
            }
            DoElem::Have(span, binder, val) => {
                let mut lifted = Vec::new();
                let new_val = Self::expand_nested_actions_expr(val, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::Have(*span, binder.clone(), Box::new(new_val)),
                )
            }
            DoElem::LetMut(span, binder, val) => {
                let mut lifted = Vec::new();
                let new_val = Self::expand_nested_actions_expr(val, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::LetMut(*span, binder.clone(), Box::new(new_val)),
                )
            }
            DoElem::LetRec(_, decls) => {
                // `doLetRec` is a binder Lean never lifts over
                // (`liftMethodForbiddenBinder`): `let rec k : Nat := (← e)`
                // is refused, binder or not. Hoisting the action out of the
                // recursive value (the pre-G52 behaviour) accepted it.
                let lifts = decls
                    .iter()
                    .any(|(binder, val)| binder_has_lift_method(binder) || has_lift_method(val));
                if lifts {
                    return Err(lift_over_binder_error());
                }
                (Vec::new(), elem.clone())
            }
            DoElem::If(span, cond, then_branch, else_branch) => {
                // Only lift from the condition, not from branches
                // (branches are their own do-element scopes)
                let mut lifted = Vec::new();
                let new_cond = Self::expand_nested_actions_expr(cond, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::If(
                        *span,
                        Box::new(new_cond),
                        then_branch.clone(),
                        else_branch.clone(),
                    ),
                )
            }
            DoElem::IfLet(span, pat, scrutinee, then_branch, else_branch) => {
                // Only lift from the scrutinee (branches and pattern are sub-scopes)
                let mut lifted = Vec::new();
                let new_scrutinee =
                    Self::expand_nested_actions_expr(scrutinee, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::IfLet(
                        *span,
                        pat.clone(),
                        Box::new(new_scrutinee),
                        then_branch.clone(),
                        else_branch.clone(),
                    ),
                )
            }
            DoElem::IfDecidable(span, witness, prop, then_branch, else_branch) => {
                // Only lift from the proposition (branches are sub-scopes)
                let mut lifted = Vec::new();
                let new_prop = Self::expand_nested_actions_expr(prop, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::IfDecidable(
                        *span,
                        witness.clone(),
                        Box::new(new_prop),
                        then_branch.clone(),
                        else_branch.clone(),
                    ),
                )
            }
            // `for x in (← xs) do …` and `match ← e, (← f) with …`: the
            // collection and the discriminants are lifted ahead of the
            // element, as Lean's `expandLiftMethod` walks every argument of
            // the element up to the nested `doSeq` delimiters (G30).
            DoElem::For(span, binder, collection, body) => {
                let mut lifted = Vec::new();
                let new_collection =
                    Self::expand_nested_actions_expr(collection, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::For(
                        *span,
                        binder.clone(),
                        Box::new(new_collection),
                        body.clone(),
                    ),
                )
            }
            DoElem::Match(span, discrs, arms) => {
                let mut lifted = Vec::new();
                let new_discrs = discrs
                    .iter()
                    .map(|discr| Self::expand_nested_actions_expr(discr, counter, &mut lifted))
                    .collect::<Result<Vec<_>, _>>()?;
                (lifted, DoElem::Match(*span, new_discrs, arms.clone()))
            }
            // TryCatch, Repeat: nothing outside their nested sequences.
            DoElem::TryCatch(..) | DoElem::Repeat(..) => (Vec::new(), elem.clone()),
            // A `while` condition is evaluated on every iteration: Lean's
            // `while c do b` is `repeat if c then b else break`, so its lifts
            // belong INSIDE the loop. `expand_seq_nested_actions` rewrites a
            // lifting condition to that form; nothing is hoisted here (G53).
            DoElem::While(..) => (Vec::new(), elem.clone()),
            DoElem::DbgTrace(span, msg) => {
                // Lift from message expression
                let mut lifted = Vec::new();
                let new_msg = Self::expand_nested_actions_expr(msg, counter, &mut lifted)?;
                (lifted, DoElem::DbgTrace(*span, Box::new(new_msg)))
            }
            DoElem::LetElse(span, pat, action, fallback) => {
                // Only lift from the action expression (fallback is a sub-scope)
                let mut lifted = Vec::new();
                let new_action = Self::expand_nested_actions_expr(action, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::LetElse(*span, pat.clone(), Box::new(new_action), fallback.clone()),
                )
            }
            DoElem::LetExpr(span, pat, discr, kind, fallback) => {
                let mut lifted = Vec::new();
                let new_discr = Self::expand_nested_actions_expr(discr, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::LetExpr(
                        *span,
                        pat.clone(),
                        Box::new(new_discr),
                        *kind,
                        fallback.clone(),
                    ),
                )
            }
            // Break and Continue are pure control flow — no sub-expressions to lift from
            DoElem::Break(..) | DoElem::Continue(..) => (Vec::new(), elem.clone()),
            DoElem::Reassign(span, name, val) => {
                // Lift from the reassignment value expression
                let mut lifted = Vec::new();
                let new_val = Self::expand_nested_actions_expr(val, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::Reassign(*span, name.clone(), Box::new(new_val)),
                )
            }
            DoElem::PatternReassign(span, pat, val) => {
                let mut lifted = Vec::new();
                let new_val = Self::expand_nested_actions_expr(val, counter, &mut lifted)?;
                (
                    lifted,
                    DoElem::PatternReassign(*span, pat.clone(), Box::new(new_val)),
                )
            }
        })
    }

    /// Walk a `SurfaceExpr`, replacing `LiftMethod(span, inner)` nodes with
    /// fresh identifiers `__do_lift_N` and accumulating `DoElem::Bind` elements.
    ///
    /// Stops at do-block boundaries (`Do`, `For`, `Return`) since those have
    /// their own nested action scope. A lift under a binder Lean never lifts
    /// over (`fun`, a match alternative, `let rec`) is refused with Lean's
    /// message.
    pub(crate) fn expand_nested_actions_expr(
        expr: &SurfaceExpr,
        counter: &mut usize,
        lifted: &mut Vec<DoElem>,
    ) -> Result<SurfaceExpr, ElabError> {
        Ok(match expr {
            SurfaceExpr::LiftMethod(span, inner) => {
                // Recursively expand any nested lifts inside the inner expression
                let expanded_inner = Self::expand_nested_actions_expr(inner, counter, lifted)?;

                // Generate fresh name
                let name = SurfaceName::unspellable("__do_lift", *counter as u64);
                *counter += 1;

                // Create DoElem::Bind for the lifted action
                let binder = SurfaceBinder::new_typed(name.clone(), None, SurfaceBinderInfo::Explicit);
                lifted.push(DoElem::Bind(*span, binder, Box::new(expanded_inner)));

                // Replace with identifier reference
                SurfaceExpr::Ident(*span, name)
            }

            // === Stop at do-block boundaries ===
            SurfaceExpr::Do(..) => expr.clone(),

            // === Recurse into sub-expressions ===
            SurfaceExpr::App(span, func, args) => {
                let new_func = Self::expand_nested_actions_expr(func, counter, lifted)?;
                let new_args = args
                    .iter()
                    .map(|arg| {
                        Ok(SurfaceArg {
                            span: arg.span,
                            expr: Self::expand_nested_actions_expr(&arg.expr, counter, lifted)?,
                            name: arg.name.clone(),
                        })
                    })
                    .collect::<Result<Vec<SurfaceArg>, ElabError>>()?;
                SurfaceExpr::App(*span, Box::new(new_func), new_args)
            }
            SurfaceExpr::Paren(span, inner) => {
                let new_inner = Self::expand_nested_actions_expr(inner, counter, lifted)?;
                SurfaceExpr::Paren(*span, Box::new(new_inner))
            }
            SurfaceExpr::Ascription(span, expr_inner, ty) => {
                let new_expr = Self::expand_nested_actions_expr(expr_inner, counter, lifted)?;
                let new_ty = Self::expand_nested_actions_expr(ty, counter, lifted)?;
                SurfaceExpr::Ascription(*span, Box::new(new_expr), Box::new(new_ty))
            }
            SurfaceExpr::If(span, cond, then_br, else_br) => {
                // Only lift from the condition (branches are sub-scopes)
                let new_cond = Self::expand_nested_actions_expr(cond, counter, lifted)?;
                SurfaceExpr::If(*span, Box::new(new_cond), then_br.clone(), else_br.clone())
            }
            SurfaceExpr::IfLet(span, pat, scrutinee, then_br, else_br) => {
                // Lift from scrutinee only (branches are sub-scopes, pattern is not an expr)
                let new_scrutinee = Self::expand_nested_actions_expr(scrutinee, counter, lifted)?;
                SurfaceExpr::IfLet(
                    *span,
                    pat.clone(),
                    Box::new(new_scrutinee),
                    then_br.clone(),
                    else_br.clone(),
                )
            }
            SurfaceExpr::IfDecidable(span, witness, prop, then_br, else_br) => {
                // Lift from proposition only (branches are sub-scopes)
                let new_prop = Self::expand_nested_actions_expr(prop, counter, lifted)?;
                SurfaceExpr::IfDecidable(
                    *span,
                    witness.clone(),
                    Box::new(new_prop),
                    then_br.clone(),
                    else_br.clone(),
                )
            }
            SurfaceExpr::Match(span, hyp, discriminee, arms) => {
                // Lift from discriminee only (arm bodies are binder scopes where
                // lifts are forbidden per Lean 4 liftMethodForbiddenBinder)
                if arms.iter().any(|arm| has_lift_method(&arm.body)) {
                    return Err(lift_over_binder_error());
                }
                let new_disc = Self::expand_nested_actions_expr(discriminee, counter, lifted)?;
                SurfaceExpr::Match(*span, hyp.clone(), Box::new(new_disc), arms.clone())
            }
            SurfaceExpr::StructLit {
                span,
                struct_type,
                base,
                fields,
            } => {
                // Recurse into base expr and field values (not struct_type annotation)
                let new_base = base
                    .as_ref()
                    .map(|b| Self::expand_nested_actions_expr(b, counter, lifted).map(Box::new))
                    .transpose()?;
                let new_fields = fields
                    .iter()
                    .map(|f| {
                        Ok(clean_parser::SurfaceFieldAssign {
                            span: f.span,
                            name: f.name.clone(),
                            val: Self::expand_nested_actions_expr(&f.val, counter, lifted)?,
                        })
                    })
                    .collect::<Result<Vec<_>, ElabError>>()?;
                SurfaceExpr::StructLit {
                    span: *span,
                    struct_type: struct_type.clone(),
                    base: new_base,
                    fields: new_fields,
                }
            }
            SurfaceExpr::Arrow(span, from, to) => {
                let new_from = Self::expand_nested_actions_expr(from, counter, lifted)?;
                let new_to = Self::expand_nested_actions_expr(to, counter, lifted)?;
                SurfaceExpr::Arrow(*span, Box::new(new_from), Box::new(new_to))
            }
            SurfaceExpr::Proj(span, expr_inner, proj) => {
                let new_expr = Self::expand_nested_actions_expr(expr_inner, counter, lifted)?;
                SurfaceExpr::Proj(*span, Box::new(new_expr), proj.clone())
            }
            SurfaceExpr::Explicit(span, inner) => {
                let new_inner = Self::expand_nested_actions_expr(inner, counter, lifted)?;
                SurfaceExpr::Explicit(*span, Box::new(new_inner))
            }
            SurfaceExpr::NamedArg(span, name, val) => {
                let new_val = Self::expand_nested_actions_expr(val, counter, lifted)?;
                SurfaceExpr::NamedArg(*span, name.clone(), Box::new(new_val))
            }
            SurfaceExpr::OutParam(span, inner) => {
                let new_inner = Self::expand_nested_actions_expr(inner, counter, lifted)?;
                SurfaceExpr::OutParam(*span, Box::new(new_inner))
            }
            SurfaceExpr::SemiOutParam(span, inner) => {
                let new_inner = Self::expand_nested_actions_expr(inner, counter, lifted)?;
                SurfaceExpr::SemiOutParam(*span, Box::new(new_inner))
            }

            // === Binders Lean never lifts over (`liftMethodForbiddenBinder`):
            // `fun` (and its pattern-matching form) and `let rec`. ===
            SurfaceExpr::Lambda(..)
            | SurfaceExpr::PatternMatchLambda(..)
            | SurfaceExpr::LetRec(..) => {
                if has_lift_method(expr) {
                    return Err(lift_over_binder_error());
                }
                expr.clone()
            }

            // === Leaf nodes and other binder positions: no recursion ===
            // (a lift left inside one of these is refused when it is
            // elaborated: "nested action outside a do block")
            SurfaceExpr::Ident(..)
            | SurfaceExpr::SyntheticSorry(..)
            | SurfaceExpr::Universe(..)
            | SurfaceExpr::Lit(..)
            | SurfaceExpr::Hole(..)
            | SurfaceExpr::NamedHole(..)
            | SurfaceExpr::SyntaxQuote(..)
            | SurfaceExpr::Pi(..)
            | SurfaceExpr::Let(..) | SurfaceExpr::Have(..)
            | SurfaceExpr::LetPattern(..)
            | SurfaceExpr::UniverseInst(..)
            | SurfaceExpr::QQuotation { .. }
            | SurfaceExpr::QAntiquot { .. }
            | SurfaceExpr::ByTactic(..)
            | SurfaceExpr::CalcBlock(..)
            // `open X in <term>` scopes name resolution to its own sub-term; do
            // not lift nested actions across the boundary (leaf treatment).
            | SurfaceExpr::OpenIn { .. }
            | SurfaceExpr::InterpolatedStr { .. } => expr.clone(),
        })
    }
}
