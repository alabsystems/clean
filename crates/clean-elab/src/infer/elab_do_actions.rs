// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nested action lifting for do-notation.
//!
//! Extracts `<- expr` (LiftMethod) nodes from within do-element sub-expressions
//! and hoists them into explicit `let __do_lift_N <- expr` bindings.
//!
//! Reference: Lean 4 `expandNestedActions` in src/Lean/Elab/Do/Basic.lean:687-741

use super::*;
use clean_parser::SurfaceBinderInfo;

impl<'a> ElabCtx<'a> {
    /// Expand a do-element by extracting any `LiftMethod` (`<- expr`) nodes from
    /// its sub-expressions. Returns the lifted `let __do_lift_N <- expr` bindings
    /// and the rewritten element.
    ///
    /// If no `LiftMethod` nodes are found, the returned Vec is empty and the
    /// element is unchanged.
    pub(super) fn expand_do_elem_actions(
        &self,
        elem: &DoElem,
        counter: &mut usize,
    ) -> (Vec<DoElem>, DoElem) {
        match elem {
            DoElem::Expr(span, expr) => {
                let mut lifted = Vec::new();
                let new_expr = Self::expand_nested_actions_expr(expr, counter, &mut lifted);
                (lifted, DoElem::Expr(*span, Box::new(new_expr)))
            }
            DoElem::Return(span, expr) => {
                let mut lifted = Vec::new();
                let new_expr = Self::expand_nested_actions_expr(expr, counter, &mut lifted);
                (lifted, DoElem::Return(*span, Box::new(new_expr)))
            }
            DoElem::Bind(span, binder, action) => {
                let mut lifted = Vec::new();
                let new_action = Self::expand_nested_actions_expr(action, counter, &mut lifted);
                (
                    lifted,
                    DoElem::Bind(*span, binder.clone(), Box::new(new_action)),
                )
            }
            DoElem::Let(span, binder, val) => {
                let mut lifted = Vec::new();
                let new_val = Self::expand_nested_actions_expr(val, counter, &mut lifted);
                (
                    lifted,
                    DoElem::Let(*span, binder.clone(), Box::new(new_val)),
                )
            }
            DoElem::LetMut(span, binder, val) => {
                let mut lifted = Vec::new();
                let new_val = Self::expand_nested_actions_expr(val, counter, &mut lifted);
                (
                    lifted,
                    DoElem::LetMut(*span, binder.clone(), Box::new(new_val)),
                )
            }
            DoElem::LetRec(span, decls) => {
                let mut lifted = Vec::new();
                let new_decls: Vec<_> = decls
                    .iter()
                    .map(|(binder, val)| {
                        let new_val = Self::expand_nested_actions_expr(val, counter, &mut lifted);
                        (binder.clone(), Box::new(new_val))
                    })
                    .collect();
                (lifted, DoElem::LetRec(*span, new_decls))
            }
            DoElem::If(span, cond, then_branch, else_branch) => {
                // Only lift from the condition, not from branches
                // (branches are their own do-element scopes)
                let mut lifted = Vec::new();
                let new_cond = Self::expand_nested_actions_expr(cond, counter, &mut lifted);
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
                    Self::expand_nested_actions_expr(scrutinee, counter, &mut lifted);
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
                let new_prop = Self::expand_nested_actions_expr(prop, counter, &mut lifted);
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
            // For, Match, TryCatch, Repeat: don't lift from their sub-elements
            // (they have their own scopes)
            DoElem::For(..) | DoElem::Match(..) | DoElem::TryCatch(..) | DoElem::Repeat(..) => {
                (Vec::new(), elem.clone())
            }
            DoElem::While(span, cond, body) => {
                // Lift from condition only (body is a sub-scope)
                let mut lifted = Vec::new();
                let new_cond = Self::expand_nested_actions_expr(cond, counter, &mut lifted);
                (
                    lifted,
                    DoElem::While(*span, Box::new(new_cond), body.clone()),
                )
            }
            DoElem::DbgTrace(span, msg) => {
                // Lift from message expression
                let mut lifted = Vec::new();
                let new_msg = Self::expand_nested_actions_expr(msg, counter, &mut lifted);
                (lifted, DoElem::DbgTrace(*span, Box::new(new_msg)))
            }
            DoElem::LetElse(span, pat, action, fallback) => {
                // Only lift from the action expression (fallback is a sub-scope)
                let mut lifted = Vec::new();
                let new_action = Self::expand_nested_actions_expr(action, counter, &mut lifted);
                (
                    lifted,
                    DoElem::LetElse(*span, pat.clone(), Box::new(new_action), fallback.clone()),
                )
            }
            DoElem::LetExpr(span, pat, discr, kind, fallback) => {
                let mut lifted = Vec::new();
                let new_discr = Self::expand_nested_actions_expr(discr, counter, &mut lifted);
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
                let new_val = Self::expand_nested_actions_expr(val, counter, &mut lifted);
                (
                    lifted,
                    DoElem::Reassign(*span, name.clone(), Box::new(new_val)),
                )
            }
            DoElem::PatternReassign(span, pat, val) => {
                let mut lifted = Vec::new();
                let new_val = Self::expand_nested_actions_expr(val, counter, &mut lifted);
                (
                    lifted,
                    DoElem::PatternReassign(*span, pat.clone(), Box::new(new_val)),
                )
            }
        }
    }

    /// Walk a `SurfaceExpr`, replacing `LiftMethod(span, inner)` nodes with
    /// fresh identifiers `__do_lift_N` and accumulating `DoElem::Bind` elements.
    ///
    /// Stops at do-block boundaries (`Do`, `For`, `Return`) since those have
    /// their own nested action scope.
    pub(crate) fn expand_nested_actions_expr(
        expr: &SurfaceExpr,
        counter: &mut usize,
        lifted: &mut Vec<DoElem>,
    ) -> SurfaceExpr {
        match expr {
            SurfaceExpr::LiftMethod(span, inner) => {
                // Recursively expand any nested lifts inside the inner expression
                let expanded_inner = Self::expand_nested_actions_expr(inner, counter, lifted);

                // Generate fresh name
                let name = format!("__do_lift_{}", *counter);
                *counter += 1;

                // Create DoElem::Bind for the lifted action
                let binder = SurfaceBinder::new(&name, None, SurfaceBinderInfo::Explicit);
                lifted.push(DoElem::Bind(*span, binder, Box::new(expanded_inner)));

                // Replace with identifier reference
                SurfaceExpr::Ident(*span, name)
            }

            // === Stop at do-block boundaries ===
            SurfaceExpr::Do(..) => expr.clone(),

            // === Recurse into sub-expressions ===
            SurfaceExpr::App(span, func, args) => {
                let new_func = Self::expand_nested_actions_expr(func, counter, lifted);
                let new_args: Vec<SurfaceArg> = args
                    .iter()
                    .map(|arg| SurfaceArg {
                        span: arg.span,
                        expr: Self::expand_nested_actions_expr(&arg.expr, counter, lifted),
                        name: arg.name.clone(),
                    })
                    .collect();
                SurfaceExpr::App(*span, Box::new(new_func), new_args)
            }
            SurfaceExpr::Paren(span, inner) => {
                let new_inner = Self::expand_nested_actions_expr(inner, counter, lifted);
                SurfaceExpr::Paren(*span, Box::new(new_inner))
            }
            SurfaceExpr::Ascription(span, expr_inner, ty) => {
                let new_expr = Self::expand_nested_actions_expr(expr_inner, counter, lifted);
                let new_ty = Self::expand_nested_actions_expr(ty, counter, lifted);
                SurfaceExpr::Ascription(*span, Box::new(new_expr), Box::new(new_ty))
            }
            SurfaceExpr::If(span, cond, then_br, else_br) => {
                // Only lift from the condition (branches are sub-scopes)
                let new_cond = Self::expand_nested_actions_expr(cond, counter, lifted);
                SurfaceExpr::If(*span, Box::new(new_cond), then_br.clone(), else_br.clone())
            }
            SurfaceExpr::IfLet(span, pat, scrutinee, then_br, else_br) => {
                // Lift from scrutinee only (branches are sub-scopes, pattern is not an expr)
                let new_scrutinee = Self::expand_nested_actions_expr(scrutinee, counter, lifted);
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
                let new_prop = Self::expand_nested_actions_expr(prop, counter, lifted);
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
                let new_disc = Self::expand_nested_actions_expr(discriminee, counter, lifted);
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
                    .map(|b| Box::new(Self::expand_nested_actions_expr(b, counter, lifted)));
                let new_fields: Vec<_> = fields
                    .iter()
                    .map(|f| clean_parser::SurfaceFieldAssign {
                        span: f.span,
                        name: f.name.clone(),
                        val: Self::expand_nested_actions_expr(&f.val, counter, lifted),
                    })
                    .collect();
                SurfaceExpr::StructLit {
                    span: *span,
                    struct_type: struct_type.clone(),
                    base: new_base,
                    fields: new_fields,
                }
            }
            SurfaceExpr::Arrow(span, from, to) => {
                let new_from = Self::expand_nested_actions_expr(from, counter, lifted);
                let new_to = Self::expand_nested_actions_expr(to, counter, lifted);
                SurfaceExpr::Arrow(*span, Box::new(new_from), Box::new(new_to))
            }
            SurfaceExpr::Proj(span, expr_inner, proj) => {
                let new_expr = Self::expand_nested_actions_expr(expr_inner, counter, lifted);
                SurfaceExpr::Proj(*span, Box::new(new_expr), proj.clone())
            }
            SurfaceExpr::Explicit(span, inner) => {
                let new_inner = Self::expand_nested_actions_expr(inner, counter, lifted);
                SurfaceExpr::Explicit(*span, Box::new(new_inner))
            }
            SurfaceExpr::NamedArg(span, name, val) => {
                let new_val = Self::expand_nested_actions_expr(val, counter, lifted);
                SurfaceExpr::NamedArg(*span, name.clone(), Box::new(new_val))
            }
            SurfaceExpr::OutParam(span, inner) => {
                let new_inner = Self::expand_nested_actions_expr(inner, counter, lifted);
                SurfaceExpr::OutParam(*span, Box::new(new_inner))
            }
            SurfaceExpr::SemiOutParam(span, inner) => {
                let new_inner = Self::expand_nested_actions_expr(inner, counter, lifted);
                SurfaceExpr::SemiOutParam(*span, Box::new(new_inner))
            }

            // === Leaf nodes and binder positions: no recursion ===
            // (Lean 4 forbids lifts inside lambda/forall/let binder positions,
            // and these are all either leaves or binder scopes.)
            SurfaceExpr::Ident(..)
            | SurfaceExpr::SyntheticSorry(..)
            | SurfaceExpr::Universe(..)
            | SurfaceExpr::Lit(..)
            | SurfaceExpr::Hole(..)
            | SurfaceExpr::NamedHole(..)
            | SurfaceExpr::SyntaxQuote(..)
            | SurfaceExpr::Lambda(..)
            | SurfaceExpr::PatternMatchLambda(..)
            | SurfaceExpr::Pi(..)
            | SurfaceExpr::Let(..)
            | SurfaceExpr::LetRec(..)
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
        }
    }
}
