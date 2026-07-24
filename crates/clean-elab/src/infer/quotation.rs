// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Q/q quotation elaboration
//!
//! This module handles elaboration of Qq quotations:
//! - `Q(α)`: Type quotation - elaborates α to a type expression
//! - `q(e)`: Value quotation - elaborates e, handling $-antiquotations
//!
//! Part of #16: Qq quotation support

use super::ElabCtx;
use crate::stack_safe;
use crate::unify::{Unifier, UnifyResult};
use crate::ElabError;
use clean_kernel::Expr;
use clean_parser::{
    QAntiquotContent, QQuotationKind, SurfaceArg, SurfaceExpr, SurfaceFieldAssign, SurfaceMatchArm,
};

impl<'a> ElabCtx<'a> {
    /// Elaborate Q(α) or q(e) quotation
    ///
    /// Part of #16: Qq quotation support
    ///
    /// - Q(α): Type quotation - elaborates α to a type expression
    /// - q(e): Value quotation - elaborates e, handling $-antiquotations
    pub(super) fn elaborate_q_quotation(
        &mut self,
        kind: QQuotationKind,
        inner: &SurfaceExpr,
        type_annot: Option<&SurfaceExpr>,
    ) -> Result<Expr, ElabError> {
        match kind {
            QQuotationKind::Type => {
                // Q(α) - type quotation
                // Elaborate α to get the type expression
                let ty_expr = self.elaborate(inner)?;

                // If there's a type annotation, check it
                if let Some(annot) = type_annot {
                    let annot_expr = self.elaborate(annot)?;
                    // The annotation should be the kind of the type
                    let ty_of_ty = self.infer_type(&ty_expr)?;
                    let ctx = self.build_local_ctx();
                    let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                    if let UnifyResult::Failure(msg) = unifier.unify(&ty_of_ty, &annot_expr) {
                        return Err(ElabError::TypeMismatch {
                            expected: format!("{annot_expr:?}"),
                            actual: format!("{ty_of_ty:?} ({msg})"),
                        });
                    }
                }

                // Create Q(α) representation
                // For now, Q(α) is represented as Qq.Quoted α where Quoted is just Expr
                // This is the transparent representation - the type α is tracked but
                // Q(α) ≡ Expr at the kernel level
                self.mk_q_type(ty_expr)
            }

            QQuotationKind::Value => {
                // q(e) - value quotation
                // Process antiquotations in the expression
                let processed = self.process_qq_antiquots(inner)?;

                // Elaborate the processed expression
                let expr = self.elaborate(&processed)?;

                // If there's a type annotation, check it
                if let Some(annot) = type_annot {
                    let expected_ty = self.elaborate(annot)?;
                    let actual_ty = self.infer_type(&expr)?;
                    let ctx = self.build_local_ctx();
                    let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
                    if let UnifyResult::Failure(msg) = unifier.unify(&actual_ty, &expected_ty) {
                        return Err(ElabError::TypeMismatch {
                            expected: format!("{expected_ty:?}"),
                            actual: format!("{actual_ty:?} ({msg})"),
                        });
                    }
                }

                Ok(expr)
            }
        }
    }

    /// Create the type expression for Q(α)
    ///
    /// Q(α) is represented as `Qq.Quoted α` which is transparent (just Expr with type tracking)
    pub(super) fn mk_q_type(&self, inner_type: Expr) -> Result<Expr, ElabError> {
        // For Phase 2, Q(α) just returns the inner type directly
        // This is the transparent representation - Q(Nat) ≈ Nat at elaboration time
        // Full quote4 semantics would wrap in a Quoted constructor
        //
        // Note: This simplified approach means Q(α) doesn't add indirection.
        // For type-safe metaprogramming, we'd need:
        //   Qq.Quoted : Type u → Type u
        //   q : {α : Type u} → α → Qq.Quoted α
        //
        // For now, we're transparent to get parsing and basic elaboration working.
        Ok(inner_type)
    }

    /// Process antiquotations in a q(...) body
    ///
    /// Walks the surface expression, replacing $x, $(e), and $(x:τ) with
    /// their elaborated values from the enclosing scope.
    pub(super) fn process_qq_antiquots(
        &mut self,
        expr: &SurfaceExpr,
    ) -> Result<SurfaceExpr, ElabError> {
        stack_safe(|| match expr {
            SurfaceExpr::QAntiquot { content, span } => {
                // Process antiquotation - look up variable in scope
                match content {
                    QAntiquotContent::Simple(name) => {
                        // $x - reference the variable x from enclosing scope
                        // For now, just return it as an identifier - elaboration will resolve it
                        Ok(SurfaceExpr::Ident(*span, name.clone()))
                    }

                    QAntiquotContent::Expr(inner) => {
                        // $(e) - splice in the expression e
                        // Return the inner expression directly for elaboration
                        Ok((**inner).clone())
                    }

                    QAntiquotContent::Typed { name, ty: _ } => {
                        // $(x : τ) - typed splice
                        // For now, just resolve to the identifier
                        // Type checking happens during elaboration
                        Ok(SurfaceExpr::Ident(*span, name.clone()))
                    }

                    QAntiquotContent::Splice { name, .. } => {
                        // $[xs]* - splice a list of expressions
                        // For now, just resolve to the identifier - the macro
                        // expander will handle iterating over the list
                        Ok(SurfaceExpr::Ident(*span, name.clone()))
                    }
                }
            }

            // Recursively process children
            SurfaceExpr::App(span, func, args) => {
                let new_func = self.process_qq_antiquots(func)?;
                let new_args: Result<Vec<_>, ElabError> = args
                    .iter()
                    .map(|arg| {
                        let new_expr = self.process_qq_antiquots(&arg.expr)?;
                        Ok(SurfaceArg {
                            span: arg.span,
                            expr: new_expr,
                            name: arg.name.clone(),
                        })
                    })
                    .collect();
                Ok(SurfaceExpr::App(*span, Box::new(new_func), new_args?))
            }

            SurfaceExpr::Lambda(span, binders, body) => {
                let new_body = self.process_qq_antiquots(body)?;
                Ok(SurfaceExpr::Lambda(
                    *span,
                    binders.clone(),
                    Box::new(new_body),
                ))
            }

            SurfaceExpr::Pi(span, binders, body) => {
                let new_body = self.process_qq_antiquots(body)?;
                Ok(SurfaceExpr::Pi(*span, binders.clone(), Box::new(new_body)))
            }

            SurfaceExpr::Arrow(span, from, to) => {
                let new_from = self.process_qq_antiquots(from)?;
                let new_to = self.process_qq_antiquots(to)?;
                Ok(SurfaceExpr::Arrow(
                    *span,
                    Box::new(new_from),
                    Box::new(new_to),
                ))
            }

            SurfaceExpr::Let(span, binder, val, body) => {
                let new_val = self.process_qq_antiquots(val)?;
                let new_body = self.process_qq_antiquots(body)?;
                Ok(SurfaceExpr::Let(
                    *span,
                    binder.clone(),
                    Box::new(new_val),
                    Box::new(new_body),
                ))
            }

            SurfaceExpr::Paren(span, inner) => {
                let new_inner = self.process_qq_antiquots(inner)?;
                Ok(SurfaceExpr::Paren(*span, Box::new(new_inner)))
            }

            SurfaceExpr::Ascription(span, expr, ty) => {
                let new_expr = self.process_qq_antiquots(expr)?;
                let new_ty = self.process_qq_antiquots(ty)?;
                Ok(SurfaceExpr::Ascription(
                    *span,
                    Box::new(new_expr),
                    Box::new(new_ty),
                ))
            }

            SurfaceExpr::If(span, cond, then_br, else_br) => {
                let new_cond = self.process_qq_antiquots(cond)?;
                let new_then = self.process_qq_antiquots(then_br)?;
                let new_else = self.process_qq_antiquots(else_br)?;
                Ok(SurfaceExpr::If(
                    *span,
                    Box::new(new_cond),
                    Box::new(new_then),
                    Box::new(new_else),
                ))
            }

            // Nested quotations - process recursively
            SurfaceExpr::QQuotation {
                span,
                kind,
                inner,
                type_annot,
            } => {
                let new_inner = self.process_qq_antiquots(inner)?;
                let new_type_annot = if let Some(ta) = type_annot {
                    Some(Box::new(self.process_qq_antiquots(ta)?))
                } else {
                    None
                };
                Ok(SurfaceExpr::QQuotation {
                    span: *span,
                    kind: *kind,
                    inner: Box::new(new_inner),
                    type_annot: new_type_annot,
                })
            }

            // Match expression - process scrutinee and arm bodies
            SurfaceExpr::Match(span, hyp, scrutinee, arms) => {
                let new_scrutinee = self.process_qq_antiquots(scrutinee)?;
                let new_arms: Result<Vec<_>, ElabError> = arms
                    .iter()
                    .map(|arm| {
                        let new_body = self.process_qq_antiquots(&arm.body)?;
                        Ok(SurfaceMatchArm {
                            span: arm.span,
                            pattern: arm.pattern.clone(),
                            body: new_body,
                        })
                    })
                    .collect();
                Ok(SurfaceExpr::Match(
                    *span,
                    hyp.clone(),
                    Box::new(new_scrutinee),
                    new_arms?,
                ))
            }

            // Struct literal - process field values
            SurfaceExpr::StructLit {
                span,
                struct_type,
                base,
                fields,
            } => {
                let new_struct_type = if let Some(st) = struct_type {
                    Some(Box::new(self.process_qq_antiquots(st)?))
                } else {
                    None
                };
                let new_base = if let Some(b) = base {
                    Some(Box::new(self.process_qq_antiquots(b)?))
                } else {
                    None
                };
                let new_fields: Result<Vec<_>, ElabError> = fields
                    .iter()
                    .map(|f| {
                        let new_val = self.process_qq_antiquots(&f.val)?;
                        Ok(SurfaceFieldAssign {
                            span: f.span,
                            name: f.name.clone(),
                            val: new_val,
                        })
                    })
                    .collect();
                Ok(SurfaceExpr::StructLit {
                    span: *span,
                    struct_type: new_struct_type,
                    base: new_base,
                    fields: new_fields?,
                })
            }

            // Projection - process base expression
            SurfaceExpr::Proj(span, base, proj) => {
                let new_base = self.process_qq_antiquots(base)?;
                Ok(SurfaceExpr::Proj(*span, Box::new(new_base), proj.clone()))
            }

            // Explicit (@) - process inner expression
            SurfaceExpr::Explicit(span, inner) => {
                let new_inner = self.process_qq_antiquots(inner)?;
                Ok(SurfaceExpr::Explicit(*span, Box::new(new_inner)))
            }

            // Leaf nodes - return unchanged
            SurfaceExpr::Ident(_, _)
            | SurfaceExpr::SyntheticSorry(_)
            | SurfaceExpr::Universe(_, _)
            | SurfaceExpr::Lit(_, _)
            | SurfaceExpr::Hole(_)
            | SurfaceExpr::NamedHole(_, _)
            | SurfaceExpr::SyntaxQuote(_, _) => Ok(expr.clone()),

            // LetRec - recursive let binding
            SurfaceExpr::LetRec(span, binder, val, body) => {
                let new_val = self.process_qq_antiquots(val)?;
                let new_body = self.process_qq_antiquots(body)?;
                Ok(SurfaceExpr::LetRec(
                    *span,
                    binder.clone(),
                    Box::new(new_val),
                    Box::new(new_body),
                ))
            }

            // LetPattern - pattern match in let binding
            SurfaceExpr::LetPattern(span, pattern, scrutinee, fallback, body) => {
                let new_scrutinee = self.process_qq_antiquots(scrutinee)?;
                let new_fallback = self.process_qq_antiquots(fallback)?;
                let new_body = self.process_qq_antiquots(body)?;
                // Note: pattern itself doesn't contain expressions, only the bound parts
                Ok(SurfaceExpr::LetPattern(
                    *span,
                    pattern.clone(),
                    Box::new(new_scrutinee),
                    Box::new(new_fallback),
                    Box::new(new_body),
                ))
            }

            // IfLet - if with pattern matching
            SurfaceExpr::IfLet(span, pattern, scrutinee, then_br, else_br) => {
                let new_scrutinee = self.process_qq_antiquots(scrutinee)?;
                let new_then = self.process_qq_antiquots(then_br)?;
                let new_else = self.process_qq_antiquots(else_br)?;
                Ok(SurfaceExpr::IfLet(
                    *span,
                    pattern.clone(),
                    Box::new(new_scrutinee),
                    Box::new(new_then),
                    Box::new(new_else),
                ))
            }

            // IfDecidable - if with decidability witness
            SurfaceExpr::IfDecidable(span, witness, prop, then_br, else_br) => {
                let new_prop = self.process_qq_antiquots(prop)?;
                let new_then = self.process_qq_antiquots(then_br)?;
                let new_else = self.process_qq_antiquots(else_br)?;
                Ok(SurfaceExpr::IfDecidable(
                    *span,
                    witness.clone(),
                    Box::new(new_prop),
                    Box::new(new_then),
                    Box::new(new_else),
                ))
            }

            // PatternMatchLambda - fun with pattern matching
            SurfaceExpr::PatternMatchLambda(span, binders, body) => {
                let new_body = self.process_qq_antiquots(body)?;
                Ok(SurfaceExpr::PatternMatchLambda(
                    *span,
                    binders.clone(),
                    Box::new(new_body),
                ))
            }

            // OutParam - output parameter marker
            SurfaceExpr::OutParam(span, inner) => {
                let new_inner = self.process_qq_antiquots(inner)?;
                Ok(SurfaceExpr::OutParam(*span, Box::new(new_inner)))
            }

            // SemiOutParam - semi-output parameter marker
            SurfaceExpr::SemiOutParam(span, inner) => {
                let new_inner = self.process_qq_antiquots(inner)?;
                Ok(SurfaceExpr::SemiOutParam(*span, Box::new(new_inner)))
            }

            // NamedArg - named argument in application
            SurfaceExpr::NamedArg(span, name, inner) => {
                let new_inner = self.process_qq_antiquots(inner)?;
                Ok(SurfaceExpr::NamedArg(
                    *span,
                    name.clone(),
                    Box::new(new_inner),
                ))
            }

            // UniverseInst - explicit universe instantiation
            // Universe levels don't contain antiquotations, but base expression might
            SurfaceExpr::UniverseInst(span, base, levels) => {
                let new_base = self.process_qq_antiquots(base)?;
                Ok(SurfaceExpr::UniverseInst(
                    *span,
                    Box::new(new_base),
                    levels.clone(),
                ))
            }

            // Tactic/calc/do blocks are opaque to antiquotation processing
            SurfaceExpr::ByTactic(_, _) | SurfaceExpr::CalcBlock(_, _) | SurfaceExpr::Do(_, _) => {
                Ok(expr.clone())
            }

            SurfaceExpr::LiftMethod(span, inner) => {
                let new_inner = self.process_qq_antiquots(inner)?;
                Ok(SurfaceExpr::LiftMethod(*span, Box::new(new_inner)))
            }

            // Interpolated strings are opaque to antiquotation processing;
            // sub-expressions were parsed at lex time and don't participate
            // in quotation splicing.
            SurfaceExpr::InterpolatedStr { .. } => Ok(expr.clone()),

            // `open X in <term>` - process antiquotations inside the sub-term,
            // preserving the opened namespaces and the `scoped` flag.
            SurfaceExpr::OpenIn {
                span,
                paths,
                scoped,
                body,
            } => {
                let new_body = self.process_qq_antiquots(body)?;
                Ok(SurfaceExpr::OpenIn {
                    span: *span,
                    paths: paths.clone(),
                    scoped: *scoped,
                    body: Box::new(new_body),
                })
            }
        })
    }
}
