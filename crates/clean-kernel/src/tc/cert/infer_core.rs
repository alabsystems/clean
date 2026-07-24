// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core CIC type inference with certificates.
//!
//! Handles the standard Calculus of Inductive Constructions expression kinds:
//! BVar, FVar, Sort, Const, App, Lam, Pi, Let, Lit, Proj, MData.
//! Mode-specific expressions (Cubical, ZFC, Impredicative) are delegated
//! to `infer_modes.rs`.

use crate::cert::ProofCert;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::expr_location::ExprPathStep;
use crate::tc::infer::is_eager_reduce;
use crate::tc::TypeChecker;
use crate::TypeError;

use super::convert_fvar_cert_to_bvar;

impl<'env> TypeChecker<'env> {
    /// Inner implementation of type inference with certificates.
    pub(crate) fn infer_type_with_cert_inner(
        &self,
        e: &Expr,
    ) -> Result<(Expr, ProofCert), TypeError> {
        match &e.kind {
            ExprKind::BVar(idx) => {
                // BVar should have been replaced by FVar during elaboration
                Err(TypeError::UnboundVariable(*idx))
            }
            ExprKind::FVar(id) => {
                let ty = self
                    .ctx
                    .borrow()
                    .get(*id)
                    .map(|d| d.type_.clone())
                    .ok_or(TypeError::UnknownFVar(*id))?;
                let cert = ProofCert::FVar {
                    id: *id,
                    type_: Box::new(ty.clone()),
                };
                Ok((ty, cert))
            }
            ExprKind::Sort(l) => {
                // Lean 4 parity: when infer_only=false, validate level params.
                // Part of #3225.
                if !self.infer_only.get() {
                    self.check_level(l)?;
                }
                let result_ty = Expr::from_kind(ExprKind::Sort(Level::succ(l.clone())));
                let cert = ProofCert::Sort { level: l.clone() };
                Ok((result_ty, cert))
            }
            ExprKind::Const(name, levels) => {
                // Check level count before instantiation (#1277)
                let info = self
                    .env
                    .get_const(name)
                    .ok_or_else(|| TypeError::UnknownConst(name.clone()))?;
                if info.level_params.len() != levels.len() {
                    return Err(TypeError::LevelCountMismatch {
                        name: name.clone(),
                        expected: info.level_params.len(),
                        got: levels.len(),
                    });
                }

                // Lean 4 parity: when infer_only=false, check level params
                // and unsafe/partial safety. Part of #3225, #3226.
                if !self.infer_only.get() {
                    for l in levels {
                        self.check_level(l)?;
                    }
                    if !self.allow_unsafe && self.env.is_unsafe(name) {
                        return Err(TypeError::UnsafeDeclaration { name: name.clone() });
                    }
                    if !self.allow_partial && self.env.is_partial(name) {
                        return Err(TypeError::PartialDeclaration { name: name.clone() });
                    }
                }

                let ty = self
                    .env
                    .instantiate_type(name, levels)
                    .ok_or_else(|| TypeError::UnknownConst(name.clone()))?;
                let cert = ProofCert::Const {
                    name: name.clone(),
                    levels: levels.to_vec(),
                    type_: Box::new(ty.clone()),
                };
                Ok((ty, cert))
            }
            ExprKind::App(f, a) => {
                // #3425: thread expression-path breadcrumbs so TypeErrors under
                // nested App/Lam/Pi/Let carry an ExprLocation pointing at the
                // failing sub-expression.
                self.expr_loc_push(ExprPathStep::AppFn);
                // Track WW: memoize on the `Arc` child's stable identity so the
                // shared-`Arc` DAG produced by match lowering is walked once.
                let f_result = self.infer_type_with_cert_arc(f);
                self.expr_loc_pop();
                let (f_type, f_cert) = f_result?;
                let f_type_whnf = self.whnf_impl(&f_type);

                match &f_type_whnf.kind {
                    ExprKind::Pi(_, expected_arg_type, result_type) => {
                        // SOUNDNESS: infer the argument type in the CURRENT mode
                        // (infer_only stays false in check mode) so the argument's OWN
                        // sub-arguments are type-checked recursively. Forcing
                        // infer_only=true here skipped nested arg checks, which let an
                        // ill-typed coercion buried one application deep
                        // (`g (id False True.intro)`) be accepted as a proof of False.
                        self.expr_loc_push(ExprPathStep::AppArg);
                        let a_result = self.infer_type_with_cert_arc(a);
                        self.expr_loc_pop();
                        let (arg_type, arg_cert) = a_result?;

                        // Lean 4 parity: when infer_only=false (check mode),
                        // verify the argument type matches. When infer_only=true
                        // (infer_type mode), skip the check.
                        // Ref: type_checker.cpp:163-196 (infer_app)
                        if !self.infer_only.get() {
                            // Lean 4 parity: set eager_reduce when the argument is
                            // wrapped in `eagerReduce _ _`. Ref: type_checker.cpp:168-176
                            let prev_eager = self.eager_reduce.get();
                            if is_eager_reduce(a) {
                                self.eager_reduce.set(true);
                            }
                            // Cumulative subtyping (`is_le`) at this ascription
                            // point, in PARITY with the release fast path
                            // (`infer.rs` App-arg check): the argument's type
                            // must be a SUBTYPE of the expected domain.
                            // `is_le` == `is_def_eq` unless the Coq cumulative
                            // lane is enabled, so the Lean-faithful cert path
                            // is unchanged; without this the cfg(debug)
                            // cert path rejected Coq-lane terms the release
                            // path accepts (debug/release divergence).
                            let eq = self.is_le(&arg_type, expected_arg_type);
                            self.eager_reduce.set(prev_eager);

                            if !eq {
                                // Point at the argument position. Part of #3425.
                                self.expr_loc_push(ExprPathStep::AppArg);
                                let loc = self.expr_loc_snapshot();
                                self.expr_loc_pop();
                                return Err(TypeError::TypeMismatch {
                                    expected: Box::new(expected_arg_type.as_ref().clone()),
                                    inferred: Box::new(arg_type),
                                    location: loc,
                                });
                            }
                        }

                        // Substitute argument into result type
                        let result_ty = result_type.instantiate(a);

                        let cert = ProofCert::App {
                            fn_cert: Box::new(f_cert),
                            fn_type: Box::new(f_type_whnf.clone()),
                            arg_cert: Box::new(arg_cert),
                            result_type: Box::new(result_ty.clone()),
                        };

                        Ok((result_ty, cert))
                    }
                    _ => {
                        // Point at the function position of the offending App.
                        // Part of #3425.
                        self.expr_loc_push(ExprPathStep::AppFn);
                        let loc = self.expr_loc_snapshot();
                        self.expr_loc_pop();
                        Err(TypeError::NotAFunction {
                            ty: Box::new(f_type),
                            location: loc,
                        })
                    }
                }
            }
            ExprKind::Lam(bi, arg_type, body) => {
                // Infer arg type cert (always needed for the certificate).
                // #3425: breadcrumb into the lambda's binder type.
                self.expr_loc_push(ExprPathStep::LamType);
                let arg_type_result = self.infer_type_with_cert_impl(arg_type);
                self.expr_loc_pop();
                let (arg_sort, arg_type_cert) = arg_type_result?;
                // Lean 4 parity: when infer_only=true, skip the domain Sort
                // check. Lean 4's infer_lambda calls ensure_sort only when
                // infer_only=false (check mode). Part of #3223.
                if !self.infer_only.get() {
                    let arg_sort_whnf = self.whnf_impl(&arg_sort);
                    let ExprKind::Sort(_arg_level) = &arg_sort_whnf.kind else {
                        // Point at the binder type. Part of #3425.
                        self.expr_loc_push(ExprPathStep::LamType);
                        let loc = self.expr_loc_snapshot();
                        self.expr_loc_pop();
                        return Err(TypeError::ExpectedSort {
                            ty: Box::new(arg_sort),
                            location: loc,
                        });
                    };
                }

                // Add variable to context and infer body type
                let fvar_id = self.ctx_push(Name::anon(), arg_type.as_ref().clone(), *bi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                self.expr_loc_push(ExprPathStep::LamBody);
                let body_result = self.infer_type_with_cert_impl(&body_with_fvar);
                self.expr_loc_pop();
                let (body_type, body_cert_raw) = body_result?;
                self.ctx_pop();

                // Convert FVar certificates back to BVar certificates for the body
                let body_cert = convert_fvar_cert_to_bvar(body_cert_raw, fvar_id, 0);

                // Abstract back to get Pi type
                let body_type_abstract = body_type.abstract_fvar(fvar_id);
                let result_type = Expr::from_kind(ExprKind::Pi(
                    *bi,
                    arg_type.clone(),
                    body_type_abstract.into(),
                ));

                let cert = ProofCert::Lam {
                    binder_info: bi.info,
                    arg_type_cert: Box::new(arg_type_cert),
                    body_cert: Box::new(body_cert),
                    result_type: Box::new(result_type.clone()),
                };

                Ok((result_type, cert))
            }
            ExprKind::Pi(bi, arg_type, body) => {
                // Check arg_type is a type.
                // #3425: breadcrumb into the Pi's domain.
                self.expr_loc_push(ExprPathStep::PiDom);
                let dom_result = self.infer_type_with_cert_impl(arg_type);
                self.expr_loc_pop();
                let (arg_sort, arg_type_cert) = dom_result?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort);
                let ExprKind::Sort(l1) = &arg_sort_whnf.kind else {
                    self.expr_loc_push(ExprPathStep::PiDom);
                    let loc = self.expr_loc_snapshot();
                    self.expr_loc_pop();
                    return Err(TypeError::ExpectedSort {
                        ty: Box::new(arg_sort),
                        location: loc,
                    });
                };
                let l1 = l1.clone();

                // Add variable to context and check body is a type.
                // #3425: breadcrumb into the Pi's codomain.
                let fvar_id = self.ctx_push(Name::anon(), arg_type.as_ref().clone(), *bi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                self.expr_loc_push(ExprPathStep::PiBody);
                let body_result = self.infer_type_with_cert_impl(&body_with_fvar);
                self.expr_loc_pop();
                let (body_sort, body_type_cert_raw) = body_result?;
                self.ctx_pop();

                // Convert FVar certificates back to BVar certificates for the body
                let body_type_cert = convert_fvar_cert_to_bvar(body_type_cert_raw, fvar_id, 0);

                let body_sort_whnf = self.whnf_impl(&body_sort);
                let ExprKind::Sort(l2) = &body_sort_whnf.kind else {
                    self.expr_loc_push(ExprPathStep::PiBody);
                    let loc = self.expr_loc_snapshot();
                    self.expr_loc_pop();
                    return Err(TypeError::ExpectedSort {
                        ty: Box::new(body_sort),
                        location: loc,
                    });
                };
                let l2 = l2.clone();

                let result_level = Level::imax(l1.clone(), l2.clone());
                let result_type = Expr::from_kind(ExprKind::Sort(result_level));

                let cert = ProofCert::Pi {
                    binder_info: bi.info,
                    arg_type_cert: Box::new(arg_type_cert),
                    arg_level: l1,
                    body_type_cert: Box::new(body_type_cert),
                    body_level: l2,
                };

                Ok((result_type, cert))
            }
            ExprKind::Let(_, ty, val, body, _) => {
                // Always infer type and value certs for the certificate.
                // #3425: breadcrumb into the let-type annotation.
                self.expr_loc_push(ExprPathStep::LetType);
                let ty_result = self.infer_type_with_cert_impl(ty);
                self.expr_loc_pop();
                let (ty_sort, type_cert) = ty_result?;
                // SOUNDNESS: infer the let value's type in the CURRENT mode
                // (infer_only stays false in check mode) so the value's OWN nested
                // arguments are type-checked, mirroring the App-argument fix and the
                // fast path. Otherwise an ill-typed coercion in the let value slips
                // through, and the cert/micro cross-validator never sees it.
                self.expr_loc_push(ExprPathStep::LetVal);
                let val_result = self.infer_type_with_cert_impl(val);
                self.expr_loc_pop();
                let (_val_type, value_cert) = val_result?;

                // Lean 4 parity: when infer_only=false (check mode), verify
                // the type annotation is a Sort and the value matches it.
                // When infer_only=true, skip these checks.
                // Ref: type_checker.cpp:198-221 (infer_let)
                if !self.infer_only.get() {
                    let ty_sort_whnf = self.whnf_impl(&ty_sort);
                    match &ty_sort_whnf.kind {
                        ExprKind::Sort(_) => {}
                        _ => {
                            self.expr_loc_push(ExprPathStep::LetType);
                            let loc = self.expr_loc_snapshot();
                            self.expr_loc_pop();
                            return Err(TypeError::ExpectedSort {
                                ty: Box::new(ty_sort),
                                location: loc,
                            });
                        }
                    }

                    // Cumulative subtyping at the let-value ascription, in
                    // PARITY with the release fast path (`infer.rs` Let-val
                    // check). `is_le` == `is_def_eq` off the Coq lane.
                    if !self.is_le(&_val_type, ty) {
                        self.expr_loc_push(ExprPathStep::LetVal);
                        let loc = self.expr_loc_snapshot();
                        self.expr_loc_pop();
                        return Err(TypeError::TypeMismatch {
                            expected: Box::new(ty.as_ref().clone()),
                            inferred: Box::new(_val_type),
                            location: loc,
                        });
                    }
                }

                // Add let binding to context and infer body type.
                // #3425: breadcrumb into the let body.
                let fvar_id =
                    self.ctx_push_let(Name::anon(), ty.as_ref().clone(), val.as_ref().clone());
                let body_with_fvar = self.open_bvar(body, fvar_id);
                self.expr_loc_push(ExprPathStep::LetBody);
                let body_result = self.infer_type_with_cert_impl(&body_with_fvar);
                self.expr_loc_pop();
                let (body_type, body_cert_raw) = body_result?;
                self.ctx_pop();

                // Convert FVar certificates back to BVar certificates for the body
                let body_cert = convert_fvar_cert_to_bvar(body_cert_raw, fvar_id, 0);

                // Substitute FVar(fvar_id) → val directly (zeta-reduction).
                // Must use subst_fvar, not instantiate: after open_bvar, body_type
                // contains FVar(fvar_id), not BVar(0). instantiate would search for
                // BVar(0) and find nothing, leaking FVars into the result type.
                let result_type = body_type.subst_fvar(fvar_id, val);

                let cert = ProofCert::Let {
                    type_cert: Box::new(type_cert),
                    value_cert: Box::new(value_cert),
                    body_cert: Box::new(body_cert),
                    result_type: Box::new(result_type.clone()),
                };

                Ok((result_type, cert))
            }
            ExprKind::Lit(lit) => {
                let type_ = match lit {
                    crate::expr::Literal::Nat(_) => Expr::const_(super::NAME_NAT.clone(), vec![]),
                    crate::expr::Literal::String(_) => {
                        Expr::const_(super::NAME_STRING.clone(), vec![])
                    }
                };
                let cert = ProofCert::Lit {
                    lit: lit.clone(),
                    type_: Box::new(type_.clone()),
                };
                Ok((type_, cert))
            }
            ExprKind::Proj(struct_name, idx, e) => {
                // First get the type of the expression being projected.
                // #3425: breadcrumb into the projected expression.
                self.expr_loc_push(ExprPathStep::ProjExpr);
                let expr_result = self.infer_type_with_cert_impl(e);
                self.expr_loc_pop();
                let (expr_type, expr_cert) = expr_result?;

                // Get the field type using the pre-computed expr_type to avoid duplicate inference
                let field_type = self.infer_proj_type_from(struct_name, *idx, e, &expr_type)?;

                let cert = ProofCert::Proj {
                    struct_name: struct_name.clone(),
                    idx: *idx,
                    expr_cert: Box::new(expr_cert),
                    expr_type: Box::new(expr_type),
                    field_type: Box::new(field_type.clone()),
                };
                Ok((field_type, cert))
            }
            // MData is transparent - just infer the type of the inner expression
            // We wrap the certificate to preserve that it came from an MData
            ExprKind::MData(metadata, inner) => {
                // #3425: breadcrumb into the MData's inner expression.
                self.expr_loc_push(ExprPathStep::MDataExpr);
                let inner_result = self.infer_type_with_cert_impl(inner);
                self.expr_loc_pop();
                let (inner_type, inner_cert) = inner_result?;
                let cert = ProofCert::MData {
                    metadata: metadata.clone(),
                    inner_cert: Box::new(inner_cert),
                    result_type: Box::new(inner_type.clone()),
                };
                Ok((inner_type, cert))
            }

            // Mode-specific expressions — delegate to infer_modes.rs
            _ => self.infer_mode_specific_cert(e),
        }
    }
}
