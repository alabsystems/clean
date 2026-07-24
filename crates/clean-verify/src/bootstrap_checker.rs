// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minimal bootstrap checker for the closed kernel core.

use clean_kernel::{Environment, Expr, ExprKind, Level, TypeChecker, TypeError};
use std::collections::BTreeSet;

/// Trusted axioms that remain at the bootstrap boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TrustedAxiom {
    Prop,
    Sort,
    Pi,
    Lambda,
    App,
}

const TRUSTED_AXIOMS: [TrustedAxiom; 5] = [
    TrustedAxiom::Prop,
    TrustedAxiom::Sort,
    TrustedAxiom::Pi,
    TrustedAxiom::Lambda,
    TrustedAxiom::App,
];

/// Bootstrapping progress for a set of checked terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BootstrapStatus {
    FullyBootstrapped,
    PartiallyBootstrapped(Vec<TrustedAxiom>),
}

impl BootstrapStatus {
    #[must_use]
    pub fn is_fully_bootstrapped(&self) -> bool {
        matches!(self, Self::FullyBootstrapped)
    }
}

/// Result of checking the checker against its own sample corpus.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReflectionCheck {
    pub samples_checked: usize,
    pub samples_passed: usize,
    pub covered_axioms: Vec<TrustedAxiom>,
    pub status: BootstrapStatus,
}

impl ReflectionCheck {
    #[must_use]
    pub fn passed(&self) -> bool {
        self.samples_checked == self.samples_passed
    }
}

/// Bootstrap checker failures.
#[derive(Debug, thiserror::Error)]
pub enum BootstrapError {
    #[error("unsupported expression in bootstrap checker: {0}")]
    UnsupportedExpr(&'static str),
    #[error("unbound variable index: {0}")]
    UnboundVariable(u32),
    #[error("expected sort, got {0:?}")]
    ExpectedSort(Expr),
    #[error("expected function type, got {0:?}")]
    NotAFunction(Expr),
    #[error("type mismatch: expected {expected:?}, got {actual:?}")]
    TypeMismatch { expected: Expr, actual: Expr },
    #[error("kernel/bootstrap disagreement: kernel={kernel:?}, bootstrap={bootstrap:?}")]
    KernelDisagreement { kernel: Expr, bootstrap: Expr },
    #[error(transparent)]
    Kernel(#[from] TypeError),
}

#[derive(Debug, Default, Clone, Copy)]
pub struct BootstrapChecker;

#[derive(Debug)]
struct InferResult {
    ty: Expr,
    axioms: BTreeSet<TrustedAxiom>,
}

impl BootstrapChecker {
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    #[must_use]
    pub fn trusted_axioms(&self) -> &'static [TrustedAxiom] {
        &TRUSTED_AXIOMS
    }

    pub fn infer_type(&self, expr: &Expr) -> Result<Expr, BootstrapError> {
        Ok(self.infer_with_ctx(expr.strip_mdata(), &[] as &[Expr])?.ty)
    }

    pub fn recheck_inferred_type(
        &self,
        expr: &Expr,
        kernel_ty: &Expr,
    ) -> Result<(), BootstrapError> {
        let bootstrap_ty = self.infer_type(expr)?;
        if self.def_eq(&bootstrap_ty, kernel_ty) {
            Ok(())
        } else {
            Err(BootstrapError::KernelDisagreement {
                kernel: kernel_ty.clone(),
                bootstrap: bootstrap_ty,
            })
        }
    }

    pub fn recheck_kernel_inference(&self, expr: &Expr) -> Result<Expr, BootstrapError> {
        let env = Environment::new();
        let kernel_ty = TypeChecker::new(&env).infer_type(expr)?;
        self.recheck_inferred_type(expr, &kernel_ty)?;
        Ok(kernel_ty)
    }

    /// STEP FIDELITY (the (F) brick of the whnf reducer-universal composition):
    /// run the REAL kernel's `TypeChecker::whnf` on `expr`, independently reduce
    /// with this micro-checker's small code-independent `whnf` (beta + zeta over
    /// the fragment), and demand STRUCTURAL agreement of the weak-head normal
    /// forms. Where `recheck_kernel_inference` cross-checks the kernel's
    /// INFERENCE, this cross-checks its REDUCTION STEP — the literal
    /// `whnf_outer_loop` fixpoint machinery whose exits are MIR-witnessed in
    /// trust-certify — against an auditable model, on the bounded fragment.
    ///
    /// Structural equality (not `def_eq`) is deliberate: two correct weak-head
    /// reducers on this fragment must produce the SAME term (beta and zeta are
    /// deterministic; there are no consts to unfold and no alpha to vary a
    /// de-Bruijn representation), and a `def_eq` comparison would let the very
    /// reduction under test paper over a divergence.
    pub fn recheck_kernel_whnf(&self, expr: &Expr) -> Result<Expr, BootstrapError> {
        let env = Environment::new();
        let kernel_whnf = TypeChecker::new(&env).whnf(expr);
        let bootstrap_whnf = self.whnf(expr);
        if kernel_whnf == bootstrap_whnf {
            Ok(kernel_whnf)
        } else {
            Err(BootstrapError::KernelDisagreement {
                kernel: kernel_whnf,
                bootstrap: bootstrap_whnf,
            })
        }
    }

    pub fn status_for_terms(&self, terms: &[Expr]) -> Result<BootstrapStatus, BootstrapError> {
        let mut covered = BTreeSet::new();
        for term in terms {
            covered.extend(
                self.infer_with_ctx(term.strip_mdata(), &[] as &[Expr])?
                    .axioms,
            );
        }
        Ok(Self::status_from_coverage(&covered))
    }

    pub fn reflection_check(&self) -> Result<ReflectionCheck, BootstrapError> {
        let mut covered = BTreeSet::new();
        let samples = self.reflection_samples();
        let mut passed = 0;

        for sample in &samples {
            let inferred = self.infer_with_ctx(sample, &[] as &[Expr])?;
            covered.extend(inferred.axioms.iter().copied());
            self.recheck_inferred_type(sample, &inferred.ty)?;
            passed += 1;
        }

        Ok(ReflectionCheck {
            samples_checked: samples.len(),
            samples_passed: passed,
            covered_axioms: covered.iter().copied().collect(),
            status: Self::status_from_coverage(&covered),
        })
    }

    fn reflection_samples(&self) -> Vec<Expr> {
        vec![
            Expr::prop(),
            Expr::type_(),
            Expr::pi(
                clean_kernel::BinderInfo::Default,
                Expr::prop(),
                Expr::prop(),
            ),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                Expr::prop(),
                Expr::bvar(0),
            ),
            Expr::app(
                Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    Expr::type_(),
                    Expr::bvar(0),
                ),
                Expr::prop(),
            ),
        ]
    }

    fn status_from_coverage(covered: &BTreeSet<TrustedAxiom>) -> BootstrapStatus {
        let missing: Vec<_> = TRUSTED_AXIOMS
            .into_iter()
            .filter(|axiom| !covered.contains(axiom))
            .collect();
        if missing.is_empty() {
            BootstrapStatus::FullyBootstrapped
        } else {
            BootstrapStatus::PartiallyBootstrapped(missing)
        }
    }

    fn infer_with_ctx(&self, expr: &Expr, ctx: &[Expr]) -> Result<InferResult, BootstrapError> {
        match expr.kind() {
            ExprKind::BVar(idx) => {
                let idx = *idx;
                let depth = ctx.len();
                if (idx as usize) >= depth {
                    return Err(BootstrapError::UnboundVariable(idx));
                }
                let pos = depth - 1 - idx as usize;
                Ok(InferResult {
                    ty: ctx[pos].lift((depth - pos) as u32),
                    axioms: BTreeSet::new(),
                })
            }
            ExprKind::Sort(level) => {
                let mut axioms = BTreeSet::new();
                axioms.insert(if level.is_zero() {
                    TrustedAxiom::Prop
                } else {
                    TrustedAxiom::Sort
                });
                Ok(InferResult {
                    ty: Expr::sort(Level::succ(level.clone())),
                    axioms,
                })
            }
            ExprKind::Pi(_binder, arg_ty, body) => {
                let arg = self.infer_with_ctx(arg_ty.as_ref(), ctx)?;
                let arg_level = self.expect_sort(&arg.ty)?;
                let mut next_ctx = ctx.to_vec();
                next_ctx.push(arg_ty.as_ref().clone());
                let body_result = self.infer_with_ctx(body.as_ref(), &next_ctx)?;
                let body_level = self.expect_sort(&body_result.ty)?;

                let mut axioms = arg.axioms;
                axioms.extend(body_result.axioms);
                axioms.insert(TrustedAxiom::Pi);

                Ok(InferResult {
                    ty: Expr::sort(Level::imax(arg_level, body_level)),
                    axioms,
                })
            }
            ExprKind::Lam(binder, arg_ty, body) => {
                let arg = self.infer_with_ctx(arg_ty.as_ref(), ctx)?;
                let _ = self.expect_sort(&arg.ty)?;

                let mut next_ctx = ctx.to_vec();
                next_ctx.push(arg_ty.as_ref().clone());
                let body_result = self.infer_with_ctx(body.as_ref(), &next_ctx)?;

                let mut axioms = arg.axioms;
                axioms.extend(body_result.axioms);
                axioms.insert(TrustedAxiom::Lambda);

                Ok(InferResult {
                    ty: Expr::pi(*binder, arg_ty.as_ref().clone(), body_result.ty),
                    axioms,
                })
            }
            ExprKind::App(fun, arg) => {
                let fn_result = self.infer_with_ctx(fun.as_ref(), ctx)?;
                let arg_result = self.infer_with_ctx(arg.as_ref(), ctx)?;
                let fn_ty_whnf = self.whnf(&fn_result.ty);

                let ExprKind::Pi(_, expected_arg_ty, body_ty) = fn_ty_whnf.kind() else {
                    return Err(BootstrapError::NotAFunction(fn_ty_whnf));
                };

                if !self.def_eq(&arg_result.ty, expected_arg_ty.as_ref()) {
                    return Err(BootstrapError::TypeMismatch {
                        expected: expected_arg_ty.as_ref().clone(),
                        actual: arg_result.ty,
                    });
                }

                let mut axioms = fn_result.axioms;
                axioms.extend(arg_result.axioms);
                axioms.insert(TrustedAxiom::App);

                Ok(InferResult {
                    ty: body_ty.instantiate(arg.as_ref()),
                    axioms,
                })
            }
            ExprKind::MData(_, inner) => self.infer_with_ctx(inner.as_ref(), ctx),
            ExprKind::FVar(_) => Err(BootstrapError::UnsupportedExpr("FVar")),
            ExprKind::Const(_, _) => Err(BootstrapError::UnsupportedExpr("Const")),
            ExprKind::Let(_, ty, val, body, _) => {
                // Mirror of the kernel's Let rule (tc/infer.rs): the annotation
                // must be a sort, the value must have the annotated type, and
                // the let types as its zeta-expansion — the body with the value
                // substituted (kernel substitutes fvar -> val; on this closed
                // de Bruijn fragment instantiate is the same operation).
                let ty_result = self.infer_with_ctx(ty.as_ref(), ctx)?;
                let _ = self.expect_sort(&ty_result.ty)?;
                let val_result = self.infer_with_ctx(val.as_ref(), ctx)?;
                if !self.def_eq(&val_result.ty, ty.as_ref()) {
                    return Err(BootstrapError::TypeMismatch {
                        expected: ty.as_ref().clone(),
                        actual: val_result.ty,
                    });
                }
                let body_inst = body.instantiate(val.as_ref());
                let body_result = self.infer_with_ctx(&body_inst, ctx)?;
                let mut axioms = ty_result.axioms;
                axioms.extend(val_result.axioms);
                axioms.extend(body_result.axioms);
                Ok(InferResult {
                    ty: body_result.ty,
                    axioms,
                })
            }
            ExprKind::Lit(_) => Err(BootstrapError::UnsupportedExpr("Lit")),
            ExprKind::Proj(_, _, _) => Err(BootstrapError::UnsupportedExpr("Proj")),
            ExprKind::SProp => Err(BootstrapError::UnsupportedExpr("SProp")),
            ExprKind::Squash(_) => Err(BootstrapError::UnsupportedExpr("Squash")),
            ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1
            | ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. } => Err(BootstrapError::UnsupportedExpr("Cubical")),
            ExprKind::ZFCSet(_) | ExprKind::ZFCMem { .. } | ExprKind::ZFCComprehension { .. } => {
                Err(BootstrapError::UnsupportedExpr("ZFC"))
            }
        }
    }

    fn expect_sort(&self, ty: &Expr) -> Result<Level, BootstrapError> {
        match self.whnf(ty).kind() {
            ExprKind::Sort(level) => Ok(level.clone()),
            _ => Err(BootstrapError::ExpectedSort(ty.clone())),
        }
    }

    fn whnf(&self, expr: &Expr) -> Expr {
        match expr.strip_mdata().kind() {
            ExprKind::App(fun, arg) => {
                let fn_whnf = self.whnf(fun.as_ref());
                match fn_whnf.strip_mdata().kind() {
                    ExprKind::Lam(_, _, body) => self.whnf(&body.instantiate(arg.as_ref())),
                    _ => Expr::app(fn_whnf, arg.as_ref().clone()),
                }
            }
            // Zeta: `let x := v in b` weak-head-reduces to `b[x := v]` — the same
            // eager substitution this checker's Let INFERENCE already performs
            // (see `infer_with_ctx`'s Let arm), now applied at the whnf level so
            // the micro-checker's reduction agrees with the kernel's on the full
            // {Sort, BVar, App, Lam, Pi, Let} fragment (step-fidelity gate).
            ExprKind::Let(_, _, val, body, _) => self.whnf(&body.instantiate(val.as_ref())),
            _ => expr.strip_mdata().clone(),
        }
    }

    fn def_eq(&self, lhs: &Expr, rhs: &Expr) -> bool {
        let lhs = self.whnf(lhs);
        let rhs = self.whnf(rhs);
        self.def_eq_whnf(lhs.strip_mdata(), rhs.strip_mdata())
    }

    fn def_eq_whnf(&self, lhs: &Expr, rhs: &Expr) -> bool {
        match (lhs.kind(), rhs.kind()) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.def_eq(f1.as_ref(), f2.as_ref()) && self.def_eq(a1.as_ref(), a2.as_ref())
            }
            (ExprKind::Lam(_, ty1, body1), ExprKind::Lam(_, ty2, body2))
            | (ExprKind::Pi(_, ty1, body1), ExprKind::Pi(_, ty2, body2)) => {
                self.def_eq(ty1.as_ref(), ty2.as_ref())
                    && self.def_eq(body1.as_ref(), body2.as_ref())
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, ExprKind};

    #[test]
    fn infers_sort_and_prop() {
        let checker = BootstrapChecker::new();
        assert_eq!(checker.infer_type(&Expr::prop()).unwrap(), Expr::type_());
        assert!(matches!(
            checker.infer_type(&Expr::type_()).unwrap().kind(),
            ExprKind::Sort(_)
        ));
    }

    #[test]
    fn infers_pi_lambda_and_app() {
        let checker = BootstrapChecker::new();

        let pi = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());
        assert_eq!(checker.infer_type(&pi).unwrap(), Expr::type_());

        let lam = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        assert_eq!(checker.infer_type(&lam).unwrap(), pi);

        let app = Expr::app(
            Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
            Expr::prop(),
        );
        assert_eq!(checker.infer_type(&app).unwrap(), Expr::type_());
    }

    #[test]
    fn rechecks_kernel_inference_for_core_terms() {
        let checker = BootstrapChecker::new();
        let expr = Expr::app(
            Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
            Expr::prop(),
        );
        assert_eq!(
            checker.recheck_kernel_inference(&expr).unwrap(),
            Expr::type_()
        );
    }

    #[test]
    fn reports_partial_status_for_incomplete_coverage() {
        let checker = BootstrapChecker::new();
        let status = checker.status_for_terms(&[Expr::prop()]).unwrap();
        assert_eq!(
            status,
            BootstrapStatus::PartiallyBootstrapped(vec![
                TrustedAxiom::Sort,
                TrustedAxiom::Pi,
                TrustedAxiom::Lambda,
                TrustedAxiom::App,
            ])
        );
    }

    #[test]
    fn reflection_check_covers_all_bootstrap_axioms() {
        let checker = BootstrapChecker::new();
        let reflection = checker.reflection_check().unwrap();

        assert!(reflection.passed());
        assert_eq!(reflection.samples_checked, 5);
        assert_eq!(reflection.samples_passed, 5);
        assert_eq!(
            reflection.covered_axioms,
            vec![
                TrustedAxiom::Prop,
                TrustedAxiom::Sort,
                TrustedAxiom::Pi,
                TrustedAxiom::Lambda,
                TrustedAxiom::App,
            ]
        );
        assert_eq!(reflection.status, BootstrapStatus::FullyBootstrapped);
    }
}
