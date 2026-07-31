// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Executable specification for the KExpr fragment used by issue #462.
//!
//! This models the algorithmic core over the spec's 6-constructor fragment:
//! `sort`, `bvar`, `app`, `lam`, `pi`, and `const`.

use clean_kernel::{Environment, Expr, ExprKind, Level, TypeError};

/// Definitional-equality procedures exposed by the spec.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefeqAlgorithm {
    StructuralEquality,
    AlphaEquivalence,
    BetaEtaEquivalence,
}

/// Successful typing steps for the KExpr fragment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeCheckStep {
    Sort,
    BoundVariable,
    Constant,
    Application,
    Lambda,
    Pi,
    Conversion,
}

/// Records why an algorithmic type check succeeded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletenessWitness {
    pub step: TypeCheckStep,
    pub expr: Expr,
    pub inferred_type: Expr,
    pub expected_type: Expr,
    pub defeq_algorithm: DefeqAlgorithm,
    pub premises: Vec<CompletenessWitness>,
}

impl CompletenessWitness {
    fn inferred(
        step: TypeCheckStep,
        expr: Expr,
        inferred_type: Expr,
        premises: Vec<CompletenessWitness>,
    ) -> Self {
        Self {
            step,
            expr,
            expected_type: inferred_type.clone(),
            inferred_type,
            defeq_algorithm: DefeqAlgorithm::BetaEtaEquivalence,
            premises,
        }
    }

    fn conversion(expr: Expr, inferred_type: Expr, expected_type: Expr, premise: Self) -> Self {
        Self {
            step: TypeCheckStep::Conversion,
            expr,
            inferred_type,
            expected_type,
            defeq_algorithm: DefeqAlgorithm::BetaEtaEquivalence,
            premises: vec![premise],
        }
    }
}

/// Check definitional equality according to the requested spec algorithm.
#[must_use]
pub fn check_defeq_spec(lhs: &Expr, rhs: &Expr, algorithm: DefeqAlgorithm) -> bool {
    match algorithm {
        DefeqAlgorithm::StructuralEquality => lhs == rhs,
        DefeqAlgorithm::AlphaEquivalence => alpha_equiv(lhs, rhs),
        DefeqAlgorithm::BetaEtaEquivalence => {
            alpha_equiv(lhs, rhs) || normalize_beta_eta(lhs) == normalize_beta_eta(rhs)
        }
    }
}

/// Check `expr : expected` in the KExpr fragment and return a success witness.
pub fn check_type_spec(
    env: &Environment,
    ctx: &[Expr],
    expr: &Expr,
    expected: &Expr,
) -> Result<CompletenessWitness, TypeError> {
    let witness = infer_type_spec(env, ctx, expr)?;
    if witness.inferred_type == *expected {
        return Ok(CompletenessWitness {
            expected_type: expected.clone(),
            ..witness
        });
    }
    if check_defeq_spec(
        &witness.inferred_type,
        expected,
        DefeqAlgorithm::BetaEtaEquivalence,
    ) {
        return Ok(CompletenessWitness::conversion(
            expr.clone(),
            witness.inferred_type.clone(),
            expected.clone(),
            witness,
        ));
    }
    Err(TypeError::TypeMismatch {
        expected: Box::new(expected.clone()),
        inferred: Box::new(witness.inferred_type),
        location: None,
    })
}

fn infer_type_spec(
    env: &Environment,
    ctx: &[Expr],
    expr: &Expr,
) -> Result<CompletenessWitness, TypeError> {
    match expr.kind() {
        ExprKind::Sort(level) => Ok(CompletenessWitness::inferred(
            TypeCheckStep::Sort,
            expr.clone(),
            Expr::sort(Level::succ(level.clone())),
            vec![],
        )),
        ExprKind::BVar(idx) => {
            let ty = ctx
                .get(*idx as usize)
                .cloned()
                .ok_or(TypeError::UnboundVariable(*idx))?;
            Ok(CompletenessWitness::inferred(
                TypeCheckStep::BoundVariable,
                expr.clone(),
                ty,
                vec![],
            ))
        }
        ExprKind::Const(name, levels) => {
            let info = env
                .get_const(name)
                .ok_or_else(|| TypeError::UnknownConst(name.clone()))?;
            if info.level_params.len() != levels.len() {
                return Err(TypeError::LevelCountMismatch {
                    name: name.clone(),
                    expected: info.level_params.len(),
                    got: levels.len(),
                });
            }
            let ty = env
                .instantiate_type(name, levels)
                .ok_or_else(|| TypeError::UnknownConst(name.clone()))?;
            Ok(CompletenessWitness::inferred(
                TypeCheckStep::Constant,
                expr.clone(),
                ty,
                vec![],
            ))
        }
        ExprKind::App(fun, arg) => {
            let fun_witness = infer_type_spec(env, ctx, fun)?;
            let arg_witness = infer_type_spec(env, ctx, arg)?;
            let fun_type = fun_witness.inferred_type.clone();
            let fun_type_nf = normalize_beta_eta(&fun_type);
            let ExprKind::Pi(_, domain, codomain) = fun_type_nf.kind() else {
                return Err(TypeError::NotAFunction {
                    ty: Box::new(fun_type),
                    location: None,
                });
            };
            if !check_defeq_spec(
                &arg_witness.inferred_type,
                domain,
                DefeqAlgorithm::BetaEtaEquivalence,
            ) {
                return Err(TypeError::TypeMismatch {
                    expected: Box::new(domain.as_ref().clone()),
                    inferred: Box::new(arg_witness.inferred_type.clone()),
                    location: None,
                });
            }
            Ok(CompletenessWitness::inferred(
                TypeCheckStep::Application,
                expr.clone(),
                codomain.instantiate(arg),
                vec![fun_witness, arg_witness],
            ))
        }
        ExprKind::Lam(binder, ty, body) => {
            let ty_witness = infer_type_spec(env, ctx, ty)?;
            let _ = ensure_sort(&ty_witness.inferred_type)?;
            let extended_ctx = extend_context(ctx, ty.as_ref().clone());
            let body_witness = infer_type_spec(env, &extended_ctx, body)?;
            Ok(CompletenessWitness::inferred(
                TypeCheckStep::Lambda,
                expr.clone(),
                Expr::pi(
                    *binder,
                    ty.as_ref().clone(),
                    body_witness.inferred_type.clone(),
                ),
                vec![ty_witness, body_witness],
            ))
        }
        ExprKind::Pi(binder, ty, body) => {
            let ty_witness = infer_type_spec(env, ctx, ty)?;
            let domain_level = ensure_sort(&ty_witness.inferred_type)?;
            let extended_ctx = extend_context(ctx, ty.as_ref().clone());
            let body_witness = infer_type_spec(env, &extended_ctx, body)?;
            let codomain_level = ensure_sort(&body_witness.inferred_type)?;
            Ok(CompletenessWitness::inferred(
                TypeCheckStep::Pi,
                expr.clone(),
                Expr::sort(Level::imax(domain_level, codomain_level)),
                vec![ty_witness, body_witness],
            ))
        }
        _ => Err(TypeError::ModeRequired {
            feature: "check_type_spec KExpr executable fragment".to_string(),
            mode: "sort/bvar/app/lam/pi/const expressions".to_string(),
        }),
    }
}

fn alpha_equiv(lhs: &Expr, rhs: &Expr) -> bool {
    match (lhs.kind(), rhs.kind()) {
        (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
        (ExprKind::BVar(i1), ExprKind::BVar(i2)) => i1 == i2,
        (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => n1 == n2 && ls1 == ls2,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            alpha_equiv(f1, f2) && alpha_equiv(a1, a2)
        }
        (ExprKind::Lam(b1, ty1, body1), ExprKind::Lam(b2, ty2, body2))
        | (ExprKind::Pi(b1, ty1, body1), ExprKind::Pi(b2, ty2, body2)) => {
            b1 == b2 && alpha_equiv(ty1, ty2) && alpha_equiv(body1, body2)
        }
        _ => false,
    }
}

fn normalize_beta_eta(expr: &Expr) -> Expr {
    match expr.kind() {
        ExprKind::Sort(_) | ExprKind::BVar(_) | ExprKind::Const(_, _) => expr.clone(),
        ExprKind::App(fun, arg) => {
            let fun_nf = normalize_beta_eta(fun);
            let arg_nf = normalize_beta_eta(arg);
            if let ExprKind::Lam(_, _, body) = fun_nf.kind() {
                normalize_beta_eta(&body.instantiate(&arg_nf))
            } else {
                Expr::app(fun_nf, arg_nf)
            }
        }
        ExprKind::Lam(binder, ty, body) => {
            let lambda = Expr::lam(*binder, normalize_beta_eta(ty), normalize_beta_eta(body));
            eta_contract(lambda)
        }
        ExprKind::Pi(binder, ty, body) => {
            Expr::pi(*binder, normalize_beta_eta(ty), normalize_beta_eta(body))
        }
        _ => expr.clone(),
    }
}

fn eta_contract(expr: Expr) -> Expr {
    let ExprKind::Lam(_, _, body) = expr.kind() else {
        return expr;
    };
    let ExprKind::App(fun, arg) = body.kind() else {
        return expr;
    };
    if matches!(arg.kind(), ExprKind::BVar(0)) && !fun.has_loose_bvar(0) {
        normalize_beta_eta(&fun.instantiate(&Expr::bvar(0)))
    } else {
        expr
    }
}

fn ensure_sort(expr: &Expr) -> Result<Level, TypeError> {
    let normalized = normalize_beta_eta(expr);
    match normalized.kind() {
        ExprKind::Sort(level) => Ok(level.clone()),
        _ => Err(TypeError::ExpectedSort {
            ty: Box::new(expr.clone()),
            location: None,
        }),
    }
}

fn extend_context(ctx: &[Expr], ty: Expr) -> Vec<Expr> {
    let mut extended = Vec::with_capacity(ctx.len() + 1);
    extended.push(ty);
    extended.extend_from_slice(ctx);
    extended
}
