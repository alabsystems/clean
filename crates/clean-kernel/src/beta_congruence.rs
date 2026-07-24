// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Binder congruence constructors for deep WHNF confluence.
//!
//! WHNF does not reduce under binders, but definitional equality must see
//! through binder congruences. This module provides explicit constructors
//! and a reduction function for Pi, Lambda, and Let congruence steps.
//!
//! Part of #2859.

use crate::env::Environment;
use crate::expr::{stack_safe, BinderData, Expr, ExprKind};
use crate::name::Name;
use std::{fmt, sync::Arc};

/// Binder congruence step — records how a binder was reduced through its
/// sub-expressions without changing the binder structure.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum BetaReduces {
    /// Reduction in a lambda type annotation.
    LamType(Box<BetaReduces>),
    /// Reduction in a lambda body.
    LamBody(Box<BetaReduces>),
    /// Reduction in a Pi domain.
    PiDomain(Box<BetaReduces>),
    /// Reduction in a Pi codomain.
    PiCodomain(Box<BetaReduces>),
    /// `Pi(bd, A, B) -> Pi(bd, A', B')` where `A ->* A'` and `B ->* B'`.
    PiCongr {
        binder: BinderData,
        domain_orig: Expr,
        domain_reduced: Expr,
        body_orig: Expr,
        body_reduced: Expr,
    },
    /// `Lam(bd, A, b) -> Lam(bd, A', b')` where `A ->* A'` and `b ->* b'`.
    LamCongr {
        binder: BinderData,
        param_ty_orig: Expr,
        param_ty_reduced: Expr,
        body_orig: Expr,
        body_reduced: Expr,
    },
    /// `Let(n, A, v, b, nd) -> Let(n, A', v', b', nd)`.
    LetCongr {
        name: Name,
        ty_orig: Expr,
        ty_reduced: Expr,
        val_orig: Expr,
        val_reduced: Expr,
        body_orig: Expr,
        body_reduced: Expr,
        non_dep: bool,
    },
}

/// Back-compat alias for earlier local naming in the kernel crate.
pub(crate) type BetaCongruence = BetaReduces;

impl BetaReduces {
    /// Whether all sub-expressions are identical to their originals.
    #[must_use]
    pub(crate) fn is_identity(&self) -> bool {
        match self {
            Self::LamType(inner)
            | Self::LamBody(inner)
            | Self::PiDomain(inner)
            | Self::PiCodomain(inner) => inner.is_identity(),
            Self::PiCongr {
                domain_orig,
                domain_reduced,
                body_orig,
                body_reduced,
                ..
            } => domain_orig == domain_reduced && body_orig == body_reduced,
            Self::LamCongr {
                param_ty_orig,
                param_ty_reduced,
                body_orig,
                body_reduced,
                ..
            } => param_ty_orig == param_ty_reduced && body_orig == body_reduced,
            Self::LetCongr {
                ty_orig,
                ty_reduced,
                val_orig,
                val_reduced,
                body_orig,
                body_reduced,
                ..
            } => ty_orig == ty_reduced && val_orig == val_reduced && body_orig == body_reduced,
        }
    }

    /// Build the source expression from this congruence step.
    pub(crate) fn source(&self) -> Expr {
        match self {
            Self::LamType(inner)
            | Self::LamBody(inner)
            | Self::PiDomain(inner)
            | Self::PiCodomain(inner) => inner.source(),
            Self::PiCongr {
                binder,
                domain_orig,
                body_orig,
                ..
            } => Expr::pi(*binder, domain_orig.clone(), body_orig.clone()),
            Self::LamCongr {
                binder,
                param_ty_orig,
                body_orig,
                ..
            } => Expr::lam(*binder, param_ty_orig.clone(), body_orig.clone()),
            Self::LetCongr {
                name,
                ty_orig,
                val_orig,
                body_orig,
                non_dep,
                ..
            } => Expr::let_named(
                name.clone(),
                ty_orig.clone(),
                val_orig.clone(),
                body_orig.clone(),
                *non_dep,
            ),
        }
    }

    /// Build the target expression from this congruence step.
    pub(crate) fn target(&self) -> Expr {
        match self {
            Self::LamType(inner)
            | Self::LamBody(inner)
            | Self::PiDomain(inner)
            | Self::PiCodomain(inner) => inner.target(),
            Self::PiCongr {
                binder,
                domain_reduced,
                body_reduced,
                ..
            } => Expr::pi(*binder, domain_reduced.clone(), body_reduced.clone()),
            Self::LamCongr {
                binder,
                param_ty_reduced,
                body_reduced,
                ..
            } => Expr::lam(*binder, param_ty_reduced.clone(), body_reduced.clone()),
            Self::LetCongr {
                name,
                ty_reduced,
                val_reduced,
                body_reduced,
                non_dep,
                ..
            } => Expr::let_named(
                name.clone(),
                ty_reduced.clone(),
                val_reduced.clone(),
                body_reduced.clone(),
                *non_dep,
            ),
        }
    }

    /// Build the reduced expression from this congruence step.
    pub(crate) fn reduced_expr(&self) -> Expr {
        self.target()
    }

    /// Build the original expression from this congruence step.
    pub(crate) fn original_expr(&self) -> Expr {
        self.source()
    }
}

impl fmt::Display for BetaReduces {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LamType(inner) => write!(f, "LamType({inner})"),
            Self::LamBody(inner) => write!(f, "LamBody({inner})"),
            Self::PiDomain(inner) => write!(f, "PiDomain({inner})"),
            Self::PiCodomain(inner) => write!(f, "PiCodomain({inner})"),
            Self::PiCongr { .. } => write!(f, "PiCongr({} -> {})", self.source(), self.target()),
            Self::LamCongr { .. } => {
                write!(f, "LamCongr({} -> {})", self.source(), self.target())
            }
            Self::LetCongr { .. } => {
                write!(f, "LetCongr({} -> {})", self.source(), self.target())
            }
        }
    }
}

/// Try to reduce through a binder by reducing its sub-expressions.
///
/// Returns `Some(BetaCongruence)` if `expr` is a Pi/Lam/Let and at least one
/// sub-expression reduced. `None` otherwise.
///
/// ENSURES: If `Some(congr)`, then `congr.reduced_expr()` is definitionally
///          equal to `expr`.
#[must_use]
pub(crate) fn reduce_binder_congruence(expr: &Expr, env: &Environment) -> Option<BetaReduces> {
    match expr.kind() {
        ExprKind::Pi(bd, domain, body) => reduce_pi(*bd, domain, body, env),
        ExprKind::Lam(bd, ty, body) => reduce_lam(*bd, ty, body, env),
        ExprKind::Let(name, ty, val, body, non_dep) => {
            let val_reduced = try_deep_reduce(val, env);
            reduce_let(name, ty, val, val_reduced, body, *non_dep, env)
        }
        _ => None,
    }
}

/// Shared binder-part reducer for Pi/Lam congruence builders.
fn reduce_binder_parts(
    ty: &Arc<Expr>,
    body: &Arc<Expr>,
    env: &Environment,
) -> Option<(Expr, Option<Expr>, Expr, Option<Expr>)> {
    let ty_red = try_deep_reduce(ty, env);
    let body_red = try_deep_reduce(body, env);
    if ty_red.is_none() && body_red.is_none() {
        return None;
    }
    let ty_orig = (**ty).clone();
    let body_orig = (**body).clone();
    Some((ty_orig, ty_red, body_orig, body_red))
}

/// Pi congruence builder.
fn reduce_pi(
    bd: BinderData,
    domain: &Arc<Expr>,
    body: &Arc<Expr>,
    env: &Environment,
) -> Option<BetaReduces> {
    let (domain_orig, domain_reduced, body_orig, body_reduced) =
        reduce_binder_parts(domain, body, env)?;
    let domain_changed = domain_reduced.is_some();
    let body_changed = body_reduced.is_some();
    let congr = BetaReduces::PiCongr {
        binder: bd,
        domain_orig: domain_orig.clone(),
        domain_reduced: domain_reduced.unwrap_or_else(|| domain_orig.clone()),
        body_orig: body_orig.clone(),
        body_reduced: body_reduced.unwrap_or_else(|| body_orig.clone()),
    };
    Some(match (domain_changed, body_changed) {
        (true, false) => BetaReduces::PiDomain(Box::new(congr)),
        (false, true) => BetaReduces::PiCodomain(Box::new(congr)),
        (true, true) => congr,
        (false, false) => unreachable!("reduce_binder_parts filtered the identity case"),
    })
}

/// Lambda congruence builder.
fn reduce_lam(
    bd: BinderData,
    ty: &Arc<Expr>,
    body: &Arc<Expr>,
    env: &Environment,
) -> Option<BetaReduces> {
    let (param_ty_orig, param_ty_reduced, body_orig, body_reduced) =
        reduce_binder_parts(ty, body, env)?;
    let ty_changed = param_ty_reduced.is_some();
    let body_changed = body_reduced.is_some();
    let congr = BetaReduces::LamCongr {
        binder: bd,
        param_ty_orig: param_ty_orig.clone(),
        param_ty_reduced: param_ty_reduced.unwrap_or_else(|| param_ty_orig.clone()),
        body_orig: body_orig.clone(),
        body_reduced: body_reduced.unwrap_or_else(|| body_orig.clone()),
    };
    Some(match (ty_changed, body_changed) {
        (true, false) => BetaReduces::LamType(Box::new(congr)),
        (false, true) => BetaReduces::LamBody(Box::new(congr)),
        (true, true) => congr,
        (false, false) => unreachable!("reduce_binder_parts filtered the identity case"),
    })
}

/// Let congruence builder.
fn reduce_let(
    name: &Name,
    ty: &Arc<Expr>,
    val: &Arc<Expr>,
    val_reduced: Option<Expr>,
    body: &Arc<Expr>,
    non_dep: bool,
    env: &Environment,
) -> Option<BetaReduces> {
    let ty_red = try_deep_reduce(ty, env);
    let body_red = try_deep_reduce(body, env);
    if ty_red.is_none() && val_reduced.is_none() && body_red.is_none() {
        return None;
    }
    let ty_o = (**ty).clone();
    let val_o = (**val).clone();
    let body_o = (**body).clone();
    Some(BetaReduces::LetCongr {
        name: name.clone(),
        ty_orig: ty_o.clone(),
        ty_reduced: ty_red.unwrap_or(ty_o),
        val_orig: val_o.clone(),
        val_reduced: val_reduced.unwrap_or(val_o),
        body_orig: body_o.clone(),
        body_reduced: body_red.unwrap_or(body_o),
        non_dep,
    })
}

/// Delta-reduce a single expression (unfold head constant at default transparency).
fn try_delta_reduce(expr: &Expr, env: &Environment) -> Option<Expr> {
    if let ExprKind::Const(name, levels) = expr.kind() {
        return env.unfold_with_transparency(name, levels, crate::env::TransparencyMode::Default);
    }
    let head = expr.get_app_fn();
    if let ExprKind::Const(name, levels) = head.kind() {
        if let Some(unfolded) =
            env.unfold_with_transparency(name, levels, crate::env::TransparencyMode::Default)
        {
            let args = expr.get_app_args();
            return Some(
                args.iter()
                    .fold(unfolded, |acc, a| Expr::app(acc, (*a).clone())),
            );
        }
    }
    None
}

/// Deep single-step reduction: delta, beta, zeta, then recurse into sub-exprs.
/// Stack-safe via `stacker::maybe_grow`.
fn try_deep_reduce(expr: &Expr, env: &Environment) -> Option<Expr> {
    stack_safe(|| try_deep_reduce_inner(expr, env))
}

fn try_deep_reduce_inner(expr: &Expr, env: &Environment) -> Option<Expr> {
    if let Some(r) = try_delta_reduce(expr, env) {
        return Some(r);
    }
    // Beta: (lam _ body) arg -> body[arg/x]
    if let ExprKind::App(f, a) = expr.kind() {
        if let ExprKind::Lam(_, _, body) = f.kind() {
            return Some(body.instantiate(a));
        }
    }
    // Zeta: let _ := val in body -> body[val/x]
    if let ExprKind::Let(_, _, val, body, _) = expr.kind() {
        return Some(body.instantiate(val));
    }
    // Recurse into sub-expressions.
    match expr.kind() {
        ExprKind::App(f, a) => try_deep_reduce(f, env)
            .map(|r| Expr::app(r, (**a).clone()))
            .or_else(|| try_deep_reduce(a, env).map(|r| Expr::app((**f).clone(), r))),
        ExprKind::Pi(bd, d, b) => try_deep_reduce(d, env)
            .map(|r| Expr::pi(*bd, r, (**b).clone()))
            .or_else(|| try_deep_reduce(b, env).map(|r| Expr::pi(*bd, (**d).clone(), r))),
        ExprKind::Lam(bd, t, b) => try_deep_reduce(t, env)
            .map(|r| Expr::lam(*bd, r, (**b).clone()))
            .or_else(|| try_deep_reduce(b, env).map(|r| Expr::lam(*bd, (**t).clone(), r))),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{BinderInfo, Expr};
    use crate::level::Level;

    fn env() -> Environment {
        Environment::new()
    }
    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }
    fn type1() -> Expr {
        Expr::sort(Level::succ(Level::zero()))
    }
    fn id_lam() -> Expr {
        Expr::lam(BinderInfo::Default, prop(), Expr::bvar(0))
    }
    fn const_lam(ret: Expr) -> Expr {
        Expr::lam(BinderInfo::Default, prop(), ret)
    }

    #[test]
    fn test_non_binder_returns_none() {
        let e = env();
        assert!(reduce_binder_congruence(&Expr::bvar(0), &e).is_none());
        assert!(reduce_binder_congruence(&prop(), &e).is_none());
        assert!(reduce_binder_congruence(&Expr::app(Expr::bvar(0), Expr::bvar(1)), &e).is_none());
    }

    #[test]
    fn test_irreducible_binders_return_none() {
        let e = env();
        let pi = Expr::pi(BinderInfo::Default, prop(), Expr::bvar(0));
        assert!(reduce_binder_congruence(&pi, &e).is_none());
        let lam = Expr::lam(BinderInfo::Default, prop(), Expr::bvar(0));
        assert!(reduce_binder_congruence(&lam, &e).is_none());
        let lt = Expr::let_named(Name::anon(), prop(), Expr::bvar(0), Expr::bvar(0), false);
        assert!(reduce_binder_congruence(&lt, &e).is_none());
    }

    #[test]
    fn test_pi_beta_in_domain() {
        let e = env();
        let domain = Expr::app(id_lam(), prop()); // (lam x. x) Prop -> Prop
        let body = Expr::bvar(0);
        let pi = Expr::pi(BinderInfo::Default, domain.clone(), body.clone());
        let congr = reduce_binder_congruence(&pi, &e).expect("should reduce");
        assert!(!congr.is_identity());
        match &congr {
            BetaCongruence::PiDomain(inner) => match inner.as_ref() {
                BetaCongruence::PiCongr {
                    domain_orig,
                    domain_reduced,
                    body_reduced,
                    ..
                } => {
                    assert_eq!(domain_orig, &domain);
                    assert_eq!(domain_reduced, &prop());
                    assert_eq!(body_reduced, &body);
                }
                _ => panic!("expected wrapped PiCongr"),
            },
            _ => panic!("expected PiDomain"),
        }
        assert_eq!(
            congr.reduced_expr(),
            Expr::pi(BinderInfo::Default, prop(), body)
        );
    }

    #[test]
    fn test_lam_beta_in_body() {
        let e = env();
        let body = Expr::app(id_lam(), Expr::bvar(0)); // (lam y. y) (BVar 0) -> BVar 0
        let lam = Expr::lam(BinderInfo::Default, prop(), body.clone());
        let congr = reduce_binder_congruence(&lam, &e).expect("should reduce");
        match &congr {
            BetaCongruence::LamBody(inner) => match inner.as_ref() {
                BetaCongruence::LamCongr {
                    body_orig,
                    body_reduced,
                    param_ty_reduced,
                    ..
                } => {
                    assert_eq!(body_orig, &body);
                    assert_eq!(body_reduced, &Expr::bvar(0));
                    assert_eq!(param_ty_reduced, &prop());
                }
                _ => panic!("expected wrapped LamCongr"),
            },
            _ => panic!("expected LamBody"),
        }
    }

    #[test]
    fn test_let_zeta_in_value() {
        let e = env();
        let inner_let = Expr::let_named(Name::anon(), prop(), prop(), Expr::bvar(0), false);
        let lt = Expr::let_named(
            Name::from_string("x"),
            prop(),
            inner_let.clone(),
            Expr::bvar(0),
            false,
        );
        let congr = reduce_binder_congruence(&lt, &e).expect("should reduce");
        match &congr {
            BetaCongruence::LetCongr {
                val_orig,
                val_reduced,
                name,
                ..
            } => {
                assert_eq!(*name, Name::from_string("x"));
                assert_eq!(val_orig, &inner_let);
                assert_eq!(val_reduced, &prop());
            }
            _ => panic!("expected LetCongr"),
        }
    }

    #[test]
    fn test_pi_both_domain_and_body_reduced() {
        let e = env();
        let domain = Expr::app(const_lam(prop()), prop());
        let body = Expr::app(const_lam(type1()), prop());
        let pi = Expr::pi(BinderInfo::Default, domain, body);
        let congr = reduce_binder_congruence(&pi, &e).expect("should reduce both");
        match &congr {
            BetaCongruence::PiCongr {
                domain_reduced,
                body_reduced,
                ..
            } => {
                assert_eq!(domain_reduced, &prop());
                assert_eq!(body_reduced, &type1());
            }
            _ => panic!("expected PiCongr"),
        }
    }

    #[test]
    fn test_identity_detection() {
        let d = prop();
        let b = Expr::bvar(0);
        let id = BetaCongruence::PiCongr {
            binder: BinderInfo::Default.into(),
            domain_orig: d.clone(),
            domain_reduced: d.clone(),
            body_orig: b.clone(),
            body_reduced: b.clone(),
        };
        assert!(id.is_identity());
        let non_id = BetaCongruence::PiCongr {
            binder: BinderInfo::Default.into(),
            domain_orig: d.clone(),
            domain_reduced: type1(),
            body_orig: b.clone(),
            body_reduced: b,
        };
        assert!(!non_id.is_identity());
    }

    #[test]
    fn test_wrapper_identity_source_target_and_display() {
        let inner = BetaCongruence::LamCongr {
            binder: BinderInfo::Default.into(),
            param_ty_orig: prop(),
            param_ty_reduced: prop(),
            body_orig: Expr::bvar(0),
            body_reduced: Expr::bvar(0),
        };
        let congr = BetaCongruence::LamType(Box::new(inner));
        assert!(congr.is_identity());
        assert_eq!(
            congr.source(),
            Expr::lam(BinderInfo::Default, prop(), Expr::bvar(0))
        );
        assert_eq!(
            congr.target(),
            Expr::lam(BinderInfo::Default, prop(), Expr::bvar(0))
        );
        assert!(format!("{congr}").contains("LamType"));
    }

    #[test]
    fn test_lam_beta_in_type_returns_lam_type() {
        let e = env();
        let ty = Expr::app(id_lam(), prop());
        let lam = Expr::lam(BinderInfo::Default, ty.clone(), Expr::bvar(0));
        let congr = reduce_binder_congruence(&lam, &e).expect("should reduce");
        match &congr {
            BetaCongruence::LamType(inner) => match inner.as_ref() {
                BetaCongruence::LamCongr {
                    param_ty_orig,
                    param_ty_reduced,
                    body_reduced,
                    ..
                } => {
                    assert_eq!(param_ty_orig, &ty);
                    assert_eq!(param_ty_reduced, &prop());
                    assert_eq!(body_reduced, &Expr::bvar(0));
                }
                _ => panic!("expected wrapped LamCongr"),
            },
            _ => panic!("expected LamType"),
        }
    }

    #[test]
    fn test_pi_beta_in_body_returns_pi_codomain() {
        let e = env();
        let body = Expr::app(id_lam(), Expr::bvar(0));
        let pi = Expr::pi(BinderInfo::Default, prop(), body.clone());
        let congr = reduce_binder_congruence(&pi, &e).expect("should reduce");
        match &congr {
            BetaCongruence::PiCodomain(inner) => match inner.as_ref() {
                BetaCongruence::PiCongr {
                    domain_reduced,
                    body_orig,
                    body_reduced,
                    ..
                } => {
                    assert_eq!(domain_reduced, &prop());
                    assert_eq!(body_orig, &body);
                    assert_eq!(body_reduced, &Expr::bvar(0));
                }
                _ => panic!("expected wrapped PiCongr"),
            },
            _ => panic!("expected PiCodomain"),
        }
    }

    #[test]
    fn test_original_and_reduced_expr_round_trip() {
        let congr = BetaCongruence::LamCongr {
            binder: BinderInfo::Default.into(),
            param_ty_orig: prop(),
            param_ty_reduced: type1(),
            body_orig: Expr::bvar(0),
            body_reduced: Expr::bvar(1),
        };
        assert_eq!(
            congr.original_expr(),
            Expr::lam(BinderInfo::Default, prop(), Expr::bvar(0))
        );
        assert_eq!(
            congr.source(),
            Expr::lam(BinderInfo::Default, prop(), Expr::bvar(0))
        );
        assert_eq!(
            congr.reduced_expr(),
            Expr::lam(BinderInfo::Default, type1(), Expr::bvar(1))
        );
        assert_eq!(
            congr.target(),
            Expr::lam(BinderInfo::Default, type1(), Expr::bvar(1))
        );
    }

    #[test]
    fn test_try_deep_reduce_beta_and_zeta() {
        let e = env();
        let beta = Expr::app(id_lam(), prop());
        assert_eq!(try_deep_reduce(&beta, &e).unwrap(), prop());
        let zeta = Expr::let_named(Name::anon(), prop(), prop(), Expr::bvar(0), false);
        assert_eq!(try_deep_reduce(&zeta, &e).unwrap(), prop());
        assert!(try_deep_reduce(&Expr::bvar(0), &e).is_none());
        assert!(try_deep_reduce(&Expr::app(Expr::bvar(0), Expr::bvar(1)), &e).is_none());
    }

    #[test]
    fn test_primary_beta_reduces_name_works() {
        let congr = BetaReduces::PiCongr {
            binder: BinderInfo::Default.into(),
            domain_orig: prop(),
            domain_reduced: type1(),
            body_orig: Expr::bvar(0),
            body_reduced: Expr::bvar(1),
        };
        assert_eq!(
            congr.original_expr(),
            Expr::pi(BinderInfo::Default, prop(), Expr::bvar(0))
        );
        assert_eq!(
            congr.reduced_expr(),
            Expr::pi(BinderInfo::Default, type1(), Expr::bvar(1))
        );
    }
}
