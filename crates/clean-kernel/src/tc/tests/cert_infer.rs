// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `infer_type_with_cert` — AC1 + AC4: correct certs, validity.

use crate::cert::ProofCert;
use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind, FVarId, Literal};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;
use std::sync::Arc;

fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}

#[test]
fn test_cert_sort_zero_produces_sort_one() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let e = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let (ty, cert) = tc
        .infer_type_with_cert(&e)
        .expect("Sort(0) should type-check");
    assert_eq!(ty.kind, ExprKind::Sort(Level::succ(Level::zero())));
    assert_eq!(
        cert,
        ProofCert::Sort {
            level: Level::zero()
        }
    );
}

#[test]
fn test_cert_sort_one_produces_sort_two() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let l1 = Level::succ(Level::zero());
    let e = Expr::from_kind(ExprKind::Sort(l1.clone()));
    let (ty, cert) = tc
        .infer_type_with_cert(&e)
        .expect("Sort(1) should type-check");
    assert_eq!(ty.kind, ExprKind::Sort(Level::succ(l1.clone())));
    assert_eq!(cert, ProofCert::Sort { level: l1 });
}

#[test]
fn test_cert_nat_lit() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let e = Expr::nat_lit(42);
    let (ty, cert) = tc
        .infer_type_with_cert(&e)
        .expect("Nat lit should type-check");
    assert_eq!(ty, nat_ty());
    match &cert {
        ProofCert::Lit { lit, type_ } => {
            assert_eq!(lit, &Literal::nat(42));
            assert_eq!(type_.as_ref(), &nat_ty());
        }
        other => panic!("expected Lit cert, got {:?}", other),
    }
}

#[test]
fn test_cert_string_lit() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let e = Expr::from_kind(ExprKind::Lit(Literal::String("hello".into())));
    let (ty, cert) = tc
        .infer_type_with_cert(&e)
        .expect("String lit should type-check");
    assert_eq!(ty, Expr::const_str("String"));
    match &cert {
        ProofCert::Lit { lit, type_ } => {
            assert_eq!(lit, &Literal::String("hello".into()));
            assert_eq!(type_.as_ref(), &Expr::const_str("String"));
        }
        other => panic!("expected Lit cert, got {:?}", other),
    }
}

#[test]
fn test_cert_bvar_returns_error() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let e = Expr::from_kind(ExprKind::BVar(0));
    let result = tc.infer_type_with_cert(&e);
    assert!(result.is_err(), "unbound BVar should fail");
    match result.unwrap_err() {
        crate::TypeError::UnboundVariable(idx) => assert_eq!(idx, 0),
        other => panic!("expected UnboundVariable, got {:?}", other),
    }
}

#[test]
fn test_cert_unknown_fvar_returns_error() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let e = Expr::from_kind(ExprKind::FVar(FVarId::new(999)));
    let result = tc.infer_type_with_cert(&e);
    assert!(result.is_err(), "unknown FVar should fail");
    assert!(matches!(
        result.unwrap_err(),
        crate::TypeError::UnknownFVar(_)
    ));
}

#[test]
fn test_cert_const_with_axiom() {
    let mut env = Environment::new();
    let name = Name::from_string("myAxiom");
    let ty = Expr::from_kind(ExprKind::Sort(Level::zero()));
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: ty.clone(),
    })
    .expect("add axiom");
    let tc = TypeChecker::new(&env);
    let e = Expr::const_str("myAxiom");
    let (result_ty, cert) = tc
        .infer_type_with_cert(&e)
        .expect("const should type-check");
    assert_eq!(result_ty, ty);
    match &cert {
        ProofCert::Const {
            name: cert_name,
            levels,
            type_,
        } => {
            assert_eq!(cert_name, &name);
            assert!(levels.is_empty());
            assert_eq!(type_.as_ref(), &ty);
        }
        other => panic!("expected Const cert, got {:?}", other),
    }
}

#[test]
fn test_cert_unknown_const_returns_error() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let e = Expr::const_str("nonexistent");
    let result = tc.infer_type_with_cert(&e);
    assert!(result.is_err(), "unknown const should fail");
    assert!(matches!(
        result.unwrap_err(),
        crate::TypeError::UnknownConst(_)
    ));
}

#[test]
fn test_cert_pi_prop_to_prop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let e = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(prop.clone()),
        Arc::new(prop),
    ));
    let (ty, cert) = tc.infer_type_with_cert(&e).expect("Pi should type-check");
    assert_eq!(
        ty.kind,
        ExprKind::Sort(Level::succ(Level::zero())),
        "(Prop → Prop) : Sort(1)"
    );
    match &cert {
        ProofCert::Pi {
            binder_info,
            arg_level,
            body_level,
            ..
        } => {
            assert_eq!(*binder_info, BinderInfo::Default);
            assert_eq!(arg_level, &Level::succ(Level::zero()));
            assert_eq!(body_level, &Level::succ(Level::zero()));
        }
        other => panic!("expected Pi cert, got {:?}", other),
    }
}

#[test]
fn test_cert_mdata_transparent() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let inner = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let e = Expr::from_kind(ExprKind::MData(vec![], Arc::new(inner)));
    let (ty, cert) = tc
        .infer_type_with_cert(&e)
        .expect("MData should type-check");
    assert_eq!(ty.kind, ExprKind::Sort(Level::succ(Level::zero())));
    match &cert {
        ProofCert::MData {
            inner_cert,
            result_type,
            ..
        } => {
            assert_eq!(
                inner_cert.as_ref(),
                &ProofCert::Sort {
                    level: Level::zero()
                }
            );
            assert_eq!(
                result_type.as_ref().kind,
                ExprKind::Sort(Level::succ(Level::zero()))
            );
        }
        other => panic!("expected MData cert, got {:?}", other),
    }
}

#[test]
fn test_cert_cubical_interval_requires_mode() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let e = Expr::from_kind(ExprKind::CubicalInterval);
    let result = tc.infer_type_with_cert(&e);
    assert!(result.is_err(), "CubicalInterval requires Cubical mode");
    assert!(matches!(
        result.unwrap_err(),
        crate::TypeError::ModeRequired { .. }
    ));
}

#[test]
fn test_cert_sprop_requires_mode() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let e = Expr::from_kind(ExprKind::SProp);
    let result = tc.infer_type_with_cert(&e);
    assert!(result.is_err(), "SProp requires Impredicative mode");
    assert!(matches!(
        result.unwrap_err(),
        crate::TypeError::ModeRequired { .. }
    ));
}

#[test]
fn test_cert_known_fvar_returns_type_and_cert() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let nat = nat_ty();
    let fvar_id =
        tc.ctx
            .borrow_mut()
            .push(Name::from_string("x"), nat.clone(), BinderInfo::Default);
    let e = Expr::from_kind(ExprKind::FVar(fvar_id));
    let (ty, cert) = tc
        .infer_type_with_cert(&e)
        .expect("known FVar should type-check");
    assert_eq!(ty, nat, "FVar type should be Nat");
    match &cert {
        ProofCert::FVar { id, type_ } => {
            assert_eq!(*id, fvar_id, "cert FVar id should match");
            assert_eq!(type_.as_ref(), &nat, "cert type should be Nat");
        }
        other => panic!("expected FVar cert, got {:?}", other),
    }
}
