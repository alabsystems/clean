// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core builder tests: constructor and bookkeeping operations.

use std::sync::Arc;

use crate::cert::builder::{CertBuilder, NodeId};
use crate::cert::{CertError, ProofCert};
use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};
use crate::level::Level;
use crate::name::Name;

#[test]
fn test_sort_construction() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let prop = builder.sort(Level::zero()).unwrap();
    assert_eq!(
        builder.type_of(prop),
        &Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );

    let type1 = builder.sort(Level::succ(Level::zero())).unwrap();
    assert_eq!(
        builder.type_of(type1),
        &Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero()))))
    );
}

#[test]
fn test_bvar_out_of_bounds() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);
    let result = builder.bvar(0);
    assert!(matches!(result, Err(CertError::InvalidBVar(0))));
}

#[test]
fn test_unknown_fvar() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);
    let result = builder.fvar(FVarId(999999));
    assert!(matches!(result, Err(CertError::UnknownFVar(_))));
}

#[test]
fn test_fvar_registration_and_reference() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let fvar_id = FVarId(12345);
    let fvar_type = Expr::from_kind(ExprKind::Sort(Level::zero()));
    builder.register_fvar(fvar_id, fvar_type.clone()).unwrap();

    let node_id = builder.fvar(fvar_id).unwrap();
    assert_eq!(builder.type_of(node_id), &fvar_type);

    let cert = builder.get_cert(node_id).unwrap();
    assert!(matches!(cert, ProofCert::FVar { id, .. } if *id == fvar_id));
}

#[test]
fn test_invalid_node_id_in_app() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let prop = builder.sort(Level::zero()).unwrap();

    let invalid_id = NodeId(999);
    let result = builder.app(invalid_id, prop);
    assert!(matches!(result, Err(CertError::InvalidCert(_))));

    let result2 = builder.app(prop, invalid_id);
    assert!(matches!(result2, Err(CertError::InvalidCert(_))));
}

#[test]
fn test_node_id_type_of() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let prop = builder.sort(Level::zero()).unwrap();
    let type1 = builder.sort(Level::succ(Level::zero())).unwrap();

    assert_eq!(builder.len(), 2);
    assert_eq!(
        builder.type_of(prop),
        &Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );
    assert_eq!(
        builder.type_of(type1),
        &Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero()))))
    );
}

#[test]
fn test_finish_extracts_cert() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let prop = builder.sort(Level::zero()).unwrap();
    let cert = builder.finish(prop).unwrap();

    assert!(matches!(cert, ProofCert::Sort { level } if level == Level::zero()));
}

#[test]
fn test_try_type_of_invalid_id() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let prop = builder.sort(Level::zero()).unwrap();
    let _ty = builder
        .try_type_of(prop)
        .expect("valid NodeId should return type");

    let invalid_id = NodeId(999);
    assert!(
        builder.try_type_of(invalid_id).is_none(),
        "invalid NodeId should return None, got {:?}",
        builder.try_type_of(invalid_id)
    );
}

#[test]
fn test_with_mode() {
    use crate::mode::CleanMode;

    let env = Environment::new();

    let builder_default = CertBuilder::new(&env);
    assert_eq!(builder_default.mode(), CleanMode::Constructive);

    let builder_classical = CertBuilder::with_mode(&env, CleanMode::Classical);
    assert_eq!(builder_classical.mode(), CleanMode::Classical);

    let builder_cubical = CertBuilder::with_mode(&env, CleanMode::Cubical);
    assert_eq!(builder_cubical.mode(), CleanMode::Cubical);
}

#[test]
fn test_new_inherits_environment_mode() {
    use crate::mode::CleanMode;

    let env = Environment::with_mode(CleanMode::Cubical);
    let builder = CertBuilder::new(&env);
    assert_eq!(builder.mode(), env.mode());
}

#[test]
fn test_is_empty() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    assert!(builder.is_empty());
    assert_eq!(builder.len(), 0);

    let _prop = builder.sort(Level::zero()).unwrap();
    assert!(!builder.is_empty());
    assert_eq!(builder.len(), 1);
}

#[test]
fn test_const_construction() {
    let mut env = Environment::new();

    env.add_decl(Declaration::Definition {
        name: Name::from_string("myConst"),
        level_params: vec![],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        value: Expr::from_kind(ExprKind::Sort(Level::zero())),
        is_reducible: true,
    })
    .unwrap();

    let mut builder = CertBuilder::new(&env);

    let const_id = builder
        .const_(Name::from_string("myConst"), vec![])
        .unwrap();

    assert_eq!(
        builder.type_of(const_id),
        &Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );

    let cert = builder.get_cert(const_id).unwrap();
    assert!(matches!(cert, ProofCert::Const { name, .. } if *name == Name::from_string("myConst")));
}

#[test]
fn test_const_unknown() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let result = builder.const_(Name::from_string("nonExistent"), vec![]);
    assert!(matches!(result, Err(CertError::UnknownConst(_))));
}

#[test]
fn test_lam_construction() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let prop_type = builder.sort(Level::zero()).unwrap();

    let lam_id = builder
        .lam(BinderInfo::Default, prop_type, |b| b.bvar(0))
        .unwrap();

    let expected_type = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
        Arc::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    ));
    assert_eq!(builder.type_of(lam_id), &expected_type);

    let cert = builder.get_cert(lam_id).unwrap();
    assert!(matches!(cert, ProofCert::Lam { .. }));
}

#[test]
fn test_lam_nested() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let prop = builder.sort(Level::zero()).unwrap();

    let lam_id = builder
        .lam(BinderInfo::Default, prop, |b| {
            let inner_prop = b.sort(Level::zero()).unwrap();
            b.lam(BinderInfo::Default, inner_prop, |b2| b2.bvar(1))
        })
        .unwrap();

    let cert = builder.get_cert(lam_id).unwrap();
    assert!(matches!(cert, ProofCert::Lam { .. }));
}

#[test]
fn test_pi_construction() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let prop_type = builder.sort(Level::zero()).unwrap();

    let pi_id = builder
        .pi(BinderInfo::Default, prop_type, |b| {
            b.sort(Level::succ(Level::zero()))
        })
        .unwrap();

    let expected_type = Expr::from_kind(ExprKind::Sort(Level::imax(
        Level::succ(Level::zero()),
        Level::succ(Level::succ(Level::zero())),
    )));
    assert_eq!(builder.type_of(pi_id), &expected_type);

    let cert = builder.get_cert(pi_id).unwrap();
    assert!(matches!(cert, ProofCert::Pi { .. }));
}

#[test]
fn test_let_construction() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let type1 = builder.sort(Level::succ(Level::zero())).unwrap();
    let prop = builder.sort(Level::zero()).unwrap();

    let let_id = builder.let_(type1, prop, |b| b.bvar(0)).unwrap();

    assert_eq!(
        builder.type_of(let_id),
        &Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );

    let cert = builder.get_cert(let_id).unwrap();
    assert!(matches!(cert, ProofCert::Let { .. }));
}

#[test]
fn test_let_type_mismatch() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let type2 = builder
        .sort(Level::succ(Level::succ(Level::zero())))
        .unwrap();
    let prop = builder.sort(Level::zero()).unwrap();

    let result = builder.let_(type2, prop, |b| b.bvar(0));
    assert!(matches!(result, Err(CertError::TypeMismatch { .. })));
}

#[test]
fn test_def_eq_coerce() {
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("myProp"),
        level_params: vec![],
        type_: Expr::from_kind(ExprKind::Sort(Level::zero())),
    })
    .unwrap();

    env.add_decl(Declaration::Definition {
        name: Name::from_string("PropAlias"),
        level_params: vec![],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        value: Expr::from_kind(ExprKind::Sort(Level::zero())),
        is_reducible: true,
    })
    .unwrap();

    let mut builder = CertBuilder::new(&env);

    let my_prop = builder.const_(Name::from_string("myProp"), vec![]).unwrap();

    let prop_alias_name = Name::from_string("PropAlias");
    let coerced = builder
        .def_eq_coerce(my_prop, Expr::const_(prop_alias_name.clone(), vec![]))
        .unwrap();

    assert_eq!(
        builder.type_of(coerced),
        &Expr::const_(prop_alias_name, vec![])
    );

    let cert = builder.get_cert(coerced).unwrap();
    assert!(matches!(cert, ProofCert::DefEq { .. }));
}

#[test]
fn test_def_eq_coerce_failure() {
    let env = Environment::new();
    let mut builder = CertBuilder::new(&env);

    let prop = builder.sort(Level::zero()).unwrap();

    let result = builder.def_eq_coerce(
        prop,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero())))),
    );
    assert!(matches!(result, Err(CertError::DefEqFailed { .. })));
}
