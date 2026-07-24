// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `convert_fvar_cert_to_bvar` — AC3: round-trip correctness.

use crate::cert::ProofCert;
use crate::expr::{BinderInfo, Expr, ExprKind, FVarId, Literal};
use crate::level::Level;
use crate::tc::cert::convert_fvar_cert_to_bvar;

fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}

#[test]
fn test_convert_fvar_cert_matching_fvar_becomes_bvar() {
    let fvar_id = FVarId::new(42);
    let ty = nat_ty();
    let cert = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(ty.clone()),
    };
    let result = convert_fvar_cert_to_bvar(cert, fvar_id, 0);
    match result {
        ProofCert::BVar { idx, expected_type } => {
            assert_eq!(idx, 0);
            assert_eq!(*expected_type, ty);
        }
        other => panic!("expected BVar cert, got {:?}", other),
    }
}

#[test]
fn test_convert_fvar_cert_non_matching_fvar_preserved() {
    let target = FVarId::new(42);
    let other = FVarId::new(99);
    let ty = nat_ty();
    let cert = ProofCert::FVar {
        id: other,
        type_: Box::new(ty.clone()),
    };
    let result = convert_fvar_cert_to_bvar(cert, target, 0);
    match result {
        ProofCert::FVar { id, type_ } => {
            assert_eq!(id, other);
            assert_eq!(*type_, ty);
        }
        other => panic!("expected FVar cert, got {:?}", other),
    }
}

#[test]
fn test_convert_fvar_cert_sort_unchanged() {
    let fvar_id = FVarId::new(1);
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let result = convert_fvar_cert_to_bvar(cert.clone(), fvar_id, 0);
    assert_eq!(result, cert);
}

#[test]
fn test_convert_fvar_cert_bvar_shifted() {
    let fvar_id = FVarId::new(1);
    let ty = nat_ty();
    let cert = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(ty.clone()),
    };
    // BVar(0) at depth 0 → shifted to BVar(1)
    let result = convert_fvar_cert_to_bvar(cert, fvar_id, 0);
    match result {
        ProofCert::BVar { idx, .. } => assert_eq!(idx, 1),
        other => panic!("expected BVar cert, got {:?}", other),
    }
}

#[test]
fn test_convert_fvar_cert_bvar_not_shifted_below_depth() {
    let fvar_id = FVarId::new(1);
    let ty = nat_ty();
    let cert = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(ty),
    };
    // BVar(0) at depth 1 → not shifted (0 < 1)
    let result = convert_fvar_cert_to_bvar(cert, fvar_id, 1);
    match result {
        ProofCert::BVar { idx, .. } => assert_eq!(idx, 0),
        other => panic!("expected BVar cert, got {:?}", other),
    }
}

#[test]
fn test_convert_fvar_cert_app_recurses() {
    let fvar_id = FVarId::new(50);
    let nat_ty = nat_ty();
    let fn_cert = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(nat_ty.clone()),
    };
    let arg_cert = ProofCert::Lit {
        lit: Literal::nat(1),
        type_: Box::new(nat_ty.clone()),
    };
    let cert = ProofCert::App {
        fn_cert: Box::new(fn_cert),
        fn_type: Box::new(nat_ty.clone()),
        arg_cert: Box::new(arg_cert),
        result_type: Box::new(nat_ty.clone()),
    };
    let result = convert_fvar_cert_to_bvar(cert, fvar_id, 0);
    match result {
        ProofCert::App {
            fn_cert, arg_cert, ..
        } => {
            assert!(matches!(*fn_cert, ProofCert::BVar { idx: 0, .. }));
            assert!(matches!(*arg_cert, ProofCert::Lit { .. }));
        }
        other => panic!("expected App cert, got {:?}", other),
    }
}

#[test]
fn test_convert_fvar_cert_lam_depth_increment() {
    let fvar_id = FVarId::new(60);
    let nat_ty = nat_ty();
    let body_cert = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(nat_ty.clone()),
    };
    let arg_type_cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };
    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(arg_type_cert),
        body_cert: Box::new(body_cert),
        result_type: Box::new(nat_ty.clone()),
    };
    let result = convert_fvar_cert_to_bvar(cert, fvar_id, 0);
    match result {
        ProofCert::Lam { body_cert, .. } => {
            assert!(
                matches!(*body_cert, ProofCert::BVar { idx: 1, .. }),
                "expected BVar(1), got {:?}",
                body_cert
            );
        }
        other => panic!("expected Lam cert, got {:?}", other),
    }
}

#[test]
fn test_convert_fvar_cert_pi_depth_increment() {
    let fvar_id = FVarId::new(61);
    let nat_ty = nat_ty();
    let body_cert = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(nat_ty.clone()),
    };
    let arg_type_cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };
    let cert = ProofCert::Pi {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(arg_type_cert),
        arg_level: Level::succ(Level::zero()),
        body_type_cert: Box::new(body_cert),
        body_level: Level::zero(),
    };
    let result = convert_fvar_cert_to_bvar(cert, fvar_id, 0);
    match result {
        ProofCert::Pi { body_type_cert, .. } => {
            assert!(
                matches!(*body_type_cert, ProofCert::BVar { idx: 1, .. }),
                "Pi body at depth+1: expected BVar(1), got {:?}",
                body_type_cert
            );
        }
        other => panic!("expected Pi cert, got {:?}", other),
    }
}

#[test]
fn test_convert_fvar_cert_let_depth_increment() {
    let fvar_id = FVarId::new(62);
    let nat_ty = nat_ty();
    let body_cert = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(nat_ty.clone()),
    };
    let type_cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };
    let value_cert = ProofCert::Lit {
        lit: Literal::nat(0),
        type_: Box::new(nat_ty.clone()),
    };
    let cert = ProofCert::Let {
        type_cert: Box::new(type_cert),
        value_cert: Box::new(value_cert),
        body_cert: Box::new(body_cert),
        result_type: Box::new(nat_ty.clone()),
    };
    let result = convert_fvar_cert_to_bvar(cert, fvar_id, 0);
    match result {
        ProofCert::Let {
            body_cert,
            type_cert,
            value_cert,
            ..
        } => {
            assert!(
                matches!(*body_cert, ProofCert::BVar { idx: 1, .. }),
                "Let body at depth+1: expected BVar(1), got {:?}",
                body_cert
            );
            assert!(matches!(*type_cert, ProofCert::Sort { .. }));
            assert!(matches!(*value_cert, ProofCert::Lit { .. }));
        }
        other => panic!("expected Let cert, got {:?}", other),
    }
}

#[test]
fn test_convert_fvar_cert_lit_type_abstracted() {
    let fvar_id = FVarId::new(70);
    let fvar_type = Expr::from_kind(ExprKind::FVar(fvar_id));
    let cert = ProofCert::Lit {
        lit: Literal::nat(42),
        type_: Box::new(fvar_type),
    };
    let result = convert_fvar_cert_to_bvar(cert, fvar_id, 0);
    match result {
        ProofCert::Lit { lit, type_ } => {
            assert_eq!(lit, Literal::nat(42));
            assert_eq!(type_.kind, ExprKind::BVar(0), "fvar in type → BVar");
        }
        other => panic!("expected Lit cert, got {:?}", other),
    }
}
