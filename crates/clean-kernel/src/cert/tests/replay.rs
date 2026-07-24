// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate replay tests

use crate::cert::*;
use crate::env::Environment;
use crate::expr::{BigNat, BinderInfo, Expr, ExprKind, FVarId, Literal};
use crate::level::Level;
use crate::name::Name;

fn empty_env() -> Environment {
    Environment::new()
}

#[test]
fn test_replay_sort() {
    let expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let replayed = replay_cert(&cert);
    assert_eq!(replayed, expr);
}

#[test]
fn test_replay_bvar() {
    let expr = Expr::from_kind(ExprKind::BVar(3));
    let cert = ProofCert::BVar {
        idx: 3,
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let replayed = replay_cert(&cert);
    assert_eq!(replayed, expr);
}

#[test]
fn test_replay_fvar() {
    let fvar_id = FVarId(42);
    let expr = Expr::from_kind(ExprKind::FVar(fvar_id));
    let cert = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let replayed = replay_cert(&cert);
    assert_eq!(replayed, expr);
}

#[test]
fn test_replay_const() {
    let name = Name::from_string("Nat");
    let levels = vec![Level::zero()];
    let expr = Expr::const_(name.clone(), levels.clone());
    let cert = ProofCert::Const {
        name: name.clone(),
        levels: levels.clone(),
        type_: Box::new(Expr::type_()),
    };

    let replayed = replay_cert(&cert);
    assert_eq!(replayed, expr);
}

#[test]
fn test_replay_app() {
    // Build: f x where f : A -> B, x : A
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let expr = Expr::from_kind(ExprKind::App(f.clone().into(), x.clone().into()));

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);

    let cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Const {
            name: Name::from_string("f"),
            levels: vec![],
            type_: Box::new(Expr::arrow(a_ty.clone(), b_ty.clone())),
        }),
        fn_type: Box::new(Expr::arrow(a_ty.clone(), b_ty.clone())),
        arg_cert: Box::new(ProofCert::Const {
            name: Name::from_string("x"),
            levels: vec![],
            type_: Box::new(a_ty),
        }),
        result_type: Box::new(b_ty),
    };

    let replayed = replay_cert(&cert);
    assert_eq!(replayed, expr);
}

#[test]
fn test_replay_lam() {
    // Build: λ (x : Prop). x
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
    );

    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(Expr::pi(BinderInfo::Default, prop.clone(), prop.clone())),
    };

    let replayed = replay_cert(&cert);
    assert_eq!(replayed, expr);
}

#[test]
fn test_replay_pi() {
    // Build: Prop -> Prop
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());

    let cert = ProofCert::Pi {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        arg_level: Level::succ(Level::zero()),
        body_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_level: Level::succ(Level::zero()),
    };

    let replayed = replay_cert(&cert);
    assert_eq!(replayed, expr);
}

#[test]
fn test_replay_lit() {
    let expr = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let cert = ProofCert::Lit {
        lit: Literal::Nat(BigNat::Small(42)),
        type_: Box::new(nat_ty),
    };

    let replayed = replay_cert(&cert);
    assert_eq!(replayed, expr);
}

#[test]
fn test_replay_def_eq() {
    // DefEq should be transparent in replay
    let inner_expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let cert = ProofCert::DefEq {
        inner: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
        actual_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
        eq_steps: vec![DefEqStep::Refl],
    };

    let replayed = replay_cert(&cert);
    assert_eq!(replayed, inner_expr);
}

#[test]
fn test_replay_mdata() {
    use crate::expr::MDataValue;

    let inner_expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let metadata = vec![(Name::from_string("trace"), MDataValue::Bool(true))];
    let expr = Expr::mdata(metadata.clone(), inner_expr.clone());

    let cert = ProofCert::MData {
        metadata: metadata.clone(),
        inner_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        result_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
    };

    let replayed = replay_cert(&cert);
    assert_eq!(replayed, expr);
}

#[test]
fn test_replay_and_verify_sort() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let (expr, ty) = verifier
        .replay_and_verify(&cert)
        .expect("replay_and_verify Sort should succeed");
    assert_eq!(expr, Expr::from_kind(ExprKind::Sort(Level::zero())));
    assert_eq!(
        ty,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );
}

#[test]
fn test_replay_and_verify_identity() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Certificate for λ (x : Prop). x : Prop → Prop
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(Expr::pi(BinderInfo::Default, prop.clone(), prop.clone())),
    };

    let (expr, ty) = verifier
        .replay_and_verify(&cert)
        .expect("replay_and_verify identity lambda should succeed");

    // Verify the replayed expression is correct
    assert!(matches!(&expr.kind, ExprKind::Lam(_, _, _)));

    // Verify the type is Prop → Prop
    assert!(matches!(&ty.kind, ExprKind::Pi(_, _, _)));
}

#[test]
fn test_replay_roundtrip_with_serialization() {
    // Test the full flow: expr -> cert -> serialize -> deserialize -> replay -> expr
    let expr = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };

    // Serialize to JSON
    let json = serde_json::to_string(&cert).expect("JSON serialization failed");

    // Deserialize
    let restored: ProofCert = serde_json::from_str(&json).expect("JSON deserialization failed");

    // Replay
    let replayed = replay_cert(&restored);

    // Should match original
    assert_eq!(replayed, expr);
}

#[test]
fn test_replay_complex_nested_cert() {
    // Build: (λ (A : Type). λ (x : A). x)
    // Type: (A : Type) → A → A
    let type0 = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

    // The expression (for reference, we verify structure below)
    let _inner_lam = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::BVar(0)), // A (outer binder)
        Expr::from_kind(ExprKind::BVar(0)), // x (inner binder)
    );
    // Outer lambda: λ (A : Type). _inner_lam

    // Build certificate for inner body: x : A (BVar 0)
    let inner_body_cert = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(Expr::from_kind(ExprKind::BVar(1))), // A lifted
    };

    // Certificate for inner lambda
    let inner_cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(type1.clone()),
        }),
        body_cert: Box::new(inner_body_cert),
        result_type: Box::new(Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(0)),
            Expr::from_kind(ExprKind::BVar(1)),
        )),
    };

    // Certificate for outer lambda
    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(inner_cert),
        result_type: Box::new(Expr::pi(
            BinderInfo::Default,
            type0.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::BVar(0)),
                Expr::from_kind(ExprKind::BVar(1)),
            ),
        )),
    };

    let replayed = replay_cert(&cert);

    // Should match original expression structure
    assert!(matches!(replayed.kind, ExprKind::Lam(_, _, _)));

    // Verify the inner structure
    match &replayed.kind {
        ExprKind::Lam(_, outer_ty, outer_body) => {
            assert_eq!(outer_ty.as_ref(), &type0);
            assert!(matches!(outer_body.as_ref().kind, ExprKind::Lam(_, _, _)));
        }
        _ => panic!("Expected outer Lam"),
    }
}

#[test]
fn test_replay_let() {
    // Build: let x : Prop := Prop in x
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::let_named(
        Name::anon(),
        prop.clone(),
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
        false,
    );

    let cert = ProofCert::Let {
        type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        value_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(prop.clone()),
    };

    let replayed = replay_cert(&cert);
    assert_eq!(replayed, expr);
}

// ========================================================================
// Replay coverage for Cubical, Classical, ZFC, SProp, Squash, Proj paths
// ========================================================================

#[test]
fn test_replay_cubical_interval() {
    let cert = ProofCert::CubicalInterval;
    let replayed = replay_cert(&cert);
    assert_eq!(replayed, Expr::from_kind(ExprKind::CubicalInterval));
}

#[test]
fn test_replay_cubical_endpoint_i0() {
    let cert = ProofCert::CubicalEndpoint { is_one: false };
    let replayed = replay_cert(&cert);
    assert_eq!(replayed, Expr::from_kind(ExprKind::CubicalI0));
}

#[test]
fn test_replay_cubical_endpoint_i1() {
    let cert = ProofCert::CubicalEndpoint { is_one: true };
    let replayed = replay_cert(&cert);
    assert_eq!(replayed, Expr::from_kind(ExprKind::CubicalI1));
}

#[test]
fn test_replay_cubical_path() {
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let cert = ProofCert::CubicalPath {
        ty_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        ty_level: Level::succ(Level::zero()),
        left_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        right_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
    };

    let replayed = replay_cert(&cert);
    match &replayed.kind {
        ExprKind::CubicalPath { ty, left, right } => {
            assert_eq!(**ty, prop);
            assert_eq!(**left, prop);
            assert_eq!(**right, prop);
        }
        other => panic!("Expected CubicalPath, got {other:?}"),
    }
}

#[test]
fn test_replay_cubical_path_lam() {
    let prop_cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let cert = ProofCert::CubicalPathLam {
        body_cert: Box::new(prop_cert),
        body_type: Box::new(Expr::prop()),
        result_type: Box::new(Expr::type_()),
    };

    let replayed = replay_cert(&cert);
    match &replayed.kind {
        ExprKind::CubicalPathLam { body } => {
            assert_eq!(**body, Expr::from_kind(ExprKind::Sort(Level::zero())));
        }
        other => panic!("Expected CubicalPathLam, got {other:?}"),
    }
}

#[test]
fn test_replay_cubical_path_app() {
    let cert = ProofCert::CubicalPathApp {
        path_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        arg_cert: Box::new(ProofCert::CubicalEndpoint { is_one: false }),
        path_type: Box::new(Expr::type_()),
        result_type: Box::new(Expr::type_()),
    };

    let replayed = replay_cert(&cert);
    match &replayed.kind {
        ExprKind::CubicalPathApp { path, arg } => {
            assert_eq!(**path, Expr::from_kind(ExprKind::Sort(Level::zero())));
            assert_eq!(**arg, Expr::from_kind(ExprKind::CubicalI0));
        }
        other => panic!("Expected CubicalPathApp, got {other:?}"),
    }
}

#[test]
fn test_replay_cubical_hcomp() {
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let cert = ProofCert::CubicalHComp {
        ty_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        phi_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        u_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        base_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        result_type: Box::new(Expr::type_()),
    };

    let replayed = replay_cert(&cert);
    match &replayed.kind {
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            assert_eq!(**ty, prop);
            assert_eq!(**phi, prop);
            assert_eq!(**u, prop);
            assert_eq!(**base, prop);
        }
        other => panic!("Expected CubicalHComp, got {other:?}"),
    }
}

#[test]
fn test_replay_cubical_transp() {
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let cert = ProofCert::CubicalTransp {
        ty_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        phi_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        base_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        result_type: Box::new(Expr::type_()),
    };

    let replayed = replay_cert(&cert);
    match &replayed.kind {
        ExprKind::CubicalTransp { ty, phi, base } => {
            assert_eq!(**ty, prop);
            assert_eq!(**phi, prop);
            assert_eq!(**base, prop);
        }
        other => panic!("Expected CubicalTransp, got {other:?}"),
    }
}

#[test]
fn test_replay_zfc_set_empty() {
    use crate::expr::ZFCSetExpr;

    let cert = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Empty,
        result_type: Box::new(Expr::type_()),
    };
    let replayed = replay_cert(&cert);
    assert_eq!(
        replayed,
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty))
    );
}

#[test]
fn test_replay_zfc_set_infinity() {
    use crate::expr::ZFCSetExpr;

    let cert = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Infinity,
        result_type: Box::new(Expr::type_()),
    };
    let replayed = replay_cert(&cert);
    assert_eq!(
        replayed,
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Infinity))
    );
}

#[test]
fn test_replay_zfc_set_singleton() {
    use crate::expr::ZFCSetExpr;

    let cert = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Singleton(Box::new(ProofCert::Sort {
            level: Level::zero(),
        })),
        result_type: Box::new(Expr::type_()),
    };
    let replayed = replay_cert(&cert);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    assert_eq!(
        replayed,
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(prop.into())))
    );
}

#[test]
fn test_replay_zfc_set_pair() {
    use crate::expr::ZFCSetExpr;

    let cert = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Pair(
            Box::new(ProofCert::Sort {
                level: Level::zero(),
            }),
            Box::new(ProofCert::Sort {
                level: Level::succ(Level::zero()),
            }),
        ),
        result_type: Box::new(Expr::type_()),
    };
    let replayed = replay_cert(&cert);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    assert_eq!(
        replayed,
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
            prop.into(),
            type_.into()
        )))
    );
}

#[test]
fn test_replay_zfc_set_union() {
    use crate::expr::ZFCSetExpr;

    let cert = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Union(Box::new(ProofCert::ZFCSet {
            kind: ZFCSetCertKind::Empty,
            result_type: Box::new(Expr::type_()),
        })),
        result_type: Box::new(Expr::type_()),
    };
    let replayed = replay_cert(&cert);
    let empty = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    assert_eq!(
        replayed,
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Union(empty.into())))
    );
}

#[test]
fn test_replay_zfc_set_power_set() {
    use crate::expr::ZFCSetExpr;

    let cert = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::PowerSet(Box::new(ProofCert::ZFCSet {
            kind: ZFCSetCertKind::Empty,
            result_type: Box::new(Expr::type_()),
        })),
        result_type: Box::new(Expr::type_()),
    };
    let replayed = replay_cert(&cert);
    let empty = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    assert_eq!(
        replayed,
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::PowerSet(empty.into())))
    );
}

#[test]
fn test_replay_zfc_set_separation() {
    use crate::expr::ZFCSetExpr;

    let cert = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Separation {
            set_cert: Box::new(ProofCert::ZFCSet {
                kind: ZFCSetCertKind::Empty,
                result_type: Box::new(Expr::type_()),
            }),
            pred_cert: Box::new(ProofCert::Sort {
                level: Level::zero(),
            }),
        },
        result_type: Box::new(Expr::type_()),
    };
    let replayed = replay_cert(&cert);
    let empty = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    assert_eq!(
        replayed,
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
            set: empty.into(),
            pred: prop.into(),
        }))
    );
}

#[test]
fn test_replay_zfc_set_replacement() {
    use crate::expr::ZFCSetExpr;

    let cert = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Replacement {
            set_cert: Box::new(ProofCert::ZFCSet {
                kind: ZFCSetCertKind::Empty,
                result_type: Box::new(Expr::type_()),
            }),
            func_cert: Box::new(ProofCert::Sort {
                level: Level::zero(),
            }),
        },
        result_type: Box::new(Expr::type_()),
    };
    let replayed = replay_cert(&cert);
    let empty = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    assert_eq!(
        replayed,
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
            set: empty.into(),
            func: prop.into(),
        }))
    );
}

#[test]
fn test_replay_zfc_set_choice() {
    use crate::expr::ZFCSetExpr;

    let cert = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Choice(Box::new(ProofCert::ZFCSet {
            kind: ZFCSetCertKind::Empty,
            result_type: Box::new(Expr::type_()),
        })),
        result_type: Box::new(Expr::type_()),
    };
    let replayed = replay_cert(&cert);
    let empty = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    assert_eq!(
        replayed,
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Choice(empty.into())))
    );
}

#[test]
fn test_replay_zfc_mem() {
    let cert = ProofCert::ZFCMem {
        elem_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        set_cert: Box::new(ProofCert::Sort {
            level: Level::succ(Level::zero()),
        }),
    };
    let replayed = replay_cert(&cert);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    match &replayed.kind {
        ExprKind::ZFCMem { element, set } => {
            assert_eq!(**element, prop);
            assert_eq!(**set, type_);
        }
        other => panic!("Expected ZFCMem, got {other:?}"),
    }
}

#[test]
fn test_replay_zfc_comprehension() {
    let cert = ProofCert::ZFCComprehension {
        var_ty_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        pred_cert: Box::new(ProofCert::Sort {
            level: Level::succ(Level::zero()),
        }),
        result_type: Box::new(Expr::type_()),
    };
    let replayed = replay_cert(&cert);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    match &replayed.kind {
        ExprKind::ZFCComprehension { domain, pred } => {
            assert_eq!(**domain, prop);
            assert_eq!(**pred, type_);
        }
        other => panic!("Expected ZFCComprehension, got {other:?}"),
    }
}

#[test]
fn test_replay_sprop() {
    let cert = ProofCert::SProp;
    let replayed = replay_cert(&cert);
    assert_eq!(replayed, Expr::from_kind(ExprKind::SProp));
}

#[test]
fn test_replay_squash() {
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let cert = ProofCert::Squash {
        inner_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
    };
    let replayed = replay_cert(&cert);
    assert_eq!(replayed, Expr::from_kind(ExprKind::Squash(prop.into())));
}

#[test]
fn test_replay_proj() {
    let struct_name = Name::from_string("Prod");
    let cert = ProofCert::Proj {
        struct_name: struct_name.clone(),
        idx: 0,
        expr_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        expr_type: Box::new(Expr::type_()),
        field_type: Box::new(Expr::type_()),
    };
    let replayed = replay_cert(&cert);
    let inner = Expr::from_kind(ExprKind::Sort(Level::zero()));
    assert_eq!(replayed, Expr::proj(struct_name, 0, inner));
}

// ========================================================================
// Certificate Compression tests
// ========================================================================
