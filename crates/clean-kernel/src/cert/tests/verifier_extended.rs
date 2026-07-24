// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended unit tests for `CertVerifier::verify` — gap-fill coverage.
//!
//! Covers Sort basic, BVar basic, FVar basic/unregistered, Lit(Nat),
//! MData (basic + type_mismatch), and the full Proj test suite
//! (basic_fst, basic_snd, polymorphic, struct_name_mismatch,
//! index_mismatch, field_out_of_bounds, unknown_inductive,
//! field_type_forgery, expr_type_mismatch, multiple_constructors,
//! cert_on_wrong_expr).
//!
//! Part of #2435.

use crate::cert::*;
use crate::env::{Declaration, Environment};
use crate::expr::{BigNat, BinderInfo, Expr, ExprKind, FVarId, Literal, MDataValue};
use crate::inductive::{ConstructorVal, InductiveVal};
use crate::level::Level;
use crate::name::Name;

fn empty_env() -> Environment {
    Environment::new()
}

// =========================================================================
// Sort — basic happy path
// =========================================================================

#[test]
fn test_verify_sort_basic() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Sort(0) = Prop, has type Sort(1) = Type 0
    let expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let ty = verifier
        .verify(&cert, &expr)
        .expect("Sort(0) should verify");
    assert_eq!(
        ty,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        "Sort(0) has type Sort(1)"
    );
}

#[test]
fn test_verify_sort_level_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Cert claims Sort(0) but expr is Sort(1)
    let expr = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let result = verifier.verify(&cert, &expr);
    assert!(result.is_err(), "Mismatched Sort level should fail");
}

// =========================================================================
// BVar — basic happy path
// =========================================================================

#[test]
fn test_verify_bvar_basic() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // BVar(0) inside a lambda with expected_type = Prop
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let bvar_expr = Expr::from_kind(ExprKind::BVar(0));
    let lam_expr = Expr::lam(BinderInfo::Default, prop.clone(), bvar_expr.clone());

    // Build a Lam cert where the body is BVar
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

    let ty = verifier
        .verify(&cert, &lam_expr)
        .expect("Lam with BVar(0) body should verify");
    assert_eq!(
        ty,
        Expr::pi(BinderInfo::Default, prop.clone(), prop.clone()),
        "Lambda should have Pi type"
    );
}

// =========================================================================
// FVar — basic happy path + unregistered
// =========================================================================

#[test]
fn test_verify_fvar_basic() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let fvar_id = FVarId(42);
    verifier.register_fvar(fvar_id, prop.clone()).unwrap();

    let expr = Expr::from_kind(ExprKind::FVar(fvar_id));
    let cert = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(prop.clone()),
    };
    let ty = verifier.verify(&cert, &expr).expect("FVar should verify");
    assert_eq!(ty, prop);
}

#[test]
fn test_verify_fvar_unregistered() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let fvar_id = FVarId(999);

    let expr = Expr::from_kind(ExprKind::FVar(fvar_id));
    let cert = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(prop),
    };
    let result = verifier.verify(&cert, &expr);
    assert!(result.is_err(), "Unregistered FVar should fail");
}

// =========================================================================
// Lit — Nat happy path
// =========================================================================

#[test]
fn test_verify_lit_nat() {
    let mut env = empty_env();
    // Register Nat axiom so Lit verification can look it up
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
    })
    .unwrap();
    let mut verifier = CertVerifier::new(&env);

    let lit_expr = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::from(42u64))));
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let cert = ProofCert::Lit {
        lit: Literal::Nat(BigNat::from(42u64)),
        type_: Box::new(nat_type.clone()),
    };
    let ty = verifier
        .verify(&cert, &lit_expr)
        .expect("Lit Nat should verify");
    assert_eq!(ty, nat_type);
}

// =========================================================================
// MData — basic + type mismatch
// =========================================================================

#[test]
fn test_verify_mdata_basic() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let metadata = vec![(Name::from_string("tag"), MDataValue::Bool(true))];
    let inner = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::mdata(metadata.clone(), inner);

    let sort1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let cert = ProofCert::MData {
        metadata,
        inner_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        result_type: Box::new(sort1.clone()),
    };
    let ty = verifier
        .verify(&cert, &expr)
        .expect("MData wrapping Sort(0) should verify");
    assert_eq!(ty, sort1);
}

#[test]
fn test_verify_mdata_type_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let metadata = vec![(Name::from_string("tag"), MDataValue::Bool(true))];
    let inner = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::mdata(metadata.clone(), inner);

    // Claim result is Sort(2), but inner Sort(0) has type Sort(1)
    let sort2 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero()))));
    let cert = ProofCert::MData {
        metadata,
        inner_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        result_type: Box::new(sort2),
    };
    let result = verifier.verify(&cert, &expr);
    assert!(result.is_err(), "MData with wrong result type should fail");
}

// =========================================================================
// Proj test helpers — environment setup
// =========================================================================

/// Monomorphic pair structure: `structure MyPair where fst : Prop; snd : Prop`
///
/// Constructor type: `Prop → Prop → MyPair`
/// As Pi: `Π (_ : Prop), Π (_ : Prop), MyPair`
/// With de Bruijn: `Pi(Prop, Pi(Prop, Const(MyPair)))`
fn env_with_my_pair() -> Environment {
    let mut env = Environment::new();
    let struct_name = Name::from_string("MyPair");
    let ctor_name = Name::from_string("MyPair.mk");
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let my_pair_const = Expr::from_kind(ExprKind::Const(struct_name.clone(), vec![].into()));

    // MyPair : Prop (lives in Prop since both fields are Prop)
    env.register_inductive(InductiveVal {
        name: struct_name.clone(),
        level_params: vec![],
        type_: prop.clone(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![struct_name.clone()],
        constructor_names: vec![ctor_name.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: false,
        is_nested: false,
    });

    // MyPair.mk : Prop → Prop → MyPair
    // Pi(_, Prop, Pi(_, Prop, Const(MyPair)))
    let ctor_type = Expr::pi(
        BinderInfo::Default,
        prop.clone(),
        Expr::pi(BinderInfo::Default, prop.clone(), my_pair_const),
    );
    env.register_constructor(ConstructorVal {
        name: ctor_name,
        inductive_name: struct_name,
        level_params: vec![],
        type_: ctor_type,
        num_params: 0,
        num_fields: 2,
        constructor_idx: 0,
    });
    env
}

/// Polymorphic box: `structure MyBox (α : Sort u) where val : α`
///
/// Constructor type: `Π (α : Sort u), α → MyBox α`
/// With de Bruijn: `Pi(Sort(u), Pi(BVar(0), App(Const(MyBox,[u]), BVar(1))))`
/// num_params = 1 (α is a parameter), num_fields = 1 (val)
fn env_with_my_box() -> Environment {
    let mut env = Environment::new();
    let struct_name = Name::from_string("MyBox");
    let ctor_name = Name::from_string("MyBox.mk");
    let u = Name::from_string("u");
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    // MyBox : Sort u → Sort u
    let ind_type = Expr::pi(BinderInfo::Default, sort_u.clone(), sort_u.clone());
    env.register_inductive(InductiveVal {
        name: struct_name.clone(),
        level_params: vec![u.clone()],
        type_: ind_type,
        num_params: 1,
        num_indices: 0,
        all_names: vec![struct_name.clone()],
        constructor_names: vec![ctor_name.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: false,
        is_nested: false,
    });

    // MyBox.mk : Π (α : Sort u), α → MyBox α
    // = Pi(Sort(u), Pi(BVar(0), App(Const(MyBox,[u]), BVar(1))))
    let my_box_app = Expr::app(
        Expr::const_(struct_name.clone(), vec![Level::param(u.clone())]),
        Expr::from_kind(ExprKind::BVar(1)),
    );
    let ctor_type = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(0)),
            my_box_app,
        ),
    );
    env.register_constructor(ConstructorVal {
        name: ctor_name,
        inductive_name: struct_name,
        level_params: vec![u],
        type_: ctor_type,
        num_params: 1,
        num_fields: 1,
        constructor_idx: 0,
    });
    env
}

// =========================================================================
// Proj tests
// =========================================================================

#[test]
fn test_verify_proj_basic_fst() {
    let env = env_with_my_pair();
    let mut verifier = CertVerifier::new(&env);

    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let struct_name = Name::from_string("MyPair");
    let my_pair_type = Expr::from_kind(ExprKind::Const(struct_name.clone(), vec![].into()));

    // p : MyPair
    let fvar_p = FVarId(10);
    verifier
        .register_fvar(fvar_p, my_pair_type.clone())
        .unwrap();
    let p_expr = Expr::from_kind(ExprKind::FVar(fvar_p));

    // Proj(MyPair, 0, p) — project first field
    let proj_expr = Expr::proj(struct_name.clone(), 0, p_expr.clone());

    let cert = ProofCert::Proj {
        struct_name: struct_name.clone(),
        idx: 0,
        expr_cert: Box::new(ProofCert::FVar {
            id: fvar_p,
            type_: Box::new(my_pair_type.clone()),
        }),
        expr_type: Box::new(my_pair_type),
        field_type: Box::new(prop.clone()),
    };

    let ty = verifier
        .verify(&cert, &proj_expr)
        .expect("Proj.0 of MyPair should verify");
    assert_eq!(ty, prop, "First field of MyPair is Prop");
}

#[test]
fn test_verify_proj_basic_snd() {
    let env = env_with_my_pair();
    let mut verifier = CertVerifier::new(&env);

    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let struct_name = Name::from_string("MyPair");
    let my_pair_type = Expr::from_kind(ExprKind::Const(struct_name.clone(), vec![].into()));

    let fvar_p = FVarId(10);
    verifier
        .register_fvar(fvar_p, my_pair_type.clone())
        .unwrap();
    let p_expr = Expr::from_kind(ExprKind::FVar(fvar_p));

    let proj_expr = Expr::proj(struct_name.clone(), 1, p_expr.clone());

    let cert = ProofCert::Proj {
        struct_name: struct_name.clone(),
        idx: 1,
        expr_cert: Box::new(ProofCert::FVar {
            id: fvar_p,
            type_: Box::new(my_pair_type.clone()),
        }),
        expr_type: Box::new(my_pair_type),
        field_type: Box::new(prop.clone()),
    };

    let ty = verifier
        .verify(&cert, &proj_expr)
        .expect("Proj.1 of MyPair should verify");
    assert_eq!(ty, prop, "Second field of MyPair is Prop");
}

#[test]
fn test_verify_proj_polymorphic() {
    let env = env_with_my_box();
    let mut verifier = CertVerifier::new(&env);

    let struct_name = Name::from_string("MyBox");
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // MyBox applied at universe 0: MyBox.{0} Prop
    let my_box_prop = Expr::app(
        Expr::const_(struct_name.clone(), vec![Level::zero()]),
        prop.clone(),
    );

    let fvar_b = FVarId(20);
    verifier.register_fvar(fvar_b, my_box_prop.clone()).unwrap();
    let b_expr = Expr::from_kind(ExprKind::FVar(fvar_b));

    // Proj(MyBox, 0, b) — project the val field
    let proj_expr = Expr::proj(struct_name.clone(), 0, b_expr.clone());

    let cert = ProofCert::Proj {
        struct_name: struct_name.clone(),
        idx: 0,
        expr_cert: Box::new(ProofCert::FVar {
            id: fvar_b,
            type_: Box::new(my_box_prop.clone()),
        }),
        expr_type: Box::new(my_box_prop),
        field_type: Box::new(prop.clone()),
    };

    let ty = verifier
        .verify(&cert, &proj_expr)
        .expect("Polymorphic Proj should verify");
    assert_eq!(ty, prop, "MyBox.{{0}} Prop projected val should be Prop");
}

#[test]
fn test_verify_proj_polymorphic_missing_levels_rejected() {
    let env = env_with_my_box();
    let mut verifier = CertVerifier::new(&env);

    let struct_name = Name::from_string("MyBox");
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // Malformed: MyBox Prop with NO universe levels on Const (empty vec instead of [Level::zero()])
    let my_box_prop_bad = Expr::app(Expr::const_(struct_name.clone(), vec![]), prop.clone());

    let fvar_b = FVarId(21);
    verifier
        .register_fvar(fvar_b, my_box_prop_bad.clone())
        .unwrap();
    let b_expr = Expr::from_kind(ExprKind::FVar(fvar_b));

    let proj_expr = Expr::proj(struct_name.clone(), 0, b_expr.clone());

    let cert = ProofCert::Proj {
        struct_name: struct_name.clone(),
        idx: 0,
        expr_cert: Box::new(ProofCert::FVar {
            id: fvar_b,
            type_: Box::new(my_box_prop_bad.clone()),
        }),
        expr_type: Box::new(my_box_prop_bad),
        field_type: Box::new(prop.clone()),
    };

    let result = verifier.verify(&cert, &proj_expr);
    assert!(
        result.is_err(),
        "Missing universe levels should be rejected"
    );
    let err = result.unwrap_err();
    match &err {
        CertError::InvalidCert(msg) => {
            assert!(
                msg.contains("level_params") && msg.contains("type_levels"),
                "Error should mention level count mismatch, got: {}",
                msg
            );
        }
        other => panic!("Expected InvalidCert, got: {:?}", other),
    }
}

#[test]
fn test_verify_proj_struct_name_mismatch() {
    let env = env_with_my_pair();
    let mut verifier = CertVerifier::new(&env);

    let struct_name = Name::from_string("MyPair");
    let wrong_name = Name::from_string("WrongStruct");
    let my_pair_type = Expr::from_kind(ExprKind::Const(struct_name.clone(), vec![].into()));
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let fvar_p = FVarId(10);
    verifier
        .register_fvar(fvar_p, my_pair_type.clone())
        .unwrap();
    let p_expr = Expr::from_kind(ExprKind::FVar(fvar_p));

    // Expr says MyPair but cert says WrongStruct
    let proj_expr = Expr::proj(struct_name, 0, p_expr);

    let cert = ProofCert::Proj {
        struct_name: wrong_name,
        idx: 0,
        expr_cert: Box::new(ProofCert::FVar {
            id: fvar_p,
            type_: Box::new(my_pair_type.clone()),
        }),
        expr_type: Box::new(my_pair_type),
        field_type: Box::new(prop),
    };

    let result = verifier.verify(&cert, &proj_expr);
    assert!(
        result.is_err(),
        "Cert struct name ≠ expr proj name should fail"
    );
}

#[test]
fn test_verify_proj_index_mismatch() {
    let env = env_with_my_pair();
    let mut verifier = CertVerifier::new(&env);

    let struct_name = Name::from_string("MyPair");
    let my_pair_type = Expr::from_kind(ExprKind::Const(struct_name.clone(), vec![].into()));
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let fvar_p = FVarId(10);
    verifier
        .register_fvar(fvar_p, my_pair_type.clone())
        .unwrap();
    let p_expr = Expr::from_kind(ExprKind::FVar(fvar_p));

    // Expr says index 0, cert says index 1
    let proj_expr = Expr::proj(struct_name.clone(), 0, p_expr);

    let cert = ProofCert::Proj {
        struct_name,
        idx: 1,
        expr_cert: Box::new(ProofCert::FVar {
            id: fvar_p,
            type_: Box::new(my_pair_type.clone()),
        }),
        expr_type: Box::new(my_pair_type),
        field_type: Box::new(prop),
    };

    let result = verifier.verify(&cert, &proj_expr);
    assert!(result.is_err(), "Cert index ≠ expr index should fail");
}

#[test]
fn test_verify_proj_field_out_of_bounds() {
    let env = env_with_my_pair();
    let mut verifier = CertVerifier::new(&env);

    let struct_name = Name::from_string("MyPair");
    let my_pair_type = Expr::from_kind(ExprKind::Const(struct_name.clone(), vec![].into()));
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let fvar_p = FVarId(10);
    verifier
        .register_fvar(fvar_p, my_pair_type.clone())
        .unwrap();
    let p_expr = Expr::from_kind(ExprKind::FVar(fvar_p));

    // Index 5 is out of bounds (MyPair has 2 fields)
    let proj_expr = Expr::proj(struct_name.clone(), 5, p_expr);

    let cert = ProofCert::Proj {
        struct_name,
        idx: 5,
        expr_cert: Box::new(ProofCert::FVar {
            id: fvar_p,
            type_: Box::new(my_pair_type.clone()),
        }),
        expr_type: Box::new(my_pair_type),
        field_type: Box::new(prop),
    };

    let result = verifier.verify(&cert, &proj_expr);
    assert!(result.is_err(), "Out-of-bounds field index should fail");
}

#[test]
fn test_verify_proj_unknown_inductive() {
    let env = empty_env(); // No inductives registered
    let mut verifier = CertVerifier::new(&env);

    let struct_name = Name::from_string("Ghost");
    let ghost_type = Expr::from_kind(ExprKind::Const(struct_name.clone(), vec![].into()));
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let fvar_g = FVarId(30);
    verifier.register_fvar(fvar_g, ghost_type.clone()).unwrap();
    let g_expr = Expr::from_kind(ExprKind::FVar(fvar_g));

    let proj_expr = Expr::proj(struct_name.clone(), 0, g_expr);

    let cert = ProofCert::Proj {
        struct_name,
        idx: 0,
        expr_cert: Box::new(ProofCert::FVar {
            id: fvar_g,
            type_: Box::new(ghost_type.clone()),
        }),
        expr_type: Box::new(ghost_type),
        field_type: Box::new(prop),
    };

    let result = verifier.verify(&cert, &proj_expr);
    assert!(result.is_err(), "Unknown inductive in Proj should fail");
}

#[test]
fn test_verify_proj_field_type_forgery() {
    let env = env_with_my_pair();
    let mut verifier = CertVerifier::new(&env);

    let struct_name = Name::from_string("MyPair");
    let my_pair_type = Expr::from_kind(ExprKind::Const(struct_name.clone(), vec![].into()));
    // Cert claims field type is Sort(1) but actual field type is Prop=Sort(0)
    let sort1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

    let fvar_p = FVarId(10);
    verifier
        .register_fvar(fvar_p, my_pair_type.clone())
        .unwrap();
    let p_expr = Expr::from_kind(ExprKind::FVar(fvar_p));

    let proj_expr = Expr::proj(struct_name.clone(), 0, p_expr);

    let cert = ProofCert::Proj {
        struct_name,
        idx: 0,
        expr_cert: Box::new(ProofCert::FVar {
            id: fvar_p,
            type_: Box::new(my_pair_type.clone()),
        }),
        expr_type: Box::new(my_pair_type),
        field_type: Box::new(sort1), // FORGERY: claiming Sort(1) when field is Prop
    };

    let result = verifier.verify(&cert, &proj_expr);
    assert!(
        result.is_err(),
        "Forged field_type should be caught by independent derivation"
    );
}

#[test]
fn test_verify_proj_expr_type_mismatch() {
    let env = env_with_my_pair();
    let mut verifier = CertVerifier::new(&env);

    let struct_name = Name::from_string("MyPair");
    let my_pair_type = Expr::from_kind(ExprKind::Const(struct_name.clone(), vec![].into()));
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    // Cert claims the inner expression has type Prop, but it's actually MyPair
    let wrong_expr_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

    let fvar_p = FVarId(10);
    verifier
        .register_fvar(fvar_p, my_pair_type.clone())
        .unwrap();
    let p_expr = Expr::from_kind(ExprKind::FVar(fvar_p));

    let proj_expr = Expr::proj(struct_name.clone(), 0, p_expr);

    let cert = ProofCert::Proj {
        struct_name,
        idx: 0,
        expr_cert: Box::new(ProofCert::FVar {
            id: fvar_p,
            type_: Box::new(my_pair_type),
        }),
        expr_type: Box::new(wrong_expr_type), // WRONG: claims Sort(1) instead of MyPair
        field_type: Box::new(prop),
    };

    let result = verifier.verify(&cert, &proj_expr);
    assert!(result.is_err(), "Wrong expr_type in Proj cert should fail");
}

#[test]
fn test_verify_proj_multiple_constructors() {
    // derive_proj_field_type rejects types with != 1 constructor
    let mut env = Environment::new();
    let struct_name = Name::from_string("MultiCtor");
    let ctor1 = Name::from_string("MultiCtor.a");
    let ctor2 = Name::from_string("MultiCtor.b");
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let mc_const = Expr::from_kind(ExprKind::Const(struct_name.clone(), vec![].into()));

    env.register_inductive(InductiveVal {
        name: struct_name.clone(),
        level_params: vec![],
        type_: prop.clone(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![struct_name.clone()],
        constructor_names: vec![ctor1.clone(), ctor2.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: false,
        is_nested: false,
    });
    env.register_constructor(ConstructorVal {
        name: ctor1,
        inductive_name: struct_name.clone(),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, prop.clone(), mc_const.clone()),
        num_params: 0,
        num_fields: 1,
        constructor_idx: 0,
    });
    env.register_constructor(ConstructorVal {
        name: ctor2,
        inductive_name: struct_name.clone(),
        level_params: vec![],
        type_: mc_const.clone(),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 1,
    });

    let mut verifier = CertVerifier::new(&env);
    let fvar_m = FVarId(50);
    verifier.register_fvar(fvar_m, mc_const.clone()).unwrap();
    let m_expr = Expr::from_kind(ExprKind::FVar(fvar_m));

    let proj_expr = Expr::proj(struct_name.clone(), 0, m_expr);

    let cert = ProofCert::Proj {
        struct_name,
        idx: 0,
        expr_cert: Box::new(ProofCert::FVar {
            id: fvar_m,
            type_: Box::new(mc_const.clone()),
        }),
        expr_type: Box::new(mc_const),
        field_type: Box::new(prop),
    };

    let result = verifier.verify(&cert, &proj_expr);
    assert!(
        result.is_err(),
        "Proj on type with multiple constructors should fail"
    );
}

#[test]
fn test_verify_proj_cert_on_wrong_expr() {
    let env = env_with_my_pair();
    let mut verifier = CertVerifier::new(&env);

    let struct_name = Name::from_string("MyPair");
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let my_pair_type = Expr::from_kind(ExprKind::Const(struct_name.clone(), vec![].into()));

    // Expression is Sort(0) but cert is Proj — structure mismatch
    let wrong_expr = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let cert = ProofCert::Proj {
        struct_name,
        idx: 0,
        expr_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        expr_type: Box::new(my_pair_type),
        field_type: Box::new(prop),
    };

    let result = verifier.verify(&cert, &wrong_expr);
    assert!(
        result.is_err(),
        "Proj cert on non-Proj expression should fail"
    );
}
