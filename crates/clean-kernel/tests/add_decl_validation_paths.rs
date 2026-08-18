// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{BinderInfo, Declaration, EnvError, Environment, Expr, FVarId, Level, Name};

#[test]
fn add_decl_rejects_duplicate_name_on_second_insertion() {
    let mut env = Environment::new();
    let name = Name::from_string("dup_decl_1311");

    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("first declaration should succeed");

    let err = env
        .add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect_err("second declaration with same name must fail");

    assert!(
        matches!(err, EnvError::DuplicateName(ref duplicate) if *duplicate == name),
        "expected DuplicateName({name:?}), got: {err:?}"
    );
}

#[test]
fn add_decl_rejects_free_variable_in_type() {
    let mut env = Environment::new();
    let name = Name::from_string("fvar_in_type_1311");

    let err = env
        .add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::fvar(FVarId::new(0)),
        })
        .expect_err("declaration type containing fvar must fail");

    assert!(
        matches!(err, EnvError::ContainsFreeVar { name: ref decl_name, .. } if *decl_name == name),
        "expected ContainsFreeVar for {name:?}, got: {err:?}"
    );
}

#[test]
fn add_decl_rejects_free_variable_in_value() {
    let mut env = Environment::new();
    let name = Name::from_string("fvar_in_value_1311");

    let err = env
        .add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::prop(),
            value: Expr::fvar(FVarId::new(1)),
            is_reducible: false,
        })
        .expect_err("declaration value containing fvar must fail");

    assert!(
        matches!(err, EnvError::ContainsFreeVar { name: ref decl_name, .. } if *decl_name == name),
        "expected ContainsFreeVar for {name:?}, got: {err:?}"
    );
}

#[test]
fn add_decl_rejects_undefined_level_param_in_type() {
    let mut env = Environment::new();
    let name = Name::from_string("undef_param_type_1311");
    let declared = Name::from_string("u");
    let undefined = Name::from_string("v");

    let err = env
        .add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![declared],
            type_: Expr::sort(Level::param(undefined.clone())),
        })
        .expect_err("undefined level param in type must fail");

    assert!(
        matches!(
            err,
            EnvError::UndefinedLevelParam {
                name: ref decl_name,
                ref param
            } if *decl_name == name && *param == undefined
        ),
        "expected UndefinedLevelParam({undefined:?}) for {name:?}, got: {err:?}"
    );
}

#[test]
fn add_decl_rejects_undefined_level_param_in_value() {
    let mut env = Environment::new();
    let name = Name::from_string("undef_param_value_1311");
    let declared = Name::from_string("u");
    let undefined = Name::from_string("v");

    let err = env
        .add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![declared.clone()],
            type_: Expr::sort(Level::param(declared)),
            value: Expr::sort(Level::param(undefined.clone())),
            is_reducible: false,
        })
        .expect_err("undefined level param in value must fail");

    assert!(
        matches!(
            err,
            EnvError::UndefinedLevelParam {
                name: ref decl_name,
                ref param
            } if *decl_name == name && *param == undefined
        ),
        "expected UndefinedLevelParam({undefined:?}) for {name:?}, got: {err:?}"
    );
}

#[test]
fn add_decl_accepts_theorem_with_imax_param_zero_prop_sort() {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let alpha_name = Name::from_string("Alpha_1311_pos");
    let prop_name = Name::from_string("P_1311_pos");
    let proof_name = Name::from_string("p_1311_pos");
    let theorem_name = Name::from_string("thm_imax_u_zero_1311");

    env.add_decl(Declaration::Axiom {
        name: alpha_name.clone(),
        level_params: vec![u.clone()],
        type_: Expr::sort(Level::param(u.clone())),
    })
    .expect("Alpha : Sort(u) should succeed");

    env.add_decl(Declaration::Axiom {
        name: prop_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("P : Prop should succeed");

    env.add_decl(Declaration::Axiom {
        name: proof_name.clone(),
        level_params: vec![],
        type_: Expr::const_(prop_name.clone(), vec![]),
    })
    .expect("p : P should succeed");

    let alpha_u = Expr::const_(alpha_name, vec![Level::param(u.clone())]);
    let theorem_type = Expr::pi(
        BinderInfo::Default,
        alpha_u.clone(),
        Expr::const_(prop_name, vec![]),
    );
    let theorem_value = Expr::lam(
        BinderInfo::Default,
        alpha_u,
        Expr::const_(proof_name, vec![]),
    );

    env.add_decl(Declaration::Theorem {
        name: theorem_name.clone(),
        level_params: vec![u],
        type_: theorem_type,
        value: theorem_value,
    })
    .expect("theorem sort imax(u, 0) should reduce to Prop and be accepted");

    assert!(
        env.get_const(&theorem_name).is_some(),
        "accepted theorem should be present in the environment"
    );
}

#[test]
fn add_decl_rejects_theorem_with_imax_zero_param_nonprop_sort() {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let alpha_name = Name::from_string("Alpha_1311_neg");
    let witness_name = Name::from_string("a_1311_neg");
    let prop_name = Name::from_string("P_1311_neg");
    let theorem_name = Name::from_string("thm_imax_zero_u_1311");

    env.add_decl(Declaration::Axiom {
        name: alpha_name.clone(),
        level_params: vec![u.clone()],
        type_: Expr::sort(Level::param(u.clone())),
    })
    .expect("Alpha : Sort(u) should succeed");

    env.add_decl(Declaration::Axiom {
        name: witness_name.clone(),
        level_params: vec![u.clone()],
        type_: Expr::const_(alpha_name.clone(), vec![Level::param(u.clone())]),
    })
    .expect("a : Alpha should succeed");

    env.add_decl(Declaration::Axiom {
        name: prop_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("P : Prop should succeed");

    let prop_const = Expr::const_(prop_name, vec![]);
    let alpha_const = Expr::const_(alpha_name, vec![Level::param(u.clone())]);
    let theorem_type = Expr::pi(BinderInfo::Default, prop_const.clone(), alpha_const.clone());
    let theorem_value = Expr::lam(
        BinderInfo::Default,
        prop_const,
        Expr::const_(witness_name, vec![Level::param(u.clone())]),
    );

    let err = env
        .add_decl(Declaration::Theorem {
            name: theorem_name.clone(),
            level_params: vec![u],
            type_: theorem_type,
            value: theorem_value,
        })
        .expect_err("theorem sort imax(0, u) is not definitively Prop and must fail");

    assert!(
        matches!(
            err,
            EnvError::TheoremTypeNotProp {
                ref name,
                ref sort
            } if *name == theorem_name && !sort.is_zero()
        ),
        "expected TheoremTypeNotProp with non-zero sort, got: {err:?}"
    );
}

#[test]
fn add_decl_rejects_meta_tagged_fvar_in_type() {
    // META_FVAR_TAG encodes metavariables as FVars with the high bit set.
    // These must be rejected by add_decl (caught by the fvar check).
    const META_FVAR_TAG: u64 = 1 << 63;
    let mut env = Environment::new();
    let name = Name::from_string("meta_fvar_type_1300");

    let err = env
        .add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::fvar(FVarId::new(META_FVAR_TAG | 42)),
        })
        .expect_err("declaration with meta-tagged FVar in type must fail");

    assert!(
        matches!(err, EnvError::ContainsFreeVar { name: ref decl_name, .. } if *decl_name == name),
        "expected ContainsFreeVar for meta-tagged FVar, got: {err:?}"
    );
}

#[test]
fn add_decl_rejects_meta_tagged_fvar_in_value() {
    const META_FVAR_TAG: u64 = 1 << 63;
    let mut env = Environment::new();
    let name = Name::from_string("meta_fvar_value_1300");

    let err = env
        .add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::prop(),
            value: Expr::fvar(FVarId::new(META_FVAR_TAG)),
            is_reducible: false,
        })
        .expect_err("declaration with meta-tagged FVar in value must fail");

    assert!(
        matches!(err, EnvError::ContainsFreeVar { name: ref decl_name, .. } if *decl_name == name),
        "expected ContainsFreeVar for meta-tagged FVar, got: {err:?}"
    );
}

#[test]
fn add_decl_rejects_nested_fvar_in_app() {
    // Verify the O(1) metadata propagation catches FVars nested in expressions
    let mut env = Environment::new();
    let name = Name::from_string("nested_fvar_1300");

    let nested = Expr::app(Expr::sort(Level::zero()), Expr::fvar(FVarId::new(99)));
    let err = env
        .add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: nested,
        })
        .expect_err("nested FVar must be caught by O(1) metadata check");

    assert!(
        matches!(err, EnvError::ContainsFreeVar { name: ref decl_name, .. } if *decl_name == name),
        "expected ContainsFreeVar for nested FVar, got: {err:?}"
    );
}

#[test]
fn add_decl_rejects_deeply_nested_fvar_in_lambda() {
    // Verify has_fvar_quick propagates through lambda/pi binders
    let mut env = Environment::new();
    let name = Name::from_string("deep_fvar_1300");

    let fvar_expr = Expr::fvar(FVarId::new(7));
    let inner = Expr::lam(BinderInfo::Default, Expr::prop(), fvar_expr);
    let outer = Expr::pi(BinderInfo::Default, inner, Expr::prop());

    let err = env
        .add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: outer,
        })
        .expect_err("deeply nested FVar must be caught");

    assert!(
        matches!(err, EnvError::ContainsFreeVar { name: ref decl_name, .. } if *decl_name == name),
        "expected ContainsFreeVar for deeply nested FVar, got: {err:?}"
    );
}
