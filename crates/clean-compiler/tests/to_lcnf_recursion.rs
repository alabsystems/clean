// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_compiler::constant_to_decl;
use clean_kernel::env::{ConstantInfo, TrustedEnvExt};
use clean_kernel::{BinderInfo, Environment, Expr, Name};

fn make_env() -> Environment {
    Environment::default()
}

fn lambda_to(callee: &Name, ty: &Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        ty.clone(),
        Expr::app(Expr::const_(callee.clone(), Vec::new()), Expr::bvar(0)),
    )
}

#[test]
fn test_constant_to_decl_strips_runtime_param_binders_from_return_type() {
    let mut env = make_env();
    let ty_name = Name::from_string("ReturnType");
    let ty = Expr::const_(ty_name.clone(), Vec::new());
    let id_name = Name::from_string("ReturnType.id");
    let fn_ty = Expr::arrow(ty.clone(), ty.clone());
    let value = Expr::lam(BinderInfo::Default, ty.clone(), Expr::bvar(0));

    env.extend_constants_unchecked(
        [
            ConstantInfo::new(ty_name, vec![], Expr::type_(), None, false),
            ConstantInfo::new(id_name.clone(), vec![], fn_ty, Some(value), false),
        ]
        .into_iter(),
    );

    let decl = constant_to_decl(&env, env.get_const(&id_name).unwrap())
        .unwrap()
        .expect("definition lowers");

    assert_eq!(decl.params.len(), 1);
    assert_eq!(decl.ty, ty);
}

#[test]
fn test_constant_to_decl_marks_mutual_recursion() {
    let mut env = make_env();
    let ty_name = Name::from_string("MyType");
    let ty = Expr::const_(ty_name.clone(), Vec::new());
    let even_name = Name::from_string("Even.loop");
    let odd_name = Name::from_string("Odd.loop");
    let fn_ty = Expr::arrow(ty.clone(), ty.clone());

    env.extend_constants_unchecked(
        [
            ConstantInfo::new(ty_name, vec![], Expr::type_(), None, false),
            ConstantInfo::new(
                even_name.clone(),
                vec![],
                fn_ty.clone(),
                Some(lambda_to(&odd_name, &ty)),
                false,
            ),
            ConstantInfo::new(
                odd_name.clone(),
                vec![],
                fn_ty,
                Some(lambda_to(&even_name, &ty)),
                false,
            ),
        ]
        .into_iter(),
    );

    let even_decl = constant_to_decl(&env, env.get_const(&even_name).unwrap())
        .unwrap()
        .expect("mutual definition lowers");
    let odd_decl = constant_to_decl(&env, env.get_const(&odd_name).unwrap())
        .unwrap()
        .expect("mutual definition lowers");

    assert!(even_decl.recursive);
    assert!(odd_decl.recursive);
}

#[test]
fn test_constant_to_decl_marks_transitive_mutual_recursion() {
    let mut env = make_env();
    let ty_name = Name::from_string("CycleType");
    let ty = Expr::const_(ty_name.clone(), Vec::new());
    let a_name = Name::from_string("Cycle.a");
    let b_name = Name::from_string("Cycle.b");
    let c_name = Name::from_string("Cycle.c");
    let fn_ty = Expr::arrow(ty.clone(), ty.clone());

    env.extend_constants_unchecked(
        [
            ConstantInfo::new(ty_name, vec![], Expr::type_(), None, false),
            ConstantInfo::new(
                a_name.clone(),
                vec![],
                fn_ty.clone(),
                Some(lambda_to(&b_name, &ty)),
                false,
            ),
            ConstantInfo::new(
                b_name.clone(),
                vec![],
                fn_ty.clone(),
                Some(lambda_to(&c_name, &ty)),
                false,
            ),
            ConstantInfo::new(
                c_name.clone(),
                vec![],
                fn_ty,
                Some(lambda_to(&a_name, &ty)),
                false,
            ),
        ]
        .into_iter(),
    );

    let a_decl = constant_to_decl(&env, env.get_const(&a_name).unwrap())
        .unwrap()
        .expect("transitive cycle lowers");

    assert!(a_decl.recursive);
}

#[test]
fn test_constant_to_decl_ignores_type_only_dependency_cycle() {
    let mut env = make_env();
    let ty_name = Name::from_string("CycleType");
    let ty = Expr::const_(ty_name.clone(), Vec::new());
    let base_name = Name::from_string("Cycle.base");
    let f_name = Name::from_string("Cycle.f");
    let g_name = Name::from_string("Cycle.g");
    let fn_ty = Expr::arrow(ty.clone(), ty.clone());

    env.extend_constants_unchecked(
        [
            ConstantInfo::new(ty_name, vec![], Expr::type_(), None, false),
            ConstantInfo::new(base_name.clone(), vec![], ty.clone(), None, false),
            ConstantInfo::new(
                f_name.clone(),
                vec![],
                fn_ty.clone(),
                Some(lambda_to(&g_name, &ty)),
                false,
            ),
            ConstantInfo::new(
                g_name.clone(),
                vec![],
                fn_ty,
                Some(Expr::lam(
                    BinderInfo::Default,
                    Expr::const_(f_name.clone(), Vec::new()),
                    Expr::const_(base_name, Vec::new()),
                )),
                false,
            ),
        ]
        .into_iter(),
    );

    let f_decl = constant_to_decl(&env, env.get_const(&f_name).unwrap())
        .unwrap()
        .expect("definition lowers");

    assert!(
        !f_decl.recursive,
        "binder-type references in a callee must not mark the caller recursive"
    );
}

#[test]
fn test_constant_to_decl_does_not_mark_caller_of_recursive_callee() {
    let mut env = make_env();
    let ty_name = Name::from_string("CallType");
    let ty = Expr::const_(ty_name.clone(), Vec::new());
    let caller_name = Name::from_string("Call.caller");
    let loop_name = Name::from_string("Call.loop");
    let fn_ty = Expr::arrow(ty.clone(), ty.clone());

    env.extend_constants_unchecked(
        [
            ConstantInfo::new(ty_name, vec![], Expr::type_(), None, false),
            ConstantInfo::new(
                caller_name.clone(),
                vec![],
                fn_ty.clone(),
                Some(lambda_to(&loop_name, &ty)),
                false,
            ),
            ConstantInfo::new(
                loop_name.clone(),
                vec![],
                fn_ty,
                Some(lambda_to(&loop_name, &ty)),
                false,
            ),
        ]
        .into_iter(),
    );

    let caller_decl = constant_to_decl(&env, env.get_const(&caller_name).unwrap())
        .unwrap()
        .expect("definition lowers");
    let loop_decl = constant_to_decl(&env, env.get_const(&loop_name).unwrap())
        .unwrap()
        .expect("definition lowers");

    assert!(
        !caller_decl.recursive,
        "calling a separately recursive definition must not mark the caller recursive"
    );
    assert!(loop_decl.recursive);
}
