// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{BinderInfo, FVarId, LocalContext, TypeChecker};

fn application(name: &str, levels: Vec<Level>, args: Vec<Expr>) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), levels), args)
}

#[test]
fn recursive_no_confusion_uses_registered_parameter_levels() {
    let env = Environment::with_prelude();
    let u = Level::param(Name::from_string("u"));
    let alpha = Expr::fvar(FVarId::new(0));
    let x = Expr::fvar(FVarId::new(1));
    let mut locals = LocalContext::new();
    locals.push_with_id(
        FVarId::new(0),
        Name::from_string("alpha"),
        Expr::sort(Level::succ(u.clone())),
        BinderInfo::Implicit,
    );
    locals.push_with_id(
        FVarId::new(1),
        Name::from_string("x"),
        alpha.clone(),
        BinderInfo::Default,
    );
    let bool_ty = Expr::const_str("Bool");
    let levels = vec![u.clone(), Level::zero()];
    let product_level = Level::max(u.clone(), Level::zero());
    let product = application("Prod", levels.clone(), vec![alpha.clone(), bool_ty.clone()]);
    let left = application(
        "Prod.mk",
        levels.clone(),
        vec![
            alpha.clone(),
            bool_ty.clone(),
            x.clone(),
            Expr::const_str("Bool.true"),
        ],
    );
    let right = application(
        "Prod.mk",
        levels,
        vec![
            alpha.clone(),
            bool_ty,
            x.clone(),
            Expr::const_str("Bool.false"),
        ],
    );
    let option = application("Option", vec![product_level.clone()], vec![product.clone()]);
    let some_left = application(
        "Option.some",
        vec![product_level.clone()],
        vec![product.clone(), left.clone()],
    );
    let some_right = application(
        "Option.some",
        vec![product_level.clone()],
        vec![product.clone(), right.clone()],
    );
    let list = application("List", vec![u.clone()], vec![alpha.clone()]);
    let nil = application("List.nil", vec![u.clone()], vec![alpha.clone()]);
    let one = application(
        "List.cons",
        vec![u.clone()],
        vec![alpha.clone(), x.clone(), nil],
    );
    let two = application("List.cons", vec![u.clone()], vec![alpha, x, one.clone()]);
    let checker = TypeChecker::with_context(&env, locals);
    for (label, ty, lhs, rhs, level) in [
        (
            "opaque product component",
            product,
            left,
            right,
            Level::succ(product_level.clone()),
        ),
        (
            "nested option/product",
            option,
            some_left,
            some_right,
            Level::succ(product_level),
        ),
        (
            "list length with opaque payload",
            list,
            one,
            two,
            Level::succ(u),
        ),
    ] {
        let proof = build_noconfusion_ne_proof(&env, &ty, &lhs, &rhs, &level).expect(label);
        for constant in crate::tactic::unfold::collect_consts(&proof) {
            assert!(
                env.axiom_deps(&constant)
                    .expect("registered proof constant")
                    .is_empty(),
                "{label}: domain axiom in {constant}"
            );
        }
        let equality = application("Eq", vec![level], vec![ty, lhs, rhs]);
        let target = Expr::pi(BinderInfo::Default, equality, Expr::const_str("False"));
        checker
            .check_type(&proof, &target)
            .unwrap_or_else(|error| panic!("{label}: {error:?}"));
    }
}
