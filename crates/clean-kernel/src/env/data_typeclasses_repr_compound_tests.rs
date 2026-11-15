// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The default prelude's `Repr` renderings through the kernel: every instance
//! is a checked, axiom-free definition, and no two values (or element
//! instances) Lean renders differently are definitionally equal renderings.
//! Each `!is_def_eq` below is a theorem Lean 4.8 refuses with `type mismatch`
//! (measured 2026-09-30 with the pinned toolchain as oracle) and the earlier
//! `fun _ _ => ""` stubs accepted.

use super::*;
use crate::env::types::ConstantKind;
use crate::tc::TypeChecker;

fn c0(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat() -> Expr {
    c0("Nat")
}

/// `@repr.{0} ty inst x`.
fn repr_of(ty: Expr, inst: Expr, x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("repr"), vec![Level::zero()]),
        [ty, inst, x],
    )
}

fn at0(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![Level::zero()])
}

fn some_nat(n: u64) -> Expr {
    Expr::apps(at0("Option.some"), [nat(), Expr::nat_lit(n)])
}

fn option_nat() -> Expr {
    Expr::app(at0("Option"), nat())
}

fn inst_repr_option_nat() -> Expr {
    Expr::apps(at0("instReprOption"), [nat(), c0("instReprNat")])
}

#[test]
fn test_repr_render_registered_opaque_with_witness_value() {
    let env = Environment::with_prelude();
    let info = env
        .get_const(&Name::from_string(REPR_RENDER))
        .expect("Clean.Repr.render is registered");
    assert_eq!(info.kind, ConstantKind::Opaque, "never δ-unfolded");
    assert!(info.value.is_some(), "a witness value, so not an axiom");
}

#[test]
fn test_repr_compound_instances_checked_axiom_free_registered() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for (name, n_levels) in [
        ("instReprOption", 1usize),
        ("Clean.instReprProdOfRepr", 2),
        ("instReprList", 1),
        ("instReprNat", 0),
    ] {
        let n = Name::from_string(name);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("{name} missing"));
        assert_eq!(info.kind, ConstantKind::Definition, "{name}");
        assert!(
            env.instances().any(|i| i.name == n),
            "{name} not an instance"
        );
        let deps = env.axiom_deps(&n).expect("registered");
        assert!(deps.is_empty(), "{name} axiom closure: {deps:?}");
        let levels = vec![Level::zero(); n_levels];
        let _checked = tc
            .infer_type(&Expr::const_(n, levels))
            .unwrap_or_else(|e| panic!("{name} must type-check: {e:?}"));
    }
}

#[test]
fn test_repr_option_distinct_values_are_distinct_renderings() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let one = repr_of(option_nat(), inst_repr_option_nat(), some_nat(1));
    let two = repr_of(option_nat(), inst_repr_option_nat(), some_nat(2));
    let ty = tc.infer_type(&one).expect("`repr (some 1)` type-checks");
    assert!(tc.is_def_eq(&ty, &c0("String")), "a rendering is a String");
    let one_again = repr_of(option_nat(), inst_repr_option_nat(), some_nat(1));
    assert!(
        tc.is_def_eq(&one, &one_again),
        "equal values, equal renderings"
    );
    assert!(
        !tc.is_def_eq(&one, &two),
        "Lean refuses repr (some 1) = repr (some 2)"
    );
    assert!(
        !tc.is_def_eq(&one, &Expr::str_lit("")),
        "no constant rendering"
    );
}

#[test]
fn test_repr_nat_and_list_distinct_values_are_distinct_renderings() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let r1 = repr_of(nat(), c0("instReprNat"), Expr::nat_lit(1));
    let r2 = repr_of(nat(), c0("instReprNat"), Expr::nat_lit(2));
    assert!(!tc.is_def_eq(&r1, &r2), "Lean refuses repr 1 = repr 2");

    let list_nat = Expr::app(at0("List"), nat());
    let inst_list = Expr::apps(at0("instReprList"), [nat(), c0("instReprNat")]);
    let nil = Expr::app(at0("List.nil"), nat());
    let one = Expr::apps(at0("List.cons"), [nat(), Expr::nat_lit(1), nil.clone()]);
    let a = repr_of(list_nat.clone(), inst_list.clone(), one);
    let b = repr_of(list_nat, inst_list, nil);
    assert!(!tc.is_def_eq(&a, &b), "Lean refuses repr [1] = repr []");
}

#[test]
fn test_repr_list_element_instance_reaches_the_rendering() {
    // Two different `Repr Nat` instances render the same list differently in
    // Lean; the packed `(inst, l)` keeps them apart here.
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let other_nat_inst = Expr::apps(
        at0("Repr.mk"),
        [
            nat(),
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam(BinderInfo::Default, nat(), Expr::str_lit("x")),
            ),
        ],
    );
    let list_nat = Expr::app(at0("List"), nat());
    let nil = Expr::app(at0("List.nil"), nat());
    let via = |elem_inst: Expr| {
        repr_of(
            list_nat.clone(),
            Expr::apps(at0("instReprList"), [nat(), elem_inst]),
            nil.clone(),
        )
    };
    assert!(!tc.is_def_eq(&via(c0("instReprNat")), &via(other_nat_inst)));
}

#[test]
fn test_repr_prod_distinct_values_are_distinct_renderings() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let levels = vec![Level::zero(), Level::zero()];
    let prod_nn = Expr::apps(
        Expr::const_(Name::from_string("Prod"), levels.clone()),
        [nat(), nat()],
    );
    let inst = Expr::apps(
        Expr::const_(
            Name::from_string("Clean.instReprProdOfRepr"),
            levels.clone(),
        ),
        [nat(), nat(), c0("instReprNat"), c0("instReprNat")],
    );
    let pair = |a: u64, b: u64| {
        Expr::apps(
            Expr::const_(Name::from_string("Prod.mk"), levels.clone()),
            [nat(), nat(), Expr::nat_lit(a), Expr::nat_lit(b)],
        )
    };
    let r12 = repr_of(prod_nn.clone(), inst.clone(), pair(1, 2));
    let r13 = repr_of(prod_nn, inst, pair(1, 3));
    let ty = tc.infer_type(&r12).expect("`repr (1, 2)` type-checks");
    assert!(tc.is_def_eq(&ty, &c0("String")), "a rendering is a String");
    assert!(
        !tc.is_def_eq(&r12, &r13),
        "Lean refuses repr (1, 2) = repr (1, 3)"
    );
}

#[test]
fn test_repr_compound_import_mode_is_not_seeded() {
    // The String-valued stubs must not shadow Lean's Format-valued ones.
    let env = Environment::try_with_prelude_for_import().expect("import prelude builds");
    for name in [REPR_RENDER, "instReprOption", "Clean.instReprProdOfRepr"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} seeded under import"
        );
    }
}
