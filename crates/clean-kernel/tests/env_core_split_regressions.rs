// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Environment, Expr, Level, Name, TypeChecker};

fn const0(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn assert_field_index(env: &Environment, struct_name: &str, field_name: &str, expected: u32) {
    assert_eq!(
        env.get_structure_field_index(
            &Name::from_string(struct_name),
            &Name::from_string(field_name),
        ),
        Some(expected),
        "{struct_name}.{field_name} should map to field index {expected}"
    );
}

fn assert_binary_structure_fields(env: &Environment, struct_name: &str) {
    assert_field_index(env, struct_name, "fst", 0);
    assert_field_index(env, struct_name, "snd", 1);
}

fn assert_const_registered(env: &Environment, const_name: &str) {
    assert!(
        env.get_const(&Name::from_string(const_name)).is_some(),
        "{const_name} should be registered"
    );
}

fn assert_core_trust_surface(env: &Environment) {
    assert_const_registered(env, "sorry");
    assert_const_registered(env, "trustedArith");
    assert_const_registered(env, "trustedAy");
}

struct SwapFixture {
    unit_ty: Expr,
    bool_ty: Expr,
    unit_val: Expr,
    bool_false: Expr,
    swap_name: String,
    fst_name: String,
    snd_name: String,
    swapped: Expr,
}

fn mk_pair_expr(
    struct_name: &str,
    levels: &[Level],
    unit_ty: &Expr,
    bool_ty: &Expr,
    unit_val: &Expr,
    bool_false: &Expr,
) -> Expr {
    let mk_name = format!("{struct_name}.mk");
    Expr::apps(
        Expr::const_(Name::from_string(&mk_name), levels.to_vec()),
        [
            unit_ty.clone(),
            bool_ty.clone(),
            unit_val.clone(),
            bool_false.clone(),
        ],
    )
}

fn assert_swap_type(
    tc: &TypeChecker<'_>,
    struct_name: &str,
    swap_name: &str,
    levels: &[Level],
    unit_ty: &Expr,
    bool_ty: &Expr,
    swapped: &Expr,
) {
    let expected_type = Expr::apps(
        Expr::const_(Name::from_string(struct_name), levels.to_vec()),
        [bool_ty.clone(), unit_ty.clone()],
    );
    let inferred_type = tc
        .infer_type(swapped)
        .unwrap_or_else(|_| panic!("{swap_name} should typecheck"));
    assert!(
        tc.is_def_eq(&inferred_type, &expected_type),
        "{swap_name} should return {struct_name} Bool Unit"
    );
}

fn assert_projection_value(
    tc: &TypeChecker<'_>,
    projection_name: &str,
    levels: &[Level],
    bool_ty: &Expr,
    unit_ty: &Expr,
    swapped: &Expr,
    expected: &Expr,
    message: &str,
) {
    let actual = tc.whnf(&Expr::apps(
        Expr::const_(Name::from_string(projection_name), levels.to_vec()),
        [bool_ty.clone(), unit_ty.clone(), swapped.clone()],
    ));
    assert!(tc.is_def_eq(&actual, expected), "{message}");
}

fn build_swap_fixture(struct_name: &str, levels: &[Level]) -> SwapFixture {
    let unit_ty = const0("Unit");
    let bool_ty = const0("Bool");
    let unit_val = const0("Unit.unit");
    let bool_false = const0("Bool.false");
    let swap_name = format!("{struct_name}.swap");
    let fst_name = format!("{struct_name}.fst");
    let snd_name = format!("{struct_name}.snd");
    let pair = mk_pair_expr(
        struct_name,
        levels,
        &unit_ty,
        &bool_ty,
        &unit_val,
        &bool_false,
    );
    let swapped = Expr::apps(
        Expr::const_(Name::from_string(&swap_name), levels.to_vec()),
        [unit_ty.clone(), bool_ty.clone(), pair],
    );

    SwapFixture {
        unit_ty,
        bool_ty,
        unit_val,
        bool_false,
        swap_name,
        fst_name,
        snd_name,
        swapped,
    }
}

fn assert_swap_reverses_fields(env: &Environment, struct_name: &str, levels: Vec<Level>) {
    let tc = TypeChecker::new(env);
    let fixture = build_swap_fixture(struct_name, &levels);

    assert_swap_type(
        &tc,
        struct_name,
        &fixture.swap_name,
        &levels,
        &fixture.unit_ty,
        &fixture.bool_ty,
        &fixture.swapped,
    );

    assert_projection_value(
        &tc,
        &fixture.fst_name,
        &levels,
        &fixture.bool_ty,
        &fixture.unit_ty,
        &fixture.swapped,
        &fixture.bool_false,
        &format!(
            "{} fst should reduce to the original second field",
            fixture.swap_name
        ),
    );
    assert_projection_value(
        &tc,
        &fixture.snd_name,
        &levels,
        &fixture.bool_ty,
        &fixture.unit_ty,
        &fixture.swapped,
        &fixture.unit_val,
        &format!(
            "{} snd should reduce to the original first field",
            fixture.swap_name
        ),
    );
}

#[test]
fn test_prod_swap_whnf_reverses_fields_after_core_split() {
    let mut env = Environment::new();
    env.init_bool().expect("init_bool");
    env.init_unit().expect("init_unit");
    env.init_prod().expect("init_prod");
    assert_binary_structure_fields(&env, "Prod");
    assert_swap_reverses_fields(&env, "Prod", vec![Level::zero(), Level::zero()]);
}

#[test]
fn test_pprod_swap_whnf_reverses_fields_after_core_split() {
    let mut env = Environment::new();
    env.init_bool().expect("init_bool");
    env.init_unit().expect("init_unit");
    env.init_pprod().expect("init_pprod");
    assert_binary_structure_fields(&env, "PProd");
    let type0 = Level::succ(Level::zero());
    assert_swap_reverses_fields(&env, "PProd", vec![type0.clone(), type0]);
}

#[test]
fn test_sigma_structure_fields_register_after_core_split() {
    let mut env = Environment::new();
    env.init_sigma().expect("init_sigma");
    assert_binary_structure_fields(&env, "Sigma");
}

#[test]
fn test_with_prelude_exposes_split_core_structure_metadata() {
    let env = Environment::with_prelude();
    assert_binary_structure_fields(&env, "Prod");
    assert_binary_structure_fields(&env, "Sigma");
    assert_field_index(&env, "Subtype", "val", 0);
    assert_field_index(&env, "Subtype", "property", 1);
}

#[test]
fn test_environment_constructors_expose_split_core_trust_surface() {
    let env = Environment::new();
    assert_core_trust_surface(&env);

    let env = Environment::with_prelude();
    assert_core_trust_surface(&env);
}
