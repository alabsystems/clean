// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Actual declaration admission and projection checks across universe instances.
//! These are production regression tests, not a proof of the model-to-Rust bridge.
//! A schematic Prop declaration may store data, but that does not permit its
//! data projection. A universe-polymorphic data declaration must instead satisfy
//! its field bound before any particular universe instance is selected.

use clean_kernel::cert::{CertError, CertVerifier, ProofCert};
use clean_kernel::env::{EnvError, Environment};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveError, InductiveType};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::{TypeChecker, TypeError};
use std::sync::Arc;

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn base_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("admit actual Nat and Nat.zero");
    env.init_true_false()
        .expect("admit actual True and True.intro");
    env
}

/// One stored parameterized declaration, never pre-instantiated at zero or one.
/// `MyExists : (A : Sort u) -> Prop`, or `Box : (A : Sort u) -> Sort u`.
fn add_family(env: &mut Environment, name: &str, in_prop: bool) -> Name {
    let family = Name::from_string(name);
    let ctor = Name::from_string(&format!("{name}.mk"));
    let parameter = Name::from_string("u");
    let level = Level::param(parameter.clone());
    let family_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(level.clone()),
        if in_prop {
            Expr::prop()
        } else {
            Expr::sort(level.clone())
        },
    );
    let constructor_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(level.clone()),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(Expr::const_(family.clone(), vec![level]), Expr::bvar(1)),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![parameter.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: family.clone(),
            type_: family_type.clone(),
            constructors: vec![Constructor {
                name: ctor.clone(),
                type_: constructor_type.clone(),
            }],
        }],
    })
    .expect("the schematic family and its actual constructor must be admitted");

    let stored_family = env.get_inductive(&family).expect("stored family metadata");
    let stored_ctor = env
        .get_constructor(&ctor)
        .expect("stored constructor metadata");
    assert_eq!(stored_family.level_params, vec![parameter.clone()]);
    assert_eq!(stored_ctor.level_params, vec![parameter]);
    assert_eq!(stored_family.type_, family_type);
    assert_eq!(stored_ctor.type_, constructor_type);
    assert_eq!(stored_family.constructor_names, vec![ctor]);
    assert_eq!(stored_ctor.inductive_name, family);
    assert_eq!(stored_ctor.num_params, 1);
    assert_eq!(stored_ctor.num_fields, 1);
    family
}

fn instance(family: &Name, level: Level, domain: Expr, value: Expr) -> (Expr, Expr) {
    let instance_type = Expr::app(
        Expr::const_(family.clone(), vec![level.clone()]),
        domain.clone(),
    );
    let inner = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string(&format!("{family}.mk")), vec![level]),
            domain,
        ),
        value,
    );
    (inner, instance_type)
}

fn genuine_inner(env: &Environment, inner: &Expr, expected: &Expr) -> ProofCert {
    assert_eq!(
        TypeChecker::new(env)
            .infer_type_full(inner)
            .expect("the complete constructor application must type-check"),
        *expected
    );
    let (actual, certificate) = TypeChecker::new(env)
        .infer_type_with_cert(inner)
        .expect("generate a genuine constructor certificate");
    assert_eq!(actual, *expected);
    assert_eq!(
        CertVerifier::new(env)
            .verify(&certificate, inner)
            .expect("independently verify the constructor certificate"),
        *expected
    );
    certificate
}

fn accepts(env: &Environment, family: Name, level: Level, proof: bool, in_prop: bool) {
    let domain = constant(if proof { "True" } else { "Nat" });
    let value = constant(if proof { "True.intro" } else { "Nat.zero" });
    let (inner, instance_type) = instance(&family, level.clone(), domain.clone(), value.clone());
    let _ = genuine_inner(env, &inner, &instance_type);
    assert_eq!(
        TypeChecker::new(env).infer_sort(&instance_type).unwrap(),
        if in_prop { Level::zero() } else { level }
    );
    let projection = Expr::proj(family, 0, inner);

    // A fresh checker exercises public release inference before certificate
    // generation could populate its cache. Repeat to cover the cached path.
    let public_checker = TypeChecker::new(env);
    for _ in 0..2 {
        assert_eq!(public_checker.infer_type(&projection).unwrap(), domain);
    }
    assert_eq!(
        TypeChecker::new(env).infer_type_full(&projection).unwrap(),
        domain
    );
    TypeChecker::new(env)
        .check_type(&projection, &domain)
        .expect("check the permitted projection against its actual field domain");
    let (actual, certificate) = TypeChecker::new(env)
        .infer_type_with_cert(&projection)
        .expect("generate the permitted projection certificate");
    assert_eq!(actual, domain);
    assert_eq!(
        CertVerifier::new(env)
            .verify(&certificate, &projection)
            .expect("independently derive the instantiated field domain"),
        domain
    );
    assert!(TypeChecker::new(env).is_def_eq(&projection, &value));
}

#[test]
fn prop_family_at_zero_accepts_true_field_projection() {
    let mut env = base_env();
    let family = add_family(&mut env, "MyExists", true);
    accepts(&env, family, Level::zero(), true, true);
}

#[test]
fn prop_family_at_one_rejects_nat_field_projection_and_certificate() {
    let mut env = base_env();
    let family = add_family(&mut env, "MyExists", true);
    let (inner, inner_type) = instance(
        &family,
        Level::succ(Level::zero()),
        constant("Nat"),
        constant("Nat.zero"),
    );
    let inner_cert = genuine_inner(&env, &inner, &inner_type);
    assert_eq!(
        TypeChecker::new(&env).infer_sort(&inner_type).unwrap(),
        Level::zero()
    );
    let projection = Expr::proj(family.clone(), 0, inner);
    let public_checker = TypeChecker::new(&env);
    for _ in 0..2 {
        assert!(matches!(
            public_checker.infer_type(&projection),
            Err(TypeError::InvalidProjFromProp { field_idx: 0 })
        ));
    }
    assert!(matches!(
        TypeChecker::new(&env).infer_type_full(&projection),
        Err(TypeError::InvalidProjFromProp { field_idx: 0 })
    ));
    assert!(matches!(
        TypeChecker::new(&env).infer_type_with_cert(&projection),
        Err(TypeError::InvalidProjFromProp { field_idx: 0 })
    ));

    // The projection rule alone is forbidden: its inner certificate and claimed
    // Nat field domain are genuine, so this is not a malformed-input refusal.
    let certificate = ProofCert::Proj {
        struct_name: family,
        idx: 0,
        expr_cert: Arc::new(inner_cert),
        expr_type: Box::new(inner_type),
        field_type: Box::new(constant("Nat")),
    };
    let result = CertVerifier::new(&env).verify(&certificate, &projection);
    assert!(
        matches!(&result, Err(CertError::InvalidCert(message))
            if message.contains("field 0 of a Prop structure must itself be in Prop")),
        "the verifier must reject precisely the Prop elimination: {result:?}"
    );
}

#[test]
fn universe_polymorphic_box_accepts_newly_prop_instance() {
    let mut env = base_env();
    let family = add_family(&mut env, "Box", false);
    accepts(
        &env,
        family.clone(),
        Level::succ(Level::zero()),
        false,
        false,
    );
    accepts(&env, family, Level::zero(), true, false);
}

#[test]
fn universe_polymorphic_box_accepts_data_instance_after_prop_instance() {
    let mut env = base_env();
    let family = add_family(&mut env, "Box", false);
    accepts(&env, family.clone(), Level::zero(), true, false);
    accepts(&env, family, Level::succ(Level::zero()), false, false);
}

#[test]
fn schematic_universe_leak_is_refused_before_any_instance_exists() {
    let mut env = base_env();
    let family = Name::from_string("Leak");
    let ctor = Name::from_string("Leak.mk");
    let parameter = Name::from_string("u");
    let level = Level::param(parameter.clone());
    let before = (
        env.num_constants(),
        env.num_inductives(),
        env.num_constructors(),
        env.num_recursors(),
        env.generation(),
    );
    let result = env.add_inductive(InductiveDecl {
        level_params: vec![parameter],
        num_params: 0,
        types: vec![InductiveType {
            name: family.clone(),
            type_: Expr::sort(level.clone()),
            constructors: vec![Constructor {
                name: ctor.clone(),
                type_: Expr::pi(
                    BinderInfo::Default,
                    constant("Nat"),
                    Expr::const_(family.clone(), vec![level]),
                ),
            }],
        }],
    });
    assert!(
        matches!(&result, Err(EnvError::Inductive(InductiveError::UniverseMismatch(name)))
            if name == &ctor),
        "the schematic Nat-field bound must fail at admission: {result:?}"
    );
    assert_eq!(
        (
            env.num_constants(),
            env.num_inductives(),
            env.num_constructors(),
            env.num_recursors(),
            env.generation(),
        ),
        before
    );
    assert!(env.get_const(&family).is_none());
    assert!(env.get_inductive(&family).is_none());
    assert!(env.get_const(&ctor).is_none());
    assert!(env.get_constructor(&ctor).is_none());
    assert!(env.get_recursor(&Name::from_string("Leak.rec")).is_none());

    // The same environment still admits the valid bounded declaration.
    let valid = add_family(&mut env, "Box", false);
    accepts(&env, valid, Level::succ(Level::zero()), false, false);
}
