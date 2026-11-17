// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::CompiledBefore;
use clean_kernel::{BinderInfo, Declaration};

fn name(value: &str) -> Name {
    Name::from_string(value)
}

fn identity() -> Expr {
    Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0))
}

fn call(target: &str) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::app(Expr::const_str(target), Expr::bvar(0)),
    )
}

fn definition(env: &mut Environment, name: Name, value: Expr) {
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")),
        value,
        is_reducible: false,
    })
    .unwrap();
}

fn environment() -> Environment {
    let mut env = Environment::with_prelude();
    for value in ["logical", "runtime", "other"] {
        definition(&mut env, name(value), identity());
    }
    definition(&mut env, name("chosen"), call("logical"));
    env.register_implemented_by(name("logical"), name("runtime"));
    env
}

#[test]
fn compiler_binding_plan_retains_logical_runtime_and_family_members() {
    let env = environment();
    let roots = [name("chosen")];
    let plan = RuntimeBindingPlan::discover(&env, &roots, 100).unwrap();
    let members: BTreeSet<_> = plan.members().cloned().collect();
    for expected in [
        "chosen", "logical", "runtime", "Nat", "Nat.zero", "Nat.succ",
    ] {
        assert!(members.contains(&name(expected)), "missing {expected}");
    }
    assert!(!members.contains(&name("other")));
    assert_eq!(plan.roots().cloned().collect::<Vec<_>>(), roots.to_vec());
    assert_eq!(plan.attributes.len(), members.len());
    let closure = plan.finish(&env).unwrap();
    assert_eq!(closure, RuntimeBindingClosure::check(&env, &roots).unwrap());
    closure
        .constant(&env, env.get_const(&name("chosen")).unwrap())
        .unwrap();
}

#[test]
fn compiler_binding_plan_population_bound_refuses_the_first_excess_member() {
    let env = environment();
    let roots = [name("chosen")];
    let complete = RuntimeBindingPlan::discover(&env, &roots, 100).unwrap();
    let population = complete.members().len();
    assert!(population > roots.len());
    RuntimeBindingPlan::discover(&env, &roots, population).unwrap();
    for bound in [0, population - 1] {
        let error = RuntimeBindingPlan::discover(&env, &roots, bound).unwrap_err();
        assert!(error.to_string().contains("population bound"), "{error}");
    }
    assert!(RuntimeBindingPlan::discover(&env, &[], 100)
        .unwrap_err()
        .to_string()
        .contains("requires a root"));
}

#[test]
fn compiler_binding_plan_finish_rechecks_reachability_attributes_and_order() {
    let original = environment();
    let plan = RuntimeBindingPlan::discover(&original, &[name("chosen")], 100).unwrap();
    let mut changed = original.clone();
    changed.register_extern(name("runtime"), "different_external".to_owned());
    assert!(plan.finish(&changed).is_err());
    let mut changed = original.clone();
    changed.register_implemented_by(name("logical"), name("other"));
    assert!(plan.finish(&changed).is_err());
    let mut changed = original;
    changed.record_compiled_before(vec![(
        name("runtime"),
        CompiledBefore {
            rebound: name("runtime"),
            via: name("runtime"),
        },
    )]);
    assert!(matches!(
        plan.finish(&changed),
        Err(CompilerError::RuntimeBindingOrder { .. })
    ));
}

#[test]
fn compiler_binding_plan_typed_names_cannot_expand_the_finished_closure() {
    let mut env = environment();
    let segmented = name("Shadow.chosen");
    let quoted = Name::anon().str("Shadow.chosen");
    assert_ne!(segmented, quoted);
    definition(&mut env, segmented.clone(), identity());
    definition(&mut env, quoted.clone(), identity());
    let plan = RuntimeBindingPlan::discover(&env, std::slice::from_ref(&segmented), 100).unwrap();
    assert!(plan.members().any(|member| member == &segmented));
    assert!(!plan.members().any(|member| member == &quoted));
    let closure = plan.finish(&env).unwrap();
    assert!(closure
        .constant(&env, env.get_const(&quoted).unwrap())
        .is_err());
}
