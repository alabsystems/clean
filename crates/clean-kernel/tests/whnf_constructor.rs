// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{BinderInfo, Expr, KernelTypeError as TypeError, Level, Name, TypeChecker};

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn list_head(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![Level::zero()])
}

fn nil() -> Expr {
    Expr::app(list_head("List.nil"), constant("Nat"))
}

fn cons(head: Expr, tail: Expr) -> Expr {
    Expr::apps(list_head("List.cons"), [constant("Nat"), head, tail])
}

#[test]
fn ordinary_constructor_whnf_avoids_reduction_and_cache_entries() {
    let mut env = Environment::new();
    env.init_list().unwrap();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(32);
    let field = Expr::app(constant("Nat.succ"), Expr::nat_lit(7));
    let value = cons(field, nil());
    #[cfg(feature = "inference-stats")]
    let _ = clean_kernel::work_meter::stats::take();
    for _ in 0..1_000 {
        assert_eq!(tc.whnf(&value), value);
    }
    // The bounded recognizer's actual walk is still billed; there is no
    // reduction heartbeat or growing cached identity term per visit.
    #[cfg(feature = "inference-stats")]
    {
        let work = clean_kernel::work_meter::stats::take();
        assert_eq!(work.step_ticks, 0);
        assert!(work.work_heartbeats <= 8);
    }
    assert_eq!(tc.whnf_cache_entries(), 0);
    let _ = tc.infer_type(&constant("Nat")).unwrap();
}

#[test]
fn constructor_recognition_preserves_nat_literal_normalization() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let tc = TypeChecker::new(&env);
    let successor = Expr::app(constant("Nat.succ"), Expr::nat_lit(7));
    assert_eq!(tc.whnf(&successor), Expr::nat_lit(8));
    for malformed in [
        Expr::app(successor, Expr::nat_lit(0)),
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![Level::zero()]),
            Expr::nat_lit(7),
        ),
    ] {
        assert_eq!(tc.whnf(&malformed), malformed);
    }
}

#[test]
fn a_constructor_spelling_does_not_hide_a_definition() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("List.cons"),
        level_params: vec![],
        type_: Expr::arrow(constant("Nat"), constant("Nat")),
        value: Expr::lam(BinderInfo::Default, constant("Nat"), Expr::nat_lit(19)),
        is_reducible: true,
    })
    .unwrap();
    let tc = TypeChecker::new(&env);
    let application = Expr::app(constant("List.cons"), Expr::nat_lit(7));
    assert_eq!(tc.whnf(&application), Expr::nat_lit(19));
}

#[test]
fn constructor_whnf_does_not_grant_well_typed_fields_or_extra_arguments() {
    let mut env = Environment::new();
    env.init_list().unwrap();
    env.init_bool().unwrap();
    let tc = TypeChecker::new(&env);
    let list_nat = Expr::app(list_head("List"), constant("Nat"));
    let good = cons(Expr::nat_lit(7), nil());
    tc.check_type(&good, &list_nat).unwrap();
    let bad_field = cons(constant("Bool.true"), nil());
    assert!(matches!(
        tc.check_type(&bad_field, &list_nat),
        Err(TypeError::TypeMismatch { .. })
    ));
    let overapplied = Expr::app(good, Expr::nat_lit(0));
    assert!(matches!(
        tc.check_type(&overapplied, &list_nat),
        Err(TypeError::NotAFunction { .. })
    ));
}

#[test]
fn registered_native_constructor_hook_keeps_the_existing_path() {
    let mut env = Environment::new();
    env.init_list().unwrap();
    // A constructor has no admitted definition body for this arbitrary hook.
    // Retain the existing dispatch and its refusal to grant that hook authority.
    env.register_native_reducer(Name::from_string("List.cons"), |_| Some(Expr::nat_lit(99)));
    let tc = TypeChecker::new(&env);
    let value = cons(Expr::nat_lit(7), nil());
    assert_eq!(tc.whnf(&value), value);
    assert!(tc.whnf_cache_entries() > 0);
}

#[test]
#[cfg(feature = "inference-stats")]
fn cached_deep_application_does_not_repeat_the_constructor_scan() {
    let mut env = Environment::new();
    env.init_list().unwrap();
    let tc = TypeChecker::new(&env);
    let mut deep = nil();
    for _ in 0..1_000 {
        deep = Expr::app(deep, Expr::nat_lit(0));
    }
    let _ = tc.whnf(&deep);
    let _ = clean_kernel::work_meter::stats::take();
    let _ = tc.whnf(&deep);
    assert_eq!(clean_kernel::work_meter::stats::take().fold_nodes, 0);
}

#[test]
fn an_eliminator_with_a_constructor_scrutinee_still_reduces() {
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env.init_nat().unwrap();
    let tc = TypeChecker::new(&env);
    let motive = Expr::lam(BinderInfo::Default, constant("Bool"), constant("Nat"));
    for (constructor, expected) in [("Bool.false", 7), ("Bool.true", 19)] {
        let choice = Expr::apps(
            Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                motive.clone(),
                Expr::nat_lit(7),
                Expr::nat_lit(19),
                constant(constructor),
            ],
        );
        tc.check_type(&choice, &constant("Nat")).unwrap();
        assert_eq!(tc.whnf(&choice), Expr::nat_lit(expected));
    }
}

#[test]
fn cubical_modes_keep_their_existing_constructor_reduction_path() {
    let mut env = Environment::new();
    env.init_list().unwrap();
    let mut tc = TypeChecker::new(&env);
    let value = cons(Expr::nat_lit(7), nil());
    tc.set_mode(clean_kernel::CleanMode::Cubical);
    assert_eq!(tc.whnf(&value), value);
    assert!(tc.whnf_cache_entries() > 0);
}
