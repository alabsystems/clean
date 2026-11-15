// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use clean_kernel::env::{Declaration, KernelTheory, Reducibility, TrustedEnvExt};
use clean_kernel::{BinderInfo, Environment, Expr, KernelTypeError, Level, Name, TypeChecker};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}
fn env(reducible: bool) -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_bool().unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("polyId"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        ),
        value: lam(Expr::type_(), lam(Expr::bvar(0), Expr::bvar(0))),
        is_reducible: reducible,
    })
    .unwrap();
    if !reducible {
        assert!(env.set_reducibility(&Name::from_string("polyId"), Reducibility::Irreducible));
    }
    env
}
fn apply(ty: Expr, value: Expr) -> Expr {
    Expr::apps(c("polyId"), [ty, value])
}

#[test]
fn repeated_type_specialization_reuses_its_checked_normalization() {
    let env = env(true);
    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.whnf(&apply(c("Nat"), Expr::nat_lit(13))),
        Expr::nat_lit(13)
    );
    #[cfg(feature = "inference-stats")]
    let _ = clean_kernel::work_meter::stats::take();
    assert_eq!(
        tc.whnf(&apply(c("Nat"), Expr::nat_lit(29))),
        Expr::nat_lit(29)
    );
    #[cfg(feature = "inference-stats")]
    assert_eq!(clean_kernel::work_meter::stats::take().step_ticks, 1);
}

#[test]
fn different_type_and_value_arguments_keep_their_identity() {
    let env = env(true);
    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.whnf(&apply(c("Nat"), Expr::nat_lit(13))),
        Expr::nat_lit(13)
    );
    assert_eq!(tc.whnf(&apply(c("Bool"), c("Bool.true"))), c("Bool.true"));
    let wrong = apply(c("Nat"), c("Bool.true"));
    assert!(matches!(
        tc.check_type(&wrong, &c("Nat")),
        Err(KernelTypeError::TypeMismatch { .. })
    ));
}

#[test]
fn partial_application_and_extra_arguments_are_preserved() {
    let env = env(true);
    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.whnf(&Expr::app(c("polyId"), c("Nat"))),
        lam(c("Nat"), Expr::bvar(0))
    );
    let extra = Expr::app(apply(c("Nat"), Expr::nat_lit(13)), Expr::nat_lit(29));
    assert_eq!(
        tc.whnf(&extra),
        Expr::app(Expr::nat_lit(13), Expr::nat_lit(29))
    );
    assert!(matches!(
        tc.check_type(&extra, &c("Nat")),
        Err(KernelTypeError::NotAFunction { .. })
    ));
}

#[test]
fn exhausted_specialization_is_not_retained_as_a_complete_answer() {
    let env = env(true);
    let mut tc = TypeChecker::new(&env);
    let term = apply(c("Nat"), Expr::nat_lit(13));
    tc.set_heartbeat_limit(2);
    assert_ne!(tc.whnf(&term), Expr::nat_lit(13));
    assert!(tc.heartbeat_spent());
    tc.set_heartbeat_limit(10_000);
    assert_eq!(tc.whnf(&term), Expr::nat_lit(13));
}

#[test]
fn irreducibility_and_native_dispatch_still_control_the_original_call() {
    let irreducible = env(false);
    let tc = TypeChecker::new(&irreducible);
    tc.set_honor_reducibility(true);
    let term = apply(c("Nat"), Expr::nat_lit(13));
    assert_eq!(tc.whnf(&term), term);
    let mut native = env(true);
    native.register_native_reducer(Name::from_string("polyId"), |_| Some(Expr::nat_lit(99)));
    let tc = TypeChecker::new(&native);
    assert_eq!(
        tc.whnf(&apply(c("Nat"), Expr::nat_lit(13))),
        Expr::nat_lit(13)
    );
}

#[test]
fn specialized_body_keeps_the_existing_native_grind_guard() {
    let mut env = env(true);
    let motive = lam(c("Nat"), c("Nat"));
    let successor = lam(c("Nat"), lam(c("Nat"), Expr::bvar(0)));
    let body = Expr::apps(
        Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [motive, Expr::bvar(0), successor, Expr::nat_lit(1024)],
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("polyGrind"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::arrow(c("Nat"), c("Nat")),
        ),
        value: lam(Expr::type_(), lam(c("Nat"), body)),
        is_reducible: true,
    })
    .unwrap();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(200);
    let local = tc.push_binder_local(Name::from_string("symbolic"), c("Nat"), BinderInfo::Default);
    let term = Expr::apps(c("polyGrind"), [c("Nat"), Expr::fvar(local)]);
    tc.check_type(&term, &c("Nat")).unwrap();
    assert!(tc.whnf(&term).get_app_fn().is_lam());
    assert!(!tc.heartbeat_spent());
    tc.pop_binder_local();
}

#[test]
fn captured_type_arguments_do_not_escape_or_alias_new_binders() {
    let env = env(true);
    let tc = TypeChecker::new(&env);
    let old_type = tc.push_binder_local(Name::from_string("A"), Expr::type_(), BinderInfo::Default);
    let old_value = tc.push_binder_local(
        Name::from_string("a"),
        Expr::fvar(old_type),
        BinderInfo::Default,
    );
    let old_term = apply(Expr::fvar(old_type), Expr::fvar(old_value));
    tc.check_type(&old_term, &Expr::fvar(old_type)).unwrap();
    assert_eq!(tc.whnf(&old_term), Expr::fvar(old_value));
    tc.pop_binder_local();
    tc.pop_binder_local();
    let new_type = tc.push_binder_local(Name::from_string("B"), Expr::type_(), BinderInfo::Default);
    let new_value = tc.push_binder_local(
        Name::from_string("b"),
        Expr::fvar(new_type),
        BinderInfo::Default,
    );
    assert_ne!(old_type, new_type);
    assert_ne!(old_value, new_value);
    let new_term = apply(Expr::fvar(new_type), Expr::fvar(new_value));
    tc.check_type(&new_term, &Expr::fvar(new_type)).unwrap();
    assert_eq!(tc.whnf(&new_term), Expr::fvar(new_value));
    tc.pop_binder_local();
    tc.pop_binder_local();
}

#[test]
fn longer_application_spines_keep_the_original_result_and_refusal() {
    let env = env(true);
    let tc = TypeChecker::new(&env);
    let mut term = apply(c("Nat"), Expr::nat_lit(13));
    let mut expected = Expr::nat_lit(13);
    for _ in 0..12 {
        term = Expr::app(term, Expr::nat_lit(0));
        expected = Expr::app(expected, Expr::nat_lit(0));
    }
    assert_eq!(tc.whnf(&term), expected);
    assert!(matches!(
        tc.check_type(&term, &c("Nat")),
        Err(KernelTypeError::NotAFunction { .. })
    ));
}

#[test]
fn opaque_polymorphic_values_remain_opaque() {
    let mut env = env(true);
    let template = env.get_const(&Name::from_string("polyId")).unwrap().clone();
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("opaquePoly"),
        level_params: vec![],
        type_: template.type_,
        value: template.value.unwrap(),
    })
    .unwrap();
    let tc = TypeChecker::new(&env);
    let term = Expr::apps(c("opaquePoly"), [c("Nat"), Expr::nat_lit(13)]);
    assert_eq!(tc.whnf(&term), term);
    tc.check_type(&term, &c("Nat")).unwrap();
}

#[test]
fn sharing_dependent_prefix_records_a_terminal_refusal() {
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let level = Level::IMax(
        Level::param(v.clone()).into(),
        Level::succ(Level::param(u.clone())).into(),
    );
    let domain = Expr::sort(level);
    let mut env = Environment::for_lean_replay();
    // The same raw level-shape refusal as level_profile_tests: this is a
    // presented declaration, not a claim that unchecked import grants authority.
    env.add_decl_unchecked(Declaration::Definition {
        name: Name::from_string("sharingPoly"),
        level_params: vec![u.clone(), v.clone()],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::arrow(domain.clone(), domain.clone()),
        ),
        value: lam(Expr::type_(), lam(domain, Expr::bvar(0))),
        is_reducible: true,
    });
    let mut tc = TypeChecker::new(&env);
    tc.set_kernel_theory(KernelTheory::LeanReference);
    let term = Expr::apps(
        Expr::const_(
            Name::from_string("sharingPoly"),
            vec![Level::param(u), Level::param(v)],
        ),
        [Expr::type_(), Expr::type_()],
    );
    let _ = tc.whnf(&term);
    assert!(tc.level_sharing_error().is_some());
    assert!(matches!(
        tc.infer_type(&Expr::prop()),
        Err(KernelTypeError::LevelSharingDependent { .. })
    ));
    assert_eq!(tc.whnf_cache_entries(), 0);
}

#[test]
fn cubical_mode_keeps_the_original_type_application_path() {
    let env = env(true);
    let mut tc = TypeChecker::new(&env);
    tc.set_mode(clean_kernel::CleanMode::Cubical);
    let term = apply(c("Nat"), Expr::nat_lit(13));
    #[cfg(feature = "inference-stats")]
    let _ = clean_kernel::work_meter::stats::take();
    assert_eq!(tc.whnf(&term), Expr::nat_lit(13));
    #[cfg(feature = "inference-stats")]
    {
        let work = clean_kernel::work_meter::stats::take();
        // This mode keeps its original route. The retained baseline/candidate
        // comparison also observes exactly 95 steps on this input in both.
        assert!(work.step_ticks >= 2);
    }
}
