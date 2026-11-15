// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::env::{ConstantInfo, ConstantSource};
use crate::{BinderInfo, Environment, Name};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn environment() -> Environment {
    let mut env = Environment::default();
    for (name, ty) in [
        ("D", Expr::type_()),
        ("d", c("D")),
        ("f", Expr::arrow(c("D"), c("D"))),
    ] {
        env.add_constant_for_test(ConstantInfo::new(
            Name::from_string(name),
            vec![],
            ty,
            None,
            false,
        ));
    }
    env
}
fn data(n: usize) -> Arc<Expr> {
    let f = Arc::new(c("f"));
    (0..n).fold(Arc::new(c("d")), |arg, _| {
        Arc::new(Expr::app_arc(f.clone(), arg))
    })
}
fn frame(tc: &TypeChecker<'_>) {
    tc.infer_only.set(false);
    tc.infer_memo_depth.set(1);
}

#[test]
fn independent_data_survives_sibling_scopes_and_pins_actual_input() {
    let env = environment();
    let tc = TypeChecker::new(&env);
    frame(&tc);
    tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let input = data(96);
    let weak = Arc::downgrade(&input);
    let _ = crate::work_meter::stats::take();
    assert_eq!(tc.infer_type_fast_arc(&input).unwrap(), c("D"));
    let cold = crate::work_meter::stats::take().probes;
    let key = InferArcMemoKey::independent(&input, false);
    assert!(tc.infer_arc_memo.borrow().contains_key(&key));
    for _ in 0..12 {
        tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
        let _ = crate::work_meter::stats::take();
        assert_eq!(tc.infer_type_fast_arc(&input).unwrap(), c("D"));
        assert!(crate::work_meter::stats::take().probes < cold / 8);
        tc.ctx_pop();
    }
    drop(input);
    assert!(weak.upgrade().is_some());
    tc.infer_arc_memo.borrow_mut().clear();
    assert!(weak.upgrade().is_none());
}

#[test]
fn infer_only_app_cannot_supply_strict_argument_check() {
    let env = environment();
    let tc = TypeChecker::new(&env);
    frame(&tc);
    tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    tc.infer_only.set(true);
    let argument = Arc::new(Expr::prop());
    assert_eq!(tc.infer_type_fast_arc(&argument).unwrap(), Expr::type_());
    let bad = Arc::new(Expr::app_arc(Arc::new(c("f")), argument));
    assert_eq!(tc.infer_type_fast_arc(&bad).unwrap(), c("D"));
    assert!(tc
        .infer_arc_memo
        .borrow()
        .contains_key(&InferArcMemoKey::independent(&bad, true)));
    tc.infer_only.set(false);
    assert!(tc.infer_type_fast_arc(&bad).is_err());
    assert!(!tc
        .infer_arc_memo
        .borrow()
        .contains_key(&InferArcMemoKey::independent(&bad, false)));
}

#[test]
fn ambient_variable_hidden_in_environment_value_prevents_promotion() {
    let mut env = environment();
    env.add_constant_for_test(ConstantInfo::new(
        Name::from_string("Alias"),
        vec![],
        Expr::type_(),
        Some(Expr::fvar(crate::FVarId::new(0))),
        true,
    ));
    env.add_constant_for_test(ConstantInfo::new(
        Name::from_string("g"),
        vec![],
        c("Alias"),
        None,
        false,
    ));
    let tc = TypeChecker::new(&env);
    frame(&tc);
    let id = tc.ctx_push_let(Name::anon(), Expr::type_(), Expr::arrow(c("D"), c("D")));
    assert_eq!(id, crate::FVarId::new(0));
    let input = Arc::new(Expr::app(c("g"), c("d")));
    assert_eq!(tc.infer_type_fast_arc(&input).unwrap(), c("D"));
    assert!(!tc.independent_environment());
    assert!(!tc
        .infer_arc_memo
        .borrow()
        .contains_key(&InferArcMemoKey::independent(&input, false)));
    tc.ctx_pop();
    assert!(tc.infer_arc_memo.borrow().is_empty());
}

#[derive(Debug)]
struct HiddenSource;
impl ConstantSource for HiddenSource {
    fn get(&self, _: &Name) -> Option<&ConstantInfo> {
        None
    }
    fn contains(&self, _: &Name) -> bool {
        false
    }
}
#[test]
fn unenumerated_lazy_provider_and_unknown_native_callback_keep_scoped_route() {
    for lazy in [false, true] {
        let mut env = environment();
        if lazy {
            env.set_constant_source(Arc::new(HiddenSource));
        } else {
            env.register_native_reducer(Name::from_string("unknown"), |_| {
                Some(Expr::fvar(crate::FVarId::new(0)))
            });
        }
        let tc = TypeChecker::new(&env);
        frame(&tc);
        tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
        let input = data(3);
        assert_eq!(tc.infer_type_fast_arc(&input).unwrap(), c("D"));
        assert!(!tc.independent_environment());
        assert!(!tc
            .infer_arc_memo
            .borrow()
            .contains_key(&InferArcMemoKey::independent(&input, false)));
        assert!(tc
            .infer_arc_memo
            .borrow()
            .contains_key(&tc.infer_arc_memo_key(&input)));
    }
}

#[test]
fn binders_extensions_and_free_or_loose_variables_have_no_independent_key() {
    let env = environment();
    let tc = TypeChecker::new(&env);
    tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    for expr in [
        Expr::fvar(crate::FVarId::new(0)),
        Expr::bvar(0),
        Expr::lam(BinderInfo::Default, c("D"), Expr::bvar(0)),
        Expr::from_kind(ExprKind::Squash(Arc::new(c("D")))),
    ] {
        assert!(tc.independent_infer_key(&Arc::new(expr)).is_none());
    }
}

#[test]
fn independent_entries_share_total_capacity_and_never_leave_checker_in_tc_caches() {
    let env = environment();
    for capacity in [0, 1, 2, 7] {
        let mut tc = TypeChecker::new(&env);
        tc.set_max_cache_entries(capacity);
        frame(&tc);
        tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
        assert_eq!(tc.infer_type_fast_arc(&data(24)).unwrap(), c("D"));
        assert!(tc.infer_arc_memo.borrow().len() <= capacity);
        let caches = tc.take_caches();
        let other = TypeChecker::with_context_and_caches(&env, crate::LocalContext::new(), caches);
        assert!(other.infer_arc_memo.borrow().is_empty());
        assert_eq!(other.independent_infer_environment.get(), None);
    }
}

#[test]
fn unsafe_policy_transition_clears_independent_entries() {
    let mut env = environment();
    env.mark_unsafe(Name::from_string("f"));
    let mut tc = TypeChecker::new(&env);
    frame(&tc);
    tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let input = data(3);
    assert_eq!(tc.infer_type_fast_arc(&input).unwrap(), c("D"));
    assert!(tc
        .infer_arc_memo
        .borrow()
        .contains_key(&InferArcMemoKey::independent(&input, false)));
    tc.set_allow_unsafe(false);
    assert!(tc.infer_arc_memo.borrow().is_empty());
    assert!(tc.infer_type_fast_arc(&input).is_err());
}

#[test]
fn builtin_callback_custody_is_not_recreated_by_name_or_function_address() {
    let mut env = environment();
    env.ensure_native_reducers();
    assert!(env.has_only_owned_native_reducers());
    let name = Name::from_string("Nat.add");
    let function = *env.get_native_reducer(&name).unwrap();
    assert_eq!(
        function(&[&Expr::nat_lit(2), &Expr::nat_lit(3)]).unwrap(),
        Expr::nat_lit(5)
    );
    assert!(env.clone().has_only_owned_native_reducers());
    let tc = TypeChecker::new(&env);
    frame(&tc);
    tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let input = data(3);
    assert_eq!(tc.infer_type_fast_arc(&input).unwrap(), c("D"));
    assert!(tc
        .infer_arc_memo
        .borrow()
        .contains_key(&InferArcMemoKey::independent(&input, false)));
    drop(tc);
    // Even the identical callable, reintroduced by the ordinary public API,
    // has no private installation custody. This deliberately refuses to infer
    // ownership from a matching symbol, digest or code address.
    env.register_native_reducer(name, function);
    assert!(!env.has_only_owned_native_reducers());
    env.ensure_native_reducers();
    assert!(env.has_only_owned_native_reducers());
    env.register_native_reducer(Name::from_string("foreign"), function);
    env.ensure_native_reducers();
    assert!(!env.has_only_owned_native_reducers());
    let restored = Environment::from_dag_bincode(&env.to_dag_bincode().unwrap()).unwrap();
    assert_eq!(restored.registered_native_reducer_names().count(), 0);
}

#[test]
fn partial_universe_and_cumulative_policy_tightening_rechecks_actual_terms() {
    let mut env = environment();
    env.mark_partial(Name::from_string("f"));
    let mut tc = TypeChecker::new(&env);
    frame(&tc);
    tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let input = data(2);
    assert_eq!(tc.infer_type_fast_arc(&input).unwrap(), c("D"));
    tc.set_allow_partial(false);
    assert!(tc.infer_arc_memo.borrow().is_empty());
    assert!(tc.infer_type_fast_arc(&input).is_err());

    let env = environment();
    let mut tc = TypeChecker::new(&env);
    frame(&tc);
    tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let sort = Arc::new(Expr::sort(crate::Level::param(Name::from_string("u"))));
    assert!(tc.infer_type_fast_arc(&sort).is_ok());
    tc.set_level_params(vec![]);
    assert!(tc.infer_arc_memo.borrow().is_empty());
    assert!(tc.infer_type_fast_arc(&sort).is_err());

    let mut env = environment();
    env.add_constant_for_test(ConstantInfo::new(
        Name::from_string("P"),
        vec![],
        Expr::prop(),
        None,
        false,
    ));
    env.add_constant_for_test(ConstantInfo::new(
        Name::from_string("lift"),
        vec![],
        Expr::arrow(Expr::type_(), c("D")),
        None,
        false,
    ));
    let mut tc = TypeChecker::new(&env);
    tc.set_cumulative(true);
    frame(&tc);
    tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let term = Arc::new(Expr::app(c("lift"), c("P")));
    assert_eq!(tc.infer_type_fast_arc(&term).unwrap(), c("D"));
    tc.set_cumulative(false);
    assert!(tc.infer_arc_memo.borrow().is_empty());
    assert!(tc.infer_type_fast_arc(&term).is_err());
}

#[test]
fn mode_transparency_reducibility_and_level_callback_clear_retained_answers() {
    let env = environment();
    let mut tc = TypeChecker::new(&env);
    frame(&tc);
    tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let input = data(2);
    assert_eq!(tc.infer_type_fast_arc(&input).unwrap(), c("D"));
    tc.set_mode(crate::CleanMode::Classical);
    assert!(tc.infer_arc_memo.borrow().is_empty());
    assert_eq!(tc.infer_type_fast_arc(&input).unwrap(), c("D"));
    tc.set_transparency(crate::TransparencyMode::Reducible);
    assert!(tc.infer_arc_memo.borrow().is_empty());
    assert_eq!(tc.infer_type_fast_arc(&input).unwrap(), c("D"));
    tc.set_honor_reducibility(true);
    assert!(tc.infer_arc_memo.borrow().is_empty());
    assert_eq!(tc.infer_type_fast_arc(&input).unwrap(), c("D"));
    tc.set_level_eq_override(|a, b| a == b);
    assert!(tc.infer_arc_memo.borrow().is_empty());
    assert!(tc.independent_infer_key(&input).is_none());
}

#[test]
fn fact_delta_reassembly_keeps_actual_callback_and_its_custody_together() {
    let mut before = environment();
    before.ensure_native_reducers();
    let mut after = before.clone();
    after.set_lean4_core_strict_monads(true);
    let delta = after.local_fact_delta_since(&before).unwrap();
    let delta = crate::env::EnvFactDelta::decode(&delta.encode().unwrap()).unwrap();
    for foreign in [false, true] {
        let mut target = before.clone();
        if foreign {
            target.register_native_reducer(Name::from_string("Nat.add"), |_| {
                Some(Expr::nat_lit(999))
            });
        }
        target.apply_local_fact_delta(&delta).unwrap();
        assert_eq!(target.has_only_owned_native_reducers(), !foreign);
        let function = target
            .get_native_reducer(&Name::from_string("Nat.add"))
            .unwrap();
        assert_eq!(
            function(&[&Expr::nat_lit(2), &Expr::nat_lit(3)]).unwrap(),
            Expr::nat_lit(if foreign { 999 } else { 5 })
        );
    }
}

#[test]
fn same_symbol_and_input_pointer_in_different_environment_do_not_share_answers() {
    let input = Arc::new(Expr::app(c("f"), c("d")));
    for function_type in [true, false] {
        let mut env = environment();
        env.add_constant_for_test(ConstantInfo::new(
            Name::from_string("Alias"),
            vec![],
            Expr::type_(),
            Some(if function_type {
                Expr::arrow(c("D"), c("D"))
            } else {
                c("D")
            }),
            true,
        ));
        env.add_constant_for_test(ConstantInfo::new(
            Name::from_string("f"),
            vec![],
            c("Alias"),
            None,
            false,
        ));
        let tc = TypeChecker::new(&env);
        frame(&tc);
        tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
        let result = tc.infer_type_fast_arc(&input);
        assert_eq!(result.is_ok(), function_type);
        if function_type {
            assert_eq!(result.unwrap(), c("D"));
        }
    }
}
