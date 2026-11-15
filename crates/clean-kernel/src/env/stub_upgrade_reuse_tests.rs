// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{ConstantInfo, ConstantSource, Declaration, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

fn stub(env: &mut Environment, text: &str, ty: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(text),
        level_params: vec![],
        type_: ty,
    })
    .unwrap();
}

fn record(text: &str, ty: Expr, value: Expr) -> ConstantInfo {
    ConstantInfo::new(Name::from_string(text), vec![], ty, Some(value), false)
}

fn snapshot(env: &Environment) -> BTreeMap<Name, (ConstantInfo, String, String)> {
    env.constants()
        .map(|info| {
            (
                info.name.clone(),
                (
                    info.clone(),
                    format!("{:?}", env.declaration_verification(&info.name)),
                    format!("{:?}", env.get_constant_origin(&info.name)),
                ),
            )
        })
        .collect()
}

fn fixpoint(
    env: &mut Environment,
    mut pending: Vec<ConstantInfo>,
    reuse: bool,
) -> (usize, Vec<(Name, String)>, usize, usize) {
    let mut total = 0;
    let mut checks = 0;
    let mut cached = 0;
    loop {
        let (upgraded, refused, work) =
            env.upgrade_axiom_stubs_checked_with_work(pending.clone().into_iter(), reuse);
        total += upgraded;
        checks += work.speculative_checks + work.sequential_checks;
        cached += work.reused_refusals;
        if upgraded == 0 || refused.is_empty() {
            return (
                total,
                refused
                    .into_iter()
                    .map(|(n, e)| (n, format!("{e:?}")))
                    .collect(),
                checks,
                cached,
            );
        }
        pending.retain(|info| refused.iter().any(|(name, _)| name == &info.name));
    }
}

fn compare(env: Environment, records: Vec<ConstantInfo>) -> (usize, usize, usize) {
    let mut old = env.clone();
    let mut new = env;
    let before = Instant::now();
    let baseline = fixpoint(&mut old, records.clone(), false);
    let old_time = before.elapsed();
    let before = Instant::now();
    let actual = fixpoint(&mut new, records, true);
    let new_time = before.elapsed();
    assert_eq!(actual.0, baseline.0, "same accepted count");
    assert_eq!(actual.1, baseline.1, "same ordered refusal diagnostics");
    assert_eq!(
        snapshot(&new),
        snapshot(&old),
        "same payloads and authority stamps"
    );
    assert_eq!(
        new.to_bincode().unwrap(),
        old.to_bincode().unwrap(),
        "same complete persisted environment"
    );
    assert_eq!(new.generation(), old.generation());
    assert!(actual.2 <= baseline.2);
    eprintln!(
        "checked stub work: baseline={} {:?}; reuse={} {:?}; cached={}",
        baseline.2, old_time, actual.2, new_time, actual.3
    );
    (baseline.2, actual.2, actual.0)
}

#[test]
fn unchanged_refused_batch_checks_each_value_once() {
    let mut env = Environment::new();
    let mut records = Vec::new();
    let identity = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    for i in 0..32 {
        let name = format!("Reuse.bad{i}");
        stub(&mut env, &name, Expr::prop());
        let mut wrong = Expr::prop();
        for _ in 0..32 {
            wrong = Expr::app(identity.clone(), wrong);
        }
        records.push(record(&name, Expr::prop(), wrong));
    }
    let (old, new, accepted) = compare(env, records);
    assert_eq!(accepted, 0);
    // A one-worker admission uses the original serial path; a parallel
    // batch must eliminate the repeated refusal checks.
    assert!(matches!((old, new), (32, 32) | (64, 32)));
}

#[test]
fn accepted_batches_keep_the_original_single_check_per_value() {
    let mut env = Environment::new();
    let mut records = Vec::new();
    for i in 0..32 {
        let name = format!("Reuse.accept{i}");
        stub(&mut env, &name, Expr::type_());
        records.push(record(&name, Expr::type_(), Expr::prop()));
    }
    let (old, new, accepted) = compare(env, records);
    assert_eq!(accepted, 32);
    assert_eq!(old, 32);
    assert_eq!(new, 32);
}

#[test]
fn any_installation_invalidates_later_refusals() {
    let mut env = Environment::new();
    stub(&mut env, "Reuse.A", Expr::type_());
    let mut records = vec![record("Reuse.A", Expr::type_(), Expr::prop())];
    for i in 0..7 {
        let name = format!("Reuse.after{i}");
        stub(&mut env, &name, Expr::prop());
        records.push(record(&name, Expr::prop(), Expr::type_()));
    }
    assert_eq!(compare(env, records).2, 1);
}

#[test]
fn transitive_stub_dependency_is_rechecked_after_an_installation() {
    let mut env = Environment::new();
    stub(&mut env, "Reuse.A", Expr::type_());
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Reuse.B"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::const_str("Reuse.A"),
        is_reducible: true,
    })
    .unwrap();
    stub(&mut env, "Reuse.b", Expr::const_str("Reuse.B"));
    let proposition = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let mut records = vec![
        record("Reuse.b", Expr::const_str("Reuse.B"), proposition),
        record("Reuse.A", Expr::type_(), Expr::prop()),
    ];
    for i in 0..5 {
        let name = format!("Reuse.tail{i}");
        stub(&mut env, &name, Expr::prop());
        records.push(record(&name, Expr::prop(), Expr::type_()));
    }
    assert_eq!(compare(env, records).2, 2);
}

#[test]
fn duplicate_missing_and_cyclic_records_keep_the_original_results() {
    let mut env = Environment::new();
    for name in ["Reuse.A", "Reuse.B", "Reuse.bad"] {
        stub(&mut env, name, Expr::type_());
    }
    let a = record("Reuse.A", Expr::type_(), Expr::const_str("Reuse.B"));
    let records = vec![
        a.clone(),
        record("Reuse.B", Expr::type_(), Expr::const_str("Reuse.A")),
        a,
        record("Reuse.missing", Expr::type_(), Expr::prop()),
        record(
            "Reuse.bad",
            Expr::type_(),
            Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        ),
    ];
    assert_eq!(compare(env, records).2, 2);
}

#[test]
fn malformed_records_keep_exact_structural_refusals() {
    let mut env = Environment::new();
    let mut records = Vec::new();
    for i in 0..8 {
        let name = format!("Reuse.malformed{i}");
        stub(&mut env, &name, Expr::prop());
        let value = if i % 2 == 0 {
            Expr::bvar(0)
        } else {
            Expr::sort(crate::level::Level::param(Name::from_string("undeclared")))
        };
        records.push(record(&name, Expr::prop(), value));
    }
    assert_eq!(compare(env, records).2, 0);
}

#[test]
fn boolean_type_anchor_refusals_keep_the_original_recheck() {
    let mut env = Environment::new();
    let mut records = Vec::new();
    for i in 0..8 {
        let name = format!("Reuse.anchor{i}");
        stub(&mut env, &name, Expr::prop());
        records.push(record(&name, Expr::type_(), Expr::prop()));
    }
    let (old, new, accepted) = compare(env, records);
    assert_eq!(accepted, 0);
    assert_eq!(old, new);
}

#[test]
fn resource_errors_are_not_completed_refusals() {
    use super::stub_upgrade_parallel::completed_type_refusal;
    use crate::tc::{TypeChecker, TypeError};
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    for error in [
        TypeError::HeartbeatExceeded {
            limit: 1,
            profile: None,
        },
        TypeError::DeclarationBudgetExhausted { limit: 1 },
        TypeError::Interrupted,
        TypeError::ExcessiveMemory,
        TypeError::DeepRecursion,
        TypeError::SortDepthExceeded { depth: 1 },
    ] {
        assert!(!completed_type_refusal(&tc, &error), "{error:?}");
    }
    let semantic = TypeError::UnknownConst(Name::from_string("missing"));
    assert!(completed_type_refusal(&tc, &semantic));
    tc.set_heartbeat_limit(1);
    let _ = tc.infer_type(&Expr::app(Expr::type_(), Expr::prop()));
    assert!(tc.heartbeat_spent());
    assert!(!completed_type_refusal(&tc, &semantic));
}

#[test]
fn ambient_budget_and_deadline_preserve_original_checks() {
    std::thread::spawn(|| {
        let mut env = Environment::new();
        let mut records = Vec::new();
        for i in 0..8 {
            let name = format!("Reuse.bounded{i}");
            stub(&mut env, &name, Expr::prop());
            records.push(record(&name, Expr::prop(), Expr::type_()));
        }
        for limit in [1, 10, 1_000_000] {
            let mut old = env.clone();
            let mut new = env.clone();
            crate::tc::set_declaration_budget(limit);
            let baseline = fixpoint(&mut old, records.clone(), false);
            let used = crate::tc::declaration_budget_used();
            crate::tc::set_declaration_budget(limit);
            let actual = fixpoint(&mut new, records.clone(), true);
            assert_eq!(actual, baseline);
            assert_eq!(used, crate::tc::declaration_budget_used());
            assert_eq!(actual.3, 0);
            crate::tc::clear_declaration_budget();
        }
        let result = crate::tc::run_until(Some(Instant::now() + Duration::from_secs(60)), || {
            let mut old = env.clone();
            let mut new = env;
            let baseline = fixpoint(&mut old, records.clone(), false);
            let actual = fixpoint(&mut new, records, true);
            assert_eq!(actual, baseline);
            assert_eq!(actual.3, 0);
        });
        assert!(result.is_some());
    })
    .join()
    .unwrap();
}

#[test]
fn lazy_sources_keep_the_original_rechecks() {
    #[derive(Debug)]
    struct EmptySource;
    impl ConstantSource for EmptySource {
        fn get(&self, _: &Name) -> Option<&ConstantInfo> {
            None
        }
        fn contains(&self, _: &Name) -> bool {
            false
        }
    }
    let mut env = Environment::new();
    env.set_constant_source(std::sync::Arc::new(EmptySource));
    let mut records = Vec::new();
    for i in 0..8 {
        let name = format!("Reuse.lazy{i}");
        stub(&mut env, &name, Expr::prop());
        records.push(record(&name, Expr::prop(), Expr::type_()));
    }
    let mut old = env.clone();
    let baseline = fixpoint(&mut old, records.clone(), false);
    let actual = fixpoint(&mut env, records, true);
    assert_eq!(actual, baseline);
    assert_eq!(actual.3, 0);
}
