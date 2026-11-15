// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The concurrent checks of `upgrade_axiom_stubs_checked` decide every batch
//! exactly as the record-at-a-time loop does: a value that checks only once an
//! earlier sibling's value is installed still upgrades, one whose sibling comes
//! later is still refused, a tampered value is refused, and the ambient budget
//! is charged or, when it would run out, left to the sequential loop.

use super::stub_upgrade_parallel::MIN_PARALLEL_BATCH;
use super::types::{ConstantInfo, Declaration, EnvError};
use super::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// `∀ x : Prop, x` — a term whose type is `Prop`.
fn a_prop() -> Expr {
    Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0))
}

fn stub(env: &mut Environment, name: &str, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .expect("stub axiom must register through add_decl");
}

fn record(name: &str, type_: Expr, value: Expr) -> ConstantInfo {
    ConstantInfo::new(Name::from_string(name), vec![], type_, Some(value), false)
}

/// `A : Type := Prop`, `b : A := ∀ x : Prop, x` (checks only once `A`
/// unfolds), a tampered `t : Type := λ x : Type, x`, and padding stubs so the
/// batch is large enough to fan out. Returns the environment and the records,
/// with `b` placed before or after `A`.
fn batch(b_after_a: bool) -> (Environment, Vec<ConstantInfo>) {
    let mut env = Environment::new();
    stub(&mut env, "Spec.A", Expr::type_());
    stub(&mut env, "Spec.b", Expr::const_str("Spec.A"));
    stub(&mut env, "Spec.t", Expr::type_());
    let a = record("Spec.A", Expr::type_(), Expr::prop());
    let b = record("Spec.b", Expr::const_str("Spec.A"), a_prop());
    let t = record(
        "Spec.t",
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
    );
    let mut records = if b_after_a {
        vec![a, b, t]
    } else {
        vec![b, a, t]
    };
    for i in 0..MIN_PARALLEL_BATCH {
        let name = format!("Spec.pad{i}");
        stub(&mut env, &name, Expr::type_());
        records.push(record(&name, Expr::type_(), Expr::prop()));
    }
    (env, records)
}

/// The record-at-a-time loop: one-record batches never fan out.
fn one_by_one(env: &mut Environment, records: &[ConstantInfo]) -> (usize, Vec<Name>) {
    let mut upgraded = 0;
    let mut refused = Vec::new();
    for ci in records {
        let (n, r) = env.upgrade_axiom_stubs_checked(std::iter::once(ci.clone()));
        upgraded += n;
        refused.extend(r.into_iter().map(|(name, _)| name));
    }
    (upgraded, refused)
}

fn has_value(env: &Environment, name: &str) -> bool {
    env.get_const(&Name::from_string(name))
        .is_some_and(|ci| ci.value.is_some())
}

#[test]
fn test_parallel_stub_upgrade_sibling_before_upgrades_like_the_sequential_loop() {
    let (mut env, records) = batch(true);
    let (mut control, _) = batch(true);
    let (upgraded, refused) = env.upgrade_axiom_stubs_checked(records.clone().into_iter());
    let (control_upgraded, control_refused) = one_by_one(&mut control, &records);

    assert_eq!(upgraded, control_upgraded);
    assert_eq!(
        upgraded,
        2 + MIN_PARALLEL_BATCH,
        "A, b and the padding upgrade"
    );
    assert!(
        has_value(&env, "Spec.b"),
        "b checks once A is installed, as in order"
    );
    let names: Vec<Name> = refused.iter().map(|(n, _)| n.clone()).collect();
    assert_eq!(names, control_refused);
    assert_eq!(names, vec![Name::from_string("Spec.t")]);
    assert!(
        matches!(refused[0].1, EnvError::TypeCheckFailed { .. }),
        "the tampered value is refused by the kernel check: {:?}",
        refused[0].1
    );
    assert!(!has_value(&env, "Spec.t"), "fail-closed: t stays a stub");
}

#[test]
fn test_parallel_stub_upgrade_sibling_after_is_refused_like_the_sequential_loop() {
    let (mut env, records) = batch(false);
    let (mut control, _) = batch(false);
    let (upgraded, refused) = env.upgrade_axiom_stubs_checked(records.clone().into_iter());
    let (control_upgraded, control_refused) = one_by_one(&mut control, &records);

    assert_eq!(upgraded, control_upgraded);
    let names: Vec<Name> = refused.into_iter().map(|(n, _)| n).collect();
    assert_eq!(names, control_refused, "same refusals, same order");
    assert!(
        names.contains(&Name::from_string("Spec.b")),
        "b's turn comes while A is still a stub, so b is refused: {names:?}"
    );
    assert!(!has_value(&env, "Spec.b"));
    assert!(has_value(&env, "Spec.A"));
}

#[test]
fn test_parallel_stub_upgrade_duplicate_record_is_a_silent_no_op() {
    let (mut env, mut records) = batch(true);
    let first = records[0].clone();
    records.push(first);
    let (upgraded, refused) = env.upgrade_axiom_stubs_checked(records.into_iter());
    assert_eq!(
        upgraded,
        2 + MIN_PARALLEL_BATCH,
        "the repeat installs nothing"
    );
    assert_eq!(refused.len(), 1, "only the tampered record: {refused:?}");
}

#[test]
fn test_parallel_stub_upgrade_charges_the_ambient_budget() {
    std::thread::spawn(|| {
        let (mut env, records) = batch(true);
        crate::tc::set_declaration_budget(1_000_000_000);
        let (upgraded, _) = env.upgrade_axiom_stubs_checked(records.into_iter());
        assert_eq!(upgraded, 2 + MIN_PARALLEL_BATCH);
        assert!(
            crate::tc::declaration_budget_used() > 0,
            "the workers' ticks are charged to the calling thread"
        );
        crate::tc::clear_declaration_budget();
    })
    .join()
    .expect("budget test thread must not panic");
}

#[test]
fn test_parallel_stub_upgrade_tight_budget_decides_sequentially() {
    // With almost no budget the concurrent checks would together overspend
    // it, so the batch is decided by the sequential loop from the untouched
    // budget: the same outcome as one record at a time under that budget.
    for limit in [1u64, 3, 10] {
        let outcome = std::thread::spawn(move || {
            // Both environments are built before the budget is armed: building
            // one type-checks its stubs.
            let (mut env, records) = batch(true);
            let (mut control, _) = batch(true);
            crate::tc::set_declaration_budget(limit);
            let (upgraded, refused) = env.upgrade_axiom_stubs_checked(records.clone().into_iter());
            let batch_names: Vec<Name> = refused.into_iter().map(|(n, _)| n).collect();
            crate::tc::set_declaration_budget(limit);
            let control_outcome = one_by_one(&mut control, &records);
            crate::tc::clear_declaration_budget();
            ((upgraded, batch_names), control_outcome)
        })
        .join()
        .expect("budget test thread must not panic");
        assert_eq!(outcome.0, outcome.1, "limit {limit}");
    }
}
