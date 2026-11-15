// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! A reference-admitted base is bound to the exact records it checked.
use clean_kernel::env::{Environment, TrustedEnvExt};
use clean_kernel::{Expr, Level, Name};
use clean_olean::{load_module_with_deps, ImportedConeGate};
use std::collections::BTreeSet;

fn names(xs: &[&str]) -> BTreeSet<Name> {
    xs.iter().map(|s| Name::from_string(s)).collect()
}

#[test]
fn reference_foundations_accept_original_records_and_refuse_mutations() {
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean library");
    let mut source = Environment::for_lean_replay();
    load_module_with_deps(&mut source, "Init.Core", &[lib]).expect("load genuine foundations");
    let roots = names(&["propext", "Classical.choice", "Quot.sound", "Quot.ind"]);
    let mut gate = ImportedConeGate::from_reference_cone(&source, &roots)
        .expect("reference-admit canonical foundations");
    let uses = names(&["Eq.ndrec", "propext", "Classical.choice"]);
    let good = gate.check(&source, &uses);
    assert!(good.passed(false), "{}", good.refusal_summary(false));

    // Mutation after the successful check cannot borrow the original receipt.
    let mut wrong_type = source.clone();
    let mut info = source
        .get_const(&Name::from_string("propext"))
        .expect("propext")
        .clone();
    info.type_ = Expr::const_(Name::from_string("False"), vec![]);
    assert!(wrong_type
        .extend_constants_structural(std::iter::once(info))
        .is_empty());
    assert!(!gate.check(&wrong_type, &roots).passed(false));
    assert!(ImportedConeGate::from_reference_cone(&wrong_type, &roots).is_err());

    let mut wrong_rule = source
        .clone_pruned_shadowing_overlay(&std::iter::once(Name::from_string("Eq.rec")).collect());
    let mut rec = source
        .get_recursor(&Name::from_string("Eq.rec"))
        .expect("Eq.rec")
        .clone();
    rec.rules[0].rhs = Expr::sort(Level::zero());
    assert!(!wrong_rule
        .extend_recursors_structural(std::iter::once(rec.clone()))
        .is_empty());
    // Test-only corruption bypasses that first defence to exercise the receipt.
    wrong_rule.extend_recursors_unchecked(std::iter::once(rec));
    assert!(!gate.check(&wrong_rule, &uses).passed(false));
    assert!(ImportedConeGate::from_reference_cone(&wrong_rule, &roots).is_err());

    let mut wrong_metadata =
        source.clone_pruned_shadowing_overlay(&std::iter::once(Name::from_string("Eq")).collect());
    let mut family = source
        .get_inductive(&Name::from_string("Eq"))
        .expect("Eq")
        .clone();
    family.is_large_elim = !family.is_large_elim;
    wrong_metadata.extend_inductives_unchecked(std::iter::once(family));
    assert!(!gate.check(&wrong_metadata, &uses).passed(false));

    let mut extra_axiom = source.clone();
    let mut info = source
        .get_const(&Name::from_string("propext"))
        .expect("propext")
        .clone();
    info.name = Name::from_string("not_a_foundation");
    info.type_ = Expr::const_(Name::from_string("False"), vec![]);
    assert!(extra_axiom
        .extend_constants_structural(std::iter::once(info))
        .is_empty());
    assert!(!gate
        .check(&extra_axiom, &names(&["not_a_foundation"]))
        .passed(false));

    let restored = gate.check(&source, &uses);
    assert!(
        restored.passed(false),
        "{}",
        restored.refusal_summary(false)
    );
}
