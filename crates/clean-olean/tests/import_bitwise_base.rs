// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{Environment, Name};
use clean_olean::{load_module_with_deps, ImportedConeGate};
use std::collections::BTreeSet;

#[test]
fn imported_list_indexing_replays_with_bitwise_definitions() {
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("Lean bin");
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned library");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let output = std::process::Command::new(bin.join("leanchecker"))
        .args(["--fresh", "Init.GetElem"])
        .env("LEAN_PATH", &lib)
        .env("PATH", std::env::join_paths(paths).expect("tool path"))
        .output()
        .expect("independent replay");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let base = Environment::try_with_prelude_for_import().expect("import prelude");
    let mut env = base.clone();
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean");
    load_module_with_deps(&mut env, "Init.GetElem", &[lib]).expect("actual indexed-list module");
    for text in ["Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftRight"] {
        let name = Name::from_string(text);
        assert!(
            env.native_fold_authorized(&name),
            "existing fold authority for {text}"
        );
        let review = clean_kernel::env::native_fold_review::review(&env, &name, true);
        eprintln!("bitwise review {text}: {review:?}");
        assert!(review.passed(), "{text}: {review:?}");
    }
    let name = Name::from_string("List.get?Internal._sparseCasesOn_1");
    assert!(
        env.get_const(&name).is_some(),
        "actual compiler-generated helper"
    );
    let dependencies = env.axiom_deps(&name).expect("helper axiom closure");
    assert!(
        dependencies
            .iter()
            .all(|axiom| env.is_canonical_foundational_axiom(axiom)),
        "{dependencies:?}"
    );
    let verdict = ImportedConeGate::new(&base).check(&env, &BTreeSet::from([name]));
    assert!(verdict.passed(false), "{}", verdict.refusal_summary(false));
}

#[test]
fn explicit_caller_axiom_is_not_silently_replaced_during_replay() {
    use clean_kernel::{BinderInfo, Declaration, Expr};
    let mut base = Environment::try_with_prelude_for_import().expect("import prelude");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    base.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.land"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, nat.clone(), nat),
        ),
    })
    .expect("caller-supplied axiom");
    let mut env = base.clone();
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean");
    load_module_with_deps(&mut env, "Init.GetElem", &[lib]).expect("actual indexed-list module");
    let verdict = ImportedConeGate::new(&base).check(
        &env,
        &BTreeSet::from([Name::from_string("List.get?Internal._sparseCasesOn_1")]),
    );
    assert!(
        !verdict.passed(false),
        "the caller's axiom must stay opaque in replay"
    );
    assert!(
        verdict.refusals.iter().any(|refusal| matches!(refusal,
        clean_olean::recheck_closed::ClosedRecheckRefusal::DeclarationRefused { name, .. }
        if name == "List.get?Internal._sparseCasesOn_1")),
        "{}",
        verdict.refusal_summary(false)
    );
}

#[test]
fn counterfeit_bitwise_definition_is_not_bound() {
    use clean_kernel::{BinderInfo, Expr};
    let base = Environment::try_with_prelude_for_import().expect("import prelude");
    let mut env = base.clone();
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean");
    load_module_with_deps(&mut env, "Init.GetElem", &[lib]).expect("actual indexed-list module");
    let name = Name::from_string("Nat.land");
    let mut counterfeit = env.get_const(&name).expect("imported land").clone();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    counterfeit.value = Some(Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat, Expr::bvar(1)),
    ));
    assert!(env.forget_decl(&name));
    assert!(env
        .extend_constants_structural(std::iter::once(counterfeit))
        .is_empty());
    let verdict = ImportedConeGate::new(&base).check(&env, &BTreeSet::from([name]));
    assert!(!verdict.passed(false), "counterfeit land must be rejected");
    assert!(
        verdict.refusals.iter().any(|refusal| matches!(refusal,
        clean_olean::recheck_closed::ClosedRecheckRefusal::ExtensionBindingMismatch { name, .. }
        if name == "Nat.land")),
        "{}",
        verdict.refusal_summary(false)
    );
}
