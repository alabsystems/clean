// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Strictly check reached trie roots after the actual EvalIR builder runs.
//! A later builder refusal remains a refusal; this is not complete-bundle coverage.

use super::{
    bundles::{run_bundle, CoreSpecBundle},
    BMEM_TRIE_NAMES,
};
use crate::spec::{ProofStatus, Specification};
use crate::spec_axiom_closure::computed_axiom_closure;
use clean_kernel::{
    ConstantKind, DeclarationVerification, Expr, ExprKind, Level, Name, TypeChecker,
};
use std::collections::BTreeSet;

fn require_closed(expression: &Expr, name: &str) {
    assert!(
        !expression.has_fvar_quick(),
        "{name}: unexpected free variable"
    );
    assert!(
        !expression.has_loose_bvars(),
        "{name}: loose bound variable"
    );
    assert!(
        !expression.has_expr_mvar_quick(),
        "{name}: unresolved term meta"
    );
    assert!(
        !expression.has_level_mvar_quick(),
        "{name}: unresolved universe meta"
    );
}

fn require_checked_root(spec: &Specification, name: &str) {
    let record = spec
        .get_definition(name)
        .unwrap_or_else(|| panic!("{name}: actual source record"));
    assert_eq!(record.name, name, "{name}: exact stored name");
    assert!(
        !record.is_axiom,
        "{name}: source record must not be an axiom"
    );
    assert_ne!(
        record.proof_status,
        ProofStatus::Axiom,
        "{name}: axiom status"
    );
    assert!(
        record
            .value_src
            .as_ref()
            .is_some_and(|source| !source.is_empty()),
        "{name}: actual authored value"
    );
    let type_ = record
        .elaborated_type
        .as_ref()
        .unwrap_or_else(|| panic!("{name}: stored type"));
    let value = record
        .elaborated_value
        .as_ref()
        .unwrap_or_else(|| panic!("{name}: stored value"));
    let kernel_name = Name::from_string(name);
    let root = spec
        .env()
        .get_const(&kernel_name)
        .unwrap_or_else(|| panic!("{name}: actual kernel root"));
    assert_eq!(root.name, kernel_name, "{name}: exact live kernel name");
    assert_ne!(root.kind, ConstantKind::Axiom, "{name}: kernel axiom");
    assert_eq!(&root.type_, type_, "{name}: source/kernel type identity");
    assert_eq!(
        root.value.as_ref(),
        Some(value),
        "{name}: source/kernel value identity"
    );
    assert_eq!(
        spec.env().declaration_verification(&kernel_name),
        Some(DeclarationVerification::FullKernelCheck),
        "{name}: full checked provenance"
    );
    require_closed(type_, name);
    require_closed(value, name);
    assert!(
        !value.collect_constants().contains(&kernel_name),
        "{name}: value must not cite its own root"
    );

    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let sort = checker
        .infer_type_full(type_)
        .unwrap_or_else(|error| panic!("{name}: full declared-type check: {error:?}"));
    assert!(
        matches!(checker.whnf(&sort).kind(), ExprKind::Sort(_)),
        "{name}: declared type must inhabit a sort"
    );
    assert!(
        !checker.heartbeat_spent(),
        "{name}: declared-type check must finish"
    );
    checker
        .check_type(value, type_)
        .unwrap_or_else(|error| panic!("{name}: public full value check: {error:?}"));
    assert!(
        !checker.heartbeat_spent(),
        "{name}: value check must finish"
    );
    spec.verify_definition(name).unwrap_or_else(|error| {
        panic!("{name}: original verification must also succeed: {error:?}")
    });

    require_empty_closures(spec, &kernel_name, name);
}

fn require_empty_closures(spec: &Specification, kernel_name: &Name, name: &str) {
    // Require actual answers before using the legacy computed API, whose own
    // absent-root behavior is an empty set. Missing data cannot pass this test.
    let domain = spec
        .env()
        .axiom_deps(kernel_name)
        .unwrap_or_else(|| panic!("{name}: missing domain closure"));
    let foundational = spec
        .env()
        .foundational_axiom_deps(kernel_name)
        .unwrap_or_else(|| panic!("{name}: missing foundational closure"));
    let computed = computed_axiom_closure(spec, name);
    let rendered: BTreeSet<String> = domain.iter().map(Name::to_unambiguous_string).collect();
    assert_eq!(
        computed, rendered,
        "{name}: computed/live domain closure agreement"
    );
    assert!(domain.is_empty(), "{name}: domain axioms {domain:?}");
    assert!(
        foundational.is_empty(),
        "{name}: foundational axioms {foundational:?}"
    );
    assert!(computed.is_empty(), "{name}: computed axioms {computed:?}");
}

#[test]
fn actual_evalir_builder_trie21_roots_recheck_strictly_at_the_reached_prefix() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = Specification::new_empty();
        let result = run_bundle(&mut spec, CoreSpecBundle::EvalIr);
        println!("TRIE_PREFIX_ACTUAL_BUNDLE_OUTCOME {result:?}");
        // This selected-root test may inspect a reached prefix after a later
        // refusal. The original complete-bundle and strict46 tests still fail
        // that refusal; no error is turned into a completed-bundle result here.
        let expected: BTreeSet<_> = BMEM_TRIE_NAMES.iter().copied().collect();
        assert_eq!(BMEM_TRIE_NAMES.len(), 21);
        assert_eq!(expected.len(), 21, "exact distinct production roots");
        let data = ["IRBmKV", "IRBmTrie"];
        let mut checked = BTreeSet::new();
        let mut values = 0;
        for &name in BMEM_TRIE_NAMES {
            assert!(checked.insert(name));
            if data.contains(&name) {
                let key = Name::from_string(name);
                let record = spec
                    .get_definition(name)
                    .expect("actual source family record");
                let family = spec
                    .env()
                    .get_inductive(&key)
                    .expect("actual reached family");
                let root = spec
                    .env()
                    .get_const(&key)
                    .expect("actual reached kernel family");
                assert_eq!(root.name, key);
                assert!(!record.is_axiom);
                assert_ne!(root.kind, ConstantKind::Axiom);
                assert_eq!(record.elaborated_type.as_ref(), Some(&root.type_));
                assert_eq!(family.type_, root.type_);
                assert!(record.elaborated_value.is_none());
                assert!(
                    root.value.is_none(),
                    "data metadata, never a value-free proof"
                );
                assert_eq!(
                    spec.env().declaration_verification(&key),
                    Some(DeclarationVerification::FullKernelCheck)
                );
                assert_eq!(family.num_params, 1);
                assert_eq!(family.num_indices, 0);
                require_closed(&root.type_, name);
                let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
                let sort = checker
                    .infer_type_full(&root.type_)
                    .expect("full family-type check");
                assert!(matches!(checker.whnf(&sort).kind(), ExprKind::Sort(_)));
                let term = Expr::const_(
                    key.clone(),
                    root.level_params
                        .iter()
                        .cloned()
                        .map(Level::param)
                        .collect::<Vec<_>>(),
                );
                checker
                    .check_type(&term, &root.type_)
                    .expect("public full family check");
                assert!(!checker.heartbeat_spent());
                require_empty_closures(&spec, &key, name);
            } else {
                require_checked_root(&spec, name);
                values += 1;
            }
        }
        assert_eq!(values, 19, "all actual value-bearing trie roots");
        assert_eq!(
            checked, expected,
            "all and only the 21 reached production roots"
        );
        println!(
            "TRIE_PREFIX_STRICT_ROOTS values={values} families=2 total={}",
            checked.len()
        );
    });
}
