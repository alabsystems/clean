// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use crate::spec::{SpecDefinition, Specification};
use clean_kernel::{ConstantKind, Declaration, Expr, Level, Name, TypeChecker};

pub(super) const ROOTS: [&str; 21] = [
    "ir_div_agrees_at_fuel",
    "ir_rem_agrees_at_fuel",
    "ir_byte_lshr_u64_by_three_v1",
    "ir_byte_ashr_i64_by_three_v1",
    "ir_byte_lshr_u64_max_by_three_v1",
    "ir_byte_ashr_i64_negative_one_by_three_v1",
    "ir_byte_ashr_i64_min_by_three_v1",
    "ir_byte_lshr_u64_by_three_result_bound_v1",
    "ir_byte_ashr_i64_by_three_result_bound_v1",
    "ir_byte_add_uint_canonical_v1",
    "ir_byte_add_int_canonical_v1",
    "ir_byte_add_uint_canonical_result_bound_v1",
    "ir_byte_add_int_canonical_result_bound_v1",
    "ir_byte_icmp_uint_ult_canonical_v1",
    "ir_byte_icmp_int_ult_canonical_v1",
    "ir_byte_icmp_uint_ule_canonical_v1",
    "ir_byte_icmp_int_ule_canonical_v1",
    "ir_byte_icmp_uint_ugt_canonical_v1",
    "ir_byte_icmp_int_ugt_canonical_v1",
    "ir_byte_icmp_uint_uge_canonical_v1",
    "ir_byte_icmp_int_uge_canonical_v1",
];

pub(super) fn strict_root(spec: &Specification, name: &str) {
    let key = Name::from_string(name);
    let info = spec.env().get_const(&key).expect("actual stored law");
    let definition = spec.get_definition(name).expect("actual metadata");
    let value = info.value.as_ref().expect("actual proof body");
    assert_eq!(info.kind, ConstantKind::Definition);
    assert!(!definition.is_axiom);
    assert_eq!(definition.elaborated_type.as_ref(), Some(&info.type_));
    assert_eq!(definition.elaborated_value.as_ref(), Some(value));
    assert!(!info.type_.has_fvar_quick() && !value.has_fvar_quick());
    spec.verify_definition(name).expect("exact stored replay");
    spec.env()
        .check_decl_readonly_strict(&Declaration::Definition {
            name: key.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: value.clone(),
            is_reducible: info.is_reducible,
        })
        .expect("strict immutable stored declaration check");
    let term = Expr::const_(
        key.clone(),
        info.level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let mut checker = TypeChecker::new(spec.env());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.check_type(&term, &info.type_).expect("strict root");
    assert!(!checker.heartbeat_spent());
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    let audit = spec.env().audit_certification(&info.type_, &term);
    assert!(audit.is_certified(), "{name}: {audit:#?}");
    assert!(audit.dependencies.contains(&key));
    assert!(spec.env().axiom_deps(&key).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&key).unwrap().is_empty());
}

pub(super) fn same_definition(before: &SpecDefinition, after: &SpecDefinition) {
    macro_rules! fields {
        ($($field:ident),+ $(,)?) => {
            $(assert_eq!(before.$field, after.$field, "{}: {}", before.name, stringify!($field));)+
        };
    }
    fields!(
        name,
        type_src,
        value_src,
        is_axiom,
        category,
        proof_status,
        description,
        elaborated_type,
        elaborated_value,
        dependencies,
        axiom_deps
    );
}

pub(super) fn same_definitions(expected: &Specification, actual: &Specification) {
    assert_eq!(expected.definitions().len(), actual.definitions().len());
    for (name, before) in expected.definitions() {
        let after = actual.get_definition(name).expect("complete clone");
        same_definition(before, after);
        assert_eq!(
            expected.env().get_const(&Name::from_string(name)),
            actual.env().get_const(&Name::from_string(name))
        );
        assert_eq!(
            expected
                .env()
                .declaration_verification(&Name::from_string(name)),
            actual
                .env()
                .declaration_verification(&Name::from_string(name))
        );
    }
    let empty = expected.env().effect_since(expected.env());
    let actual = actual.env().effect_since(expected.env());
    assert!(empty.disagreement(&actual, expected.env()).is_none());
}

/// Runs the exact test `name` alone in a fresh process with `probe=mode` and
/// returns its stdout once that process passed exactly that one test. The
/// caller asserts the completion line its own child half printed, so the
/// parent half of every probe test fails at its own site, never only inside
/// this helper.
pub(super) fn run_child(name: &str, probe: &str, mode: &str) -> String {
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args([name, "--exact", "--test-threads=1", "--nocapture"])
        .env(probe, mode)
        .env_remove("CLEAN_SPEC_DECL_BUDGET")
        .env_remove("CLEAN_STRICT_PROOF_QUALITY")
        .output()
        .expect("isolated actual public profile consumer");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "{mode}: {stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.contains("1 passed; 0 failed"), "{stdout}");
    stdout.into_owned()
}
