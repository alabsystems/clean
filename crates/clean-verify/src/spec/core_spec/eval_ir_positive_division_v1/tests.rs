// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::{install_transactionally, laws, source_for_probe, verify_root};
use crate::spec::{ModelUnitSource, ProofStatus, SpecError, Specification};
use clean_kernel::{
    CertificationAudit, CertificationIssue, Declaration, Expr, Level, Name, TypeChecker,
};
use std::collections::BTreeSet;

// Independent, ordered inventory: deriving the expectation from `laws()` would
// miss accidental omissions, duplicates, renaming and registration-order drift.
const EXPECTED_NAMES: [&str; 49] = [
    "nat_add_zero_left",
    "nat_add_succ_left",
    "nat_add_assoc_local",
    "nat_add_comm_local",
    "ir_nat_mul_succ_left",
    "nat_add_swap_first_two",
    "ir_nat_mul_add_right",
    "ir_nat_dbl_is_add",
    "nat_add_exchange",
    "ir_nat_mul_add_left",
    "ir_nat_mul_dbl_shift",
    "ir_nat_ltb_walk_zero_right",
    "ir_nat_ltb_walk_add_cancel_right",
    "ir_nat_sub_add_cancel_walk",
    "ir_nat_sub_bound_walk",
    "ir_dm_step2_gen",
    "ir_dm_step_eq",
    "ir_dm_step_bound",
    "ir_nat_mul_zero_left",
    "ir_dm_eta",
    "ir_dm_step_on_state",
    "ir_dm_go_gen",
    "ir_dm_go_eq",
    "ir_dm_go_bound",
    "ir_nat_mul_comm",
    "ir_nat_ltb_walk_add_self_false",
    "nat_succ_inj",
    "nat_add_right_cancel",
    "nat_add_left_cancel",
    "ir_nat_mul_succ_left_assoc",
    "ir_nat_mul_zero_left_add",
    "ir_nat_ltb_walk_add_left_self_false",
    "ir_nat_lt_add_left_absurd",
    "ir_nat_qr_unique_q",
    "ir_nat_qr_unique_r",
    "ir_nat_mul_one_left",
    "ir_div_rem_go",
    "ir_div_go_gen",
    "ir_div_rem_go_gen",
    "ir_div_go_pair_eq",
    "ir_div_rem_go_bound",
    "nat_sub_add_left",
    "ir_nat_rem_is_residue",
    "ir_nat_ltb_walk_self_lt_add_succ",
    "ir_div_fuel_suffices_pos",
    "ir_dm_go_is_the_quotient",
    "ir_dm_go_is_the_remainder",
    "ir_div_agrees_at_fuel",
    "ir_rem_agrees_at_fuel",
];

fn byte_spec() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("ordinary public owned ByteV1 substrate")
}

fn independent_audit(spec: &Specification, root: &str) -> CertificationAudit {
    let info = spec
        .env()
        .get_const(&Name::from_string(root))
        .expect("actual stored root");
    let term = Expr::const_(
        info.name.clone(),
        info.level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let sort = TypeChecker::new(spec.env())
        .infer_sort(&info.type_)
        .expect("root type is a sort");
    let (goal, proof) = if sort.is_zero() {
        (info.type_.clone(), term)
    } else {
        (
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![sort.clone()]),
                [info.type_.clone(), term.clone(), term.clone()],
            ),
            Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![sort]),
                [info.type_.clone(), term],
            ),
        )
    };
    spec.env().audit_certification(&goal, &proof)
}

fn assert_owner_unchanged(before: &Specification, after: &Specification) {
    // This existing typed observer covers all semantic environment components
    // without serializing the entire shared expression DAG into a JSON tree.
    let no_change = before.env().effect_since(before.env());
    let observed = after.env().effect_since(before.env());
    assert_eq!(no_change.disagreement(&observed, after.env()), None);
    assert_eq!(before.env().generation(), after.env().generation());
    assert_eq!(
        before.env().has_constant_source(),
        after.env().has_constant_source()
    );
    assert_eq!(before.definitions().len(), after.definitions().len());
    for (name, expected) in before.definitions() {
        let actual = after
            .get_definition(name)
            .expect("rollback retains every definition");
        assert_eq!(
            (
                &actual.name,
                &actual.type_src,
                &actual.value_src,
                actual.is_axiom,
                actual.category,
                actual.proof_status,
                &actual.description,
                &actual.elaborated_type,
                &actual.elaborated_value,
                &actual.dependencies,
                &actual.axiom_deps
            ),
            (
                &expected.name,
                &expected.type_src,
                &expected.value_src,
                expected.is_axiom,
                expected.category,
                expected.proof_status,
                &expected.description,
                &expected.elaborated_type,
                &expected.elaborated_value,
                &expected.dependencies,
                &expected.axiom_deps
            ),
            "complete specification bookkeeping for {name}",
        );
        let key = Name::from_string(name);
        assert_eq!(
            before.env().declaration_verification(&key),
            after.env().declaration_verification(&key),
            "transient provenance for {name}"
        );
    }
    assert_eq!(
        before.red_env_script_override,
        after.red_env_script_override
    );
    assert_eq!(
        before.red_env_interning_override,
        after.red_env_interning_override
    );
    match (&before.model_unit_source, &after.model_unit_source) {
        (ModelUnitSource::CleanFiles, ModelUnitSource::CleanFiles)
        | (ModelUnitSource::RetainedLiterals, ModelUnitSource::RetainedLiterals) => {}
        (ModelUnitSource::Planted(expected), ModelUnitSource::Planted(actual)) => {
            assert_eq!(expected, actual)
        }
        (expected, actual) => panic!("model source changed: {expected:?} -> {actual:?}"),
    }
}

fn assert_collision(error: SpecError, name: &str) {
    match error {
        SpecError::EnvError(detail) => {
            assert!(detail.contains("name collision"), "{detail}");
            assert!(detail.contains(name), "{detail}");
        }
        other => panic!("expected exact collision for {name}, got {other}"),
    }
}

#[test]
fn public_owned_package_has_all_49_exact_roots_and_strict_authority() {
    crate::test_utils::run_with_stack(|| {
        assert_eq!(
            laws().map(|(name, _)| name).collect::<Vec<_>>(),
            EXPECTED_NAMES
        );
        let base = byte_spec();
        let spec = crate::eval_ir::build_positive_division_byte_prelude_spec_v1_with_stack()
            .expect("public owned positive-divisor vocabulary");
        assert_eq!(
            spec.definitions().len(),
            base.definitions().len() + EXPECTED_NAMES.len() + 1
        );
        let changed = spec.env().effect_since(base.env());
        let actual: BTreeSet<_> = changed
            .changed_constant_names()
            .map(ToString::to_string)
            .collect();
        let expected: BTreeSet<_> = std::iter::once("ir_bool_false_ne_true")
            .chain(EXPECTED_NAMES.iter().copied())
            .map(str::to_owned)
            .collect();
        assert_eq!(
            actual, expected,
            "only the canonical 49 laws and original Bool prerequisite are added or changed"
        );
        let old_cong = Name::from_string("Eq.cong");
        let bridge = Name::from_string("ir_eq_cong");
        let mut bridge_used = false;
        for name in EXPECTED_NAMES {
            let definition = spec
                .get_definition(name)
                .expect("original registered definition");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            spec.verify_definition(name)
                .unwrap_or_else(|error| panic!("{name}: {error}"));
            let audit = independent_audit(&spec, name);
            assert!(audit.is_certified(), "{name}: {audit:#?}");
            assert!(
                audit.dependencies.contains(&Name::from_string(name)),
                "audit includes actual root {name}"
            );
            assert!(
                !audit.dependencies.contains(&old_cong),
                "foundation-only congruence leaked into {name}"
            );
            bridge_used |= audit.dependencies.contains(&bridge);
            assert!(
                spec.env()
                    .axiom_deps(&Name::from_string(name))
                    .expect("root closure")
                    .is_empty(),
                "{name}"
            );
            assert!(
                spec.env()
                    .trust_marker_deps(&Name::from_string(name))
                    .expect("root marker closure")
                    .is_empty(),
                "{name}"
            );
            let raw = source_for_probe(name).expect("historical probe source retained");
            assert_eq!(definition.type_src, raw.replace("Eq.cong", "ir_eq_cong"));
            assert_eq!(
                definition.value_src.as_deref(),
                Some(definition.type_src.as_str())
            );
        }
        assert!(
            bridge_used,
            "production proof closure uses the existing shared congruence bridge"
        );
        assert!(
            laws().any(|(_, source)| source.contains("Eq.cong")),
            "raw historical spelling is not replaced at its source"
        );
        assert!(source_for_probe("not_a_positive_division_law").is_none());
        assert!(
            base.get_definition(EXPECTED_NAMES[0]).is_none(),
            "owned installation does not mutate the shared base"
        );
    });
}

#[test]
fn early_and_late_collisions_preserve_the_complete_owner() {
    crate::test_utils::run_with_stack(|| {
        for (name, source) in [
            (
                "ir_bool_false_ne_true",
                "def ir_bool_false_ne_true : Nat := Nat.zero",
            ),
            (
                "nat_add_zero_left",
                "def nat_add_zero_left : Nat := Nat.zero",
            ),
            (
                "ir_rem_agrees_at_fuel",
                "def ir_rem_agrees_at_fuel : Nat := Nat.zero",
            ),
        ] {
            let mut spec = byte_spec();
            spec.add_recursive_def(source, "deliberate checked name squatter")
                .expect("squatter fixture is type-correct");
            spec.env_mut().set_option(
                "positiveDivisionTest.sentinel".into(),
                Some("retained".into()),
            );
            let before = spec.clone();
            assert_collision(
                spec.install_eval_ir_positive_division_laws_v1()
                    .expect_err("existing package names must refuse"),
                name,
            );
            assert_owner_unchanged(&before, &spec);
        }
        // Environment-only squatters are invisible to specification bookkeeping.
        let mut spec = byte_spec();
        spec.env_mut()
            .add_decl(Declaration::Axiom {
                name: Name::from_string("nat_add_zero_left"),
                level_params: vec![],
                type_: Expr::const_str("Nat"),
            })
            .expect("checked environment-only collision fixture");
        let before = spec.clone();
        assert_collision(
            spec.install_eval_ir_positive_division_laws_v1()
                .expect_err("environment-only collision must refuse"),
            "nat_add_zero_left",
        );
        assert_owner_unchanged(&before, &spec);
    });
}

#[test]
fn repeat_installation_refuses_without_replacing_or_promoting_roots() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::eval_ir::build_positive_division_byte_prelude_spec_v1_with_stack()
            .expect("first public installation");
        let before = spec.clone();
        assert_collision(
            spec.install_eval_ir_positive_division_laws_v1()
                .expect_err("fixed package is not first-name-wins idempotent"),
            "ir_bool_false_ne_true",
        );
        assert_owner_unchanged(&before, &spec);
    });
}

#[test]
fn missing_substrate_refuses_without_leaking_session_or_spec_state() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = Specification::new_empty();
        spec.env_mut().set_option(
            "positiveDivisionTest.sentinel".into(),
            Some("retained".into()),
        );
        let before = spec.clone();
        let error = spec
            .install_eval_ir_positive_division_laws_v1()
            .expect_err("missing EvalIR arithmetic substrate must refuse");
        assert!(
            error.to_string().contains("ir_bool_false_ne_true"),
            "{error}"
        );
        assert_owner_unchanged(&before, &spec);
        assert!(EXPECTED_NAMES
            .iter()
            .all(|name| spec.get_definition(name).is_none()));
    });
}

#[test]
fn last_false_arithmetic_row_rolls_back_all_preceding_rows() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = byte_spec();
        spec.env_mut().set_option(
            "positiveDivisionTest.sentinel".into(),
            Some("retained".into()),
        );
        let before = spec.clone();
        let mut rows: Vec<_> = laws().collect();
        assert_eq!(rows.len(), 49);
        let last = rows.last_mut().expect("fixed nonempty catalog");
        assert_eq!(last.0, "ir_rem_agrees_at_fuel");
        last.1 = "def ir_rem_agrees_at_fuel : @Eq Nat Nat.zero (Nat.succ Nat.zero) := @Eq.refl Nat (Nat.succ Nat.zero)";
        let error = install_transactionally(&mut spec, rows.into_iter())
            .expect_err("last false arithmetic claim must fail after earlier rows register");
        let detail = error.to_string();
        assert!(detail.contains("ir_rem_agrees_at_fuel"), "{detail}");
        assert!(
            detail.to_ascii_lowercase().contains("type mismatch"),
            "mathematical refusal, not lookup or parsing: {detail}"
        );
        for resource in [
            "budget",
            "heartbeat",
            "recursion limit",
            "unknown identifier",
            "parse error",
        ] {
            assert!(!detail.to_ascii_lowercase().contains(resource), "{detail}");
        }
        assert_owner_unchanged(&before, &spec);
        assert!(EXPECTED_NAMES
            .iter()
            .all(|name| spec.get_definition(name).is_none()));
    });
}

#[test]
fn type_correct_axiom_and_sorry_debt_cannot_be_promoted_by_bookkeeping() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = byte_spec();
        let axiom = Name::from_string("positive_division_test_axiom");
        spec.env_mut()
            .add_decl(Declaration::Axiom {
                name: axiom.clone(),
                level_params: vec![],
                type_: Expr::const_str("Nat"),
            })
            .expect("ordinary checked axiom fixture");
        spec.add_recursive_def(
            "def positive_division_axiom_backed : Nat := positive_division_test_axiom",
            "deliberate domain-axiom debt",
        )
        .expect("debt-bearing computational root is well-typed");
        spec.add_recursive_def(
            "def positive_division_sorry_backed : Nat := @sorryAx Nat Bool.false",
            "deliberate incomplete-proof marker debt",
        )
        .expect("existing sorry axiom supplies a type-correct negative fixture");
        for (root, debt) in [
            ("positive_division_axiom_backed", axiom),
            (
                "positive_division_sorry_backed",
                Name::from_string("sorryAx"),
            ),
        ] {
            let definition = spec
                .definitions_mut()
                .get_mut(root)
                .expect("debt root bookkeeping");
            definition.proof_status = ProofStatus::DerivedProved;
            definition.axiom_deps.clear();
            definition.dependencies = Some(Default::default());
            spec.verify_definition(root)
                .expect("mere typing does not certify authority");
            let error =
                verify_root(&spec, root).expect_err("falsified labels cannot certify actual debt");
            assert!(error.to_string().contains(root), "{error}");
            let audit = independent_audit(&spec, root);
            assert!(!audit.is_certified(), "{audit:#?}");
            assert!(audit.dependencies.contains(&Name::from_string(root)));
            assert!(audit.dependencies.contains(&debt));
            assert!(audit.issues.iter().any(|issue| matches!(issue,
                CertificationIssue::NonFoundationalAxiom { name } | CertificationIssue::TrustMarker { name } if name == &debt
            )), "actual debt is exposed: {audit:#?}");
        }
    });
}

#[test]
fn endpoint_metadata_drift_and_unsafe_or_partial_dependencies_refuse() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::eval_ir::build_positive_division_byte_prelude_spec_v1_with_stack()
            .expect("actual checked package");
        spec.definitions_mut()
            .get_mut("ir_dm_step2_gen")
            .expect("computational helper")
            .elaborated_value = Some(Expr::nat_lit(0));
        let error = verify_root(&spec, "ir_dm_step2_gen")
            .expect_err("cached metadata is not the stored endpoint");
        assert!(error.to_string().contains("inconsistent"), "{error}");
        for unsafe_dependency in [false, true] {
            let mut spec = byte_spec();
            let helper = Name::from_string("ir_nat_mul");
            if unsafe_dependency {
                spec.env_mut().mark_unsafe(helper);
            } else {
                spec.env_mut().mark_partial(helper);
            }
            let before = spec.clone();
            let error = spec
                .install_eval_ir_positive_division_laws_v1()
                .expect_err("unsafe or partial substrate cannot supply certified laws");
            let detail = error.to_string().to_ascii_lowercase();
            assert!(
                detail.contains(if unsafe_dependency {
                    "unsafe"
                } else {
                    "partial"
                }),
                "{error}"
            );
            assert_owner_unchanged(&before, &spec);
        }
    });
}
