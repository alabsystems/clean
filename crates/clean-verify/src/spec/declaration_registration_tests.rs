// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::Environment;

fn specification() -> Specification {
    Specification {
        env: Environment::with_prelude(),
        definitions: Default::default(),
        red_env_script_override: None,
        red_env_interning_override: None,
        model_unit_source: Default::default(),
    }
}

fn assert_unchanged(before: &Specification, after: &Specification) {
    let expected = before.env.effect_since(&before.env);
    let observed = after.env.effect_since(&before.env);
    assert_eq!(expected.disagreement(&observed, &after.env), None);
    assert_eq!(before.env.generation(), after.env.generation());
    assert_eq!(before.definitions.len(), after.definitions.len());
    for (name, definition) in &before.definitions {
        let retained = after
            .definitions
            .get(name)
            .expect("original tracking remains");
        assert_eq!(definition.type_src, retained.type_src);
        assert_eq!(definition.value_src, retained.value_src);
        assert_eq!(definition.elaborated_type, retained.elaborated_type);
        assert_eq!(definition.elaborated_value, retained.elaborated_value);
    }
}

#[test]
fn late_attribute_refusal_cannot_leave_the_checked_declaration_behind() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let before = spec.clone();
        let error = spec
            .add_recursive_def(
                "@[implemented_by absentImplementation] def lateRefusal : Nat := 0",
                "late attribute refusal",
            )
            .expect_err("unknown implementation remains a registration refusal");
        assert!(error.to_string().contains("absentImplementation"));
        assert_unchanged(&before, &spec);
        assert!(spec
            .env
            .get_const(&Name::from_string("lateRefusal"))
            .is_none());
    });
}

#[test]
fn unexpected_inductive_result_cannot_publish_a_family_through_the_definition_api() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let before = spec.clone();
        let error = spec
            .add_recursive_def(
                "inductive WrongResult : Type\n| mk : WrongResult",
                "wrong result shape",
            )
            .expect_err("the existing declaration-kind restriction remains");
        assert!(matches!(error, SpecError::TypeError(_)));
        assert_unchanged(&before, &spec);
        for name in ["WrongResult", "WrongResult.mk", "WrongResult.rec"] {
            assert!(spec.env.get_const(&Name::from_string(name)).is_none());
        }
    });
}
