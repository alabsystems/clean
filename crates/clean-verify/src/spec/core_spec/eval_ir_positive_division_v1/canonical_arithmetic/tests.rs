// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::{extend_owned, roots, rows};
use crate::spec::{SpecError, Specification};
use clean_kernel::Name;
use std::collections::BTreeSet;

#[test]
fn composition_preflights_every_existing_source_name_before_returning_an_owner() {
    crate::test_utils::run_with_stack(|| {
        let base = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        assert_eq!(rows().count(), 128);
        assert_eq!(roots().count(), 42);
        assert_eq!(
            rows().map(|(name, _)| name).collect::<BTreeSet<_>>().len(),
            128
        );
        // Capture a separate real registration. Production elaboration may
        // retain OfNat applications: its stored Nat zero is not required to
        // have the raw Expr::nat_lit syntax. Compare exact stored endpoints,
        // never normalize the conflicting definition or rewrite its value.
        let (sentinel_type, sentinel_value) = {
            let mut sentinel = base.clone();
            sentinel
                .add_recursive_def(
                    "def canonical_arithmetic_collision_sentinel : Nat := 0",
                    "independently registered collision sentinel",
                )
                .unwrap();
            let info = sentinel
                .env()
                .get_const(&Name::from_string(
                    "canonical_arithmetic_collision_sentinel",
                ))
                .unwrap();
            (
                info.type_.clone(),
                info.value.clone().expect("stored sentinel body"),
            )
        };
        for (name, _) in rows() {
            let mut conflict = base.clone();
            conflict
                .add_recursive_def(
                    &format!("def {name} : Nat := 0"),
                    "genuine source collision",
                )
                .unwrap();
            let recorded = conflict
                .env()
                .get_const(&Name::from_string(name))
                .unwrap()
                .clone();
            assert_eq!(recorded.type_, sentinel_type, "{name}");
            assert_eq!(recorded.value.as_ref(), Some(&sentinel_value), "{name}");
            let original = conflict.clone();
            let error = conflict.into_canonical_arithmetic_byte_v1().unwrap_err();
            assert!(
                matches!(&error, SpecError::EnvError(detail) if detail == &format!("positive-division package name collision: {name}")),
                "{name}: {error:?}"
            );
            assert_eq!(original.definitions().len(), base.definitions().len() + 1);
            assert_eq!(
                original.env().get_const(&Name::from_string(name)),
                Some(&recorded),
                "the complete actual declaration remains unchanged: {name}"
            );
            assert!(base.get_definition(name).is_none());
            // The same contract also refuses an environment-only collision;
            // removing specification metadata cannot hide its actual constant.
            let mut environment_only = original;
            environment_only.definitions_mut().remove(name).unwrap();
            assert_eq!(
                environment_only.env().get_const(&Name::from_string(name)),
                Some(&recorded),
                "removing metadata retains the exact conflicting declaration: {name}"
            );
            let error = environment_only
                .into_canonical_arithmetic_byte_v1()
                .unwrap_err();
            assert!(
                matches!(&error, SpecError::EnvError(detail) if detail.ends_with(name)),
                "{error:?}"
            );
        }
        let owned = base.clone().into_canonical_arithmetic_byte_v1().unwrap();
        assert_eq!(owned.definitions().len(), base.definitions().len() + 128);
        for root in roots() {
            let key = Name::from_string(root);
            assert!(owned.env().axiom_deps(&key).unwrap().is_empty());
            assert!(owned.env().trust_marker_deps(&key).unwrap().is_empty());
        }
    });
}

#[test]
fn composition_actual_last_false_source_refuses_and_original_owner_remains_retryable() {
    crate::test_utils::run_with_stack(|| {
        let base = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        const LAST: &str = "ir_byte_shl_uint_canonical_v1";
        const FALSE: &str = "def ir_byte_shl_uint_canonical_v1 : @Eq Bool Bool.true Bool.false := @Eq.refl Bool Bool.false";
        assert_eq!(rows().last().unwrap().0, LAST);
        let declarations =
            rows().map(|(name, source)| (name, if name == LAST { FALSE } else { source }));
        let error = extend_owned(base.clone(), declarations).unwrap_err();
        assert!(
            !matches!(&error, SpecError::DeclarationBudgetExhausted { .. }),
            "resource stop is not a rejection: {error:?}"
        );
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        assert!(
            format!("{error:?}").contains(LAST),
            "actual final false declaration: {error:?}"
        );
        for (name, _) in rows() {
            assert!(base.get_definition(name).is_none());
            assert!(base.env().get_const(&Name::from_string(name)).is_none());
        }
        let owned: Specification = base.clone().into_canonical_arithmetic_byte_v1().unwrap();
        assert_eq!(owned.definitions().len(), base.definitions().len() + 128);
        owned.verify_definition(LAST).unwrap();
        assert!(owned
            .env()
            .axiom_deps(&Name::from_string(LAST))
            .unwrap()
            .is_empty());
    });
}
