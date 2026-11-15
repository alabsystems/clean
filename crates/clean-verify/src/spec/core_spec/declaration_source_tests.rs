// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use crate::spec::{SpecError, Specification};
use clean_kernel::Name;

fn assert_unchanged(before: &Specification, after: &Specification) {
    let no_change = before.env().effect_since(before.env());
    let observed = after.env().effect_since(before.env());
    assert_eq!(no_change.disagreement(&observed, after.env()), None);
    assert_eq!(before.env().generation(), after.env().generation());
    assert_eq!(before.definitions().len(), after.definitions().len());
}

#[test]
fn inductive_registration_rejects_trailing_source_before_mutation() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = Specification::new_empty();
        let source = "inductive ExactSourceData : Type\n| mk : ExactSourceData";
        let before = spec.clone();
        for suffix in ["\n)", "\n,", "\ndef hidden : Type := Type"] {
            let result = spec.add_inductive(&format!("{source}{suffix}"), "malformed source");
            assert!(
                matches!(result, Err(SpecError::ParseError(_))),
                "{result:?}"
            );
            assert_unchanged(&before, &spec);
            for name in [
                "ExactSourceData",
                "ExactSourceData.mk",
                "ExactSourceData.rec",
                "hidden",
            ] {
                assert!(spec.env().get_const(&Name::from_string(name)).is_none());
            }
        }
        spec.add_inductive(&format!("{source}\n-- complete source\n"), "valid retry")
            .expect("the same valid declaration still registers after refusals");
        assert!(spec
            .env()
            .get_const(&Name::from_string("ExactSourceData.rec"))
            .is_some());
    });
}

#[test]
fn definition_registration_rejects_trailing_source_before_mutation() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = Specification::new_empty();
        let source = "def exactSourceIdentity (A : Type) (x : A) : A := x";
        let before = spec.clone();
        for suffix in ["\n)", "\n,", "\ndef hidden : Type := Type"] {
            let result = spec.add_recursive_def(&format!("{source}{suffix}"), "malformed source");
            assert!(
                matches!(result, Err(SpecError::ParseError(_))),
                "{result:?}"
            );
            assert_unchanged(&before, &spec);
            for name in ["exactSourceIdentity", "hidden"] {
                assert!(spec.env().get_const(&Name::from_string(name)).is_none());
            }
        }
        spec.add_recursive_def(&format!("{source}\n/- complete source -/\n"), "valid retry")
            .expect("the same valid definition still registers after refusals");
        assert!(spec.get_definition("exactSourceIdentity").is_some());
    });
}
