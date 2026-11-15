// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{theorem, NEGATIVE_CONTROLS};
use super::checks::{assert_sort, elaborate};
use crate::spec::{SpecError, Specification};
use crate::test_utils::{run_with_stack, shared_spec};
use clean_kernel::{Level, Name, TypeChecker};

fn assert_absent(spec: &Specification, name: &str) {
    assert!(!spec.definitions().contains_key(name), "no record {name}");
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_none(),
        "no root {name}"
    );
}

#[test]
fn declaration_input_admission_nine_forged_bodies_are_not_registered() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        let before = spec.definitions().len();
        let (mut prop, mut type_proofs) = (0, 0);
        for &(name, ty_source, body_source) in NEGATIVE_CONTROLS {
            assert_absent(&spec, name);
            let is_prop = name == "dia_false_reuse_position";
            let ty = elaborate(&spec, ty_source);
            let level = if is_prop {
                Level::zero()
            } else {
                Level::succ(Level::zero())
            };
            assert_sort(&spec, &ty, level.clone());
            let body = elaborate(&spec, body_source);
            {
                let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
                let actual = checker
                    .infer_type_full(&body)
                    .expect("forged body itself is valid");
                assert_sort(&spec, &actual, level);
                assert!(!checker.is_def_eq(&actual, &ty), "{name}: real mismatch");
            }
            let error = theorem(
                &mut spec,
                name,
                ty_source,
                body_source,
                "Owned false supplied-payload or history/trace body",
            )
            .expect_err("false body must fail");
            let SpecError::TypeError(message) = error else {
                panic!("{name}: expected kernel body mismatch, got {error:?}")
            };
            assert!(
                message.starts_with(&format!("add_decl {name}:")),
                "{message}"
            );
            let lower = message.to_ascii_lowercase();
            assert!(lower.contains("type mismatch"), "{message}");
            for unrelated in [
                "unknown identifier",
                "unknown constant",
                "unknown definition",
                "unresolved metavariable",
            ] {
                assert!(!lower.contains(unrelated), "{message}");
            }
            assert_absent(&spec, name);
            assert_eq!(spec.definitions().len(), before);
            if is_prop {
                prop += 1;
            } else {
                type_proofs += 1;
            }
        }
        assert_eq!((prop, type_proofs), (1, 8));
    });
}

#[test]
fn declaration_input_admission_legacy_judgments_unchanged() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (name, ty, ctors) in [
            ("KEnv", "Type", &["empty", "addConst", "addInductive"][..]),
            ("ConstantExtension", "KEnv -> KEnv -> Type", &["mk"][..]),
            ("InductiveExtension", "KEnv -> KEnv -> Type", &["mk"][..]),
            (
                "KernelAddDeclAccepts",
                "KEnv -> KEnv -> Type",
                &["const_case", "inductive_case"][..],
            ),
            (
                "KernelAddDeclChain",
                "KEnv -> KEnv -> Type",
                &["refl", "step"][..],
            ),
        ] {
            let root = Name::from_string(name);
            let metadata = spec.env().get_inductive(&root).expect("legacy carrier");
            let expected = elaborate(spec, ty);
            let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
            assert!(
                checker.is_def_eq(&metadata.type_, &expected),
                "{name}: legacy type"
            );
            assert_eq!(
                metadata.constructor_names,
                ctors
                    .iter()
                    .map(|c| Name::from_string(&format!("{name}.{c}")))
                    .collect::<Vec<_>>()
            );
        }
    });
}
