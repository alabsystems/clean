// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{declarations, records, DeclarationInput};
use crate::spec::Specification;
use crate::test_utils::{run_with_stack, shared_spec};
use clean_kernel::Name;
use std::collections::HashSet;

mod callers;
mod checks;

#[test]
fn ind_ctor_table_exact_partitions_parse() {
    let mut proofs = Vec::new();
    let mut data = Vec::new();
    let mut names = HashSet::new();
    for declaration in declarations() {
        let (name, ty, body) = match declaration {
            DeclarationInput::Proof(name, ty, body) => {
                proofs.push(*name);
                (name, ty, body)
            }
            DeclarationInput::Data(name, ty, body) => {
                data.push(*name);
                (name, ty, body)
            }
        };
        checks::tuple_ast(name, ty, body);
        assert!(names.insert(*name), "unique declaration {name}");
    }
    assert_eq!(proofs, records::PROOF_ROOTS);
    assert_eq!(proofs, records::PROP_PROOF_ROOTS);
    assert_eq!(data, records::DATA_NAMES);
    assert!(records::TYPE_PROOF_ROOTS.is_empty(), "all proofs are Prop");
    assert!(records::INDUCTIVE_NAMES.is_empty(), "no new carriers");
    assert_eq!((names.len(), proofs.len(), data.len()), (22, 19, 3));
    assert_eq!(data, ["ict_append", "ict_has_name_b", "ict_eq_updates"]);
    let mut negatives = Vec::new();
    for &(name, ty, body) in records::NEGATIVE_CONTROLS {
        checks::tuple_ast(name, ty, body);
        assert!(names.insert(name), "fresh refusal {name}");
        negatives.push(name);
    }
    assert_eq!(
        negatives,
        [
            "ict_false_cross_kind_survives",
            "ict_false_other_without_inequality",
            "ict_false_append_order",
            "ict_false_cross_kind_is_fresh",
        ]
    );
    assert_eq!(names.len(), 26);
}

#[test]
fn ind_ctor_table_actual_records_recheck() {
    run_with_stack(|| {
        let spec = shared_spec();
        let (mut proofs, mut data) = (0, 0);
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Proof(name, ty, body) => {
                    assert!(records::PROP_PROOF_ROOTS.contains(name));
                    checks::record(spec, name, ty, body, Some(true));
                    proofs += 1;
                }
                DeclarationInput::Data(name, ty, body) => {
                    checks::record(spec, name, ty, body, None);
                    data += 1;
                }
            }
        }
        assert_eq!((proofs, data), (19, 3));
    });
}

fn assert_absent(spec: &Specification, name: &str) {
    assert!(!spec.definitions().contains_key(name), "no record {name}");
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_none(),
        "no kernel root {name}"
    );
}

#[test]
fn ind_ctor_table_four_forged_bodies_are_not_registered() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        let before = spec.definitions().len();
        for &(name, ty, body) in records::NEGATIVE_CONTROLS {
            assert_absent(&spec, name);
            let error = super::theorem(
                &mut spec,
                name,
                ty,
                body,
                "False lookup/freshness body, not a parser or missing-name control",
            )
            .expect_err("wrong proof body must be rejected");
            checks::type_mismatch(name, error);
            assert_absent(&spec, name);
            assert_eq!(spec.definitions().len(), before);
        }
        assert_eq!(records::NEGATIVE_CONTROLS.len(), 4);
    });
}
