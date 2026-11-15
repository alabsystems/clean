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
fn named_block_return_exact_partitions_parse() {
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
    assert_eq!(data, records::DATA_NAMES);
    assert!(records::INDUCTIVE_NAMES.is_empty(), "no new carriers");
    assert_eq!((names.len(), proofs.len(), data.len()), (48, 15, 33));
    assert_eq!(records::PROP_PROOF_ROOTS.len(), 11);
    assert_eq!(
        records::TYPE_PROOF_ROOTS,
        [
            "nrb_option_resolve",
            "nrb_block_walk_select",
            "nrb_selected_constructor",
            "nrb_demo_selected_g",
        ]
    );
    let kinds: Vec<_> = records::PROP_PROOF_ROOTS
        .iter()
        .chain(records::TYPE_PROOF_ROOTS)
        .copied()
        .collect();
    let kind_set: HashSet<_> = kinds.iter().copied().collect();
    assert_eq!(kinds.len(), kind_set.len());
    assert_eq!(kind_set, proofs.iter().copied().collect());
    let mut negatives = Vec::new();
    for &(name, ty, body) in records::NEGATIVE_CONTROLS {
        checks::tuple_ast(name, ty, body);
        assert!(names.insert(name), "fresh refusal {name}");
        negatives.push(name);
    }
    assert_eq!(
        negatives,
        [
            "nrb_false_other_parent_accepts",
            "nrb_false_other_index_accepts",
            "nrb_false_g_index_count_zero",
            "nrb_false_selected_family",
        ]
    );
    assert_eq!(names.len(), 52);
}

#[test]
fn named_block_return_actual_records_recheck() {
    run_with_stack(|| {
        let spec = shared_spec();
        let (mut prop, mut nonprop, mut data) = (0, 0, 0);
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Proof(name, ty, body) => {
                    let is_prop = records::PROP_PROOF_ROOTS.contains(name);
                    assert!(is_prop || records::TYPE_PROOF_ROOTS.contains(name));
                    checks::record(spec, name, ty, body, Some(is_prop));
                    if is_prop {
                        prop += 1;
                    } else {
                        nonprop += 1;
                    }
                }
                DeclarationInput::Data(name, ty, body) => {
                    checks::record(spec, name, ty, body, None);
                    data += 1;
                }
            }
        }
        assert_eq!((prop, nonprop, data), (11, 4, 33));
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
fn named_block_return_four_forged_bodies_are_not_registered() {
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
                "Actual false-endpoint refusal; not missing-name evidence",
            )
            .expect_err("wrong proof body must be rejected");
            checks::type_mismatch(name, error);
            assert_absent(&spec, name);
            assert_eq!(spec.definitions().len(), before);
        }
        assert_eq!(records::NEGATIVE_CONTROLS.len(), 4);
    });
}
