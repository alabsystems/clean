// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual registration checks for modeled admission and finite ProdType closing.
//! No general named-environment or executing Rust admission claim is made.

use super::{
    admission, declarations, generic_closing as closing_cohort, prod_admission, return_spine,
    DeclarationInput,
};
use crate::spec::Specification;
use crate::test_utils::{run_with_stack, shared_spec};
use clean_kernel::Name;
use std::collections::HashSet;

mod callers;
mod checks;
mod generic_closing;

struct Cohort {
    label: &'static str,
    declarations: &'static [DeclarationInput],
    proofs: &'static [&'static str],
    data: &'static [&'static str],
    carriers: &'static [&'static str],
    prop_proofs: &'static [&'static str],
    type_proofs: &'static [&'static str],
    negatives: &'static [(&'static str, &'static str, &'static str)],
    counts: (usize, usize, usize, usize, usize),
}

const COHORTS: &[Cohort] = &[
    Cohort {
        label: "admission",
        declarations: admission::DECLARATIONS,
        proofs: admission::PROOF_ROOTS,
        data: admission::DATA_NAMES,
        carriers: admission::INDUCTIVE_NAMES,
        prop_proofs: admission::PROP_PROOF_ROOTS,
        type_proofs: admission::TYPE_PROOF_ROOTS,
        negatives: admission::NEGATIVE_CONTROLS,
        counts: (12, 5, 11, 1, 3),
    },
    Cohort {
        label: "prod_admission",
        declarations: prod_admission::DECLARATIONS,
        proofs: prod_admission::PROOF_ROOTS,
        data: prod_admission::DATA_NAMES,
        carriers: prod_admission::INDUCTIVE_NAMES,
        prop_proofs: prod_admission::PROP_PROOF_ROOTS,
        type_proofs: prod_admission::TYPE_PROOF_ROOTS,
        negatives: prod_admission::NEGATIVE_CONTROLS,
        counts: (28, 25, 14, 14, 3),
    },
    Cohort {
        label: "return_spine",
        declarations: return_spine::DECLARATIONS,
        proofs: return_spine::PROOF_ROOTS,
        data: return_spine::DATA_NAMES,
        carriers: return_spine::INDUCTIVE_NAMES,
        prop_proofs: return_spine::PROP_PROOF_ROOTS,
        type_proofs: return_spine::TYPE_PROOF_ROOTS,
        negatives: return_spine::NEGATIVE_CONTROLS,
        counts: (10, 1, 10, 0, 2),
    },
    Cohort {
        label: "generic_closing",
        declarations: closing_cohort::DECLARATIONS,
        proofs: closing_cohort::PROOF_ROOTS,
        data: closing_cohort::DATA_NAMES,
        carriers: closing_cohort::INDUCTIVE_NAMES,
        prop_proofs: closing_cohort::PROP_PROOF_ROOTS,
        type_proofs: closing_cohort::TYPE_PROOF_ROOTS,
        negatives: closing_cohort::NEGATIVE_CONTROLS,
        counts: (21, 1, 21, 0, 3),
    },
];

// Pin the reviewed Type-valued statements independently of the cohort arrays.
// In particular, Le and arc_admitted_selected_arity are Prop, not Type.
const TYPE_ROOTS: &[&str] = &[
    "ac_nonuniform_environment_refused",
    "rpa_family_typed",
    "rpa_self_typed",
    "rpa_A_typed",
    "rpa_B_typed",
    "rpa_return_typed",
    "rpa_x_domain_typed",
    "rpa_y_domain_typed",
    "rpa_ctor_typed",
    "rpa_fields_bounded",
    "rpa_ctors_typed",
    "rpa_well_formed",
    "rpa_extension",
    "rpa_env_sound",
    "rpa_connected_admission",
];

fn declaration_name(declaration: &DeclarationInput) -> &'static str {
    match declaration {
        DeclarationInput::Proof(name, ..) | DeclarationInput::Data(name, ..) => name,
    }
}

#[test]
fn constructor_return_coherence_exact_partitions_parse() {
    let mut names = HashSet::new();
    let mut ordered = Vec::new();
    let mut all_proofs = Vec::new();
    let mut all_data = Vec::new();
    let mut all_prop = Vec::new();
    let mut all_type = Vec::new();
    for cohort in COHORTS {
        let (mut proofs, mut data) = (Vec::new(), Vec::new());
        for declaration in cohort.declarations {
            let name = declaration_name(declaration);
            match declaration {
                DeclarationInput::Proof(name, ty, body) => {
                    checks::tuple_ast(name, ty, body);
                    proofs.push(*name);
                }
                DeclarationInput::Data(name, ty, body) => {
                    checks::tuple_ast(name, ty, body);
                    data.push(*name);
                }
            }
            assert!(names.insert(name), "duplicate {name}");
            ordered.push(name);
        }
        assert_eq!(proofs, cohort.proofs, "{}: proof order", cohort.label);
        assert_eq!(data, cohort.data, "{}: data order", cohort.label);
        assert!(cohort.carriers.is_empty(), "no new carriers");
        assert_eq!(
            (
                proofs.len(),
                data.len(),
                cohort.prop_proofs.len(),
                cohort.type_proofs.len(),
                cohort.negatives.len()
            ),
            cohort.counts,
            "{}: exact partition",
            cohort.label
        );
        let kind_names = cohort
            .prop_proofs
            .iter()
            .chain(cohort.type_proofs)
            .copied()
            .collect::<Vec<_>>();
        let kind_set = kind_names.iter().copied().collect::<HashSet<_>>();
        assert_eq!(kind_set.len(), kind_names.len(), "disjoint proof kinds");
        assert_eq!(kind_set, proofs.iter().copied().collect::<HashSet<_>>());
        all_proofs.extend(proofs);
        all_data.extend(data);
        all_prop.extend_from_slice(cohort.prop_proofs);
        all_type.extend_from_slice(cohort.type_proofs);
    }
    assert_eq!(
        declarations().map(declaration_name).collect::<Vec<_>>(),
        ordered
    );
    assert_eq!(
        (
            names.len(),
            all_proofs.len(),
            all_data.len(),
            all_prop.len(),
            all_type.len()
        ),
        (103, 71, 32, 56, 15)
    );
    assert_eq!(all_type, TYPE_ROOTS);
    assert!(all_prop.contains(&"arc_admitted_selected_arity"));

    let mut negative_names = Vec::new();
    for &(name, ty, body) in COHORTS.iter().flat_map(|cohort| cohort.negatives) {
        checks::tuple_ast(name, ty, body);
        assert!(names.insert(name), "negative name collision: {name}");
        negative_names.push(name);
    }
    assert_eq!(
        negative_names,
        [
            "ac_reject_bad_return",
            "ac_reject_fake_admission",
            "ac_reject_wrong_slot",
            "rpa_bad_admission_parameter_count",
            "rpa_bad_self_substitution_target",
            "rpa_bad_metadata_field_count",
            "arc_forged_reversed_parameters",
            "arc_forged_constructor_as_family",
            "gcc_forged_wrong_family",
            "gcc_forged_wrong_order",
            "gcc_forged_underflow_endpoint",
        ]
    );
    assert_eq!(names.len(), 114);
}

#[test]
fn constructor_return_coherence_actual_records_recheck() {
    run_with_stack(|| {
        let spec = shared_spec();
        let (mut prop, mut type_proofs, mut data) = (0, 0, 0);
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Proof(name, ty, body) => {
                    let is_prop = !TYPE_ROOTS.contains(name);
                    checks::record(spec, name, ty, body, Some(is_prop));
                    if is_prop {
                        prop += 1;
                    } else {
                        type_proofs += 1;
                    }
                }
                DeclarationInput::Data(name, ty, body) => {
                    checks::record(spec, name, ty, body, None);
                    data += 1;
                }
            }
        }
        assert_eq!((prop, type_proofs, data), (56, 15, 32));
        for name in ["TypingCtxConvIn.proj", "TypingCDPCtxConvIn.proj"] {
            assert_absent(spec, name);
        }
    });
}

fn assert_absent(spec: &Specification, name: &str) {
    assert!(!spec.definitions().contains_key(name), "{name}: no record");
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_none(),
        "{name}: no kernel root"
    );
}

#[test]
fn constructor_return_coherence_forged_evidence_is_not_registered() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        let original_count = spec.definitions().len();
        let mut checked = 0;
        // Preserve the original eight controls; the new cohort has its own
        // three-refusal runtime test in generic_closing.rs.
        for &(name, ty, body) in [
            admission::NEGATIVE_CONTROLS,
            prod_admission::NEGATIVE_CONTROLS,
            return_spine::NEGATIVE_CONTROLS,
        ]
        .into_iter()
        .flatten()
        {
            checks::tuple_ast(name, ty, body);
            assert_absent(&spec, name);
            let error = super::theorem(
                &mut spec,
                name,
                ty,
                body,
                "Actual constructor-return forged evidence",
            )
            .expect_err("well-parsed false endpoint or admission must fail registration");
            checks::type_mismatch(name, error);
            assert_absent(&spec, name);
            assert_eq!(
                spec.definitions().len(),
                original_count,
                "failed registration inserts nothing"
            );
            checked += 1;
        }
        assert_eq!(checked, 8);
    });
}
