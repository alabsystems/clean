// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual registration controls, not a source-execution or admission certificate.

use super::{declarations, evidence, guard, DeclarationInput};
use crate::spec::Specification;
use crate::test_utils::{run_with_stack, shared_spec};
use clean_kernel::Name;
use clean_parser::{parse_decl, SurfaceDecl};
use std::collections::HashSet;

mod callers;
mod checks;

struct Cohort {
    declarations: &'static [DeclarationInput],
    proofs: &'static [&'static str],
    data: &'static [&'static str],
    carriers: &'static [&'static str],
    prop: &'static [&'static str],
    nonprop: &'static [&'static str],
    negatives: &'static [(&'static str, &'static str, &'static str)],
    counts: (usize, usize, usize, usize, usize, usize),
}

const COHORTS: &[Cohort] = &[
    Cohort {
        declarations: guard::DECLARATIONS,
        proofs: guard::PROOF_ROOTS,
        data: guard::DATA_NAMES,
        carriers: guard::INDUCTIVE_NAMES,
        prop: guard::PROP_PROOF_ROOTS,
        nonprop: guard::TYPE_PROOF_ROOTS,
        negatives: guard::NEGATIVE_CONTROLS,
        counts: (19, 11, 1, 16, 3, 0),
    },
    Cohort {
        declarations: evidence::DECLARATIONS,
        proofs: evidence::PROOF_ROOTS,
        data: evidence::DATA_NAMES,
        carriers: evidence::INDUCTIVE_NAMES,
        prop: evidence::PROP_PROOF_ROOTS,
        nonprop: evidence::TYPE_PROOF_ROOTS,
        negatives: evidence::NEGATIVE_CONTROLS,
        counts: (65, 7, 0, 62, 3, 11),
    },
];

const TYPE_ROOTS: &[&str] = &[
    "nig_args_sound",
    "nig_strict_sound",
    "nig_strict_decompose",
    "nig_eq_actual_facts",
    "nig_eq_actual_decomposition",
    "nig_eq_connected_stored_context",
];

fn declaration_name(declaration: &DeclarationInput) -> String {
    match declaration {
        DeclarationInput::Inductive(source) => {
            let SurfaceDecl::Inductive { name, ctors, .. } =
                parse_decl(source).expect("real carrier AST")
            else {
                panic!("expected inductive source");
            };
            assert_eq!(
                name,
                clean_parser::parse_name("NamedStrictAppFacts").expect("explicit carrier name")
            );
            assert_eq!(
                ctors
                    .iter()
                    .map(|ctor| ctor.name.clone())
                    .collect::<Vec<_>>(),
                [clean_parser::parse_name("mk").expect("explicit constructor name")]
            );
            checks::carrier_name(&name)
        }
        DeclarationInput::Proof(name, ..) | DeclarationInput::Data(name, ..) => (*name).to_owned(),
    }
}

#[test]
fn named_indexed_guard_exact_partitions_parse() {
    let mut ordered = Vec::new();
    let mut names = HashSet::new();
    let mut nonprop = Vec::new();
    let (mut proof_count, mut data_count, mut carrier_count, mut prop_count) = (0, 0, 0, 0);
    for cohort in COHORTS {
        let (mut proofs, mut data, mut carriers) = (Vec::new(), Vec::new(), Vec::new());
        for declaration in cohort.declarations {
            let name = declaration_name(declaration);
            match declaration {
                DeclarationInput::Inductive(_) => carriers.push(name.clone()),
                DeclarationInput::Proof(name, ty, body) => {
                    checks::tuple_ast(name, ty, body);
                    proofs.push(*name);
                }
                DeclarationInput::Data(name, ty, body) => {
                    checks::tuple_ast(name, ty, body);
                    data.push(*name);
                }
            }
            assert!(names.insert(name.clone()), "unique declaration {name}");
            ordered.push(name);
        }
        assert_eq!(proofs, cohort.proofs);
        assert_eq!(data, cohort.data);
        assert_eq!(carriers, cohort.carriers);
        assert_eq!(
            (
                proofs.len(),
                data.len(),
                carriers.len(),
                cohort.prop.len(),
                cohort.nonprop.len(),
                cohort.negatives.len()
            ),
            cohort.counts
        );
        let kind_names: Vec<_> = cohort.prop.iter().chain(cohort.nonprop).copied().collect();
        let kind_set: HashSet<_> = kind_names.iter().copied().collect();
        assert_eq!(kind_set.len(), kind_names.len(), "disjoint kind partitions");
        assert_eq!(kind_set, proofs.iter().copied().collect());
        proof_count += proofs.len();
        data_count += data.len();
        carrier_count += carriers.len();
        prop_count += cohort.prop.len();
        nonprop.extend_from_slice(cohort.nonprop);
    }
    assert_eq!(
        declarations().map(declaration_name).collect::<Vec<_>>(),
        ordered
    );
    assert_eq!(
        (
            names.len(),
            proof_count,
            data_count,
            carrier_count,
            prop_count,
            nonprop.len()
        ),
        (103, 84, 18, 1, 78, 6)
    );
    assert_eq!(nonprop, TYPE_ROOTS);
    assert_eq!(
        ordered.last().map(String::as_str),
        Some("nig_eq_connected_stored_context")
    );
    let mut negatives = Vec::new();
    for &(name, ty, body) in COHORTS.iter().flat_map(|cohort| cohort.negatives) {
        checks::tuple_ast(name, ty, body);
        assert!(names.insert(name.to_owned()), "negative name is fresh");
        negatives.push(name);
    }
    assert_eq!(
        negatives,
        [
            "nig_forged_wrong_family",
            "nig_forged_missing_index",
            "nig_forged_wrong_levels",
            "nig_forged_mutual_projection_subject",
            "nig_forged_prefix_underflow",
            "nig_forged_eq_zero_indices",
            "nig_forged_swapped_eq_parameters",
            "nig_forged_same_length_level_name",
            "nig_forged_captured_empty_block",
            "nig_forged_constructor_as_parent",
            "nig_forged_zero_extracted_domains",
        ]
    );
    assert_eq!(names.len(), 114);
}

#[test]
fn named_indexed_guard_actual_records_and_carrier_recheck() {
    run_with_stack(|| {
        let spec = shared_spec();
        let (mut prop, mut nonprop, mut data, mut carriers) = (0, 0, 0, 0);
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => {
                    checks::carrier(spec, source);
                    carriers += 1;
                }
                DeclarationInput::Proof(name, ty, body) => {
                    let is_prop = !TYPE_ROOTS.contains(name);
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
        assert_eq!((prop, nonprop, data, carriers), (78, 6, 18, 1));
    });
}

fn assert_absent(spec: &Specification, name: &str) {
    assert!(!spec.definitions().contains_key(name), "{name}: no record");
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_none(),
        "{name}: no kernel constant"
    );
}

#[test]
fn named_indexed_guard_forged_evidence_is_not_registered() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        let before = spec.definitions().len();
        let mut count = 0;
        for &(name, ty, body) in COHORTS.iter().flat_map(|cohort| cohort.negatives) {
            checks::tuple_ast(name, ty, body);
            assert_absent(&spec, name);
            let error = super::theorem(&mut spec, name, ty, body, "Actual false-endpoint control")
                .expect_err("well-parsed wrong evidence must fail checked registration");
            checks::type_mismatch(name, error);
            assert_absent(&spec, name);
            assert_eq!(
                spec.definitions().len(),
                before,
                "no record inserted by refusal"
            );
            count += 1;
        }
        assert_eq!(count, 11);
    });
}

#[test]
fn named_indexed_guard_old_judgments_are_unchanged() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (name, expected) in [
            (
                "DefEqIn",
                &[
                    "refl", "symm", "trans", "raw", "levels", "app", "lam", "pi", "let_", "proj",
                ][..],
            ),
            (
                "TypingCtxConvIn",
                &[
                    "var",
                    "sort",
                    "pi",
                    "lam",
                    "app",
                    "const",
                    "conv",
                    "let_",
                    "lit_nat",
                    "lit_string",
                ][..],
            ),
            (
                "KernelInfersIn",
                &[
                    "sort",
                    "bvar",
                    "pi",
                    "lam",
                    "const",
                    "app",
                    "let_",
                    "lit_nat",
                    "lit_string",
                ][..],
            ),
        ] {
            let metadata = spec
                .env()
                .get_inductive(&Name::from_string(name))
                .expect("existing judgment");
            let names = expected
                .iter()
                .map(|ctor| Name::from_string(&format!("{name}.{ctor}")))
                .collect::<Vec<_>>();
            assert_eq!(metadata.constructor_names, names, "no acceptance migration");
        }
        assert!(spec
            .env()
            .get_constructor(&Name::from_string("TypingCtxConvIn.proj"))
            .is_none());
        assert!(spec
            .env()
            .get_constructor(&Name::from_string("KernelInfersIn.proj"))
            .is_none());
    });
}
