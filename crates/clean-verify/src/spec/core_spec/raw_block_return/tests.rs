// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual FULL registration and refusal checks for the additive raw model.
//! Source admission, Rust refinement, and broader typing are not claimed here.

use super::{declarations, family, raw, whole, DeclarationInput};
use crate::spec::Specification;
use crate::test_utils::{run_with_stack, shared_spec};
use clean_kernel::Name;
use clean_parser::{parse_decl, SurfaceDecl};
use std::collections::HashSet;

mod callers;
mod checks;

struct Cohort {
    label: &'static str,
    declarations: &'static [DeclarationInput],
    proofs: &'static [&'static str],
    prop: &'static [&'static str],
    type_proofs: &'static [&'static str],
    data: &'static [&'static str],
    carriers: &'static [&'static str],
    negatives: &'static [(&'static str, &'static str, &'static str)],
    counts: (usize, usize, usize, usize),
}

const COHORTS: &[Cohort] = &[
    Cohort {
        label: "raw",
        declarations: raw::DECLARATIONS,
        proofs: raw::PROOF_ROOTS,
        prop: raw::PROP_PROOF_ROOTS,
        type_proofs: raw::TYPE_PROOF_ROOTS,
        data: raw::DATA_NAMES,
        carriers: raw::INDUCTIVE_NAMES,
        negatives: raw::NEGATIVE_CONTROLS,
        counts: (37, 0, 23, 2),
    },
    Cohort {
        label: "family",
        declarations: family::DECLARATIONS,
        proofs: family::PROOF_ROOTS,
        prop: family::PROP_PROOF_ROOTS,
        type_proofs: family::TYPE_PROOF_ROOTS,
        data: family::DATA_NAMES,
        carriers: family::INDUCTIVE_NAMES,
        negatives: family::NEGATIVE_CONTROLS,
        counts: (14, 2, 0, 0),
    },
    Cohort {
        label: "whole",
        declarations: whole::DECLARATIONS,
        proofs: whole::PROOF_ROOTS,
        prop: whole::PROP_PROOF_ROOTS,
        type_proofs: whole::TYPE_PROOF_ROOTS,
        data: whole::DATA_NAMES,
        carriers: whole::INDUCTIVE_NAMES,
        negatives: whole::NEGATIVE_CONTROLS,
        counts: (20, 3, 11, 0),
    },
];

fn declaration_name(declaration: &DeclarationInput) -> String {
    match declaration {
        DeclarationInput::Inductive(source) => {
            let SurfaceDecl::Inductive { name, .. } = parse_decl(source).expect("carrier AST")
            else {
                panic!("expected inductive declaration")
            };
            checks::carrier_name(&name)
        }
        DeclarationInput::Proof(name, ..) | DeclarationInput::Data(name, ..) => (*name).to_owned(),
    }
}

#[test]
fn raw_block_return_exact_partitions_parse() {
    let mut names = HashSet::new();
    let mut ordered = Vec::new();
    let mut all_type_proofs = Vec::new();
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
            assert!(names.insert(name.clone()), "duplicate {name}");
            ordered.push(name);
        }
        assert_eq!(proofs, cohort.proofs, "{}: proof order", cohort.label);
        assert_eq!(data, cohort.data, "{}: data order", cohort.label);
        assert_eq!(carriers, cohort.carriers, "{}: carriers", cohort.label);
        assert_eq!(
            (
                cohort.prop.len(),
                cohort.type_proofs.len(),
                data.len(),
                carriers.len()
            ),
            cohort.counts,
            "{}: counts",
            cohort.label
        );
        assert_eq!(
            proofs
                .iter()
                .filter(|name| cohort.prop.contains(name))
                .copied()
                .collect::<Vec<_>>(),
            cohort.prop
        );
        assert_eq!(
            proofs
                .iter()
                .filter(|name| cohort.type_proofs.contains(name))
                .copied()
                .collect::<Vec<_>>(),
            cohort.type_proofs
        );
        let partition = cohort
            .prop
            .iter()
            .chain(cohort.type_proofs)
            .copied()
            .collect::<Vec<_>>();
        let set = partition.iter().copied().collect::<HashSet<_>>();
        assert_eq!(
            set.len(),
            partition.len(),
            "{}: disjoint sorts",
            cohort.label
        );
        assert_eq!(
            set,
            proofs.iter().copied().collect(),
            "{}: exhaustive sorts",
            cohort.label
        );
        all_type_proofs.extend_from_slice(cohort.type_proofs);
        assert_eq!(cohort.negatives.len(), 4);
    }
    assert_eq!(
        declarations().map(declaration_name).collect::<Vec<_>>(),
        ordered
    );
    assert_eq!(names.len(), 112);
    assert_eq!(
        raw::INDUCTIVE_NAMES,
        ["NamedCtorSource", "NamedMemberSource"]
    );
    assert_eq!(
        all_type_proofs,
        [
            "nsi_raw_selected_lookups",
            "nfi_demo_six_equation_consumer",
            "nwr_selected_constructor_from_raw",
            "nwr_selected_strict_facts",
            "nwr_demo_selected_second_ctor"
        ]
    );
    let mut negatives = Vec::new();
    for &(name, ty, body) in COHORTS.iter().flat_map(|cohort| cohort.negatives) {
        checks::tuple_ast(name, ty, body);
        assert!(names.insert(name.to_owned()), "fresh refusal {name}");
        negatives.push(name);
    }
    assert_eq!(
        negatives,
        [
            "nsi_false_selected_parent",
            "nsi_false_selected_index",
            "nsi_false_cross_kind_survives",
            "nsi_false_input_slot",
            "nfi_false_member_index_count",
            "nfi_false_member_block_order",
            "nsi_false_member_position_name",
            "nsi_false_constructor_position_name",
            "nwr_false_empty_accepts",
            "nwr_false_other_member_accepts",
            "nwr_false_installed_outcome",
            "nwr_false_selected_family",
        ]
    );
    assert_eq!(names.len(), 124);
}

#[test]
fn raw_block_return_actual_records_and_carriers_recheck() {
    run_with_stack(|| {
        let spec = shared_spec();
        let (mut prop, mut type_proofs, mut data, mut carriers) = (0, 0, 0, 0);
        for cohort in COHORTS {
            for declaration in cohort.declarations {
                match declaration {
                    DeclarationInput::Inductive(source) => {
                        checks::carrier(spec, source);
                        carriers += 1;
                    }
                    DeclarationInput::Proof(name, ty, body) => {
                        let is_prop = cohort.prop.contains(name);
                        assert!(is_prop || cohort.type_proofs.contains(name));
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
        }
        assert_eq!((prop, type_proofs, data, carriers), (71, 5, 34, 2));
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
fn raw_block_return_twelve_forged_bodies_are_not_registered() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        let before = spec.definitions().len();
        let (mut prop, mut type_proofs) = (0, 0);
        for &(name, ty, body) in COHORTS.iter().flat_map(|cohort| cohort.negatives) {
            let is_prop = name != "nwr_false_selected_family";
            checks::statement_sort(&spec, ty, is_prop);
            assert_absent(&spec, name);
            let error = super::theorem(
                &mut spec,
                name,
                ty,
                body,
                "Actual forged raw-block endpoint; not a parser or missing-name control",
            )
            .expect_err("wrong proof body must be rejected");
            checks::type_mismatch(name, error);
            assert_absent(&spec, name);
            assert_eq!(spec.definitions().len(), before);
            if is_prop {
                prop += 1;
            } else {
                type_proofs += 1;
            }
        }
        assert_eq!((prop, type_proofs), (11, 1));
    });
}

#[test]
fn raw_block_return_preserves_original_acceptance_constructors() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (carrier, ctors) in [
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
            let root = Name::from_string(carrier);
            let metadata = spec
                .env()
                .get_inductive(&root)
                .expect("old acceptance carrier");
            let names = ctors
                .iter()
                .map(|ctor| Name::from_string(&format!("{carrier}.{ctor}")))
                .collect::<Vec<_>>();
            assert_eq!(
                metadata.constructor_names, names,
                "{carrier}: no acceptance migration"
            );
        }
    });
}
