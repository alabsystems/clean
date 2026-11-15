// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual registration tests for the additive model typing batch.
//! Model DepPair, new conversion and whole-spine typing are not source admission.

use super::{declarations, domain, generation, instantiation, spine, typing, DeclarationInput};
use crate::spec::Specification;
use crate::test_utils::{run_with_stack, shared_spec};
use clean_kernel::Name;
use clean_parser::{parse_decl, SurfaceDecl};
use std::collections::HashSet;

mod callers;
mod checks;

#[test]
fn projection_typing_explicit_motive_registers_without_expected_type() {
    run_with_stack(|| {
        // No shared_spec/FULL initialization: isolate the production registrar's
        // independently inferred value against three genuinely different types.
        let mut spec = Specification::new_empty();
        assert!(spec.definitions().is_empty());
        for source in [
            "inductive MotiveTag : Type\n| left : MotiveTag\n| right : MotiveTag",
            "inductive MotiveLeft : Type\n| mk : MotiveLeft",
            "inductive MotiveRight : Type\n| mk : MotiveRight",
        ] {
            spec.add_inductive(source, "Small explicit-motive regression carrier")
                .expect("actual carrier registration");
        }
        let family_type = "MotiveTag -> Type";
        let family_body = r"fun (tag : MotiveTag) => match tag with
| MotiveTag.left => MotiveLeft
| MotiveTag.right => MotiveRight";
        spec.add_recursive_def(
            &format!("def MotiveFamily : {family_type} := {family_body}"),
            "Transparent annotated type family for the explicit-motive regression",
        )
        .expect("actual transparent family registration");
        checks::record(&spec, "MotiveFamily", family_type, family_body, None);
        checks::computes(&spec, "MotiveFamily MotiveTag.left", "MotiveLeft");
        checks::computes(&spec, "MotiveFamily MotiveTag.right", "MotiveRight");
        checks::not_def_eq(&spec, "MotiveLeft", "MotiveRight");

        let proof = DeclarationInput::Proof(
            "MotiveExplicit",
            "forall (tag : MotiveTag), MotiveFamily tag",
            r"fun (tag : MotiveTag) => MotiveTag.rec
 (fun (tag0 : MotiveTag) => MotiveFamily tag0)
 MotiveLeft.mk MotiveRight.mk tag",
        );
        let DeclarationInput::Proof(name, ty, body) = proof else {
            panic!("explicit-motive control must use a production proof tuple")
        };
        checks::tuple_ast(name, ty, body);
        super::theorem(
            &mut spec,
            name,
            ty,
            body,
            "Checked explicit dependent motive",
        )
        .expect("production proof registrar accepts the explicit recursor motive");
        checks::record(&spec, name, ty, body, Some(false));
        checks::caller(&spec, "MotiveExplicit MotiveTag.left", "MotiveLeft");
        checks::caller(&spec, "MotiveExplicit MotiveTag.right", "MotiveRight");

        // Every actual carrier/constructor/recursor/family/proof is axiom-free.
        // In particular, both branches have real closed witnesses: no assumed
        // caller typing, desired result, or unrelated FULL declaration is used.
        for root in spec.definitions().keys() {
            let kernel_name = Name::from_string(root);
            let constant = spec.env().get_const(&kernel_name).expect("actual root");
            assert_ne!(constant.kind, clean_kernel::ConstantKind::Axiom, "{root}");
            assert!(spec
                .env()
                .axiom_deps(&kernel_name)
                .expect("root exists")
                .is_empty());
            assert!(spec
                .env()
                .foundational_axiom_deps(&kernel_name)
                .expect("root exists")
                .is_empty());
            assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, root).is_empty());
        }
        assert_absent(&spec, "KExpr");
        let registered_before_refusals = spec.definitions().len();

        let wrong_name = "MotiveWrongReturn";
        let wrong_type = "MotiveFamily MotiveTag.right";
        let wrong_body = "MotiveLeft.mk";
        checks::tuple_ast(wrong_name, wrong_type, wrong_body);
        assert_absent(&spec, wrong_name);
        let error = super::theorem(
            &mut spec,
            wrong_name,
            wrong_type,
            wrong_body,
            "Wrong dependent branch",
        )
        .expect_err("left witness cannot inhabit the right return type");
        match error {
            crate::spec::SpecError::TypeError(message) => assert!(
                message.to_ascii_lowercase().contains("type mismatch"),
                "only the actual type refusal counts: {message}"
            ),
            other => panic!("parser/missing-name/elaboration failure is not the wrong-return control: {other:?}"),
        }
        assert_absent(&spec, wrong_name);

        assert_eq!(spec.definitions().len(), registered_before_refusals);
    });
}

struct Cohort {
    label: &'static str,
    declarations: &'static [DeclarationInput],
    proofs: &'static [&'static str],
    data: &'static [&'static str],
    carriers: &'static [&'static str],
    negatives: &'static [(&'static str, &'static str, &'static str)],
    counts: (usize, usize, usize, usize),
}

const COHORTS: &[Cohort] = &[
    Cohort {
        label: "domain",
        declarations: domain::DECLARATIONS,
        proofs: domain::PROOF_ROOTS,
        data: domain::DATA_NAMES,
        carriers: domain::INDUCTIVE_NAMES,
        negatives: domain::NEGATIVE_CONTROLS,
        counts: (24, 22, 0, 4),
    },
    Cohort {
        label: "typing",
        declarations: typing::DECLARATIONS,
        proofs: typing::PROOF_ROOTS,
        data: typing::DATA_NAMES,
        carriers: typing::INDUCTIVE_NAMES,
        negatives: typing::NEGATIVE_CONTROLS,
        counts: (8, 0, 1, 4),
    },
    Cohort {
        label: "generation",
        declarations: generation::DECLARATIONS,
        proofs: generation::PROOF_ROOTS,
        data: generation::DATA_NAMES,
        carriers: generation::INDUCTIVE_NAMES,
        negatives: generation::NEGATIVE_CONTROLS,
        counts: (12, 4, 3, 3),
    },
    Cohort {
        label: "instantiation",
        declarations: instantiation::DECLARATIONS,
        proofs: instantiation::PROOF_ROOTS,
        data: instantiation::DATA_NAMES,
        carriers: instantiation::INDUCTIVE_NAMES,
        negatives: instantiation::NEGATIVE_CONTROLS,
        counts: (13, 0, 0, 4),
    },
    Cohort {
        label: "spine",
        declarations: spine::DECLARATIONS,
        proofs: spine::PROOF_ROOTS,
        data: spine::DATA_NAMES,
        carriers: spine::INDUCTIVE_NAMES,
        negatives: spine::NEGATIVE_CONTROLS,
        counts: (17, 1, 2, 4),
    },
];

const PROP_ROOTS: &[&str] = &[
    "dp_resolve_run",
    "dp_ctor_lookup",
    "dp_field_domains",
    "dp_raw_spine_run",
    "dp_raw_field1_prefix",
    "dp_selected_field1",
    "dp_select_field0",
    "dp_select_field1",
    "dp_invalid_field_refused",
    "dp_wrong_family_refused",
    "dp_inferred_field1_run",
    "cdp_instantiate_retains_outer_variable",
    "cdp_spine_capture_run",
];

fn declaration_name(declaration: &DeclarationInput) -> String {
    match declaration {
        DeclarationInput::Inductive(source) => {
            let SurfaceDecl::Inductive { name, .. } = parse_decl(source).expect("carrier AST")
            else {
                panic!("expected an inductive declaration")
            };
            checks::carrier_name(&name)
        }
        DeclarationInput::Proof(name, ..) | DeclarationInput::Data(name, ..) => (*name).to_owned(),
    }
}

#[test]
fn projection_typing_exact_partitions_parse() {
    let mut names = HashSet::new();
    let mut ordered = Vec::new();
    let mut proof_names = Vec::new();
    for cohort in COHORTS {
        let (mut proofs, mut data, mut carriers) = (Vec::new(), Vec::new(), Vec::new());
        for declaration in cohort.declarations {
            let name = declaration_name(declaration);
            match declaration {
                DeclarationInput::Inductive(_) => carriers.push(name.clone()),
                DeclarationInput::Proof(name, ty, body) => {
                    checks::tuple_ast(name, ty, body);
                    proofs.push(*name);
                    proof_names.push(*name);
                }
                DeclarationInput::Data(name, ty, body) => {
                    checks::tuple_ast(name, ty, body);
                    data.push(*name);
                }
            }
            assert!(names.insert(name.clone()), "duplicate {name}");
            ordered.push(name);
        }
        assert_eq!(
            (
                proofs.len(),
                data.len(),
                carriers.len(),
                cohort.negatives.len()
            ),
            cohort.counts,
            "{}: exact partition",
            cohort.label
        );
        assert_eq!(proofs, cohort.proofs, "{}: proof order", cohort.label);
        assert_eq!(data, cohort.data, "{}: data order", cohort.label);
        assert_eq!(carriers, cohort.carriers, "{}: real carriers", cohort.label);
    }
    assert_eq!(
        declarations().map(declaration_name).collect::<Vec<_>>(),
        ordered
    );
    assert_eq!(names.len(), 107);
    assert_eq!(proof_names.len(), 74);
    assert_eq!(PROP_ROOTS.len(), 13);
    assert_eq!(PROP_ROOTS.iter().copied().collect::<HashSet<_>>().len(), 13);
    for name in PROP_ROOTS {
        assert!(
            proof_names.contains(name),
            "Prop root must be a proof: {name}"
        );
    }
    let mut negatives = 0;
    for &(name, ty, body) in COHORTS.iter().flat_map(|cohort| cohort.negatives) {
        checks::tuple_ast(name, ty, body);
        assert!(
            names.insert(name.to_owned()),
            "negative name collision: {name}"
        );
        negatives += 1;
    }
    assert_eq!(negatives, 19);
    assert_eq!(names.len(), 126);
    assert!(
        !names.contains("DefEqCDPIn"),
        "reuse the existing conversion carrier"
    );
}

#[test]
fn projection_typing_actual_records_and_carriers_recheck() {
    run_with_stack(|| {
        let spec = shared_spec();
        let (mut prop, mut type_proofs, mut data, mut carriers) = (0, 0, 0, 0);
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => {
                    checks::carrier(spec, source);
                    carriers += 1;
                }
                DeclarationInput::Proof(name, ty, body) => {
                    let is_prop = PROP_ROOTS.contains(name);
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
        assert_eq!((prop, type_proofs, data, carriers), (13, 61, 27, 6));
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
fn projection_typing_forged_evidence_is_not_registered() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        let mut checked = 0;
        for &(name, ty, body) in COHORTS.iter().flat_map(|cohort| cohort.negatives) {
            checks::tuple_ast(name, ty, body);
            assert_absent(&spec, name);
            let error = super::theorem(&mut spec, name, ty, body, "Actual negative proof control")
                .expect_err("well-parsed wrong proof must fail actual registration");
            assert!(
                format!("{error:?}")
                    .to_ascii_lowercase()
                    .contains("type mismatch"),
                "{name}: parsing or missing names cannot count as refusal: {error:?}"
            );
            assert_absent(&spec, name);
            checked += 1;
        }
        assert_eq!(checked, 19);
    });
}
