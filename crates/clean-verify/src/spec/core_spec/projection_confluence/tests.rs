// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual registration checks; independent replay is a separate full-corpus gate.

use super::{
    cdp_bindings, composition, declarations, iota, mixed_roots, mixed_strong, projection_only,
    relation_union, union_sandwich, DeclarationInput,
};
use crate::spec::Specification;
use crate::test_utils::{run_with_stack, shared_spec};
use clean_kernel::Name;
use clean_parser::{parse_decl, SurfaceDecl};
use std::collections::HashSet;

mod checks;

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
        label: "relation_union",
        declarations: relation_union::DECLARATIONS,
        proofs: relation_union::PROOF_ROOTS,
        data: relation_union::DATA_NAMES,
        carriers: relation_union::INDUCTIVE_NAMES,
        negatives: relation_union::NEGATIVE_CONTROLS,
        counts: (14, 0, 3, 1),
    },
    Cohort {
        label: "cdp_bindings",
        declarations: cdp_bindings::DECLARATIONS,
        proofs: cdp_bindings::PROOF_ROOTS,
        data: cdp_bindings::DATA_NAMES,
        carriers: cdp_bindings::INDUCTIVE_NAMES,
        negatives: cdp_bindings::NEGATIVE_CONTROLS,
        counts: (24, 1, 1, 3),
    },
    Cohort {
        label: "projection_only",
        declarations: projection_only::DECLARATIONS,
        proofs: projection_only::PROOF_ROOTS,
        data: projection_only::DATA_NAMES,
        carriers: projection_only::INDUCTIVE_NAMES,
        negatives: projection_only::NEGATIVE_CONTROLS,
        counts: (43, 4, 7, 4),
    },
    Cohort {
        label: "mixed_roots",
        declarations: mixed_roots::DECLARATIONS,
        proofs: mixed_roots::PROOF_ROOTS,
        data: mixed_roots::DATA_NAMES,
        carriers: mixed_roots::INDUCTIVE_NAMES,
        negatives: mixed_roots::NEGATIVE_CONTROLS,
        counts: (52, 6, 1, 5),
    },
    Cohort {
        label: "iota",
        declarations: iota::DECLARATIONS,
        proofs: iota::PROOF_ROOTS,
        data: iota::DATA_NAMES,
        carriers: iota::INDUCTIVE_NAMES,
        negatives: iota::NEGATIVE_CONTROLS,
        counts: (38, 25, 0, 6),
    },
    Cohort {
        label: "mixed_strong",
        declarations: mixed_strong::DECLARATIONS,
        proofs: mixed_strong::PROOF_ROOTS,
        data: mixed_strong::DATA_NAMES,
        carriers: mixed_strong::INDUCTIVE_NAMES,
        negatives: mixed_strong::NEGATIVE_CONTROLS,
        counts: (18, 0, 0, 4),
    },
    Cohort {
        label: "union_sandwich",
        declarations: union_sandwich::DECLARATIONS,
        proofs: union_sandwich::PROOF_ROOTS,
        data: union_sandwich::DATA_NAMES,
        carriers: union_sandwich::INDUCTIVE_NAMES,
        negatives: union_sandwich::NEGATIVE_CONTROLS,
        counts: (20, 3, 0, 2),
    },
    Cohort {
        label: "composition",
        declarations: composition::DECLARATIONS,
        proofs: composition::PROOF_ROOTS,
        data: composition::DATA_NAMES,
        carriers: composition::INDUCTIVE_NAMES,
        negatives: composition::NEGATIVE_CONTROLS,
        counts: (15, 0, 0, 2),
    },
];

#[test]
fn projection_confluence_generic_core_registers_without_full_spec() {
    run_with_stack(|| {
        let mut spec = Specification {
            env: clean_kernel::Environment::new(),
            definitions: std::collections::HashMap::new(),
            red_env_script_override: None,
            red_env_interning_override: None,
            model_unit_source: crate::spec::ModelUnitSource::default(),
        };
        for declaration in relation_union::DECLARATIONS {
            match declaration {
                DeclarationInput::Inductive(source) => spec
                    .add_inductive(source, "Generic relation carrier in an empty environment")
                    .expect("actual generic carrier"),
                DeclarationInput::Proof(name, ty, body) => {
                    super::theorem(&mut spec, name, ty, body, "Generic relation proof")
                        .unwrap_or_else(|error| panic!("{name}: {error:?}"));
                    checks::record(&spec, name, ty, body, true);
                }
                DeclarationInput::Data(..) => panic!("generic core has no data records"),
            }
        }
        for declaration in relation_union::DECLARATIONS {
            if let DeclarationInput::Inductive(source) = declaration {
                checks::carrier(&spec, source);
            }
        }
    });
}

#[test]
fn projection_confluence_exact_partitions_parse() {
    let mut names = HashSet::new();
    let mut ordered = Vec::new();
    for cohort in COHORTS {
        let mut proofs = Vec::new();
        let mut data = Vec::new();
        let mut carriers = Vec::new();
        for declaration in cohort.declarations {
            let name = match declaration {
                DeclarationInput::Inductive(source) => {
                    let SurfaceDecl::Inductive { name, .. } =
                        parse_decl(source).expect("actual inductive syntax")
                    else {
                        panic!("expected a carrier declaration")
                    };
                    carriers.push(name.qualify_under(&Default::default()).into_name());
                    name.qualify_under(&Default::default()).into_name()
                }
                DeclarationInput::Proof(name, ty, body) => {
                    checks::tuple_ast(name, ty, body);
                    proofs.push(*name);
                    clean_parser::parse_name(name)
                        .expect("explicit source name")
                        .qualify_under(&Default::default())
                        .into_name()
                }
                DeclarationInput::Data(name, ty, body) => {
                    checks::tuple_ast(name, ty, body);
                    data.push(*name);
                    clean_parser::parse_name(name)
                        .expect("explicit source name")
                        .qualify_under(&Default::default())
                        .into_name()
                }
            };
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
        assert_eq!(data, cohort.data, "{}: transparent data", cohort.label);
        assert_eq!(
            carriers,
            cohort
                .carriers
                .iter()
                .map(|n| clean_parser::parse_name(n)
                    .expect("explicit source name")
                    .qualify_under(&Default::default())
                    .into_name())
                .collect::<Vec<_>>(),
            "{}: real carriers",
            cohort.label
        );
    }
    let actual_order: Vec<_> = declarations()
        .map(|declaration| match declaration {
            DeclarationInput::Inductive(source) => {
                let SurfaceDecl::Inductive { name, .. } = parse_decl(source).expect("carrier")
                else {
                    panic!("carrier")
                };
                name.qualify_under(&Default::default()).into_name()
            }
            DeclarationInput::Proof(name, ..) | DeclarationInput::Data(name, ..) => {
                clean_parser::parse_name(name)
                    .expect("explicit source name")
                    .qualify_under(&Default::default())
                    .into_name()
            }
        })
        .collect();
    assert_eq!(
        actual_order, ordered,
        "actual registration order is cohort order"
    );
    assert_eq!(names.len(), 275);
    for &(name, ty, body) in COHORTS.iter().flat_map(|cohort| cohort.negatives) {
        checks::tuple_ast(name, ty, body);
        assert!(
            names.insert(
                clean_parser::parse_name(name)
                    .expect("explicit source name")
                    .qualify_under(&Default::default())
                    .into_name()
            ),
            "negative name collision"
        );
    }
}

#[test]
fn projection_confluence_actual_records_and_carriers_recheck() {
    run_with_stack(|| {
        let spec = shared_spec();
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => checks::carrier(spec, source),
                DeclarationInput::Proof(name, ty, body) => {
                    checks::record(spec, name, ty, body, true)
                }
                DeclarationInput::Data(name, ty, body) => {
                    checks::record(spec, name, ty, body, false)
                }
            }
        }
    });
}

#[test]
fn projection_confluence_forged_evidence_is_not_registered() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        for &(name, ty, body) in COHORTS.iter().flat_map(|cohort| cohort.negatives) {
            checks::tuple_ast(name, ty, body);
            assert_absent(&spec, name);
            let error = super::theorem(
                &mut spec,
                name,
                ty,
                body,
                "Negative control: wrong relation color or endpoint is not evidence.",
            )
            .expect_err("well-parsed wrong proof must be refused by actual registration");
            assert!(
                format!("{error:?}")
                    .to_ascii_lowercase()
                    .contains("type mismatch"),
                "{name}: parsing/missing names do not count: {error:?}"
            );
            assert_absent(&spec, name);
        }
    });
}

fn assert_absent(spec: &Specification, name: &str) {
    assert!(!spec.definitions().contains_key(name), "{name}: no record");
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_none(),
        "{name}: no kernel declaration"
    );
}

#[test]
fn projection_confluence_connected_callers_and_computation() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (source, expected) in [
            ("cdp_binding_projection", "KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject"),
            ("projection_post_whnf_reduct the_red_env cdp_binding_projection", "OptionType.some KExpr projection_binding_field"),
            ("instantiate projection_binding_field (KExpr.bvar (Nat.succ Nat.zero))", "KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))"),
            ("cdp_union_mixed_source", "KExpr.app (KExpr.lam rfnz_nat cdp_binding_projection) (KExpr.bvar (Nat.succ Nat.zero))"),
            ("cdp_union_mixed_middle", "KExpr.app (KExpr.lam rfnz_nat projection_binding_field) (KExpr.bvar (Nat.succ Nat.zero))"),
        ] {
            checks::computes(spec, source, expected);
        }
        for (source, expected_type) in [
            ("par_cdp_to_star the_red_env cdp_prod_inner_projection rfnz_zero cdp_prod_inner_step", "par_reduces_cdp_star the_red_env cdp_prod_inner_projection rfnz_zero"),
            ("cdp_union_mixed_to_cdp_star", "par_reduces_cdp_star the_red_env cdp_union_mixed_source (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))"),
            ("cdp_union_mixed_roundtrip", "cd_projection_union_star the_red_env cdp_union_mixed_source (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))"),
            ("cdp_confluence_prod_join", "RelationJoin KExpr (par_reduces_cdp_star the_red_env) (par_reduces_cdp_star the_red_env) (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex"),
            ("cdp_confluence_prod_explicit_meet", "RelationJoin KExpr (par_reduces_cdp_star the_red_env) (par_reduces_cdp_star the_red_env) (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex"),
            ("cd_projection_strong_actual_extract", "CDProjectionPeak the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex"),
        ] {
            checks::caller(spec, source, expected_type);
        }
    });
}
