// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::clone_on_copy,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_original_index_domains_and_v8_bytes_match_all_optional_blocks() {
    let (m, row, b) = fixture();
    for formula in [false, true] {
        for spec in [false, true] {
            for binds in [false, true] {
                let mut r = row.clone();
                if !formula {
                    r.formula = None;
                } else if !binds {
                    r.formula.as_mut().unwrap().bindings.clear();
                }
                if !spec {
                    r.spec = None;
                }
                exact(&m, &r, Some(&b));
            }
        }
    }
}
#[test]
fn every_obligation_kind_including_full_custom_strings_has_exact_original_tag() {
    let (m, row, b) = fixture();
    for kind in [
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::LoopInvariant,
        ObligationKind::TypeInvariant,
        ObligationKind::RefinementType,
        ObligationKind::TranslationValidation,
        ObligationKind::MemorySafety,
        ObligationKind::PanicFreedom,
        ObligationKind::TemporalSafety,
        ObligationKind::Liveness,
        ObligationKind::ArithmeticSafety,
        ObligationKind::BoundsCheck,
        ObligationKind::GiveBackRefinement,
        ObligationKind::Termination,
        ObligationKind::Ownership,
        ObligationKind::Custom {
            namespace: "n\0é".repeat(50),
            name: "name".into(),
        },
    ] {
        let mut r = row.clone();
        r.kind = kind;
        exact(&m, &r, Some(&b));
    }
}
#[test]
fn all_clause_sort_and_place_carriers_preserve_raw_order_widths_and_malformed_names() {
    let (m, row, b) = fixture();
    let sorts = vec![
        ClauseSort::Bool,
        ClauseSort::Int,
        ClauseSort::BitVec(0),
        ClauseSort::BitVec(u32::MAX),
        ClauseSort::Array(Box::new(ClauseSort::Bool), Box::new(ClauseSort::Int)),
        ClauseSort::Float {
            eb: 0,
            sb: u32::MAX,
        },
        ClauseSort::RoundingMode,
        ClauseSort::Datatype {
            name: "D\0".into(),
            constructors: vec![
                ("c".into(), vec![("f".into(), ClauseSort::Int)]),
                ("c".into(), vec![]),
            ],
        },
    ];
    let places = vec![
        ClausePlace::Param { index: 0 },
        ClausePlace::ResultSlot { index: 1 },
        ClausePlace::MutParamExit { index: 2 },
        ClausePlace::World,
        ClausePlace::Unwind,
        ClausePlace::Value(ValueId::new(9)),
        ClausePlace::SpecVar { index: 8 },
        ClausePlace::SpecVarNext { index: 7 },
        ClausePlace::WorldPre,
        ClausePlace::WorldPost,
        ClausePlace::ParamPointeeEntry { index: u32::MAX },
    ];
    for sort in sorts {
        for place in &places {
            let mut r = row.clone();
            r.formula.as_mut().unwrap().bindings = vec![(
                "x".into(),
                ClauseBinding {
                    sort: sort.clone(),
                    place: place.clone(),
                },
            )];
            exact(&m, &r, Some(&b));
        }
    }
}
#[test]
fn nested_datatype_arrays_keep_full_stored_field_and_constructor_order_without_recursion() {
    let (m, mut row, b) = fixture();
    let mut sort = ClauseSort::Int;
    for n in 0..64 {
        sort = ClauseSort::Datatype {
            name: format!("D{n}"),
            constructors: vec![(
                "c".into(),
                vec![
                    ("a".into(), ClauseSort::Bool),
                    (
                        "b".into(),
                        ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(sort)),
                    ),
                ],
            )],
        };
    }
    row.formula.as_mut().unwrap().bindings = vec![(
        "x".into(),
        ClauseBinding {
            sort,
            place: ClausePlace::World,
        },
    )];
    exact(&m, &row, Some(&b));
}
#[test]
fn v8_names_ignore_renumbering_but_index_identity_moves_and_duplicate_ids_are_unkeyed() {
    let (mut m, mut row, b) = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let old = original_v8(&row, &c, Some(&b));
    let indexed = super::super::super::super::clean_cic_lineage_digest(&row);
    drop(c);
    m.functions[0].id = FuncId::new(3);
    row.id = ProofId::new(5);
    row.function = Some(FuncId::new(3));
    row.site.as_mut().unwrap().function = FuncId::new(3);
    assert_eq!(
        original_v8(&row, &ModuleFunctionCatalog::new(&m), Some(&b)),
        old
    );
    assert_ne!(
        super::super::super::super::clean_cic_lineage_digest(&row),
        indexed
    );
    exact(&m, &row, Some(&b));
    let f = m.functions[0].clone();
    m.functions.push(f);
    assert!(original_content(&row, &ModuleFunctionCatalog::new(&m)).is_none());
    exact(&m, &row, Some(&b));
}
#[test]
fn missing_owner_or_site_symbols_return_original_none_without_smaller_content() {
    let (m, row, b) = fixture();
    for owner in [false, true] {
        let mut r = row.clone();
        if owner {
            r.function = Some(FuncId::new(999));
        } else {
            r.site.as_mut().unwrap().function = FuncId::new(999);
        }
        assert!(original_content(&r, &ModuleFunctionCatalog::new(&m)).is_none());
        exact(&m, &r, Some(&b));
    }
}
#[test]
fn status_is_excluded_but_full_source_site_spec_and_bound_metadata_are_identity() {
    let (m, row, b) = fixture();
    let original = super::super::super::super::clean_cic_lineage_digest(&row);
    for status in [
        ProofStatus::Pending,
        ProofStatus::Discharged,
        ProofStatus::Trusted,
        ProofStatus::Failed,
    ] {
        let mut r = row.clone();
        r.status = status;
        assert_eq!(
            super::super::super::super::clean_cic_lineage_digest(&r),
            original
        );
        exact(&m, &r, Some(&b));
    }
    let mut r = row.clone();
    r.source
        .as_mut()
        .unwrap()
        .public
        .as_mut()
        .unwrap()
        .obligation_id
        .push('x');
    assert_ne!(
        super::super::super::super::clean_cic_lineage_digest(&r),
        original
    );
    exact(&m, &r, Some(&b));
}
#[test]
fn binds_and_is_v8_match_original_without_claiming_term_or_status_authority() {
    let (m, row, b) = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    for lineage in [
        super::super::super::super::clean_cic_lineage_digest(&row),
        original_v8(&row, &c, Some(&b)).unwrap(),
        ProofDigest::sha256([99; 32]),
    ] {
        let e = ProofEvidence::CleanCic {
            term: vec![],
            context: vec![],
            lineage,
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "unknown".into(),
                theorems: vec![],
                anchor: "unknown".into(),
                allowed_axioms: vec![],
                binding: Some(Box::new(b.clone())),
            }),
        };
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            e.clean_cic_lineage_binds_observed(&row, &c, &mut s, site())
                .unwrap(),
            super::super::super::super::clean_cic_lineage_binds(&row, &e, &|id| c
                .unique(id)
                .map(|f| f.name.clone()))
        );
        assert_eq!(
            e.clean_cic_lineage_is_v8_observed(&row, &c, &mut s, site())
                .unwrap(),
            super::super::super::super::clean_cic_lineage_is_v8(&row, &e, &|id| c
                .unique(id)
                .map(|f| f.name.clone()))
        );
    }
}
