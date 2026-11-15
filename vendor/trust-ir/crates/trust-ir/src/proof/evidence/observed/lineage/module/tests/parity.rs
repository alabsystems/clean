// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn complete_sparse_module_resolver_digest_and_both_predicates_match_original() {
    let (m, row, b) = fixture();
    let d = observed(&m, &row, Some(&b)).0.unwrap();
    assert_eq!(
        exact_evidence(&m, &row, &evidence(d, Some(b))),
        (true, true)
    );
}
#[test]
fn indexed_id_match_takes_precedence_over_an_earlier_duplicate_fallback() {
    let (mut m, mut row, b) = fixture();
    m.functions = vec![function(1, "earlier"), function(1, "indexed")];
    row.function = Some(FuncId::new(1));
    row.site = None;
    assert_eq!(m.function_by_id(FuncId::new(1)).unwrap().name, "indexed");
    let d = observed(&m, &row, Some(&b)).0;
    m.functions[0].name = "changed ignored fallback".into();
    assert_eq!(observed(&m, &row, Some(&b)).0, d);
    m.functions[1].name = "changed indexed".into();
    assert_ne!(observed(&m, &row, Some(&b)).0, d);
}
#[test]
fn off_index_lookup_returns_first_physical_duplicate_not_last_or_unique() {
    let (mut m, row, b) = fixture();
    m.functions = vec![function(77, "FIRST"), function(77, "LAST")];
    let d = observed(&m, &row, Some(&b)).0;
    m.functions[1].name = "ignored last".into();
    assert_eq!(observed(&m, &row, Some(&b)).0, d);
    m.functions.swap(0, 1);
    assert_ne!(observed(&m, &row, Some(&b)).0, d);
}
#[test]
fn unresolved_owner_or_sited_function_returns_exact_semantic_none() {
    let (mut m, row, b) = fixture();
    m.functions.clear();
    assert_eq!(observed(&m, &row, Some(&b)).0, None);
    m.functions.push(function(77, "owner"));
    let mut r = row.clone();
    r.site.as_mut().unwrap().function = FuncId::new(99);
    assert_eq!(observed(&m, &r, Some(&b)).0, None);
}
#[test]
fn no_owner_and_no_site_need_no_function_resolution() {
    let (mut m, mut row, b) = fixture();
    m.functions.clear();
    row.function = None;
    row.site = None;
    assert!(observed(&m, &row, Some(&b)).0.is_some());
}
#[test]
fn own_binding_bytes_and_absence_are_both_exact_and_change_v8() {
    let (m, row, b) = fixture();
    assert_ne!(observed(&m, &row, None).0, observed(&m, &row, Some(&b)).0);
    let mut changed = b.clone();
    changed.callees = vec!["late λ\0".into()];
    assert_ne!(
        observed(&m, &row, Some(&b)).0,
        observed(&m, &row, Some(&changed)).0
    );
}
#[test]
fn all_optional_formula_source_spec_groups_keep_original_byte_order() {
    let (m, row, b) = fixture();
    for form in [false, true] {
        for source in [false, true] {
            for spec in [false, true] {
                let mut r = row.clone();
                if !form {
                    r.formula = None;
                }
                if !source {
                    r.source = None;
                }
                if !spec {
                    r.spec = None;
                }
                observed(&m, &r, Some(&b));
            }
        }
    }
}
#[test]
fn renumbered_function_and_obligation_ids_preserve_v8_link_symbol_content() {
    let (mut m, mut row, b) = fixture();
    let d = observed(&m, &row, Some(&b)).0;
    m.functions[0].id = FuncId::new(101);
    row.id = ProofId::new(3);
    row.function = Some(FuncId::new(101));
    row.site.as_mut().unwrap().function = FuncId::new(101);
    assert_eq!(observed(&m, &row, Some(&b)).0, d);
}
#[test]
fn full_raw_unicode_nul_link_symbol_tail_is_bound_without_normalization() {
    let (mut m, row, b) = fixture();
    m.functions[0].name = "raw λ\0尾".repeat(400);
    let d = observed(&m, &row, Some(&b)).0;
    m.functions[0].name.push('x');
    assert_ne!(observed(&m, &row, Some(&b)).0, d);
}
#[test]
fn every_non_clean_evidence_family_short_circuits_without_replaying_or_resolving() {
    let (mut m, mut row, _) = fixture();
    m.functions.clear();
    row.description = "ignored".repeat(200);
    for e in [
        ProofEvidence::SmtProof(vec![1]),
        ProofEvidence::LeanProof("x".into()),
        ProofEvidence::KaniHarness("y".into()),
        ProofEvidence::GammaCrownBound {
            epsilon: f64::NAN,
            verified_layers: u32::MAX,
        },
        ProofEvidence::TranslationValidation {
            rule_name: "z".into(),
            smt_hash: [0; 32],
        },
        ProofEvidence::Trusted("audit".into()),
        ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(77),
            obligation: ProofId::new(3),
            external: None,
        },
    ] {
        assert_eq!(exact_evidence(&m, &row, &e), (false, false));
    }
}
#[test]
fn legacy_match_precedes_v8_even_when_the_real_module_cannot_resolve_owner() {
    let (mut m, row, _) = fixture();
    m.functions.clear();
    let e = evidence(crate::proof::clean_cic_lineage_digest(&row), None);
    assert_eq!(exact_evidence(&m, &row, &e), (true, false));
}
#[test]
fn v8_requires_the_certificate_own_exact_binding_not_an_external_candidate() {
    let (m, row, b) = fixture();
    let d = original(&m, &row, Some(&b)).unwrap();
    let mut changed = b.clone();
    changed.statement_digest = ProofDigest::sha256([91; 32]);
    assert_eq!(
        exact_evidence(&m, &row, &evidence(d, Some(changed))),
        (false, false)
    );
}
#[test]
fn original_catalog_unique_helper_remains_distinct_from_the_core_duplicate_resolver() {
    let (mut m, row, b) = fixture();
    m.functions.push(function(77, "duplicate"));
    let c = ModuleFunctionCatalog::new(&m);
    assert!(c.unique(FuncId::new(77)).is_none());
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        row.clean_cic_lineage_digest_v8_observed(&c, Some(&b), &mut s, site())
            .unwrap(),
        None
    );
    assert!(
        row.clean_cic_lineage_digest_v8_in_module_observed(&m, Some(&b), &mut s, site())
            .unwrap()
            .is_some()
    );
}
#[test]
fn all_status_labels_and_even_empty_terms_do_not_change_lineage_data_or_create_replay() {
    let (m, mut row, b) = fixture();
    let d = original(&m, &row, Some(&b)).unwrap();
    for status in [
        ProofStatus::Pending,
        ProofStatus::Failed,
        ProofStatus::Trusted,
        ProofStatus::Discharged,
        ProofStatus::Certified,
    ] {
        row.status = status;
        let mut e = evidence(d, Some(b.clone()));
        if let ProofEvidence::CleanCic { term, .. } = &mut e {
            term.clear();
        }
        assert_eq!(exact_evidence(&m, &row, &e), (true, true));
    }
}
