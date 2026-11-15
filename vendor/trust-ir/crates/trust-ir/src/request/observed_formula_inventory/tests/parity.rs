// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_inventory_keeps_exact_original_order_and_both_leads_to_leaves() {
    let m = fixture();
    let (out, _, _) = run(&m);
    let sites: Vec<_> = out
        .into_iter()
        .map(|e| match e {
            E::FormulaTextsDisagree { site } => site,
            _ => panic!("wrong diagnostic"),
        })
        .collect();
    assert_eq!(
        sites,
        vec![
            FormulaSite::Obligation(ProofId::new(3)),
            FormulaSite::SummaryClause {
                function: FuncId::new(7),
                clause: "requires",
                index: 1
            },
            FormulaSite::SummaryClause {
                function: FuncId::new(7),
                clause: "ensures",
                index: 0
            },
            FormulaSite::SummaryClause {
                function: FuncId::new(7),
                clause: "decreases",
                index: 0
            },
            FormulaSite::SpecInvariant {
                machine: "M".into(),
                invariant: "I".into()
            },
            FormulaSite::SpecTemporal {
                machine: "M".into(),
                property: "A".into()
            },
            FormulaSite::SpecTemporal {
                machine: "M".into(),
                property: "L".into()
            },
            FormulaSite::SpecTemporal {
                machine: "M".into(),
                property: "L".into()
            },
            FormulaSite::SpecTemporal {
                machine: "M".into(),
                property: "W".into()
            }
        ]
    );
}
#[test]
fn empty_and_absent_carriers_produce_no_disagreement_or_label_copy() {
    let mut m = Module::new("");
    assert!(run(&m).0.is_empty());
    m.proof_obligations.push(obligation(7, None));
    m.functions.push(Function::new(
        FuncId::new(1),
        "unread",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    let mut spec = SpecModule::new("huge λ\0".repeat(10000));
    spec.invariants
        .push(SpecInvariant::new("ignored 尾".repeat(10000), "ignored"));
    spec.temporal.push(SpecTemporal::new(
        "ignored".repeat(10000),
        TemporalForm::StrongFair {
            action: "ignored".into(),
            relation: None,
        },
    ));
    m.spec_modules.push(spec);
    let (_, large, _) = run(&m);
    m.spec_modules[0].name = "M".into();
    m.spec_modules[0].invariants[0].name = "I".into();
    m.spec_modules[0].temporal[0].name = "T".into();
    let (_, short, _) = run(&m);
    assert_eq!(large.events, short.events);
}
#[test]
fn raw_unicode_nul_labels_are_owned_whole_without_normalization() {
    let mut m = Module::new("");
    let name = " raw λ\0尾\n".repeat(1000);
    let label = " invariant \0尾 λ ".repeat(900);
    let mut spec = SpecModule::new(&name);
    spec.invariants
        .push(SpecInvariant::new(&label, "ignored").with_typed(bad()));
    m.spec_modules.push(spec);
    assert_eq!(
        run(&m).0,
        vec![E::FormulaTextsDisagree {
            site: FormulaSite::SpecInvariant {
                machine: name,
                invariant: label
            }
        }]
    );
}
#[test]
fn summary_clauses_keep_physical_functions_and_original_clause_indices() {
    let mut m = Module::new("");
    m.functions = vec![
        function(9, vec![good(), bad(), good(), bad()], vec![], vec![bad()]),
        function(9, vec![bad()], vec![bad(), good(), bad()], vec![]),
    ];
    let out = run(&m).0;
    assert_eq!(out.len(), 6);
    assert!(
        matches!(&out[3],E::FormulaTextsDisagree{site:FormulaSite::SummaryClause{function,clause:"requires",index:0}} if *function==FuncId::new(9))
    );
}
#[test]
fn repeated_spec_and_property_labels_keep_all_physical_errors() {
    let mut m = fixture();
    let spec = m.spec_modules[0].clone();
    m.spec_modules.push(spec);
    let out = run(&m).0;
    assert_eq!(out.len(), 14);
    assert_eq!(&out[4..9], &out[9..14]);
}
#[test]
fn every_temporal_form_and_recorded_or_absent_fairness_relation_is_exact() {
    let mut m = Module::new("");
    let mut spec = SpecModule::new("M");
    for form in [
        TemporalForm::Always(bad()),
        TemporalForm::Eventually(bad()),
        TemporalForm::LeadsTo(good(), bad()),
        TemporalForm::LeadsTo(bad(), good()),
        TemporalForm::WeakFair {
            action: "W".into(),
            relation: Some(bad()),
        },
        TemporalForm::StrongFair {
            action: "S".into(),
            relation: Some(bad()),
        },
        TemporalForm::WeakFair {
            action: "W".into(),
            relation: None,
        },
        TemporalForm::StrongFair {
            action: "S".into(),
            relation: None,
        },
    ] {
        spec.temporal.push(SpecTemporal::new("T", form));
    }
    m.spec_modules.push(spec);
    assert_eq!(run(&m).0.len(), 6);
}
#[test]
fn actual_predicate_schema_child_matches_then_detects_rendering_tampering() {
    let mut m = Module::new("");
    m.predicates = vec![crate::pred::Pred::FiniteSet(vec![
        crate::Constant::SymbolAddr {
            symbol: "raw λ\0尾".repeat(1200),
            addend: -9,
        },
    ])];
    let text = m
        .pred_table()
        .smtlib_of(crate::value::PredId::new(0))
        .unwrap();
    let mut f = ProofFormula::new(crate::pred::PRED_FORMULA_SCHEMA, "pred.0");
    f.smtlib = Some(text);
    m.proof_obligations.push(obligation(7, Some(f)));
    assert!(run(&m).0.is_empty());
    m.proof_obligations[0]
        .formula
        .as_mut()
        .unwrap()
        .smtlib
        .as_mut()
        .unwrap()
        .push(' ');
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn opaque_absent_and_claim_formulas_keep_the_original_group_outcome() {
    let mut m = Module::new("");
    let mut opaque = ProofFormula::new("opaque", "false");
    opaque.smtlib = Some("true".into());
    let absent = ProofFormula::new("smtlib2", "false");
    let mut claim = ProofFormula::new(
        crate::proof::OwnedFormulaSchema::LineageTransformBinding.name(),
        "unread",
    );
    claim.smtlib = Some("true".into());
    m.proof_obligations = vec![
        obligation(1, Some(opaque)),
        obligation(2, Some(absent)),
        obligation(3, Some(claim)),
    ];
    assert_eq!(
        run(&m).0,
        vec![E::FormulaTextsDisagree {
            site: FormulaSite::Obligation(ProofId::new(3))
        }]
    );
}

#[test]
fn full_width_sparse_obligation_and_summary_ids_are_not_reindexed() {
    let mut m = Module::new("");
    m.proof_obligations.push(obligation(u32::MAX, Some(bad())));
    m.functions
        .push(function(u32::MAX - 1, vec![bad()], vec![], vec![]));
    let out = run(&m).0;
    assert_eq!(
        out[0],
        E::FormulaTextsDisagree {
            site: FormulaSite::Obligation(ProofId::new(u32::MAX))
        }
    );
    assert!(
        matches!(&out[1],E::FormulaTextsDisagree{site:FormulaSite::SummaryClause{function,..}}if *function==FuncId::new(u32::MAX-1))
    );
}
#[test]
fn duplicate_physical_obligation_ids_keep_each_actual_formula_occurrence() {
    let mut m = Module::new("");
    m.proof_obligations = vec![
        obligation(7, Some(bad())),
        obligation(7, Some(good())),
        obligation(7, Some(bad())),
    ];
    let out = run(&m).0;
    assert_eq!(out.len(), 2);
    assert_eq!(out[0], out[1]);
}
#[test]
fn bundle_leaf_uses_actual_module_and_never_request_or_status_authority() {
    let m = fixture();
    let mut b = bundle(m.clone());
    b.requests.clear();
    b.evidence_bundles.clear();
    b.module.proof_certificates.clear();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.formula_text_errors_observed(&mut s, site()).unwrap();
    assert_eq!(rows, ordinary(&m));
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
#[test]
fn owned_temporal_labels_outlive_the_complete_borrowed_bundle() {
    let machine = "M λ\0尾".repeat(900);
    let property = "T 尾\0λ".repeat(700);
    let mut m = Module::new("");
    let mut sp = SpecModule::new(&machine);
    sp.temporal.push(SpecTemporal::new(
        &property,
        TemporalForm::LeadsTo(bad(), bad()),
    ));
    m.spec_modules.push(sp);
    let b = bundle(m);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.formula_text_errors_observed(&mut s, site()).unwrap();
    drop(b);
    let expected = E::FormulaTextsDisagree {
        site: FormulaSite::SpecTemporal { machine, property },
    };
    assert_eq!(rows, vec![expected.clone(), expected]);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
