// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: the actual boolean, not claim parsing or authority.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::{FuncId, interpret::InterpretOptions, pred::Pred};
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original formula stop");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(467))
}
fn formula(schema: &str, payload: &str, rendering: Option<&str>) -> ProofFormula {
    let mut formula = ProofFormula::new(schema, payload);
    formula.smtlib = rendering.map(str::to_owned);
    formula
}
fn run(f: &ProofFormula, table: &PredTable<'_>) -> (bool, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = f.states_two_texts_observed(table, &mut s, site()).unwrap();
    assert_eq!(out, f.states_two_texts(table));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (out, o)
}
#[test]
fn absent_rendering_reads_no_schema_payload_sort_or_bindings() {
    let table = PredTable::new(&[], &[]);
    let mut baseline = None;
    for schema in [
        "",
        "unread",
        OwnedFormulaSchema::Pred.name(),
        OwnedFormulaSchema::Smtlib2.name(),
    ] {
        let f = formula(schema, &"raw λ\0尾".repeat(10000), None);
        let (out, o) = run(&f, &table);
        assert!(!out);
        if let Some(prior) = &baseline {
            assert_eq!(&o.events, prior)
        } else {
            baseline = Some(o.events)
        }
    }
}
#[test]
fn exact_registry_is_case_and_byte_sensitive_for_all_five_schema_names() {
    let table = PredTable::new(&[], &[]);
    for schema in OwnedFormulaSchema::ALL {
        let f = formula(schema.name(), "unread", Some("other"));
        assert!(run(&f, &table).0);
        for wrong in [
            schema.name().to_ascii_uppercase(),
            schema.name().to_owned() + " ",
            schema.name().to_owned() + "\0",
        ] {
            assert!(!run(&formula(&wrong, "unread", Some("other")), &table).0);
        }
    }
}
#[test]
fn opaque_schema_ignores_payload_and_rendering_instead_of_reading_either() {
    let table = PredTable::new(&[], &[]);
    let (_, baseline) = run(&formula("opaque", "a", Some("b")), &table);
    let (_, large) = run(
        &formula("opaque", &"λ\0".repeat(10000), Some(&"尾".repeat(10000))),
        &table,
    );
    assert_eq!(baseline.events, large.events);
}
#[test]
fn claim_and_unread_payloads_have_identical_two_text_boolean_without_parsing() {
    let table = PredTable::new(&[], &[]);
    for schema in [
        OwnedFormulaSchema::BvBlastGoal,
        OwnedFormulaSchema::SatRes,
        OwnedFormulaSchema::LineageTransformBinding,
    ] {
        let (_, baseline) = run(&formula(schema.name(), "", Some("")), &table);
        for payload in [
            "sha256:".to_owned() + &"0".repeat(64),
            "garbage λ\0".repeat(10000),
            "site=0;kind=goal".into(),
        ] {
            let (out, o) = run(&formula(schema.name(), &payload, Some("raw λ\0")), &table);
            assert!(out);
            assert_eq!(o.events, baseline.events);
        }
    }
}
#[test]
fn smtlib_payload_equality_is_exact_for_empty_unicode_nul_and_long_chunks() {
    let table = PredTable::new(&[], &[]);
    for text in ["".into(), "true".into(), "λ\0尾".repeat(700)] {
        assert!(
            !run(
                &formula(OwnedFormulaSchema::Smtlib2.name(), &text, Some(&text)),
                &table
            )
            .0
        );
        assert!(
            run(
                &formula(
                    OwnedFormulaSchema::Smtlib2.name(),
                    &text,
                    Some(&(text.clone() + " "))
                ),
                &table
            )
            .0
        );
        if !text.is_empty() {
            let at = text.chars().next().unwrap().len_utf8();
            let bad = "?".to_owned() + &text[at..];
            assert!(
                run(
                    &formula(OwnedFormulaSchema::Smtlib2.name(), &text, Some(&bad)),
                    &table
                )
                .0
            );
        }
    }
}
#[test]
fn canonical_citations_and_dangling_or_bad_citations_preserve_actual_original() {
    let preds = [Pred::Top, Pred::NonZero];
    let table = PredTable::new(&preds, &[]);
    let schema = OwnedFormulaSchema::Pred.name();
    for (payload, rendering, expected) in [
        ("pred.0", "true", false),
        ("pred.1", "(not (= self 0))", false),
        ("pred.1", "true", true),
        ("pred.4294967295", "true", true),
    ] {
        assert_eq!(
            run(&formula(schema, payload, Some(rendering)), &table).0,
            expected
        );
    }
    for bad in [
        "",
        "0",
        "Pred.0",
        "pred.",
        "pred.00",
        "pred.01",
        "pred.+0",
        "pred.-0",
        "pred. 0",
        "pred.0 ",
        "pred.0\n",
        "pred.0\0",
        "pred.０",
        "pred.4294967296",
        "pred.999999999999999999999999999999999999",
    ] {
        assert!(run(&formula(schema, bad, Some("true")), &table).0);
    }
}
#[test]
fn predicate_delegation_is_actual_and_missing_depth_or_cardinality_stays_disagreeing() {
    let preds = [
        Pred::Interval {
            lo: i128::MIN,
            hi: i128::MAX,
        },
        Pred::Conj(vec![PredId::new(7)]),
    ];
    let table = PredTable::new(&preds, &[]);
    let text = table.smtlib_of(PredId::new(0)).unwrap();
    let schema = OwnedFormulaSchema::Pred.name();
    assert!(!run(&formula(schema, "pred.0", Some(&text)), &table).0);
    assert!(run(&formula(schema, "pred.1", Some("(and true)")), &table).0);
    let (_, o) = run(&formula(schema, "pred.0", Some(&text)), &table);
    // Compare the actual complete child trace, including retirement, instead
    // of guessing how many scratch callbacks this scalar fixture needs.
    let mut child = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut child);
    assert!(
        table
            .smtlib_matches_observed(PredId::new(0), &text, &mut session, site())
            .unwrap()
    );
    assert!(session.first_refusal().is_none());
    drop(session);
    assert!(!child.events.is_empty());
    assert!(
        o.events
            .windows(child.events.len())
            .any(|events| events == child.events.as_slice())
    );
    let retirement = |events: &[ExecutionProgress]| {
        events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .copied()
            .collect::<Vec<_>>()
    };
    let child_retirement = retirement(&child.events);
    assert!(!child_retirement.is_empty());
    assert_eq!(retirement(&o.events), child_retirement);
    assert!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Publication)
            .count()
            >= 2
    );
}
