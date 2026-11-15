// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN: actual scalar pricing and existing terminal paths.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use std::collections::BTreeSet;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    retirement_stop: bool,
    work: usize,
    limit: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(p);
        if self.stop == Some(self.events.len()) {
            return Err("interior");
        }
        if self.retirement_stop && p.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self.work.checked_add(p.work).ok_or("overflow")?;
        if self.limit.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(9871))
}
fn whitespace() -> String {
    [
        '\t', '\n', '\u{b}', '\u{c}', '\r', ' ', '\u{85}', '\u{a0}', '\u{1680}', '\u{2000}',
        '\u{2001}', '\u{2002}', '\u{2003}', '\u{2004}', '\u{2005}', '\u{2006}', '\u{2007}',
        '\u{2008}', '\u{2009}', '\u{200a}', '\u{2028}', '\u{2029}', '\u{202f}', '\u{205f}',
        '\u{3000}',
    ]
    .into_iter()
    .collect()
}
#[test]
fn all_actual_ascii_and_unicode_whitespace_scalars_preserve_original_trim_semantics() {
    let source = whitespace();
    assert_eq!(source.chars().count(), 25);
    assert!(source.trim().is_empty());
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(blank(&source, &mut s, site()), Ok(true));
    drop(s);
    assert_eq!(o.events.len(), 26);
    assert!(
        o.events
            .iter()
            .all(|p| p.work == 64 && p.copy_bytes == 0 && p.site == site())
    );
}
#[test]
fn actual_unicode_boundaries_and_four_byte_nonwhitespace_are_never_normalized() {
    for c in [
        '\0',
        '\u{84}',
        '\u{86}',
        '\u{180e}',
        '\u{200b}',
        '\u{feff}',
        '🦀',
        '\u{10ffff}',
    ] {
        let source = format!("\u{2003}{c}\u{3000}");
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            blank(&source, &mut s, site()).unwrap(),
            source.trim().is_empty()
        );
        drop(s);
        assert_eq!(o.events.len(), 2);
    }
}
#[test]
fn empty_and_nonblank_early_exit_have_exact_bounded_scalar_and_end_fees() {
    for (source, callbacks) in [("", 1), ("x ignored", 1), (" \t🦀 unvisited", 3)] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            blank(source, &mut s, site()).unwrap(),
            source.trim().is_empty()
        );
        drop(s);
        assert_eq!(o.events.len(), callbacks);
        assert_eq!(o.work, callbacks * 64);
    }
}
#[test]
fn every_scalar_and_exhaustion_admission_can_refuse_before_more_decode_or_predicate() {
    let source = whitespace();
    for cut in 1..=26 {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            blank(&source, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress.work, 64);
        drop(s);
        assert_eq!(o.events.len(), cut);
    }
}
#[test]
fn original_cumulative_work_covers_repeated_unicode_scans_without_new_grant() {
    let source = "\u{2003} \t";
    let mut o = Observer {
        limit: Some(4 * 64),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(blank(source, &mut s, site()), Ok(true));
    assert_eq!(
        blank(source, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "work");
}
#[test]
fn complete_public_provenance_unicode_blank_diagnostic_matches_unchanged_validator() {
    let mut b = crate::request::tests::native_bundle();
    b.provenance.producer_version = whitespace();
    b.provenance.toolchain[0].name = whitespace();
    let expected: Vec<_> = b
        .validate()
        .unwrap_err()
        .into_iter()
        .filter(|e| matches!(e, E::EmptyProvenanceField(_)))
        .collect();
    assert_eq!(
        expected,
        vec![E::EmptyProvenanceField("provenance.toolchain")]
    );
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.provenance_errors_observed(&mut s, site()).unwrap();
    assert_eq!(rows, expected);
    assert!(!rows.is_empty());
    crate::request::retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
#[test]
fn actual_functions_finish_preserves_held_error_after_cleanup_refusal() {
    let st = Functions {
        rows: vec![(
            Some(Producer::Other("whole λ\0".into())),
            vec![FuncId::new(4)],
        )],
        pending_producer: Some(Producer::Other("pending".into())),
        pending_ids: vec![FuncId::new(9)],
    };
    let mut o = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        st.finish(Err(ObservedValueError::CapacityOverflow), &mut s, site()),
        Err(ObservedValueError::CapacityOverflow)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "retirement");
    drop(s);
    assert!(
        o.events
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events.len() > 3);
}
#[test]
fn actual_imports_finish_preserves_held_error_with_full_pending_and_prior_rows() {
    let st = Imports {
        rows: vec![(
            ImportId::new(3),
            "whole λ\0".into(),
            Some(Producer::Other("producer".into())),
        )],
        pending_name: "pending".into(),
        pending_producer: Some(Producer::Other("tail".into())),
    };
    let mut o = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut s, site()),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "retirement");
    drop(s);
    assert!(o.events.len() > 3);
}
#[test]
fn actual_checking_finish_preserves_held_error_while_full_coverage_rows_are_retired() {
    let st = Checking {
        errors: vec![E::BundleLanguageUncovered {
            producer: Some(Producer::Other("raw λ\0".into())),
            functions: vec![FuncId::new(3)],
            source_languages: BTreeSet::from([NativeSourceLanguage::Rust]),
        }],
        pending: Some(E::EmptyProvenanceField("pending")),
        functions: vec![(None, vec![FuncId::new(9)])],
        imports: vec![(ImportId::new(5), "import".into(), None)],
    };
    let mut o = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        st.finish(Err(ObservedValueError::UnsupportedValue), &mut s, site()),
        Err(ObservedValueError::UnsupportedValue)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "retirement");
}
#[test]
fn cleanup_only_stop_still_refuses_healthy_provenance_instead_of_empty_success() {
    let mut o = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        Checking::default().finish(Ok(()), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
