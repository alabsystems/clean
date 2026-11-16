// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! P3, Trust leg: the planted proof of `False` through Trust's temporal source
//! certification, `trust_spec_temporal::certify_clean_temporal_source` and
//! `recheck_clean_temporal_certificate` (acceptance sites of the
//! `trust-spec-temporal` route in P1's census, with `checked_theorem`, which
//! both call). Each elaborates an authored Clean unit after the fixed temporal
//! prelude, in a fresh environment, then checks the named theorem: its stored
//! value by `check_type` at its type, its proof quality, its axioms and the
//! certification audit. The recheck re-elaborates the exact source, requires
//! the stored type and proof to equal the fresh ones, and checks the stored
//! proof again.
//!
//! This file belongs to Clean (`scripts/p3_trust_leg/`), not to Trust: Clean's
//! `scripts/patched_kernel_control_trust.py` installs it into a scratch copy of
//! Trust's tree as `crates/trust-spec-temporal/tests/p3_planted_temporal.rs`
//! (its own Cargo workspace, built with its own target directory), beside
//! `p3_contract/contract.rs`, the contract it shares with `p3_planted_e9.rs`,
//! once over `first-party/clean`'s unmodified kernel and once over P3's mutant
//! M1, and runs it in each. In both, clean-tla carries the runner's two-arm
//! shim, without which this workspace does not compile from Trust's pins
//! (`shim_clean_tla`). Nothing of it lands in Trust.
//!
//! The sites, in order:
//!
//! * `trust.temporal.certify_clean_temporal_source.source`: the plain planted
//!   theorem `p3_planted_src : False := Nat.zero`. The elaborator compares the
//!   body's type with the stated type by `is_def_eq`, which M1 does not touch,
//!   so both legs refuse: the same kernel's other entry, not an independent
//!   check.
//! * `trust.temporal.certify_clean_temporal_source.let_rec_source`: the planted
//!   pair inside a term-level `let rec` (`theorem p3_letrec_src : False := let
//!   rec go : False := Nat.zero; go`). The elaborator lifts the non-recursive
//!   helper with no check of its value (as at Trust's island door, which the
//!   same `elaborate_decl_and_register_inner` serves), so the only check the
//!   helper's value meets is the kernel's `check_type`, the comparison M1
//!   mutates: at the helper's `add_decl`, and again in `checked_theorem`'s
//!   certification audit, whose dependency walk re-checks it the same way.
//!   `checked_theorem` also checks the parent.
//! * `trust.temporal.recheck_clean_temporal_certificate.let_rec_source`: the
//!   certificate that row issued, replayed against the same source. With the
//!   source refused there is no certificate to replay.
//!
//! Controls run in both legs and must mint, or the leg measures nothing
//! (`P3 VACUOUS`): the honest theorem `p3_honest_src : True := True.intro` and
//! the honest `let rec` source `p3_letrec_honest_src : True := let rec go :
//! True := True.intro; go`, each certified and rechecked.

#[path = "p3_contract/contract.rs"]
mod contract;

use clean_kernel::Environment;
use trust_spec_temporal::{
    CleanTemporalCertificate, certify_clean_temporal_source, recheck_clean_temporal_certificate,
};

use crate::contract::{Control, Outcome, Pin, Row, is_planted_mismatch};

const PLANTED_SOURCE: &str = "theorem p3_planted_src : False := Nat.zero\n";
const HONEST_SOURCE: &str = "theorem p3_honest_src : True := True.intro\n";
const LET_REC_SOURCE: &str =
    "theorem p3_letrec_src : False :=\n  let rec go : False := Nat.zero\n  go\n";
const HONEST_LET_REC_SOURCE: &str =
    "theorem p3_letrec_honest_src : True :=\n  let rec go : True := True.intro\n  go\n";

/// The outcome each site is pinned to, per declared kernel (`contract::Pin`).
const PINS: &[Pin] = &[
    ("trust.temporal.certify_clean_temporal_source.source", Outcome::Refused, Outcome::Refused),
    (
        "trust.temporal.certify_clean_temporal_source.let_rec_source",
        Outcome::Refused,
        Outcome::Minted,
    ),
    (
        "trust.temporal.recheck_clean_temporal_certificate.let_rec_source",
        Outcome::Refused,
        Outcome::Minted,
    ),
];

/// The kernel's refusal of the lifted helper, in whatever words the entry
/// renders it: a type mismatch between `False` and `Nat`.
fn is_let_rec_mismatch(detail: &str) -> bool {
    let lower = detail.to_lowercase();
    lower.contains("mismatch") && lower.contains("false") && lower.contains("nat")
}

/// `certify_clean_temporal_source` on one authored unit. Errors are printed
/// with `{:?}`, which escapes tabs and newlines, so the runner's row parse
/// stays four cells.
fn certify(source: &str, theorem: &str) -> ((Outcome, String), Option<CleanTemporalCertificate>) {
    match certify_clean_temporal_source(source, theorem) {
        Ok(certificate) => {
            let detail = format!("CleanTemporalCertificate for {:?}", certificate.theorem);
            ((Outcome::Minted, detail), Some(certificate))
        }
        Err(error) => ((Outcome::Refused, format!("{error:?}")), None),
    }
}

/// `recheck_clean_temporal_certificate` on the certificate `certify` issued.
fn recheck(certificate: Option<&CleanTemporalCertificate>, source: &str) -> (Outcome, String) {
    match certificate {
        None => (Outcome::Refused, "no certificate to recheck: the source was refused".to_string()),
        Some(certificate) => match recheck_clean_temporal_certificate(certificate, source) {
            Ok(()) => (
                Outcome::Minted,
                "recheck_clean_temporal_certificate accepted: fresh elaboration, artifacts equal, stored proof checked"
                    .to_string(),
            ),
            Err(error) => (Outcome::Refused, format!("{error:?}")),
        },
    }
}

#[test]
fn p3_planted_false_through_temporal_certification() {
    let mut failures = Vec::new();
    let env = Environment::with_prelude();
    let declared = contract::start(PINS, &env, &mut failures);

    // Controls: each honest unit is certified and its certificate rechecked.
    let mut control: Vec<Control> = Vec::new();
    for (certify_stage, recheck_stage, source, theorem) in [
        ("temporal.honest.certify", "temporal.honest.recheck", HONEST_SOURCE, "p3_honest_src"),
        (
            "temporal.let_rec.certify",
            "temporal.let_rec.recheck",
            HONEST_LET_REC_SOURCE,
            "p3_letrec_honest_src",
        ),
    ] {
        let (certified, certificate) = certify(source, theorem);
        control.push((certify_stage, certified));
        control.push((recheck_stage, recheck(certificate.as_ref(), source)));
    }
    contract::report_controls(&control, &mut failures);

    // The planted pair: the plain theorem is refused by the elaborator's
    // `is_def_eq`; the `let rec` spelling only by the kernel's check of the
    // helper. Any other refusal is not this measurement.
    let mut rows: Vec<Row> = Vec::new();
    let ((outcome, detail), _) = certify(PLANTED_SOURCE, "p3_planted_src");
    if outcome == Outcome::Refused && !is_planted_mismatch(&detail) && !is_let_rec_mismatch(&detail)
    {
        failures.push(format!(
            "P3 UNEXPECTED REFUSAL: trust.temporal.certify_clean_temporal_source.source: {detail}"
        ));
    }
    rows.push(("trust.temporal.certify_clean_temporal_source.source", outcome, detail));
    let ((outcome, detail), certificate) = certify(LET_REC_SOURCE, "p3_letrec_src");
    if outcome == Outcome::Refused && !is_let_rec_mismatch(&detail) {
        failures.push(format!(
            "P3 UNEXPECTED REFUSAL: trust.temporal.certify_clean_temporal_source.let_rec_source: {detail}"
        ));
    }
    rows.push(("trust.temporal.certify_clean_temporal_source.let_rec_source", outcome, detail));
    let (outcome, detail) = recheck(certificate.as_ref(), LET_REC_SOURCE);
    if outcome == Outcome::Refused && certificate.is_some() {
        failures.push(format!(
            "P3 UNEXPECTED REFUSAL: trust.temporal.recheck_clean_temporal_certificate.let_rec_source refused a certificate certify issued: {detail}"
        ));
    }
    rows.push((
        "trust.temporal.recheck_clean_temporal_certificate.let_rec_source",
        outcome,
        detail,
    ));

    contract::finish(&rows, PINS, declared, failures);
}
