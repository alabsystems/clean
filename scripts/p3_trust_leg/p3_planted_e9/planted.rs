// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The planted pair at every site of `p3_planted_e9.rs`, in the order of its
//! pins, installed beside it (`p3_planted_e9/planted.rs`).

use clean_auto::bridge::ay_contract::serialize_term;
use clean_kernel::{Environment, Expr, Name};
use trust_certify::reference_mint::{check_closed_in, check_registered_in};
use trust_certify::{
    recheck_presented_linear_int_vc, reference_certificate_for, replay_presented_vc_evidence,
};

use crate::contract::{Outcome, Row, is_planted_mismatch};
use crate::controls::Honest;
use crate::evidence::{
    RETURNED_BOOL, RETURNED_SOME, calculus_base, calculus_lane, konst, presented, verdict,
};
use crate::lanes::{
    E9Mint, batch_example, e9_grade, e9_lane, is_example_mismatch, is_let_rec_mismatch, island,
    island_example, island_judgment, let_rec_lanes, theorem, universe_judgment,
};
use crate::{LET_REC_SOURCE, PLANTED_EXAMPLE, PLANTED_SOURCE};

/// Every planted row, on `env`, which gains the theorem `p3_planted` when the
/// linked kernel admits it.
pub(crate) fn rows(env: &mut Environment, honest: &Honest, failures: &mut Vec<String>) -> Vec<Row> {
    let Honest { refutation: honest_refutation, presented_for: refutation_presented, .. } = honest;
    // The planted pair.
    let mut rows: Vec<Row> = Vec::new();
    let (outcome, detail) = island(PLANTED_SOURCE, "p3_planted_src");
    rows.push(("trust.island.source", outcome, detail));
    let resident = match env.add_decl(theorem("p3_planted", "False", "Nat.zero")) {
        Ok(()) => {
            let detail = "p3_planted : False := Nat.zero resident in the island environment (clean-kernel's door, no Trust code)";
            rows.push(("kernel.add_decl", Outcome::Minted, detail.to_string()));
            true
        }
        Err(error) => {
            let detail = format!("{error:?}");
            if !is_planted_mismatch(&detail) {
                failures.push(format!("P3 UNEXPECTED REFUSAL: kernel.add_decl: {detail}"));
            }
            rows.push(("kernel.add_decl", Outcome::Refused, detail));
            false
        }
    };
    let recheck = match check_registered_in(env, &Name::from_string("p3_planted")) {
        Ok(certificate) => {
            (Outcome::Minted, format!("ReferenceCertificate in {:?}", certificate.theory_id()))
        }
        Err(miss) => {
            let detail = format!("{miss:?}");
            // With the theorem refused at admission the gate finds nothing to
            // re-check; with it resident, only the type mismatch is the planted one.
            let expected =
                if resident { is_planted_mismatch(&detail) } else { detail.contains("absent") };
            if !expected {
                failures.push(format!(
                    "P3 UNEXPECTED REFUSAL: trust.island.reference_recheck: {detail}"
                ));
            }
            (Outcome::Refused, detail)
        }
    };
    rows.push(("trust.island.reference_recheck", recheck.0, recheck.1));
    let lane = e9_lane(env, E9Mint::Scalar, "false", "p3_planted", failures);
    for (site, (outcome, detail)) in [
        "trust.e9.certify_ensures_discharge",
        "trust.e9.reference_entry",
        "trust.e9.registered_certificate",
    ]
    .into_iter()
    .zip(lane)
    {
        rows.push((site, outcome, detail));
    }
    let direct = match check_closed_in(env, &Expr::const_str("False"), &Expr::const_str("Nat.zero"))
    {
        Ok(certificate) => {
            (Outcome::Minted, format!("ReferenceCertificate in {:?}", certificate.theory_id()))
        }
        Err(miss) => {
            let detail = format!("{miss:?}");
            if !is_planted_mismatch(&detail) {
                failures.push(format!(
                    "P3 UNEXPECTED REFUSAL: trust.reference_mint.check_closed_in: {detail}"
                ));
            }
            (Outcome::Refused, detail)
        }
    };
    rows.push(("trust.reference_mint.check_closed_in", direct.0, direct.1));

    // The universe branch of the island's judgment check, citing the resident
    // theorem. Not resident: the kernel finds no `p3_planted`; resident, only
    // the planted mismatch (from the entry's re-check of it) is expected.
    let (goal, proof) = universe_judgment("False", "p3_planted");
    let universe = island_judgment(env, &goal, &proof).unwrap_or_else(|detail| {
        let expected = if resident {
            is_planted_mismatch(&detail)
        } else {
            detail.contains("UnknownConst") || detail.contains("nknown constant")
        };
        if !expected {
            failures.push(format!(
                "P3 UNEXPECTED REFUSAL: trust.reference_mint.check_island_judgment_in.universe: {detail}"
            ));
        }
        (Outcome::Refused, detail)
    });
    rows.push(("trust.reference_mint.check_island_judgment_in.universe", universe.0, universe.1));

    let (outcome, detail) = e9_grade(env, "false", "p3_planted");
    let expected =
        if resident { is_planted_mismatch(&detail) } else { detail.contains("TheoremNotFound") };
    if outcome == Outcome::Refused && !expected {
        failures.push(format!(
            "P3 UNEXPECTED REFUSAL: trust.e9.grade.kernel_discharge_ensures_citation: {detail}"
        ));
    }
    rows.push(("trust.e9.grade.kernel_discharge_ensures_citation", outcome, detail));

    let lane = e9_lane(env, E9Mint::Domains, "false", "p3_planted", failures);
    for (site, (outcome, detail)) in [
        "trust.e9.domains.certify_ensures_discharge_with_domains",
        "trust.e9.domains.reference_entry",
        "trust.e9.domains.registered_certificate",
    ]
    .into_iter()
    .zip(lane)
    {
        rows.push((site, outcome, detail));
    }

    // Both doors on the planted example: the elaborator refuses before any
    // anonymous judgment exists. A refusal by the reference re-check itself,
    // or of any other shape, is not this measurement.
    for (site, (outcome, detail)) in [
        ("trust.island.example_source", island_example(PLANTED_EXAMPLE)),
        ("trust.island_batch.example_source", batch_example(PLANTED_EXAMPLE)),
    ] {
        if outcome == Outcome::Refused
            && (!is_example_mismatch(&detail) || detail.contains("reference kernel recheck"))
        {
            failures.push(format!("P3 UNEXPECTED REFUSAL: {site}: {detail}"));
        }
        rows.push((site, outcome, detail));
    }

    // The calculus row, (A) the planted pair as the producer's annotation over
    // an honest `A : False` family, (B) the resident theorem cited by the
    // family's `row_of`.
    let annotation = match calculus_base(env, "False", "True", "p3_honest") {
        Err(detail) => {
            failures
                .push(format!("P3 VACUOUS: the honest `A : False` family is refused: {detail}"));
            (Outcome::Refused, detail)
        }
        Ok(reference) => {
            match calculus_lane(
                &reference,
                b"p3_calculus_planted_annotation",
                &konst("Nat.zero"),
                failures,
            ) {
                Ok([certified, _]) => certified,
                Err(detail) => {
                    if !is_planted_mismatch(&detail) {
                        failures.push(format!(
                            "P3 UNEXPECTED REFUSAL: trust.calculus.producer_annotation: {detail}"
                        ));
                    }
                    (Outcome::Refused, detail)
                }
            }
        }
    };
    rows.push(("trust.calculus.producer_annotation", annotation.0, annotation.1));
    let cited = calculus_base(env, "True", "False", "p3_planted").and_then(|reference| {
        calculus_lane(&reference, b"p3_calculus_planted_base", &konst("True.intro"), failures)
    });
    let cited = cited.unwrap_or_else(|detail| {
        let expected = if resident {
            is_planted_mismatch(&detail)
        } else {
            detail.contains("p3_planted absent")
        };
        if !expected {
            failures.push(format!(
                "P3 UNEXPECTED REFUSAL: trust.calculus.certify_calculus_row: {detail}"
            ));
        }
        [(Outcome::Refused, detail), (Outcome::Refused, "no certificate to bind".to_string())]
    });
    for (site, (outcome, detail)) in
        ["trust.calculus.certify_calculus_row", "trust.calculus.registered_bound"]
            .into_iter()
            .zip(cited)
    {
        rows.push((site, outcome, detail));
    }

    // Presented refutation evidence carrying the planted term.
    let planted_presented = match (honest_refutation, serialize_term(&konst("Nat.zero")).ok()) {
        (Some(evidence), Some(term)) => presented(evidence, Some(term), refutation_presented),
        _ => None,
    };
    let refutation_rows = match &planted_presented {
        Some(evidence) => [
            verdict(
                replay_presented_vc_evidence(refutation_presented, evidence),
                "replay_presented_vc_evidence",
                RETURNED_BOOL,
            ),
            verdict(
                reference_certificate_for(evidence).is_some(),
                "reference_certificate_for",
                RETURNED_SOME,
            ),
            verdict(
                recheck_presented_linear_int_vc(refutation_presented, evidence),
                "recheck_presented_linear_int_vc",
                RETURNED_BOOL,
            ),
        ],
        None => {
            failures.push(
                "P3 VACUOUS: no refutation evidence to present the planted term in".to_string(),
            );
            std::array::from_fn(|_| (Outcome::Refused, "no evidence presented".to_string()))
        }
    };
    for (site, (outcome, detail)) in [
        "trust.refutation.replay_presented_vc_evidence",
        "trust.refutation.reference_certificate",
        "trust.refutation.recheck_presented_linear_int_vc",
    ]
    .into_iter()
    .zip(refutation_rows)
    {
        rows.push((site, outcome, detail));
    }

    // The planted pair from source, through a term-level `let rec`: the doors
    // refuse only by the kernel's check of the lifted helper, a type mismatch.
    let planted_let_rec =
        let_rec_lanes(LET_REC_SOURCE, "p3_letrec_src", "false", "p3_letrec", failures);
    for (index, (site, (outcome, detail))) in [
        "trust.island.let_rec_source",
        "trust.island_batch.let_rec_source",
        "trust.e9.let_rec.certify_ensures_discharge",
        "trust.e9.let_rec.reference_entry",
        "trust.e9.let_rec.registered_certificate",
        "trust.e9.let_rec.grade",
        "trust.e9.let_rec_parent.certify_ensures_discharge",
        "trust.e9.let_rec_parent.reference_entry",
        "trust.e9.let_rec_parent.registered_certificate",
        "trust.e9.let_rec_parent.grade",
    ]
    .into_iter()
    .zip(planted_let_rec)
    .enumerate()
    {
        if index < 2 && outcome == Outcome::Refused && !is_let_rec_mismatch(&detail) {
            failures.push(format!("P3 UNEXPECTED REFUSAL: {site}: {detail}"));
        }
        rows.push((site, outcome, detail));
    }
    rows
}
