// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The honest counterpart of every planted row of `p3_planted_e9.rs`, installed
//! beside it (`p3_planted_e9/controls.rs`). Each must mint, or the leg measures
//! nothing (`P3 VACUOUS`).

use clean_kernel::Environment;
use trust_certify::{
    certify_vc, recheck_presented_linear_int_vc, reference_certificate_for,
    replay_presented_vc_evidence,
};
use trust_types::VerificationCondition;

use crate::contract::{Control, Outcome};
use crate::evidence::{
    RETURNED_BOOL, calculus_base, calculus_lane, konst, presented, refutation_vc, verdict,
};
use crate::lanes::{
    E9Mint, batch_example, e9_grade, e9_lane, island, island_example, island_judgment,
    let_rec_lanes, theorem, universe_judgment,
};
use crate::{HONEST_EXAMPLE, HONEST_LET_REC_SOURCE, HONEST_SOURCE};

/// The controls, and what the planted rows reuse from them: the honest
/// refutation evidence (issued once; the planted term is presented in its
/// place) and the row it is presented for.
pub(crate) struct Honest {
    pub(crate) control: Vec<Control>,
    pub(crate) refutation: Option<trust_ir::ProofEvidence>,
    pub(crate) presented_for: VerificationCondition,
}

/// Every honest counterpart, on `env`, which gains the theorem `p3_honest`.
pub(crate) fn controls(env: &mut Environment, failures: &mut Vec<String>) -> Honest {
    // Controls: every honest counterpart mints.
    let mut control = vec![("island", island(HONEST_SOURCE, "p3_honest_src"))];
    match env.add_decl(theorem("p3_honest", "True", "True.intro")) {
        Ok(()) => {
            let honest = e9_lane(env, E9Mint::Scalar, "true", "p3_honest", failures);
            control.extend(["audited", "reference", "registered"].into_iter().zip(honest));
            let honest = e9_lane(env, E9Mint::Domains, "true", "p3_honest", failures);
            control.extend(
                ["domains.audited", "domains.reference", "domains.registered"]
                    .into_iter()
                    .zip(honest),
            );
            control.push(("grade", e9_grade(env, "true", "p3_honest")));
            let (goal, proof) = universe_judgment("True", "p3_honest");
            let universe =
                island_judgment(env, &goal, &proof).unwrap_or_else(|why| (Outcome::Refused, why));
            control.push(("island_judgment_universe", universe));
            let honest_calculus =
                calculus_base(env, "True", "True", "p3_honest").and_then(|reference| {
                    calculus_lane(&reference, b"p3_calculus_honest", &konst("True.intro"), failures)
                });
            let [certified, registered] = honest_calculus.unwrap_or_else(|why| {
                [(Outcome::Refused, why), (Outcome::Refused, "no certificate to bind".to_string())]
            });
            control.extend([("calculus.certify", certified), ("calculus.registered", registered)]);
        }
        Err(error) => {
            failures.push(format!("P3 VACUOUS: the honest theorem is refused: {error:?}"))
        }
    }
    control.push(("island_example", island_example(HONEST_EXAMPLE)));
    control.push(("batch_example", batch_example(HONEST_EXAMPLE)));
    let refutation_certified = refutation_vc("p3_refutation_certified");
    let refutation_presented = refutation_vc("p3_refutation_presented");
    let honest_refutation = certify_vc(&refutation_certified);
    let honest_presented = honest_refutation
        .as_ref()
        .and_then(|evidence| presented(evidence, None, &refutation_presented));
    control.push((
        "refutation.certify_vc",
        verdict(honest_refutation.is_some(), "certify_vc", ("returned evidence", "returned None")),
    ));
    let replayed = honest_presented.as_ref().is_some_and(|evidence| {
        replay_presented_vc_evidence(&refutation_presented, evidence)
            && reference_certificate_for(evidence).is_some()
    });
    control.push((
        "refutation.replay",
        verdict(
            replayed,
            "replay_presented_vc_evidence, cold under a recomputed lineage, then reference_certificate_for:",
            ("true, then a certificate", "false, or no certificate"),
        ),
    ));
    let rechecked = honest_presented
        .as_ref()
        .is_some_and(|evidence| recheck_presented_linear_int_vc(&refutation_presented, evidence));
    control.push((
        "refutation.linear_int",
        verdict(rechecked, "recheck_presented_linear_int_vc", RETURNED_BOOL),
    ));
    let honest_let_rec = let_rec_lanes(
        HONEST_LET_REC_SOURCE,
        "p3_letrec_honest_src",
        "true",
        "p3_letrec_honest",
        failures,
    );
    control.extend(
        [
            "let_rec.island",
            "let_rec.batch",
            "let_rec.audited",
            "let_rec.reference",
            "let_rec.registered",
            "let_rec.grade",
            "let_rec_parent.audited",
            "let_rec_parent.reference",
            "let_rec_parent.registered",
            "let_rec_parent.grade",
        ]
        .into_iter()
        .zip(honest_let_rec),
    );
    Honest { control, refutation: honest_refutation, presented_for: refutation_presented }
}
