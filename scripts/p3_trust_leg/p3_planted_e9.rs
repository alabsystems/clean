// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! P3, Trust leg: the planted proof of `False` through `trust-certify`'s
//! island door and its E9 lane, which ends in the `ReferenceCertificate` the
//! compiler's `Certified` mint requires (`trust_certify::reference_certificate_for`).
//!
//! This file belongs to Clean (`scripts/p3_trust_leg/`), not to Trust: Clean's
//! `scripts/patched_kernel_control_trust.py` copies it into a scratch copy of
//! Trust's tree as `crates/trust-certify/tests/p3_planted_e9.rs`, once over an
//! unmodified `first-party/clean` and once over the copy whose
//! `TypeChecker::check_type` also accepts `Nat.zero : False` (P3's mutant M1),
//! and runs it in each. Nothing of it lands in Trust.
//!
//! The sites, in order:
//!
//! * `trust.island.source`: the planted SOURCE through Trust's island door
//!   (`check_clean_island`). Its elaborator compares a body with its type by
//!   `is_def_eq`, which M1 does not touch, so it is expected to refuse in both
//!   legs: that refusal is the same kernel's other entry, not an independent
//!   check (a mutant one function over would pass it).
//! * `kernel.add_decl`: the planted theorem made resident in the island
//!   environment through clean-kernel's own door, `Environment::add_decl`. No
//!   Trust code runs here; it stands in for an island constant that reached the
//!   environment, which the island door above does not let this source do. The
//!   rows after it are therefore conditional on that residency.
//! * `trust.island.reference_recheck`: the island's reference gate
//!   (`reference_mint::check_registered_in`) on the resident constant.
//! * `trust.e9.certify_ensures_discharge`, `trust.e9.reference_entry`,
//!   `trust.e9.registered_certificate`: `ensures false by p3_planted` through
//!   the E9 lane: the audited certificate, the fenced entry's certificate on
//!   it, and the certificate the compiler reads back for the row's payload. In
//!   Trust's Rust contract surface `false` in proposition position elaborates
//!   to Lean's `False`; the test asks the elaborator and fails unless the goal
//!   is exactly the constant `False`, the type M1 accepts `Nat.zero` at.
//! * `trust.reference_mint.check_closed_in`: the fenced entry asked directly
//!   about the closed pair, whatever is resident.
//!
//! Controls run in both legs and must pass, or the leg measures nothing
//! (`P3 VACUOUS`): the honest source `theorem p3_honest_src : True :=
//! True.intro` is accepted by the island door, and `ensures true by p3_honest`
//! reaches a registered certificate through the E9 lane.
//!
//! Every pin, control and row is printed (`P3_TRUST_PIN`, `P3_TRUST_CONTROL`,
//! `P3_TRUST`) before anything is asserted, so a red run still shows the whole
//! measurement; the runner refuses a leg whose printed rows do not match the
//! printed pins site for site.

use clean_kernel::{Declaration, Environment, Expr, Name, TheoryId, TypeChecker};
use trust_certify::clean_island::{
    EnsuresDischargeClause, EnsuresDischargeRoute, certify_ensures_discharge, check_clean_island,
};
use trust_certify::reference_certificate_for;
use trust_certify::reference_mint::{check_closed_in, check_registered_in};
use trust_spec_elab::{FacetTable, ProofClauseInputs};
use trust_types::{Formula, SourceSpan, VcKind, VerificationCondition};

const MODE_ENV: &str = "CLEAN_P3_KERNEL_UNDER_TEST";
const MUTANT_ID: &str = "check-type-nat-zero-false";
const FUNCTION: &str = "p3_trust_leg_fn";
const PLANTED_SOURCE: &str = "theorem p3_planted_src : False := Nat.zero\n";
const HONEST_SOURCE: &str = "theorem p3_honest_src : True := True.intro\n";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kernel {
    Unmodified,
    Mutant,
}

impl Kernel {
    fn declared() -> Self {
        match std::env::var(MODE_ENV) {
            Err(std::env::VarError::NotPresent) => Self::Unmodified,
            Ok(value) if value == MUTANT_ID => Self::Mutant,
            other => panic!("{MODE_ENV} must be unset or `{MUTANT_ID}`, got {other:?}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    Minted,
    Refused,
}

/// The outcome each site is pinned to, per declared kernel: (site, unmodified,
/// mutant). A mutant `Minted` is a named gap: the day the site gains a check
/// independent of `clean-kernel`, the mutant leg reports `P3 KNOWN GAP CLOSED`
/// and stays red until this table moves; the runner then re-mints the record,
/// which carries these pins and this file's digest.
const PINS: &[(&str, Outcome, Outcome)] = &[
    ("trust.island.source", Outcome::Refused, Outcome::Refused),
    ("kernel.add_decl", Outcome::Refused, Outcome::Minted),
    ("trust.island.reference_recheck", Outcome::Refused, Outcome::Minted),
    ("trust.e9.certify_ensures_discharge", Outcome::Refused, Outcome::Minted),
    ("trust.e9.reference_entry", Outcome::Refused, Outcome::Minted),
    ("trust.e9.registered_certificate", Outcome::Refused, Outcome::Minted),
    ("trust.reference_mint.check_closed_in", Outcome::Refused, Outcome::Minted),
];

fn theorem(name: &str, type_: &str, value: &str) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::const_str(type_),
        value: Expr::const_str(value),
    }
}

fn row_for(function: &str) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Postcondition,
        function: trust_types::Symbol::intern(function),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }
}

fn is_planted_mismatch(message: &str) -> bool {
    message.contains("Type mismatch: expected False, got Nat")
        || (message.contains("TypeMismatch")
            && message.contains("False")
            && message.contains("Nat"))
}

/// The goal Trust's elaborator builds for an `ensures` clause of a function
/// with no parameters, through the entry the E9 lane calls
/// (`elaborate_ensures_in`, with this test's facet table and inputs).
fn elaborated_goal(clause: &str) -> Result<Expr, String> {
    trust_spec_elab::elaborate_ensures_in(
        clause,
        &[],
        FUNCTION,
        &FacetTable::new(),
        &ProofClauseInputs::strict(),
    )
    .map(|elaborated| elaborated.goal)
}

/// The island door on one source: accepted when the theorem is registered and
/// the island is not rejected.
fn island(source: &str, theorem: &str) -> (Outcome, String) {
    let outcome = check_clean_island(source);
    if !outcome.is_rejected() && outcome.registered.iter().any(|name| name == theorem) {
        (Outcome::Minted, format!("registered {:?}", outcome.registered))
    } else {
        let errors: Vec<String> = outcome.errors.iter().map(|error| format!("{error:?}")).collect();
        (Outcome::Refused, format!("rejected: {}", errors.join(" | ")))
    }
}

/// The E9 lane end to end for `ensures <clause> by <theorem>`. Each stage that
/// yields nothing stops the chain; the rows say which. Anything that is
/// neither a mint nor a refusal is pushed to `failures`.
fn e9_lane(
    env: &Environment,
    clause: &str,
    theorem: &str,
    failures: &mut Vec<String>,
) -> [(Outcome, String); 3] {
    let facets = FacetTable::new();
    let inputs = ProofClauseInputs::strict();
    let clauses = [EnsuresDischargeClause {
        clause_src: clause,
        route: EnsuresDischargeRoute::CitedTheorem(theorem),
        facets: &facets,
    }];
    let refused = |why: &str| (Outcome::Refused, why.to_string());
    let Some(certificate) = certify_ensures_discharge(env, &clauses, &[], FUNCTION, &inputs) else {
        let none =
            "certify_ensures_discharge returned None (elaboration, lookup or audit_certification)";
        return [
            refused(none),
            refused("no certificate to check"),
            refused("no certificate to register"),
        ];
    };
    let audited =
        (Outcome::Minted, "EnsuresDischargeCertificate (audit_certification clean)".to_string());
    let Some(reference) = certificate.reference() else {
        return [
            audited,
            refused("the fenced entry refused the audited judgment (reference None)"),
            refused("nothing to register"),
        ];
    };
    if reference.theory_id() != TheoryId::LeanReferenceV1 {
        failures.push(format!(
            "P3 UNEXPECTED THEORY: the fenced entry's certificate for `{clause}` names {:?}",
            reference.theory_id()
        ));
    }
    let entry = (Outcome::Minted, format!("ReferenceCertificate in {:?}", reference.theory_id()));
    let vc = row_for(FUNCTION);
    let Some(evidence) = certificate.evidence_for_row(&vc) else {
        return [audited, entry, refused("evidence_for_row returned None")];
    };
    let registered = match reference_certificate_for(&evidence) {
        Some(found) if &found == reference => (
            Outcome::Minted,
            "reference_certificate_for returns the registered certificate, the precondition of the compiler's Certified mint".to_string(),
        ),
        Some(other) => {
            failures.push(format!(
                "P3 UNEXPECTED CERTIFICATE: reference_certificate_for returned {other:?}, not the one registered"
            ));
            refused("reference_certificate_for returned another certificate")
        }
        None => refused("reference_certificate_for returned None"),
    };
    [audited, entry, registered]
}

#[test]
fn p3_planted_false_through_trust_certify_e9_lane() {
    let declared = Kernel::declared();
    let mut failures = Vec::new();
    let mut env = Environment::with_prelude();
    for (site, unmodified, mutant) in PINS {
        println!("P3_TRUST_PIN\t{site}\t{unmodified:?}\t{mutant:?}");
    }

    // Liveness: does the linked kernel accept the planted pair?
    let checker = TypeChecker::new(&env);
    let honest_pair = checker.check_type(&Expr::const_str("True.intro"), &Expr::const_str("True"));
    let planted_pair = checker.check_type(&Expr::const_str("Nat.zero"), &Expr::const_str("False"));
    drop(checker);
    let live = planted_pair.is_ok();
    println!("P3_TRUST_KERNEL\tdeclared={declared:?}\tlive={live}");
    if let Err(error) = &honest_pair {
        failures
            .push(format!("P3 VACUOUS: the linked kernel refuses `True.intro : True`: {error:?}"));
    }
    if let Err(error) = &planted_pair
        && !is_planted_mismatch(&format!("{error:?}"))
    {
        failures.push(format!(
            "P3 UNEXPECTED REFUSAL: the linked kernel refuses the planted pair by {error:?}, not the type mismatch"
        ));
    }
    match (declared, live) {
        (Kernel::Unmodified, true) => failures.push(format!(
            "P3 WRONG ACCEPT: {MODE_ENV} is unset, but the linked clean-kernel accepts the planted pair"
        )),
        (Kernel::Mutant, false) => failures.push(format!(
            "P3 MUTATION NOT LIVE: {MODE_ENV}={MUTANT_ID}, but the linked clean-kernel refuses the planted pair"
        )),
        _ => {}
    }

    // The clauses state exactly the constants the pairs are typed at.
    for (clause, constant) in [("true", "True"), ("false", "False")] {
        let goal = elaborated_goal(clause);
        println!("P3_TRUST_GOAL\t{clause}\t{goal:?}");
        if goal.as_ref().ok() != Some(&Expr::const_str(constant)) {
            failures.push(format!(
                "P3 GOAL NOT {constant}: the clause `{clause}` must elaborate to the constant `{constant}`, got {goal:?}"
            ));
        }
    }

    // Controls: the honest source and the honest E9 judgment both mint.
    let mut control = vec![("island", island(HONEST_SOURCE, "p3_honest_src"))];
    match env.add_decl(theorem("p3_honest", "True", "True.intro")) {
        Ok(()) => {
            let honest = e9_lane(&env, "true", "p3_honest", &mut failures);
            control.extend(["audited", "reference", "registered"].into_iter().zip(honest));
        }
        Err(error) => {
            failures.push(format!("P3 VACUOUS: the honest theorem is refused: {error:?}"))
        }
    }
    for (stage, (outcome, detail)) in &control {
        println!("P3_TRUST_CONTROL\t{stage}\t{outcome:?}\t{detail}");
        if *outcome != Outcome::Minted {
            failures
                .push(format!("P3 VACUOUS: the control stage `{stage}` did not mint: {detail}"));
        }
    }

    // The planted pair.
    let mut rows: Vec<(&str, Outcome, String)> = Vec::new();
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
    let recheck = match check_registered_in(&env, &Name::from_string("p3_planted")) {
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
    let lane = e9_lane(&env, "false", "p3_planted", &mut failures);
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
    let direct =
        match check_closed_in(&env, &Expr::const_str("False"), &Expr::const_str("Nat.zero")) {
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

    for (site, outcome, detail) in &rows {
        println!("P3_TRUST\t{site}\t{outcome:?}\t{detail}");
    }

    // Compare with the pins for the declared kernel.
    let sites: Vec<&str> = rows.iter().map(|(site, _, _)| *site).collect();
    let pinned: Vec<&str> = PINS.iter().map(|(site, _, _)| *site).collect();
    if sites != pinned {
        failures.push(format!("P3 SITES MOVED: measured {sites:?}, pinned {pinned:?}"));
    }
    for ((site, outcome, detail), (_, unmodified, mutant)) in rows.iter().zip(PINS) {
        let pin = if declared == Kernel::Mutant { *mutant } else { *unmodified };
        match (pin, *outcome) {
            (Outcome::Refused, Outcome::Minted) => {
                failures.push(format!("P3 WRONG ACCEPT: {site}: {detail}"));
            }
            (Outcome::Minted, Outcome::Refused) => {
                failures.push(format!("P3 KNOWN GAP CLOSED: {site}: {detail}"));
            }
            (Outcome::Minted, Outcome::Minted) | (Outcome::Refused, Outcome::Refused) => {}
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
