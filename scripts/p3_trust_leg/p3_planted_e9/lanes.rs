// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The island doors and the E9 lane of `p3_planted_e9.rs`, installed beside it
//! (`p3_planted_e9/lanes.rs`): the helpers its controls and its planted rows share.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name, TheoryId};
use trust_certify::clean_island::{
    CitationVerdict, CleanIslandDiagnostic, CleanIslandSession, EnsuresDischargeClause,
    EnsuresDischargeRoute, certify_ensures_discharge, certify_ensures_discharge_with_domains,
    check_clean_island, kernel_discharge_ensures_citation_in,
};
use trust_certify::reference_certificate_for;
use trust_certify::reference_mint::check_island_judgment_in;
use trust_spec_elab::{FacetTable, ProofClauseInputs};
use trust_types::{Formula, SourceSpan, VcKind, VerificationCondition};

use crate::FUNCTION;
use crate::contract::{Outcome, is_planted_mismatch};

pub(crate) fn theorem(name: &str, type_: &str, value: &str) -> Declaration {
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
pub(crate) fn island(source: &str, theorem: &str) -> (Outcome, String) {
    let outcome = check_clean_island(source);
    if !outcome.is_rejected() && outcome.registered.iter().any(|name| name == theorem) {
        (Outcome::Minted, format!("registered {:?}", outcome.registered))
    } else {
        let errors: Vec<String> = outcome.errors.iter().map(|error| format!("{error:?}")).collect();
        (Outcome::Refused, format!("rejected: {}", errors.join(" | ")))
    }
}

/// Which E9 mint issues the certificate: the scalar lane, or the exact-domain
/// lane (no parameters, so no domain is involved).
#[derive(Debug, Clone, Copy)]
pub(crate) enum E9Mint {
    Scalar,
    Domains,
}

/// The E9 lane end to end for `ensures <clause> by <theorem>`. Each stage that
/// yields nothing stops the chain; the rows say which. Anything that is
/// neither a mint nor a refusal is pushed to `failures`.
pub(crate) fn e9_lane(
    env: &Environment,
    mint: E9Mint,
    clause: &str,
    theorem: &str,
    failures: &mut Vec<String>,
) -> [(Outcome, String); 3] {
    e9_lane_for(env, mint, FUNCTION, clause, theorem, failures)
}

/// [`e9_lane`] for the row of `function`.
fn e9_lane_for(
    env: &Environment,
    mint: E9Mint,
    function: &str,
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
    let (certificate, entry) = match mint {
        E9Mint::Scalar => (
            certify_ensures_discharge(env, &clauses, &[], function, &inputs),
            "certify_ensures_discharge",
        ),
        E9Mint::Domains => (
            certify_ensures_discharge_with_domains(env, &clauses, &[], function),
            "certify_ensures_discharge_with_domains",
        ),
    };
    let Some(certificate) = certificate else {
        let none = format!("{entry} returned None (elaboration, lookup or audit)");
        return [
            refused(&none),
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
    let vc = row_for(function);
    let Some(evidence) = certificate.evidence_for_row(&vc) else {
        return [audited, entry, refused("evidence_for_row returned None")];
    };
    let read_back = match mint {
        E9Mint::Scalar => {
            "reference_certificate_for returns the registered certificate, the precondition of the compiler's Certified mint"
        }
        E9Mint::Domains => {
            "reference_certificate_for returns the registered certificate (no compiler path produces this lane's evidence)"
        }
    };
    let registered = match reference_certificate_for(&evidence) {
        Some(found) if &found == reference => (Outcome::Minted, read_back.to_string()),
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

/// The E9 grade the compiler's cited lane reads before it routes the clause
/// to the cited theorem and mints (`cert_meter::grade`); the compiler asks the
/// conditional rungs only when this grade fails.
pub(crate) fn e9_grade(env: &Environment, clause: &str, theorem: &str) -> (Outcome, String) {
    match kernel_discharge_ensures_citation_in(
        env,
        theorem,
        clause,
        &[],
        FUNCTION,
        &FacetTable::new(),
        &ProofClauseInputs::strict(),
    ) {
        CitationVerdict::KernelStatementMatchCertified => (
            Outcome::Minted,
            "KernelStatementMatchCertified (cert_meter::grade certified)".to_string(),
        ),
        other => (Outcome::Refused, format!("{other:?}")),
    }
}

/// `∀ (_ : Sort u), conclusion` proved by `fun (_ : Sort u) => body`: a
/// judgment with a universe parameter, so the island's judgment check takes
/// its `add_checked` branch.
pub(crate) fn universe_judgment(conclusion: &str, body: &str) -> (Expr, Expr) {
    let sort_u = || Expr::sort(Level::param(Name::from_string("u")));
    (
        Expr::pi(BinderInfo::Default, sort_u(), Expr::const_str(conclusion)),
        Expr::lam(BinderInfo::Default, sort_u(), Expr::const_str(body)),
    )
}

pub(crate) fn island_judgment(
    env: &Environment,
    goal: &Expr,
    proof: &Expr,
) -> Result<(Outcome, String), String> {
    check_island_judgment_in(env, goal, proof)
        .map(|certificate| {
            (Outcome::Minted, format!("ReferenceCertificate in {:?}", certificate.theory_id()))
        })
        .map_err(|miss| format!("{miss:?}"))
}

/// The elaborator's refusal of the planted example body.
pub(crate) fn is_example_mismatch(message: &str) -> bool {
    is_planted_mismatch(message)
        || (message.contains("not definitionally equal")
            && message.contains("False")
            && message.contains("Nat"))
}

/// Minted only when the island is accepted with exactly one anonymous
/// judgment: `IslandReference::check_judgment` then ran on it and returned a
/// certificate. Messages are printed with `{:?}`, which escapes the tabs and
/// newlines of a batch rendering, so the runner's row parse stays four cells.
fn judged(rejected: bool, anonymous: usize, errors: &[CleanIslandDiagnostic]) -> (Outcome, String) {
    if !rejected && anonymous == 1 {
        (
            Outcome::Minted,
            "accepted, one anonymous judgment: IslandReference::check_judgment returned a certificate"
                .to_string(),
        )
    } else {
        let messages: Vec<&str> = errors.iter().map(|error| error.message.as_str()).collect();
        (Outcome::Refused, format!("rejected (anonymous_judgments={anonymous}): {messages:?}"))
    }
}

pub(crate) fn island_example(source: &str) -> (Outcome, String) {
    let outcome = check_clean_island(source);
    judged(outcome.is_rejected(), outcome.anonymous_judgments, &outcome.errors)
}

pub(crate) fn batch_example(source: &str) -> (Outcome, String) {
    let mut session = CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    let anonymous: usize = batch.outcomes.iter().map(|outcome| outcome.anonymous_judgments).sum();
    let errors: Vec<CleanIslandDiagnostic> =
        batch.outcomes.iter().flat_map(|outcome| outcome.errors.iter().cloned()).collect();
    judged(batch.is_rejected(), anonymous, &errors)
}

/// The single door's verdict on a `let rec` source: minted when the island is
/// accepted with both the parent and its lifted helper `<parent>.go` registered
/// (`check_clean_island` lists both).
fn let_rec_door(
    rejected: bool,
    registered: &[String],
    errors: &[CleanIslandDiagnostic],
    parent: &str,
) -> (Outcome, String) {
    let helper = format!("{parent}.go");
    let both = [parent, helper.as_str()]
        .iter()
        .all(|name| registered.iter().any(|registered| registered == name));
    if !rejected && both {
        (Outcome::Minted, format!("registered {registered:?}"))
    } else {
        let messages: Vec<&str> = errors.iter().map(|error| error.message.as_str()).collect();
        (Outcome::Refused, format!("rejected (registered {registered:?}): {messages:?}"))
    }
}

/// The kernel's refusal of the lifted helper: a type mismatch between `False`
/// and `Nat`, in whatever words the door renders it.
pub(crate) fn is_let_rec_mismatch(detail: &str) -> bool {
    let lower = detail.to_lowercase();
    lower.contains("mismatch") && lower.contains("false") && lower.contains("nat")
}

/// A `let rec` source through the single door, then the batched door, then,
/// on the batched door's session environment (the one the compiler stashes
/// for its in-walk E9 lane), its helper and its parent cited by `ensures
/// <clause>` through the scalar E9 lane and graded, each under a function name
/// of its own (`<tag>_helper_fn`, `<tag>_parent_fn`). Ten rows, in the order
/// of the `let_rec` pins.
pub(crate) fn let_rec_lanes(
    source: &str,
    parent: &str,
    clause: &str,
    tag: &str,
    failures: &mut Vec<String>,
) -> Vec<(Outcome, String)> {
    let single = check_clean_island(source);
    let mut rows =
        vec![let_rec_door(single.is_rejected(), &single.registered, &single.errors, parent)];
    let mut session = CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    let registered: Vec<String> =
        batch.outcomes.iter().flat_map(|outcome| outcome.registered.iter().cloned()).collect();
    let errors: Vec<CleanIslandDiagnostic> =
        batch.outcomes.iter().flat_map(|outcome| outcome.errors.iter().cloned()).collect();
    // The batched door reports each declaration by its surface name only (a
    // run on 2026-11-15 listed `[parent]` for an accepted batch), so the lifted
    // helper is looked up in the session environment the compiler stashes.
    let helper = format!("{parent}.go");
    let env = session.environment().filter(|env| {
        !batch.is_rejected()
            && registered.iter().any(|name| name == parent)
            && env.get_const(&Name::from_string(&helper)).is_some()
    });
    rows.push(match env {
        Some(_) => (
            Outcome::Minted,
            format!("registered {registered:?}; {helper} resident in the session environment"),
        ),
        None => {
            let messages: Vec<&str> = errors.iter().map(|error| error.message.as_str()).collect();
            (Outcome::Refused, format!("rejected (registered {registered:?}): {messages:?}"))
        }
    });
    for (cited, role) in [(helper.as_str(), "helper"), (parent, "parent")] {
        let function = format!("{tag}_{role}_fn");
        match env {
            Some(env) => {
                rows.extend(e9_lane_for(env, E9Mint::Scalar, &function, clause, cited, failures));
                rows.push(e9_grade(env, clause, cited));
            }
            None => {
                let none = "no session environment: the batched door refused the source";
                rows.extend(std::iter::repeat_n((Outcome::Refused, none.to_string()), 4));
            }
        }
    }
    rows
}

/// The clauses state exactly the constants the pairs are typed at: Trust's Rust
/// contract surface reads `true`/`false` in proposition position as Lean's
/// `True`/`False`, and the test fails unless the elaborator says so.
pub(crate) fn check_goals(failures: &mut Vec<String>) {
    for (clause, constant) in [("true", "True"), ("false", "False")] {
        let goal = elaborated_goal(clause);
        println!("P3_TRUST_GOAL\t{clause}\t{goal:?}");
        if goal.as_ref().ok() != Some(&Expr::const_str(constant)) {
            failures.push(format!(
            "P3 GOAL NOT {constant}: the clause `{clause}` must elaborate to the constant `{constant}`, got {goal:?}"
        ));
        }
    }
}
