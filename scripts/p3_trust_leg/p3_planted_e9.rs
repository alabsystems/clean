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
//! * `trust.reference_mint.check_island_judgment_in.universe`: the other
//!   branch of the island's anonymous-judgment check (`IslandReference::
//!   check_judgment` is crate-private; this is its public kernel path), on
//!   `∀ (_ : Sort u), False` proved by `fun _ => p3_planted`: a universe
//!   parameter sends it through the entry's `add_checked`.
//! * `trust.e9.grade.kernel_discharge_ensures_citation`: the E9 grade the
//!   compiler's cited lane reads before it routes the clause and mints
//!   (`kernel_discharge_ensures_citation_in`, then `cert_meter::grade`). The
//!   compiler climbs the conditional rungs only when this grade fails, so the
//!   planted pair never reaches them.
//! * `trust.e9.domains.*`: the exact-domain E9 mint
//!   (`certify_ensures_discharge_with_domains`), the same three stages as the
//!   scalar lane above. Nothing in the compiler calls this lane at the
//!   measured Trust (it mints through the scalar lane only), and its fenced
//!   entry is the same `check_closed_in` call on the same pair as
//!   `trust.e9.reference_entry` and `trust.reference_mint.check_closed_in`.
//! * `trust.island.example_source`, `trust.island_batch.example_source`:
//!   `example : False := Nat.zero` through the island door and the batched
//!   door (`CleanIslandSession::check_all`), the feeders of
//!   `IslandReference::check_judgment`. Like `trust.island.source`, the
//!   elaborator's `is_def_eq` refuses it in both legs.
//! * `trust.calculus.*`: a calculus row (`certify_calculus_row`) over a
//!   STAND-IN VF5 family admitted by `calculus_row::test_support::
//!   pin_own_digest` (Trust's `calculus-row-test-support` feature; no
//!   production pin admits any base today). `producer_annotation` hands the
//!   planted pair to the row as the producer's annotation, judged as an
//!   application argument (by `is_le`, not `check_type`), so both legs refuse;
//!   `certify_calculus_row` and `registered_bound` cite the resident
//!   `p3_planted` from the family's `row_of`. The test registers the
//!   certificate itself (`calculus_row::register`, as the compiler's own
//!   calculus tests do: no Trust code path certifies or registers a calculus
//!   row at the measured Trust), and `registered_bound` is the compiler's
//!   lookup (`calculus_row_certificate_bound`) on it.
//! * `trust.refutation.*`: presented violation-refutation evidence. The
//!   honest certificate for `x < 0 ∧ 0 < x` (`certify_vc`) is presented again
//!   with its term replaced by `Nat.zero` and its lineage recomputed (an
//!   unkeyed hash, reimplemented here). `replay_presented_vc_evidence` and
//!   `reference_certificate_for` read the reference entry, which judges the
//!   term closed over the obligation's hypotheses, a shape M1 does not match;
//!   `recheck_presented_linear_int_vc` checks the open term at `False` and
//!   consults no reference entry. Where the replay is refused is measured by
//!   the runner, not here: it runs this test with `TRUST_KR0_DEBUG=1`, Trust's
//!   measurement-only report of each reference-entry refusal (lane `int`).
//!
//! Controls run in both legs and must pass, or the leg measures nothing
//! (`P3 VACUOUS`): the honest source `theorem p3_honest_src : True :=
//! True.intro` is accepted by the island door, `ensures true by p3_honest`
//! reaches a registered certificate through both E9 mints and is graded
//! certified, `∀ (_ : Sort u), True` by `fun _ =>
//! p3_honest` passes the universe branch, `example : True := True.intro`
//! passes both doors, the honest stand-in family certifies and binds a
//! calculus row, and the honest refutation certificate is issued, replayed
//! cold under a recomputed lineage (which checks the reimplemented hash) and
//! rechecked by the linear-Int lane.
//!
//! Every pin, control and row is printed (`P3_TRUST_PIN`, `P3_TRUST_CONTROL`,
//! `P3_TRUST`) before anything is asserted, so a red run still shows the whole
//! measurement; the runner refuses a leg whose printed rows do not match the
//! printed pins site for site.

use clean_auto::bridge::ay_contract::serialize_term;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, Level, Name, ReferenceKernel, TheoryId, TypeChecker,
};
use sha2::{Digest, Sha256};
use trust_certify::calculus_row::{
    self, CalculusRowClaim, Vf5Reference, certify_calculus_row, test_support,
};
use trust_certify::clean_island::{
    CitationVerdict, CleanIslandDiagnostic, CleanIslandSession, EnsuresDischargeClause,
    EnsuresDischargeRoute, certify_ensures_discharge, certify_ensures_discharge_with_domains,
    check_clean_island, kernel_discharge_ensures_citation_in,
};
use trust_certify::reference_mint::{
    check_closed_in, check_island_judgment_in, check_registered_in,
};
use trust_certify::{
    certify_vc, recheck_presented_linear_int_vc, reference_certificate_for,
    replay_presented_vc_evidence,
};
use trust_spec_elab::{FacetTable, ProofClauseInputs};
use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

const MODE_ENV: &str = "CLEAN_P3_KERNEL_UNDER_TEST";
const MUTANT_ID: &str = "check-type-nat-zero-false";
const FUNCTION: &str = "p3_trust_leg_fn";
const PLANTED_SOURCE: &str = "theorem p3_planted_src : False := Nat.zero\n";
const HONEST_SOURCE: &str = "theorem p3_honest_src : True := True.intro\n";
const PLANTED_EXAMPLE: &str = "example : False := Nat.zero\n";
const HONEST_EXAMPLE: &str = "example : True := True.intro\n";
const CALCULUS_ARTIFACT: &[u8] = b"p3-calculus-row-artifact";
/// Trust's `LINEAGE_DOMAIN` (`trust-certify/src/lib.rs`).
const LINEAGE_DOMAIN: &[u8] = b"trust-certify.cleancic.v3";

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
    ("trust.reference_mint.check_island_judgment_in.universe", Outcome::Refused, Outcome::Minted),
    ("trust.e9.grade.kernel_discharge_ensures_citation", Outcome::Refused, Outcome::Minted),
    ("trust.e9.domains.certify_ensures_discharge_with_domains", Outcome::Refused, Outcome::Minted),
    ("trust.e9.domains.reference_entry", Outcome::Refused, Outcome::Minted),
    ("trust.e9.domains.registered_certificate", Outcome::Refused, Outcome::Minted),
    ("trust.island.example_source", Outcome::Refused, Outcome::Refused),
    ("trust.island_batch.example_source", Outcome::Refused, Outcome::Refused),
    ("trust.calculus.producer_annotation", Outcome::Refused, Outcome::Refused),
    ("trust.calculus.certify_calculus_row", Outcome::Refused, Outcome::Minted),
    ("trust.calculus.registered_bound", Outcome::Refused, Outcome::Minted),
    ("trust.refutation.replay_presented_vc_evidence", Outcome::Refused, Outcome::Refused),
    ("trust.refutation.reference_certificate", Outcome::Refused, Outcome::Refused),
    ("trust.refutation.recheck_presented_linear_int_vc", Outcome::Refused, Outcome::Minted),
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

/// Which E9 mint issues the certificate: the scalar lane, or the exact-domain
/// lane (no parameters, so no domain is involved).
#[derive(Debug, Clone, Copy)]
enum E9Mint {
    Scalar,
    Domains,
}

/// The E9 lane end to end for `ensures <clause> by <theorem>`. Each stage that
/// yields nothing stops the chain; the rows say which. Anything that is
/// neither a mint nor a refusal is pushed to `failures`.
fn e9_lane(
    env: &Environment,
    mint: E9Mint,
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
            certify_ensures_discharge(env, &clauses, &[], FUNCTION, &inputs),
            "certify_ensures_discharge",
        ),
        E9Mint::Domains => (
            certify_ensures_discharge_with_domains(env, &clauses, &[], FUNCTION),
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
    let vc = row_for(FUNCTION);
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
fn e9_grade(env: &Environment, clause: &str, theorem: &str) -> (Outcome, String) {
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
fn universe_judgment(conclusion: &str, body: &str) -> (Expr, Expr) {
    let sort_u = || Expr::sort(Level::param(Name::from_string("u")));
    (
        Expr::pi(BinderInfo::Default, sort_u(), Expr::const_str(conclusion)),
        Expr::lam(BinderInfo::Default, sort_u(), Expr::const_str(body)),
    )
}

fn island_judgment(
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
fn is_example_mismatch(message: &str) -> bool {
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

fn island_example(source: &str) -> (Outcome, String) {
    let outcome = check_clean_island(source);
    judged(outcome.is_rejected(), outcome.anonymous_judgments, &outcome.errors)
}

fn batch_example(source: &str) -> (Outcome, String) {
    let mut session = CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    let anonymous: usize = batch.outcomes.iter().map(|outcome| outcome.anonymous_judgments).sum();
    let errors: Vec<CleanIslandDiagnostic> =
        batch.outcomes.iter().flat_map(|outcome| outcome.errors.iter().cloned()).collect();
    judged(batch.is_rejected(), anonymous, &errors)
}

fn konst(name: &str) -> Expr {
    Expr::const_str(name)
}

fn konst_at(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

fn list_nat() -> Expr {
    Expr::app(konst_at("List", vec![Level::zero()]), konst("Nat"))
}

fn pi(ty: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, ty, body)
}

fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

fn eq_true(lhs: Expr) -> Expr {
    Expr::apps(
        konst_at("Eq", vec![Level::succ(Level::zero())]),
        [konst("Bool"), lhs, konst("Bool.true")],
    )
}

fn definition(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: false,
    }
}

/// A VF5-shaped STAND-IN family over a clone of `env`, in the shape of
/// `calculus_row::test_support::toy_kernel` with the annotation binder typed
/// `annotation_type`: `checkBlob` and `rowShape` always true, `RowProved _ _ _
/// _ := row_prop`, and `row_of .. _ _ := witness`. Admitted under a pin of its
/// own digest (`test_support::pin_own_digest`), which no production pin is.
fn calculus_base(
    env: &Environment,
    annotation_type: &str,
    row_prop: &str,
    witness: &str,
) -> Result<Vf5Reference, String> {
    if env.get_const(&Name::from_string(witness)).is_none() {
        return Err(format!("{witness} absent: row_of has no witness to cite"));
    }
    let mut base = env.clone();
    let a = || konst(annotation_type);
    let decls = [
        definition(
            "VF5.checkBlob",
            pi(list_nat(), pi(a(), pi(konst("Nat"), konst("Bool")))),
            lam(list_nat(), lam(a(), lam(konst("Nat"), konst("Bool.true")))),
        ),
        definition(
            "VF5.rowShape",
            pi(list_nat(), pi(a(), pi(konst("Nat"), pi(list_nat(), konst("Bool"))))),
            lam(list_nat(), lam(a(), lam(konst("Nat"), lam(list_nat(), konst("Bool.true"))))),
        ),
        definition(
            "VF5.RowProved",
            pi(list_nat(), pi(a(), pi(konst("Nat"), pi(list_nat(), Expr::prop())))),
            lam(list_nat(), lam(a(), lam(konst("Nat"), lam(list_nat(), konst(row_prop))))),
        ),
    ];
    for decl in decls {
        base.add_decl(decl)
            .map_err(|error| format!("the stand-in family is refused: {error:?}"))?;
    }
    // Binders, outermost first: bs A cs fid sym h hs.
    let check =
        eq_true(Expr::apps(konst("VF5.checkBlob"), [Expr::bvar(4), Expr::bvar(3), Expr::bvar(2)]));
    let shape = eq_true(Expr::apps(
        konst("VF5.rowShape"),
        [Expr::bvar(5), Expr::bvar(4), Expr::bvar(2), Expr::bvar(1)],
    ));
    let row = Expr::apps(
        konst("VF5.RowProved"),
        [Expr::bvar(6), Expr::bvar(5), Expr::bvar(3), Expr::bvar(2)],
    );
    let binders = |tail: Expr, wrap: fn(Expr, Expr) -> Expr| {
        wrap(list_nat(), wrap(a(), wrap(konst("Nat"), wrap(konst("Nat"), wrap(list_nat(), tail)))))
    };
    let type_ = binders(pi(check.clone(), pi(shape.clone(), row)), pi);
    let value = binders(lam(check, lam(shape, konst(witness))), lam);
    base.add_decl(Declaration::Theorem {
        name: Name::from_string("VF5.row_of"),
        level_params: vec![],
        type_,
        value,
    })
    .map_err(|error| format!("the stand-in row_of is refused: {error:?}"))?;
    let kernel = ReferenceKernel::new(base)
        .map_err(|refusal| format!("the entry refused the base: {refusal:?}"))?;
    test_support::pin_own_digest(kernel).map_err(|miss| format!("pin_own_digest: {miss:?}"))
}

/// One calculus row end to end: the certificate, then the compiler's bound
/// lookup (`calculus_row_certificate_bound`, which its `CalculusRowProved`
/// mint reads).
fn calculus_lane(
    reference: &Vf5Reference,
    symbol: &[u8],
    annotation: &Expr,
    failures: &mut Vec<String>,
) -> Result<[(Outcome, String); 2], String> {
    let claim =
        CalculusRowClaim { artifact: CALCULUS_ARTIFACT.to_vec(), fid: 0, symbol: symbol.to_vec() };
    let certificate = certify_calculus_row(reference, &claim, annotation, &Expr::nat_lit(0))
        .map_err(|miss| format!("{miss:?}"))?;
    let theory = certificate.reference().theory_id();
    if theory != TheoryId::LeanReferenceV1 {
        failures.push(format!("P3 UNEXPECTED THEORY: the calculus certificate names {theory:?}"));
    }
    let certified =
        (Outcome::Minted, format!("CalculusRowCertificate (ReferenceCertificate in {theory:?})"));
    calculus_row::register(certificate.clone());
    let registered = match calculus_row::calculus_row_certificate_bound(symbol, CALCULUS_ARTIFACT) {
        Some(found) if found == certificate => (
            Outcome::Minted,
            "calculus_row_certificate_bound returns it, the precondition of the compiler's CalculusRowProved mint"
                .to_string(),
        ),
        Some(other) => {
            failures.push(format!(
                "P3 UNEXPECTED CERTIFICATE: the bound lookup returned {other:?}, not the one registered"
            ));
            (Outcome::Refused, "calculus_row_certificate_bound returned another certificate".to_string())
        }
        None => (Outcome::Refused, "calculus_row_certificate_bound returned None".to_string()),
    };
    if calculus_row::calculus_row_certificate_bound(symbol, b"other artifact bytes").is_some() {
        failures.push(
            "P3 UNEXPECTED CERTIFICATE: the bound lookup ignored the artifact bytes".to_string(),
        );
    }
    Ok([certified, registered])
}

/// The violation `x < 0 ∧ 0 < x` over `Int`, the linear-Int lane's shape.
fn refutation_vc(function: &str) -> VerificationCondition {
    let x = || Formula::Var("p3_refutation_x".into(), Sort::Int);
    VerificationCondition {
        kind: VcKind::Assertion { message: "p3 refutation fixture".into() },
        function: trust_types::Symbol::intern(function),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
        ]),
        contract_metadata: None,
        obligation: None,
    }
}

/// Trust's `CleanCic` lineage digest (`lineage_digest` over
/// `ObligationIdentity::from_vc`), reimplemented: SHA-256 over the domain tag
/// and the length-prefixed term, context and `vc:\0`-tagged bincode VC. It is
/// unkeyed, so it binds a payload to a row but does not authenticate who
/// produced it; the honest cold replay control checks this copy is exact.
fn lineage(term: &[u8], context: &[u8], vc: &VerificationCondition) -> trust_ir::ProofDigest {
    let mut identity = b"vc:\0".to_vec();
    bincode::serialize_into(&mut identity, vc).expect("a verification condition serializes");
    let mut hasher = Sha256::new();
    hasher.update(LINEAGE_DOMAIN);
    for field in [term, context, identity.as_slice()] {
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    trust_ir::ProofDigest::sha256(hasher.finalize().into())
}

/// `evidence` presented for `vc` with its term replaced by `term`.
fn presented(
    evidence: &trust_ir::ProofEvidence,
    term: Option<Vec<u8>>,
    vc: &VerificationCondition,
) -> Option<trust_ir::ProofEvidence> {
    let mut evidence = evidence.clone();
    let trust_ir::ProofEvidence::CleanCic { term: bytes, context, lineage: digest, .. } =
        &mut evidence
    else {
        return None;
    };
    if let Some(term) = term {
        *bytes = term;
    }
    *digest = lineage(bytes, context, vc);
    Some(evidence)
}

/// A yes/no entry's answer as a row: `entry` and what it returned.
fn verdict(minted: bool, entry: &str, (yes, no): (&str, &str)) -> (Outcome, String) {
    if minted {
        (Outcome::Minted, format!("{entry} {yes}"))
    } else {
        (Outcome::Refused, format!("{entry} {no}"))
    }
}

const RETURNED_BOOL: (&str, &str) = ("returned true", "returned false");
const RETURNED_SOME: (&str, &str) = ("returned a certificate", "returned None");

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

    // Controls: every honest counterpart mints.
    let mut control = vec![("island", island(HONEST_SOURCE, "p3_honest_src"))];
    match env.add_decl(theorem("p3_honest", "True", "True.intro")) {
        Ok(()) => {
            let honest = e9_lane(&env, E9Mint::Scalar, "true", "p3_honest", &mut failures);
            control.extend(["audited", "reference", "registered"].into_iter().zip(honest));
            let honest = e9_lane(&env, E9Mint::Domains, "true", "p3_honest", &mut failures);
            control.extend(
                ["domains.audited", "domains.reference", "domains.registered"]
                    .into_iter()
                    .zip(honest),
            );
            control.push(("grade", e9_grade(&env, "true", "p3_honest")));
            let (goal, proof) = universe_judgment("True", "p3_honest");
            let universe =
                island_judgment(&env, &goal, &proof).unwrap_or_else(|why| (Outcome::Refused, why));
            control.push(("island_judgment_universe", universe));
            let honest_calculus =
                calculus_base(&env, "True", "True", "p3_honest").and_then(|reference| {
                    calculus_lane(
                        &reference,
                        b"p3_calculus_honest",
                        &konst("True.intro"),
                        &mut failures,
                    )
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
    let lane = e9_lane(&env, E9Mint::Scalar, "false", "p3_planted", &mut failures);
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

    // The universe branch of the island's judgment check, citing the resident
    // theorem. Not resident: the kernel finds no `p3_planted`; resident, only
    // the planted mismatch (from the entry's re-check of it) is expected.
    let (goal, proof) = universe_judgment("False", "p3_planted");
    let universe = island_judgment(&env, &goal, &proof).unwrap_or_else(|detail| {
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

    let (outcome, detail) = e9_grade(&env, "false", "p3_planted");
    let expected =
        if resident { is_planted_mismatch(&detail) } else { detail.contains("TheoremNotFound") };
    if outcome == Outcome::Refused && !expected {
        failures.push(format!(
            "P3 UNEXPECTED REFUSAL: trust.e9.grade.kernel_discharge_ensures_citation: {detail}"
        ));
    }
    rows.push(("trust.e9.grade.kernel_discharge_ensures_citation", outcome, detail));

    let lane = e9_lane(&env, E9Mint::Domains, "false", "p3_planted", &mut failures);
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
    let annotation = match calculus_base(&env, "False", "True", "p3_honest") {
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
                &mut failures,
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
    let cited = calculus_base(&env, "True", "False", "p3_planted").and_then(|reference| {
        calculus_lane(&reference, b"p3_calculus_planted_base", &konst("True.intro"), &mut failures)
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
    let planted_presented = match (&honest_refutation, serialize_term(&konst("Nat.zero")).ok()) {
        (Some(evidence), Some(term)) => presented(evidence, Some(term), &refutation_presented),
        _ => None,
    };
    let refutation_rows = match &planted_presented {
        Some(evidence) => [
            verdict(
                replay_presented_vc_evidence(&refutation_presented, evidence),
                "replay_presented_vc_evidence",
                RETURNED_BOOL,
            ),
            verdict(
                reference_certificate_for(evidence).is_some(),
                "reference_certificate_for",
                RETURNED_SOME,
            ),
            verdict(
                recheck_presented_linear_int_vc(&refutation_presented, evidence),
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
