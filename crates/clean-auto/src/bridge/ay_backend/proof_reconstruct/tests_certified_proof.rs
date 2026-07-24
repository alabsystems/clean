// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness tests for [`certify_reconstruction`].
//!
//! POSITIVE: a genuinely reconstructed unsat proof with
//! `trust_subterm_count == 0` certifies, and the serialized term re-checks to
//! `False` after a bincode round-trip.
//!
//! NEGATIVE (soundness): a proof that uses a `trustedAy` sub-term
//! (`trust_subterm_count > 0`), a proof that does not derive the empty clause,
//! a proof with unbound witnesses, an absent proof term, and a deliberately
//! malformed proof term — plus valid kernel terms backed by free axioms or
//! mutated authority state — each must return [`NotCertified`], NEVER a
//! [`CertifiedPayload`]. Bound assumptions remain certifiable.
//!
//! The reconstruction setup mirrors the unit-contradiction fixture in
//! `tests_e2e.rs`.

use super::super::{attempt_reconstruction, ReconstructionResult, VariableMapping};
use super::{
    certify_kernel_term, certify_reconstruction, deserialize_context, deserialize_term, false_expr,
    serialize_context, serialize_term, CertifiedPayload, NotCertified, ReducedContext,
    ReducedLocalDecl,
};
use ay::Sort;
use ay_core::{Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, CertificationIssue, Declaration, Environment, Expr, FVarId, Level, LocalContext,
    TypeChecker,
};

/// Environment with Eq, Nat, Not/absurd/False and no domain axioms.
fn mk_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    env
}

/// `@Eq.{1} Nat Nat.zero Nat.zero`.
fn mk_eq_prop() -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let b = a.clone();
    let u1 = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u1]), nat_ty),
            a,
        ),
        b,
    )
}

/// `Not (Eq Nat Nat.zero Nat.zero)`.
fn mk_neq_prop() -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), mk_eq_prop())
}

fn true_expr() -> Expr {
    Expr::const_(Name::from_string("True"), vec![])
}

fn complete_result(term: Expr) -> ReconstructionResult {
    ReconstructionResult {
        proof_term: Some(term),
        negated_goal_fvar: None,
        compound_witness_fvars: Vec::new(),
        derives_empty_clause: true,
        trust_subterm_count: 0,
        residual: crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSummary::empty(),
        stats: super::super::ReconstructionStats::default(),
    }
}

/// Build the unit-contradiction reconstruction and close it: returns the
/// reconstruction result (with any sentinel FVar substituted out of the proof
/// term) and a `LocalContext` containing every needed hypothesis.
///
/// This is exactly the e2e unit-contradiction setup; the resulting proof term
/// type-checks to `False`.
fn reconstruct_unit_contradiction() -> (Environment, ReconstructionResult, LocalContext) {
    let env = mk_env();
    let eq_prop = mk_eq_prop();
    let neq_prop = mk_neq_prop();

    let h_eq_id = FVarId::new(10);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let p = terms.mk_var("p", Sort::Bool);
    map.register_var("p", eq_prop.clone(), Expr::prop());
    map.register_hypothesis("p", h_eq_id, Expr::fvar(h_eq_id), eq_prop.clone());

    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(p, None);
    let h2 = proof.add_assume(not_p, None);
    proof.add_resolution(vec![], p, h1, h2);

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_eq_id,
        Name::from_string("h_eq"),
        eq_prop,
        BinderInfo::Default,
    );

    let mut result = attempt_reconstruction(&proof, &terms, &map, &neq_prop);

    // Close the proof term: replace any sentinel negated-goal FVar with a
    // normal FVarId that lives in the LocalContext.
    if let Some(sentinel_id) = result.negated_goal_fvar {
        let normal_neg_id = FVarId::new(20);
        let closed = result
            .proof_term
            .as_ref()
            .expect("unit contradiction should produce a proof term")
            .subst_fvar(sentinel_id, &Expr::fvar(normal_neg_id));
        result.proof_term = Some(closed);
        ctx.push_with_id(
            normal_neg_id,
            Name::from_string("h_neg"),
            neq_prop,
            BinderInfo::Default,
        );
    }

    (env, result, ctx)
}

/// Sanity: confirm the fixture is a genuine, fully-reconstructed proof — the
/// preconditions the certification gates depend on.
#[test]
fn test_unit_contradiction_fixture_is_fully_reconstructed() {
    let (_env, result, _ctx) = reconstruct_unit_contradiction();
    assert!(result.proof_term.is_some(), "fixture must produce a term");
    assert!(
        result.derives_empty_clause,
        "fixture must derive the empty clause"
    );
    assert!(
        result.compound_witness_fvars.is_empty(),
        "fixture must have no unbound witnesses"
    );
    assert_eq!(
        result.trust_subterm_count, 0,
        "fixture must not lean on trustedAy"
    );
}

/// POSITIVE: a reconstructed unsat proof certifies, and the serialized term
/// re-checks to `False` after a bincode round-trip.
#[test]
fn test_certify_unit_contradiction_yields_payload_and_roundtrips() {
    let (env, result, ctx) = reconstruct_unit_contradiction();

    let payload: CertifiedPayload = certify_reconstruction(&result, &env, &ctx)
        .expect("fully-reconstructed unsat proof should certify");

    assert_eq!(
        payload.trust_count, 0,
        "a CertifiedPayload always has trust_count == 0"
    );
    assert!(
        !payload.term_bytes.is_empty(),
        "term_bytes must be non-empty"
    );
    assert!(
        !payload.context_bytes.is_empty(),
        "context_bytes must be non-empty"
    );

    // Re-deserialize the term and reduced context, then re-run the FULL kernel
    // check (check_type, infer_only = false) — it must still type-check to False.
    let term = deserialize_term(&payload.term_bytes).expect("term should deserialize");
    let reduced = deserialize_context(&payload.context_bytes).expect("context should deserialize");
    let rebuilt_ctx = reduced.into_context();

    let tc = TypeChecker::with_context(&env, rebuilt_ctx);
    tc.check_type(&term, &false_expr())
        .expect("deserialized term must still kernel-check to False");

    // And the deserialized term equals the original proof term.
    assert_eq!(
        &term,
        result.proof_term.as_ref().expect("term present"),
        "round-trip must preserve the proof term"
    );
}

/// Canonical proof carriers reject a valid term prefix followed by arbitrary
/// unauthenticated envelope bytes.
#[test]
fn test_deserialize_term_rejects_trailing_bytes() {
    let mut bytes = serialize_term(&Expr::nat_lit(7)).expect("serialize term");
    bytes.extend_from_slice(b"trailing");

    let Err(NotCertified::SerializationFailed { message }) = deserialize_term(&bytes) else {
        panic!("term decoder must reject trailing bytes");
    };
    assert!(
        message.contains("non-canonical proof term encoding"),
        "{message}"
    );
}

/// Context decoding has the same exact-consumption rule as term decoding.
#[test]
fn test_deserialize_context_rejects_trailing_bytes() {
    let mut bytes =
        serialize_context(&ReducedContext { decls: Vec::new() }).expect("serialize context");
    bytes.extend_from_slice(b"trailing");

    let Err(NotCertified::SerializationFailed { message }) = deserialize_context(&bytes) else {
        panic!("context decoder must reject trailing bytes");
    };
    assert!(
        message.contains("non-canonical reduced-context encoding"),
        "{message}"
    );
}

/// Exact consumption is not canonicality: bincode accepts the non-minimal
/// three-byte U16 representation of the empty context's zero-length vector.
/// The shared decoder must reject that second spelling even though raw bincode
/// consumes the complete slice and produces the expected value.
#[test]
fn test_deserialize_context_rejects_nonminimal_varint() {
    let bytes = [251, 0, 0];
    let expected = ReducedContext { decls: Vec::new() };
    let (decoded, consumed): (ReducedContext, usize) =
        bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
            .expect("raw bincode accepts the non-minimal zero varint");
    assert_eq!(decoded, expected);
    assert_eq!(consumed, bytes.len());

    let Err(NotCertified::SerializationFailed { message }) = deserialize_context(&bytes) else {
        panic!("canonical context decoder must reject a non-minimal varint");
    };
    assert!(
        message.contains("non-canonical reduced-context encoding"),
        "{message}"
    );
}

#[test]
fn test_shared_codec_preserves_raw_bincode2_wire_contract() {
    let term = Expr::const_(
        Name::from_string("Poly.f"),
        vec![Level::succ(Level::param(Name::from_string("u")))],
    );
    let shared = serialize_term(&term).expect("shared term encoding");
    let raw = bincode::serde::encode_to_vec(&term, bincode::config::standard())
        .expect("raw bincode-2 term encoding");
    assert_eq!(
        shared, raw,
        "resource hardening must not change authenticated CleanCic term bytes"
    );
    let (decoded, consumed): (Expr, usize) =
        bincode::serde::decode_from_slice(&shared, bincode::config::standard())
            .expect("legacy raw consumer still decodes shared bytes");
    assert_eq!(consumed, shared.len());
    assert_eq!(decoded, term);
}

#[test]
fn test_deserialize_context_rejects_duplicate_ids_before_replay() {
    let decl = ReducedLocalDecl {
        id: 7,
        name: Name::from_string("x"),
        type_: Expr::sort(Level::zero()),
        value: None,
        bi: BinderInfo::Default.into(),
    };
    // Bypass the shared encoder: this models an attacker-supplied, otherwise
    // canonical bincode carrier.  LocalContext::push_with_id would panic on
    // the second declaration if the decoder admitted it.
    let bytes = bincode::serde::encode_to_vec(
        ReducedContext {
            decls: vec![decl.clone(), decl],
        },
        bincode::config::standard(),
    )
    .expect("raw context encoding");

    let Err(NotCertified::SerializationFailed { message }) = deserialize_context(&bytes) else {
        panic!("duplicate context ids must be rejected before into_context");
    };
    assert!(
        message.contains("duplicate local declaration id 7"),
        "{message}"
    );
}

#[test]
fn test_deserialize_context_rejects_reserved_sentinel_id() {
    let bytes = bincode::serde::encode_to_vec(
        ReducedContext {
            decls: vec![ReducedLocalDecl {
                id: u64::MAX,
                name: Name::from_string("x"),
                type_: Expr::sort(Level::zero()),
                value: None,
                bi: BinderInfo::Default.into(),
            }],
        },
        bincode::config::standard(),
    )
    .expect("raw context encoding");

    let Err(NotCertified::SerializationFailed { message }) = deserialize_context(&bytes) else {
        panic!("reserved sentinel context id must be rejected before into_context");
    };
    assert!(
        message.contains("reserved reconstruction-sentinel range"),
        "{message}"
    );
}

#[test]
fn test_deserialize_term_rejects_excessive_structural_depth() {
    let mut term = Expr::nat_lit(0);
    for _ in 0..=crate::proof_codec::TERM_STRUCTURE_LIMITS.max_depth {
        term = Expr::app(Expr::const_str("f"), term);
    }
    // Raw encoding deliberately bypasses the shared encoder's symmetric
    // structural guard so the decoder rejection path is exercised.
    let bytes = bincode::serde::encode_to_vec(&term, bincode::config::standard())
        .expect("stack-safe raw encoding of deep term");

    let Err(NotCertified::SerializationFailed { message }) = deserialize_term(&bytes) else {
        panic!("over-depth proof term must be rejected");
    };
    assert!(message.contains("structural depth"), "{message}");
}

/// NEGATIVE (gate d): a proof that leaned on a trustedAy sub-term
/// (`trust_subterm_count > 0`) must NOT certify, even if it otherwise looks
/// complete and the term type-checks.
#[test]
fn test_trusted_subterm_proof_is_not_certified() {
    let (env, mut result, ctx) = reconstruct_unit_contradiction();

    // Simulate a partially-verified proof that leaned on one trustedAy lemma.
    // Everything else (term present, empty clause, no witnesses, type-checks)
    // is identical to the positive case — only gate (d) differs.
    result.trust_subterm_count = 1;

    match certify_reconstruction(&result, &env, &ctx) {
        Err(NotCertified::TrustedSubterms { count }) => assert_eq!(count, 1),
        other => panic!("expected NotCertified::TrustedSubterms, got {other:?}"),
    }
}

/// NEGATIVE (gate e): a deliberately malformed proof term must be rejected by
/// the kernel `check_type`, yielding `NotCertified::KernelRejected` — never a
/// payload.
#[test]
fn test_malformed_proof_term_is_rejected_by_kernel() {
    let (env, mut result, ctx) = reconstruct_unit_contradiction();

    // Replace the valid proof term with the `False` constant itself. `False`
    // is a *type* (lives in `Prop`), not a *proof of* `False`, so
    // check_type(False, False) must fail.
    result.proof_term = Some(false_expr());
    // Keep every other gate satisfied so the ONLY thing that can reject this
    // is the full kernel re-validation.
    result.derives_empty_clause = true;
    result.compound_witness_fvars = Vec::new();
    result.trust_subterm_count = 0;

    match certify_reconstruction(&result, &env, &ctx) {
        Err(NotCertified::KernelRejected { .. }) => {}
        Ok(_) => panic!("malformed proof term must NOT certify"),
        other => panic!("expected NotCertified::KernelRejected, got {other:?}"),
    }
}

/// NEGATIVE (gate a): an absent proof term degrades to Trusted.
#[test]
fn test_absent_proof_term_is_not_certified() {
    let (env, mut result, ctx) = reconstruct_unit_contradiction();
    result.proof_term = None;
    assert_eq!(
        certify_reconstruction(&result, &env, &ctx),
        Err(NotCertified::NoProofTerm),
    );
}

/// NEGATIVE (gate b): a proof that does not derive the empty clause degrades.
#[test]
fn test_no_empty_clause_is_not_certified() {
    let (env, mut result, ctx) = reconstruct_unit_contradiction();
    result.derives_empty_clause = false;
    assert_eq!(
        certify_reconstruction(&result, &env, &ctx),
        Err(NotCertified::NoEmptyClause),
    );
}

/// NEGATIVE (gate c): a proof term with unbound compound-witness FVars degrades.
#[test]
fn test_unbound_witnesses_is_not_certified() {
    let (env, mut result, ctx) = reconstruct_unit_contradiction();
    let witness_prop = mk_eq_prop();
    result
        .compound_witness_fvars
        .push((FVarId::new(99), witness_prop));
    match certify_reconstruction(&result, &env, &ctx) {
        Err(NotCertified::UnboundWitnesses { count }) => assert_eq!(count, 1),
        other => panic!("expected NotCertified::UnboundWitnesses, got {other:?}"),
    }
}

/// Defense-in-depth: the gates are checked in order, but a proof that fails
/// MULTIPLE gates still never certifies. Here trust_subterm_count > 0 AND the
/// term is malformed — must be `NotCertified`, never a payload.
#[test]
fn test_multiple_gate_failures_never_certify() {
    let (env, mut result, ctx) = reconstruct_unit_contradiction();
    result.proof_term = Some(false_expr());
    result.trust_subterm_count = 3;
    let res = certify_reconstruction(&result, &env, &ctx);
    assert!(
        res.is_err(),
        "a proof failing multiple gates must never certify, got {res:?}"
    );
}

/// ADVERSARIAL (gate d, defense-in-depth): a reconstructor that LIES — emitting
/// a proof term that DOES apply `trustedAy` while reporting
/// `trust_subterm_count == 0` — must STILL be rejected, because gate (d) now
/// re-scans the final term independently of the reported field.
///
/// The term `@trustedAy.{0} False` is a genuine proof of `False` (the axiom has
/// type `{α : Sort u} → α`), so it PASSES the full kernel `check_type(_, False)`
/// re-validation — gate (e) cannot catch it (axioms type-check fine). The ONLY
/// barrier is the independent re-scan in gate (d). Without the re-scan (i.e.
/// trusting `result.trust_subterm_count`), this term would WRONGLY certify.
#[test]
fn test_lying_trust_count_with_real_trusted_ay_subterm_is_not_certified() {
    // Fresh env with `False` and the polymorphic `trustedAy` axiom registered.
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    env.init_trusted_ay().expect("init_trusted_ay");

    // term = `@trustedAy.{0} False` : a proof of `False` that embeds trustedAy.
    let trusted_ay = Expr::const_(Name::from_string("trustedAy"), vec![Level::zero()]);
    let term = Expr::app(trusted_ay, false_expr());
    let ctx = LocalContext::new();

    // Sanity: gate (e) would NOT catch this — it genuinely type-checks to False.
    let tc = TypeChecker::with_context(&env, ctx.clone());
    tc.check_type(&term, &false_expr())
        .expect("@trustedAy.{0} False must kernel-check to False (axioms type-check)");

    // Build an otherwise-valid result whose term embeds trustedAy but whose
    // reported trust_subterm_count LIES that there is none.
    let result = complete_result(term);

    // Gate (d) must reject via the independent re-scan, NOT the honest field.
    match certify_reconstruction(&result, &env, &ctx) {
        Err(NotCertified::TrustedSubterms { count }) => assert_eq!(
            count, 1,
            "re-scan must count the one embedded trustedAy sub-term"
        ),
        other => {
            panic!("lying trust_subterm_count must be caught by gate (d) re-scan, got {other:?}")
        }
    }
}

/// Both payload constructors must reject an arbitrary axiom that happens to
/// type-check as the requested goal. This is the case the old two-name trust
/// scan missed: `forgedFalse` is neither `trustedAy` nor `trustedArith`, but it
/// is still non-foundational authority.
#[test]
fn arbitrary_false_axiom_is_rejected_by_both_payload_constructors() {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    let forged = Name::from_string("forgedFalse");
    env.add_decl(Declaration::Axiom {
        name: forged.clone(),
        level_params: vec![],
        type_: false_expr(),
    })
    .expect("well-typed domain axiom");
    let term = Expr::const_(forged.clone(), vec![]);
    let ctx = LocalContext::new();

    TypeChecker::with_context(&env, ctx.clone())
        .check_type(&term, &false_expr())
        .expect("the adversarial axiom is deliberately kernel-well-typed");

    for outcome in [
        certify_kernel_term(&term, &false_expr(), &env, &ctx),
        certify_reconstruction(&complete_result(term.clone()), &env, &ctx),
    ] {
        match outcome {
            Err(NotCertified::AuthorityRejected { issues }) => assert!(
                issues.iter().any(|issue| matches!(
                    issue,
                    CertificationIssue::NonFoundationalAxiom { name } if name == &forged
                )),
                "authority rejection must identify forgedFalse: {issues:#?}"
            ),
            other => panic!("a free False axiom must never mint a payload: {other:?}"),
        }
    }
}

/// Free data constants are authority too: even reflexivity is not a strongest-
/// grade certificate when its subject is an arbitrary environment axiom.
#[test]
fn reflexivity_over_free_data_axiom_is_rejected() {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let datum_name = Name::from_string("freeDatum");
    env.add_decl(Declaration::Axiom {
        name: datum_name.clone(),
        level_params: vec![],
        type_: nat.clone(),
    })
    .expect("well-typed data axiom");
    let datum = Expr::const_(datum_name.clone(), vec![]);
    let u1 = Level::succ(Level::zero());
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
        [nat.clone(), datum.clone(), datum.clone()],
    );
    let term = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [nat, datum],
    );

    match certify_kernel_term(&term, &goal, &env, &LocalContext::new()) {
        Err(NotCertified::AuthorityRejected { issues }) => assert!(issues.iter().any(|issue| {
            matches!(
                issue,
                CertificationIssue::NonFoundationalAxiom { name } if name == &datum_name
            )
        })),
        other => panic!("reflexivity over a free data axiom must be rejected: {other:?}"),
    }
}

/// The same data is sound when it is a genuine local parameter. Closing the
/// judgment turns the local into a `Pi`/`Lam`, so no free axiom remains.
#[test]
fn reflexivity_over_bound_data_parameter_is_certified() {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let mut ctx = LocalContext::new();
    let datum_id = FVarId::new(41);
    ctx.push_with_id(
        datum_id,
        Name::from_string("datum"),
        nat.clone(),
        BinderInfo::Default,
    );
    let datum = Expr::fvar(datum_id);
    let u1 = Level::succ(Level::zero());
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
        [nat.clone(), datum.clone(), datum.clone()],
    );
    let term = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [nat, datum],
    );

    certify_kernel_term(&term, &goal, &env, &ctx)
        .expect("a properly bound data parameter must remain certifiable");
}

/// Mutation test: a checked theorem can authorize a payload, but eliding its
/// proof value invalidates the exact declaration payload and must immediately
/// revoke certification even though the theorem constant still type-checks.
#[test]
fn proof_value_elision_revokes_payload_authority() {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    let theorem_name = Name::from_string("checkedTrue");
    env.add_decl(Declaration::Theorem {
        name: theorem_name.clone(),
        level_params: vec![],
        type_: true_expr(),
        value: Expr::const_(Name::from_string("True.intro"), vec![]),
    })
    .expect("checked theorem");
    let term = Expr::const_(theorem_name.clone(), vec![]);
    let ctx = LocalContext::new();

    certify_kernel_term(&term, &true_expr(), &env, &ctx)
        .expect("the exact checked theorem should initially certify");
    assert!(env.forget_value(&theorem_name), "fixture mutation applied");

    match certify_kernel_term(&term, &true_expr(), &env, &ctx) {
        Err(NotCertified::AuthorityRejected { issues }) => assert!(
            issues.iter().any(|issue| matches!(
                issue,
                CertificationIssue::MissingValue { name } if name == &theorem_name
            )),
            "elided theorem must expose its missing value: {issues:#?}"
        ),
        other => panic!("proof-value mutation must revoke certification: {other:?}"),
    }
}

/// Context serialization must preserve let values. The previous projection
/// silently replayed every let as an assumption, changing the certified
/// judgment and giving the payload more authority than the original context.
#[test]
fn local_let_binding_roundtrips_without_becoming_an_axiom() {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    let let_id = FVarId::new(77);
    let let_value = Expr::const_(Name::from_string("True.intro"), vec![]);
    let mut ctx = LocalContext::new();
    ctx.push_let_with_id(
        let_id,
        Name::from_string("truth"),
        true_expr(),
        let_value.clone(),
    );
    let term = Expr::fvar(let_id);

    let payload = certify_kernel_term(&term, &true_expr(), &env, &ctx)
        .expect("a foundational local definition should certify");
    let reduced = deserialize_context(&payload.context_bytes).expect("deserialize context");
    assert_eq!(reduced.decls.len(), 1);
    assert_eq!(reduced.decls[0].value.as_ref(), Some(&let_value));
    let rebuilt = reduced.into_context();
    assert_eq!(
        rebuilt.get(let_id).and_then(|decl| decl.value.as_ref()),
        Some(&let_value),
        "replay must preserve the let definition"
    );
    TypeChecker::with_context(&env, rebuilt)
        .check_type(&term, &true_expr())
        .expect("replayed let context must validate the serialized term");
}
