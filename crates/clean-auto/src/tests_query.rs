// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_auto_prove_with_query_mirrors_docs_builder_example() {
    use crate::engine_api::AutomationQuery;

    let env = setup_env_with_prop("P");
    let goal = Expr::const_(Name::from_string("P"), vec![]);
    let mut local_ctx = LocalContext::new();
    local_ctx.push_with_id(
        FVarId::new(42),
        Name::from_string("h"),
        goal.clone(),
        BinderInfo::Default,
    );
    let hypotheses = vec![(goal.clone(), None)];
    let engine = AutomationEngine::new();

    let query = AutomationQuery::new(&goal, Duration::from_secs(5))
        .with_hypotheses(hypotheses.as_slice())
        .with_local_ctx(&local_ctx);
    let outcome = engine.auto_prove_with_query(&env, query);

    match outcome {
        AutomationOutcome::Verified(result) => {
            let proof_context = result
                .proof_context
                .expect("query using docs-style builders should preserve proof context");
            let names: Vec<String> = proof_context
                .iter()
                .map(|decl| decl.name.to_string())
                .collect();
            assert_eq!(names, vec!["h".to_string()]);
        }
        other => panic!("expected local hypothesis to prove the goal, got {other:?}"),
    }
}

#[test]
fn test_prelude_docs_example_uses_query_api() {
    use crate::prelude::*;

    let env = setup_env_with_prop("P");
    let goal = Expr::const_(Name::from_string("P"), vec![]);
    let hypotheses = vec![(goal.clone(), None)];
    let timeout = Duration::from_secs(5);
    let engine = AutomationEngine::new();

    let query = AutomationQuery::new(&goal, timeout).with_hypotheses(hypotheses.as_slice());
    let outcome = engine.auto_prove_with_query(&env, query);

    match outcome {
        AutomationOutcome::Verified(result) => {
            let inferred = result.infer_type(&env);
            assert!(
                inferred.is_ok(),
                "prelude docs example should type-check through the query API: {:?}",
                inferred.err()
            );
        }
        other => panic!("expected prelude docs example to verify the goal, got {other:?}"),
    }
}

#[test]
fn test_auto_prove_with_query_uses_oracle_after_unknown_smt() {
    use crate::engine_api::AutomationQuery;

    let env = setup_env_with_eq();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let quantified_goal = Expr::pi(
        BinderInfo::Default,
        a_ty.clone(),
        make_eq(a_ty.clone(), Expr::bvar(0), Expr::bvar(0)),
    );
    let goal = Expr::pi(BinderInfo::Default, quantified_goal.clone(), a_ty);
    let engine = AutomationEngine::new();
    let oracle = TestOracle::new(&[("exact a", 0.9)]);
    let runner = TestOracleRunner {
        proof_term: Expr::lam(
            BinderInfo::Default,
            quantified_goal,
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        proof_text: "exact a".to_string(),
    };

    let query = AutomationQuery::new(&goal, Duration::from_secs(5)).with_oracle(&oracle, &runner);
    let outcome = engine.auto_prove_with_query(&env, query);

    match outcome {
        AutomationOutcome::Verified(result) => {
            let result = *result;
            assert_eq!(result.proof_text(), "exact a");
            let inferred = result.infer_type(&env);
            assert!(
                inferred.is_ok(),
                "oracle proof should type-check through the query API: {:?}",
                inferred.err()
            );
        }
        other => panic!("expected oracle-verified outcome after SMT fallback, got {other:?}"),
    }
}

#[test]
fn test_auto_prove_with_query_preserves_detailed_outcomes() {
    use crate::engine_api::AutomationQuery;

    let env = setup_env_with_prop("P");
    let goal = Expr::const_(Name::from_string("P"), vec![]);
    let engine = AutomationEngine::new();

    let query = AutomationQuery::new(&goal, Duration::from_secs(5));
    let outcome = engine.auto_prove_with_query(&env, query);

    assert!(
        matches!(
            outcome,
            AutomationOutcome::Refuted {
                source: AutomationSource::Smt,
                ..
            }
        ),
        "AutomationQuery should preserve SMT refutation, got: {outcome:?}"
    );
}

#[test]
fn test_auto_prove_with_query_reflexivity() {
    use crate::engine_api::AutomationQuery;

    let env = setup_env_with_eq();
    let engine = AutomationEngine::new();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty, a.clone(), a);

    let query = AutomationQuery::new(&goal, Duration::from_secs(5));
    let outcome = engine.auto_prove_with_query(&env, query);

    match outcome {
        AutomationOutcome::Verified(result) => {
            assert!(!result.proof_text().is_empty(), "Should have proof text");
        }
        other => panic!("expected Verified for a = a, got {other:?}"),
    }
}

#[test]
fn test_auto_prove_with_query_from_request_conversion() {
    use crate::engine_api::AutomationQuery;

    let env = setup_env_with_eq();
    let engine = AutomationEngine::new();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty, a.clone(), a);

    // Build via AutomationRequest then convert
    let request = AutomationRequest::new(&goal, Duration::from_secs(5));
    let query = AutomationQuery::from(request);

    // Verify getters
    assert_eq!(query.goal(), &goal);
    assert_eq!(query.timeout(), Duration::from_secs(5));
    assert!(query.local_ctx().is_none());
    assert!(query.hypotheses().is_empty());
    assert!(query.premise_db().is_none());

    // Converted query should match direct request wrapper behavior
    let outcome = engine.auto_prove_with_query(&env, query);
    assert!(
        matches!(outcome, AutomationOutcome::Verified(_)),
        "converted query should prove a = a"
    );
    let request_outcome =
        engine.auto_prove_with_request(&env, AutomationRequest::new(&goal, Duration::from_secs(5)));
    assert!(
        matches!(request_outcome, AutomationOutcome::Verified(_)),
        "request wrapper parity"
    );
}

// =============================================================================
// Tests for suggest_tactic / suggest_proof_term oracle integration (Part of #2404)
// =============================================================================

use crate::oracle::{OracleError, ProofTermCandidate};

/// Oracle that returns proof terms directly (no tactic text).
struct ProofTermOracle {
    proof_terms: Vec<ProofTermCandidate>,
}

impl ProofTermOracle {
    fn new(proof_terms: Vec<ProofTermCandidate>) -> Self {
        Self { proof_terms }
    }
}

impl crate::oracle::ProofOracle for ProofTermOracle {
    fn suggest_proof(
        &self,
        _request: &crate::oracle::OracleRequest,
    ) -> Result<Vec<crate::oracle::OracleCandidate>, OracleError> {
        // This oracle only produces proof terms, not tactic text.
        Ok(Vec::new())
    }

    fn suggest_proof_term(
        &self,
        _request: &crate::oracle::OracleRequest,
    ) -> Result<Vec<ProofTermCandidate>, OracleError> {
        Ok(self.proof_terms.clone())
    }

    fn model_id(&self) -> &str {
        "proof-term-oracle"
    }

    fn is_available(&self) -> bool {
        true
    }
}

#[test]
fn test_oracle_suggest_proof_term_kernel_validated() {
    use crate::engine_api::AutomationQuery;

    let env = setup_env_with_eq();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty.clone(), a.clone(), a.clone());

    // Build a valid proof term: @Eq.refl A a
    let proof_term = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
            ),
            a_ty,
        ),
        a,
    );

    let oracle = ProofTermOracle::new(vec![
        ProofTermCandidate::new(proof_term, 0.95).with_description("Eq.refl")
    ]);

    let engine = AutomationEngine::new();
    let query = AutomationQuery::new(&goal, Duration::from_secs(5)).with_proof_term_oracle(&oracle);
    let outcome = engine.auto_prove_with_query(&env, query);

    match outcome {
        AutomationOutcome::Verified(result) => {
            let inferred = result.infer_type(&env);
            assert!(
                inferred.is_ok(),
                "oracle proof term should type-check through kernel: {:?}",
                inferred.err()
            );
        }
        other => panic!("expected Verified from proof-term oracle for a = a, got {other:?}"),
    }
}

#[test]
fn test_oracle_suggest_proof_term_rejects_ill_typed() {
    use crate::engine_api::AutomationQuery;

    let env = setup_env_with_eq();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    // Goal: a = b (not provable by refl)
    let goal = make_eq(a_ty.clone(), a.clone(), b);

    // Offer a proof term for a = a (wrong goal)
    let bad_proof = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
            ),
            a_ty,
        ),
        a,
    );

    let oracle = ProofTermOracle::new(vec![ProofTermCandidate::new(bad_proof, 0.95)]);

    let engine = AutomationEngine::new();
    let query = AutomationQuery::new(&goal, Duration::from_secs(5)).with_proof_term_oracle(&oracle);
    let outcome = engine.auto_prove_with_query(&env, query);

    // The proof term proves a = a, not a = b. Kernel validation rejects it.
    assert!(
        !matches!(outcome, AutomationOutcome::Verified(_)),
        "ill-typed oracle proof term must be rejected, got {outcome:?}"
    );
}

#[test]
fn test_oracle_suggest_proof_term_falls_back_to_tactic_runner() {
    use crate::engine_api::AutomationQuery;

    let env = setup_env_with_eq();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    // Use a quantified goal that SMT and superposition both produce Unknown for,
    // ensuring the oracle phase is reached.
    let quantified_inner = Expr::pi(
        BinderInfo::Default,
        a_ty.clone(),
        make_eq(a_ty.clone(), Expr::bvar(0), Expr::bvar(0)),
    );
    let goal = Expr::pi(BinderInfo::Default, quantified_inner.clone(), a_ty.clone());

    // Offer a bad proof term (type Nat, obviously wrong for the goal)
    let bad_proof = Expr::nat_lit(42);

    // The tactic runner returns a correct proof via the fallback path
    let good_proof = Expr::lam(
        BinderInfo::Default,
        quantified_inner,
        Expr::const_(Name::from_string("a"), vec![]),
    );

    // Oracle produces a bad proof term but good tactic candidates
    struct FallbackOracle {
        bad_proof: Expr,
    }
    impl crate::oracle::ProofOracle for FallbackOracle {
        fn suggest_proof(
            &self,
            _request: &crate::oracle::OracleRequest,
        ) -> Result<Vec<crate::oracle::OracleCandidate>, OracleError> {
            Ok(vec![crate::oracle::OracleCandidate::new(
                "exact proof",
                0.9,
            )])
        }
        fn suggest_proof_term(
            &self,
            _request: &crate::oracle::OracleRequest,
        ) -> Result<Vec<ProofTermCandidate>, OracleError> {
            Ok(vec![ProofTermCandidate::new(self.bad_proof.clone(), 0.95)])
        }
        fn model_id(&self) -> &str {
            "fallback-oracle"
        }
        fn is_available(&self) -> bool {
            true
        }
    }

    let oracle = FallbackOracle { bad_proof };
    let runner = TestOracleRunner {
        proof_term: good_proof,
        proof_text: "fallback tactic".to_string(),
    };

    let engine = AutomationEngine::new();
    let query = AutomationQuery::new(&goal, Duration::from_secs(5)).with_oracle(&oracle, &runner);
    let outcome = engine.auto_prove_with_query(&env, query);

    match outcome {
        AutomationOutcome::Verified(result) => {
            assert_eq!(
                result.proof_text(),
                "fallback tactic",
                "should fall through to tactic runner after proof-term rejection"
            );
        }
        other => panic!("expected Verified via tactic fallback, got {other:?}"),
    }
}

#[test]
fn test_oracle_suggest_tactic_delegates_to_suggest_proof() {
    // Verify the default suggest_tactic delegates to suggest_proof
    let oracle = TestOracle::new(&[("exact rfl", 0.9), ("simp", 0.5)]);
    let request = crate::oracle::OracleRequest::new("True");

    let proof_result = oracle
        .suggest_proof(&request)
        .expect("suggest_proof should succeed");
    let tactic_result = oracle
        .suggest_tactic(&request)
        .expect("suggest_tactic should succeed");

    assert_eq!(proof_result.len(), tactic_result.len());
    for (p, t) in proof_result.iter().zip(tactic_result.iter()) {
        assert_eq!(p.tactic_text, t.tactic_text);
        assert!((p.confidence - t.confidence).abs() < f64::EPSILON);
    }
}

#[test]
fn test_oracle_proof_term_candidate_sorting() {
    use crate::oracle::sort_proof_term_candidates;

    let mut candidates = vec![
        ProofTermCandidate::new(Expr::prop(), 0.3),
        ProofTermCandidate::new(Expr::prop(), 0.9),
        ProofTermCandidate::new(Expr::prop(), 0.6),
    ];
    sort_proof_term_candidates(&mut candidates);

    assert!((candidates[0].confidence - 0.9).abs() < f64::EPSILON);
    assert!((candidates[1].confidence - 0.6).abs() < f64::EPSILON);
    assert!((candidates[2].confidence - 0.3).abs() < f64::EPSILON);
}

#[test]
fn test_oracle_with_proof_term_oracle_no_runner_needed() {
    use crate::engine_api::AutomationQuery;

    let env = setup_env_with_eq();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let goal = make_eq(a_ty.clone(), a.clone(), a.clone());

    let proof_term = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
            ),
            a_ty,
        ),
        a,
    );

    let oracle = ProofTermOracle::new(vec![ProofTermCandidate::new(proof_term, 0.95)]);

    let engine = AutomationEngine::new();
    // Use with_proof_term_oracle (no runner) -- should still work
    let query = AutomationQuery::new(&goal, Duration::from_secs(5)).with_proof_term_oracle(&oracle);
    let outcome = engine.auto_prove_with_query(&env, query);

    assert!(
        matches!(outcome, AutomationOutcome::Verified(_)),
        "proof-term-only oracle (no runner) should verify a = a, got {outcome:?}"
    );
}
