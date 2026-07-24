// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Performance proof tests for tactic subsystem.
//!
//! Documents algorithmic complexity of key operations and detects regressions.
//! Phase: performance_proofs (P1 iter 771).

use super::*;
use crate::tactic::simp::{SimpIndexMode, SimpLemma, SimpLemmaSet};
use clean_kernel::env::Declaration;

// ============================================================================
// Performance proof: DratVerifier::verify has O(clauses^2) cost
//
// Three quadratic patterns in drat.rs:
//
// 1. remove_clause (drat.rs:389-408): Linear scan to find clause O(n),
//    Vec::remove shift O(n), full watch index update O(total_watches).
//    Called once per Delete step. N deletions = O(N * clauses).
//
// 2. propagate (drat.rs:442-508): Scans ALL clauses per fixpoint
//    iteration without two-watched-literal optimization. Each is_rup
//    call is O(clauses * vars * iterations).
//
// 3. is_rat (drat.rs:514-539): For each clause containing negated pivot,
//    resolvent.contains() is O(resolvent) per literal, plus is_rup call
//    per resolvent. Total: O(clauses^2 * vars).
//
// Fix: Clause ID map + tombstone deletion for remove_clause.
// Two-watched-literal propagation for is_rup.
// HashSet for resolvent dedup in is_rat.
// ============================================================================

/// Documents O(clauses) scaling of DRAT verify per proof step.
///
/// DratVerifier::verify exercises propagate() (which scans all clauses)
/// and remove_clause (which does linear search + index updates) through
/// the public API. This test times verify() on formulas of increasing
/// size to document the linear-per-step cost.
#[test]
fn test_drat_verify_scaling_per_step() {
    use super::super::drat::{CnfFormula, DratOp, DratProof, DratVerifier};

    let sizes = [50usize, 200, 800];
    let mut times = Vec::new();

    for &n in &sizes {
        // Build an UNSAT formula with n clauses.
        // Structure: n-2 padding clauses + (x1) + (¬x1) at the end.
        // The padding clauses use variables 2..n+1 so they don't interfere.
        let mut formula = CnfFormula::new();
        formula.num_vars = n + 1;
        for i in 0..n.saturating_sub(2) {
            let v = (i + 2) as i32;
            formula.clauses.push(vec![v, v + 1]);
        }
        formula.clauses.push(vec![1]);
        formula.clauses.push(vec![-1]);

        // Build a proof that:
        // 1. Deletes half the padding clauses (exercises remove_clause)
        // 2. Derives empty clause (exercises propagate via is_rup)
        let mut proof = DratProof::new();
        for i in 0..n.saturating_sub(2) / 2 {
            let v = (i + 2) as i32;
            proof.operations.push(DratOp::Delete(vec![v, v + 1]));
        }
        proof.operations.push(DratOp::Add(vec![])); // empty clause = RUP

        // Verify correctness first — if verify() returns Err, the timing
        // would measure error-path latency, not the quadratic deletion path.
        let result = DratVerifier::verify(&formula, &proof);
        assert!(
            result.is_ok(),
            "DRAT verify should succeed for n={n}: {:?}",
            result
        );

        let iters = 20;
        let start = std::time::Instant::now();
        for _ in 0..iters {
            let _ = DratVerifier::verify(&formula, &proof);
        }
        let elapsed = start.elapsed().as_nanos() as u64;
        times.push(elapsed / iters as u64);
    }

    // With deletion + propagation, scaling includes quadratic component.
    // For pure linear (O(n)), 800/50 ratio = 16x.
    // For O(n^2), ratio = 256x.
    // Assert < 2000x to catch any > O(n^2.5) regression.
    if times[0] > 0 {
        let ratio = times[2] as f64 / times[0] as f64;
        assert!(
            ratio < 2000.0,
            "DRAT verify scaling: 800/50 ratio = {ratio:.1}x. \
             O(n) = 16x, O(n^2) = 256x. times: {times:?}"
        );
    }
}

// ============================================================================
// Performance proof: collect_fvars uses Vec.contains() — O(nodes * fvars)
//
// hypothesis.rs:234-259 — collect_fvars_rec uses `fvars.contains(id)` (O(f)
// linear scan on Vec<FVarId>) at every FVar node in the expression tree.
// For an expression with N nodes containing F unique FVarIds, total cost
// is O(N * F). Since F <= N, worst case is O(N^2).
//
// Called from clear_all_unused (line 188) and clear_except (line 368) which
// both run fixpoint loops, multiplying the cost. The callers convert the
// result to HashSet anyway (line 199, 370), so the Vec is unnecessary.
//
// Fix: Use HashSet<FVarId> inside collect_fvars_rec for O(1) membership
// testing, or return HashSet<FVarId> directly since all callers convert.
// ============================================================================

/// Documents O(nodes * fvars) scaling of collect_fvars.
///
/// Builds expressions with increasing numbers of distinct FVarIds in app chains.
/// With N unique FVarIds and N expression nodes, the Vec.contains() check
/// at hypothesis.rs:237 makes each FVar visit O(F), giving O(N*F) = O(N^2).
#[test]
fn test_collect_fvars_quadratic_scaling() {
    let sizes = [50usize, 200, 800];
    let mut times = Vec::new();

    for &n in &sizes {
        // Build expression tree with n unique FVarIds in app chain:
        // App(App(...App(fvar0, fvar1), fvar2), ..., fvarN)
        let mut expr = Expr::fvar(FVarId::new(0));
        for i in 1..n {
            expr = Expr::app(expr, Expr::fvar(FVarId::new(i as u64)));
        }

        // Warm up
        for _ in 0..3 {
            let _ = collect_fvars(&expr);
        }

        let iters = 50;
        let start = std::time::Instant::now();
        for _ in 0..iters {
            let _ = collect_fvars(&expr);
        }
        let elapsed = start.elapsed().as_nanos() as u64;
        times.push(elapsed / iters as u64);
    }

    // For O(n^2), ratio of 800/50 = (16)^2 = 256x
    // For O(n), ratio = 16x
    // Documents current behavior. If fixed to HashSet, ratio drops to ~16x.
    if times[0] > 0 {
        let ratio = times[2] as f64 / times[0] as f64;
        assert!(
            ratio < 2000.0,
            "collect_fvars scaling: 800/50 ratio = {ratio:.1}x. \
             O(n^2) expected ~256x for Vec.contains(). times: {times:?}"
        );
    }
}

// ============================================================================
// Performance proof: Polynomial::add uses Vec.position() — O(terms^2)
//
// polyrith.rs:63-87 — Polynomial::add searches result_terms with
// `.position()` (O(n) linear scan) for each term in other.terms.
// For polynomials with T1 and T2 terms: O(T1 * T2).
//
// Multiplication (polyrith.rs:109) compounds this: O(T1 * T2) pairs
// each calling add, giving O(T1^2 * T2^2) for polynomial multiplication.
//
// Bounded in practice by max_degree=4 and max_hyps=10, so not urgent.
//
// Fix: Use HashMap<Monomial, Coefficient> for O(1) term lookup.
// ============================================================================

/// Documents O(terms^2) scaling of Polynomial::add.
#[test]
fn test_polynomial_add_quadratic_scaling() {
    use super::super::polyrith::Polynomial;

    let sizes = [10usize, 40, 160];
    let mut times = Vec::new();

    for &n in &sizes {
        // Build two polynomials each with n terms using distinct variables
        let mut p1 = Polynomial::zero();
        let mut p2 = Polynomial::zero();
        for i in 0..n {
            // p1 has vars 0..n, p2 has vars n..2n (no overlap = worst case
            // for position() since every term needs full scan)
            p1 = p1.add(&Polynomial::var(i));
            p2 = p2.add(&Polynomial::var(n + i));
        }

        // Warm up
        for _ in 0..3 {
            let _ = p1.add(&p2);
        }

        let iters = 100;
        let start = std::time::Instant::now();
        for _ in 0..iters {
            let _ = p1.add(&p2);
        }
        let elapsed = start.elapsed().as_nanos() as u64;
        times.push(elapsed / iters as u64);
    }

    // For O(n^2) with no overlap: each of T2 terms scans all T1 terms.
    // 160/10 = 16x input, so ratio should be ~256x for O(n^2).
    if times[0] > 0 {
        let ratio = times[2] as f64 / times[0] as f64;
        assert!(
            ratio < 3000.0,
            "Polynomial::add scaling: 160/10 ratio = {ratio:.1}x. \
             O(n^2) expected ~256x for Vec.position(). times: {times:?}"
        );
    }
}

fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .unwrap();
}

fn mk_eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}

fn mk_simp_lemma(name: &str, lhs: Expr, rhs: Expr, eq_type: &Expr) -> SimpLemma {
    SimpLemma {
        name: Name::from_string(name),
        lhs,
        rhs,
        eq_type: Some(eq_type.clone()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    }
}

fn setup_simp_candidate_state(noise_count: usize) -> (ProofState, Goal, Expr, Expr, Expr) {
    let mut env = setup_env();
    env.init_eq().unwrap();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    for name in ["keep", "rhs", "alt_rhs"] {
        add_axiom(&mut env, name, a_ty.clone());
    }
    for i in 0..noise_count {
        add_axiom(&mut env, &format!("noise{i}"), a_ty.clone());
    }

    let query = Expr::const_(Name::from_string("keep"), vec![]);
    let target = mk_eq(a_ty.clone(), query.clone(), query.clone());
    let state = ProofState::new(env, target);
    let goal = state.current_goal().expect("goal should exist").clone();
    let rhs = Expr::const_(Name::from_string("rhs"), vec![]);
    (state, goal, query, rhs, a_ty)
}

/// Regression proof for #1931: indexed simp lookup must keep the original
/// lemma order without falling back to a full ordered-lemma scan.
#[test]
fn test_simp_candidates_preserve_order_for_multiple_index_hits() {
    let (state, goal, query, rhs, a_ty) = setup_simp_candidate_state(1);
    let alt_rhs = Expr::const_(Name::from_string("alt_rhs"), vec![]);
    let noise = Expr::const_(Name::from_string("noise0"), vec![]);
    let lemmas = vec![
        mk_simp_lemma("match_high", query.clone(), rhs.clone(), &a_ty),
        mk_simp_lemma("noise", noise, rhs, &a_ty),
        mk_simp_lemma("match_low", query.clone(), alt_rhs, &a_ty),
    ];
    let lemma_set = SimpLemmaSet::with_goal(&state, &goal, lemmas);

    let candidate_names: Vec<_> = lemma_set
        .candidates(&state, &goal, &query)
        .into_iter()
        .map(|lemma| lemma.name.clone())
        .collect();

    assert_eq!(
        candidate_names,
        vec![
            Name::from_string("match_high"),
            Name::from_string("match_low"),
        ],
        "indexed simp candidates should preserve the original ordered priority"
    );
}

/// Performance proof for #1931: irrelevant simp lemmas should not make a
/// specific indexed lookup scale linearly with total lemma count.
#[test]
fn test_simp_candidates_ignore_irrelevant_lemma_count_scaling() {
    use std::hint::black_box;
    use std::time::Instant;

    let sizes = [512usize, 4096, 32_768];
    let mut times = Vec::new();

    for &noise_count in &sizes {
        let (state, goal, query, rhs, a_ty) = setup_simp_candidate_state(noise_count);
        let mut lemmas = Vec::with_capacity(noise_count + 1);
        lemmas.push(mk_simp_lemma("match", query.clone(), rhs.clone(), &a_ty));
        for i in 0..noise_count {
            lemmas.push(mk_simp_lemma(
                &format!("noise_lemma{i}"),
                Expr::const_(Name::from_string(&format!("noise{i}")), vec![]),
                rhs.clone(),
                &a_ty,
            ));
        }
        let lemma_set = SimpLemmaSet::with_goal(&state, &goal, lemmas);

        let candidates = lemma_set.candidates(&state, &goal, &query);
        assert_eq!(
            candidates.len(),
            1,
            "only the specific indexed lemma should match the query"
        );
        assert_eq!(
            candidates[0].name,
            Name::from_string("match"),
            "indexed simp lookup should return the matching lemma"
        );

        for _ in 0..8 {
            black_box(lemma_set.candidates(&state, &goal, &query).len());
        }

        let iters = 128;
        let start = Instant::now();
        for _ in 0..iters {
            black_box(lemma_set.candidates(&state, &goal, &query).len());
        }
        times.push(start.elapsed().as_nanos() as f64 / iters as f64);
    }

    if times[0] > 0.0 {
        let ratio = times[2] / times[0];
        assert!(
            ratio < 12.0,
            "simp candidate lookup regressed: 32768/512 irrelevant lemmas ratio = \
             {ratio:.1}x, expected near-constant indexed lookup. times_ns={times:?}"
        );
    }
}
