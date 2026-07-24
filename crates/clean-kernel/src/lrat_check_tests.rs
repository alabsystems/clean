// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the computational LRAT (RUP) trace checker (reflection backend).
//!
//! These confirm (1) the checker ops are reducible `Definition`s, (2) a valid
//! LRAT trace reflects to `Bool.true` and an `Eq.refl` over it kernel-type-checks,
//! and (3) every CORRUPTION of a valid trace reflects to `Bool.false` — headlined
//! by the three CK1 WS1-M2 acceptance corruptions: a dropped hint, a permuted
//! clause DB, and a truncated trace.

use super::{check_lrat_app, check_lrat_initialtrie_app, names, LratStepData};
use crate::name::Name;
use crate::resolution_check::encode_clauses;
use crate::{Environment, Expr, Level, TypeChecker};

fn env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_lrat_check().expect("init_lrat_check");
    env.init_lrat_check().expect("idempotent");
    env
}

fn btrue() -> Expr {
    Expr::const_str("Bool.true")
}
fn bfalse() -> Expr {
    Expr::const_str("Bool.false")
}
fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}
fn eq_refl_bool(v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty(), v],
    )
}
fn eq_bool(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [bool_ty(), x, y],
    )
}

/// The base UNSAT clause DB (ids 0..3):
///   c0 = (x ∨ y),  c1 = (x ∨ ¬y),  c2 = (¬x ∨ y),  c3 = (¬x ∨ ¬y).
fn base_clauses() -> Vec<Vec<(u32, bool)>> {
    vec![
        vec![(0, false), (1, false)],
        vec![(0, false), (1, true)],
        vec![(0, true), (1, false)],
        vec![(0, true), (1, true)],
    ]
}

/// A genuine 3-step LRAT refutation of `base_clauses`:
///   step0: clause (x)  [id 4], hints [0, 1] — assume ¬x: c0 units y, c1 conflicts.
///   step1: clause (¬x) [id 5], hints [2, 3] — assume x: c2 units y, c3 conflicts.
///   step2: clause []          , hints [4, 5] — id4 units x, id5 conflicts.
fn base_trace() -> Vec<LratStepData> {
    vec![
        (vec![(0, false)], vec![0, 1]),
        (vec![(0, true)], vec![2, 3]),
        (vec![], vec![4, 5]),
    ]
}

/// Reduce `checkLrat` (pre-built initial trie) on (clauses, trace) to whnf.
fn whnf_check_lrat(clauses: &[Vec<(u32, bool)>], trace: &[LratStepData]) -> Expr {
    let env = env();
    let app = check_lrat_app(clauses, trace);
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.whnf(&app)
}

#[test]
fn test_lrat_checker_ops_are_reducible_definitions() {
    use crate::ConstantKind;
    let env = env();
    for op in [
        names::LRAT_STEP_CLAUSE,
        names::LRAT_STEP_CLAUSE_EMPTY,
        names::LIST_LRAT_STEP_IS_CONS,
        names::LIST_NAT_IS_CONS,
        names::LRAT_REDUCE,
        names::LRAT_RUP,
        names::CHECK_LRAT_STEP,
        names::CHECK_LRAT,
    ] {
        let info = env
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} should be registered"));
        assert!(
            matches!(info.kind, ConstantKind::Definition),
            "{op} must be a Definition, not an axiom; got {:?}",
            info.kind
        );
    }
    assert!(
        env.get_inductive(&Name::from_string(names::LRAT_STEP))
            .is_some(),
        "LratStep inductive must be registered"
    );
    assert!(
        env.get_const(&Name::from_string("Clean.Res.LratStep.rec"))
            .is_some(),
        "LratStep.rec must be derived"
    );
}

#[test]
fn test_lrat_valid_trace_reflects_to_true() {
    assert_eq!(
        whnf_check_lrat(&base_clauses(), &base_trace()),
        btrue(),
        "a genuine LRAT trace must reflect to Bool.true"
    );
}

#[test]
fn test_lrat_eq_refl_over_valid_trace_typechecks() {
    let env = env();
    let app = check_lrat_app(&base_clauses(), &base_trace());
    // The reflection certificate: Eq.refl Bool.true : checkLrat db |cs| trace = true.
    let proof = eq_refl_bool(btrue());
    let goal = eq_bool(app, btrue());
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&proof, &goal)
        .expect("Eq.refl must type-check the LRAT reflection certificate");
}

// ── the three named CK1 WS1-M2 corruptions ──────────────────────────────────────

#[test]
fn lrat_refuses_dropped_hint() {
    // Drop step0's FIRST hint (c0): the remaining hint c1 = (x ∨ ¬y) reduces
    // under F = {x} to the unit (¬y) — propagation then runs out of hints
    // without reaching conflict, so the step is no longer RUP-justified.
    let mut trace = base_trace();
    trace[0].1.remove(0);
    assert_eq!(
        whnf_check_lrat(&base_clauses(), &trace),
        bfalse(),
        "a dropped unit-propagation hint must be refused"
    );
}

#[test]
fn lrat_refuses_permuted_clause_db() {
    // Swap c0 and c3 in the clause DB WITHOUT renumbering the trace's hints:
    // step0's hint 0 now fetches (¬x ∨ ¬y), which reduces under F = {x} to two
    // unfalsified literals — neither unit nor conflict.
    let mut clauses = base_clauses();
    clauses.swap(0, 3);
    assert_eq!(
        whnf_check_lrat(&clauses, &base_trace()),
        bfalse(),
        "a permuted clause DB (stale hint ids) must be refused"
    );
}

#[test]
fn lrat_refuses_truncated_trace() {
    // Drop the final (empty-clause) step: the trace's last recorded clause is
    // (¬x) ≠ [], so the refutation never derives the empty clause.
    let mut trace = base_trace();
    trace.truncate(2);
    assert_eq!(
        whnf_check_lrat(&base_clauses(), &trace),
        bfalse(),
        "a truncated trace (no empty-clause endpoint) must be refused"
    );
}

// ── further adversarial cases ───────────────────────────────────────────────────

#[test]
fn test_lrat_refuses_absent_hint_id() {
    // Point step0's first hint at an id that was never inserted: trieGet → nil,
    // which the `listNatIsCons` guard refuses (without the guard, nil would
    // reduce to [] and fabricate a conflict — the soundness boundary).
    let mut trace = base_trace();
    trace[0].1[0] = 99;
    assert_eq!(
        whnf_check_lrat(&base_clauses(), &trace),
        bfalse(),
        "an absent hint id must be refused by the listNatIsCons guard"
    );
}

#[test]
fn test_lrat_refuses_empty_trace() {
    let trace: Vec<LratStepData> = vec![];
    assert_eq!(
        whnf_check_lrat(&base_clauses(), &trace),
        bfalse(),
        "an empty trace is not a refutation"
    );
}

#[test]
fn test_lrat_refuses_forged_final_clause_without_conflict() {
    // Claim the empty clause directly from hints that do NOT reach conflict:
    // [] with hints [0] — c0 = (x ∨ y) reduces under F = {} to two unfalsified
    // literals.
    let trace: Vec<LratStepData> = vec![(vec![], vec![0])];
    assert_eq!(
        whnf_check_lrat(&base_clauses(), &trace),
        bfalse(),
        "an unjustified empty-clause step must be refused"
    );
}

#[test]
fn test_lrat_refuses_hints_exhausted_before_conflict() {
    // step0 with only its unit hint (c0): propagation asserts y but never
    // conflicts.
    let trace: Vec<LratStepData> = vec![(vec![(0, false)], vec![0])];
    assert_eq!(
        whnf_check_lrat(&base_clauses(), &trace),
        bfalse(),
        "hints exhausted before conflict must be refused"
    );
}

#[test]
fn test_lrat_accepts_trailing_unused_hints() {
    // Hints AFTER the conflict hint are ignored (soundly irrelevant): step0
    // justified by [0, 1] stays justified by [0, 1, 2].
    let mut trace = base_trace();
    trace[0].1.push(2);
    assert_eq!(
        whnf_check_lrat(&base_clauses(), &trace),
        btrue(),
        "trailing unused hints after the conflict are ignored"
    );
}

#[test]
fn test_lrat_accepts_duplicate_literal_unit() {
    // A hint clause with a DUPLICATE literal (the pinned neg_i8 miter carries
    // `(-1 -1 -35)`): c0 = (¬x ∨ ¬x), c1 = (x). The empty clause is RUP:
    // F = {}, hint c0 reduces to [¬x, ¬x] — semantically UNIT (the tail is a
    // duplicate copy of the head, `listIsNil (dropLit u tail)`) — asserting
    // ¬x; hint c1 = (x) then conflicts.
    let clauses = vec![vec![(0, true), (0, true)], vec![(0, false)]];
    let trace: Vec<LratStepData> = vec![(vec![], vec![0, 1])];
    assert_eq!(
        whnf_check_lrat(&clauses, &trace),
        btrue(),
        "a duplicate-literal unit hint must be accepted"
    );
}

#[test]
fn test_lrat_refuses_two_distinct_unfalsified_literals() {
    // The dropLit-based unit test must NOT loosen the ≥2-DISTINCT-literals
    // refusal: c0 = (x ∨ y) under F = {} reduces to [x, y] — not a unit.
    let clauses = vec![vec![(0, false), (1, false)], vec![(0, true)]];
    let trace: Vec<LratStepData> = vec![(vec![], vec![0, 1])];
    assert_eq!(
        whnf_check_lrat(&clauses, &trace),
        bfalse(),
        "two distinct unfalsified literals are not a unit"
    );
}

#[test]
fn test_lrat_single_step_direct_conflict() {
    // A DB with a direct contradiction: c0 = (x), c1 = (¬x). The empty clause
    // is RUP: F = {}, hint c0 = (x) is unit (asserts x), hint c1 = (¬x)
    // conflicts.
    let clauses = vec![vec![(0, false)], vec![(0, true)]];
    let trace: Vec<LratStepData> = vec![(vec![], vec![0, 1])];
    assert_eq!(
        whnf_check_lrat(&clauses, &trace),
        btrue(),
        "unit-unit conflict must be accepted"
    );
}

// ── the proven (initialTrie/listLen) form — checkLrat_sound's exact hypothesis ──

/// whnf of `checkLrat (initialTrie cs) (listLen cs) trace` — the proven-form
/// cert body (`cs` in the UNARY encoding the bridge's `Unsat cs` is about).
fn whnf_check_lrat_initialtrie(clauses: &[Vec<(u32, bool)>], trace: &[LratStepData]) -> Expr {
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness (registers initialTrie/listLen)");
    env.init_lrat_check().expect("init_lrat_check");
    let cs_lit = encode_clauses(clauses);
    let app = check_lrat_initialtrie_app(cs_lit, trace);
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.whnf(&app)
}

#[test]
fn test_lrat_initialtrie_valid_trace_reflects_to_true() {
    assert_eq!(
        whnf_check_lrat_initialtrie(&base_clauses(), &base_trace()),
        btrue(),
        "checkLrat (initialTrie cs)(listLen cs): valid trace must reflect to Bool.true"
    );
}

#[test]
fn test_lrat_initialtrie_corrupted_traces_reflect_to_false() {
    let mut dropped = base_trace();
    dropped[0].1.remove(0);
    let mut truncated = base_trace();
    truncated.truncate(2);
    for (label, trace) in [("dropped hint", dropped), ("truncated trace", truncated)] {
        assert_eq!(
            whnf_check_lrat_initialtrie(&base_clauses(), &trace),
            bfalse(),
            "checkLrat (initialTrie cs): {label} must reflect to Bool.false"
        );
    }
}
