// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the computational resolution-refutation checker (reflection backend).
//!
//! These confirm (1) the checker ops are reducible `Definition`s, (2) a valid
//! refutation reflects to `Bool.true` and an `Eq.refl` over it kernel-type-checks
//! TRACTABLY, (3) a TAMPERED refutation reflects to `Bool.false`, and (4) the
//! proved soundness endpoint `emptyClauseUnsat` has axiom closure ⊆ foundational.

use super::{check_refutes2_app, check_refutes_app, encode_clauses, encode_refutation, names};
use crate::name::Name;
use crate::{Environment, Expr, Level, TypeChecker};

fn env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_resolution_check().expect("init_resolution_check");
    env.init_resolution_check().expect("idempotent");
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

/// `@Eq.refl.{1} Bool v`.
fn eq_refl_bool(v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty(), v],
    )
}
/// `@Eq.{1} Bool x y`.
fn eq_bool(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [bool_ty(), x, y],
    )
}

/// All non-foundational axioms reachable from `name`.
fn domain_axioms(env: &Environment, name: &str) -> Vec<String> {
    let mut v: Vec<String> = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    v.sort();
    v
}

/// A tiny *valid* resolution refutation over 1 variable:
///   c0 = (x)        i.e. [(0,false)]
///   c1 = (¬x)       i.e. [(0,true)]
///   step: resolve c0 c1 on x → empty clause.
fn tiny_clauses() -> Vec<Vec<(u32, bool)>> {
    vec![vec![(0, false)], vec![(0, true)]]
}
fn tiny_refutation() -> Vec<(Vec<(u32, bool)>, u32, u32, u32)> {
    // (resolvent=[], prem1=0, prem2=1, pivot_var=0)
    vec![(vec![], 0, 1, 0)]
}

#[test]
fn test_checker_ops_are_reducible_definitions() {
    let env = env();
    use crate::ConstantKind;
    for op in [
        names::LIT_BEQ,
        names::LIT_NEG,
        names::CLAUSE_MEM,
        names::CLAUSE_SUBSET,
        names::CLAUSE_SETEQ,
        names::DROP_LIT,
        names::APPEND,
        names::CLAUSE_TAUT_FREE,
        names::RESOLVE,
        names::NTH,
        names::CHECK_STEP,
        names::CHECK_REFUTES,
    ] {
        let info = env
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} should be registered"));
        assert!(
            matches!(info.kind, ConstantKind::Definition),
            "{op} must be a Definition, not an axiom"
        );
    }
}

#[test]
fn test_valid_refutation_reflects_to_true() {
    let env = env();
    let cs = encode_clauses(&tiny_clauses());
    let pf = encode_refutation(&tiny_refutation());
    let app = check_refutes_app(cs, pf);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nf = tc.whnf(&app);
    assert_eq!(
        nf,
        btrue(),
        "valid refutation must reflect to Bool.true; got {nf:?}"
    );
}

#[test]
fn test_eq_refl_over_valid_refutation_typechecks() {
    let env = env();
    let cs = encode_clauses(&tiny_clauses());
    let pf = encode_refutation(&tiny_refutation());
    let app = check_refutes_app(cs, pf);
    // The reflection certificate: Eq.refl Bool.true : checkRefutes cs pf = Bool.true.
    let proof = eq_refl_bool(btrue());
    let goal = eq_bool(app, btrue());
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&proof, &goal)
        .expect("Eq.refl must type-check the reflection certificate");
}

#[test]
fn test_tampered_refutation_reflects_to_false() {
    let env = env();
    let cs = encode_clauses(&tiny_clauses());
    // TAMPER: claim the resolvent is (x) instead of the empty clause.
    let tampered: Vec<(Vec<(u32, bool)>, u32, u32, u32)> = vec![(vec![(0, false)], 0, 1, 0)];
    let pf = encode_refutation(&tampered);
    let app = check_refutes_app(cs, pf);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nf = tc.whnf(&app);
    assert_eq!(
        nf,
        bfalse(),
        "tampered refutation must reflect to Bool.false; got {nf:?}"
    );
}

#[test]
fn test_tampered_resolvent_not_empty_reflects_false() {
    let env = env();
    let cs = encode_clauses(&tiny_clauses());
    // Valid resolution shape but last clause not empty: a wrong pivot.
    let tampered: Vec<(Vec<(u32, bool)>, u32, u32, u32)> = vec![(vec![], 0, 1, 1)];
    let pf = encode_refutation(&tampered);
    let app = check_refutes_app(cs, pf);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nf = tc.whnf(&app);
    assert_eq!(nf, bfalse(), "wrong pivot must reflect to Bool.false");
}

/// Reduce `checkRefutes clauses refutation` to weak head normal form.
fn whnf_check(
    clauses: &[Vec<(u32, bool)>],
    refutation: &[(Vec<(u32, bool)>, u32, u32, u32)],
) -> Expr {
    let env = env();
    let cs = encode_clauses(clauses);
    let pf = encode_refutation(refutation);
    let app = check_refutes_app(cs, pf);
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.whnf(&app)
}

// ── adversarial regression tests for the resolution side condition (finding #20-1)
//
// These exercise INVALID-but-self-consistent resolutions: the recorded resolvent
// DOES set-equal the (wrongly) recomputed `resolve` result, so the seteq check
// alone passes. Only the opposite-polarity / tautology side conditions in
// checkStep reject them. Each MUST reflect to Bool.false.

#[test]
fn test_self_resolve_satisfiable_singleton_reflects_false() {
    // cs = {(x)} is SATISFIABLE. The bogus step self-resolves c0 with itself on x,
    // recording the empty clause. The unconditional `resolve` would strip x from
    // both copies and append → [], which set-equals the recorded []. Without the
    // opposite-polarity check this derived the empty clause from a SAT set (the
    // empirically confirmed hole). The pivot x appears POSITIVELY in both premises,
    // so the opposite-polarity condition fails → Bool.false.
    let cs = vec![vec![(0, false)]];
    let pf = vec![(vec![], 0, 0, 0)];
    assert_eq!(
        whnf_check(&cs, &pf),
        bfalse(),
        "self-resolving a satisfiable singleton must NOT prove unsat"
    );
}

#[test]
fn test_same_polarity_premises_reflects_false() {
    // Two distinct premises sharing the pivot with the SAME polarity:
    //   c0 = (x ∨ y),  c1 = (x ∨ ¬y).  Resolving on x is invalid (x positive in
    // both). `resolve` strips x from both → (y) ++ (¬y); recorded resolvent (y,¬y)
    // would set-equal it, but x is not opposite-polarity → Bool.false.
    let cs = vec![vec![(0, false), (1, false)], vec![(0, false), (1, true)]];
    let pf = vec![(vec![(1, false), (1, true)], 0, 1, 0)];
    assert_eq!(
        whnf_check(&cs, &pf),
        bfalse(),
        "same-polarity pivot across premises must reflect to Bool.false"
    );
}

#[test]
fn test_absent_pivot_reflects_false() {
    // Pivot var 5 appears in NEITHER premise. `resolve` drops nothing and appends
    // → (x) ++ (¬x) = (x,¬x); a recorded (x,¬x) would set-equal it. But the pivot
    // is absent from both premises, so the opposite-polarity condition fails AND the
    // resolvent is tautological → Bool.false.
    let cs = vec![vec![(0, false)], vec![(0, true)]];
    let pf = vec![(vec![(0, false), (0, true)], 0, 1, 5)];
    assert_eq!(
        whnf_check(&cs, &pf),
        bfalse(),
        "a pivot absent from both premises must reflect to Bool.false"
    );
}

#[test]
fn test_tautological_resolvent_reflects_false() {
    // A genuine opposite-polarity resolution on x whose resolvent is TAUTOLOGICAL:
    //   c0 = (x ∨ y),  c1 = (¬x ∨ ¬y).  Resolving on x → (y ∨ ¬y), a tautology.
    // Opposite-polarity holds, seteq holds, but the tautology-free check rejects it.
    let cs = vec![vec![(0, false), (1, false)], vec![(0, true), (1, true)]];
    let pf = vec![(vec![(1, false), (1, true)], 0, 1, 0)];
    assert_eq!(
        whnf_check(&cs, &pf),
        bfalse(),
        "a tautological resolvent must reflect to Bool.false"
    );
}

#[test]
fn test_valid_opposite_polarity_still_reflects_true() {
    // Positive control: a genuine, non-tautological opposite-polarity resolution to
    // the empty clause MUST still reflect to Bool.true after the hardening.
    assert_eq!(
        whnf_check(&tiny_clauses(), &tiny_refutation()),
        btrue(),
        "a valid refutation must still reflect to Bool.true after the side-condition fix"
    );
}

#[test]
fn test_empty_clause_unsat_axiom_closure_foundational() {
    let env = env();
    let axs = domain_axioms(&env, names::EMPTY_CLAUSE_UNSAT);
    assert!(
        axs.is_empty(),
        "emptyClauseUnsat must have empty domain-axiom closure; got {axs:?}"
    );
}

#[test]
fn test_check_refutes_sound_not_auto_registered() {
    // The unproved soundness bridge must NOT be injected into every environment by
    // init_resolution_check (finding #20-2): a global, citable, unproved axiom is a
    // soundness liability. It is only present after an explicit opt-in.
    let env = env();
    assert!(
        env.get_const(&Name::from_string(names::CHECK_REFUTES_SOUND))
            .is_none(),
        "checkRefutes_sound must NOT be auto-registered by init_resolution_check"
    );
}

#[test]
fn test_check_refutes_sound_opt_in_is_now_proved_theorem() {
    // As of #22 the opt-in registers the PROVED soundness bridge (a kernel-checked
    // Theorem with foundational axiom closure), no longer a stated axiom.
    use crate::ConstantKind;
    let mut env = env();
    env.register_check_refutes_sound_stmt()
        .expect("opt-in registration (now proves the theorem)");
    let info = env
        .get_const(&Name::from_string(names::CHECK_REFUTES_SOUND))
        .expect("checkRefutes_sound registered after opt-in");
    assert!(
        matches!(info.kind, ConstantKind::Theorem),
        "checkRefutes_sound is now a PROVED Theorem (was a stated Axiom before #22)"
    );
    let mut axs: Vec<String> = env
        .axiom_deps(&Name::from_string(names::CHECK_REFUTES_SOUND))
        .expect("registered")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    axs.sort();
    assert!(
        axs.is_empty(),
        "checkRefutes_sound must have empty domain-axiom closure; got {axs:?}"
    );
}

// ── checkRefutes2 (db-free, newest-first) — must MIRROR checkRefutes ───────────
//
// These pin the PERFORMANCE reformulation to the SAME reduction outcome as the
// proven `checkRefutes`: genuine refutations → Bool.true, every forgery →
// Bool.false. They are the fast (single-variable / few-step) gate; the heavy
// real-refutation smoke test + measurement live in clean-auto.

/// Reduce `checkRefutes2 clauses refutation` to weak head normal form.
fn whnf_check2(
    clauses: &[Vec<(u32, bool)>],
    refutation: &[(Vec<(u32, bool)>, u32, u32, u32)],
) -> Expr {
    let env = env();
    let cs = encode_clauses(clauses);
    let pf = encode_refutation(refutation);
    let app = check_refutes2_app(cs, pf);
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.whnf(&app)
}

/// A 2-step refutation whose SECOND step cites a DERIVED clause as a premise —
/// the case that exercises `clauseOf2`'s newest-first recency lookup.
///   c0 = (x∨y)[id0], c1 = (¬x∨y)[id1], c2 = (¬y)[id2]
///   step0: resolve c0,c1 on x  → (y)   [derived id3]
///   step1: resolve id3,c2 on y → ()    [empty]
fn derived_premise_clauses() -> Vec<Vec<(u32, bool)>> {
    vec![
        vec![(0, false), (1, false)],
        vec![(0, true), (1, false)],
        vec![(1, true)],
    ]
}
fn derived_premise_refutation() -> Vec<(Vec<(u32, bool)>, u32, u32, u32)> {
    vec![
        (vec![(1, false)], 0, 1, 0), // resolvent (y), premises c0,c1, pivot x
        (vec![], 3, 2, 1),           // resolvent (), premises derived id3 & c2, pivot y
    ]
}

#[test]
fn test2_checker2_ops_are_reducible_definitions() {
    let env = env();
    use crate::ConstantKind;
    for op in [
        names::LIST_LEN,
        names::CLAUSE_OF2,
        names::CHECK_STEP2,
        names::CHECK_REFUTES2,
    ] {
        let info = env
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} should be registered"));
        assert!(
            matches!(info.kind, ConstantKind::Definition),
            "{op} must be a Definition, not an axiom"
        );
    }
}

#[test]
fn test2_valid_refutation_reflects_to_true() {
    assert_eq!(
        whnf_check2(&tiny_clauses(), &tiny_refutation()),
        btrue(),
        "checkRefutes2: valid refutation must reflect to Bool.true"
    );
    // Agreement with checkRefutes on the same input.
    assert_eq!(
        whnf_check(&tiny_clauses(), &tiny_refutation()),
        whnf_check2(&tiny_clauses(), &tiny_refutation()),
        "checkRefutes2 must AGREE with checkRefutes"
    );
}

#[test]
fn test2_derived_premise_refutation_reflects_to_true() {
    // The key newest-first case: step1 cites derived clause id3.
    assert_eq!(
        whnf_check2(&derived_premise_clauses(), &derived_premise_refutation()),
        btrue(),
        "checkRefutes2: refutation citing a DERIVED clause must reflect to Bool.true"
    );
    assert_eq!(
        whnf_check(&derived_premise_clauses(), &derived_premise_refutation()),
        btrue(),
        "checkRefutes must also accept the derived-premise refutation (agreement)"
    );
}

#[test]
fn test2_tampered_refutation_reflects_to_false() {
    let tampered: Vec<(Vec<(u32, bool)>, u32, u32, u32)> = vec![(vec![(0, false)], 0, 1, 0)];
    assert_eq!(
        whnf_check2(&tiny_clauses(), &tampered),
        bfalse(),
        "checkRefutes2: tampered (non-empty final resolvent) must reflect to Bool.false"
    );
}

#[test]
fn test2_wrong_pivot_reflects_to_false() {
    let tampered: Vec<(Vec<(u32, bool)>, u32, u32, u32)> = vec![(vec![], 0, 1, 1)];
    assert_eq!(
        whnf_check2(&tiny_clauses(), &tampered),
        bfalse(),
        "checkRefutes2: wrong pivot must reflect to Bool.false"
    );
}

#[test]
fn test2_out_of_range_premise_reflects_to_false() {
    // The SOUNDNESS-CRITICAL bound check: cite a premise id ≥ |cs| + count with no
    // derived clauses yet. Without `boundOk`, the truncated Nat.sub would alias id 7
    // to recency 0 (most-recent derived) — but there ARE no derived clauses, and the
    // bound check rejects it outright. Must reflect to Bool.false.
    let cs = tiny_clauses(); // |cs| = 2, count starts at 0
    let forged: Vec<(Vec<(u32, bool)>, u32, u32, u32)> = vec![(vec![], 0, 7, 0)];
    assert_eq!(
        whnf_check2(&cs, &forged),
        bfalse(),
        "checkRefutes2: out-of-range premise id must reflect to Bool.false (bound check)"
    );
    // checkRefutes agrees (its `nth` returns nil past the end → resolve mismatch).
    assert_eq!(
        whnf_check(&cs, &forged),
        bfalse(),
        "checkRefutes also rejects the out-of-range premise (agreement)"
    );
}

#[test]
fn test2_self_resolve_satisfiable_singleton_reflects_false() {
    let cs = vec![vec![(0, false)]];
    let pf = vec![(vec![], 0, 0, 0)];
    assert_eq!(
        whnf_check2(&cs, &pf),
        bfalse(),
        "checkRefutes2: self-resolving a satisfiable singleton must NOT prove unsat"
    );
}

#[test]
fn test2_tautological_resolvent_reflects_false() {
    let cs = vec![vec![(0, false), (1, false)], vec![(0, true), (1, true)]];
    let pf = vec![(vec![(1, false), (1, true)], 0, 1, 0)];
    assert_eq!(
        whnf_check2(&cs, &pf),
        bfalse(),
        "checkRefutes2: a tautological resolvent must reflect to Bool.false"
    );
}

#[test]
fn test2_forged_middle_premise_in_derived_chain_reflects_false() {
    // Corrupt the 2-step derived chain's SECOND step to cite a wrong premise (c0
    // instead of derived id3), so the recorded empty resolvent no longer follows.
    let cs = derived_premise_clauses();
    let mut pf = derived_premise_refutation();
    pf[1] = (vec![], 0, 2, 1); // premise 0 = c0=(x∨y) not the derived (y)
    assert_eq!(
        whnf_check2(&cs, &pf),
        bfalse(),
        "checkRefutes2: forged middle premise must reflect to Bool.false"
    );
    assert_eq!(
        whnf_check(&cs, &pf),
        bfalse(),
        "checkRefutes agrees on the forged middle premise"
    );
}

// ── checkRefutes3 (sub-quadratic Nat-indexed trie) unit tests ──────────────────

use super::{check_refutes3_app, encode_clauses_lit, encode_initial_trie};

/// `trieGet <trie> <id>` reduced to whnf.
fn whnf_trie_get(trie: Expr, id: u64) -> Expr {
    let env = env();
    let app = Expr::apps(Expr::const_str(names::TRIE_GET), [trie, Expr::nat_lit(id)]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.whnf(&app)
}

/// whnf of the i-th clause of `clauses` under the LITERAL-id encoding (the value a
/// correct `trieGet` should return). Built by `nth (encode_clauses_lit ..) i` so we
/// compare against the kernel's own normal form for that literal clause.
fn whnf_nth_lit_clause(clauses: &[Vec<(u32, bool)>], i: u64) -> Expr {
    let env = env();
    let app = Expr::apps(
        Expr::const_str(names::NTH),
        [encode_clauses_lit(clauses), Expr::nat_lit(i)],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.whnf(&app)
}

#[test]
fn test3_trie_get_after_ins_returns_inserted_clause() {
    // Build the initial trie of `derived_premise_clauses` (ids 0,1,2) and confirm
    // trieGet returns each inserted clause (descending on the TRIE by the bits of a
    // LITERAL id — not by Nat.rec on the key).
    let clauses = derived_premise_clauses();
    let trie = encode_initial_trie(&clauses);
    for i in 0..clauses.len() as u64 {
        assert_eq!(
            whnf_trie_get(trie.clone(), i),
            whnf_nth_lit_clause(&clauses, i),
            "trieGet must return the clause inserted at id {i}"
        );
    }
}

#[test]
fn test3_trie_get_absent_id_returns_nil() {
    // An id never inserted must return `nil` (so an absent premise fails clauseSeteq,
    // exactly like an out-of-range `nth`).
    let clauses = derived_premise_clauses(); // ids 0..2 present
    let trie = encode_initial_trie(&clauses);
    let nil = super::list_nil(Expr::const_str("Nat"));
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for absent in [3u64, 7, 64, 1000] {
        assert_eq!(
            whnf_trie_get(trie.clone(), absent),
            tc.whnf(&nil),
            "trieGet on absent id {absent} must be nil"
        );
    }
}

/// Reduce `checkRefutes3` on (clauses, refutation) to whnf (literal-id trie checker).
fn whnf_check3(
    clauses: &[Vec<(u32, bool)>],
    refutation: &[(Vec<(u32, bool)>, u32, u32, u32)],
) -> Expr {
    let env = env();
    let app = check_refutes3_app(clauses, refutation);
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.whnf(&app)
}

#[test]
fn test3_checker3_ops_are_reducible_definitions() {
    use crate::ConstantKind;
    let env = env();
    for op in [
        names::TRIE_GET,
        names::TRIE_INS,
        names::CHECK_STEP3,
        names::CHECK_REFUTES3,
    ] {
        let info = env
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} should be registered"));
        assert!(
            matches!(info.kind, ConstantKind::Definition),
            "{op} must be a Definition, not an axiom"
        );
    }
    // Trie is an inductive with a kernel-derived recursor.
    assert!(
        env.get_inductive(&Name::from_string(names::TRIE)).is_some(),
        "Trie inductive must be registered"
    );
    assert!(
        env.get_const(&Name::from_string("Clean.Res.Trie.rec"))
            .is_some(),
        "Trie.rec must be derived"
    );
}

#[test]
fn test3_valid_refutation_reflects_to_true() {
    assert_eq!(
        whnf_check3(&tiny_clauses(), &tiny_refutation()),
        btrue(),
        "checkRefutes3: valid refutation must reflect to Bool.true"
    );
    assert_eq!(
        whnf_check(&tiny_clauses(), &tiny_refutation()),
        whnf_check3(&tiny_clauses(), &tiny_refutation()),
        "checkRefutes3 must AGREE with checkRefutes (tiny)"
    );
}

#[test]
fn test3_derived_premise_refutation_reflects_to_true() {
    // The 2-step chain whose step1 cites the DERIVED clause id3 — exercises a
    // trieIns of the derived resolvent followed by a trieGet of it.
    assert_eq!(
        whnf_check3(&derived_premise_clauses(), &derived_premise_refutation()),
        btrue(),
        "checkRefutes3: refutation citing a DERIVED clause must reflect to Bool.true"
    );
    assert_eq!(
        whnf_check(&derived_premise_clauses(), &derived_premise_refutation()),
        whnf_check3(&derived_premise_clauses(), &derived_premise_refutation()),
        "checkRefutes3 must AGREE with checkRefutes (derived premise)"
    );
}

#[test]
fn test3_tampered_refutation_reflects_to_false() {
    let tampered: Vec<(Vec<(u32, bool)>, u32, u32, u32)> = vec![(vec![(0, false)], 0, 1, 0)];
    assert_eq!(
        whnf_check3(&tiny_clauses(), &tampered),
        bfalse(),
        "checkRefutes3: non-empty final resolvent must reflect to Bool.false"
    );
}

#[test]
fn test3_wrong_pivot_reflects_to_false() {
    let tampered: Vec<(Vec<(u32, bool)>, u32, u32, u32)> = vec![(vec![], 0, 1, 1)];
    assert_eq!(
        whnf_check3(&tiny_clauses(), &tampered),
        bfalse(),
        "checkRefutes3: wrong pivot must reflect to Bool.false"
    );
}

#[test]
fn test3_absent_premise_reflects_to_false() {
    // Cite a premise id that was never inserted: trieGet → nil → resolve mismatch.
    let cs = tiny_clauses();
    let forged: Vec<(Vec<(u32, bool)>, u32, u32, u32)> = vec![(vec![], 0, 7, 0)];
    assert_eq!(
        whnf_check3(&cs, &forged),
        bfalse(),
        "checkRefutes3: absent premise id must reflect to Bool.false"
    );
    assert_eq!(
        whnf_check(&cs, &forged),
        whnf_check3(&cs, &forged),
        "checkRefutes3 agrees with checkRefutes on the absent premise"
    );
}

#[test]
fn test3_forged_middle_premise_in_derived_chain_reflects_false() {
    let cs = derived_premise_clauses();
    let mut pf = derived_premise_refutation();
    pf[1] = (vec![], 0, 2, 1); // cite c0 not the derived (y)
    assert_eq!(
        whnf_check3(&cs, &pf),
        bfalse(),
        "checkRefutes3: forged middle premise must reflect to Bool.false"
    );
    assert_eq!(
        whnf_check(&cs, &pf),
        whnf_check3(&cs, &pf),
        "checkRefutes3 agrees on the forged middle premise"
    );
}

// ── checkRefutes3_initialtrie_app: the PROVEN-form builder for checkRefutes3_sound ──
//
// `check_refutes3_initialtrie_app` builds `checkRefutes3 (initialTrie cs) (listLen cs)
// steps` — the EXACT shape of `checkRefutes3_sound`'s hypothesis — by applying the
// kernel `initialTrie`/`listLen` DEFINITIONS to the literal `cs` (rather than nesting
// `trieIns` at encode time). These tests confirm the kernel REDUCES that proven form to
// `Bool.true` on a genuine refutation and `Bool.false` on a forged one, so an
// `Eq.refl Bool.true` cert at this term genuinely discharges `checkRefutes3_sound`.

use super::check_refutes3_initialtrie_app;

/// Env with `init_resolution_soundness` (registers `initialTrie`/`listLen` + the
/// `checkRefutes3_sound` theorem). `initialTrie` is NOT in `init_resolution_check`.
fn sound_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");
    env
}

/// whnf of `checkRefutes3 (initialTrie (encode_clauses cs)) (listLen (encode_clauses cs))
/// (encode_refutation_lit steps)` — the proven-form cert body. `cs` is encoded with the
/// UNARY `encode_clauses` (the form the lowering bridge's `Unsat cs` is about).
fn whnf_check3_initialtrie(
    clauses: &[Vec<(u32, bool)>],
    refutation: &[(Vec<(u32, bool)>, u32, u32, u32)],
) -> Expr {
    let env = sound_env();
    let cs_lit = encode_clauses(clauses);
    let app = check_refutes3_initialtrie_app(cs_lit, refutation);
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.whnf(&app)
}

#[test]
fn test3_initialtrie_valid_refutation_reflects_to_true() {
    assert_eq!(
        whnf_check3_initialtrie(&tiny_clauses(), &tiny_refutation()),
        btrue(),
        "checkRefutes3 (initialTrie cs)(listLen cs): valid refutation must reflect to Bool.true"
    );
    assert_eq!(
        whnf_check3_initialtrie(&derived_premise_clauses(), &derived_premise_refutation()),
        btrue(),
        "checkRefutes3 (initialTrie cs): refutation citing a DERIVED clause reflects to Bool.true"
    );
}

#[test]
fn test3_initialtrie_eq_refl_typechecks_the_proven_form() {
    // Eq.refl Bool.true : checkRefutes3 (initialTrie cs)(listLen cs) steps = Bool.true.
    // This is the exact cert `checkRefutes3_sound` consumes.
    let env = sound_env();
    let cs_lit = encode_clauses(&tiny_clauses());
    let app = check_refutes3_initialtrie_app(cs_lit, &tiny_refutation());
    let proof = eq_refl_bool(btrue());
    let goal = eq_bool(app, btrue());
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&proof, &goal)
        .expect("Eq.refl must type-check the proven-form (initialTrie/listLen) reflection cert");
}

#[test]
fn test3_initialtrie_tampered_refutation_reflects_to_false() {
    let tampered: Vec<(Vec<(u32, bool)>, u32, u32, u32)> = vec![(vec![(0, false)], 0, 1, 0)];
    assert_eq!(
        whnf_check3_initialtrie(&tiny_clauses(), &tampered),
        bfalse(),
        "checkRefutes3 (initialTrie cs): non-empty final resolvent must reflect to Bool.false"
    );
    // A forged (absent) premise id must also fail through the initialTrie form.
    let forged: Vec<(Vec<(u32, bool)>, u32, u32, u32)> = vec![(vec![], 0, 7, 0)];
    assert_eq!(
        whnf_check3_initialtrie(&tiny_clauses(), &forged),
        bfalse(),
        "checkRefutes3 (initialTrie cs): absent premise id must reflect to Bool.false"
    );
}
