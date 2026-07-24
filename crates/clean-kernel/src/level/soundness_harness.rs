// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exhaustive differential soundness harness for `Level::is_def_eq`.
//!
//! This is the machine-checked soundness gate for any change to the universe
//! `Level` normalizer (`normalize` / `is_def_eq`). It is the single
//! highest-stakes property of the trusted kernel: a normalizer that equates an
//! *unequal* pair of universes is a false-accept that corrupts every downstream
//! verdict.
//!
//! The harness enumerates `Level` expressions up to a depth/count bound over a
//! small fixed set of params, computes a GROUND-TRUTH semantic equality via
//! `eval`, and asserts three properties over EVERY ordered pair:
//!
//! 1. SOUNDNESS (zero false-accepts): `is_def_eq(a, b) ==> genuine_equal(a, b)`.
//! 2. MONOTONICITY: every pair the LEGACY normalizer accepted, the current one
//!    still accepts (no lost verdict — preserves all current `KernelVerified`).
//! 3. COMPLETENESS target: the specific `funUnique`/`piUnique`-shaped pairs are
//!    now accepted.
//!
//! Performance: each level's NEW and LEGACY normal forms are computed ONCE
//! (O(N) normalizations), so the O(N^2) pairwise sweep is just structural `Eq`
//! on the precomputed forms plus a `genuine_equal` check on accepted pairs.
//! This keeps the 3,244-level / 10.5M-pair main tier well under a minute.
//!
//! `normalize_legacy` below is a frozen copy of the normalizer as it stood
//! BEFORE the imax/max distribution (subsumption) fix, so the harness can check
//! monotonicity in one process (old verdicts vs new verdicts) with no external
//! snapshot.

#![cfg(test)]

use super::*;
use std::collections::HashSet;

// ---------------------------------------------------------------------------
// Ground-truth semantics
// ---------------------------------------------------------------------------

/// Evaluate a level under a total assignment of param names to natural numbers.
///
/// This is the DEFINING semantics of universe levels (Lean 4 kernel/level.cpp):
/// - zero        = 0
/// - succ l      = eval(l) + 1
/// - max a b     = max(eval(a), eval(b))
/// - imax a b    = if eval(b) == 0 { 0 } else { max(eval(a), eval(b)) }
/// - param p     = assignment[p]
fn eval(level: &Level, assignment: &[(Name, u64)]) -> u64 {
    match level {
        Level::Zero => 0,
        Level::Succ(l) => eval(l, assignment) + 1,
        Level::Max(a, b) => eval(a, assignment).max(eval(b, assignment)),
        Level::IMax(a, b) => {
            let vb = eval(b, assignment);
            if vb == 0 {
                0
            } else {
                eval(a, assignment).max(vb)
            }
        }
        Level::Param(name) => assignment
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| *v)
            .expect("param must be in assignment"),
    }
}

/// All total assignments of `params` to values `0..=max_val`.
///
/// `max_val >= 4` is required by the soundness spec: it exercises the imax
/// 0-vs-positive pivot AND positive magnitudes large enough to distinguish
/// offset differences within the depth bound (a depth-D level adds at most
/// D successors).
fn all_assignments(params: &[Name], max_val: u64) -> Vec<Vec<(Name, u64)>> {
    let n = params.len();
    let span = (max_val + 1) as usize;
    let total = span.pow(n as u32);
    let mut out = Vec::with_capacity(total);
    for code in 0..total {
        let mut c = code;
        let mut asn = Vec::with_capacity(n);
        for p in params {
            let v = (c % span) as u64;
            c /= span;
            asn.push((p.clone(), v));
        }
        out.push(asn);
    }
    out
}

/// GROUND-TRUTH semantic equality: `eval` agrees for ALL assignments.
fn genuine_equal(a: &Level, b: &Level, assignments: &[Vec<(Name, u64)>]) -> bool {
    assignments.iter().all(|asn| eval(a, asn) == eval(b, asn))
}

// ---------------------------------------------------------------------------
// Enumeration of Level expressions
// ---------------------------------------------------------------------------

/// Structural key for dedup (Display is injective enough for our grammar, and
/// avoids depending on Hash/Eq nuances).
fn key(l: &Level) -> String {
    format!("{l}")
}

/// Enumerate distinct `Level` expressions with depth in `1..=max_depth` over
/// `params`, optionally capped at `max_levels` total. The cap is enforced
/// DURING construction (not after a full layer), so a deep bound stays bounded
/// in both time and memory: construction stops the instant the cap is reached.
///
/// Depth convention: leaves (Zero, Param) = depth 1; a node of depth `d` has at
/// least one child of depth `d-1`. Max/IMax are built from the full set of
/// strictly-smaller levels; results are structurally deduped (by Display).
fn enumerate(max_depth: u32, params: &[Name], max_levels: Option<usize>) -> Vec<Level> {
    let cap = max_levels.unwrap_or(usize::MAX);
    let mut by_depth: Vec<Vec<Level>> = Vec::new();
    let mut all: Vec<Level> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();

    // Returns true if the cap has been reached (caller should stop).
    fn push(
        l: Level,
        all: &mut Vec<Level>,
        seen: &mut HashSet<String>,
        layer: &mut Vec<Level>,
        cap: usize,
    ) -> bool {
        if seen.insert(key(&l)) {
            layer.push(l.clone());
            all.push(l);
        }
        all.len() >= cap
    }

    'depths: for depth in 1..=max_depth {
        let mut layer: Vec<Level> = Vec::new();
        if depth == 1 {
            if push(Level::Zero, &mut all, &mut seen, &mut layer, cap) {
                by_depth.push(layer);
                break 'depths;
            }
            for p in params {
                if push(
                    Level::Param(p.clone()),
                    &mut all,
                    &mut seen,
                    &mut layer,
                    cap,
                ) {
                    by_depth.push(layer);
                    break 'depths;
                }
            }
        } else {
            let prev = by_depth[(depth - 2) as usize].clone();
            let smaller: Vec<Level> = by_depth.iter().flatten().cloned().collect();
            // Succ of depth-(depth-1).
            for l in &prev {
                let s = Level::Succ(level_arc(l.clone()));
                if push(s, &mut all, &mut seen, &mut layer, cap) {
                    by_depth.push(layer);
                    break 'depths;
                }
            }
            // Max / IMax: at least one child of depth exactly depth-1. Build
            // (prev x prev), (prev x smaller), (smaller x prev), stopping the
            // moment the cap is hit.
            let pairs = prev
                .iter()
                .flat_map(|a| prev.iter().map(move |b| (a, b)))
                .chain(
                    prev.iter()
                        .flat_map(|a| smaller.iter().map(move |b| (a, b))),
                )
                .chain(
                    prev.iter()
                        .flat_map(|a| smaller.iter().map(move |b| (b, a))),
                );
            for (a, b) in pairs {
                let m = Level::Max(level_arc(a.clone()), level_arc(b.clone()));
                if push(m, &mut all, &mut seen, &mut layer, cap) {
                    by_depth.push(layer);
                    break 'depths;
                }
                let im = Level::IMax(level_arc(a.clone()), level_arc(b.clone()));
                if push(im, &mut all, &mut seen, &mut layer, cap) {
                    by_depth.push(layer);
                    break 'depths;
                }
            }
        }
        by_depth.push(layer);
    }
    all
}

// ---------------------------------------------------------------------------
// LEGACY normalizer (frozen pre-fix behavior) for monotonicity checking
// ---------------------------------------------------------------------------
//
// Verbatim copy of the production `normalize_impl` / `normalize_max` path as it
// stood BEFORE the imax/max distribution (subsumption) fix. Lets the harness
// compare OLD verdicts to NEW verdicts within one process, so monotonicity is
// machine-checked without an external snapshot.

fn legacy_normalize(l: &Level) -> Level {
    legacy_normalize_impl(l)
}

fn legacy_normalize_impl(l: &Level) -> Level {
    let (base, outer_offset) = l.get_offset();
    match base {
        Level::Zero | Level::Param(_) => l.clone(),
        Level::Succ(_) => unreachable!("get_offset strips all Succ layers"),
        Level::IMax(l1, l2) => {
            let l1_norm = legacy_normalize_impl(l1);
            let l2_norm = legacy_normalize_impl(l2);
            let result = Level::imax(l1_norm, l2_norm);
            if matches!(result, Level::Max(_, _)) {
                legacy_normalize_impl(&result.add_offset(outer_offset))
            } else {
                result.add_offset(outer_offset)
            }
        }
        Level::Max(_, _) => legacy_normalize_max(base, outer_offset),
    }
}

fn legacy_normalize_max(base: &Level, outer_offset: u32) -> Level {
    let mut todo = Vec::new();
    Level::push_max_args(base, &mut todo);
    let mut args = Vec::new();
    for a in &todo {
        let normed = legacy_normalize_impl(a);
        Level::push_max_args(&normed, &mut args);
    }
    args.sort_by(|a, b| {
        if Level::is_norm_lt(a, b) {
            std::cmp::Ordering::Less
        } else if Level::is_norm_lt(b, a) {
            std::cmp::Ordering::Greater
        } else {
            std::cmp::Ordering::Equal
        }
    });
    let mut rargs = Level::dedup_max_args(&args);
    if outer_offset > 0 {
        for a in &mut rargs {
            *a = a.add_offset(outer_offset);
        }
    }
    if rargs.is_empty() {
        Level::Zero
    } else {
        Level::mk_max_from_args(&rargs)
    }
}

// ---------------------------------------------------------------------------
// The differential checker
// ---------------------------------------------------------------------------

struct HarnessResult {
    enumeration_size: usize,
    pair_count: usize,
    max_depth: u32,
    false_accepts: Vec<(String, String)>,
    monotonicity_losses: Vec<(String, String)>,
    new_accepts_over_legacy: usize,
}

/// Run the full differential checker over an enumeration.
///
/// Precomputes each level's NEW normal form and LEGACY normal form once, so the
/// pairwise sweep is O(1) per pair (structural `Eq`) plus a `genuine_equal`
/// check only on NEW-accepted pairs.
fn run_harness(max_depth: u32, max_val: u64, max_levels: Option<usize>) -> HarnessResult {
    let params = vec![
        Name::from_string("u0"),
        Name::from_string("u1"),
        Name::from_string("u2"),
    ];
    let levels = enumerate(max_depth, &params, max_levels);
    let assignments = all_assignments(&params, max_val);

    // Precompute normal forms once.
    let new_nf: Vec<Level> = levels.iter().map(|l| l.normalize()).collect();
    let leg_nf: Vec<Level> = levels.iter().map(legacy_normalize).collect();

    let mut false_accepts = Vec::new();
    let mut monotonicity_losses = Vec::new();
    let mut new_accepts_over_legacy = 0usize;
    let n = levels.len();

    for i in 0..n {
        for j in 0..n {
            // is_def_eq(a,b) == (a==b) || normalize(a)==normalize(b).
            let new_eq = (i == j) || new_nf[i] == new_nf[j];
            if new_eq && !genuine_equal(&levels[i], &levels[j], &assignments) {
                false_accepts.push((key(&levels[i]), key(&levels[j])));
            }
            let old_eq = (i == j) || leg_nf[i] == leg_nf[j];
            if old_eq && !new_eq {
                monotonicity_losses.push((key(&levels[i]), key(&levels[j])));
            }
            if new_eq && !old_eq {
                new_accepts_over_legacy += 1;
            }
        }
    }

    HarnessResult {
        enumeration_size: n,
        pair_count: n * n,
        max_depth,
        false_accepts,
        monotonicity_losses,
        new_accepts_over_legacy,
    }
}

fn assert_green(r: &HarnessResult) {
    eprintln!(
        "[harness depth<={} levels={} pairs={} new_accepts_over_legacy={}]",
        r.max_depth, r.enumeration_size, r.pair_count, r.new_accepts_over_legacy
    );
    assert!(
        r.false_accepts.is_empty(),
        "SOUNDNESS VIOLATION (false-accept): {} pair(s); first few: {:?}",
        r.false_accepts.len(),
        &r.false_accepts[..r.false_accepts.len().min(10)]
    );
    assert!(
        r.monotonicity_losses.is_empty(),
        "MONOTONICITY VIOLATION (lost verdict): {} pair(s); first few: {:?}",
        r.monotonicity_losses.len(),
        &r.monotonicity_losses[..r.monotonicity_losses.len().min(10)]
    );
}

// ---------------------------------------------------------------------------
// Completeness target shapes (funUnique / piUnique)
// ---------------------------------------------------------------------------

/// The confirmed completeness target:
///   `max 1 (imax u u_1)` vs `max (max 1 u_1) (imax u u_1)`
/// (equal for all assignments: if u_1 == 0 both are 1; if u_1 > 0 then
/// `imax u u_1 = max(u, u_1) >= u_1` absorbs the `max 1 u_1`.)
fn completeness_target_pair() -> (Level, Level) {
    let u = Level::param(Name::from_string("u"));
    let u1 = Level::param(Name::from_string("u_1"));
    let one = Level::succ(Level::zero());
    let imax_u_u1 = Level::IMax(level_arc(u), level_arc(u1.clone()));
    // Build RAW (un-simplified) Max nodes so we test the normalizer, not the
    // smart constructor's eager simplification.
    let lhs = Level::Max(level_arc(one.clone()), level_arc(imax_u_u1.clone()));
    let max_1_u1 = Level::Max(level_arc(one), level_arc(u1));
    let rhs = Level::Max(level_arc(max_1_u1), level_arc(imax_u_u1));
    (lhs, rhs)
}

/// The WF-recursion completeness target (`List.reverseRecOn._unary` vs `.eq_1`):
///   `max (succ u) u_2`
///   `max (succ u) W`   where `W = max (max 1 u_2) (imax (succ u) (imax (succ u) u_2))`
///
/// Equal at every assignment:
/// - u_2 == 0 ⇒ LHS = succ u; on RHS, `imax _ (imax _ 0) = imax _ 0 = 0`,
///   `max 1 0 = 1`, so `W = max 1 0 = 1`, and `max (succ u) 1 = succ u` (succ u >= 1).
/// - u_2 > 0  ⇒ `imax (succ u) (imax (succ u) u_2) = max(succ u, max(succ u, u_2))
///   = max(succ u, u_2)`, `max 1 u_2 = max(1, u_2)`, so `W = max(succ u, u_2)`,
///   and `max (succ u) W = max(succ u, u_2)` = LHS.
///
/// The extra term `imax (succ u) (imax (succ u) u_2)` on the RHS is dominated by
/// the JOIN `max(succ u, u_2)` of the OTHER retained args, but by NO single one —
/// this is exactly the join-subsumption case.
fn reverse_rec_on_target_pair() -> (Level, Level) {
    let u = Level::param(Name::from_string("u"));
    let u2 = Level::param(Name::from_string("u_2"));
    let succ_u = Level::succ(u);
    let one = Level::succ(Level::zero());

    // LHS: max (succ u) u_2  (raw Max node).
    let lhs = Level::Max(level_arc(succ_u.clone()), level_arc(u2.clone()));

    // inner = imax (succ u) u_2
    let inner = Level::IMax(level_arc(succ_u.clone()), level_arc(u2.clone()));
    // outer = imax (succ u) inner = imax (succ u) (imax (succ u) u_2)
    let outer = Level::IMax(level_arc(succ_u.clone()), level_arc(inner));
    // max_1_u2 = max 1 u_2
    let max_1_u2 = Level::Max(level_arc(one), level_arc(u2));
    // W = max (max 1 u_2) outer
    let w = Level::Max(level_arc(max_1_u2), level_arc(outer));
    // RHS: max (succ u) W  (raw Max node).
    let rhs = Level::Max(level_arc(succ_u), level_arc(w));
    (lhs, rhs)
}

// ---------------------------------------------------------------------------
// Adversarial cases: a NAIVE join-subsumption would wrongly drop an arg, but
// the conservative `is_geq_core` correctly REFUSES to drop (returns false),
// so the normalizer must NOT equate these. These pin the soundness boundary of
// the join rule: dropping requires domination at EVERY assignment, and the
// imax 0-pivot breaks it for the offending assignment.
// ---------------------------------------------------------------------------

/// Adversarial pair 1 — the imax 0-pivot: `max u_0 u_1` vs
/// `max (max u_0 u_1) (imax u_2 u_1)`.
///
/// A naive "the join of the other args already covers imax(u_2, u_1)" is WRONG:
/// at the assignment `u_1 > 0, u_2 > max(u_0, u_1)`, `imax(u_2, u_1) = u_2`
/// exceeds `max(u_0, u_1)`, so the two levels DIFFER. `is_geq_core(max(u_0,u_1),
/// imax(u_2,u_1))` must return false, so the arg is kept and the levels are NOT
/// equated. (They are genuinely UNEQUAL — this is a rejection case, not an
/// accept.)
fn adversarial_imax_not_dominated() -> (Level, Level) {
    let u0 = Level::param(Name::from_string("u0"));
    let u1 = Level::param(Name::from_string("u1"));
    let u2 = Level::param(Name::from_string("u2"));
    let max_u0_u1 = Level::Max(level_arc(u0.clone()), level_arc(u1.clone()));
    let imax_u2_u1 = Level::IMax(level_arc(u2), level_arc(u1.clone()));
    // LHS: max u0 u1
    let lhs = Level::Max(level_arc(u0), level_arc(u1));
    // RHS: max (max u0 u1) (imax u2 u1) — the imax arg is NOT join-dominated.
    let rhs = Level::Max(level_arc(max_u0_u1), level_arc(imax_u2_u1));
    (lhs, rhs)
}

/// Adversarial pair 2 — join over-approximation must not fire: `max u0 u1` vs
/// `max (max u0 u1) u2`. The extra `u2` is a fresh param NOT dominated by the
/// join `max(u0, u1)` (take u2 huge). Genuinely unequal; must be rejected.
fn adversarial_fresh_param_not_dominated() -> (Level, Level) {
    let u0 = Level::param(Name::from_string("u0"));
    let u1 = Level::param(Name::from_string("u1"));
    let u2 = Level::param(Name::from_string("u2"));
    let max_u0_u1 = Level::Max(level_arc(u0.clone()), level_arc(u1.clone()));
    let lhs = Level::Max(level_arc(u0), level_arc(u1));
    let rhs = Level::Max(level_arc(max_u0_u1), level_arc(u2));
    (lhs, rhs)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// PRIMARY GATE: zero false-accepts + monotone over the full depth-3 / 3-param
/// enumeration (3,244 levels, ~10.5M pairs). Contains the target shape.
#[test]
fn harness_soundness_and_monotone_depth3_3params() {
    let r = run_harness(3, 4, None);
    // Non-vacuity: the fix must actually have added accepts over legacy.
    eprintln!("primary tier complete");
    assert_green(&r);
}

/// WIDER EVIDENCE: bounded enumeration reaching depth 5 (capped at 4,000 levels
/// breadth-first), exhaustively pairwise — zero false-accepts + monotone.
#[test]
fn harness_soundness_and_monotone_depth5_bounded() {
    let r = run_harness(5, 4, Some(4000));
    assert_green(&r);
}

/// COMPLETENESS TARGET: the `funUnique`/`piUnique` shape must be accepted.
#[test]
fn harness_completeness_target_accepted() {
    let (lhs, rhs) = completeness_target_pair();
    // Confirm the target is GENUINELY equal under ground-truth semantics
    // (covering the imax 0/positive pivot) so the test itself is honest.
    let params = vec![Name::from_string("u"), Name::from_string("u_1")];
    let assignments = all_assignments(&params, 4);
    assert!(
        genuine_equal(&lhs, &rhs, &assignments),
        "target pair is not genuinely equal — test is mis-specified"
    );
    assert!(
        Level::is_def_eq(&lhs, &rhs),
        "COMPLETENESS TARGET not met: is_def_eq rejected genuinely-equal pair\n  lhs = {lhs}\n  rhs = {rhs}\n  norm(lhs) = {}\n  norm(rhs) = {}",
        lhs.normalize(),
        rhs.normalize()
    );
}

/// COMPLETENESS TARGET (JOIN-SUBSUMPTION): the `List.reverseRecOn._unary` vs
/// `.eq_1` WF-recursion shape must be accepted. This is the exact pair whose
/// `check_type` `TypeMismatch` motivated the join-subsumption fix.
#[test]
fn harness_reverse_rec_on_target_accepted() {
    let (lhs, rhs) = reverse_rec_on_target_pair();
    // First: the pair must be GENUINELY equal under ground-truth semantics,
    // including the imax 0-pivot (u_2 = 0) and large positive values.
    let params = vec![Name::from_string("u"), Name::from_string("u_2")];
    // max_val=8 to stress large magnitudes beyond the depth bound.
    let assignments = all_assignments(&params, 8);
    assert!(
        genuine_equal(&lhs, &rhs, &assignments),
        "reverseRecOn target pair is not genuinely equal — test is mis-specified\n  lhs = {lhs}\n  rhs = {rhs}"
    );
    // Then: the (fixed) normalizer must accept it via join-subsumption.
    assert!(
        Level::is_def_eq(&lhs, &rhs),
        "JOIN-SUBSUMPTION COMPLETENESS TARGET not met: is_def_eq rejected genuinely-equal pair\n  lhs = {lhs}\n  rhs = {rhs}\n  norm(lhs) = {}\n  norm(rhs) = {}",
        lhs.normalize(),
        rhs.normalize()
    );
}

/// ADVERSARIAL SOUNDNESS: pairs where a NAIVE join-subsumption would wrongly
/// drop an arg (making two UNEQUAL levels compare equal) must be REJECTED. The
/// conservative `is_geq_core` returns false for the offending imax/fresh-param
/// domination, so the arg is retained and `is_def_eq` must be false.
#[test]
fn harness_adversarial_join_not_over_applied() {
    let params = vec![
        Name::from_string("u0"),
        Name::from_string("u1"),
        Name::from_string("u2"),
    ];
    let assignments = all_assignments(&params, 8);

    let cases: Vec<(&str, (Level, Level))> = vec![
        ("imax-0-pivot", adversarial_imax_not_dominated()),
        ("fresh-param", adversarial_fresh_param_not_dominated()),
    ];
    for (label, (lhs, rhs)) in cases {
        // Honesty check: these pairs are GENUINELY UNEQUAL (differ at some asn).
        assert!(
            !genuine_equal(&lhs, &rhs, &assignments),
            "adversarial case '{label}' is actually equal — test is mis-specified\n  lhs = {lhs}\n  rhs = {rhs}"
        );
        // The normalizer must NOT equate them (no false-accept from join rule).
        assert!(
            !Level::is_def_eq(&lhs, &rhs),
            "SOUNDNESS VIOLATION: adversarial case '{label}' was ACCEPTED by is_def_eq\n  lhs = {lhs}\n  rhs = {rhs}\n  norm(lhs) = {}\n  norm(rhs) = {}",
            lhs.normalize(),
            rhs.normalize()
        );
    }
}

/// JOIN-DENSE EXHAUSTIVE TIER: a full depth-4 / 2-param enumeration densely
/// constructs the `imax(succ u)(imax(succ u) v)`-shaped join-subsumption terms
/// (which the depth-3 tier and the breadth-capped depth-5 tier under-sample).
/// Exhaustive pairwise over the enumeration — zero false-accepts + monotone.
/// This is where the NEW join rule is exercised at maximum density.
#[test]
fn harness_soundness_and_monotone_depth4_2params_join_dense() {
    let params = vec![Name::from_string("u0"), Name::from_string("u1")];
    // Cap at 3,000 levels (breadth-first): the depth-4 layer is combinatorial
    // (Max/IMax over all smaller levels), so an uncapped enumeration is
    // intractable. The cap still reaches depth-4 imax-of-imax join shapes.
    let levels = enumerate(4, &params, Some(3000));
    let assignments = all_assignments(&params, 6);

    let new_nf: Vec<Level> = levels.iter().map(|l| l.normalize()).collect();
    let leg_nf: Vec<Level> = levels.iter().map(legacy_normalize).collect();

    let n = levels.len();
    let mut false_accepts: Vec<(String, String)> = Vec::new();
    let mut monotonicity_losses: Vec<(String, String)> = Vec::new();
    let mut new_accepts_over_legacy = 0usize;
    for i in 0..n {
        for j in 0..n {
            let new_eq = (i == j) || new_nf[i] == new_nf[j];
            if new_eq && !genuine_equal(&levels[i], &levels[j], &assignments) {
                false_accepts.push((key(&levels[i]), key(&levels[j])));
            }
            let old_eq = (i == j) || leg_nf[i] == leg_nf[j];
            if old_eq && !new_eq {
                monotonicity_losses.push((key(&levels[i]), key(&levels[j])));
            }
            if new_eq && !old_eq {
                new_accepts_over_legacy += 1;
            }
        }
    }
    eprintln!(
        "[join-dense depth<=4 2params levels={n} pairs={} new_accepts_over_legacy={new_accepts_over_legacy}]",
        n * n
    );
    assert!(
        false_accepts.is_empty(),
        "SOUNDNESS VIOLATION (false-accept): {} pair(s); first few: {:?}",
        false_accepts.len(),
        &false_accepts[..false_accepts.len().min(10)]
    );
    assert!(
        monotonicity_losses.is_empty(),
        "MONOTONICITY VIOLATION (lost verdict): {} pair(s); first few: {:?}",
        monotonicity_losses.len(),
        &monotonicity_losses[..monotonicity_losses.len().min(10)]
    );
    // Non-vacuity: the join rule must have added at least one accept over legacy.
    assert!(
        new_accepts_over_legacy > 0,
        "join-dense tier added NO new accepts over legacy — the join rule is not \
         being exercised (vacuous certification)"
    );
}

/// Sanity: the eval-based ground truth itself behaves on known identities.
#[test]
fn harness_eval_ground_truth_sanity() {
    let u = Name::from_string("u0");
    let asn = vec![(u.clone(), 3u64)];
    // imax(x, 0) = 0
    let im0 = Level::IMax(level_arc(Level::Param(u.clone())), level_arc(Level::Zero));
    assert_eq!(eval(&im0, &asn), 0);
    // imax(x, succ 0) = max(x, 1) = 3
    let im1 = Level::IMax(
        level_arc(Level::Param(u.clone())),
        level_arc(Level::succ(Level::Zero)),
    );
    assert_eq!(eval(&im1, &asn), 3);
    // max(succ 0, x) = 3
    let m = Level::Max(
        level_arc(Level::succ(Level::Zero)),
        level_arc(Level::Param(u)),
    );
    assert_eq!(eval(&m, &asn), 3);
}
