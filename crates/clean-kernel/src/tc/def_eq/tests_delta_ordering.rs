// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for lazy delta reduction ordering (#3134).
//!
//! Verifies that the `Reducibility::compare` ordering and `lazy_delta_step_both`
//! correctly match Lean 4's `compare()` in `declaration.cpp:24-49` and
//! `lazy_delta_reduction_step` in `type_checker.cpp:884-941`.
//!
//! Key invariants tested:
//! - Reducible > Regular(n) > Irreducible > Opaque (ordering)
//! - Within Regular, higher height unfolds first
//! - Level-mismatch constants are NOT delta candidates (bug fix)
//! - Both sides unfold when reducibility is equal
//! - `is_def_eq_args_only` optimization for same-name Regular AND Reducible
//!   heads (the latter is a deliberate, documented divergence from Lean's
//!   Regular-only gate at type_checker.cpp:917 — see `lazy_delta_step_equal`
//!   in delta.rs and the gate-scope pins below)
//! - The args attempt is TRUE-early ONLY: failure falls through to the
//!   byte-identical unfold-both path (constant-function detector pin)

use super::*;
use crate::env::{ConstantInfo, Environment, Reducibility, TransparencyMode};
use crate::expr::BinderInfo;
use crate::level::Level;
use std::cmp::Ordering;

// ============================================================================
// Helpers
// ============================================================================

fn add_regular_def(env: &mut Environment, name: &str, ty: Expr, value: Expr, height: u32) {
    let mut info = ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), false);
    info.reducibility = Reducibility::Regular(height);
    env.extend_constants_unchecked(std::iter::once(info));
}

fn add_reducible_def(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    let mut info = ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), true);
    info.reducibility = Reducibility::Reducible;
    env.extend_constants_unchecked(std::iter::once(info));
}

fn add_irreducible_def(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    let mut info = ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), false);
    info.reducibility = Reducibility::Irreducible;
    env.extend_constants_unchecked(std::iter::once(info));
}

/// Add a universe-polymorphic definition with explicit level params.
fn add_poly_def(
    env: &mut Environment,
    name: &str,
    level_params: Vec<Name>,
    ty: Expr,
    value: Expr,
    reducibility: Reducibility,
) {
    let mut info = ConstantInfo::new(
        Name::from_string(name),
        level_params,
        ty,
        Some(value),
        matches!(reducibility, Reducibility::Reducible),
    );
    info.reducibility = reducibility;
    env.extend_constants_unchecked(std::iter::once(info));
}

// ============================================================================
// Reducibility::compare() unit tests
// ============================================================================

#[test]
fn test_compare_reducible_vs_regular() {
    let red = Reducibility::Reducible;
    let reg = Reducibility::Regular(5);
    assert_eq!(
        red.compare(&reg),
        Ordering::Less,
        "Reducible should unfold before Regular"
    );
    assert_eq!(
        reg.compare(&red),
        Ordering::Greater,
        "Regular should unfold after Reducible"
    );
}

#[test]
fn test_compare_reducible_vs_irreducible() {
    let red = Reducibility::Reducible;
    let irr = Reducibility::Irreducible;
    assert_eq!(
        red.compare(&irr),
        Ordering::Less,
        "Reducible should unfold before Irreducible"
    );
    assert_eq!(irr.compare(&red), Ordering::Greater);
}

#[test]
fn test_compare_reducible_vs_opaque() {
    let red = Reducibility::Reducible;
    let opq = Reducibility::Opaque;
    assert_eq!(
        red.compare(&opq),
        Ordering::Less,
        "Reducible should unfold before Opaque"
    );
    assert_eq!(opq.compare(&red), Ordering::Greater);
}

#[test]
fn test_compare_regular_vs_irreducible() {
    let reg = Reducibility::Regular(3);
    let irr = Reducibility::Irreducible;
    assert_eq!(
        reg.compare(&irr),
        Ordering::Less,
        "Regular should unfold before Irreducible"
    );
    assert_eq!(irr.compare(&reg), Ordering::Greater);
}

#[test]
fn test_compare_regular_vs_opaque() {
    let reg = Reducibility::Regular(0);
    let opq = Reducibility::Opaque;
    assert_eq!(
        reg.compare(&opq),
        Ordering::Less,
        "Regular should unfold before Opaque"
    );
    assert_eq!(opq.compare(&reg), Ordering::Greater);
}

#[test]
fn test_compare_irreducible_vs_opaque() {
    let irr = Reducibility::Irreducible;
    let opq = Reducibility::Opaque;
    assert_eq!(
        irr.compare(&opq),
        Ordering::Less,
        "Irreducible should unfold before Opaque"
    );
    assert_eq!(opq.compare(&irr), Ordering::Greater);
}

#[test]
fn test_compare_same_kind_equal() {
    assert_eq!(
        Reducibility::Reducible.compare(&Reducibility::Reducible),
        Ordering::Equal
    );
    assert_eq!(
        Reducibility::Irreducible.compare(&Reducibility::Irreducible),
        Ordering::Equal
    );
    assert_eq!(
        Reducibility::Opaque.compare(&Reducibility::Opaque),
        Ordering::Equal
    );
}

#[test]
fn test_compare_regular_height_ordering() {
    let high = Reducibility::Regular(10);
    let low = Reducibility::Regular(2);
    let same = Reducibility::Regular(10);

    // Higher height unfolds first → Less
    assert_eq!(
        high.compare(&low),
        Ordering::Less,
        "Higher height should unfold first"
    );
    assert_eq!(low.compare(&high), Ordering::Greater);
    assert_eq!(
        high.compare(&same),
        Ordering::Equal,
        "Same height should be equal"
    );
}

#[test]
fn test_compare_regular_zero_vs_nonzero() {
    let zero = Reducibility::Regular(0);
    let five = Reducibility::Regular(5);
    assert_eq!(
        five.compare(&zero),
        Ordering::Less,
        "Height 5 unfolds before height 0"
    );
    assert_eq!(zero.compare(&five), Ordering::Greater);
    assert_eq!(zero.compare(&zero), Ordering::Equal);
}

// ============================================================================
// Lazy delta: Reducible vs Regular
// ============================================================================

/// Both Reducible and Regular(0) define to Prop. Reducible unfolds first
/// but both converge to Prop, so they are def-eq.
#[test]
fn test_delta_ordering_reducible_vs_regular_converge() {
    let mut env = Environment::new();
    add_reducible_def(&mut env, "red_a", Expr::prop(), Expr::prop());
    add_regular_def(&mut env, "reg_b", Expr::prop(), Expr::prop(), 0);

    let tc = TypeChecker::new(&env);
    let a = Expr::const_(Name::from_string("red_a"), vec![]);
    let b = Expr::const_(Name::from_string("reg_b"), vec![]);

    assert!(
        tc.is_def_eq(&a, &b),
        "Reducible and Regular both =Prop should be def-eq"
    );
    assert!(tc.is_def_eq(&b, &a), "Symmetric");
}

/// Reducible defines to Type, Regular defines to Prop. Not def-eq.
#[test]
fn test_delta_ordering_reducible_vs_regular_diverge() {
    let mut env = Environment::new();
    add_reducible_def(&mut env, "red_type", Expr::type_(), Expr::type_());
    add_regular_def(&mut env, "reg_prop", Expr::prop(), Expr::prop(), 0);

    let tc = TypeChecker::new(&env);
    let a = Expr::const_(Name::from_string("red_type"), vec![]);
    let b = Expr::const_(Name::from_string("reg_prop"), vec![]);

    assert!(
        !tc.is_def_eq(&a, &b),
        "Reducible(Type) vs Regular(Prop) should not be def-eq"
    );
}

// ============================================================================
// Lazy delta: Reducible vs Reducible
// ============================================================================

/// Both Reducible. Equal case: both unfold simultaneously.
#[test]
fn test_delta_ordering_reducible_vs_reducible_both_unfold() {
    let mut env = Environment::new();
    add_reducible_def(&mut env, "ra", Expr::prop(), Expr::prop());
    add_reducible_def(&mut env, "rb", Expr::prop(), Expr::prop());

    let tc = TypeChecker::new(&env);
    let a = Expr::const_(Name::from_string("ra"), vec![]);
    let b = Expr::const_(Name::from_string("rb"), vec![]);

    assert!(
        tc.is_def_eq(&a, &b),
        "Two Reducible defs to Prop should be def-eq"
    );
}

// ============================================================================
// Lazy delta: Regular height ordering
// ============================================================================

/// Higher Regular height unfolds first. Both converge to Prop.
#[test]
fn test_delta_ordering_regular_higher_height_first() {
    let mut env = Environment::new();
    add_regular_def(&mut env, "h10", Expr::prop(), Expr::prop(), 10);
    add_regular_def(&mut env, "h3", Expr::prop(), Expr::prop(), 3);

    let tc = TypeChecker::new(&env);
    let a = Expr::const_(Name::from_string("h10"), vec![]);
    let b = Expr::const_(Name::from_string("h3"), vec![]);

    assert!(
        tc.is_def_eq(&a, &b),
        "Regular(10) vs Regular(3) both =Prop should be def-eq"
    );
}

/// Height chain: h5 -> h3 -> h1 -> Prop. The taller side unfolds first at
/// each step, converging efficiently.
#[test]
fn test_delta_ordering_regular_height_chain() {
    let mut env = Environment::new();
    add_regular_def(&mut env, "hd1", Expr::prop(), Expr::prop(), 1);
    add_regular_def(
        &mut env,
        "hd3",
        Expr::prop(),
        Expr::const_(Name::from_string("hd1"), vec![]),
        3,
    );
    add_regular_def(
        &mut env,
        "hd5",
        Expr::prop(),
        Expr::const_(Name::from_string("hd3"), vec![]),
        5,
    );

    let tc = TypeChecker::new(&env);
    let top = Expr::const_(Name::from_string("hd5"), vec![]);
    let bot = Expr::const_(Name::from_string("hd1"), vec![]);

    assert!(
        tc.is_def_eq(&top, &bot),
        "Chain h5->h3->h1->Prop vs h1->Prop should be def-eq"
    );
    assert!(tc.is_def_eq(&bot, &top), "Symmetric");
}

// ============================================================================
// Lazy delta: Irreducible definitions
// ============================================================================

/// The kernel type checker has no transparency modes — it unfolds ANY definition
/// including Irreducible ones. Reducibility hints only control unfolding ORDER,
/// not whether something unfolds. Reference: Lean 4 type_checker.cpp:487 is_delta.
#[test]
fn test_delta_ordering_irreducible_unfolds_in_kernel() {
    let mut env = Environment::new();
    add_irreducible_def(&mut env, "irr_a", Expr::prop(), Expr::prop());
    add_irreducible_def(&mut env, "irr_b", Expr::prop(), Expr::prop());

    let tc = TypeChecker::new(&env);
    let a = Expr::const_(Name::from_string("irr_a"), vec![]);
    let b = Expr::const_(Name::from_string("irr_b"), vec![]);

    assert!(tc.is_def_eq(&a, &b), "Kernel unfolds Irreducible defs");
}

/// Reducible vs Irreducible: Reducible unfolds first. Both converge.
#[test]
fn test_delta_ordering_reducible_vs_irreducible() {
    let mut env = Environment::new();
    add_reducible_def(&mut env, "red_p", Expr::prop(), Expr::prop());
    add_irreducible_def(&mut env, "irr_p", Expr::prop(), Expr::prop());

    let tc = TypeChecker::new(&env);
    let a = Expr::const_(Name::from_string("red_p"), vec![]);
    let b = Expr::const_(Name::from_string("irr_p"), vec![]);

    assert!(tc.is_def_eq(&a, &b), "Reducible vs Irreducible, both =Prop");
}

/// Regular vs Irreducible: Regular unfolds first. Both converge.
#[test]
fn test_delta_ordering_regular_vs_irreducible() {
    let mut env = Environment::new();
    add_regular_def(&mut env, "reg_p", Expr::prop(), Expr::prop(), 5);
    add_irreducible_def(&mut env, "irr_p2", Expr::prop(), Expr::prop());

    let tc = TypeChecker::new(&env);
    let a = Expr::const_(Name::from_string("reg_p"), vec![]);
    let b = Expr::const_(Name::from_string("irr_p2"), vec![]);

    assert!(
        tc.is_def_eq(&a, &b),
        "Regular(5) vs Irreducible, both =Prop"
    );
}

// ============================================================================
// Level-mismatch bug fix (Part of #3134)
// ============================================================================

/// A universe-polymorphic definition referenced with wrong level count should
/// NOT be considered a delta candidate. Before the fix, get_delta_const would
/// return Some even for mismatched levels, causing try_unfold_const_in_place
/// to fail and potentially unfold the wrong side.
#[test]
fn test_delta_ordering_level_mismatch_not_delta_candidate() {
    let mut env = Environment::new();

    // Define: poly_id.{u} : Sort u := Sort u  (one level param)
    let u = Name::from_string("u");
    add_poly_def(
        &mut env,
        "poly_id",
        vec![u.clone()],
        Expr::sort(Level::succ(Level::param(u.clone()))),
        Expr::sort(Level::param(u)),
        Reducibility::Reducible,
    );

    let tc = TypeChecker::new(&env);

    // Reference with ZERO levels (mismatch: expected 1)
    let zero_levels = Expr::const_(Name::from_string("poly_id"), vec![]);
    // Reference with TWO levels (mismatch: expected 1)
    let two_levels = Expr::const_(
        Name::from_string("poly_id"),
        vec![Level::zero(), Level::succ(Level::zero())],
    );
    // Reference with correct ONE level
    let one_level = Expr::const_(Name::from_string("poly_id"), vec![Level::zero()]);

    // Mismatched levels should not crash. get_delta_const returns None for them,
    // so they are treated as stuck constants and NOT unfolded.
    // poly_id (no levels) vs poly_id.{0}: not def-eq because the level lists differ
    assert!(
        !tc.is_def_eq(&zero_levels, &one_level),
        "Level mismatch (0 vs 1 levels) should not be def-eq"
    );
    assert!(
        !tc.is_def_eq(&two_levels, &one_level),
        "Level mismatch (2 vs 1 levels) should not be def-eq"
    );

    // Two mismatched-level references with same levels: still def-eq (syntactically)
    let zero_levels_2 = Expr::const_(Name::from_string("poly_id"), vec![]);
    assert!(
        tc.is_def_eq(&zero_levels, &zero_levels_2),
        "Same mismatched-level exprs should be syntactically def-eq"
    );
}

/// Verify correct levels DO unfold via delta reduction.
#[test]
fn test_delta_ordering_correct_levels_unfold() {
    let mut env = Environment::new();

    let u = Name::from_string("u");
    // my_sort.{u} := Sort u
    add_poly_def(
        &mut env,
        "my_sort",
        vec![u.clone()],
        Expr::sort(Level::succ(Level::param(u.clone()))),
        Expr::sort(Level::param(u)),
        Reducibility::Reducible,
    );

    let tc = TypeChecker::new(&env);

    // my_sort.{0} should unfold to Sort 0 = Prop
    let my_sort_0 = Expr::const_(Name::from_string("my_sort"), vec![Level::zero()]);
    assert!(
        tc.is_def_eq(&my_sort_0, &Expr::prop()),
        "my_sort.{{0}} should unfold to Prop"
    );

    // my_sort.{1} should unfold to Sort 1 = Type
    let my_sort_1 = Expr::const_(
        Name::from_string("my_sort"),
        vec![Level::succ(Level::zero())],
    );
    assert!(
        tc.is_def_eq(&my_sort_1, &Expr::type_()),
        "my_sort.{{1}} should unfold to Type"
    );
}

// ============================================================================
// Same-name same-height args optimization
// ============================================================================

/// When both sides have same Regular head and matching args, the args
/// optimization fires and returns DefEqual without unfolding.
#[test]
fn test_delta_ordering_same_head_matching_args() {
    let mut env = Environment::new();
    let f_body = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    add_regular_def(
        &mut env,
        "f_id",
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        f_body,
        5,
    );

    let tc = TypeChecker::new(&env);
    let lhs = Expr::app(
        Expr::const_(Name::from_string("f_id"), vec![]),
        Expr::prop(),
    );
    let rhs = Expr::app(
        Expr::const_(Name::from_string("f_id"), vec![]),
        Expr::prop(),
    );

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "Same head, same args should be def-eq"
    );
    // Args optimization should not generate a cache failure entry
    assert_eq!(tc.args_failure_cache_entries(), 0);
}

/// When same Regular head but args differ, the args optimization fails,
/// the failure is cached, and both sides unfold.
#[test]
fn test_delta_ordering_same_head_different_args_cached() {
    let mut env = Environment::new();
    let f_body = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    add_regular_def(
        &mut env,
        "f_id2",
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        f_body,
        5,
    );

    let tc = TypeChecker::new(&env);
    let lhs = Expr::app(
        Expr::const_(Name::from_string("f_id2"), vec![]),
        Expr::prop(),
    );
    let rhs = Expr::app(
        Expr::const_(Name::from_string("f_id2"), vec![]),
        Expr::type_(),
    );

    // f_id2(Prop) vs f_id2(Type) — args differ, but after unfolding:
    // f_id2(Prop) -> Prop, f_id2(Type) -> Type. Not def-eq.
    assert!(
        !tc.is_def_eq(&lhs, &rhs),
        "Same head, different args should not be def-eq"
    );
    assert!(
        tc.args_failure_cache_entries() > 0,
        "Args failure should be cached"
    );
}

/// The args-first attempt fires for Regular AND Reducible same-name heads.
///
/// DELIBERATE DIVERGENCE from Lean 4: type_checker.cpp:917 gates the args
/// attempt on `d_t->get_hints().is_regular()`, skipping abbrev-hinted heads
/// because Lean's hints are source-faithful (a Reducible hint really means a
/// cheap `abbrev` unfold). Clean's hints over-assign `Reducible`: the prelude
/// seeds mark class definitions like `Nat.lt` `is_reducible: true`
/// (env/order_le_lt.rs:429) where Lean's olean hint is Regular, and the olean
/// importer force-promotes projection-bodied definitions (`LT.lt`,
/// `HAdd.hAdd`, …) to Reducible (clean-olean import/convert.rs:170-176) —
/// so the Regular-only gate starved exactly the class-method heads whose
/// unfolding launches genuine `Nat.rec` grinds (Step-0 witness:
/// `[EXTEQ d=2] Nat.lt t_red=Reducible s_red=Reducible gate=false
/// verdict=SKIPPED(gate: non-Regular head)`). See the gate comment in
/// tc/def_eq/delta.rs `lazy_delta_step_equal`; the deeper fix is a seed/
/// import hint-fidelity sweep, after which the gate can narrow back.
///
/// Success leaves NO args_failure_cache entry (the cache records failures
/// only) — same observable as before the widening for this same-args pair.
#[test]
fn test_delta_ordering_reducible_same_name_args_fast_path() {
    let mut env = Environment::new();
    let f_body = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    add_reducible_def(
        &mut env,
        "red_f",
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        f_body,
    );

    let tc = TypeChecker::new(&env);
    let lhs = Expr::app(
        Expr::const_(Name::from_string("red_f"), vec![]),
        Expr::prop(),
    );
    let rhs = Expr::app(
        Expr::const_(Name::from_string("red_f"), vec![]),
        Expr::prop(),
    );

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "Reducible same-name same-args should be def-eq"
    );
    // The args attempt SUCCEEDS (TRUE-early), so no failure entry is cached.
    assert_eq!(
        tc.args_failure_cache_entries(),
        0,
        "successful args fast path must not populate the failure cache"
    );
}

// ============================================================================
// TRUE-early-only detector + gate-scope pins (lazy-delta ordering parity,
// designs/2026-07-15-lazy-delta-ordering-parity.md STEP 1)
// ============================================================================

/// MUST-ACCEPT constant-function fallback pin (the TRUE-early-only detector).
///
/// `K : Nat → Nat := fun _ => c` is a constant function, so `K 1` and `K 2`
/// are definitionally equal (both δβ-reduce to `c`) even though their
/// arguments are NOT (`1 ≠ 2`). The same-head args-first fast path in
/// `lazy_delta_step_equal` therefore must be TRUE-early ONLY:
///
/// - args attempt succeeds → `DefEqual` (sound: congruence closure of the
///   unchanged per-argument acceptance);
/// - args attempt fails → record in `args_failure_cache` and FALL THROUGH
///   to the byte-identical unfold-both path, which accepts this pair.
///
/// An (illegal) FALSE-early shortcut — treating an args-attempt failure as
/// a verdict — would wrongly reject `K 1 =?= K 2`. No other suite pins this
/// distinction; this is the detector that keeps any gate change on the fast
/// path honest.
///
/// Reference: Lean 4 type_checker.cpp:917-931 — the args optimization only
/// ever produces `l_true`; failure falls through to unfolding.
#[test]
fn test_delta_ordering_constant_function_fallback_must_accept() {
    let mut env = Environment::new();

    // Minimal Nat inductive so `Nat`-typed terms are well-formed.
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    env.add_inductive(crate::inductive::InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![crate::inductive::InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                crate::inductive::Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                crate::inductive::Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    })
    .expect("add Nat inductive");

    // c : Nat — an axiom; cannot reduce further.
    env.add_decl(crate::env::Declaration::Axiom {
        name: Name::from_string("c"),
        level_params: vec![],
        type_: nat_ref.clone(),
    })
    .expect("add c axiom");

    // K : Nat → Nat := fun _ => c, Regular hint → the args attempt runs.
    add_regular_def(
        &mut env,
        "K",
        Expr::arrow(nat_ref.clone(), nat_ref.clone()),
        Expr::lam(
            BinderInfo::Default,
            nat_ref,
            Expr::const_(Name::from_string("c"), vec![]),
        ),
        1,
    );

    let tc = TypeChecker::new(&env);
    let k = Expr::const_(Name::from_string("K"), vec![]);
    let k1 = Expr::app(k.clone(), Expr::nat_lit(1));
    let k2 = Expr::app(k, Expr::nat_lit(2));

    assert!(
        tc.is_def_eq(&k1, &k2),
        "K 1 =?= K 2 must ACCEPT via the unfold-both fallback (both reduce to c)"
    );
    assert!(
        tc.args_failure_cache_entries() > 0,
        "the args-first attempt must have run on `K 1 =?= K 2`, failed (1 ≠ 2), \
         and been recorded in args_failure_cache before the unfold-both fallback"
    );
}

/// Non-vacuity pin for the same-name REDUCIBLE-head args attempt (gate scope).
///
/// Observable: a same-name Reducible-head pair with non-def-eq args populates
/// `args_failure_cache` IFF the args attempt actually ran (success never
/// caches; the gate skipping never caches).
///
/// WIDENED gate (deliberate divergence from Lean type_checker.cpp:917 — see
/// `lazy_delta_step_equal` in tc/def_eq/delta.rs): same-name Reducible heads
/// now take the args attempt. For this pair the attempt runs, fails
/// (Prop ≠ Type), is cached, and falls through to unfold-both — the VERDICT
/// is identical to the pre-widening world; only the cache entry proves the
/// attempt ran (non-vacuity of the widening).
#[test]
fn test_delta_ordering_reducible_same_name_differing_args_attempt() {
    let mut env = Environment::new();
    let body = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    add_reducible_def(
        &mut env,
        "red_gate",
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        body,
    );

    let tc = TypeChecker::new(&env);
    let lhs = Expr::app(
        Expr::const_(Name::from_string("red_gate"), vec![]),
        Expr::prop(),
    );
    let rhs = Expr::app(
        Expr::const_(Name::from_string("red_gate"), vec![]),
        Expr::type_(),
    );

    assert!(
        !tc.is_def_eq(&lhs, &rhs),
        "red_gate Prop =?= red_gate Type must reject (identity body diverges)"
    );
    assert!(
        tc.args_failure_cache_entries() > 0,
        "widened gate: the args attempt must RUN on same-name Reducible heads \
         (fail, cache, fall through to unfold-both) — non-vacuity of the widening"
    );
}

/// Same-name Reducible heads with def-eq (but not syntactically identical)
/// args must ACCEPT and leave no failure entry — before the gate widening
/// via unfold-both, after it via the TRUE-early args fast path. Stable in
/// both worlds; pins that widening can never flip an accept.
#[test]
fn test_delta_ordering_reducible_same_name_defeq_args_accepts() {
    let mut env = Environment::new();
    let body = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    add_reducible_def(
        &mut env,
        "red_acc",
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        body,
    );

    let tc = TypeChecker::new(&env);
    // (fun x : Type => x) Prop — def-eq to Prop but not syntactically equal,
    // so the argument comparison is a genuine `is_def_eq` call.
    let beta_prop = Expr::app(
        Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::from_kind(ExprKind::BVar(0)),
        ),
        Expr::prop(),
    );
    let lhs = Expr::app(
        Expr::const_(Name::from_string("red_acc"), vec![]),
        beta_prop,
    );
    let rhs = Expr::app(
        Expr::const_(Name::from_string("red_acc"), vec![]),
        Expr::prop(),
    );

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "red_acc ((fun x => x) Prop) =?= red_acc Prop must accept"
    );
    assert!(tc.is_def_eq(&rhs, &lhs), "Symmetric");
    assert_eq!(
        tc.args_failure_cache_entries(),
        0,
        "an accepted same-name pair must never leave an args-failure entry"
    );
}

// ============================================================================
// Edge cases
// ============================================================================

/// When one side is a bare axiom (no value, not delta), and the other is
/// a definition that unfolds to that axiom, they should be def-eq.
#[test]
fn test_delta_ordering_def_unfolds_to_axiom() {
    let mut env = Environment::new();
    env.add_decl(crate::env::Declaration::Axiom {
        name: Name::from_string("ax"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    add_reducible_def(
        &mut env,
        "def_ax",
        Expr::prop(),
        Expr::const_(Name::from_string("ax"), vec![]),
    );

    let tc = TypeChecker::new(&env);
    let ax = Expr::const_(Name::from_string("ax"), vec![]);
    let def = Expr::const_(Name::from_string("def_ax"), vec![]);

    assert!(tc.is_def_eq(&def, &ax), "Definition should unfold to axiom");
    assert!(tc.is_def_eq(&ax, &def), "Symmetric");
}

/// Equal-height Regular defs with different names: both unfold simultaneously.
#[test]
fn test_delta_ordering_equal_height_both_unfold() {
    let mut env = Environment::new();
    add_regular_def(&mut env, "eq_a", Expr::prop(), Expr::prop(), 7);
    add_regular_def(&mut env, "eq_b", Expr::prop(), Expr::prop(), 7);

    let tc = TypeChecker::new(&env);
    let a = Expr::const_(Name::from_string("eq_a"), vec![]);
    let b = Expr::const_(Name::from_string("eq_b"), vec![]);

    assert!(
        tc.is_def_eq(&a, &b),
        "Equal-height defs both unfold to Prop"
    );
}
