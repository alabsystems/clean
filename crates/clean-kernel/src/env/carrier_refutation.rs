// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Carrier-generic refutation engine for the Soundness Certificate (claim C4).
//!
//! This module GENERALIZES the per-carrier refutation engines in
//! `tests_false_axiom_prevention.rs` ({Rat, Interval, Fin}) into a single
//! reusable engine that the certificate runs over EVERY admitted axiom in the
//! environment. The thesis (design `2026-06-08-soundness-certificate.md` §4.4)
//! is that C4 must not be a hand-curated per-carrier list: a *future* junk
//! carrier + false axiom must be caught without anyone remembering to add a
//! check (exactly how the completeness sweep found `Fin.sum_single`).
//!
//! # What "refutable" means
//!
//! An admitted `Declaration::Axiom` is *refutable* iff there is a closed
//! assignment of junk/well-formed witnesses to its leading value binders under
//! which every hypothesis binder reduces to a PROVABLE closed proposition while
//! the conclusion reduces to a manifestly FALSE closed proposition. A refutable
//! admitted axiom is exploitable to derive `False`, so the certificate's C4
//! asserts the refutable-admitted set is EMPTY.
//!
//! # Carrier census
//!
//! The engine classifies every concrete inductive carrier as either
//! *junk-admitting* (free over an implicit invariant — e.g. `Fin`'s
//! `isLt : Prop` slot, or the free `Rat.mk : Int → Nat` carrier) or
//! faithful/opaque. The witness battery for each value binder is keyed off the
//! binder's domain type, so a binder over a junk-admitting carrier is
//! instantiated with closed junk representatives (the source of unsoundness)
//! interleaved with well-formed ones.
//!
//! # Decision procedure
//!
//! Conclusions are decided purely by kernel `whnf` / `is_def_eq` (no reliance
//! on a particular numeral encoding):
//! - `Int.le` / `Rat.le` delta-reduce to `Int.NonNeg t`; provable iff `t` is a
//!   nonneg numeral (`Int.ofNat k`), false iff negative (`Int.negSucc k`).
//! - `@Eq Rat a b` is decided through the ORDER BRIDGE (the WS-A quotient `Rat`
//!   has no constructor `noConfusion`): false iff one of `Rat.le a b` /
//!   `Rat.le b a` reduces to a false `Int.le`, provable iff both directions
//!   reduce to true.
//! - `NNVerify.IntervalBounds.contains B x` reduces to a per-index conjunction
//!   of `Rat.le` comparisons.
//! - `Nat.lt` / `Nat.le` over closed literals are decided by decoding.
//!
//! Axioms whose conclusion is an *uninterpreted* applied predicate (no
//! reduction rule) or is stuck on an *opaque* carrier are NOT engine-decidable;
//! the engine reports them non-refutable (it never fabricates a refutation).
//! This matches the documented sound-but-admitted residue
//! (`fourier_coefficient_transform`, `cert_*_valid`, `sub_interval_hull`).

use super::types::ConstantKind;
use super::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

// ────────────────────────────── witnesses ──────────────────────────────

/// `Nat.succ^n Nat.zero`.
fn nat(n: u64) -> Expr {
    let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    for _ in 0..n {
        e = Expr::app(succ.clone(), e);
    }
    e
}

/// `Int.ofNat (Nat.succ^n Nat.zero)`.
fn of_nat(n: u64) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), nat(n))
}

/// `Int.negSucc (Nat.succ^n Nat.zero)` — the integer `-(n + 1)`.
fn neg_succ(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        nat(n),
    )
}

/// `Rat.mk num denom`.
fn rat_mk(num: Expr, denom: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [num, denom],
    )
}

/// The type `Rat`.
fn rat_ty() -> Expr {
    Expr::const_(Name::from_string("Rat"), vec![])
}

/// The type `Nat`.
fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// Closed `Rat` witness battery: junk `denom = 0` representatives (the source of
/// unsoundness) interleaved with well-formed (`denom > 0`) ones.
fn rat_witnesses() -> Vec<Expr> {
    vec![
        // junk: denom = 0
        rat_mk(of_nat(0), nat(0)),
        rat_mk(of_nat(1), nat(0)),
        rat_mk(of_nat(5), nat(0)),
        rat_mk(neg_succ(0), nat(0)), // -1 / 0
        // well-formed: denom > 0
        rat_mk(of_nat(0), nat(1)),
        rat_mk(of_nat(1), nat(1)),
        rat_mk(of_nat(0), nat(2)),
        rat_mk(of_nat(2), nat(2)),
        rat_mk(neg_succ(0), nat(1)), // -1 / 1
        rat_mk(of_nat(3), nat(2)),
    ]
}

/// A `Fin n` element `@Fin.mk n (val) True` — the `isLt` slot is a `Prop`
/// VALUE, not a proof of `val < n`. This is Clean's junk-admitting `Fin`
/// constructor; `Fin n` is inhabited even for `n = 0`.
fn fin_mk(n: u64, val: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Fin.mk"), vec![]),
        [
            nat(n),
            nat(val),
            Expr::const_(Name::from_string("True"), vec![]),
        ],
    )
}

/// For a `Fin n` binder at a known `n`, the witness battery: every in-range
/// index `0..n` PLUS junk indices `n`, `n+3` (`val >= n`). The junk indices are
/// the ones the unfixed axioms (e.g. pre-fix `Fin.sum_single`) break on.
fn fin_witnesses_for(n: u64) -> Vec<Expr> {
    let mut v = Vec::new();
    for val in 0..n {
        v.push(fin_mk(n, val));
    }
    v.push(fin_mk(n, n));
    v.push(fin_mk(n, n + 3));
    v
}

// ───────────────────────── prop truth decision ─────────────────────────

/// Is `e` the constant `False`?
fn is_false_const(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "False")
}

/// Is `e` an application whose head (after spine-walk) is `Rat.mk`?
fn is_rat_mk(e: &Expr) -> bool {
    let mut cur = e;
    while let ExprKind::App(f, _) = cur.kind() {
        cur = f;
    }
    matches!(cur.kind(), ExprKind::Const(n, _) if n.to_string() == "Rat.mk")
}

/// If `e` is `c a1 a2 ...` with `c` a constant, return `(const-name, [a1, ..])`.
fn const_app(e: &Expr) -> Option<(String, Vec<Expr>)> {
    let mut args = Vec::new();
    let mut cur = e;
    while let ExprKind::App(f, a) = cur.kind() {
        args.push((**a).clone());
        cur = f;
    }
    if let ExprKind::Const(n, _) = cur.kind() {
        args.reverse();
        Some((n.to_string(), args))
    } else {
        None
    }
}

/// Decode a closed `Nat` to its value by matching `Nat.succ^k Nat.zero` for
/// small `k`. Returns `None` for a non-literal / out-of-range nat.
fn decode_nat(tc: &TypeChecker, e: &Expr) -> Option<u64> {
    (0..=16u64).find(|&k| tc.is_def_eq(e, &nat(k)))
}

/// Three-valued truth of a CLOSED `@Eq Rat a b` proposition via the order
/// bridge: FALSE iff `Rat.le a b` or `Rat.le b a` reduces to a FALSE closed
/// `Int.le`; TRUE iff BOTH directions reduce to TRUE (antisymmetry on the
/// quotient ⇒ genuine equality); `None` otherwise. Works on the WS-A quotient
/// `Rat` where constructor `noConfusion` does not apply.
fn rat_eq_truth_via_order(tc: &TypeChecker, a: &Expr, b: &Expr) -> Option<bool> {
    let le = |lhs: &Expr, rhs: &Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le"), vec![]),
            [lhs.clone(), rhs.clone()],
        )
    };
    let ab = base_prop_truth(tc, &le(a, b));
    let ba = base_prop_truth(tc, &le(b, a));
    match (ab, ba) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    }
}

/// Three-valued truth of a CLOSED proposition decided purely by kernel
/// reduction for the *base* shapes:
/// - `Rat.le _ _` / `Int.le _ _` → `Int.NonNeg t`; nonneg numeral ⇒ provable,
///   `Int.negSucc` ⇒ false.
/// - `@Eq Rat lhs rhs` where both sides reduce to closed `Rat.mk` constructors
///   → `is_def_eq` (legacy free-carrier case; on the quotient this is `None`).
/// - `Ne` / `¬(@Eq Rat ..)` → negate the inner decision.
///
/// `None` = not a base shape this layer decides (a contains/order-bridge prop is
/// handled by [`prop_truth`]).
fn base_prop_truth(tc: &TypeChecker, p: &Expr) -> Option<bool> {
    // `Ne` / negation: `Pi (_ : @Eq Rat a b) False` (non-dependent).
    if let ExprKind::Pi(_, dom, body) = p.kind() {
        if is_false_const(body) {
            return base_prop_truth(tc, dom).map(|t| !t);
        }
    }

    // `@Eq Rat lhs rhs`: peel the application spine.
    if let Some((head, args)) = const_app(p) {
        if head == "Eq" && args.len() == 3 {
            let lhs = tc.whnf(&args[1]);
            let rhs = tc.whnf(&args[2]);
            if is_rat_mk(&lhs) && is_rat_mk(&rhs) {
                return Some(tc.is_def_eq(&lhs, &rhs));
            }
            return None;
        }
    }

    // `Rat.le` / `Int.le` → `Int.NonNeg t`; decide the sign of `t`.
    let w = tc.whnf(p);
    if let ExprKind::App(f, arg) = w.kind() {
        if let ExprKind::Const(n, _) = f.kind() {
            if n.to_string() == "Int.NonNeg" {
                for k in 0..32u64 {
                    if tc.is_def_eq(arg, &of_nat(k)) {
                        return Some(true);
                    }
                    if tc.is_def_eq(arg, &neg_succ(k)) {
                        return Some(false);
                    }
                }
            }
        }
    }
    None
}

/// A `Fin 1` element used to instantiate the single `Fin d` index of a
/// `contains` predicate at `d = 1`.
fn fin1_zero() -> Expr {
    fin_mk(1, 0)
}

/// Three-valued truth of a closed `NNVerify.IntervalBounds.contains B x`
/// proposition for `d = 1`: reduce to `∀ i, And (Rat.le (B.lo i)(x i))
/// (Rat.le (x i)(B.hi i))`, instantiate at the single index, AND the decisions.
fn contains_truth(tc: &TypeChecker, p: &Expr) -> Option<bool> {
    let w = tc.whnf(p);
    let body = match w.kind() {
        ExprKind::Pi(_, _, body) => (**body).clone(),
        _ => return None,
    };
    let inst = tc.whnf(&body.instantiate(&fin1_zero()));
    let (head, args) = const_app(&inst)?;
    if head != "And" || args.len() != 2 {
        return None;
    }
    match (prop_truth(tc, &args[0]), prop_truth(tc, &args[1])) {
        (Some(true), Some(true)) => Some(true),
        (Some(false), _) | (_, Some(false)) => Some(false),
        _ => None,
    }
}

/// The canonical `NNVec 0` witness `fun (_ : Fin 0) => Rat.zero`. `NNVec 0` is
/// inhabited (a function out of the empty `Fin 0`), and any two `NNVec 0` are
/// def-eq, so this is THE point-zonotope error-coordinate witness.
fn nnvec0_witness() -> Expr {
    let fin0 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat(0));
    Expr::lam(
        BinderInfo::Default,
        fin0,
        Expr::const_(Name::from_string("Rat.zero"), vec![]),
    )
}

/// Three-valued truth of a closed `NNVerify.Zonotope.contains n k z x` for a
/// POINT zonotope (`k = 0`) in `n = 1`.
///
/// `Zonotope.contains` is a reducible Definition unfolding to
/// `∃ ε : NNVec k, (∀ i, -1 ≤ ε i ≤ 1) ∧ x = z.center + z.generators · ε`. At
/// `k = 0` the generator matrix has zero columns, so `z.generators · ε` is the
/// zero vector and the existential collapses to `x = z.center` — a point
/// zonotope contains EXACTLY its center. We therefore decide point-containment
/// COMPLETELY (both polarities are sound at `k = 0`, since the unique vacuous
/// `ε` makes the existential equivalent to the single equality):
///
/// - whnf `contains 1 0 z x` to `Exists (NNVec 0) P`;
/// - instantiate `P` at the canonical `NNVec 0` witness;
/// - whnf to `And bounds eq`; decode `eq : @Eq (NNVec 1) x rhs` at the single
///   index `⟨0⟩` via the quotient-safe `@Eq Rat` order bridge.
///
/// Returns `None` for `k ≠ 0` / `n ≠ 1` (the general existential is NOT decided
/// — the engine never fabricates a refutation over a non-point zonotope) or any
/// unexpected shape.
fn zono_point_contains_truth(tc: &TypeChecker, args: &[Expr]) -> Option<bool> {
    if args.len() != 4 {
        return None;
    }
    // Restrict to the decidable point-zonotope slice: n = 1, k = 0.
    if !tc.is_def_eq(&args[0], &nat(1)) || !tc.is_def_eq(&args[1], &nat(0)) {
        return None;
    }
    let contains = Expr::const_(Name::from_string("NNVerify.Zonotope.contains"), vec![]);
    let prop = Expr::apps(
        contains,
        [
            args[0].clone(),
            args[1].clone(),
            args[2].clone(),
            args[3].clone(),
        ],
    );
    let w = tc.whnf(&prop);
    let (head, ex_args) = const_app(&w)?;
    if head != "Exists" || ex_args.len() != 2 {
        return None;
    }
    // ex_args[1] : `fun (ε : NNVec 0) => And bounds (x = center + G·ε)`.
    let body = match ex_args[1].kind() {
        ExprKind::Lam(_, _, b) => b.instantiate(&nnvec0_witness()),
        _ => return None,
    };
    let wbody = tc.whnf(&body);
    let (hh, aa) = const_app(&wbody)?;
    if hh != "And" || aa.len() != 2 {
        return None;
    }
    // aa[1] : `@Eq (NNVec 1) x rhs`; both sides are `Fin 1 → Rat`. Instantiate at
    // the single index and decide via the quotient-safe Rat order bridge.
    let (heq, eqargs) = const_app(&aa[1])?;
    if heq != "Eq" || eqargs.len() != 3 {
        return None;
    }
    let xi = Expr::app(eqargs[1].clone(), fin1_zero());
    let ri = Expr::app(eqargs[2].clone(), fin1_zero());
    rat_eq_truth_via_order(tc, &xi, &ri)
}

/// The unified three-valued closed-prop truth oracle used by the engine across
/// ALL carriers. Tries, in order:
/// 1. `NNVerify.IntervalBounds.contains` (per-index `Rat.le` conjunction),
/// 2. `NNVerify.Zonotope.contains` for POINT zonotopes (`k = 0`, `n = 1`),
/// 3. `@Eq Rat` via the order bridge (quotient-safe),
/// 4. closed `Nat.lt` / `Nat.le` decided by decoding,
/// 5. the base `Rat.le` / `Int.le` / free-carrier `@Eq Rat` shapes.
///
/// `None` for anything not engine-decidable (uninterpreted-predicate or
/// opaque-carrier conclusions, or a non-point `Zonotope.contains`), so the
/// engine never fabricates a refutation.
fn prop_truth(tc: &TypeChecker, p: &Expr) -> Option<bool> {
    if let Some((head, args)) = const_app(p) {
        if head == "NNVerify.IntervalBounds.contains" {
            return contains_truth(tc, p);
        }
        if head == "NNVerify.Zonotope.contains" {
            return zono_point_contains_truth(tc, &args);
        }
        if head == "Eq" && args.len() == 3 && tc.is_def_eq(&args[0], &rat_ty()) {
            return rat_eq_truth_via_order(tc, &args[1], &args[2]);
        }
        if head == "Nat.le" && args.len() == 2 {
            let a = decode_nat(tc, &args[0])?;
            let b = decode_nat(tc, &args[1])?;
            return Some(a <= b);
        }
        if head == "Nat.lt" && args.len() == 2 {
            let a = decode_nat(tc, &args[0])?;
            let b = decode_nat(tc, &args[1])?;
            return Some(a < b);
        }
    }
    base_prop_truth(tc, p)
}

// ───────────────────────── binder classification ─────────────────────────

/// Classification of one leading Pi binder of an admitted-axiom type.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum BinderKind {
    /// `Nat` value binder — varied over `{0,1,2}` (also used as the implicit
    /// dimension `{d}` of interval/vector carriers, fixed to `1`).
    Nat,
    /// `Rat` value binder — varied over the junk+well-formed `Rat` battery.
    Rat,
    /// `Fin <bound>` value binder — varied over in-range AND junk indices.
    Fin,
    /// `NNVerify.IntervalBounds d` value binder — point-interval witnesses.
    Interval,
    /// `NNVerify.NNVec d` value binder — constant-vector witnesses.
    Vec,
    /// `NNVerify.Zonotope 1 0` value binder — point-zonotope witnesses (the only
    /// `Zonotope.contains`-decidable slice; see [`zono_point_contains_truth`]).
    Zonotope,
    /// Hypothesis binder (a Prop) — discharged only when it reduces to TRUE.
    Hyp,
    /// Any other binder shape — the engine cannot handle it, so the axiom is
    /// (correctly) reported non-refutable rather than fabricating a witness.
    Other,
}

/// A `Fin 1` constant vector `fun (_ : Fin 1) => r` (an `NNVec 1`).
fn nnvec1_const(r: Expr) -> Expr {
    let fin1 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat(1));
    Expr::lam(BinderInfo::Default, fin1, r)
}

/// Closed point zonotope `Zonotope 1 0` at center `v` (a bare `Rat`):
/// `Zonotope.mk 1 0 (fun _ => v) (fun _ _ => Rat.zero)`. A point zonotope (no
/// generators) contains exactly `v`, so it exercises BOTH `contains` polarities.
fn point_zono1(v: Expr) -> Expr {
    let fin1 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat(1));
    let fin0 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat(0));
    // generators : NNMat 1 0 = Fin 1 → Fin 0 → Rat.
    let gens = Expr::lam(
        BinderInfo::Default,
        fin1.clone(),
        Expr::lam(
            BinderInfo::Default,
            fin0,
            Expr::const_(Name::from_string("Rat.zero"), vec![]),
        ),
    );
    Expr::apps(
        Expr::const_(Name::from_string("NNVerify.Zonotope.mk"), vec![]),
        [nat(1), nat(0), nnvec1_const(v), gens],
    )
}

/// Closed point interval `[v, v] : IntervalBounds 1`, valid via `Rat.le_refl v`.
fn ib1_point(v: Expr) -> Expr {
    let fin1 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat(1));
    let valid = Expr::lam(
        BinderInfo::Default,
        fin1,
        Expr::app(
            Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
            v.clone(),
        ),
    );
    Expr::apps(
        Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]),
        [nat(1), nnvec1_const(v.clone()), nnvec1_const(v), valid],
    )
}

/// Classify a leading-binder domain. `dom` is inspected AFTER earlier binders
/// have been instantiated, so a `Fin <bound>` / `IntervalBounds <d>` domain
/// already carries a concrete bound.
fn binder_kind(tc: &TypeChecker, dom: &Expr) -> BinderKind {
    if tc.is_def_eq(dom, &nat_ty()) {
        return BinderKind::Nat;
    }
    if tc.is_def_eq(dom, &rat_ty()) {
        return BinderKind::Rat;
    }
    let one = nat(1);
    let ib1 = Expr::app(
        Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
        one.clone(),
    );
    let vec1 = Expr::app(
        Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
        one,
    );
    if tc.is_def_eq(dom, &ib1) {
        return BinderKind::Interval;
    }
    if tc.is_def_eq(dom, &vec1) {
        return BinderKind::Vec;
    }
    // `NNVerify.Zonotope 1 0` — the point-zonotope slice the `contains` decoder
    // can decide. (Non-point zonotopes stay `Other` ⇒ the axiom is reported
    // non-refutable rather than fabricating a witness.)
    let zono10 = Expr::apps(
        Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
        [nat(1), nat(0)],
    );
    if tc.is_def_eq(dom, &zono10) {
        return BinderKind::Zonotope;
    }
    // `Fin <something>`: head is the `Fin` constant.
    let w = tc.whnf(dom);
    if let ExprKind::App(f, _) = w.kind() {
        if matches!(f.kind(), ExprKind::Const(nm, _) if nm.to_string() == "Fin") {
            return BinderKind::Fin;
        }
    }
    // A Prop-typed domain is a hypothesis binder.
    match tc.infer_type(dom).map(|t| tc.whnf(&t)) {
        Ok(s) if matches!(s.kind(), ExprKind::Sort(l) if l.is_zero()) => BinderKind::Hyp,
        _ => BinderKind::Other,
    }
}

/// Decode the concrete bound `n` of a `Fin <bound>` domain (0..=4 covers the
/// live envs). Returns `None` for a symbolic bound (skip — non-refutable).
fn fin_bound(tc: &TypeChecker, dom: &Expr) -> Option<u64> {
    let dw = tc.whnf(dom);
    let bound = match dw.kind() {
        ExprKind::App(_, a) => (**a).clone(),
        _ => return None,
    };
    (0..=4u64).find(|&k| tc.is_def_eq(&bound, &nat(k)))
}

// ───────────────────────── refutation engine ─────────────────────────

/// The backtracking-search recursion depth bound. Every admitted axiom in the
/// live envs has ≤ 5 leading binders; the guard catches a pathological type.
const MAX_BINDER_DEPTH: usize = 8;

/// Is the admitted axiom of type `ty` REFUTABLE over its carriers?
///
/// Performs a bounded backtracking search over the leading Pi binders:
/// - `Nat` binders range over `{0,1,2}`,
/// - `Rat` binders over the junk+well-formed `Rat` battery,
/// - `Fin <bound>` binders over the in-range plus junk-index battery,
/// - `IntervalBounds 1` / `NNVec 1` binders over point-interval / constant-vec
///   witnesses (the implicit dimension `{d}` is a `Nat` binder fixed to `1`
///   when it appears; the `1`-witness from the `Nat` range covers it),
/// - hypothesis binders are discharged ONLY when they reduce to a TRUE closed
///   prop (a vacuously-false hypothesis branch is not a refutation).
///
/// The axiom is refutable iff some assignment makes every hypothesis TRUE while
/// the conclusion reduces to a FALSE closed prop.
#[must_use]
pub fn is_refutable(tc: &TypeChecker, ty: &Expr) -> bool {
    fn go(tc: &TypeChecker, cur: &Expr, depth: usize) -> bool {
        if depth > MAX_BINDER_DEPTH {
            return false;
        }
        // Decide the PRE-whnf form first: a `contains B x` / `Zonotope.contains
        // z x` conclusion is a reducible Definition whose head is lost once whnf
        // unfolds it (into a `∀ i, And …` / `Exists …`). Probing `cur` before
        // whnf lets [`prop_truth`]'s `contains` decoders see the head. Genuine
        // `∀`-conclusions (a `Pi`) yield `None` here and fall through to the
        // binder walk below.
        if let Some(t) = prop_truth(tc, cur) {
            return !t;
        }
        let w = tc.whnf(cur);
        let ExprKind::Pi(_, dom, body) = w.kind() else {
            // Reached the conclusion: refutable iff it is a FALSE closed prop.
            return prop_truth(tc, &w) == Some(false);
        };
        let witnesses: Vec<Expr> = match binder_kind(tc, dom) {
            BinderKind::Nat => (0u64..=2).map(nat).collect(),
            BinderKind::Rat => rat_witnesses(),
            BinderKind::Fin => match fin_bound(tc, dom) {
                Some(n) => fin_witnesses_for(n),
                None => return false,
            },
            BinderKind::Interval => [0u64, 1, 5]
                .into_iter()
                .map(|k| ib1_point(rat_mk(of_nat(k), nat(1))))
                .collect::<Vec<_>>(),
            BinderKind::Vec => [0u64, 1, 5]
                .into_iter()
                .map(|k| nnvec1_const(rat_mk(of_nat(k), nat(1))))
                .collect::<Vec<_>>(),
            BinderKind::Zonotope => [0u64, 1, 5]
                .into_iter()
                .map(|k| point_zono1(rat_mk(of_nat(k), nat(1))))
                .collect::<Vec<_>>(),
            BinderKind::Hyp => {
                // Discharge with a sentinel ONLY if the hypothesis is TRUE.
                if prop_truth(tc, dom) == Some(true) {
                    let next =
                        body.instantiate(&Expr::const_(Name::from_string("True.intro"), vec![]));
                    return go(tc, &next, depth + 1);
                }
                return false;
            }
            BinderKind::Other => return false,
        };
        for wexpr in witnesses {
            let next = body.instantiate(&wexpr);
            if go(tc, &next, depth + 1) {
                return true;
            }
        }
        false
    }
    go(tc, ty, 0)
}

// ─────────────────── examined-vs-opaque classification (C4) ───────────────────

/// How C4 actually engaged with one admitted axiom — the honesty distinction the
/// certificate must surface. `is_refutable` returning `false` conflates two very
/// different situations; this enum separates them.
#[derive(Clone, Copy, PartialEq, Eq, Debug, serde::Serialize)]
pub enum RefutationOutcome {
    /// C4 reduced the conclusion to a concrete decidable prop under some
    /// hypothesis-discharging assignment and found a FALSE closed instance: the
    /// axiom is EXPLOITABLE. (Must never occur in a sound env.)
    Refutable,
    /// C4 reduced the conclusion to a concrete decidable prop (an `Int.le` /
    /// `Eq Rat` / `Nat.le` / `contains` …) under at least one
    /// hypothesis-discharging assignment, and EVERY such concrete instance was
    /// TRUE/safe. C4 GENUINELY EXAMINED this axiom and found no counterexample.
    Examined,
    /// C4 could NOT reduce the conclusion to any concrete decidable prop: the
    /// conclusion stayed stuck on an opaque/abstract carrier (an uninterpreted
    /// applied predicate, an `Eq`/inequality over an opaque-valued function with
    /// no closed-decidable form, …) under every reachable assignment — OR no
    /// assignment ever discharged the hypotheses to reach the conclusion. For
    /// such an axiom "not refutable" is VACUOUS: C4 did not examine it, it is
    /// TRUSTED, not verified.
    Opaque,
}

/// Classify how C4 engaged with the admitted axiom of type `ty`: did it actually
/// EXAMINE the conclusion (reduce it to a concrete decidable prop) or is the
/// conclusion OPAQUE to refutation (stuck on an abstract carrier)?
///
/// This runs the SAME bounded backtracking search as [`is_refutable`], but tracks
/// a third signal: whether any reachable conclusion node reduced — via
/// [`prop_truth`] — to a *concrete decidable* proposition (`Some(_)`). The
/// outcome is:
/// - [`RefutationOutcome::Refutable`] iff some reachable conclusion is a FALSE
///   concrete prop (identical to `is_refutable == true`);
/// - else [`RefutationOutcome::Examined`] iff some reachable conclusion reduced
///   to a concrete decidable prop (necessarily TRUE/safe, since none was false);
/// - else [`RefutationOutcome::Opaque`] — the conclusion never reduced to a
///   concrete decidable prop, so C4 could not examine the axiom at all.
#[must_use]
pub fn classify_refutation(tc: &TypeChecker, ty: &Expr) -> RefutationOutcome {
    /// Returns `(found_false, found_decided)` over the reachable conclusion
    /// nodes of this subtree: `found_false` iff some conclusion is a FALSE
    /// concrete prop; `found_decided` iff some conclusion reduced to a concrete
    /// decidable prop (`prop_truth == Some(_)`).
    fn go(tc: &TypeChecker, cur: &Expr, depth: usize) -> (bool, bool) {
        if depth > MAX_BINDER_DEPTH {
            return (false, false);
        }
        // Decide the PRE-whnf form first (see [`is_refutable`]): a reducible
        // `contains` conclusion loses its head once whnf unfolds it, so probe
        // `cur` before whnf to let the `contains` decoders engage. A genuine
        // `∀`-conclusion yields `None` here and falls through to the binder walk.
        match prop_truth(tc, cur) {
            Some(false) => return (true, true),
            Some(true) => return (false, true),
            None => {}
        }
        let w = tc.whnf(cur);
        let ExprKind::Pi(_, dom, body) = w.kind() else {
            // Reached the conclusion. `Some(false)` ⇒ refutable AND examined;
            // `Some(true)` ⇒ examined-safe; `None` ⇒ opaque (not examined).
            return match prop_truth(tc, &w) {
                Some(false) => (true, true),
                Some(true) => (false, true),
                None => (false, false),
            };
        };
        let witnesses: Vec<Expr> = match binder_kind(tc, dom) {
            BinderKind::Nat => (0u64..=2).map(nat).collect(),
            BinderKind::Rat => rat_witnesses(),
            BinderKind::Fin => match fin_bound(tc, dom) {
                Some(n) => fin_witnesses_for(n),
                None => return (false, false),
            },
            BinderKind::Interval => [0u64, 1, 5]
                .into_iter()
                .map(|k| ib1_point(rat_mk(of_nat(k), nat(1))))
                .collect::<Vec<_>>(),
            BinderKind::Vec => [0u64, 1, 5]
                .into_iter()
                .map(|k| nnvec1_const(rat_mk(of_nat(k), nat(1))))
                .collect::<Vec<_>>(),
            BinderKind::Zonotope => [0u64, 1, 5]
                .into_iter()
                .map(|k| point_zono1(rat_mk(of_nat(k), nat(1))))
                .collect::<Vec<_>>(),
            BinderKind::Hyp => {
                // Discharge with a sentinel ONLY if the hypothesis is TRUE; an
                // undischargeable hypothesis means the conclusion is never
                // reached on this branch (contributes nothing — opaque).
                if prop_truth(tc, dom) == Some(true) {
                    let next =
                        body.instantiate(&Expr::const_(Name::from_string("True.intro"), vec![]));
                    return go(tc, &next, depth + 1);
                }
                return (false, false);
            }
            BinderKind::Other => return (false, false),
        };
        let mut any_false = false;
        let mut any_decided = false;
        for wexpr in witnesses {
            let next = body.instantiate(&wexpr);
            let (f, d) = go(tc, &next, depth + 1);
            any_false |= f;
            any_decided |= d;
        }
        (any_false, any_decided)
    }
    let (found_false, found_decided) = go(tc, ty, 0);
    if found_false {
        RefutationOutcome::Refutable
    } else if found_decided {
        RefutationOutcome::Examined
    } else {
        RefutationOutcome::Opaque
    }
}

// ─────────────────── conjecture (proof-target) refutation ───────────────────
//
// `is_refutable` / `classify_refutation` above are the C4 cert path: they probe
// admitted AXIOMS over carrier witnesses. They deliberately do NOT enumerate a
// `BoolFn` binder (it classifies as `BinderKind::Other`), and they cap `Nat`
// witnesses at `{0,1,2}`. That blind spot is exactly how a FALSE Boolean-analysis
// proof TARGET (`deriv_level_mass_lower : ∀ n f k, 2^k≤n → Var ≤ 9·M_{≥k}`, refuted
// by the dictator at `n=4,k=2`) was written into a roadmap and handed to provers.
//
// `refute_conjecture` closes that blind spot for PROPOSED TARGETS: it carries a
// `BoolFn` witness battery (the two constants + the dictators — the canonical
// separating functions of Boolean analysis) and a wider `Nat` range, and returns
// a CLEAR, human-readable counterexample. Run it on a conjecture BEFORE investing
// in a proof. It is intentionally separate from the C4 path, so the certificate's
// behaviour is unchanged.

/// `BoolAnalysis.HCPoint n` — the cube-point type `Fin n → Bool`.
fn hcpoint_ty(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
        nat(n),
    )
}

/// Witness battery for a `BoolFn n = HCPoint n → Bool` binder at concrete `n`:
/// the two constants and the (up to 3) dictators `fun x => x i`. A dictator puts
/// ALL its Fourier mass at level 1 — the extremal counterexample to high-level
/// concentration claims like `Var ≤ C·M_{≥k}`. Each is a closed term the kernel
/// evaluates on concrete inputs.
fn boolfn_witnesses_for(n: u64) -> Vec<(String, Expr)> {
    let hcp = hcpoint_ty(n);
    let const_fn = |b: &str| {
        Expr::lam(
            BinderInfo::Default,
            hcp.clone(),
            Expr::const_(Name::from_string(b), vec![]),
        )
    };
    let mut ws = vec![
        ("const-false".to_string(), const_fn("Bool.false")),
        ("const-true".to_string(), const_fn("Bool.true")),
    ];
    for i in 0..n.min(3) {
        // `fun (x : HCPoint n) => x (i : Fin n)` — `x` is BVar(0) under the λ.
        let body = Expr::app(Expr::from_kind(ExprKind::BVar(0)), fin_mk(n, i));
        ws.push((
            format!("dictator[{i}]"),
            Expr::lam(BinderInfo::Default, hcp.clone(), body),
        ));
    }
    ws
}

/// Detect a `BoolAnalysis.BoolFn n` domain and return the concrete `n`.
fn boolfn_arg(tc: &TypeChecker, dom: &Expr) -> Option<u64> {
    applied_const_arg(tc, dom, "BoolAnalysis.BoolFn")
}

/// Detect a `BoolAnalysis.HCPoint n` domain and return the concrete `n`.
fn hcpoint_arg(tc: &TypeChecker, dom: &Expr) -> Option<u64> {
    applied_const_arg(tc, dom, "BoolAnalysis.HCPoint")
}

/// If `dom` is `<name> <arg>` with `<arg>` a decodable `Nat`, return it.
fn applied_const_arg(tc: &TypeChecker, dom: &Expr, name: &str) -> Option<u64> {
    if let ExprKind::App(f, a) = dom.kind() {
        if matches!(f.kind(), ExprKind::Const(nm, _) if nm.to_string() == name) {
            return decode_nat(tc, a);
        }
    }
    None
}

/// Witness battery for an `HCPoint n = Fin n → Bool` cube-point binder: the
/// all-false and all-true points. These separate the constant cases and make any
/// dictator evaluate; standard basis points `e_i` (a closed `fun j => Nat.beq
/// (Fin.val j) i`) can be added when a statement needs coordinate distinctions.
fn hcpoint_witnesses_for(n: u64) -> Vec<(String, Expr)> {
    let fin_n = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat(n));
    let const_pt = |b: &str| {
        Expr::lam(
            BinderInfo::Default,
            fin_n.clone(),
            Expr::const_(Name::from_string(b), vec![]),
        )
    };
    vec![
        ("0ⁿ".to_string(), const_pt("Bool.false")),
        ("1ⁿ".to_string(), const_pt("Bool.true")),
    ]
}

/// Render a closed `Int` numeral (`Int.ofNat k` / `Int.negSucc k`) for a clear
/// counterexample message; `?` if it does not reduce to a numeral.
fn render_int(tc: &TypeChecker, e: &Expr) -> String {
    let w = tc.whnf(e);
    if let ExprKind::App(h, k) = w.kind() {
        if let Some(kk) = decode_nat(tc, k) {
            match h.kind() {
                ExprKind::Const(nm, _) if nm.to_string() == "Int.ofNat" => return kk.to_string(),
                ExprKind::Const(nm, _) if nm.to_string() == "Int.negSucc" => {
                    return format!("-{}", kk + 1)
                }
                _ => {}
            }
        }
    }
    "?".to_string()
}

/// Render a closed `Nat` or `Rat` (`Rat.mk num denom`) operand to a readable
/// value for a clear counterexample; `?` if it does not reduce to a numeral.
fn render_value(tc: &TypeChecker, e: &Expr) -> String {
    let w = tc.whnf(e);
    if let Some(k) = decode_nat(tc, &w) {
        return k.to_string();
    }
    if let ExprKind::App(inner, denom) = w.kind() {
        if let ExprKind::App(h, num) = inner.kind() {
            if matches!(h.kind(), ExprKind::Const(nm, _) if nm.to_string() == "Rat.mk") {
                let n = render_int(tc, num);
                return match decode_nat(tc, denom) {
                    Some(1) => n,
                    Some(d) => format!("{n}/{d}"),
                    None => format!("{n}/?"),
                };
            }
        }
    }
    "?".to_string()
}

/// If `prop` is a closed decidable comparison (`Rat.le` / `Nat.le` / `Int.le`),
/// render it with its EVALUATED operands so the counterexample reads like an
/// indictment: `` `1 ≤ 0` is FALSE ``.
fn describe_false_prop(tc: &TypeChecker, prop: &Expr) -> Option<String> {
    if let ExprKind::App(inner, b) = prop.kind() {
        if let ExprKind::App(h, a) = inner.kind() {
            if let ExprKind::Const(nm, _) = h.kind() {
                let op = match nm.to_string().as_str() {
                    "Rat.le" | "Nat.le" | "Int.le" => "≤",
                    _ => return None,
                };
                return Some(format!(
                    "`{} {op} {}` is FALSE",
                    render_value(tc, a),
                    render_value(tc, b)
                ));
            }
        }
    }
    None
}

/// Refute a PROPOSED conjecture (a closed theorem-target `Prop`) by searching
/// small concrete instances — including the `BoolFn` battery (constants +
/// dictators) and a `Nat` range wide enough to satisfy dyadic guards like
/// `2^k ≤ n` — and return a human-readable counterexample if the statement is
/// FALSE at some instance, or `None` if no small counterexample is found.
///
/// This is the target-refutation gate: a false target produces honest *prover
/// failures*, not a red test, so a prover swarm can burn for hours on a
/// statement that a 30-second dictator check would have killed. Run this FIRST.
///
/// `None` is NOT a proof of truth — it only means no counterexample was found
/// within the small-instance battery (`n ≤ 4`, the canonical functions). It is a
/// cheap, high-yield filter, not a decision procedure.
#[must_use]
pub fn refute_conjecture(tc: &TypeChecker, ty: &Expr) -> Option<String> {
    const MAX_NAT: u64 = 4;
    const MAX_DEPTH: usize = MAX_BINDER_DEPTH + 8;
    fn go(tc: &TypeChecker, cur: &Expr, depth: usize, trail: &mut Vec<String>) -> Option<String> {
        if depth > MAX_DEPTH {
            return None;
        }
        let hit = |trail: &[String], prop: &Expr| {
            let verdict = describe_false_prop(tc, prop)
                .map(|d| format!(" — {d}"))
                .unwrap_or_default();
            Some(format!(
                "counterexample at {{ {} }}{verdict}",
                trail.join(", ")
            ))
        };
        if let Some(t) = prop_truth(tc, cur) {
            return if t { None } else { hit(trail, cur) };
        }
        let w = tc.whnf(cur);
        let ExprKind::Pi(_, dom, body) = w.kind() else {
            return if prop_truth(tc, &w) == Some(false) {
                hit(trail, cur)
            } else {
                None
            };
        };
        // A `BoolFn n` binder (which `binder_kind` reports as `Other`) gets the
        // canonical Boolean-function battery; everything else reuses the C4
        // classifier but with the wider `Nat`/labelled witness sets.
        let witnesses: Vec<(String, Expr)> = if let Some(n) = boolfn_arg(tc, dom) {
            boolfn_witnesses_for(n)
        } else if let Some(n) = hcpoint_arg(tc, dom) {
            hcpoint_witnesses_for(n)
        } else {
            match binder_kind(tc, dom) {
                BinderKind::Nat => (0..=MAX_NAT)
                    .map(|k| (format!("Nat={k}"), nat(k)))
                    .collect(),
                BinderKind::Rat => rat_witnesses()
                    .into_iter()
                    .enumerate()
                    .map(|(i, e)| (format!("Rat#{i}"), e))
                    .collect(),
                BinderKind::Fin => {
                    let n = fin_bound(tc, dom)?;
                    fin_witnesses_for(n)
                        .into_iter()
                        .enumerate()
                        .map(|(i, e)| (format!("Fin#{i}"), e))
                        .collect()
                }
                BinderKind::Hyp => {
                    // Only explore instances where the hypothesis HOLDS (a false
                    // hypothesis makes the implication vacuously true — not a
                    // counterexample). The proof term is irrelevant to the
                    // conclusion's decidable truth, so a sentinel discharges it.
                    if prop_truth(tc, dom) == Some(true) {
                        let next = body
                            .instantiate(&Expr::const_(Name::from_string("True.intro"), vec![]));
                        return go(tc, &next, depth + 1, trail);
                    }
                    return None;
                }
                BinderKind::Interval
                | BinderKind::Vec
                | BinderKind::Zonotope
                | BinderKind::Other => {
                    return None;
                }
            }
        };
        for (label, wexpr) in witnesses {
            trail.push(label);
            let next = body.instantiate(&wexpr);
            if let Some(cex) = go(tc, &next, depth + 1, trail) {
                return Some(cex);
            }
            trail.pop();
        }
        None
    }
    go(tc, ty, 0, &mut Vec::new())
}

// ───────────────────────── census over carriers ─────────────────────────

/// A census of one concrete inductive carrier, classifying whether it can admit
/// JUNK witnesses outside its intended mathematical domain.
#[derive(Clone, Debug, serde::Serialize)]
pub struct CarrierCensus {
    /// The inductive type name (e.g. `Fin`, `Rat.Raw`, `Int`).
    pub name: String,
    /// Whether the carrier is *junk-admitting*: a constructor field typed `Prop`
    /// (a propositional INVARIANT carried as a value, not a proof), so the
    /// constructor accepts witnesses that violate the intended invariant
    /// (e.g. `Fin.mk _ _ True`). Such carriers are the source of false axioms.
    pub junk_admitting: bool,
    /// The constructor whose `Prop`-typed field makes the carrier junk-admitting
    /// (for the report); `None` for faithful/opaque carriers.
    pub junk_constructor: Option<String>,
}

/// Census EVERY concrete inductive carrier in `env`, classifying junk-admitting
/// (a constructor field typed in `Prop` that encodes an invariant as a value,
/// e.g. `Fin.mk`'s `isLt : Prop`) vs faithful. The classification is purely
/// structural (it inspects each constructor's telescope for a `Prop`-typed
/// non-parameter field), so it discovers a FUTURE junk carrier automatically.
#[must_use]
pub fn census_carriers(env: &Environment) -> Vec<CarrierCensus> {
    let tc = TypeChecker::with_mode(env, env.mode());
    let mut out: Vec<CarrierCensus> = Vec::new();

    for ind in env.inductives() {
        let num_params = ind.num_params;
        // A `Prop`-sorted inductive (e.g. `And`, `Eq`) is a PROOF type: its
        // constructors' `Prop`-typed fields are genuine proof arguments, not
        // invariant-as-value junk. Only data-sorted carriers can be
        // junk-admitting.
        let ind_is_prop = result_sort_is_prop(&tc, &ind.type_);
        let mut junk_ctor: Option<String> = None;

        if !ind_is_prop {
            for ctor_name in &ind.constructor_names {
                let Some(cval) = env.get_constructor(ctor_name) else {
                    continue;
                };
                if constructor_has_prop_field(&tc, &cval.type_, num_params) {
                    junk_ctor = Some(ctor_name.to_string());
                    break;
                }
            }
        }

        out.push(CarrierCensus {
            name: ind.name.to_string(),
            junk_admitting: junk_ctor.is_some(),
            junk_constructor: junk_ctor,
        });
    }

    out.sort_by(|a, b| a.name.cmp(&b.name));
    out
}

/// Does the type's RESULT sort (after peeling leading Pi binders) land in `Prop`
/// (`Sort 0`)? Used to detect proof-sorted inductives.
fn result_sort_is_prop(tc: &TypeChecker, ty: &Expr) -> bool {
    let mut cur = ty.clone();
    // Peel leading Pi binders (the inductive's params/indices). We instantiate
    // with a `Sort 0` sentinel; the FINAL sort of a non-dependent codomain is
    // unaffected, and a dependent codomain still WHNF's to the universe.
    let sentinel = Expr::prop();
    for _ in 0..32 {
        let w = tc.whnf(&cur);
        match w.kind() {
            ExprKind::Pi(_, _, body) => cur = body.instantiate(&sentinel),
            _ => {
                cur = w;
                break;
            }
        }
    }
    matches!(tc.whnf(&cur).kind(), ExprKind::Sort(l) if l.is_zero())
}

/// Does the constructor's type telescope have a non-parameter FIELD whose type
/// is `Prop` itself (i.e. the field carries a PROPOSITION as a value, not a
/// proof of one)? That is exactly the junk-admitting pattern: `Fin.mk`'s
/// `isLt : Prop` accepts ANY proposition (`True`), not a proof of `val < n`, so
/// `Fin n` is inhabited by out-of-range / `n = 0` junk witnesses.
///
/// The first `num_params` Pi binders are parameters (shared with the inductive),
/// not fields; only binders AFTER them count.
fn constructor_has_prop_field(tc: &TypeChecker, ctor_ty: &Expr, num_params: u32) -> bool {
    // Walk the telescope, instantiating each binder with a `Prop` sentinel so
    // nested domains are closed. We only need the SHAPE (is the domain literally
    // `Prop` = `Sort 0`?) of each field domain.
    let sentinel = Expr::prop();
    let mut cur = ctor_ty.clone();
    let mut idx: u32 = 0;
    while let ExprKind::Pi(_, dom, body) = cur.kind() {
        // A field whose DOMAIN is definitionally `Prop` (`Sort 0`) carries a
        // proposition-as-value — the junk slot.
        if idx >= num_params && matches!(tc.whnf(dom).kind(), ExprKind::Sort(l) if l.is_zero()) {
            return true;
        }
        idx += 1;
        let next = body.instantiate(&sentinel);
        cur = next;
    }
    false
}

/// One refutation result over the full environment.
#[derive(Clone, Debug, serde::Serialize)]
pub struct RefutationScan {
    /// Total admitted (`Axiom`-kind, non-foundational, non-trust-marker) axioms
    /// scanned.
    pub admitted_scanned: usize,
    /// Names of admitted axioms the engine found REFUTABLE (a closed
    /// counterexample exists). MUST be empty for a sound environment.
    pub refutable: Vec<String>,
    /// Names of admitted axioms C4 genuinely EXAMINED: the conclusion reduced to
    /// a concrete decidable prop under some assignment and was found
    /// counterexample-free. `refutable ⊆ examined` (a refuted axiom was also
    /// examined). The `examined` minus `refutable` set is the truly checked-safe
    /// part of the trusted base.
    pub examined: Vec<String>,
    /// Names of admitted axioms OPAQUE to refutation: the conclusion never
    /// reduced to a concrete decidable prop (it is over an abstract carrier with
    /// no closed-decidable form), so "not refutable" is VACUOUS here. These are
    /// TRUSTED, NOT CHECKED. Disjoint from `examined`;
    /// `examined.len() + opaque_unexamined.len() == admitted_scanned`.
    pub opaque_unexamined: Vec<String>,
    /// The carrier census (for the certificate's documentation).
    pub carriers: Vec<CarrierCensus>,
}

/// Run the carrier-generic refutation engine over EVERY admitted axiom in `env`
/// (every `Axiom`-kind constant that is neither a foundational axiom nor a
/// trust marker), returning the set found refutable. A sound environment yields
/// an EMPTY refutable set.
#[must_use]
pub fn scan_admitted_axioms(env: &Environment) -> RefutationScan {
    use super::axiom_audit::is_foundational_axiom;
    use super::axiom_audit::is_trust_marker;

    let tc = TypeChecker::with_mode(env, env.mode());
    let mut admitted_scanned = 0usize;
    let mut refutable = Vec::new();
    let mut examined = Vec::new();
    let mut opaque_unexamined = Vec::new();

    for c in env.constants() {
        if c.kind != ConstantKind::Axiom {
            continue;
        }
        if is_foundational_axiom(&c.name) || is_trust_marker(&c.name) {
            continue;
        }
        admitted_scanned += 1;
        let name = c.name.to_string();
        match classify_refutation(&tc, &c.type_) {
            RefutationOutcome::Refutable => {
                // A refuted axiom IS examined (its concrete conclusion reduced).
                refutable.push(name.clone());
                examined.push(name);
            }
            RefutationOutcome::Examined => examined.push(name),
            RefutationOutcome::Opaque => opaque_unexamined.push(name),
        }
    }
    refutable.sort();
    examined.sort();
    opaque_unexamined.sort();

    RefutationScan {
        admitted_scanned,
        refutable,
        examined,
        opaque_unexamined,
        carriers: census_carriers(env),
    }
}

// ───────────────── opacity-transparency refutation (C4') ─────────────────

/// One masked-axiom finding from the opacity-transparency pass: an admitted
/// axiom whose conclusion is NON-refutable while a carrier in its type stays
/// `Opaque`, but BECOMES refutable once that carrier δ-unfolds. This is exactly
/// the `Rat.abs`-class masking bug (`Rat.abs_nonneg : 0 ≤ |q|` is invisible to
/// C4 because `Rat.abs` is opaque, yet `|q|` δ-reduces to `q`, making the prop
/// `0 ≤ q`, false for `q < 0`).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct MaskedAxiom {
    /// The admitted axiom unmasked once the carrier becomes transparent.
    pub axiom: String,
    /// The `Opaque`-with-body carrier whose opacity was masking the refutation.
    pub carrier: String,
}

/// Result of the opacity-transparency refutation pass over an environment.
#[derive(Clone, Debug, Default, serde::Serialize)]
pub struct OpacityScan {
    /// Number of `Opaque`-with-body carriers examined (the risk set).
    pub checked: usize,
    /// Number of admitted axioms found refutable ONLY once their opaque carrier
    /// was made transparent (i.e. opacity-masked). MUST be 0 for soundness.
    pub refutable: usize,
    /// The masked-axiom findings (sorted). MUST be empty for soundness.
    pub masked: Vec<MaskedAxiom>,
}

/// Does `ty` mention the constant `carrier` anywhere (head or argument)?
fn type_mentions(ty: &Expr, carrier: &Name) -> bool {
    ty.collect_constants().contains(carrier)
}

/// The opacity-transparency refutation pass (certificate claim C4').
///
/// For EVERY `Declaration::Opaque` carrier in `env` that HAS a body, build a
/// scratch view (via [`Environment::with_opaque_made_transparent`]) where that
/// carrier is a TRANSPARENT reducible `Declaration::Definition` with the same
/// body, then re-run the EXISTING C4 refutation engine ([`is_refutable`]) over
/// the admitted axioms whose type mentions that carrier. An axiom is reported
/// MASKED iff it is NON-refutable under the real (opaque) env but BECOMES
/// refutable under the transparent scratch env — that delta is precisely the
/// unsoundness the carrier's opacity was hiding.
///
/// This reuses the single carrier_refutation engine (no second refutation
/// engine): only the env's unfold posture for one carrier at a time changes.
/// A sound environment yields an EMPTY masked set.
#[must_use]
pub fn scan_opacity_masked_axioms(env: &Environment) -> OpacityScan {
    use super::axiom_audit::is_foundational_axiom;
    use super::axiom_audit::is_trust_marker;

    // The admitted axioms (name + type), computed once against the real env.
    let admitted: Vec<(Name, Expr)> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Axiom)
        .filter(|c| !is_foundational_axiom(&c.name) && !is_trust_marker(&c.name))
        .map(|c| (c.name.clone(), c.type_.clone()))
        .collect();

    // The opaque-with-body carrier risk set (sorted for deterministic output).
    let mut opaque_carriers: Vec<Name> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Opaque && c.value.is_some())
        .map(|c| c.name.clone())
        .collect();
    opaque_carriers.sort_by_key(Name::to_string);

    let tc_real = TypeChecker::with_mode(env, env.mode());

    let mut out = OpacityScan::default();
    for carrier in &opaque_carriers {
        out.checked += 1;

        // The admitted axioms whose TYPE references this carrier — the only ones
        // whose refutability can change when the carrier unfolds.
        let mentioning: Vec<&(Name, Expr)> = admitted
            .iter()
            .filter(|(_, ty)| type_mentions(ty, carrier))
            .collect();
        if mentioning.is_empty() {
            continue;
        }

        // Make ONLY this carrier transparent and re-run the existing engine.
        let Some(scratch) = env.with_opaque_made_transparent(carrier) else {
            continue;
        };
        let tc_scratch = TypeChecker::with_mode(&scratch, scratch.mode());

        for (name, ty) in mentioning {
            // Masked ⟺ non-refutable while opaque, refutable once transparent.
            if !is_refutable(&tc_real, ty) && is_refutable(&tc_scratch, ty) {
                out.refutable += 1;
                out.masked.push(MaskedAxiom {
                    axiom: name.to_string(),
                    carrier: carrier.to_string(),
                });
            }
        }
    }

    out.masked
        .sort_by(|a, b| (&a.axiom, &a.carrier).cmp(&(&b.axiom, &b.carrier)));
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `classify_refutation` must split the three outcomes apart: a FALSE Rat
    /// axiom is `Refutable`, a TRUE Rat axiom is `Examined` (the conclusion DID
    /// reduce to a concrete decidable `Int.le`), and an axiom whose conclusion is
    /// an UNINTERPRETED applied predicate stays `Opaque` — C4 cannot examine it,
    /// so "not refutable" is vacuous, not checked-safe.
    #[test]
    fn classify_splits_examined_from_opaque() {
        let mut env = Environment::new();
        env.init_nn_verify_interval_arith_proofs()
            .expect("init interval arith proofs");

        let rat = rat_ty();
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);

        // Register an uninterpreted predicate `P : Rat → Prop` up front (the
        // Opaque case below uses it). Done before building `tc` to avoid a borrow
        // conflict.
        env.add_decl(super::super::Declaration::Axiom {
            name: Name::from_string("P"),
            level_params: vec![],
            type_: Expr::arrow(rat.clone(), Expr::prop()),
        })
        .expect("P : Rat → Prop is well-typed");
        let tc = TypeChecker::with_mode(&env, env.mode());

        // ∀ a b : Rat, Rat.le a b — FALSE ⇒ Refutable (and counted examined).
        let bogus = Expr::pi(
            BinderInfo::Default,
            rat.clone(),
            Expr::pi(
                BinderInfo::Default,
                rat.clone(),
                Expr::apps(rat_le.clone(), [Expr::bvar(1), Expr::bvar(0)]),
            ),
        );
        assert_eq!(
            classify_refutation(&tc, &bogus),
            RefutationOutcome::Refutable,
            "a FALSE concrete-carrier axiom must classify Refutable"
        );

        // ∀ a : Rat, Rat.le a a — TRUE concrete ⇒ Examined (genuinely checked).
        let refl = Expr::pi(
            BinderInfo::Default,
            rat.clone(),
            Expr::apps(rat_le, [Expr::bvar(0), Expr::bvar(0)]),
        );
        assert_eq!(
            classify_refutation(&tc, &refl),
            RefutationOutcome::Examined,
            "a TRUE concrete-carrier axiom must classify Examined (not Opaque)"
        );

        // ∀ a : Rat, P a — P uninterpreted (a free `Rat → Prop` axiom). The
        // conclusion never reduces to a concrete decidable prop ⇒ Opaque.
        let opaque_concl = Expr::pi(
            BinderInfo::Default,
            rat,
            Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0)),
        );
        assert_eq!(
            classify_refutation(&tc, &opaque_concl),
            RefutationOutcome::Opaque,
            "an uninterpreted-predicate conclusion must classify Opaque (C4 cannot \
             examine it — 'not refutable' is vacuous)"
        );
        // And it must NOT be reported refutable (the engine never fabricates).
        assert!(!is_refutable(&tc, &opaque_concl));
    }

    /// The engine must NOT be vacuously non-refuting: it must REFUTE a hand-built
    /// quantified false axiom `∀ a b : Rat, Rat.le a b` (junk witnesses make the
    /// conclusion a FALSE closed `Int.le`) and must NOT refute the TRUE
    /// `∀ a : Rat, Rat.le a a`.
    #[test]
    fn engine_distinguishes_true_from_false_rat() {
        let mut env = Environment::new();
        env.init_nn_verify_interval_arith_proofs()
            .expect("init interval arith proofs");
        let tc = TypeChecker::with_mode(&env, env.mode());

        let rat = rat_ty();
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);

        // ∀ a b : Rat, Rat.le a b  (FALSE: a = mk 1 0, b = mk 0 1 ⇒ Int.le 1 0).
        let body = Expr::apps(rat_le.clone(), [Expr::bvar(1), Expr::bvar(0)]);
        let inner = Expr::pi(BinderInfo::Default, rat.clone(), body);
        let bogus = Expr::pi(BinderInfo::Default, rat.clone(), inner);
        assert!(
            is_refutable(&tc, &bogus),
            "engine must refute `∀ a b : Rat, Rat.le a b`"
        );

        // ∀ a : Rat, Rat.le a a  (TRUE — reflexive).
        let refl = Expr::pi(
            BinderInfo::Default,
            rat,
            Expr::apps(rat_le, [Expr::bvar(0), Expr::bvar(0)]),
        );
        assert!(
            !is_refutable(&tc, &refl),
            "engine must NOT refute the reflexive `∀ a : Rat, Rat.le a a`"
        );
    }

    /// The census must flag a JUNK-ADMITTING data carrier — a non-`Prop` inductive
    /// whose constructor carries an invariant as a `Prop`-typed VALUE field (the
    /// exact pre-faithful-`Fin` shape `mk : (val : Nat) → (inv : Prop) → _`) — and
    /// must NOT flag faithful carriers (`Fin` after the faithful-carrier migration,
    /// whose `isLt : Nat.lt val n` field is a genuine PROOF, not a `Prop` value;
    /// and `Nat`, whose constructors carry no `Prop` field).
    ///
    /// This is the DETECTOR meta-test: it pins that `census_carriers` still flags
    /// the junk-as-value pattern structurally. (Pre-migration this test used `Fin`
    /// itself as the positive case; the faithful migration repaired `Fin`, so the
    /// positive case is now a freshly-registered junk carrier — the detector must
    /// keep flagging it WITHOUT anyone re-adding `Fin` to a hand-curated list.)
    #[test]
    fn census_flags_junk_carrier_not_faithful_fin_or_nat() {
        use super::super::{Constructor, InductiveDecl, InductiveType};
        use crate::env::decl_builder::EnvDeclBuilder;

        let mut env = Environment::new();
        env.init_fin().expect("init_fin");
        env.init_true_false().expect("init_true_false");

        // Register a deliberately JUNK-ADMITTING carrier:
        //   structure JunkBox : Type where
        //     val : Nat
        //     inv : Prop        -- invariant carried as a VALUE (any Prop fits)
        // This is exactly the pre-faithful-`Fin` `Fin.mk _ _ True` junk shape.
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let type_ = Expr::from_kind(crate::expr::ExprKind::Sort(crate::level::Level::succ(
            crate::level::Level::zero(),
        )));
        let prop = Expr::from_kind(crate::expr::ExprKind::Sort(crate::level::Level::zero()));
        let junk_const = Expr::const_(Name::from_string("JunkBox"), vec![]);
        let junk_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (val_id, _val) = b.fresh_local(nat_const.clone());
            let (inv_id, _inv) = b.fresh_local(prop.clone()); // inv : Prop (the junk slot)
            let r = junk_const.clone();
            let r = b.mk_pi(inv_id, BinderInfo::Default, prop.clone(), r);
            let r = b.mk_pi(val_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("JunkBox"),
                type_,
                constructors: vec![Constructor {
                    name: Name::from_string("JunkBox.mk"),
                    type_: junk_mk_type,
                }],
            }],
        })
        .expect("register junk carrier");

        let carriers = census_carriers(&env);

        let junk = carriers.iter().find(|c| c.name == "JunkBox");
        assert!(
            junk.is_some_and(
                |c| c.junk_admitting && c.junk_constructor.as_deref() == Some("JunkBox.mk")
            ),
            "the census MUST flag a `mk : Nat → Prop → _` junk carrier as \
             junk-admitting (the invariant-as-value pattern), got {junk:?}"
        );

        // `Fin` is now FAITHFUL (its `isLt : Nat.lt val n` field is a PROOF, not a
        // `Prop` value), so the census must NOT flag it — the faithful migration is
        // exactly what removed it from the junk set.
        let fin = carriers.iter().find(|c| c.name == "Fin");
        assert!(
            fin.is_some_and(|c| !c.junk_admitting),
            "Fin must NOT be flagged junk-admitting after the faithful-carrier \
             migration (isLt is a Nat.lt proof, not a Prop value), got {fin:?}"
        );

        let nat = carriers.iter().find(|c| c.name == "Nat");
        assert!(
            nat.is_some_and(|c| !c.junk_admitting),
            "Nat must NOT be flagged junk-admitting, got {nat:?}"
        );
    }

    /// The opacity-transparency pass must be SOUND-by-default (no masked axioms
    /// over a sound Rat env) yet CATCH a planted `Rat.abs`-class masking: an
    /// opaque identity carrier `Foo := fun a => a` plus `bad : ∀ q, 0 ≤ Foo q`
    /// (false once `Foo` unfolds, invisible while it stays opaque).
    #[test]
    fn opacity_pass_catches_planted_identity_carrier() {
        use super::super::Declaration;
        use crate::expr::BinderInfo;

        let mut env = Environment::new();
        env.init_nn_verify_interval_arith_proofs()
            .expect("init interval arith proofs");

        // Sound baseline: nothing masked.
        assert!(
            scan_opacity_masked_axioms(&env).masked.is_empty(),
            "baseline Rat env must have no opacity-masked axioms"
        );

        // Opaque identity carrier `Foo : Rat → Rat := fun a => a`.
        let rat = rat_ty();
        env.add_decl(Declaration::Opaque {
            name: Name::from_string("Foo"),
            level_params: vec![],
            type_: Expr::arrow(rat.clone(), rat.clone()),
            value: Expr::lam(BinderInfo::Default, rat.clone(), Expr::bvar(0)),
        })
        .expect("Foo : Rat → Rat is well-typed");

        // `bad : ∀ q : Rat, Rat.le (0/1) (Foo q)` — false at q = -1 once unfolded.
        let bad_body = Expr::apps(
            Expr::const_(Name::from_string("Rat.le"), vec![]),
            [
                rat_mk(of_nat(0), nat(1)),
                Expr::app(
                    Expr::const_(Name::from_string("Foo"), vec![]),
                    Expr::bvar(0),
                ),
            ],
        );
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("bad"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, rat, bad_body),
        })
        .expect("bad axiom type-checks");

        let scan = scan_opacity_masked_axioms(&env);
        assert!(
            scan.masked
                .iter()
                .any(|m| m.axiom == "bad" && m.carrier == "Foo"),
            "opacity pass must flag `bad` masked by opaque `Foo`; masked={:?}",
            scan.masked
        );
    }

    /// Build the env carrying the zonotope `contains` decoder surface (the
    /// reducible `Zonotope.contains` Definition + the three formerly-false
    /// admitted Zonotope axioms after their honest restatement).
    fn zono_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_zonotope_proofs().expect("proofs");
        env.init_nn_verify_zonotope_compress().expect("compress");
        env
    }

    /// `Zonotope.contains` for a POINT zonotope decides point-containment in BOTH
    /// directions: a point zonotope at `0` contains `0` (TRUE) and NOT `1`
    /// (FALSE). This pins that the decoder is not vacuous — the C4 examined/
    /// refutable distinction below is meaningful.
    #[test]
    fn zono_point_contains_decoder_decides_both_ways() {
        let env = zono_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let z0 = point_zono1(rat_mk(of_nat(0), nat(1)));
        let x0 = nnvec1_const(rat_mk(of_nat(0), nat(1)));
        let x1 = nnvec1_const(rat_mk(of_nat(1), nat(1)));

        assert_eq!(
            zono_point_contains_truth(&tc, &[nat(1), nat(0), z0.clone(), x0]),
            Some(true),
            "a point zonotope at 0 contains its center 0"
        );
        assert_eq!(
            zono_point_contains_truth(&tc, &[nat(1), nat(0), z0, x1]),
            Some(false),
            "a point zonotope at 0 does NOT contain 1"
        );
        // The point-zonotope domain `Zonotope 1 0` is a recognized binder kind.
        let z10 = Expr::apps(
            Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
            [nat(1), nat(0)],
        );
        assert_eq!(binder_kind(&tc, &z10), BinderKind::Zonotope);
    }

    /// NEGATIVE SELF-TEST (the `c4_opacity_catches` precedent for the zonotope
    /// carrier): the C4 engine MUST now REFUTE a hand-built FALSE point-to-point
    /// containment axiom `∀ (z z' : Zono 1 0) (x : NNVec 1), contains z x →
    /// contains z' x` (z = point@0, z' = point@1, x = [0] ⇒ hyp TRUE, concl
    /// FALSE). Before the `Zonotope.contains` decoder this stayed `Opaque`
    /// (uncaught); the decoder closes that blind spot — this is exactly the
    /// false-containment-in-a-DIFFERENT-zonotope shape the three repaired axioms
    /// exhibited.
    #[test]
    fn c4_catches_false_point_to_point_zonotope_containment() {
        let env = zono_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let zono10 = Expr::apps(
            Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
            [nat(1), nat(0)],
        );
        let vec1 = Expr::app(
            Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nat(1),
        );
        let contains = Expr::const_(Name::from_string("NNVerify.Zonotope.contains"), vec![]);
        // `∀ (z z' : Zono 1 0) (x : NNVec 1), contains z x → contains z' x`.
        // de Bruijn (innermost binder = 0): z=3, z'=2, x=1, hyp=0.
        let cz = Expr::apps(
            contains.clone(),
            [nat(1), nat(0), Expr::bvar(2), Expr::bvar(0)],
        );
        let czp = Expr::apps(contains, [nat(1), nat(0), Expr::bvar(2), Expr::bvar(1)]);
        let hyp_to_concl = Expr::pi(BinderInfo::Default, cz, czp);
        let with_x = Expr::pi(BinderInfo::Default, vec1, hyp_to_concl);
        let with_zp = Expr::pi(BinderInfo::Default, zono10.clone(), with_x);
        let bogus = Expr::pi(BinderInfo::Default, zono10, with_zp);

        assert!(
            is_refutable(&tc, &bogus),
            "C4 must refute the FALSE `∀ z z' x, contains z x → contains z' x` \
             (z=point@0, z'=point@1, x=[0])"
        );
        assert_eq!(
            classify_refutation(&tc, &bogus),
            RefutationOutcome::Refutable,
            "the false point-to-point containment must classify Refutable"
        );

        // And the engine must NOT refute the TRUE reflexive containment
        // `∀ (z : Zono 1 0) (x : NNVec 1), contains z x → contains z x`.
        let vec1b = Expr::app(
            Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nat(1),
        );
        let cc = Expr::apps(
            Expr::const_(Name::from_string("NNVerify.Zonotope.contains"), vec![]),
            [nat(1), nat(0), Expr::bvar(2), Expr::bvar(0)],
        );
        let refl = Expr::pi(
            BinderInfo::Default,
            Expr::apps(
                Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
                [nat(1), nat(0)],
            ),
            Expr::pi(
                BinderInfo::Default,
                vec1b,
                Expr::pi(BinderInfo::Default, cc.clone(), cc),
            ),
        );
        assert!(
            !is_refutable(&tc, &refl),
            "C4 must NOT refute the TRUE reflexive `∀ z x, contains z x → contains z x`"
        );
    }

    /// After the honest restatements, NONE of the three repaired Zonotope axioms
    /// is C4-refutable, and the genuinely-true T10 `center_contained` is now C4
    /// EXAMINED (the decoder verifies a point zonotope contains its center). This
    /// pins that the fix removed the refutability the pins recorded.
    #[test]
    fn repaired_zonotope_axioms_are_not_refutable_t10_examined() {
        let env = zono_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        for nm in [
            "NNVerify.Zonotope.sub_minkowski_residual",
            "NNVerify.Zonotope.sub_minkowski_reduce",
            "NNVerify.Zonotope.compress_sound",
            "NNVerify.Zonotope.center_contained",
            "NNVerify.Zonotope.to_ibp_sound",
        ] {
            let ci = env
                .get_const(&Name::from_string(nm))
                .unwrap_or_else(|| panic!("{nm} should be registered"));
            assert_ne!(
                classify_refutation(&tc, &ci.type_),
                RefutationOutcome::Refutable,
                "{nm} must NOT be C4-refutable after the honest restatement"
            );
        }

        // T10 `center_contained` is genuinely true and now EXAMINED (not Opaque):
        // the decoder confirms a point zonotope contains its center.
        let t10 = env
            .get_const(&Name::from_string("NNVerify.Zonotope.center_contained"))
            .expect("T10 registered");
        assert_eq!(
            classify_refutation(&tc, &t10.type_),
            RefutationOutcome::Examined,
            "T10 center_contained must be C4-EXAMINED (the decoder verifies a point \
             zonotope contains its center)"
        );
    }

    /// THE TARGET-REFUTATION GATE. `refute_conjecture` must CATCH a false
    /// `BoolFn`-quantified proof TARGET (the exact class that produced the false
    /// KKL `deriv_level_mass_lower`) and must NOT refute the true variant — so a
    /// false target is killed in milliseconds instead of by hours of honest
    /// prover failure. This is the safeguard the campaign lacked.
    #[test]
    fn refute_conjecture_catches_false_boolfn_target() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init boolean_analysis");
        let tc = TypeChecker::with_mode(&env, env.mode());

        let nat_ty = || Expr::const_(Name::from_string("Nat"), vec![]);
        let boolfn = |n: Expr| {
            Expr::app(
                Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
                n,
            )
        };
        let hcpoint = |n: Expr| {
            Expr::app(
                Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
                n,
            )
        };
        let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        // ∀ (n:Nat) (f:BoolFn n) (x:HCPoint n), Rat.le c (ind (f x))
        //   de Bruijn in the body: x = bvar0, f = bvar1.
        let stmt = |c: Expr| {
            let fx = Expr::app(Expr::bvar(1), Expr::bvar(0));
            let body = Expr::apps(rat_le.clone(), [c, Expr::app(ind.clone(), fx)]);
            Expr::pi(
                BinderInfo::Default,
                nat_ty(),
                Expr::pi(
                    BinderInfo::Default,
                    boolfn(Expr::bvar(0)),
                    Expr::pi(BinderInfo::Default, hcpoint(Expr::bvar(1)), body),
                ),
            )
        };
        let one = rat_mk(of_nat(1), nat(1));
        let zero = rat_mk(of_nat(0), nat(1));

        // FALSE: `1 ≤ ind(f x)` — refuted (ind(false) = 0, via const-false).
        let cex = refute_conjecture(&tc, &stmt(one));
        assert!(
            cex.is_some(),
            "refute_conjecture MUST catch the false BoolFn target `1 ≤ ind(f x)`; got None"
        );

        // TRUE: `0 ≤ ind(f x)` — ind ∈ {0,1} ≥ 0, no counterexample.
        assert_eq!(
            refute_conjecture(&tc, &stmt(zero)),
            None,
            "refute_conjecture MUST NOT refute the true target `0 ≤ ind(f x)`"
        );
    }

    /// The DICTATOR battery is load-bearing, and the counterexample is CLEAR.
    /// `∀ n f, Variance n f ≤ 0` is TRUE for every constant function (`Var = 0`)
    /// and FALSE only for a non-constant one — so ONLY a dictator witness refutes
    /// it. This is the exact shape of the false KKL `Var ≤ C·M_{≥k}` (small for
    /// constants, false for the dictator). The witness must name the dictator and
    /// carry the evaluated verdict.
    #[test]
    fn refute_conjecture_dictator_catches_false_variance() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init boolean_analysis");
        let tc = TypeChecker::with_mode(&env, env.mode());

        let boolfn = Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
            Expr::bvar(0),
        );
        let variance = Expr::const_(Name::from_string("BoolAnalysis.Variance"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let zero = rat_mk(of_nat(0), nat(1));
        // ∀ (n:Nat) (f:BoolFn n), Rat.le (Variance n f) 0  (n = bvar1, f = bvar0)
        let var_f = Expr::apps(variance, [Expr::bvar(1), Expr::bvar(0)]);
        let body = Expr::apps(rat_le, [var_f, zero]);
        let stmt = Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::pi(BinderInfo::Default, boolfn, body),
        );

        let cex = refute_conjecture(&tc, &stmt)
            .expect("the dictator MUST refute the false `∀ n f, Var ≤ 0`");
        assert!(
            cex.contains("dictator"),
            "the witness must name the dictator (constants do not refute this): {cex}"
        );
        assert!(
            cex.contains("FALSE"),
            "the witness must carry the evaluated verdict (`1 ≤ 0` is FALSE): {cex}"
        );
    }
}
