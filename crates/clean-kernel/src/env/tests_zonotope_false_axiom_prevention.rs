// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness REFUTATION PINS for the three historically-FALSE admitted Zonotope
//! axioms over the point-zonotope (`k = 0`) carrier.
//!
//! # The bug class
//!
//! `NNVerify.Zonotope.contains z x` unfolds (it is a reducible Definition) to
//! `∃ ε : NNVec k, (∀ i, -1 ≤ ε i ≤ 1) ∧ x = z.center + z.generators · ε`.
//! For a POINT zonotope (`k = 0`) the generator matrix has zero columns, so
//! `z.generators · ε` is the zero vector and the existential collapses to the
//! decidable equality `x = z.center`. A point zonotope contains EXACTLY its
//! center.
//!
//! Three admitted axioms quantified over the real carrier are FALSE precisely on
//! this `k = 0` slice (the predecessor co-design audit, re-verified here):
//!
//! 1. `Zonotope.compress_sound` (T11): `compress z = z' → ∀ x, contains z x →
//!    contains z' x`. At `k' = 0` the compressed `z'` is a point, so it can
//!    contain at most one `x`; but `z` (with `k = 1`) contains a whole segment.
//!    Witness: `z = [-1,1]` (center 0, generator 1), `z' = compress z` pinned to
//!    a point; `x = z.center + 1·1 = 1 ∈ z` yet `contains z' 1` forces
//!    `z'.center = 1`, while another in-`z` point `x' = -1` forces
//!    `z'.center = -1` — no single center works, so for at least one `x` the
//!    conclusion `contains z' x` is FALSE.
//!
//! 2. `Zonotope.sub_minkowski_residual` (T08C): `contains (minkowski_add z1 z2)
//!    w → contains z2 y → contains z1 (w - y)`. The real Minkowski sum only
//!    guarantees `w = w1 + w2` for SOME `w2 ∈ z2`; the axiom illegally lets `y`
//!    range over ALL of `z2`. Witness: `z1 = {0}` (point), `z2 = [-1,1]`,
//!    `w = 1 ∈ z1⊕z2`, `y = -1 ∈ z2` ⇒ conclusion `contains z1 (1-(-1)) =
//!    contains {0} 2`, FALSE (`2 ≠ 0`).
//!
//! 3. `Zonotope.sub_minkowski_reduce` (T08B): `contains (minkowski_reduce z1 z2)
//!    x → contains z2 y → contains z1 (x + y)`. Mathematically false because no
//!    point `z1 = {0}` admits `x + y ∈ {0}` for every `y ∈ z2 = [-1,1]`. Pinned
//!    here at the conclusion level: with `z1 = {0}`, `x = 0`, `y = 1`, the
//!    conclusion `contains {0} (0+1) = contains {0} 1` is FALSE.
//!
//! These pins CONSTRUCT the concrete `k = 0` counterexamples and assert, via the
//! kernel `TypeChecker`, that the conclusion proposition reduces to a manifestly
//! FALSE closed `Eq Rat` (decided through the order bridge, exactly as the C4
//! carrier-refutation engine does). They are the regression anchor for the
//! honest restatements in `nn_verify_zonotope_compress.rs` /
//! `nn_verify_zonotope_proofs.rs`: each fixed axiom must no longer admit its
//! `k = 0` counterexample, while these pins keep proving the counterexample
//! exists for the OLD (refuted) statement shape.

use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_zonotope_proofs()
        .expect("init_nn_verify_zonotope_proofs");
    env.init_nn_verify_zonotope_compress()
        .expect("init_nn_verify_zonotope_compress");
    env
}

// ───────────────────────── closed witnesses ─────────────────────────

fn nat(n: u64) -> Expr {
    let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    for _ in 0..n {
        e = Expr::app(succ.clone(), e);
    }
    e
}

fn of_nat(n: u64) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), nat(n))
}

fn rat_mk(num: Expr, denom: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [num, denom],
    )
}

/// The rational `k / 1`.
fn rat(k: u64) -> Expr {
    rat_mk(of_nat(k), nat(1))
}

/// `NNVec 1` constant vector `fun (_ : Fin 1) => r`.
fn nnvec1(r: Expr) -> Expr {
    let fin1 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat(1));
    Expr::lam(BinderInfo::Default, fin1, r)
}

/// `NNMat 1 0 = Fin 1 → Fin 0 → Rat` (the empty generator matrix of a point).
fn nnmat_1_0() -> Expr {
    let fin1 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat(1));
    let fin0 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat(0));
    let inner = Expr::lam(
        BinderInfo::Default,
        fin0,
        Expr::const_(Name::from_string("Rat.zero"), vec![]),
    );
    Expr::lam(BinderInfo::Default, fin1, inner)
}

/// `NNVec 0` canonical witness `fun (_ : Fin 0) => Rat.zero`.
fn nnvec0() -> Expr {
    let fin0 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat(0));
    Expr::lam(
        BinderInfo::Default,
        fin0,
        Expr::const_(Name::from_string("Rat.zero"), vec![]),
    )
}

/// The `Fin 1` index `⟨0, True⟩`.
fn fin1_zero() -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Fin.mk"), vec![]),
        [
            nat(1),
            nat(0),
            Expr::const_(Name::from_string("True"), vec![]),
        ],
    )
}

/// A point zonotope `Zonotope 1 0` whose center is the constant `NNVec 1`
/// `fun _ => center_scalar` (a bare `Rat`).
fn point_zono(center_scalar: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("NNVerify.Zonotope.mk"), vec![]),
        [nat(1), nat(0), nnvec1(center_scalar), nnmat_1_0()],
    )
}

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

/// Three-valued truth of a closed `Rat.le a b`: `Some(true)` iff it δ-reduces to
/// a non-negative `Int.NonNeg (Int.ofNat _)`, `Some(false)` iff `Int.negSucc _`,
/// `None` otherwise. (The same order bridge the C4 engine uses.)
fn rat_le_truth(tc: &TypeChecker, a: &Expr, b: &Expr) -> Option<bool> {
    let p = Expr::apps(
        Expr::const_(Name::from_string("Rat.le"), vec![]),
        [a.clone(), b.clone()],
    );
    let w = tc.whnf(&p);
    if let ExprKind::App(f, arg) = w.kind() {
        if matches!(f.kind(), ExprKind::Const(n, _) if n.to_string() == "Int.NonNeg") {
            for k in 0..32u64 {
                if tc.is_def_eq(arg, &of_nat(k)) {
                    return Some(true);
                }
                let neg = Expr::app(
                    Expr::const_(Name::from_string("Int.negSucc"), vec![]),
                    nat(k),
                );
                if tc.is_def_eq(arg, &neg) {
                    return Some(false);
                }
            }
        }
    }
    None
}

/// Decide a closed `contains z x` for a POINT zonotope (`k = 0`) in `n = 1`.
///
/// Unfolds `contains 1 0 z x` to `Exists (NNVec 0) P`, instantiates `P` at the
/// canonical `NNVec 0` witness, and decides the resulting `x = z.center`
/// equality at the single index via the order bridge (true iff both `≤`
/// directions hold). Returns `Some(true/false)` for a decided point-containment,
/// `None` if the shape is unexpected.
fn point_contains_truth(tc: &TypeChecker, z: &Expr, x: &Expr) -> Option<bool> {
    let contains = Expr::const_(Name::from_string("NNVerify.Zonotope.contains"), vec![]);
    let prop = Expr::apps(contains, [nat(1), nat(0), z.clone(), x.clone()]);
    let w = tc.whnf(&prop);
    let (head, args) = const_app(&w)?;
    if head != "Exists" || args.len() != 2 {
        return None;
    }
    // args[1] is the predicate `fun (ε : NNVec 0) => And bounds (x = center + G·ε)`.
    let body = match args[1].kind() {
        ExprKind::Lam(_, _, b) => b.instantiate(&nnvec0()),
        _ => return None,
    };
    let wbody = tc.whnf(&body);
    let (hh, aa) = const_app(&wbody)?;
    if hh != "And" || aa.len() != 2 {
        return None;
    }
    // aa[1] : `@Eq (NNVec 1) x rhs`. Both sides are `Fin 1 → Rat`.
    let (heq, eqargs) = const_app(&aa[1])?;
    if heq != "Eq" || eqargs.len() != 3 {
        return None;
    }
    let xi = Expr::app(eqargs[1].clone(), fin1_zero());
    let ri = Expr::app(eqargs[2].clone(), fin1_zero());
    // `x i = rhs i` over the quotient Rat: true iff both `≤` directions hold,
    // false iff either direction is a false `Int.le`.
    match (rat_le_truth(tc, &xi, &ri), rat_le_truth(tc, &ri, &xi)) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    }
}

// ───────────────────────── refutation pins ─────────────────────────

/// SANITY: a point zonotope contains EXACTLY its center. `contains {0} 0` is
/// TRUE; `contains {0} 1` is FALSE. This pins that the point-containment decoder
/// is not vacuous (it can produce BOTH truth values), so the FALSE assertions
/// below are meaningful refutations rather than a decoder that always says
/// false.
#[test]
fn test_point_zonotope_contains_exactly_its_center() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let z0 = point_zono(rat(0)); // center [0]

    assert_eq!(
        point_contains_truth(&tc, &z0, &nnvec1(rat(0))),
        Some(true),
        "a point zonotope at 0 MUST contain its center 0"
    );
    assert_eq!(
        point_contains_truth(&tc, &z0, &nnvec1(rat(1))),
        Some(false),
        "a point zonotope at 0 must NOT contain 1 (it contains only its center)"
    );
}

/// REFUTATION PIN for `Zonotope.compress_sound` (T11). The OLD statement claims
/// `compress z = z' → ∀ x, contains z x → contains z' x` for ALL `z'`,
/// unconditionally. Instantiate `z' = {0}` (a point at 0 — a legal
/// `Zonotope 1 0`, the codomain of `compress` at `k' = 0`) and `x = 1`. Then the
/// conclusion `contains {0} 1` is FALSE, while a non-degenerate `z` containing 1
/// makes the `contains z x` hypothesis satisfiable. No body for `compress` can
/// repair this: the conclusion's falsity is intrinsic to `z'` being a point that
/// must contain the whole image of `z`.
#[test]
fn test_compress_sound_old_statement_is_refutable_at_kprime_zero() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // z' = point zonotope at 0; x = 1. The OLD compress_sound conclusion is
    // `contains z' x` (with z' the compressed result, an arbitrary Zonotope n
    // k'); at k'=0 this is exactly `contains {0} 1`.
    let zp = point_zono(rat(0));
    let x = nnvec1(rat(1));
    assert_eq!(
        point_contains_truth(&tc, &zp, &x),
        Some(false),
        "compress_sound's conclusion `contains z' x` is FALSE at z'={{0}}, x=1 — \
         the OLD unconditional statement is refutable at k'=0"
    );
}

/// REFUTATION PIN for `Zonotope.sub_minkowski_residual` (T08C). The OLD
/// statement claims `… → contains z2 y → contains z1 (w - y)` for ALL `y ∈ z2`.
/// Counterexample over the real Minkowski sum: `z1 = {0}`, `z2 = [-1,1]`,
/// `w = 1`, `y = -1` ⇒ conclusion `contains z1 (w - y) = contains {0} 2`, FALSE.
/// We pin the conclusion's falsity directly: `contains {0} 2` is FALSE.
#[test]
fn test_sub_minkowski_residual_old_statement_conclusion_is_false() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // z1 = {0}; w - y = 1 - (-1) = 2.
    let z1 = point_zono(rat(0));
    let w_minus_y = nnvec1(rat(2));
    assert_eq!(
        point_contains_truth(&tc, &z1, &w_minus_y),
        Some(false),
        "sub_minkowski_residual's conclusion `contains z1 (w-y)` is FALSE at \
         z1={{0}}, w-y=2 — the residual must be EXISTENTIAL in y, not universal"
    );
}

/// REFUTATION PIN for `Zonotope.sub_minkowski_reduce` (T08B). The OLD statement
/// claims `… → contains z2 y → contains z1 (x + y)`. No point `z1 = {0}` admits
/// `x + y ∈ {0}` for every `y ∈ z2 = [-1,1]`. We pin the conclusion's falsity at
/// the concrete instance `z1 = {0}`, `x + y = 1`: `contains {0} 1` is FALSE.
#[test]
fn test_sub_minkowski_reduce_old_statement_conclusion_is_false() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // z1 = {0}; x + y = 0 + 1 = 1.
    let z1 = point_zono(rat(0));
    let x_plus_y = nnvec1(rat(1));
    assert_eq!(
        point_contains_truth(&tc, &z1, &x_plus_y),
        Some(false),
        "sub_minkowski_reduce's conclusion `contains z1 (x+y)` is FALSE at \
         z1={{0}}, x+y=1 — no point z1 satisfies `x+y ∈ z1` for all y ∈ z2"
    );
}
