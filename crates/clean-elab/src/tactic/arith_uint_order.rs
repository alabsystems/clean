// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pure-order reconstruction for fixed-width unsigned-integer carriers.
//!
//! The fixed-width unsigned integer carriers (`UInt8`/`UInt16`/`UInt32`/
//! `UInt64`/`USize`) define their order **definitionally** as the corresponding
//! `Nat` order on the `.toNat` projection:
//!
//! ```text
//! UInt64.le a b  ≡  Nat.le (UInt64.toNat a) (UInt64.toNat b)
//! UInt64.lt a b  ≡  Nat.lt (UInt64.toNat a) (UInt64.toNat b)
//! ```
//!
//! and `@LE.le UInt64 instLEUInt64 a b` δ-reduces through the instance to
//! `UInt64.le a b`, hence to the `Nat` statement above. `UInt64.toNat` is an
//! injective embedding into `ℕ` that **preserves order**, so a `Nat`-level proof
//! of `Nat.le (toNat a) (toNat b)` is, up to kernel def-eq, a proof of the
//! original `UInt64` goal. The final term is always re-checked by
//! `state.close_goal`, which is a full kernel def-eq check — this module only
//! proposes a candidate.
//!
//! **Soundness boundary — PURE ORDER ONLY.** `UInt64` *arithmetic* wraps at
//! `2^64` (`a + 1 > a` is false at `u64::MAX`), so the linear `Nat` model is
//! UNSOUND for any atom containing `+`/`-`/`*`. This lane therefore fires only
//! when every comparison side is a *bare order atom* — an `FVar` or a numeric
//! literal — and refuses (returns `None`, i.e. fails closed) the moment an atom
//! carries any arithmetic. The reduction to `Nat` then treats each
//! `carrier.toNat <side>` as an OPAQUE `Nat` atom, so no arithmetic identity is
//! ever assumed about it: the only facts derived are pure-order facts among
//! opaque naturals, which lift back to the wrapping carrier without loss. The
//! `close_goal` re-check is the final soundness gate regardless.

use clean_kernel::level::Level;
use clean_kernel::{Expr, ExprKind, Name};

use super::Goal;

/// The unsigned-integer carriers whose `LE`/`LT` unfold definitionally to
/// `Nat.le`/`Nat.lt` on the order-preserving `.toNat` embedding.
const UINT_ORDER_CARRIERS: &[&str] = &["UInt8", "UInt16", "UInt32", "UInt64", "USize"];

/// A recognized order relation over a `UInt` carrier.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Rel {
    Le,
    Lt,
    Eq,
}

/// `true` when `carrier` is a `Const` naming an allow-listed unsigned-integer
/// carrier whose order is `toNat`-definitional.
fn carrier_name(carrier: &Expr) -> Option<String> {
    if let ExprKind::Const(n, _) = carrier.kind() {
        let s = n.to_string();
        if UINT_ORDER_CARRIERS.contains(&s.as_str()) {
            return Some(s);
        }
    }
    None
}

/// A bare *pure-order* atom: an `FVar` or a numeric literal / constant. Anything
/// carrying arithmetic (an `HAdd`/`HSub`/`HMul`/… application, a successor, …)
/// is rejected, which is what fails the wrapping-arithmetic fragment closed.
///
/// This is a POSITIVE allow-list: only shapes known to be arithmetic-free pass.
fn is_pure_order_atom(e: &Expr, carrier: &str) -> bool {
    match e.kind() {
        // A free variable is the canonical pure-order atom.
        ExprKind::FVar(_) => true,
        // A raw literal (e.g. a `Nat` literal that a numeral lowered to).
        ExprKind::Lit(_) => true,
        // A nullary constant (`carrier.zero`, a `def`-bound value, …) — opaque
        // and arithmetic-free.
        ExprKind::Const(_, _) => true,
        // A numeric literal in typeclass form: `@OfNat.ofNat carrier n inst`, or
        // the direct `carrier.ofNat n`. No other application head is admitted,
        // so every arithmetic operator falls through to `false`.
        ExprKind::App(..) => {
            let head = e.get_app_fn();
            if let ExprKind::Const(n, _) = head.kind() {
                let s = n.to_string();
                s == "OfNat.ofNat" || s == format!("{carrier}.ofNat")
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Parse `ty` as an order comparison over an allow-listed `UInt` carrier with
/// pure-order sides. Returns `(rel, carrier_name, lhs, rhs)`.
fn parse_uint_comparison(ty: &Expr) -> Option<(Rel, String, Expr, Expr)> {
    if let Some((alpha, x, y)) = super::match_le(ty) {
        let c = carrier_name(&alpha)?;
        if is_pure_order_atom(&x, &c) && is_pure_order_atom(&y, &c) {
            return Some((Rel::Le, c, x, y));
        }
        return None;
    }
    if let Some((alpha, x, y)) = super::match_lt(ty) {
        let c = carrier_name(&alpha)?;
        if is_pure_order_atom(&x, &c) && is_pure_order_atom(&y, &c) {
            return Some((Rel::Lt, c, x, y));
        }
        return None;
    }
    if let Some((alpha, x, y)) = super::match_eq(ty) {
        let c = carrier_name(&alpha)?;
        if is_pure_order_atom(&x, &c) && is_pure_order_atom(&y, &c) {
            return Some((Rel::Eq, c, x, y));
        }
        return None;
    }
    None
}

/// `carrier.toNat e` — the opaque `Nat` image of a `UInt` side.
fn nat_atom(to_nat: &str, e: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string(to_nat), vec![]), e.clone())
}

/// `Nat.le a b` (2-arg direct head; `normalize_nat_comparison` accepts it).
fn nat_le(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Nat.le"), vec![]), [a, b])
}

/// `Nat.lt a b` (2-arg direct head).
fn nat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Nat.lt"), vec![]), [a, b])
}

/// `@Eq Nat a b`.
fn nat_eq(a: Expr, b: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat, a, b],
    )
}

/// Build the `Nat` image of a parsed comparison over `to_nat`'s carrier.
fn nat_image(rel: Rel, to_nat: &str, x: &Expr, y: &Expr) -> Expr {
    let nx = nat_atom(to_nat, x);
    let ny = nat_atom(to_nat, y);
    match rel {
        Rel::Le => nat_le(nx, ny),
        Rel::Lt => nat_lt(nx, ny),
        Rel::Eq => nat_eq(nx, ny),
    }
}

/// `@Iff.mp a b iff ha : b`.
fn iff_mp(a_prop: Expr, b_prop: Expr, iff: Expr, ha: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Iff.mp"), vec![]),
        [a_prop, b_prop, iff, ha],
    )
}

/// From a negated-order hypothesis over a `UInt` carrier, derive the equivalent
/// positive `Nat` hypothesis (proof, declared type) via the constructive
/// `Nat.not_lt` / `Nat.not_le` bridges:
///
/// * `h : ¬(x < y)`  →  `Iff.mp (Nat.not_lt X Y) h : Nat.le Y X`
/// * `h : ¬(x ≤ y)`  →  `Iff.mp (Nat.not_le X Y) h : Nat.lt Y X`
///
/// where `X = carrier.toNat x`, `Y = carrier.toNat y`. `h`'s real type
/// `¬(LT.lt carrier inst x y)` is def-eq to the `Nat` `Iff` LHS, so `Iff.mp`
/// type-checks; the derived proof's type is def-eq to the declared `Nat` type.
fn derive_from_negation(
    ty: &Expr,
    proof: &Expr,
    to_nat: &str,
    goal_carrier: &str,
) -> Option<(Expr, Expr)> {
    let inner = super::match_not(ty)?;
    // ¬(x < y) → Nat.le Y X, via `Nat.not_lt : ¬(a < b) ↔ b ≤ a`.
    if let Some((alpha, x, y)) = super::match_lt(&inner) {
        let c = carrier_name(&alpha)?;
        if c != goal_carrier || !is_pure_order_atom(&x, &c) || !is_pure_order_atom(&y, &c) {
            return None;
        }
        let (nx, ny) = (nat_atom(to_nat, &x), nat_atom(to_nat, &y));
        let a_prop =
            super::arith_push_neg::make_not(&super::tc_app::nat_lt_tc(nx.clone(), ny.clone()));
        let b_prop = super::tc_app::nat_le_tc(ny.clone(), nx.clone());
        let iff = Expr::apps(
            Expr::const_(Name::from_string("Nat.not_lt"), vec![]),
            [nx.clone(), ny.clone()],
        );
        let derived = iff_mp(a_prop, b_prop, iff, proof.clone());
        return Some((derived, nat_le(ny, nx)));
    }
    // ¬(x ≤ y) → Nat.lt Y X, via `Nat.not_le : ¬(a ≤ b) ↔ b < a`.
    if let Some((alpha, x, y)) = super::match_le(&inner) {
        let c = carrier_name(&alpha)?;
        if c != goal_carrier || !is_pure_order_atom(&x, &c) || !is_pure_order_atom(&y, &c) {
            return None;
        }
        let (nx, ny) = (nat_atom(to_nat, &x), nat_atom(to_nat, &y));
        let a_prop =
            super::arith_push_neg::make_not(&super::tc_app::nat_le_tc(nx.clone(), ny.clone()));
        let b_prop = super::tc_app::nat_lt_tc(ny.clone(), nx.clone());
        let iff = Expr::apps(
            Expr::const_(Name::from_string("Nat.not_le"), vec![]),
            [nx.clone(), ny.clone()],
        );
        let derived = iff_mp(a_prop, b_prop, iff, proof.clone());
        return Some((derived, nat_lt(ny, nx)));
    }
    None
}

/// Attempt a kernel-checkable proof of a PURE-ORDER goal over a fixed-width
/// unsigned-integer carrier by reducing it to the corresponding `Nat` order
/// problem on the `.toNat` embedding and reusing the `Nat` direct prover.
///
/// Returns `Some(proof)` (a candidate the caller MUST close via `close_goal`,
/// which kernel-re-checks it against the *original* goal by def-eq) or `None`
/// when the goal is not a supported pure-order `UInt` shape, when any atom
/// carries arithmetic (fail closed — the wrapping fragment is out of scope), or
/// when the `Nat` prover cannot discharge the reduced goal.
///
/// SOUNDNESS: every `carrier.toNat <side>` is an opaque `Nat` atom, so the `Nat`
/// prover derives only pure-order facts among naturals; those lift to the
/// carrier without wraparound reasoning. Arithmetic atoms are rejected up front,
/// and a false goal yields `None` from the `Nat` prover. No false goal can be
/// closed here — and `close_goal` is the final kernel gate regardless.
pub(crate) fn try_prove_uint_order(goal: &Goal) -> Option<Expr> {
    let (rel, carrier, x, y) = parse_uint_comparison(&goal.target)?;
    let to_nat = format!("{carrier}.toNat");

    let shadow_target = nat_image(rel, &to_nat, &x, &y);

    let mut shadow_hyps: Vec<(Expr, Expr)> = Vec::new();
    for d in &goal.local_ctx {
        let proof = Expr::fvar(d.fvar);
        // Positive order hypothesis over the SAME carrier: forward its `Nat`
        // image (its real type is def-eq, so the `FVar` proof stays valid).
        if let Some((h_rel, h_carrier, hx, hy)) = parse_uint_comparison(&d.ty) {
            if h_carrier == carrier {
                shadow_hyps.push((proof, nat_image(h_rel, &to_nat, &hx, &hy)));
                continue;
            }
        }
        // Negated order hypothesis: derive the positive `Nat` equivalent.
        if let Some((derived_proof, derived_ty)) =
            derive_from_negation(&d.ty, &proof, &to_nat, &carrier)
        {
            shadow_hyps.push((derived_proof, derived_ty));
        }
    }

    super::arith_linarith_nat_direct::try_prove_nat_inequality_direct_with_hyps(
        &shadow_target,
        &shadow_hyps,
    )
}
