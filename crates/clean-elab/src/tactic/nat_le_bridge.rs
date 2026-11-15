// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constant-size `Nat.le` proofs between literal offsets.
//!
//! The direct Nat reconstruction used to weaken a bound by applying the
//! `Nat.le.step` constructor once per unit of the gap, so the proof term — and
//! every kernel walk over it — was linear in the gap between two literal
//! bounds. Measured 2026-09-30 with `clean check`: `(h : v < 10) : v < 1000 :=
//! by omega` took 0.3 GB, `… < 100000` passed a 4 GB resident cap after 26 s,
//! and `TrustIr/Basic.lean`'s `validChar_lt_two_pow_32` (`v < 0x110000 ⊢ v <
//! 2 ^ 32`) asked for 4,293,853,184 nested applications.
//!
//! Lean's `omega` works over `Int` linear combinations whose literal arithmetic
//! the kernel decides with its GMP-backed Nat extension, never in unary. The
//! terms here follow the same rule. A literal comparison `lo ≤ hi` is
//!
//! ```text
//! @Nat.le_of_ble_eq_true lo hi (@Eq.refl.{1} Bool Bool.true) : Nat.le lo hi
//! ```
//!
//! whose argument type `Nat.ble lo hi = true` the kernel settles by folding
//! `Nat.ble` on the two literals — one comparison, whatever the gap. Every
//! constant is a foundational prelude theorem with the same argument order in
//! Clean's built-in prelude and in Lean's `Init` (`Nat.le_of_ble_eq_true`,
//! `Nat.add_le_add_left`, `Nat.le_add_right`, `Nat.le_trans`, `Nat.lt_irrefl`).
//!
//! These builders only PROPOSE terms. Every caller hands the result to
//! `close_goal`, whose kernel check is what decides: for `lo > hi` the fold
//! gives `false`, the `Eq.refl` argument does not type-check, and the goal
//! stays open.

use clean_kernel::expr::{ExprKind, Literal};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BigNat, Expr};

use super::nat_expr_eval::eval_nat_expr;

fn konst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `Nat.le lo hi` for two literals, as a constant-size term:
/// `@Nat.le_of_ble_eq_true lo hi (@Eq.refl.{1} Bool Bool.true)`.
///
/// REQUIRES: `lo <= hi` for the term to type-check; for `lo > hi` the kernel
/// folds `Nat.ble lo hi` to `false` and rejects the `Eq.refl` argument.
pub(crate) fn nat_le_lits(lo: u64, hi: u64) -> Expr {
    nat_le_lits_big(&BigNat::from(lo), &BigNat::from(hi))
}

/// [`nat_le_lits`] over arbitrary-precision literals.
pub(crate) fn nat_le_lits_big(lo: &BigNat, hi: &BigNat) -> Expr {
    let rfl_true = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [konst("Bool"), konst("Bool.true")],
    );
    Expr::apps(
        konst("Nat.le_of_ble_eq_true"),
        [big_lit(lo), big_lit(hi), rfl_true],
    )
}

/// The literal expression of `n`.
fn big_lit(n: &BigNat) -> Expr {
    Expr::from_kind(ExprKind::Lit(Literal::Nat(n.clone())))
}

/// One right-literal layer of a Nat expression: `base + k` with `k` a closed
/// literal value (`Nat.add` / `HAdd.hAdd` / `Add.add`, the shapes
/// `arith_linarith_nat_direct::nat_split_core_offset` peels), or `Nat.succ
/// base` (`k = 1`).
///
/// Only RIGHT addends: `Nat.add` recurses on its second argument, so `base +
/// k` unfolds to `k` successors of `base` and is def-eq to `Nat.add base k`.
/// A LEFT literal (`k + base`) is not def-eq to `base + k` without
/// commutativity, so it is never peeled here.
fn peel_right_offset(e: &Expr) -> Option<(Expr, u64)> {
    let ExprKind::App(f, arg) = e.kind() else {
        return None;
    };
    if let ExprKind::Const(name, _) = f.kind() {
        if name.to_string() == "Nat.succ" {
            return Some((arg.as_ref().clone(), 1));
        }
    }
    let args = e.get_app_args();
    let ExprKind::Const(op, _) = e.get_app_fn().kind() else {
        return None;
    };
    if args.len() < 2 || !matches!(op.to_string().as_str(), "Nat.add" | "HAdd.hAdd" | "Add.add") {
        return None;
    }
    let k = eval_nat_expr(args[args.len() - 1])?;
    Some((args[args.len() - 2].clone(), k))
}

/// `e` followed by each base reached by peeling one more right-literal layer,
/// paired with the offset peeled so far: `[(e, 0), (b1, k1), (b2, k1 + k2), …]`.
fn right_offset_spine(e: &Expr) -> Vec<(Expr, u64)> {
    let mut spine = vec![(e.clone(), 0u64)];
    let mut cur = e.clone();
    let mut off = 0u64;
    while let Some((base, k)) = peel_right_offset(&cur) {
        let Some(next) = off.checked_add(k) else {
            break;
        };
        off = next;
        spine.push((base.clone(), off));
        cur = base;
    }
    spine
}

/// How `Nat.le p q` is discharged.
enum Between {
    /// `p` and `q` are the same base at the same offset: def-eq, no premise.
    Same,
    /// A constant-size proof of `Nat.le p q`.
    Proof(Expr),
}

/// See [`nat_le_between`].
fn between(p: &Expr, q: &Expr) -> Option<Between> {
    if p == q {
        return Some(Between::Same);
    }
    if let (Some(a), Some(b)) = (eval_nat_expr(p), eval_nat_expr(q)) {
        return (a <= b).then(|| Between::Proof(nat_le_lits(a, b)));
    }
    // The shallowest syntactically common base of the two right-offset
    // spines: the fewer layers peeled, the closer the stated endpoints
    // `base + lo` / `base + hi` are to `p` / `q` syntactically.
    let sp = right_offset_spine(p);
    let sq = right_offset_spine(q);
    let mut best: Option<(usize, &Expr, u64, u64)> = None;
    for (i, (bp, lo)) in sp.iter().enumerate() {
        for (j, (bq, hi)) in sq.iter().enumerate() {
            if bp == bq && best.as_ref().is_none_or(|(depth, ..)| i + j < *depth) {
                best = Some((i + j, bp, *lo, *hi));
            }
        }
    }
    let (_, base, lo, hi) = best?;
    if lo > hi {
        return None;
    }
    if lo == hi {
        return Some(Between::Same);
    }
    if lo == 0 {
        // `Nat.le_add_right base hi : Nat.le base (base + hi)`.
        return Some(Between::Proof(Expr::apps(
            konst("Nat.le_add_right"),
            [base.clone(), Expr::nat_lit(hi)],
        )));
    }
    // `Nat.add_le_add_left lo hi (lo ≤ hi) base : Nat.le (base + lo) (base + hi)`.
    Some(Between::Proof(Expr::apps(
        konst("Nat.add_le_add_left"),
        [
            Expr::nat_lit(lo),
            Expr::nat_lit(hi),
            nat_le_lits(lo, hi),
            base.clone(),
        ],
    )))
}

/// A constant-size proof of `Nat.le p q`, or `None` when the shape is not one
/// this module states.
///
/// - Two closed literal values `a ≤ b`: [`nat_le_lits`].
/// - Otherwise `p` and `q` must reach a syntactically common base by peeling
///   right literal addends (`base + k`, `Nat.succ base`): `p ≡ base + lo`,
///   `q ≡ base + hi`, `lo ≤ hi`. The term is `Nat.le_add_right base hi` (for
///   `lo = 0`) or `Nat.add_le_add_left lo hi (lo ≤ hi) base`, stated over
///   `Nat.add base k`; the caller's spelling (`HAdd.hAdd`, `Nat.succ`, a
///   nested `(base + a) + b`) is def-eq by unfolding right additions only,
///   which the kernel reconciles where the caller's `Nat.le_trans` or goal
///   check meets it. Equal offsets give `Nat.le.refl p`.
///
/// The old `Nat.le.step^(hi - lo)` term asked the kernel to equate
/// `Nat.succ^(hi - lo) p` with `q`; this asks only for `q ≡ base + hi`.
pub(crate) fn nat_le_between(p: &Expr, q: &Expr) -> Option<Expr> {
    match between(p, q)? {
        Between::Same => Some(Expr::app(konst("Nat.le.refl"), p.clone())),
        Between::Proof(proof) => Some(proof),
    }
}

/// `@Nat.le_trans lhs mid rhs h₁ h₂ : Nat.le lhs rhs`.
pub(crate) fn nat_le_trans(lhs: &Expr, mid: &Expr, rhs: &Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        konst("Nat.le_trans"),
        [lhs.clone(), mid.clone(), rhs.clone(), h1, h2],
    )
}

/// Weaken `proof : Nat.le lhs upper` to `Nat.le lhs target`:
/// `Nat.le_trans lhs upper target proof (nat_le_between upper target)`, or
/// `proof` itself when `upper` and `target` are the same base and offset.
///
/// This replaces `Nat.le.step^(target - upper) proof`; the term's size and
/// its kernel cost do not depend on the gap.
pub(crate) fn nat_le_weaken_upper(
    proof: Expr,
    lhs: &Expr,
    upper: &Expr,
    target: &Expr,
) -> Option<Expr> {
    match between(upper, target)? {
        Between::Same => Some(proof),
        Between::Proof(bridge) => Some(nat_le_trans(lhs, upper, target, proof, bridge)),
    }
}

/// `False` from `proof : Nat.le lhs rhs` whose endpoints are the literals
/// `lhs_val > rhs_val`, as a constant-size term:
///
/// ```text
/// Nat.lt_irrefl rhs (Nat.le_trans (rhs+1) lhs rhs (lits: rhs+1 ≤ lhs) proof)
/// ```
///
/// `Nat.le (rhs+1) rhs` is `Nat.lt rhs rhs` by definition. This replaces a
/// `Nat.le_of_succ_le_succ` peel that took `rhs_val` nested applications.
///
/// Returns `None` when `lhs_val <= rhs_val` (nothing to refute).
pub(crate) fn nat_false_of_lits_le(proof: Expr, lhs_val: u64, rhs_val: u64) -> Option<Expr> {
    nat_false_of_lits_le_big(proof, &BigNat::from(lhs_val), &BigNat::from(rhs_val))
}

/// [`nat_false_of_lits_le`] over arbitrary-precision literals.
pub(crate) fn nat_false_of_lits_le_big(
    proof: Expr,
    lhs_val: &BigNat,
    rhs_val: &BigNat,
) -> Option<Expr> {
    if lhs_val <= rhs_val {
        return None;
    }
    let succ_rhs = rhs_val.checked_add_big(&BigNat::from(1));
    let lt_self = nat_le_trans(
        &big_lit(&succ_rhs),
        &big_lit(lhs_val),
        &big_lit(rhs_val),
        nat_le_lits_big(&succ_rhs, lhs_val),
        proof,
    );
    Some(Expr::apps(
        konst("Nat.lt_irrefl"),
        [big_lit(rhs_val), lt_self],
    ))
}

/// Number of nodes in `e` counted as a tree (shared subterms counted at each
/// occurrence) — the size every kernel walk over the term pays.
#[cfg(test)]
pub(crate) fn tree_size(e: &Expr) -> usize {
    use clean_kernel::expr::ExprKind;
    let mut stack: Vec<&Expr> = vec![e];
    let mut n = 0usize;
    while let Some(cur) = stack.pop() {
        n += 1;
        match cur.kind() {
            ExprKind::App(f, a) => stack.extend([f.as_ref(), a.as_ref()]),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                stack.extend([t.as_ref(), b.as_ref()]);
            }
            ExprKind::Let(_, t, v, b, _) => stack.extend([t.as_ref(), v.as_ref(), b.as_ref()]),
            ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => stack.push(x.as_ref()),
            _ => {}
        }
    }
    n
}
