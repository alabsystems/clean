//! Ordered rewriting for PERMUTATIVE simp lemmas (B7, Lean parity).
//!
//! A permutative lemma is one whose LHS and RHS are the same term up to a
//! bijective renaming of its pattern variables — `Nat.add_comm :
//! ?a + ?b = ?b + ?a` is the canonical case. Fired unconditionally, such a
//! lemma matches its own output: the main simp loop then flips every `+`
//! node on every pass until `max_steps`, and a goal like
//! `r.size + l.size = l.size + r.size` (battery row `data_tree-mirror-size`,
//! node arm after the mirror/size equations and both IHs) stays open even
//! though Lean 4 closes the same script.
//!
//! Lean's simp marks such lemmas `perm` at registration
//! (`Lean/Meta/Tactic/Simp/SimpTheorems.lean`, `isPerm`) and applies them
//! only when the rewrite makes the term strictly SMALLER in a fixed total
//! order (ordered rewriting, `Lean/Meta/Tactic/Simp/Rewrite.lean`). That
//! both terminates and canonicalizes: the two sides of an equality goal
//! converge on the SAME ordering-minimal operand order, and the reflexivity
//! closer (or the def-eq `eq_self` rewrite) closes the goal.
//!
//! This module supplies the two ingredients, applied at the single rewrite
//! choke point (`try_apply_simp_lemma_with_proof` — which compares the
//! instantiated RHS against the instantiated LHS PATTERN, not against the
//! goal subterm; see the guard's comment there for why goal-side spelling
//! must stay out of the comparison):
//!
//! * [`is_permutative_pair`] — the `isPerm` analogue over Clean's stored
//!   pattern representation (loose `BVar`s as pattern variables).
//! * [`expr_order_lt`] — a strict, deterministic total order on `Expr`.
//!   WHICH total order is immaterial for soundness (every accepted rewrite
//!   still carries its kernel-checked proof); it only has to be strict and
//!   stable so that ordered rewriting terminates and canonicalizes.
//!
//! Fail-closed in both directions: a lemma this detector cannot prove
//! permutative keeps today's unconditional behaviour (no new rewrites are
//! ever enabled), and a permutative rewrite that does not strictly decrease
//! the order is simply refused — simp reports the goal honestly unsolved
//! rather than oscillating.

use std::cmp::Ordering;

use clean_kernel::{Expr, ExprKind};

/// Is `lhs = rhs` a permutative rewrite rule — the same term up to a
/// bijective renaming of pattern variables, with at least one variable
/// actually moved?
///
/// Pattern variables are the LOOSE `BVar`s of the stored lemma pattern
/// (indices `>= depth` during the walk); locally-bound `BVar`s under a
/// binder inside the pattern must match exactly. The "at least one moved"
/// requirement keeps byte-identical LHS/RHS pairs (an `a = a` restatement)
/// out: those are inert anyway (`new_expr != result.expr` filters them),
/// and calling them permutative would be a lie.
///
/// ENSURES: `true` only if every node outside pattern-variable positions is
/// structurally identical and the variable map is injective (hence, with
/// RHS vars ⊆ LHS vars as every well-formed rewrite has, bijective).
pub(crate) fn is_permutative_pair(lhs: &Expr, rhs: &Expr) -> bool {
    let mut map: Vec<(u32, u32)> = Vec::new();
    perm_eq(lhs, rhs, 0, &mut map) && map.iter().any(|&(i, j)| i != j)
}

/// Lockstep structural walk for [`is_permutative_pair`].
///
/// `depth` counts binders entered inside the pattern itself; `map` collects
/// the (lhs-var → rhs-var) renaming, refusing non-injective entries.
fn perm_eq(a: &Expr, b: &Expr, depth: u32, map: &mut Vec<(u32, u32)>) -> bool {
    let (a, b) = (a.strip_mdata(), b.strip_mdata());
    match (a.kind(), b.kind()) {
        (ExprKind::BVar(i), ExprKind::BVar(j)) => {
            if *i < depth || *j < depth {
                // Locally bound inside the pattern: must be the SAME binder.
                return i == j && *i < depth;
            }
            let (pi, pj) = (*i - depth, *j - depth);
            if let Some(&(_, mapped)) = map.iter().find(|&&(x, _)| x == pi) {
                return mapped == pj;
            }
            if map.iter().any(|&(_, y)| y == pj) {
                return false; // pj already the image of a different lhs var
            }
            map.push((pi, pj));
            true
        }
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            perm_eq(f1, f2, depth, map) && perm_eq(a1, a2, depth, map)
        }
        (ExprKind::Lam(_, d1, b1), ExprKind::Lam(_, d2, b2))
        | (ExprKind::Pi(_, d1, b1), ExprKind::Pi(_, d2, b2)) => {
            perm_eq(d1, d2, depth, map) && perm_eq(b1, b2, depth + 1, map)
        }
        (ExprKind::Let(_, t1, v1, b1, _), ExprKind::Let(_, t2, v2, b2, _)) => {
            perm_eq(t1, t2, depth, map)
                && perm_eq(v1, v2, depth, map)
                && perm_eq(b1, b2, depth + 1, map)
        }
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
            n1 == n2 && i1 == i2 && perm_eq(e1, e2, depth, map)
        }
        // Every other kind is a leaf w.r.t. pattern variables (Const, Sort,
        // Lit, FVar, and the mode-extension nodes): exact equality or bust.
        // A BVar facing a non-BVar also lands here and correctly fails.
        _ => a == b,
    }
}

/// Strict total order used for ordered rewriting: `a` strictly before `b`?
#[must_use]
pub(crate) fn expr_order_lt(a: &Expr, b: &Expr) -> bool {
    expr_cmp(a, b) == Ordering::Less
}

/// Rank for the kind-first comparison. The specific rank assignment is
/// arbitrary — the guard compares two instantiations of the SAME lemma
/// pattern, which share every non-operand node — but it must stay fixed:
/// changing it silently changes which operand order simp canonicalizes to.
fn kind_rank(k: &ExprKind) -> u8 {
    match k {
        ExprKind::BVar(_) => 0,
        ExprKind::FVar(_) => 1,
        ExprKind::Sort(_) => 2,
        ExprKind::Const(_, _) => 3,
        ExprKind::Lit(_) => 4,
        ExprKind::Proj(_, _, _) => 5,
        ExprKind::App(_, _) => 6,
        ExprKind::Lam(_, _, _) => 7,
        ExprKind::Pi(_, _, _) => 8,
        ExprKind::Let(_, _, _, _, _) => 9,
        // MData is stripped before ranking; the mode-extension kinds
        // (SProp/Squash/Cubical*) share one rank and fall back to the
        // Debug-string comparison, which is total and deterministic.
        _ => 10,
    }
}

/// Deterministic total order on expressions. Kind rank first, then
/// components; `MData` is transparent (stripped on both sides, matching how
/// type checking treats it). Exotic same-rank pairs and non-`Ord` leaf
/// payloads (levels, literals) compare via their `Debug` rendering — the
/// order only has to be total and stable, not semantic.
fn expr_cmp(a: &Expr, b: &Expr) -> Ordering {
    let (a, b) = (a.strip_mdata(), b.strip_mdata());
    let (ra, rb) = (kind_rank(a.kind()), kind_rank(b.kind()));
    if ra != rb {
        return ra.cmp(&rb);
    }
    match (a.kind(), b.kind()) {
        (ExprKind::BVar(i), ExprKind::BVar(j)) => i.cmp(j),
        (ExprKind::FVar(x), ExprKind::FVar(y)) => x.cmp(y),
        (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1
            .cmp(n2)
            .then_with(|| format!("{l1:?}").cmp(&format!("{l2:?}"))),
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            expr_cmp(f1, f2).then_with(|| expr_cmp(a1, a2))
        }
        (ExprKind::Lam(_, d1, b1), ExprKind::Lam(_, d2, b2))
        | (ExprKind::Pi(_, d1, b1), ExprKind::Pi(_, d2, b2)) => {
            expr_cmp(d1, d2).then_with(|| expr_cmp(b1, b2))
        }
        (ExprKind::Let(_, t1, v1, b1, _), ExprKind::Let(_, t2, v2, b2, _)) => expr_cmp(t1, t2)
            .then_with(|| expr_cmp(v1, v2))
            .then_with(|| expr_cmp(b1, b2)),
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => n1
            .cmp(n2)
            .then_with(|| i1.cmp(i2))
            .then_with(|| expr_cmp(e1, e2)),
        _ => format!("{a:?}").cmp(&format!("{b:?}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::name::Name;

    fn nat() -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    fn add(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Nat.add"), vec![]), [a, b])
    }

    #[test]
    fn test_is_permutative_pair_add_comm_shape_detected() {
        // ?a + ?b = ?b + ?a (loose BVars 1, 0 as the two pattern vars)
        let lhs = add(Expr::bvar(1), Expr::bvar(0));
        let rhs = add(Expr::bvar(0), Expr::bvar(1));
        assert!(
            is_permutative_pair(&lhs, &rhs),
            "add_comm shape must be detected as permutative"
        );
    }

    #[test]
    fn test_is_permutative_pair_zero_add_shape_not_permutative() {
        // 0 + ?n = ?n — structure differs, NOT permutative.
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let lhs = add(zero, Expr::bvar(0));
        let rhs = Expr::bvar(0);
        assert!(
            !is_permutative_pair(&lhs, &rhs),
            "a collapsing lemma must not be flagged permutative"
        );
    }

    #[test]
    fn test_is_permutative_pair_identity_not_permutative() {
        // ?a + ?b = ?a + ?b — identical, no variable moved.
        let lhs = add(Expr::bvar(1), Expr::bvar(0));
        assert!(
            !is_permutative_pair(&lhs, &lhs.clone()),
            "an identity pair moves no variable and is not permutative"
        );
    }

    #[test]
    fn test_is_permutative_pair_non_injective_refused() {
        // ?a + ?b = ?a + ?a — two lhs vars mapping onto one rhs var.
        let lhs = add(Expr::bvar(1), Expr::bvar(0));
        let rhs = add(Expr::bvar(1), Expr::bvar(1));
        assert!(
            !is_permutative_pair(&lhs, &rhs),
            "a non-injective variable map must be refused"
        );
    }

    #[test]
    fn test_expr_order_lt_strict_and_total_on_samples() {
        let x = add(nat(), Expr::bvar(0));
        let y = add(Expr::bvar(0), nat());
        assert!(!expr_order_lt(&x, &x), "irreflexive");
        assert_ne!(
            expr_order_lt(&x, &y),
            expr_order_lt(&y, &x),
            "exactly one direction holds for distinct terms"
        );
    }
}
