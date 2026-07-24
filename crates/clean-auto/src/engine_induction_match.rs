// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! First-order matching + subterm rewriting for the structural-induction lane.
//!
//! [`crate::engine_induction_rewrite::AutomationEngine::prove_eq_rewrite`] closes
//! an equation by reflexivity, whole-term fact rewriting, and *structural*
//! congruence — but structural congruence only descends when both sides share a
//! `whnf` head. `mul_comm`'s inner residual `succ x * j + x = (x*j + x) + j` has
//! two sides that are both *stuck* `Nat.add`s on **different** operands, so they
//! share no reducible head and congruence cannot reach the sub-position where the
//! induction hypothesis (`succ x * j = x*j + j`) or the accumulator's
//! rearrangement law (`add_right_comm`) applies.
//!
//! This module supplies the missing piece: rewrite a **sub-term** of the goal's
//! left side with a directed fact — concrete (`succ x * j = x*j + j`) *or*
//! `∀`-quantified (`∀ a b c, (a+b)+c = (a+c)+b`, first-order matched at the
//! sub-position) — building a genuine `congrArg` / `congr` proof up the
//! application spine. The caller then discharges the residual and stitches the
//! two with `Eq.trans`.
//!
//! Soundness: this is on the *search* side, not the TCB. Every proof term built
//! here (`congrArg` / `congr` / the specialised fact witness) is re-checked by
//! the caller's `kernel_accepts` gate before it is trusted; a mis-built congruence
//! or a spurious match simply fails that check and yields no proof.

use clean_kernel::{Environment, Expr, ExprKind, Level, LocalContext, Name, TypeChecker};

use crate::engine_induction::{congr_arg, parse_eq, type_checker};

/// A directed rewrite fact: `(witness, equation_type)` where `equation_type` is
/// `Eq T L R` or a `∀`-telescope ending in one.
type Fact = (Expr, Expr);

/// Split a fact type into `(num_binders, lhs_pattern, rhs_pattern)`.
///
/// `∀ x₀ … x_{n-1}, Eq T L R` yields `(n, L, R)` where `L`/`R` retain their de
/// Bruijn variables (`x_{n-1}` is `bvar(n-1)`, the outermost binder). A bare
/// `Eq T L R` yields `(0, L, R)`. `None` when the telescope does not end in `Eq`.
pub(crate) fn split_forall_eq(ty: &Expr) -> Option<(usize, Expr, Expr)> {
    let mut nb = 0usize;
    let mut cur = ty.clone();
    loop {
        let stripped = cur.strip_mdata();
        if let ExprKind::Pi(_, _dom, body) = stripped.kind() {
            nb += 1;
            cur = (**body).clone();
        } else {
            break;
        }
    }
    let (_levels, _t, l, r) = parse_eq(&cur)?;
    Some((nb, l, r))
}

/// Head constant name of a type application (`Nat`, `List`, …), or `None`.
pub(crate) fn carrier_head_name(ty: &Expr) -> Option<String> {
    match ty.strip_mdata().get_app_fn().kind() {
        ExprKind::Const(n, _) => Some(n.to_string()),
        _ => None,
    }
}

/// A unary distribute (`succ_mul`) conjecture: its RHS head is `Nat.add`
/// (constructor-commute candidates have a constructor head instead).
pub(crate) fn is_distribute_conjecture(conj: &Expr) -> bool {
    split_forall_eq(conj)
        .and_then(|(_nb, _l, r)| carrier_head_name(&r))
        .as_deref()
        == Some("Nat.add")
}

/// The `add_right_comm` shape: a 3-binder `∀` whose both sides are `Nat.add`s.
pub(crate) fn is_add_right_comm_shape(ty: &Expr) -> bool {
    match split_forall_eq(ty) {
        Some((3, l, r)) => {
            carrier_head_name(&l).as_deref() == Some("Nat.add")
                && carrier_head_name(&r).as_deref() == Some("Nat.add")
        }
        _ => false,
    }
}

/// The universe `u` with `ty : Sort u`, normalised, or `None`.
fn sort_level_of(tc: &TypeChecker<'_>, ty: &Expr) -> Option<Level> {
    let sort = tc.whnf(&tc.infer_type(ty).ok()?);
    match sort.strip_mdata().kind() {
        ExprKind::Sort(level) => Some(level.normalize()),
        _ => None,
    }
}

/// First-order match of `pat` (whose `bvar(0..nb)` are pattern holes) against
/// `term`, filling `assign[i]` for `bvar(i)`. A repeated hole must match
/// def-eq. Structural elsewhere; declines under binders (our patterns are
/// binder-free, and a spurious decline only forgoes a rewrite).
fn fo_match(
    tc: &TypeChecker<'_>,
    pat: &Expr,
    term: &Expr,
    nb: usize,
    assign: &mut [Option<Expr>],
) -> bool {
    let pat = pat.strip_mdata();
    if let ExprKind::BVar(i) = pat.kind() {
        let idx = *i as usize;
        if idx < nb {
            return match &assign[idx] {
                None => {
                    assign[idx] = Some(term.strip_mdata().clone());
                    true
                }
                Some(prev) => tc.is_def_eq(prev, term),
            };
        }
    }
    let term = term.strip_mdata();
    match (pat.kind(), term.kind()) {
        (ExprKind::BVar(a), ExprKind::BVar(b)) => a == b,
        (ExprKind::FVar(a), ExprKind::FVar(b)) => a == b,
        (ExprKind::Sort(a), ExprKind::Sort(b)) => a.normalize() == b.normalize(),
        (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            fo_match(tc, f1, f2, nb, assign) && fo_match(tc, a1, a2, nb, assign)
        }
        // Structure/class field access: a projection head (`Proj(C, i, inst)` —
        // the form a typeclass operator like `mul` takes) matches head-to-head on
        // the same structure + field index, recursing into the projected term.
        // Without this, a `∀`-fact whose operator is a projection (a projected
        // class law, `∀ x, mul x one = x`) never matches at a sub-position.
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
            n1 == n2 && i1 == i2 && fo_match(tc, e1, e2, nb, assign)
        }
        // Numeric/string literals match head-to-head on equal value. Real Mathlib
        // states a class `1` as `@OfNat.ofNat α (Lit 1) inst` — the `Lit 1` node
        // sits inside the projected `mul_one`/`one_mul` pattern (and the surface
        // goal), so without this arm a `∀`-fact whose operand is a numeric literal
        // (every `… * 1` / `1 * …` law on a real Monoid) never matches at a
        // sub-position and the sub-position rewrite closer misses it.
        (ExprKind::Lit(a), ExprKind::Lit(b)) => a == b,
        _ => false,
    }
}

/// Try to match the whole `term` against `pat_l`, returning the hole assignment
/// (`bvar(i)` ↦ `assign[i]`) when every hole is bound.
fn try_match_whole(
    tc: &TypeChecker<'_>,
    term: &Expr,
    nb: usize,
    pat_l: &Expr,
) -> Option<Vec<Expr>> {
    if nb == 0 {
        return tc.is_def_eq(pat_l, term).then(Vec::new);
    }
    let mut assign: Vec<Option<Expr>> = vec![None; nb];
    if fo_match(tc, pat_l, term, nb, &mut assign) {
        assign.into_iter().collect()
    } else {
        None
    }
}

/// `@congr.{u,v} α β f₁ f₂ a a h_f (Eq.refl a) : f₁ a = f₂ a` — rewrite the
/// **function** side of an application, argument held fixed.
fn mk_congr_fun(tc: &TypeChecker<'_>, f1: &Expr, f2: &Expr, a: &Expr, h_f: &Expr) -> Option<Expr> {
    let alpha = tc.infer_type(a).ok()?;
    let beta = tc.infer_type(&Expr::app(f1.clone(), a.clone())).ok()?;
    let alpha_lvl = sort_level_of(tc, &alpha)?;
    let beta_lvl = sort_level_of(tc, &beta)?;
    let refl_a = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![alpha_lvl.clone()]),
        [alpha.clone(), a.clone()],
    );
    let congr = Expr::const_(Name::from_string("congr"), vec![alpha_lvl, beta_lvl]);
    Some(Expr::apps(
        congr,
        [
            alpha,
            beta,
            f1.clone(),
            f2.clone(),
            a.clone(),
            a.clone(),
            h_f.clone(),
            refl_a,
        ],
    ))
}

/// `@congrArg.{u,v} α β a a' f h : f a = f a'` — rewrite the **argument** side of
/// an application, function held fixed.
fn mk_congr_arg(tc: &TypeChecker<'_>, f: &Expr, a1: &Expr, a2: &Expr, h: &Expr) -> Option<Expr> {
    let alpha = tc.infer_type(a1).ok()?;
    let beta = tc.infer_type(&Expr::app(f.clone(), a1.clone())).ok()?;
    let alpha_lvl = sort_level_of(tc, &alpha)?;
    let beta_lvl = sort_level_of(tc, &beta)?;
    Some(congr_arg(
        &alpha_lvl, &beta_lvl, &alpha, &beta, a1, a2, f, h,
    ))
}

/// Re-fold `Nat.add`'s recursor form back to a surface `Nat.add base major`.
///
/// Congruence peeling a `succ` head `whnf`-reduces the operand, which UNFOLDS
/// `Nat.add` to its recursor `@Nat.rec _ base (fun _ ih => Nat.succ ih) major`.
/// The `∀`-fact rewriter matches *surface* patterns (`(a+b)+c` for
/// `add_right_comm`), which the recursor form defeats. Re-folding restores the
/// surface application; it is definitionally equal to its input, so the caller's
/// `kernel_accepts` gate still validates the assembled proof against the goal.
pub(crate) fn refold_nat_add(e: &Expr) -> Expr {
    let s = e.strip_mdata();
    if let Some((base, major)) = match_nat_add_rec(s) {
        let b = refold_nat_add(&base);
        let m = refold_nat_add(&major);
        return Expr::apps(Expr::const_(Name::from_string("Nat.add"), vec![]), [b, m]);
    }
    match s.kind() {
        ExprKind::App(f, a) => Expr::app(refold_nat_add(f), refold_nat_add(a)),
        _ => e.clone(),
    }
}

/// `@Nat.rec motive base (fun _ ih => Nat.succ ih) major` ⇒ `(base, major)` — the
/// unfolded shape of `Nat.add base major`.
fn match_nat_add_rec(e: &Expr) -> Option<(Expr, Expr)> {
    let head = e.get_app_fn().strip_mdata();
    let ExprKind::Const(n, _) = head.kind() else {
        return None;
    };
    if n.to_string() != "Nat.rec" {
        return None;
    }
    let args = e.get_app_args();
    if args.len() != 4 || !is_succ_step(args[2]) {
        return None;
    }
    Some((args[1].clone(), args[3].clone()))
}

/// `step ≡ fun _ ih => Nat.succ ih` (the `Nat.add` recursor's minor premise).
fn is_succ_step(step: &Expr) -> bool {
    let ExprKind::Lam(_, _, body1) = step.strip_mdata().kind() else {
        return false;
    };
    let ExprKind::Lam(_, _, body2) = body1.strip_mdata().kind() else {
        return false;
    };
    let inner = body2.strip_mdata();
    let ExprKind::App(f, a) = inner.kind() else {
        return false;
    };
    let f_ok =
        matches!(f.strip_mdata().kind(), ExprKind::Const(n, _) if n.to_string() == "Nat.succ");
    let a_ok = matches!(a.strip_mdata().kind(), ExprKind::BVar(0));
    f_ok && a_ok
}

/// Rewrite the leftmost-outermost sub-term of `term` at which `fact` applies,
/// returning `(rewritten_term, proof : term = rewritten_term)`.
///
/// `fact` is `(witness, ty)`; `(nb, pat_l, pat_r) = split_forall_eq(ty)`. At a
/// sub-position def-eq to an instance `σ·pat_l`, the sub-term is replaced by
/// `σ·pat_r` and the proof `σ·witness` is lifted through the surrounding
/// application spine with `congrArg` (argument positions) / `congr` (function
/// positions). `None` when the fact applies nowhere (or makes no progress).
pub(crate) fn rewrite_lhs_with_fact(
    env: &Environment,
    ctx: &LocalContext,
    term: &Expr,
    fact: &Fact,
) -> Option<(Expr, Expr)> {
    let (nb, pat_l, pat_r) = split_forall_eq(&fact.1)?;
    let tc = type_checker(env, ctx);
    rewrite_go(&tc, term, nb, &pat_l, &pat_r, &fact.0)
}

fn rewrite_go(
    tc: &TypeChecker<'_>,
    term: &Expr,
    nb: usize,
    pat_l: &Expr,
    pat_r: &Expr,
    witness: &Expr,
) -> Option<(Expr, Expr)> {
    // Whole-term match: `term ≡ σ·pat_l` ⇒ rewrite to `σ·pat_r`.
    if let Some(assign) = try_match_whole(tc, term, nb, pat_l) {
        let new = if nb == 0 {
            pat_r.clone()
        } else {
            pat_r.instantiate_rev(&assign)
        };
        if !tc.is_def_eq(term, &new) {
            let proof = if nb == 0 {
                witness.clone()
            } else {
                // Apply the witness outermost-binder-first: bvar(nb-1) … bvar(0).
                let args: Vec<Expr> = (0..nb).rev().map(|i| assign[i].clone()).collect();
                Expr::apps(witness.clone(), args)
            };
            return Some((new, proof));
        }
    }

    // Descend the application spine: try the argument first, then the function.
    if let ExprKind::App(f, a) = term.strip_mdata().kind() {
        if let Some((a2, h_a)) = rewrite_go(tc, a, nb, pat_l, pat_r, witness) {
            if let Some(proof) = mk_congr_arg(tc, f, a, &a2, &h_a) {
                return Some((Expr::app((**f).clone(), a2), proof));
            }
        }
        if let Some((f2, h_f)) = rewrite_go(tc, f, nb, pat_l, pat_r, witness) {
            if let Some(proof) = mk_congr_fun(tc, f, &f2, a, &h_f) {
                return Some((Expr::app(f2, (**a).clone()), proof));
            }
        }
    }
    None
}

#[cfg(test)]
mod lit_arm_tests {
    use super::*;
    use clean_kernel::{Environment, LocalContext};

    /// Regression for the real-Mathlib sub-position rewrite. A class `1` is stated
    /// as `@OfNat.ofNat α (Lit 1) inst`, so the projected `mul_one` / `one_mul`
    /// pattern carries a `Lit(Nat 1)` node. `fo_match` must align head-to-head
    /// THROUGH that literal, else a real `Monoid` goal's `… * 1` sub-position never
    /// matches and the sub-position rewrite closer misses it (measured on real
    /// `Mathlib.Algebra.Group.Defs`: `(a*1)*b = a*b` is UNSOLVED without this arm,
    /// SOLVED — kernel-checked — with it).
    #[test]
    fn test_fo_match_aligns_through_nat_literal() {
        let env = Environment::new();
        let ctx = LocalContext::new();
        let tc = type_checker(&env, &ctx);
        // `1` := `ofNat (Lit 1)` — the `OfNat`-wrapped numeric one.
        let one = Expr::app(
            Expr::const_(Name::from_string("ofNat"), vec![]),
            Expr::nat_lit(1),
        );
        let mul = Expr::const_(Name::from_string("mul"), vec![]);
        // pattern `mul (bvar0) one`, term `mul a one` — differ only at the hole.
        let pat = Expr::apps(mul.clone(), [Expr::bvar(0), one.clone()]);
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let term = Expr::apps(mul, [a.clone(), one]);
        let mut assign: Vec<Option<Expr>> = vec![None; 1];
        assert!(
            fo_match(&tc, &pat, &term, 1, &mut assign),
            "fo_match must align a ∀-fact pattern with the term through a Lit(Nat 1)"
        );
        assert_eq!(assign[0], Some(a), "the hole binds to `a`");
    }

    /// The arm compares VALUES: distinct literals must not match (soundness of the
    /// heuristic — a wrong match would still be caught by `kernel_accepts`, but the
    /// matcher should not manufacture spurious rewrites).
    #[test]
    fn test_fo_match_distinct_literals_do_not_match() {
        let env = Environment::new();
        let ctx = LocalContext::new();
        let tc = type_checker(&env, &ctx);
        let mut assign: Vec<Option<Expr>> = Vec::new();
        assert!(!fo_match(
            &tc,
            &Expr::nat_lit(1),
            &Expr::nat_lit(2),
            0,
            &mut assign
        ));
    }
}
