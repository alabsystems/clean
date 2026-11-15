// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat-specific helpers for the Farkas-with-goal reconstruction in
//! [`super::arith_linarith_farkas_goal`].
//!
//! Split out of that module on 2026-09-21, when merging
//! `origin/integrate/2026-09-20` grew it from 750 to 1020 lines and crossed the
//! `files_over_1000` organizational threshold that `scripts/paragon_ratchet.sh`
//! ratchets shrink-only. The cut is the module's own seam rather than an
//! arbitrary line count: everything here is Nat *expression* and *accumulator*
//! shaping -- normalizing a goal to `Nat.le`, building an accumulator from a
//! hypothesis, scaling and cancelling one, measuring the Farkas gap, and the
//! small `Expr` constructors -- while the Farkas search itself (the multiplier
//! assignments, the `False` construction and the orientation loop) stays put.
//!
//! The interface across the seam is narrow and one-directional by design: this
//! module exports eleven `pub(super)` helpers upward and takes exactly one type
//! back, [`super::arith_linarith_farkas_goal::NegGoalFact`], which it produces
//! in `negated_goal_fact_classical`.

use clean_kernel::expr::{BinderInfo, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

use super::arith_linarith_chain::{definitional_le_endpoints, detect_sort, extract_le_args_full};
use super::arith_linarith_farkas_goal::NegGoalFact;
use super::arith_linarith_proof::find_hyp_type;
use super::arith_linarith_scale::SortLeAcc;
use super::Goal;
use clean_auto::arith_proof::ArithSort;

/// Build a Nat accumulator from a hypothesis `fvar`: the oriented `Nat.le` it
/// proves by definition.
///
/// - `a ≤ b` → endpoints `(a, b)`; `a ≥ b` → `(b, a)`.
/// - `a < b` → `(Nat.succ a, b)` (`Nat.lt a b := Nat.le (succ a) b`);
///   `a > b` → `(Nat.succ b, a)`.
///
/// The orientation comes from [`extract_le_args_full`] and the strict reading
/// from [`definitional_le_endpoints`], the same two the other linarith
/// builders use; the proof is `fvar` itself, whose type is def-eq to the
/// declared `Nat.le`, so the kernel accepts it.
///
/// Returns `None` for non-Nat hypotheses (the builder is Nat-only) or unparsable
/// comparison heads.
fn nat_hyp_acc(goal: &Goal, fvar: FVarId) -> Option<SortLeAcc> {
    let h_ty = find_hyp_type(goal, fvar)?;
    let (alpha, op, a, b) = extract_le_args_full(&h_ty)?;
    if detect_sort(&alpha)? != ArithSort::Nat {
        return None;
    }
    let (lhs, rhs) = definitional_le_endpoints(ArithSort::Nat, op, &a, &b)?;
    SortLeAcc::nat_from_parts(lhs, rhs, Expr::fvar(fvar))
}

/// Candidate `Nat.le` orientations a hypothesis can contribute to the Farkas
/// sum. Inequalities give exactly one oriented fact; a Nat **equality**
/// `h : a = b` gives BOTH `a ≤ b` and `b ≤ a` (each provable from `h`), and the
/// residual solver picks whichever orientation cancels the goal/atoms.
///
/// The `Eq` orientations are built by transporting `Nat.le.refl a` along `h`:
/// - `a ≤ b`: `@Eq.ndrec Nat a (fun z => Nat.le a z) (Nat.le.refl a) b h`.
/// - `b ≤ a`: `@Eq.ndrec Nat a (fun z => Nat.le z a) (Nat.le.refl a) b h`.
/// Both use only `Nat.le.refl` and `Eq.ndrec` (constructive prelude); the kernel
/// re-check of the final term is the soundness gate.
pub(super) fn nat_hyp_acc_candidates(goal: &Goal, fvar: FVarId) -> Vec<SortLeAcc> {
    if let Some(acc) = nat_hyp_acc(goal, fvar) {
        return vec![acc];
    }
    // Equality hypothesis path.
    let Some(h_ty) = find_hyp_type(goal, fvar) else {
        return Vec::new();
    };
    let head = h_ty.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return Vec::new();
    };
    if !name.to_string().contains("Eq") {
        return Vec::new();
    }
    let args = h_ty.get_app_args();
    // `@Eq Nat a b` has args [Nat, a, b].
    if args.len() != 3 || !is_nat_const(args[0]) {
        return Vec::new();
    }
    let a = args[1].clone();
    let b = args[2].clone();
    let h = Expr::fvar(fvar);
    let mut out = Vec::new();
    // a ≤ b
    if let Some(acc) = SortLeAcc::nat_from_parts(
        a.clone(),
        b.clone(),
        eq_to_le_le(&a, &b, &h, EqLeDir::Forward),
    ) {
        out.push(acc);
    }
    // b ≤ a
    if let Some(acc) = SortLeAcc::nat_from_parts(
        b.clone(),
        a.clone(),
        eq_to_le_le(&a, &b, &h, EqLeDir::Backward),
    ) {
        out.push(acc);
    }
    out
}

#[derive(Clone, Copy)]
enum EqLeDir {
    /// `h : a = b` ⟹ `Nat.le a b`.
    Forward,
    /// `h : a = b` ⟹ `Nat.le b a`.
    Backward,
}

/// Build a `Nat.le` proof from a Nat equality `h : a = b` by transporting
/// `Nat.le.refl a` along `h`.
fn eq_to_le_le(a: &Expr, b: &Expr, h: &Expr, dir: EqLeDir) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
    let le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
    // refl : Nat.le a a
    let refl = Expr::app(le_refl, a.clone());
    // motive : fun z => Nat.le a z   (Forward)  or  fun z => Nat.le z a (Backward)
    let motive = match dir {
        EqLeDir::Forward => {
            let body = Expr::apps(nat_le, [a.clone(), Expr::bvar(0)]);
            Expr::lam(BinderInfo::Default, nat_ty.clone(), body)
        }
        EqLeDir::Backward => {
            let body = Expr::apps(nat_le, [Expr::bvar(0), a.clone()]);
            Expr::lam(BinderInfo::Default, nat_ty.clone(), body)
        }
    };
    // @Eq.ndrec.{0,1} Nat a motive refl b h : motive[b]
    let eq_ndrec = Expr::const_(
        Name::from_string("Eq.ndrec"),
        vec![Level::zero(), Level::succ(Level::zero())],
    );
    Expr::apps(
        eq_ndrec,
        [nat_ty, a.clone(), motive, refl, b.clone(), h.clone()],
    )
}

fn is_nat_const(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat")
}

/// Scale a Nat accumulator by `coeff ≥ 1` via repeated self-addition
/// (`Nat.add_le_add`). `coeff == 1` returns it unchanged.
pub(super) fn scale_nat_acc(base: SortLeAcc, coeff: i128) -> Option<SortLeAcc> {
    if coeff < 1 {
        return None;
    }
    if coeff == 1 {
        return Some(base);
    }
    // Rebuild `base` `coeff` times and fold; `SortLeAcc` is not `Clone`, so
    // capture its parts and reconstruct each summand.
    let SortLeAcc {
        lhs, rhs, proof, ..
    } = base;
    let mut acc = SortLeAcc::nat_from_parts(lhs.clone(), rhs.clone(), proof.clone())?;
    for _ in 1..coeff {
        let next = SortLeAcc::nat_from_parts(lhs.clone(), rhs.clone(), proof.clone())?;
        acc = acc.combine(next)?;
    }
    Some(acc)
}

/// Fold the implicit Nat non-negativity facts `0 ≤ v` into `acc` so every atom
/// with a *positive* residual coefficient is cancelled, leaving a pure constant
/// gap.
///
/// `acc : Nat.le L R` summarizes the hyp+neg_goal combination. Its residual is
/// `d = linearForm(L) − linearForm(R)`. The genuine UNSAT witness has, for every
/// atom `v`, a residual coefficient `d_v ≥ 0` (the negative direction can never
/// be cancelled by a `0 ≤ v` fact, which only *adds* `v` to the right side):
/// folding `d_v` copies of `0 ≤ v` adds `d_v·v` to `R`, zeroing the atom. If any
/// atom has `d_v < 0`, this is NOT a `hyp + nonneg` refutation — return `None`
/// and fail closed (the caller falls through).
///
/// Each `0 ≤ v` is `Nat.zero_le v : Nat.le 0 v`. The fold uses the same
/// `SortLeAcc::combine` (`Nat.add_le_add`); the assembled term is kernel-checked
/// by `close_goal`, so a wrong cancellation cannot be accepted.
///
/// Soundness: `0 ≤ v` holds for every Nat `v`. We only ever add it on the LHS as
/// a `0` and on the RHS as `v` (never subtract), so the combination stays a valid
/// `≤` and the only goals it can close are genuinely true ones.
pub(super) fn inject_nonneg_to_cancel(goal: &Goal, acc: SortLeAcc) -> Option<SortLeAcc> {
    let diff = linear_diff(&acc.lhs, &acc.rhs)?;

    // Nat-typed atoms eligible for a `0 ≤ v` fact, keyed by atom Expr.
    let mut nat_atoms = std::collections::HashSet::new();
    for d in &goal.local_ctx {
        if matches!(d.ty.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat") {
            nat_atoms.insert(Expr::fvar(d.fvar));
        }
    }

    let mut result = acc;
    for (atom, &coeff) in &diff.coeffs {
        if coeff == 0 {
            continue;
        }
        // A leftover atom must be a Nat variable with a POSITIVE residual to be
        // cancellable by `0 ≤ v`. Anything else means this orientation/combo is
        // not a `hyp + nonneg` witness.
        if coeff < 0 || !nat_atoms.contains(atom) {
            return None;
        }
        let count = u64::try_from(coeff).ok()?;
        // Fold `count` copies of `Nat.zero_le atom : Nat.le 0 atom`.
        let zero = Expr::nat_lit(0);
        for _ in 0..count {
            let zero_le = Expr::const_(Name::from_string("Nat.zero_le"), vec![]);
            let proof = Expr::app(zero_le, atom.clone());
            let nonneg = SortLeAcc::nat_from_parts(zero.clone(), atom.clone(), proof)?;
            result = result.combine(nonneg)?;
        }
    }
    Some(result)
}

/// Linear-form difference `lhs - rhs` (atom coeffs and constant) using the
/// shared Nat linear-form parser.
fn linear_diff(lhs: &Expr, rhs: &Expr) -> Option<NatDiff> {
    let lf = super::arith_linarith_nat_eq::parse_nat_linear_form(lhs)?;
    let rf = super::arith_linarith_nat_eq::parse_nat_linear_form(rhs)?;
    let mut coeffs = std::collections::HashMap::new();
    for (atom, &c) in &lf.coeffs {
        *coeffs.entry(atom.clone()).or_insert(0_i128) += i128::from(c);
    }
    for (atom, &c) in &rf.coeffs {
        *coeffs.entry(atom.clone()).or_insert(0_i128) -= i128::from(c);
    }
    coeffs.retain(|_, c| *c != 0);
    Some(NatDiff {
        coeffs,
        constant: i128::from(lf.constant) - i128::from(rf.constant),
    })
}

struct NatDiff {
    coeffs: std::collections::HashMap<Expr, i128>,
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    constant: i128,
}

/// Build the negated-goal accumulator `Nat.le (succ GR) GL` from `hg : ¬G`.
///
/// `Nat.not_le GL GR : Iff (Nat.le GL GR → False) (Nat.lt GR GL)` (tc form), so
/// `Iff.mp (Nat.not_le GL GR) hg : Nat.lt GR GL`, which is the reducible def
/// `Nat.le (Nat.succ GR) GL`. We declare the accumulator endpoints as
/// `(Nat.succ GR, GL)`; the `Nat.lt` proof is def-eq to `Nat.le (succ GR) GL`,
/// so the downstream `Nat.add_le_add` application kernel-checks.
pub(super) fn negated_goal_fact_classical(
    goal_le_lhs: &Expr,
    goal_le_rhs: &Expr,
    hg_fvar: FVarId,
) -> Option<NegGoalFact> {
    use super::tc_app::{nat_le_tc, nat_lt_tc};

    let not_le = Expr::const_(Name::from_string("Nat.not_le"), vec![]);
    // Nat.not_le GL GR : Iff (@LE.le Nat _ GL GR → False) (@LT.lt Nat _ GR GL)
    let iff = Expr::apps(not_le, [goal_le_lhs.clone(), goal_le_rhs.clone()]);

    // The two `Iff` Props (must be supplied explicitly — the kernel does NOT
    // auto-insert implicits in raw term application):
    //   a := (@LE.le Nat _ GL GR) → False   (the negated goal, = hg's type)
    //   b := @LT.lt Nat _ GR GL             (the positive consequence)
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let prop_a = Expr::pi(
        BinderInfo::Default,
        nat_le_tc(goal_le_lhs.clone(), goal_le_rhs.clone()),
        false_ty,
    );
    let prop_b = nat_lt_tc(goal_le_rhs.clone(), goal_le_lhs.clone());

    // @Iff.mp a b iff hg : b   (b ≡ Nat.le (succ GR) GL).
    let iff_mp = Expr::const_(Name::from_string("Iff.mp"), vec![]);
    let lt_proof = Expr::apps(iff_mp, [prop_a, prop_b, iff, Expr::fvar(hg_fvar)]);

    // Accumulator LHS endpoint: the collapsed literal `GR+1` when GR is a
    // concrete literal (so the constant is a single literal leaf), and the
    // additive form `Nat.add GR 1` when GR is symbolic. Both are def-eq to
    // `Nat.succ GR` (`Nat.add GR 1` reduces to `Nat.succ (GR + 0)` ≡ `Nat.succ
    // GR`), so the `Nat.lt`-typed `lt_proof` (= `Nat.le (succ GR) GL`)
    // kernel-checks against `Nat.le <endpoint> GL`. Using the `Nat.add` form
    // rather than a raw `Nat.succ` keeps the endpoint inside the linear-form
    // fragment the downstream equality synthesizer
    // (`try_prove_nat_equality_direct`) can canonicalize — a bare `Nat.succ`
    // atom would otherwise defeat it. The kernel re-check is the soundness gate.
    let neg_lhs = neg_goal_lhs_endpoint(goal_le_rhs)?;

    Some(NegGoalFact {
        lhs: neg_lhs,
        rhs: goal_le_lhs.clone(),
        proof: lt_proof,
    })
}

/// The `Nat.le` LHS endpoint standing for `GR + 1`: the collapsed literal when
/// `GR` is concrete (so the constant stays one literal leaf the downstream
/// linear-form canonicalizer can fold), the additive form otherwise. Both are
/// def-eq to `Nat.succ GR`.
pub(super) fn neg_goal_lhs_endpoint(goal_le_rhs: &Expr) -> Option<Expr> {
    match super::nat_expr_eval::eval_nat_expr(goal_le_rhs) {
        Some(v) => Some(Expr::nat_lit(v.checked_add(1)?)),
        None => Some(nat_add(goal_le_rhs, &Expr::nat_lit(1))),
    }
}

/// Normalize a Nat comparison goal `target` to `(GL, GR)` of `Nat.le GL GR`.
///
/// Mirrors the normalization in `arith_linarith_nat_direct::normalize_nat_comparison`:
/// - `a ≤ b` → `(a, b)`
/// - `a < b` → `(a + 1, b)`
/// - `a ≥ b` → `(b, a)`     (operands swapped)
/// - `a > b` → `(b + 1, a)` (operands swapped)
///
/// The swap is done here from the raw application args keyed on the surface
/// head. The orientation is the soundness-relevant part: the negated-goal proof
/// is built from `(GL, GR)`, and the whole term is kernel-rechecked, so a wrong
/// orientation fails closed rather than proving a false goal.
///
/// Returns `None` for non-Nat or non-comparison goals.
pub(super) fn normalize_nat_goal_to_le(target: &Expr) -> Option<(Expr, Expr)> {
    let head = target.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let name_s = name.to_string();
    let args = target.get_app_args();

    // Typeclass forms `@Rel.{u} Nat inst a b` carry the sort in `args[0]`;
    // direct forms `Nat.{le,lt} a b` are implicitly Nat.
    let (a, b) = if args.len() == 4 {
        if !is_nat_const(args[0]) {
            return None;
        }
        match name_s.as_str() {
            "LE.le" | "LT.lt" | "GE.ge" | "GT.gt" => (args[2].clone(), args[3].clone()),
            _ => return None,
        }
    } else if args.len() == 2 {
        match name_s.as_str() {
            "Nat.le" | "Nat.lt" => (args[0].clone(), args[1].clone()),
            _ => return None,
        }
    } else {
        return None;
    };

    let one = Expr::nat_lit(1);
    match name_s.as_str() {
        "LE.le" | "Nat.le" => Some((a, b)),
        "LT.lt" | "Nat.lt" => Some((nat_add(&a, &one), b)),
        "GE.ge" => Some((b, a)),
        "GT.gt" => Some((nat_add(&b, &one), a)),
        _ => None,
    }
}

/// Upper bound on the uniform hypothesis multiplier to try for a scaled-
/// monotonicity goal, derived from the largest atom coefficient appearing in the
/// goal's (normalized) `Nat.le` endpoints. For `2*a ≤ 2*b` this is `2`; for a
/// coefficient-free goal it is `1` (no scaled set generated). Capped at a small
/// constant so the search stays cheap; a genuine higher-coefficient goal that
/// exceeds the cap simply fails closed (no wrong term is ever emitted).
pub(super) fn goal_multiplier_bound(lhs: &Expr, rhs: &Expr) -> i128 {
    const CAP: i128 = 8;
    let mut bound: i128 = 1;
    for side in [lhs, rhs] {
        if let Some(form) = super::arith_linarith_nat_eq::parse_nat_linear_form(side) {
            for &c in form.coeffs.values() {
                let mag = i128::from(c).abs();
                if mag > bound {
                    bound = mag;
                }
            }
        }
    }
    bound.min(CAP)
}

/// Compute the Farkas gap `k = linearForm(lhs) - linearForm(rhs)` when it is a
/// pure non-negative constant (all atom coefficients cancel). Returns `None`
/// when the difference is not a constant (not a genuine contradiction shape).
pub(super) fn nat_farkas_gap(lhs: &Expr, rhs: &Expr) -> Option<u64> {
    let lf = super::arith_linarith_nat_eq::parse_nat_linear_form(lhs)?;
    let rf = super::arith_linarith_nat_eq::parse_nat_linear_form(rhs)?;
    // Every atom coefficient must match (cancel in the difference).
    for (atom, &lc) in &lf.coeffs {
        if rf.coeffs.get(atom).copied().unwrap_or(0) != lc {
            return None;
        }
    }
    for (atom, &rc) in &rf.coeffs {
        if lf.coeffs.get(atom).copied().unwrap_or(0) != rc {
            return None;
        }
    }
    let diff = lf.constant.checked_sub(rf.constant)?;
    if diff < 1 {
        return None;
    }
    u64::try_from(diff).ok()
}

/// `@Eq.ndrec Nat L (fun z => Nat.le z R) proof newL eq : Nat.le newL R`
/// where `proof : Nat.le L R` and `eq : L = newL`.
pub(super) fn transport_le_lhs(proof: &Expr, l: &Expr, r: &Expr, new_l: &Expr, eq: &Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
    // motive : fun (z : Nat) => Nat.le z R
    let motive = {
        let body = Expr::apps(nat_le, [Expr::bvar(0), r.clone()]);
        Expr::lam(BinderInfo::Default, nat_ty.clone(), body)
    };
    // @Eq.ndrec.{0,1} Nat L motive proof newL eq
    let eq_ndrec = Expr::const_(
        Name::from_string("Eq.ndrec"),
        vec![Level::zero(), Level::succ(Level::zero())],
    );
    Expr::apps(
        eq_ndrec,
        [
            nat_ty,
            l.clone(),
            motive,
            proof.clone(),
            new_l.clone(),
            eq.clone(),
        ],
    )
}

/// `Nat.add a b`.
pub(super) fn nat_add(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// `@Eq Nat l r`.
pub(super) fn mk_nat_eq(l: &Expr, r: &Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat_ty, l.clone(), r.clone()],
    )
}
