// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct (goal-driven) proof synthesis for linear Nat inequality goals.
//!
//! The Fourier-Motzkin / mathverse certified path proves contradictions by
//! combining *hypotheses*. For a goal like `n + 1 > n` with **no hypotheses**,
//! the unsat comes entirely from the negated goal, so there is no hypothesis
//! to thread into [`super::arith_linarith_proof::build_linarith_proof`] and it
//! returns `None` (see the `ineq_gap` diagnosis).
//!
//! This module closes that gap for the common Nat shapes by *proving the goal
//! directly* (rather than refuting hypotheses). It matches a Nat comparison
//! goal whose two sides share an additive symbolic core differing by a concrete
//! literal offset, e.g. `core + p  <op>  core + q`, and synthesizes a kernel
//! term out of the `Nat.le` inductive constructors:
//!
//! - `Nat.le.refl : (k : Nat) → Nat.le k k`
//! - `Nat.le.step : {n m : Nat} → Nat.le n m → Nat.le n (Nat.succ m)`
//!
//! To prove `Nat.le P Q` where `P` and `Q` share a core and `eval(Q) - eval(P)
//! = d >= 0`, we build `Nat.le.step^d (Nat.le.refl P) : Nat.le P (Nat.succ^d P)`.
//! Because `P + d` definitionally reduces to `Nat.succ^d P` for a concrete
//! literal `d` (the Nat.add recursor unfolds on its second argument), the
//! synthesized term is kernel-def-eq to the declared target `Nat.le P Q`.
//!
//! Every term produced here is handed back to `state.close_goal`, which runs a
//! genuine `infer_type` + WHNF + `is_def_eq` check against the target. A wrong
//! reconstruction is therefore *rejected*, never trusted: this preserves the
//! safe-reject soundness model and emits **zero** `trustedAy`/`trustedArith`
//! axioms.

use clean_kernel::expr::ExprKind;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::nat_expr_eval::eval_nat_expr;

/// A Nat comparison goal, normalized to `Nat.le lhs rhs`.
///
/// The four surface relations all reduce to a single `Nat.le` obligation:
/// - `a ≤ b`  → `Nat.le a b`
/// - `a < b`  → `Nat.le (a + 1) b`   (`Nat.lt a b := Nat.le (succ a) b`)
/// - `a ≥ b`  → `Nat.le b a`
/// - `a > b`  → `Nat.le (b + 1) a`
struct NatLeGoal {
    /// Left side of the normalized `Nat.le`.
    le_lhs: Expr,
    /// Right side of the normalized `Nat.le`.
    le_rhs: Expr,
}

/// Split a Nat expression into `(core, offset)` where `expr` is
/// definitionally `core + offset` and `offset` is a concrete literal.
///
/// Handles the additive shapes the elaborator emits:
/// - `HAdd.hAdd Nat Nat Nat inst a b` / `Nat.add a b` with `b` a literal
/// - `Nat.succ x` (offset += 1, recurse on `x`)
/// - a bare literal (core = `Nat.zero`/`0`, offset = the literal)
///
/// The recursion peels literal addends from the right so that
/// `(((c + 2) + 3))` collapses to `(c, 5)`. A non-literal addend on the right
/// stops the peel and is folded into the core.
///
/// REQUIRES: `expr` is a well-formed Nat expression.
/// ENSURES: On `Some((core, off))`, `expr` is def-eq to `Nat.add core off`
///   (and to `core` when `off == 0`).
pub(crate) fn nat_split_core_offset(expr: &Expr) -> Option<(Expr, u64)> {
    split_core_offset(expr)
}

fn split_core_offset(expr: &Expr) -> Option<(Expr, u64)> {
    // Bare literal: core is 0, offset is the value.
    if let Some(v) = eval_nat_expr(expr) {
        return Some((Expr::nat_lit(0), v));
    }

    match expr.kind() {
        // Nat.succ x  =>  (core(x), offset(x) + 1)
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Nat.succ" {
                    let (core, off) = split_core_offset(arg)?;
                    return Some((core, off.checked_add(1)?));
                }
            }

            // Binary addition: peel a literal right addend.
            let args = expr.get_app_args();
            if args.len() >= 2 {
                if let ExprKind::Const(op, _) = expr.get_app_fn().kind() {
                    let op_s = op.to_string();
                    if op_s == "Nat.add" || op_s == "HAdd.hAdd" || op_s == "Add.add" {
                        let lhs = args[args.len() - 2];
                        let rhs = args[args.len() - 1];
                        // `core + literal`
                        if let Some(rv) = eval_nat_expr(rhs) {
                            let (core, off) = split_core_offset(lhs)?;
                            return Some((core, off.checked_add(rv)?));
                        }
                        // `literal + core`
                        if let Some(lv) = eval_nat_expr(lhs) {
                            let (core, off) = split_core_offset(rhs)?;
                            return Some((core, off.checked_add(lv)?));
                        }
                    }
                }
            }
            // Symbolic atom with no literal offset.
            Some((expr.clone(), 0))
        }
        // Any other symbolic head (fvar, const variable, mul, ...): offset 0.
        _ => Some((expr.clone(), 0)),
    }
}

/// Build `Nat.le P Q` where `Q` is `Nat.succ^d P` (`d >= 0`).
///
/// `Nat.le.step^d (Nat.le.refl base)`. The result type is
/// `Nat.le base (Nat.succ^d base)`, which the kernel checks def-eq against the
/// declared `Nat.le base Q` since `base + d` reduces to `Nat.succ^d base`.
///
/// `Nat.le.step : {n m : Nat} → Nat.le n m → Nat.le n (Nat.succ m)`. The kernel
/// does **not** auto-insert implicit arguments, so each application provides
/// `@Nat.le.step base current_upper prev` explicitly, where `current_upper`
/// tracks the current right endpoint (`base`, then `Nat.succ base`, …).
pub(crate) fn nat_le_via_steps(base: &Expr, steps: u64) -> Expr {
    build_le_via_steps(base, steps)
}

fn build_le_via_steps(base: &Expr, steps: u64) -> Expr {
    let le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
    let le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    // Nat.le.refl base : Nat.le base base
    let mut proof = Expr::app(le_refl, base.clone());
    let mut current_upper = base.clone();
    for _ in 0..steps {
        // @Nat.le.step base current_upper proof : Nat.le base (Nat.succ current_upper)
        proof = Expr::apps(
            le_step.clone(),
            [base.clone(), current_upper.clone(), proof],
        );
        current_upper = Expr::app(succ.clone(), current_upper);
    }
    proof
}

/// Normalize a Nat comparison goal target to a `Nat.le` obligation.
///
/// Recognizes both the typeclass forms (`@LE.le/LT.lt/GE.ge/GT.gt Nat inst a b`)
/// and the direct `Nat.le a b` / `Nat.lt a b` heads.
///
/// REQUIRES: `target` is a well-formed goal type.
/// ENSURES: On `Some`, the returned `NatLeGoal` is provable iff the original
///   goal is, and proving `Nat.le le_lhs le_rhs` proves the original goal
///   (up to kernel def-eq).
fn normalize_nat_comparison(target: &Expr) -> Option<NatLeGoal> {
    let args = target.get_app_args();
    let head = target.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let name_s = name.to_string();

    // Confirm the comparison is over Nat and extract (a, b).
    let (rel, a, b) = if args.len() == 4 {
        // @Rel.{u} α inst a b — require α = Nat.
        if !is_nat_type(args[0]) {
            return None;
        }
        match name_s.as_str() {
            "LE.le" | "LT.lt" | "GE.ge" | "GT.gt" => {
                (name_s.as_str(), args[2].clone(), args[3].clone())
            }
            _ => return None,
        }
    } else if args.len() == 2 {
        match name_s.as_str() {
            "Nat.le" => ("LE.le", args[0].clone(), args[1].clone()),
            "Nat.lt" => ("LT.lt", args[0].clone(), args[1].clone()),
            _ => return None,
        }
    } else {
        return None;
    };

    let one = Expr::nat_lit(1);
    let (le_lhs, le_rhs) = match rel {
        // a ≤ b  ->  Nat.le a b
        "LE.le" => (a, b),
        // a < b  ->  Nat.le (a + 1) b
        "LT.lt" => (nat_add(a, one), b),
        // a ≥ b  ->  Nat.le b a
        "GE.ge" => (b, a),
        // a > b  ->  Nat.le (b + 1) a
        "GT.gt" => (nat_add(b, one), a),
        _ => return None,
    };
    Some(NatLeGoal { le_lhs, le_rhs })
}

fn is_nat_type(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat")
}

fn nat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), lhs),
        rhs,
    )
}

/// Attempt to synthesize a kernel-checked proof for a linear Nat inequality
/// goal *directly from the goal* (no hypotheses needed).
///
/// Succeeds when the goal is a Nat comparison whose two sides share an additive
/// symbolic core and the inequality holds by the literal offsets alone, e.g.
/// `n + 1 > n`, `n < n + 1`, `n ≤ n + 1`, `n + 2 > n`, `5 ≤ 7`.
///
/// The result is always re-checked by `state.close_goal`; this function only
/// proposes a candidate term.
///
/// REQUIRES: `target` is the current goal type.
/// ENSURES: On `Some(e)`, `e` is intended to have type `target`; soundness is
///   guaranteed by the caller's kernel re-check, not by this function.
/// ENSURES: On `None`, the goal is not a supported direct Nat inequality shape
///   (caller must fall through to the FM/SMT path or fail closed).
pub(crate) fn try_prove_nat_inequality_direct(target: &Expr) -> Option<Expr> {
    let NatLeGoal { le_lhs, le_rhs } = normalize_nat_comparison(target)?;

    let (lhs_core, lhs_off) = split_core_offset(&le_lhs)?;
    let (rhs_core, rhs_off) = split_core_offset(&le_rhs)?;

    // Shared symbolic core: the comparison is decided by the literal offsets.
    // (Concrete-vs-concrete also lands here with both cores equal to `0`.)
    if lhs_core == rhs_core {
        // Provable iff lhs_off <= rhs_off. If lhs_off > rhs_off the inequality
        // is FALSE on the shared core (e.g. `n > n + 1`): return None so omega
        // fails closed rather than emitting a bogus term.
        if lhs_off > rhs_off {
            return None;
        }
        let steps = rhs_off - lhs_off;
        // Prove `Nat.le le_lhs le_rhs` by weakening the RHS `steps` times from
        // `Nat.le.refl le_lhs`. `le_lhs + steps` reduces to `Nat.succ^steps
        // le_lhs`, def-eq to `le_rhs` (= shared_core + rhs_off).
        return Some(build_le_via_steps(&le_lhs, steps));
    }

    // `0 ≤ R` for any (symbolic) Nat R: provable via `Nat.zero_le R : Nat.le 0 R`.
    // Fires only when the normalized LHS is literally `0` (offset 0, zero core);
    // literal `0 ≤ k` is already handled by the shared-core weakening path above,
    // and `0 < n` normalizes to LHS offset 1 (so it correctly does NOT fire here,
    // since `0 < 0` is false). Kernel-rechecked by the caller.
    if lhs_off == 0 && lhs_core == Expr::nat_lit(0) {
        let zero_le = Expr::const_(Name::from_string("Nat.zero_le"), vec![]);
        return Some(Expr::apps(zero_le, [le_rhs.clone()]));
    }

    // Slice A (Nat non-negativity, the `a ≤ a + b` family): the goal LHS appears
    // as an addend of the RHS, so `L ≤ R` holds because the *other* addend is a
    // Nat (hence ≥ 0). This is the goal-driven form of injecting `0 ≤ x` for Nat
    // atoms. Emits `Nat.le_add_right` (def-eq form), kernel-rechecked by caller.
    try_prove_nat_le_add_nonneg(&le_lhs, &le_rhs)
}

/// Slice A: prove `Nat.le L R` where `R` is `L + extra` (L is one addend of R)
/// and `extra` is any Nat term (hence `≥ 0`).
///
/// - `R = Nat.add L extra`  →  `Nat.le_add_right L extra : Nat.le L (L + extra)`.
/// - `R = Nat.add extra L`  →  transport `Nat.le_add_right L extra` along
///   `Nat.add_comm L extra : (L + extra) = (extra + L)` via `Eq.ndrec`,
///   yielding `Nat.le L (extra + L)`.
///
/// `Nat.le_add_right : ∀ n k, Nat.le n (Nat.add n k)` and `Nat.add_comm` are
/// constructive prelude theorems (zero domain axioms). The synthesized term is
/// re-checked by `close_goal`, so a wrong match fails closed.
///
/// Soundness: only fires when `L` is *syntactically* an addend of `R`. It never
/// claims `a ≤ b` for unrelated `a, b` (those have distinct cores AND `L` is not
/// an addend of `R`, so this returns `None`). A false goal like `a + b ≤ a` has
/// `R = a` with no `Nat.add` head, so it returns `None` and omega fails closed.
fn try_prove_nat_le_add_nonneg(le_lhs: &Expr, le_rhs: &Expr) -> Option<Expr> {
    let (rhs_l, rhs_r) = nat_add_children(le_rhs)?;
    let le_add_right = Expr::const_(Name::from_string("Nat.le_add_right"), vec![]);

    // R = L + extra
    if &rhs_l == le_lhs {
        // Nat.le_add_right L extra : Nat.le L (Nat.add L extra)
        return Some(Expr::apps(le_add_right, [le_lhs.clone(), rhs_r]));
    }

    // R = extra + L  →  transport along add_comm.
    if &rhs_r == le_lhs {
        let extra = rhs_l;
        // base : Nat.le L (Nat.add L extra)
        let base = Expr::apps(le_add_right, [le_lhs.clone(), extra.clone()]);
        let l_plus_extra = nat_add(le_lhs.clone(), extra.clone());
        let extra_plus_l = nat_add(extra.clone(), le_lhs.clone());
        // motive : fun w => Nat.le L w
        let motive = {
            // Use a bound-variable-free lambda via Expr::lam over a fresh local.
            // The kernel re-checks; we build `fun (w : Nat) => Nat.le L w`.
            mk_le_motive(le_lhs)
        };
        // Nat.add_comm L extra : Eq (Nat.add L extra) (Nat.add extra L)
        let add_comm = Expr::apps(
            Expr::const_(Name::from_string("Nat.add_comm"), vec![]),
            [le_lhs.clone(), extra],
        );
        // @Eq.ndrec Nat (L+extra) motive base (extra+L) add_comm : Nat.le L (extra+L)
        // Levels: [motive_universe = 0 (Prop), alpha_universe = 1 (Nat : Sort 1)].
        let eq_ndrec = Expr::const_(
            Name::from_string("Eq.ndrec"),
            vec![
                clean_kernel::level::Level::zero(),
                clean_kernel::level::Level::succ(clean_kernel::level::Level::zero()),
            ],
        );
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        return Some(Expr::apps(
            eq_ndrec,
            [nat_ty, l_plus_extra, motive, base, extra_plus_l, add_comm],
        ));
    }

    None
}

/// Build `fun (w : Nat) => Nat.le L w` as a kernel lambda.
fn mk_le_motive(l: &Expr) -> Expr {
    use clean_kernel::expr::BinderInfo;
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    // The body references the lambda's bound variable via de Bruijn index 0.
    let body = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), l.clone()),
        Expr::bvar(0),
    );
    Expr::lam(BinderInfo::Default, nat_ty, body)
}

/// Extract `(a, b)` from `Nat.add a b` / `HAdd.hAdd .. a b` / `Add.add a b`.
fn nat_add_children(expr: &Expr) -> Option<(Expr, Expr)> {
    let args = expr.get_app_args();
    if args.len() >= 2 {
        if let ExprKind::Const(op, _) = expr.get_app_fn().kind() {
            let op_s = op.to_string();
            if op_s == "Nat.add" || op_s == "HAdd.hAdd" || op_s == "Add.add" {
                let a = args[args.len() - 2].clone();
                let b = args[args.len() - 1].clone();
                return Some((a, b));
            }
        }
    }
    None
}

/// Extract `(a, b)` from `Nat.sub a b` / `HSub.hSub .. a b` / `Sub.sub a b`.
///
/// Both the raw `Nat.sub` head and the typeclass `HSub.hSub`/`Sub.sub` heads are
/// recognized; the last two application arguments are the operands in each case.
fn nat_sub_children(expr: &Expr) -> Option<(Expr, Expr)> {
    let args = expr.get_app_args();
    if args.len() >= 2 {
        if let ExprKind::Const(op, _) = expr.get_app_fn().kind() {
            let op_s = op.to_string();
            if op_s == "Nat.sub" || op_s == "HSub.hSub" || op_s == "Sub.sub" {
                let a = args[args.len() - 2].clone();
                let b = args[args.len() - 1].clone();
                return Some((a, b));
            }
        }
    }
    None
}

/// Extract `(a, b)` from a `min`-headed Nat term.
///
/// Accepts the bare op `Nat.min a b` AND the typeclass-projection surface forms
/// that the elaborator emits once `Min`/`Max` are registered in the prelude:
///   - `@Min.min α inst a b`   (the projection method)
///   - `@min α inst a b`       (the lowercase `export Min (min)` surface alias)
///
/// In every form the two operands are the *trailing* two application arguments,
/// so peeling is purely syntactic (no whnf). For `Min Nat` the instance is
/// `instMinNat := Min.mk Nat Nat.min`, so `@Min.min Nat instMinNat a b` is
/// definitionally `Nat.min a b` — the foundational lemma (`Nat.min_le_left a b`)
/// the caller emits for the extracted `a`/`b` is re-checked by the kernel against
/// the (projection-headed) goal, so this peel only changes *which* candidate is
/// proposed, never whether it is accepted. A non-Nat `min`/`Min.min` term yields
/// a `Nat.*` lemma that fails the kernel re-check (fail-closed).
fn nat_min_children(expr: &Expr) -> Option<(Expr, Expr)> {
    nat_op2_children(expr, &["Nat.min", "Min.min", "min"])
}

/// Extract `(a, b)` from a `max`-headed Nat term — bare `Nat.max` or the
/// `Max.max` / `max` typeclass-projection surface forms. See [`nat_min_children`].
fn nat_max_children(expr: &Expr) -> Option<(Expr, Expr)> {
    nat_op2_children(expr, &["Nat.max", "Max.max", "max"])
}

/// Extract the last two application args of `op a b` when the head constant is
/// one of `op_names`. Multiple accepted heads let the bare op (`Nat.min`) and the
/// typeclass-projection / surface-alias forms (`Min.min` / `min`) share one
/// extractor, since in all of them the two operands are the trailing two args.
fn nat_op2_children(expr: &Expr, op_names: &[&str]) -> Option<(Expr, Expr)> {
    let args = expr.get_app_args();
    if args.len() >= 2 {
        if let ExprKind::Const(op, _) = expr.get_app_fn().kind() {
            let op_s = op.to_string();
            if op_names.iter().any(|n| *n == op_s) {
                let a = args[args.len() - 2].clone();
                let b = args[args.len() - 1].clone();
                return Some((a, b));
            }
        }
    }
    None
}

/// Extract the two operands of an `@Eq Nat l r` goal (literal/typeclass forms).
///
/// Returns `(l, r)` only when the equality is over `Nat`; `None` otherwise.
fn nat_eq_children(target: &Expr) -> Option<(Expr, Expr)> {
    let args = target.get_app_args();
    let ExprKind::Const(name, _) = target.get_app_fn().kind() else {
        return None;
    };
    if name.to_string() != "Eq" || args.len() != 3 {
        return None;
    }
    if !is_nat_type(args[0]) {
        return None;
    }
    Some((args[1].clone(), args[2].clone()))
}

/// Tier-1 Nat-subtraction shape recognizer.
///
/// Matches the three common, unconditionally-true Nat-subtraction goal shapes
/// and emits the *registered foundational lemma* applied to the matched args
/// (all binders explicit in this environment, so we apply both `a` and `b`):
///
/// 1. `a - b ≤ a`               →  `@Nat.sub_le a b`
///    (also covers `<`/`≥`/`>` only when they normalize to this exact `≤`).
/// 2. `a - a = 0`               →  `@Nat.sub_self a`
/// 3. `a + b - b = a`           →  `@Nat.add_sub_cancel a b`
///
/// SOUNDNESS: each branch emits the *exact* registered lemma for the *exact*
/// matched head. The synthesized term is re-checked by `close_goal`'s
/// `is_def_eq` and ultimately by `add_decl`, so a mis-binding (e.g. emitting
/// `Nat.sub_self` for `a - b` with `a ≠ b`) is rejected, never trusted. A FALSE
/// sub goal (`a - b = a`, `a ≤ a - b`, `a - b ≥ b`) matches *none* of these
/// exact shapes, so this returns `None` and omega falls through / fails closed.
/// These three lemmas have empty domain-axiom closures (foundational Nat
/// lemmas), so zero `trustedAy`/`trustedArith` is emitted.
fn try_prove_nat_sub_shape(target: &Expr) -> Option<Expr> {
    // Shape 2 & 3: an `@Eq Nat l r` goal.
    if let Some((lhs, rhs)) = nat_eq_children(target) {
        // Shape 2: `a - a = 0`  →  `@Nat.sub_self a`.
        if let Some((sa, sb)) = nat_sub_children(&lhs) {
            // RHS must be (definitionally) zero: a bare `0`/`Nat.zero` literal.
            let rhs_is_zero = eval_nat_expr(&rhs) == Some(0);
            if rhs_is_zero && sa == sb {
                let sub_self = Expr::const_(Name::from_string("Nat.sub_self"), vec![]);
                return Some(Expr::app(sub_self, sa));
            }
            // Shape 3: `(x + y) - y = a`  →  `@Nat.add_sub_cancel x y`
            //          (requires the matched `a` to be the left addend `x`).
            if let Some((add_l, add_r)) = nat_add_children(&sa) {
                if add_r == sb && add_l == rhs {
                    let add_sub_cancel =
                        Expr::const_(Name::from_string("Nat.add_sub_cancel"), vec![]);
                    return Some(Expr::apps(add_sub_cancel, [add_l, add_r]));
                }
            }
        }
        return None;
    }

    // Shape 1: `a - b ≤ a` (and the `<`/`≥`/`>` forms that normalize to it).
    // Normalize the comparison to `Nat.le le_lhs le_rhs`; the goal is exactly
    // `Nat.sub_le a b` iff `le_lhs` is `a - b` and `le_rhs` is that same `a`.
    let NatLeGoal { le_lhs, le_rhs } = normalize_nat_comparison(target)?;
    let (sa, sb) = nat_sub_children(&le_lhs)?;
    if sa == le_rhs {
        let sub_le = Expr::const_(Name::from_string("Nat.sub_le"), vec![]);
        return Some(Expr::apps(sub_le, [sa, sb]));
    }
    None
}

/// Prove a goal `Nat.le GL (X - k)` from a hypothesis `Nat.le HL X` (same
/// minuend `X`, literal subtrahend `k`) via `Nat.sub_le_sub_right`.
///
/// `@Nat.sub_le_sub_right HL X (hyp : HL ≤ X) k : HL - k ≤ X - k`. When the goal
/// LHS `GL` is exactly `HL - k` (as a concrete value, or syntactically), the
/// produced term proves the goal directly; when `GL ≤ HL - k` as concrete values
/// the result is weakened down to `GL` via `Nat.le.step`-anchored re-derivation
/// from the lowered endpoint. The reproduced case is `(h : a ≥ 3) ⊢ a - 2 ≥ 1`:
/// the goal normalizes to `Nat.le 1 (a - 2)`, the hyp to `Nat.le 3 a`, and
/// `Nat.sub_le_sub_right (h) 2 : 3 - 2 ≤ a - 2`; `3 - 2` reduces to `1`, matching
/// `GL`.
///
/// SOUNDNESS: `Nat.sub_le_sub_right` is a constructive prelude theorem; the
/// emitted term is re-checked by `close_goal`. A false goal (e.g.
/// `(h : a ≥ 3) ⊢ a - 2 ≥ 2`) has `GL = 2 > HL - k = 1`, fails the value check,
/// and returns `None` (fail closed).
fn try_prove_nat_sub_mono_from_hyp(target: &Expr, hyps: &[(Expr, Expr)]) -> Option<Expr> {
    let NatLeGoal { le_lhs, le_rhs } = normalize_nat_comparison(target)?;
    // Goal RHS must be `X - k` with `k` a concrete literal.
    let (minuend, subtrahend) = nat_sub_children(&le_rhs)?;
    let k = eval_nat_expr(&subtrahend)?;
    // Goal LHS must be a concrete value (the lowered bound `HL - k`).
    let gl = eval_nat_expr(&le_lhs)?;

    for (hyp_fvar, hyp_ty) in hyps {
        let Some(NatLeGoal {
            le_lhs: h_lhs,
            le_rhs: h_rhs,
        }) = normalize_nat_comparison(hyp_ty)
        else {
            continue;
        };
        // Same minuend `X`.
        if h_rhs != minuend {
            continue;
        }
        // Need `HL` concrete so the lowered endpoint `HL - k` is a value to
        // compare against `GL`.
        let Some(hl) = eval_nat_expr(&h_lhs) else {
            continue;
        };
        let lowered = hl.saturating_sub(k); // = HL - k (Nat truncation)
        if gl > lowered {
            continue; // goal lower bound exceeds what the hyp gives; fail closed.
        }

        // base : Nat.le (HL - k) (X - k)  via Nat.sub_le_sub_right.
        // clean's env stores the lemma as `Nat.sub_le_sub_right n m k h`
        // (subtrahend `k` THIRD, the `Nat.le`-typed proof `h` FOURTH); see
        // `nn_verify_zonotope_minkowski_define.rs`. The hyp proof's surface type
        // (`GE.ge` / `LE.le`) is def-eq to `Nat.le h_lhs h_rhs`, so the kernel
        // app check accepts it; `close_goal` re-checks the whole term.
        let sub_le_sub_right = Expr::const_(Name::from_string("Nat.sub_le_sub_right"), vec![]);
        let base = Expr::apps(
            sub_le_sub_right,
            [
                h_lhs.clone(),
                h_rhs.clone(),
                subtrahend.clone(),
                hyp_fvar.clone(),
            ],
        );
        if gl == lowered {
            // `HL - k` reduces to `GL`; `base` already has the goal type
            // (def-eq), so return it.
            return Some(base);
        }
        // gl < lowered: weaken the LHS down from `lowered` to `gl`. We have
        // `base : Nat.le lowered (X - k)`; since `gl ≤ lowered`, `gl ≤ X - k`
        // follows by `Nat.le_trans (Nat.le.refl-stepped gl ≤ lowered) base`.
        let gl_le_lowered = nat_le_via_steps(&Expr::nat_lit(gl), lowered - gl);
        let le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);
        let lowered_lit = Expr::nat_lit(lowered);
        return Some(Expr::apps(
            le_trans,
            [
                Expr::nat_lit(gl),
                lowered_lit,
                le_rhs.clone(),
                gl_le_lowered,
                base,
            ],
        ));
    }
    None
}

/// Tier-1 Nat min/max shape recognizer.
///
/// Matches the common, unconditionally-true `Nat.min`/`Nat.max` goal shapes and
/// emits the *registered foundational lemma* applied to BOTH explicit operands
/// (every binder is `BinderInfo::Default` in this environment, so we apply both
/// `a` and `b`, e.g. `@Nat.min_le_left a b`):
///
/// Inequality shapes (via [`normalize_nat_comparison`] → `Nat.le le_lhs le_rhs`):
/// 1. `min a b ≤ a`   →  `@Nat.min_le_left a b`
/// 2. `min a b ≤ b`   →  `@Nat.min_le_right a b`
/// 3. `a ≤ max a b`   →  `@Nat.le_max_left a b`
/// 4. `b ≤ max a b`   →  `@Nat.le_max_right a b`
///
/// Equality shapes (via [`nat_eq_children`]):
/// 5. `min a b = min b a`  →  `@Nat.min_comm a b`
/// 6. `max a b = max b a`  →  `@Nat.max_comm a b`
/// 7. `min a a = a`        →  `@Nat.min_self a`
/// 8. `max a a = a`        →  `@Nat.max_self a`
///
/// SOUNDNESS: each branch emits the *exact* registered lemma for the *exact*
/// matched head. The synthesized term is re-checked by `close_goal`'s
/// `is_def_eq` and ultimately by `add_decl`, so a mis-binding is rejected, never
/// trusted. A FALSE min/max goal (`a ≤ min a b`, `max a b ≤ a`, `min a b = a`,
/// `min a b = min b c` with `b ≠ c`) matches *none* of these exact shapes, so
/// this returns `None` and omega falls through / fails closed. Every lemma above
/// is a constructive `Declaration::Theorem` with an empty domain-axiom closure,
/// so zero `trustedAy`/`trustedArith` is emitted.
///
/// The conjunction shapes (`Nat.le_min`, `Nat.max_le`) and the general
/// case-split are deliberately deferred.
fn try_prove_nat_minmax_shape(target: &Expr) -> Option<Expr> {
    // Equality shapes (5-8): an `@Eq Nat l r` goal.
    if let Some((lhs, rhs)) = nat_eq_children(target) {
        // 7. `min a a = a`  →  `@Nat.min_self a`.
        if let Some((ma, mb)) = nat_min_children(&lhs) {
            if ma == mb && ma == rhs {
                let min_self = Expr::const_(Name::from_string("Nat.min_self"), vec![]);
                return Some(Expr::app(min_self, ma));
            }
            // 5. `min a b = min b a`  →  `@Nat.min_comm a b`.
            if let Some((ra, rb)) = nat_min_children(&rhs) {
                if ma == rb && mb == ra {
                    let min_comm = Expr::const_(Name::from_string("Nat.min_comm"), vec![]);
                    return Some(Expr::apps(min_comm, [ma, mb]));
                }
            }
        }
        // 8. `max a a = a`  →  `@Nat.max_self a`.
        if let Some((ma, mb)) = nat_max_children(&lhs) {
            if ma == mb && ma == rhs {
                let max_self = Expr::const_(Name::from_string("Nat.max_self"), vec![]);
                return Some(Expr::app(max_self, ma));
            }
            // 6. `max a b = max b a`  →  `@Nat.max_comm a b`.
            if let Some((ra, rb)) = nat_max_children(&rhs) {
                if ma == rb && mb == ra {
                    let max_comm = Expr::const_(Name::from_string("Nat.max_comm"), vec![]);
                    return Some(Expr::apps(max_comm, [ma, mb]));
                }
            }
        }
        return None;
    }

    // Inequality shapes (1-4): normalize the comparison to `Nat.le le_lhs le_rhs`.
    let NatLeGoal { le_lhs, le_rhs } = normalize_nat_comparison(target)?;

    // 1 & 2: `min a b ≤ a` / `min a b ≤ b`.
    if let Some((ma, mb)) = nat_min_children(&le_lhs) {
        if le_rhs == ma {
            let min_le_left = Expr::const_(Name::from_string("Nat.min_le_left"), vec![]);
            return Some(Expr::apps(min_le_left, [ma, mb]));
        }
        if le_rhs == mb {
            let min_le_right = Expr::const_(Name::from_string("Nat.min_le_right"), vec![]);
            return Some(Expr::apps(min_le_right, [ma, mb]));
        }
    }

    // 3 & 4: `a ≤ max a b` / `b ≤ max a b`.
    if let Some((ma, mb)) = nat_max_children(&le_rhs) {
        if le_lhs == ma {
            let le_max_left = Expr::const_(Name::from_string("Nat.le_max_left"), vec![]);
            return Some(Expr::apps(le_max_left, [ma, mb]));
        }
        if le_lhs == mb {
            let le_max_right = Expr::const_(Name::from_string("Nat.le_max_right"), vec![]);
            return Some(Expr::apps(le_max_right, [ma, mb]));
        }
    }

    None
}

/// Like [`try_prove_nat_inequality_direct`], but may also discharge the goal by
/// **weakening a hypothesis** of the form `h : Nat.le L (core + d_h)` up to the
/// goal `Nat.le L (core + d_g)` when `d_g >= d_h` and `L` / `core` match.
///
/// This covers the transitivity shape `(h : a ≤ b) ⊢ a ≤ b + 1`: the goal
/// shares the lhs `a` and the rhs core `b` with the hypothesis, so the proof is
/// `Nat.le.step^(d_g - d_h) h` (here `Nat.le.step h : Nat.le a (Nat.succ b)`).
///
/// `hyps` is a slice of `(hyp_fvar_expr, hyp_type)` pairs from the goal's local
/// context. The synthesized term is still re-checked by `state.close_goal`.
///
/// REQUIRES: `target` is the goal type; each `hyps[i].0` is the `Expr::fvar` for
///   a hypothesis whose type is `hyps[i].1`.
/// ENSURES: On `Some`, the candidate term is intended to prove `target`.
/// ENSURES: On `None`, neither the goal-only nor the hypothesis-weakening shape
///   matched (caller falls through / fails closed).
pub(crate) fn try_prove_nat_inequality_direct_with_hyps(
    target: &Expr,
    hyps: &[(Expr, Expr)],
) -> Option<Expr> {
    // 0a. Nat-subtraction shape recognizer (`a - b ≤ a`, `a - a = 0`,
    //     `a + b - b = a`). These would otherwise be parsed as opaque atoms by
    //     the linear form (Nat.sub has truncation semantics the linear parser
    //     does not model), so handle them FIRST by emitting the registered
    //     foundational lemma (Nat.sub_le / Nat.sub_self / Nat.add_sub_cancel).
    //     Short-circuits before the decide/ay path, avoiding the trustedAy
    //     residual the old `a - a = 0` route produced. False sub goals match
    //     none of the exact shapes → fall through and fail closed.
    if let Some(proof) = try_prove_nat_sub_shape(target) {
        return Some(proof);
    }

    // 0a-bis. Nat min/max shape recognizer (`min a b ≤ a`, `a ≤ max a b`,
    //     `min a b = min b a`, `min a a = a`, …). Like `Nat.sub`, an App-headed
    //     `Nat.min`/`Nat.max` is NOT modeled by the linear-form parser (it
    //     atomizes only FVars; an App-headed min/max returns None → the
    //     linear/FM path refuses the goal rather than treating it as a fresh
    //     integer atom), so handle them HERE by emitting the registered
    //     foundational lemma (Nat.min_le_left / … / Nat.max_self). False min/max
    //     goals match none of the exact shapes → fall through and fail closed.
    if let Some(proof) = try_prove_nat_minmax_shape(target) {
        return Some(proof);
    }

    // 0a-ter. Right-subtraction monotonicity from a `≤`/`≥` hypothesis:
    //     `(h : c ≤ a) ⊢ a - k ≥ c - k` and its reproduced instance
    //     `(h : a ≥ 3) ⊢ a - 2 ≥ 1` (here `c = 3`, `k = 2`, `c - k = 1`). The
    //     `Nat.sub` core atomizes in the linear form, so the FM/equality paths
    //     never see it; emit `Nat.sub_le_sub_right` directly. False sub goals
    //     match no hyp / fail the value check → fall through and fail closed.
    if let Some(proof) = try_prove_nat_sub_mono_from_hyp(target, hyps) {
        return Some(proof);
    }

    // 0. Linear Nat *equality* goal (`a + b = b + a`, `a + b + c = c + b + a`,
    //    `a + 0 = a`): decide by canonical linear form, synthesize an
    //    add_comm/add_assoc rewrite chain. Returns `None` for false equalities
    //    AND for shapes needing literal-coeff expansion (`2*a = a+a`) — both
    //    fall through and fail closed.
    if let Some(proof) = super::arith_linarith_nat_eq::try_prove_nat_equality_direct(target) {
        return Some(proof);
    }

    // 0.5. Linear Nat *equality* goal that follows from hypothesis equalities
    //      `{hi : ai = bi}` (e.g. `(h : a = b) ⊢ a + 1 = b + 1`, congruence;
    //      `(h1 : a = b)(h2 : b = c) ⊢ a + 1 = c + 1`, threaded substitution).
    //      Decides by reducing `glhs - grhs` against the lattice generated by
    //      `{ai - bi}`; synthesizes a congrArg/Eq.trans/Eq.symm chain. Returns
    //      `None` for goals that do NOT follow from the hyps (e.g.
    //      `(h : a = b) ⊢ a = c`), so omega fails closed.
    if let Some(proof) =
        super::arith_linarith_nat_eq::try_prove_nat_equality_from_hyps(target, hyps)
    {
        return Some(proof);
    }

    // 0.6. General goal reconstruction from linear equality hypotheses that PIN
    //      variables to ground values (e.g. `(h : a = 2) ⊢ a + 1 = 3`;
    //      `(h : a + b = 5)(h2 : a = 2) ⊢ b = 3` / `⊢ b ≤ 3`; `(h : a = 2) ⊢ a ≠ 3`).
    //      Solves the equality system for ground variable values, substitutes
    //      them into the goal, and closes the residual (ground equality via
    //      `Eq.refl`, disequality via `Nat.noConfusion`, inequality via this
    //      prover recursively). Returns `None` for goals that do NOT follow from
    //      the pinned values (e.g. the FALSE `(h : a = 2) ⊢ a + 1 = 4`), so omega
    //      fails closed. The recursion terminates: the residual goal is already
    //      substituted, so the inner pin pass produces no change and bails.
    if let Some(proof) = super::eq_goal_solver::try_prove_goal_via_eq_hyps(target, hyps, None) {
        return Some(proof);
    }

    // 1. Goal-only direct proof (no hypotheses required).
    if let Some(proof) = try_prove_nat_inequality_direct(target) {
        return Some(proof);
    }

    // 2. Hypothesis-weakening: goal `Nat.le L (core + d_g)` from a hypothesis
    //    `Nat.le L (core + d_h)` with d_g >= d_h.
    let NatLeGoal { le_lhs, le_rhs } = normalize_nat_comparison(target)?;
    let (goal_rhs_core, goal_rhs_off) = split_core_offset(&le_rhs)?;

    for (hyp_fvar, hyp_ty) in hyps {
        let Some(NatLeGoal {
            le_lhs: h_lhs,
            le_rhs: h_rhs,
        }) = normalize_nat_comparison(hyp_ty)
        else {
            continue;
        };
        // Same left endpoint.
        if h_lhs != le_lhs {
            continue;
        }
        let Some((h_rhs_core, h_rhs_off)) = split_core_offset(&h_rhs) else {
            continue;
        };
        // Same right-hand core, goal weaker-or-equal on the right.
        if h_rhs_core != goal_rhs_core || goal_rhs_off < h_rhs_off {
            continue;
        }
        let steps = goal_rhs_off - h_rhs_off;
        // `hyp_fvar : Nat.le L (h_rhs_core + h_rhs_off)`; weaken the RHS
        // `steps` times. `Nat.le.step` needs the explicit endpoint, which is
        // `h_rhs` initially. We re-derive via the same builder anchored at the
        // hypothesis proof.
        return Some(build_le_step_from(hyp_fvar, &le_lhs, &h_rhs, steps));
    }

    // 2.5. Matched-symbolic-core shifted inequality: goal `Nat.le (cl + k_l)
    //      (cr + k_r)` from a hypothesis `Nat.le (cl + h_l) (cr + h_r)` where
    //      BOTH sides share their symbolic core with the corresponding goal side
    //      and the RHS core `cr` is *symbolic* (PATH 3 already covers the
    //      concrete-RHS case). This is the family PATH 2 cannot reach because the
    //      goal LHS is shifted off the hypothesis LHS (`h_lhs != le_lhs`):
    //
    //        (h : a ≤ b)  ⊢ a + 1 ≤ b + 1     (k_l=k_r=1, h_l=h_r=0)
    //        (h : a < b)  ⊢ a + 1 ≤ b         (normalized hyp a+1≤b: h_l=1,h_r=0;
    //                                          goal a+1≤b: k_l=1,k_r=0 — identical)
    //        (h : a ≤ b)  ⊢ a + 3 ≤ b + 3     (k_l=k_r=3, h_l=h_r=0)
    //
    //      See `try_prove_nat_shifted_le_from_hyp` for the validity condition and
    //      construction. Returns `None` (fail closed) when no hyp matches or the
    //      integer-slack condition fails (e.g. the FALSE `a ≤ b ⊢ a + 2 ≤ b`).
    if let Some(proof) =
        try_prove_nat_shifted_le_from_hyp(&le_lhs, &le_rhs, &goal_rhs_core, goal_rhs_off, hyps)
    {
        return Some(proof);
    }

    // 3. Offset-combination (bounded slice B): hypothesis `Nat.le HL HR` whose
    //    LHS shares a symbolic core with the goal LHS, both RHS concrete
    //    literals. Covers `n < c1 ⊢ n + k <|≤ c2` (T2 family).
    try_prove_nat_le_offset_from_hyp(&le_lhs, &le_rhs, hyps)
}

/// Matched-symbolic-core shifted inequality: prove goal `Nat.le GL GR` where
/// `GL = cl + k_l`, `GR = cr + k_r` from a hypothesis `Nat.le HL HR` where
/// `HL = cl + h_l`, `HR = cr + h_r` — i.e. both goal sides share the symbolic
/// core (`cl`, `cr`) of the corresponding hypothesis side.
///
/// **Validity (over ℕ, for all `cl, cr ≥ 0`).** From `cl + h_l ≤ cr + h_r` the
/// goal `cl + k_l ≤ cr + k_r` follows iff `k_l - k_r ≤ h_l - h_r` as integers
/// (the goal slack `k_r - k_l` is at least the hypothesis slack `h_r - h_l`).
/// The hypothesis is *tight* at `cl = 0, cr = h_r - h_l + (cl-side)`… more
/// precisely: adding the constant `(k_l - h_l)` to both sides of the hypothesis
/// gives `cl + k_l ≤ cr + h_r + (k_l - h_l)`, and the goal RHS `cr + k_r`
/// dominates that endpoint exactly when `k_r ≥ h_r + (k_l - h_l)`, i.e. the
/// validity condition. No instantiation of `cl`/`cr` is needed — the proof is
/// uniform in the cores.
///
/// **Construction (requires `k_l ≥ h_l`, the supported padding scheme).**
///   1. `c = k_l - h_l ≥ 0`.
///   2. `Nat.add_le_add_right HL HR hyp c : Nat.le (HL + c) (HR + c)`.
///      `HL + c = cl + h_l + c` is def-eq to `cl + k_l = GL`.
///      `HR + c = cr + h_r + c`, whose offset on `cr` is `h_r + c`.
///   3. Weaken the RHS upper endpoint from `cr + (h_r + c)` up to `cr + k_r`
///      via `Nat.le.step^(k_r - (h_r + c))` (needs `k_r ≥ h_r + c`, which the
///      validity condition guarantees for `c = k_l - h_l`).
///
/// Returns `None` (fail closed) when `k_l < h_l` (out-of-scope padding
/// direction) or the integer-slack condition fails — both leave the goal for
/// the FM/SMT path and, ultimately, a closed failure. Every synthesized term is
/// re-checked by `state.close_goal`, so a wrong match is rejected, never
/// trusted. The FALSE goal `a ≤ b ⊢ a + 2 ≤ b` has `k_l=2, k_r=0, h_l=h_r=0`,
/// so `c=2` and `k_r (0) < h_r + c (2)` → `None`; the FALSE `a ≤ b ⊢ b + 1 ≤ a`
/// has mismatched cores (goal LHS core `b` ≠ hyp LHS core `a`) → `None`.
fn try_prove_nat_shifted_le_from_hyp(
    goal_lhs: &Expr,
    _goal_rhs: &Expr,
    goal_rhs_core: &Expr,
    goal_rhs_off: u64,
    hyps: &[(Expr, Expr)],
) -> Option<Expr> {
    let (goal_lhs_core, k_l) = split_core_offset(goal_lhs)?;
    let k_r = goal_rhs_off;

    // Require a genuine symbolic RHS core: the concrete-RHS shape is PATH 3's
    // job, and a concrete LHS+RHS is the goal-only path's.
    if eval_nat_expr(goal_rhs_core).is_some() {
        return None;
    }

    for (hyp_fvar, hyp_ty) in hyps {
        let Some(NatLeGoal {
            le_lhs: h_lhs,
            le_rhs: h_rhs,
        }) = normalize_nat_comparison(hyp_ty)
        else {
            continue;
        };
        let Some((h_lhs_core, h_l)) = split_core_offset(&h_lhs) else {
            continue;
        };
        let Some((h_rhs_core, h_r)) = split_core_offset(&h_rhs) else {
            continue;
        };
        // Both sides must share their symbolic core with the goal.
        if h_lhs_core != goal_lhs_core || &h_rhs_core != goal_rhs_core {
            continue;
        }

        // Supported padding scheme: c = k_l - h_l >= 0.
        if k_l < h_l {
            continue;
        }
        let c = k_l - h_l;

        // Validity: after padding, the hypothesis RHS offset is h_r + c; the goal
        // RHS offset k_r must dominate it (goal slack >= hyp slack).
        let padded_rhs_off = h_r.checked_add(c)?;
        if k_r < padded_rhs_off {
            continue; // goal not provable from this hypothesis; fail closed.
        }
        let rhs_steps = k_r - padded_rhs_off;

        // Step 2: pad the hypothesis on the right by `c`.
        //   Nat.add_le_add_right HL HR hyp c : Nat.le (HL + c) (HR + c)
        // HL + c is def-eq to `goal_lhs` (cl + k_l); HR + c is `cr + (h_r + c)`.
        let padded = if c == 0 {
            // No padding needed: the hypothesis already has LHS offset k_l.
            hyp_fvar.clone()
        } else {
            let add_le_add_right = Expr::const_(Name::from_string("Nat.add_le_add_right"), vec![]);
            Expr::apps(
                add_le_add_right,
                [
                    h_lhs.clone(),
                    h_rhs.clone(),
                    hyp_fvar.clone(),
                    Expr::nat_lit(c),
                ],
            )
        };

        // The `padded` proof has type `Nat.le GL (cr + padded_rhs_off)` (def-eq).
        // Weaken the upper endpoint `rhs_steps` times up to `cr + k_r = GR`.
        let upper = if padded_rhs_off == 0 {
            goal_rhs_core.clone()
        } else {
            nat_add(goal_rhs_core.clone(), Expr::nat_lit(padded_rhs_off))
        };
        return Some(build_le_step_from(&padded, goal_lhs, &upper, rhs_steps));
    }
    None
}

/// Bounded slice B: prove goal `Nat.le GL GR` from a hypothesis `Nat.le HL HR`
/// where `GL = core + ga`, `HL = core + ha` share a symbolic core and `HR`,
/// `GR` are concrete literals `hr`, `gr`.
///
/// Validity (over ℕ, for all `core ≥ 0`): `core + ha ≤ hr ⟹ core + ga ≤ gr`
/// holds iff `ga - ha ≤ gr - hr` (the strongest case is `core = hr - ha`).
///
/// Construction picks `c = max(0, ga - ha) ≥ 0` and builds:
///   1. `Nat.add_le_add_right HL HR h c : Nat.le (HL + c) (HR + c)`.
///      `HL + c = core + ha + c` is def-eq to `core + ga` (= GL) when `c = ga - ha`,
///      and to a `≤ GL` endpoint we then weaken from when `c = 0` (ga ≤ ha).
///   2. weaken the LHS endpoint down to `GL` (when `ga ≤ ha + c`) — handled by
///      threading the proof through the shared core: we re-anchor on `GL` via
///      `Nat.le.refl`/`Nat.le_trans` only in the `ga < ha` arm.
///   3. weaken the RHS literal `hr + c` up to `gr` via `Nat.le.step` (needs
///      `gr ≥ hr + c`, which the validity bound guarantees for the chosen `c`).
///
/// We only synthesize when `c` exists with `ga ≤ ha + c` and `hr + c ≤ gr`,
/// i.e. `max(0, ga - ha) ≤ gr - hr`. Otherwise return `None` and fail closed.
/// Every term is re-checked by `close_goal`, so a wrong reconstruction is
/// rejected rather than trusted.
fn try_prove_nat_le_offset_from_hyp(
    goal_lhs: &Expr,
    goal_rhs: &Expr,
    hyps: &[(Expr, Expr)],
) -> Option<Expr> {
    // Goal RHS must be a concrete literal.
    let gr = eval_nat_expr(goal_rhs)?;
    let (goal_core, ga) = split_core_offset(goal_lhs)?;
    // Require a genuine symbolic core (otherwise the goal-only path handles it).
    if eval_nat_expr(goal_lhs).is_some() {
        return None;
    }

    for (hyp_fvar, hyp_ty) in hyps {
        let Some(NatLeGoal {
            le_lhs: h_lhs,
            le_rhs: h_rhs,
        }) = normalize_nat_comparison(hyp_ty)
        else {
            continue;
        };
        let Some(hr) = eval_nat_expr(&h_rhs) else {
            continue;
        };
        let Some((h_core, ha)) = split_core_offset(&h_lhs) else {
            continue;
        };
        // Shared symbolic core between hypothesis LHS and goal LHS.
        if h_core != goal_core {
            continue;
        }

        // Validity as integers: ga - ha <= gr - hr.
        let d = i128::from(ga) - i128::from(ha); // ga - ha
        let slack = i128::from(gr) - i128::from(hr); // gr - hr
        if d > slack {
            continue; // goal not provable from this hypothesis; fail closed.
        }

        // Only the c = max(0, d) >= 0 padding scheme is supported here.
        // c must satisfy ga <= ha + c (i.e. c >= d) and hr + c <= gr (c <= slack).
        // Pick c = max(0, d). Need c <= slack.
        let c_i = d.max(0);
        if c_i > slack {
            // ga < ha and gr < hr: needs hypothesis-side cancellation, not the
            // non-negative padding scheme. Out of scope; fail closed.
            continue;
        }
        let c = u64::try_from(c_i).ok()?;

        // Step 1: pad the hypothesis on the right by `c`.
        //   Nat.add_le_add_right HL HR hyp c : Nat.le (HL + c) (HR + c)
        // HL + c is def-eq to `core + (ha + c)`; with c = ga - ha (when ga >= ha)
        // this is exactly `core + ga = GL`.
        let add_le_add_right = Expr::const_(Name::from_string("Nat.add_le_add_right"), vec![]);
        let c_lit = Expr::nat_lit(c);
        let padded = Expr::apps(
            add_le_add_right,
            [h_lhs.clone(), h_rhs.clone(), hyp_fvar.clone(), c_lit],
        );
        // Endpoints of `padded` as concrete offsets on the shared core:
        //   lhs offset = ha + c, rhs literal = hr + c.
        let padded_lhs_off = ha.checked_add(c)?;
        let padded_rhs_val = hr.checked_add(c)?;

        // Build `Nat.le (core + ga) (core + padded_lhs_off)` chained with padded
        // to reach `Nat.le GL (hr + c)`, then weaken the RHS up to `gr`.
        //
        // When ga == padded_lhs_off (the ga >= ha arm with c = ga - ha), the
        // padded LHS already equals GL, so no LHS weakening is needed.
        let padded_lhs = nat_add(goal_core.clone(), Expr::nat_lit(padded_lhs_off));

        // Re-anchor the LHS at GL if needed (ga <= padded_lhs_off).
        let (proof_le_padded_rhs, _cur_lhs) = if ga == padded_lhs_off {
            (padded, padded_lhs.clone())
        } else if ga < padded_lhs_off {
            // GL = core + ga, padded_lhs = core + padded_lhs_off, ga < off.
            // q : Nat.le GL padded_lhs  via Nat.le.step weakening from GL.
            let gl = nat_add(goal_core.clone(), Expr::nat_lit(ga));
            let q = build_le_via_steps(&gl, padded_lhs_off - ga);
            // Nat.le_trans GL padded_lhs (hr+c) q padded : Nat.le GL (hr+c)
            let le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);
            let combined = Expr::apps(
                le_trans,
                [
                    gl.clone(),
                    padded_lhs.clone(),
                    Expr::nat_lit(padded_rhs_val),
                    q,
                    padded,
                ],
            );
            (combined, gl)
        } else {
            // ga > padded_lhs_off cannot happen since padded_lhs_off = ha + c >= ga.
            continue;
        };

        // Step 3: weaken the RHS literal from `hr + c` up to `gr`.
        let rhs_steps = gr.checked_sub(padded_rhs_val)?;
        // The current proof has type `Nat.le GL (hr + c)`; weaken the upper
        // endpoint `rhs_steps` times to reach `Nat.le GL gr`.
        let gl_expr = nat_add(goal_core.clone(), Expr::nat_lit(ga));
        let upper = Expr::nat_lit(padded_rhs_val);
        return Some(build_le_step_from(
            &proof_le_padded_rhs,
            &gl_expr,
            &upper,
            rhs_steps,
        ));
    }
    None
}

/// Weaken a hypothesis proof `hyp : Nat.le lhs upper` by `steps`, giving
/// `Nat.le lhs (Nat.succ^steps upper)` via `@Nat.le.step lhs · ·` applications.
fn build_le_step_from(hyp: &Expr, lhs: &Expr, upper: &Expr, steps: u64) -> Expr {
    let le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let mut proof = hyp.clone();
    let mut current_upper = upper.clone();
    for _ in 0..steps {
        proof = Expr::apps(le_step.clone(), [lhs.clone(), current_upper.clone(), proof]);
        current_upper = Expr::app(succ.clone(), current_upper);
    }
    proof
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nat_var(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    #[test]
    fn test_split_core_offset_succ() {
        let n = nat_var("n");
        let succ_n = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            n.clone(),
        );
        let (core, off) = split_core_offset(&succ_n).expect("succ n splits");
        assert_eq!(core, n);
        assert_eq!(off, 1);
    }

    #[test]
    fn test_split_core_offset_add_literal() {
        let n = nat_var("n");
        let e = nat_add(n.clone(), Expr::nat_lit(2));
        let (core, off) = split_core_offset(&e).expect("n + 2 splits");
        assert_eq!(core, n);
        assert_eq!(off, 2);
    }

    #[test]
    fn test_split_core_offset_bare_literal() {
        let (core, off) = split_core_offset(&Expr::nat_lit(5)).expect("literal splits");
        assert_eq!(core, Expr::nat_lit(0));
        assert_eq!(off, 5);
    }

    /// Build an `@LE.le Nat inst a b` goal (the typeclass surface form).
    fn nat_le_tc(a: Expr, b: Expr) -> Expr {
        let inst = nat_var("instLENat");
        Expr::apps(
            Expr::const_(Name::from_string("LE.le"), vec![]),
            [nat_var("Nat"), inst, a, b],
        )
    }

    /// Build an `@LT.lt Nat inst a b` goal.
    fn nat_lt_tc(a: Expr, b: Expr) -> Expr {
        let inst = nat_var("instLTNat");
        Expr::apps(
            Expr::const_(Name::from_string("LT.lt"), vec![]),
            [nat_var("Nat"), inst, a, b],
        )
    }

    #[test]
    fn test_shifted_le_a_plus_1_le_b_plus_1_from_a_le_b() {
        // (h : a ≤ b) ⊢ a + 1 ≤ b + 1  — the h1 shape that PATH 2 cannot reach.
        let a = nat_var("a");
        let b = nat_var("b");
        let hyp_ty = nat_le_tc(a.clone(), b.clone());
        let hyp_fvar = nat_var("h");
        let goal = nat_le_tc(
            nat_add(a.clone(), Expr::nat_lit(1)),
            nat_add(b.clone(), Expr::nat_lit(1)),
        );
        let proof = try_prove_nat_inequality_direct_with_hyps(&goal, &[(hyp_fvar, hyp_ty)]);
        assert!(
            proof.is_some(),
            "a ≤ b ⊢ a + 1 ≤ b + 1 must synthesize a candidate term"
        );
    }

    #[test]
    fn test_shifted_le_a_plus_3_le_b_plus_3_from_a_le_b() {
        // (h : a ≤ b) ⊢ a + 3 ≤ b + 3.
        let a = nat_var("a");
        let b = nat_var("b");
        let hyp_ty = nat_le_tc(a.clone(), b.clone());
        let hyp_fvar = nat_var("h");
        let goal = nat_le_tc(
            nat_add(a.clone(), Expr::nat_lit(3)),
            nat_add(b.clone(), Expr::nat_lit(3)),
        );
        let proof = try_prove_nat_inequality_direct_with_hyps(&goal, &[(hyp_fvar, hyp_ty)]);
        assert!(
            proof.is_some(),
            "a ≤ b ⊢ a + 3 ≤ b + 3 must synthesize a candidate term"
        );
    }

    #[test]
    fn test_shifted_le_a_plus_1_le_b_from_a_lt_b() {
        // (h : a < b) ⊢ a + 1 ≤ b  — the h4 shape; lt-hyp normalizes to a+1 ≤ b.
        let a = nat_var("a");
        let b = nat_var("b");
        let hyp_ty = nat_lt_tc(a.clone(), b.clone());
        let hyp_fvar = nat_var("h");
        let goal = nat_le_tc(nat_add(a.clone(), Expr::nat_lit(1)), b.clone());
        let proof = try_prove_nat_inequality_direct_with_hyps(&goal, &[(hyp_fvar, hyp_ty)]);
        assert!(
            proof.is_some(),
            "a < b ⊢ a + 1 ≤ b must synthesize a candidate term"
        );
    }

    #[test]
    fn test_shifted_le_false_a_plus_2_le_b_returns_none() {
        // FALSE: (h : a ≤ b) ⊢ a + 2 ≤ b. k_l=2,k_r=0,h_l=h_r=0 → c=2,
        // k_r (0) < h_r + c (2) → None. Must NOT synthesize.
        let a = nat_var("a");
        let b = nat_var("b");
        let hyp_ty = nat_le_tc(a.clone(), b.clone());
        let hyp_fvar = nat_var("h");
        let goal = nat_le_tc(nat_add(a.clone(), Expr::nat_lit(2)), b.clone());
        let proof = try_prove_nat_inequality_direct_with_hyps(&goal, &[(hyp_fvar, hyp_ty)]);
        assert!(
            proof.is_none(),
            "FALSE goal a ≤ b ⊢ a + 2 ≤ b must not synthesize a term"
        );
    }

    #[test]
    fn test_shifted_le_false_b_plus_1_le_a_returns_none() {
        // FALSE: (h : a ≤ b) ⊢ b + 1 ≤ a. Goal LHS core `b` ≠ hyp LHS core `a`
        // → core mismatch → None.
        let a = nat_var("a");
        let b = nat_var("b");
        let hyp_ty = nat_le_tc(a.clone(), b.clone());
        let hyp_fvar = nat_var("h");
        let goal = nat_le_tc(nat_add(b.clone(), Expr::nat_lit(1)), a.clone());
        let proof = try_prove_nat_inequality_direct_with_hyps(&goal, &[(hyp_fvar, hyp_ty)]);
        assert!(
            proof.is_none(),
            "FALSE goal a ≤ b ⊢ b + 1 ≤ a must not synthesize a term"
        );
    }

    #[test]
    fn test_shifted_le_no_hyp_a_plus_1_le_b_plus_1_returns_none() {
        // FALSE without a hypothesis: ⊢ a + 1 ≤ b + 1 (distinct cores a, b, no
        // hyp relating them). Goal-only path sees distinct cores → None, and the
        // shifted-from-hyp arm has no hypothesis → None.
        let a = nat_var("a");
        let b = nat_var("b");
        let goal = nat_le_tc(
            nat_add(a.clone(), Expr::nat_lit(1)),
            nat_add(b.clone(), Expr::nat_lit(1)),
        );
        let proof = try_prove_nat_inequality_direct_with_hyps(&goal, &[]);
        assert!(
            proof.is_none(),
            "no-hyp a + 1 ≤ b + 1 (distinct cores) must not synthesize a term"
        );
    }

    #[test]
    fn test_direct_false_inequality_returns_none() {
        // n > n + 1  ->  Nat.le (n+1+1) n  ->  lhs_off=2 > rhs_off=0  -> None
        let n = nat_var("n");
        let n_plus_1 = nat_add(n.clone(), Expr::nat_lit(1));
        let gt = super::super::tc_app::nat_lt_tc(n_plus_1, n); // n+1 < n  (false)
        assert!(
            try_prove_nat_inequality_direct(&gt).is_none(),
            "false inequality must not synthesize a term"
        );
    }
}
