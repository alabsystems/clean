// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Goal reconstruction from linear **Nat equality hypotheses**.
//!
//! ## The gap this closes
//!
//! omega's certified constraint solver already *detects* unsatisfiability for
//! problems whose witness uses equality hypotheses (the equality solver in
//! `omega_tactic::equality_solver` substitutes `±1`-coefficient equalities out
//! of the system). But the proof-*reconstruction* path
//! (`build_mathverse_proof` / the Farkas-with-goal builder) only knows how to
//! thread `≤` / `<` hypotheses. Given an equality hypothesis it falls back to
//! returning the raw hypothesis fvar, whose type is the hypothesis itself, so
//! `state.close_goal` rejects it (a fail-closed type mismatch) and omega
//! errors. The reproduced failures were `(h : a = 2) ⊢ a + 1 = 3`,
//! `(h : a + b = 5) (h2 : a = 2) ⊢ b = 3`, `… ⊢ b ≤ 3`, and `(h : a = 2) ⊢ a ≠ 3`.
//!
//! ## Construction (substitute the equality hyps, then close the residual)
//!
//! 1. **Pin variables.** Each equality hypothesis is parsed to a linear form.
//!    Iteratively, whenever a hypothesis — after substituting the
//!    already-pinned variables — has the shape `(constant) + 1·v = (constant)`
//!    (exactly one free atom, coefficient `+1`), the atom `v` is pinned to the
//!    ground value `rhs - lhs_const`, and a kernel proof `pf_v : v = value` is
//!    synthesized (directly when the hyp already reads `v = value`, or via
//!    `Nat.add_left_cancel` / `Nat.add_right_cancel` when a literal addend
//!    remains). Every pin proof is built from the original hypothesis fvars and
//!    foundational constants only.
//! 2. **Substitute into the goal.** Each pinned `v` is rewritten to its literal
//!    value throughout the goal, lifting every single-occurrence rewrite with
//!    `congrArg motive pf_v` threaded by `Eq.trans` (the same engine
//!    `arith_linarith_nat_eq` uses). This yields a proof that the *original*
//!    goal proposition is propositionally equal (as a `Prop`, via `Eq` on the
//!    relation arguments) to the **substituted** goal, whose free variables are
//!    now literals.
//! 3. **Close the residual.** The substituted goal is closed by the existing
//!    structural provers (`try_prove_nat_inequality_direct_with_hyps`,
//!    recursively; ground equalities/inequalities/`Nat.sub` shapes), or — for a
//!    ground `≠` goal — by `Nat.noConfusion` on the impossible literal equality.
//!    A `congrArg`/`Eq.mpr` cast transports that residual proof back to the
//!    original goal type.
//!
//! ## Soundness
//!
//! Fail-closed and axiom-free. The pins are only believed when the synthesized
//! `pf_v` actually type-checks (it is rebuilt from the hyp fvars and re-checked
//! by the caller's `state.close_goal` + `add_decl`). The substitution proof is a
//! `congrArg`/`Eq.trans` chain; the residual proof is produced by an existing
//! sound prover or `Nat.noConfusion`. A FALSE goal leaves a FALSE residual
//! (e.g. `2 + 1 = 4`, `2 ≠ 2`), for which every residual closer returns `None`
//! (or, for `≠`, the literals are equal so `noConfusion` is inapplicable), so
//! the whole builder returns `None` and omega fails closed. No bogus term is
//! ever emitted for a false goal. Every constant used (`Eq.refl`, `Eq.symm`,
//! `Eq.trans`, `congrArg`, `Eq.mpr`, `Nat.add_left_cancel`,
//! `Nat.add_right_cancel`, `Nat.noConfusion`, `Nat.add`) is a foundational
//! prelude theorem / recursor — zero domain-specific axioms.

use std::collections::HashMap;

use clean_kernel::expr::{BinderInfo, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

use super::arith_linarith_nat_eq::{match_nat_eq, parse_nat_linear_form};
use super::decide_eq_noconfusion::build_noconfusion_ne_proof;
use super::nat_expr_eval::eval_nat_expr;

/// A variable pinned to a concrete ground value by the equality hypotheses,
/// together with a kernel proof of `atom = value`.
struct Pin {
    /// The pinned atom expression (typically an `Expr::fvar`).
    atom: Expr,
    /// Its ground value.
    value: u64,
    /// Proof term of type `@Eq Nat atom <value-literal>`.
    proof: Expr,
}

/// Attempt to prove a Nat goal by substituting the linear equality hypotheses.
///
/// Returns a candidate proof of the ORIGINAL `target` (the caller re-checks it
/// with `state.close_goal`). Returns `None` whenever any precondition fails, so
/// the caller falls through and ultimately fails closed.
///
/// REQUIRES: `target` is the current goal type; each `hyps[i]` is
///   `(fvar_expr, hyp_type)` from the goal's local context.
/// ENSURES: On `Some(e)`, `e` is intended to have type `target`; soundness is
///   guaranteed by the caller's kernel re-check, not by this function.
/// ENSURES: On `None`, the goal could not be reconstructed via equality
///   substitution — in particular every FALSE goal yields `None`.
pub(crate) fn try_prove_goal_via_eq_hyps(
    target: &Expr,
    hyps: &[(Expr, Expr)],
    env: Option<&Environment>,
) -> Option<Expr> {
    // Collect linear Nat equality hypotheses.
    let mut eq_hyps: Vec<(Expr, Expr, Expr)> = Vec::new(); // (proof, lhs, rhs)
    for (fvar, ty) in hyps {
        if let Some((l, r)) = match_nat_eq(ty) {
            eq_hyps.push((fvar.clone(), l, r));
        }
    }
    if eq_hyps.is_empty() {
        return None;
    }

    let pins = pin_variables(&eq_hyps);
    if pins.is_empty() {
        return None;
    }

    // Dispatch on the goal head. Equality and disequality goals are closed with
    // pure Nat-level `Eq` terms (no `Prop`-level rewriting); inequality goals
    // are closed by substituting the pins into the goal proposition and
    // transporting the residual proof back with `Eq.mpr` (#omega-eq).
    if match_nat_eq(target).is_some() {
        return prove_eq_goal_via_pins(target, &pins);
    }
    if match_nat_ne(target).is_some() {
        return prove_ne_goal_via_pins(target, &pins, env?);
    }
    prove_relation_goal_via_pins(target, &pins, hyps)
}

/// Prove a disequality goal `¬(a = k)` / `a ≠ k` (`a` a Nat variable, `k` a
/// literal) from a **bounding inequality hypothesis** whose range excludes `k`.
///
/// This is the goal-side of the negated-relation gap: e.g. `(h : a < 3) ⊢ ¬(a = 5)`.
/// The goal `¬(a = k)` is `(a = k) → False`; we build the term
///
/// ```text
/// fun (heq : @Eq Nat a k) =>
///   -- Eq.subst rewrites the hypothesis `h : R(a)` to `h' : R(k)` (a false
///   -- ground Nat inequality), then a `Nat.lt_irrefl`-based refutation gives False.
///   false_of (@Eq.subst Nat (fun x => R(x)) a k heq h)
/// ```
///
/// The intro'd `heq` is the only new binder; substituting it into the bounding
/// hypothesis yields a *ground* false relation (`5 < 3`, `5 ≤ 2`, …) which the
/// shared ground-`Nat.le` refuter (`derive_false_from_contradictory_le`)
/// discharges. Every constant used (`Eq.subst`, `Nat.le_of_succ_le_succ`,
/// `Nat.lt_irrefl`, `Nat.not_succ_lt_zero`) is a foundational prelude theorem —
/// zero domain-specific axioms. The lambda body has type `False` directly, which
/// is exactly the codomain of `(a = k) → False`.
///
/// Soundness: a candidate is only produced when the substituted hypothesis is a
/// genuinely false ground inequality (`c1 > c2` in `Nat.le (core+c1) (core+c2)`
/// with `core` ground). If `k` is actually consistent with the bound (the goal
/// `¬(a = k)` would be FALSE), no hypothesis substitutes to a false ground
/// relation, so this returns `None` and the caller fails closed. The assembled
/// term is re-checked by `state.close_goal`, the trusted gate.
///
/// REQUIRES: `target` is the current goal type; each `hyps[i]` is
///   `(fvar_expr, hyp_type)` from the goal's local context.
/// ENSURES: On `Some(e)`, `e` is intended to have type `target` (caller
///   re-checks). On `None`, no bounding hypothesis refutes `a = k`.
pub(crate) fn try_prove_not_eq_via_bound_hyp(target: &Expr, hyps: &[(Expr, Expr)]) -> Option<Expr> {
    // Goal must be `¬(a = k)` (surface `Not (Eq …)`) or `Ne a k`; `a` a Nat
    // fvar, `k` a literal.
    let (a, k) = match_not_nat_eq(target).or_else(|| match_nat_ne(target))?;
    if !matches!(a.kind(), ExprKind::FVar(_)) {
        return None;
    }
    let kv = eval_nat_expr(&k)?;
    let k_lit = Expr::nat_lit(kv);

    // Find a hypothesis that, after `a := k`, becomes a false ground `Nat`
    // inequality, and build its `False` proof.
    for (hf, hty) in hyps {
        // The hypothesis must mention `a` and be a Nat comparison whose `a := k`
        // instance is a false `Nat.le lhs_val rhs_val` (with `lhs_val > rhs_val`).
        let Some((lhs_val, rhs_val)) = substituted_hyp_false_nat_le(hty, &a, &k_lit) else {
            continue;
        };

        // motive : Nat → Prop, `fun x => hty[a := x]`. Replace ALL occurrences
        // of `a` with the fresh binder (bvar 0) so `Eq.subst` rewrites every one.
        let mut occurred = false;
        let motive_body = subst_all(hty, &a, &Expr::bvar(0), &mut occurred);
        if !occurred {
            continue;
        }
        let motive = Expr::lam(BinderInfo::Default, nat(), motive_body);

        // h' : hty[a := k]  via  @Eq.subst Nat motive a k heq h.
        // `heq` is the intro'd binder (bvar 0 inside the lambda we build below).
        let heq = Expr::bvar(0);
        let eq_subst = Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        );
        let h_subst = Expr::apps(
            eq_subst,
            [nat(), motive, a.clone(), k_lit.clone(), heq, hf.clone()],
        );

        // `h_subst : hty[a:=k]` is def-eq to the false `Nat.le lhs_val rhs_val`
        // (`lhs_val > rhs_val`). Refute it with the shared `Nat.lt_irrefl`-based
        // ground refuter, which the kernel accepts up to that def-eq.
        let false_proof = super::arith_linarith_close::derive_false_from_contradictory_le(
            h_subst, lhs_val, rhs_val,
        )?;

        // fun (heq : @Eq Nat a k) => false_proof  :  (a = k) → False  ≡  ¬(a = k).
        let eq_ak = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat(), a.clone(), k_lit.clone()],
        );
        return Some(Expr::lam(BinderInfo::Default, eq_ak, false_proof));
    }
    None
}

/// Match `¬(@Eq Nat a b)` (surface `Not (Eq Nat a b)`) and return `(a, b)`.
fn match_not_nat_eq(target: &Expr) -> Option<(Expr, Expr)> {
    let head = target.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if name.to_string() != "Not" {
        return None;
    }
    let args = target.get_app_args();
    if args.len() != 1 {
        return None;
    }
    let (ty, l, r) = match_eq_app(args[0])?;
    if !is_nat(&ty) {
        return None;
    }
    Some((l, r))
}

/// Match `@Eq ty a b` and return `(ty, a, b)`.
fn match_eq_app(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let head = expr.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if name.to_string() != "Eq" {
        return None;
    }
    let args = expr.get_app_args();
    if args.len() != 3 {
        return None;
    }
    Some((args[0].clone(), args[1].clone(), args[2].clone()))
}

/// If substituting `a := k_lit` into the Nat comparison hypothesis `hty` yields a
/// FALSE ground inequality, return the `(lhs_val, rhs_val)` (with
/// `lhs_val > rhs_val`) of the equivalent false `Nat.le lhs_val rhs_val` that the
/// `Nat.lt_irrefl` refuter consumes.
///
/// Handled hypothesis shapes (all Nat), with `u = lhs[a:=k]`, `v = rhs[a:=k]`:
/// - `u ≤ v` false ⟺ `u > v`  → `Nat.le u v`.
/// - `u < v` false ⟺ `u ≥ v`  → `Nat.le (u+1) v` (`<` is `Nat.le (succ …) …`).
/// - `u ≥ v` (= `v ≤ u`) false ⟺ `v > u` → `Nat.le v u`.
/// - `u > v` (= `v < u`) false ⟺ `v ≥ u` → `Nat.le (v+1) u`.
///
/// Returns `None` unless BOTH substituted sides evaluate to ground literals and
/// the relation is genuinely false — so a consistent bound (goal would be false)
/// yields `None` and the caller fails closed.
fn substituted_hyp_false_nat_le(hty: &Expr, a: &Expr, k_lit: &Expr) -> Option<(u64, u64)> {
    // (ty, lhs, rhs, is_strict, swap_sides)
    let parsed = if let Some((ty, l, r)) = super::match_le(hty) {
        (ty, l, r, false, false)
    } else if let Some((ty, l, r)) = super::match_lt(hty) {
        (ty, l, r, true, false)
    } else if let Some((ty, l, r)) = super::match_ge(hty) {
        // a ≥ b ≡ b ≤ a: swap so (lo, hi) = (b, a) with `≤`.
        (ty, l, r, false, true)
    } else if let Some((ty, l, r)) = super::match_gt(hty) {
        // a > b ≡ b < a: swap so (lo, hi) = (b, a) with `<`.
        (ty, l, r, true, true)
    } else {
        return None;
    };
    let (ty, lhs, rhs, strict, swap) = parsed;
    if !is_nat(&ty) {
        return None;
    }
    // Orient to `lo <|≤ hi`.
    let (lo, hi) = if swap { (rhs, lhs) } else { (lhs, rhs) };
    let lo_v = eval_nat_expr(&substitute_value(&lo, a, k_lit))?;
    let hi_v = eval_nat_expr(&substitute_value(&hi, a, k_lit))?;

    // The hypothesis asserts `lo <|≤ hi`. It is FALSE iff:
    //   `≤`:  lo > hi   → refute `Nat.le lo hi`.
    //   `<`:  lo ≥ hi   → refute `Nat.le (lo+1) hi`.
    if strict {
        if lo_v >= hi_v {
            return Some((lo_v.checked_add(1)?, hi_v));
        }
    } else if lo_v > hi_v {
        return Some((lo_v, hi_v));
    }
    None
}

/// Substitute every occurrence of `src` in `e` with `dst` (value substitution).
fn substitute_value(e: &Expr, src: &Expr, dst: &Expr) -> Expr {
    replace_all(e, src, dst)
}

/// Prove an **equality** goal `glhs = grhs` by substituting the pins into each
/// side (Nat-level `congrArg` chains) and closing the ground residual.
///
/// `pf_l : glhs = glhs_sub`, `pf_r : grhs = grhs_sub`, and the residual ground
/// equality `glhs_sub = grhs_sub` is discharged by
/// [`super::arith_linarith_nat_eq::try_prove_nat_equality_direct`] (which has a
/// ground-constant fast path). The result is
/// `Eq.trans pf_l (Eq.trans residual (Eq.symm pf_r)) : glhs = grhs`. A FALSE
/// goal leaves an unequal ground residual, for which the residual prover returns
/// `None`, so we fail closed.
fn prove_eq_goal_via_pins(target: &Expr, pins: &[Pin]) -> Option<Expr> {
    let (glhs, grhs) = match_nat_eq(target)?;
    let (glhs_sub, pf_l) = rewrite_expr_with_pins(&glhs, pins); // glhs = glhs_sub
    let (grhs_sub, pf_r) = rewrite_expr_with_pins(&grhs, pins); // grhs = grhs_sub

    // Residual ground equality `glhs_sub = grhs_sub`.
    let residual_goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), glhs_sub.clone(), grhs_sub.clone()],
    );
    let residual = super::arith_linarith_nat_eq::try_prove_nat_equality_direct(&residual_goal)?;

    // Eq.trans glhs glhs_sub grhs : combine pf_l with (residual ; symm pf_r).
    let symm_r = mk_symm(&grhs, &grhs_sub, &pf_r); // grhs_sub = grhs
    let tail = mk_trans(&glhs_sub, &grhs_sub, &grhs, &residual, &symm_r); // glhs_sub = grhs
    Some(mk_trans(&glhs, &glhs_sub, &grhs, &pf_l, &tail))
}

/// Prove a **disequality** goal `a ≠ b` (`a = b → False`). After substituting
/// the pins, `a`/`b` are ground; if they evaluate to DISTINCT literals we build
/// a ground witness `gnd : a_sub ≠ b_sub` via the shared `Nat.noConfusion`
/// disequality builder (which expands the literals to constructors so the
/// kernel can reduce), then compose
/// `fun (heq : a = b) => gnd (Eq.trans (Eq.symm pf_a) (Eq.trans heq pf_b))`,
/// where `pf_a : a = a_sub`, `pf_b : b = b_sub` are the pin rewrites.
fn prove_ne_goal_via_pins(target: &Expr, pins: &[Pin], env: &Environment) -> Option<Expr> {
    let (a, b) = match_nat_ne(target)?;
    let (a_sub_e, pf_a) = rewrite_expr_with_pins(&a, pins); // a = a_sub
    let (b_sub_e, pf_b) = rewrite_expr_with_pins(&b, pins); // b = b_sub
    let av = eval_nat_expr(&a_sub_e)?;
    let bv = eval_nat_expr(&b_sub_e)?;
    if av == bv {
        return None; // a = b holds — `a ≠ b` is FALSE; fail closed.
    }

    // Ground disequality witness `gnd : @Eq Nat a_sub b_sub → False`.
    let eq_level = Level::succ(Level::zero());
    let gnd = build_noconfusion_ne_proof(env, &nat(), &a_sub_e, &b_sub_e, &eq_level)?;

    // Inside `fun (heq : a = b)`, transport `heq` to `a_sub = b_sub`:
    //   chain = Eq.trans (Eq.symm pf_a) (Eq.trans heq pf_b) : a_sub = b_sub.
    let heq = Expr::bvar(0); // heq : @Eq Nat a b
    let chain = mk_trans(
        &a_sub_e,
        &a,
        &b_sub_e,
        &mk_symm(&a, &a_sub_e, &pf_a),
        &mk_trans(&a, &b, &b_sub_e, &heq, &pf_b),
    );
    let body = Expr::app(gnd, chain); // gnd chain : False

    // fun (heq : @Eq Nat a b) => body  : (a = b) → False  ≡  a ≠ b
    let eq_ab = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), a.clone(), b.clone()],
    );
    Some(Expr::lam(BinderInfo::Default, eq_ab, body))
}

/// Prove an inequality (`≤` / `<` / `≥` / `>`) or other relation goal by
/// substituting the pins into the goal proposition and transporting the
/// residual proof back with `Eq.mpr`.
fn prove_relation_goal_via_pins(
    target: &Expr,
    pins: &[Pin],
    hyps: &[(Expr, Expr)],
) -> Option<Expr> {
    let (substituted, subst_proof) = substitute_pins_into_prop(target, pins)?;
    if substituted == *target {
        return None;
    }
    let residual_proof = close_substituted_goal(&substituted, hyps)?;
    Some(mk_eq_mpr(
        target,
        &substituted,
        &subst_proof,
        &residual_proof,
    ))
}

/// Iteratively pin variables to ground values from the equality hypotheses.
///
/// A hypothesis pins a variable when — after substituting the values of
/// already-pinned variables into both sides — exactly one free atom remains
/// with coefficient `+1` and the other side is ground. Each pin carries a
/// kernel proof `atom = value`.
fn pin_variables(eq_hyps: &[(Expr, Expr, Expr)]) -> Vec<Pin> {
    let mut pins: Vec<Pin> = Vec::new();
    let mut known: HashMap<Expr, u64> = HashMap::new();

    // Bound iterations: each successful pass pins at least one new variable.
    for _ in 0..=eq_hyps.len() {
        let mut progressed = false;
        for (proof, lhs, rhs) in eq_hyps {
            if let Some(pin) = try_pin_from_hyp(proof, lhs, rhs, &known, &pins) {
                if known.insert(pin.atom.clone(), pin.value).is_none() {
                    pins.push(pin);
                    progressed = true;
                }
            }
        }
        if !progressed {
            break;
        }
    }
    pins
}

/// Try to derive a single pin `atom = value` from one equality hypothesis,
/// given the values of already-known variables. Returns `None` if the
/// hypothesis does not pin exactly one fresh variable.
fn try_pin_from_hyp(
    proof: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    known: &HashMap<Expr, u64>,
    pins: &[Pin],
) -> Option<Pin> {
    // Substitute known variables into both sides first (so a hyp like
    // `a + b = 5` becomes pinnable for `b` once `a` is known).
    let lhs_s = substitute_known(lhs, pins);
    let rhs_s = substitute_known(rhs, pins);

    let lf = parse_nat_linear_form(&lhs_s)?;
    let rf = parse_nat_linear_form(&rhs_s)?;

    // Combine to `D = lhs_form - rhs_form` so we can find the single free atom.
    // D must be `1·v + c` (exactly one atom, coefficient +1) with the constant
    // already absorbed: i.e. lf has exactly one atom (coeff +1), rf has none.
    // We orient so the lone atom is on the left.
    let (atom, atom_const, ground_val, on_left) = if lf.coeffs.len() == 1 && rf.coeffs.is_empty() {
        let (atom, &c) = lf.coeffs.iter().next()?;
        if c != 1 {
            return None;
        }
        (atom.clone(), lf.constant, rf.constant, true)
    } else if rf.coeffs.len() == 1 && lf.coeffs.is_empty() {
        let (atom, &c) = rf.coeffs.iter().next()?;
        if c != 1 {
            return None;
        }
        (atom.clone(), rf.constant, lf.constant, false)
    } else {
        return None;
    };

    // Skip if already known.
    if known.contains_key(&atom) {
        return None;
    }

    // value = ground_val - atom_const ; must be non-negative (Nat).
    let value_i = ground_val.checked_sub(atom_const)?;
    let value = u64::try_from(value_i).ok()?;

    // Build the kernel proof `atom = value`.
    let pin_proof = build_pin_proof(proof, lhs, rhs, &atom, atom_const, value, on_left, pins)?;

    Some(Pin {
        atom,
        value,
        proof: pin_proof,
    })
}

/// Build `pf : atom = value` from the hypothesis `proof : lhs = rhs`.
///
/// After substituting the already-known pins, the (oriented) hypothesis side
/// holding the atom reads `atom_const + atom` (or `atom + atom_const`, or just
/// `atom`) and the other side is ground (= `value + atom_const`). We:
///   1. Rewrite the hypothesis with the known pins (so its literal addends are
///      concrete) — via `congrArg` substitution of each pinned variable.
///   2. Strip the literal addend `atom_const` with `Nat.add_left_cancel` /
///      `Nat.add_right_cancel` (when `atom_const > 0`), or use the rewritten
///      hypothesis directly (when `atom_const == 0`).
///   3. Orient so the atom is on the left (`Eq.symm` if the hyp had it on the
///      right).
fn build_pin_proof(
    proof: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    atom: &Expr,
    atom_const: i64,
    value: u64,
    on_left: bool,
    pins: &[Pin],
) -> Option<Expr> {
    // Step 1: rewrite the hypothesis sides with the known pins.
    // h_rw : lhs = rhs  becomes  h_rw' : lhs_sub = rhs_sub
    let (lhs_sub, lhs_eq) = rewrite_expr_with_pins(lhs, pins); // lhs = lhs_sub
    let (rhs_sub, rhs_eq) = rewrite_expr_with_pins(rhs, pins); // rhs = rhs_sub
                                                               // h' : lhs_sub = rhs_sub  via  Eq.symm(lhs_eq) ▸ proof ▸ rhs_eq
                                                               //   = Eq.trans (Eq.symm lhs_eq) (Eq.trans proof rhs_eq)
    let h_sub = mk_trans(
        &lhs_sub,
        lhs,
        &rhs_sub,
        &mk_symm(lhs, &lhs_sub, &lhs_eq),
        &mk_trans(lhs, rhs, &rhs_sub, proof, &rhs_eq),
    );

    // Orient so the atom-bearing side is the LHS: `atom_side = ground_side`.
    // (`ground_side`'s value is only needed for the def-eq reasoning the comments
    // describe; the kernel re-derives it, so we don't read the binding directly.)
    let (atom_side, _ground_side, h_oriented) = if on_left {
        (lhs_sub.clone(), rhs_sub.clone(), h_sub)
    } else {
        (
            rhs_sub.clone(),
            lhs_sub.clone(),
            mk_symm(&lhs_sub, &rhs_sub, &h_sub),
        )
    };

    let value_lit = Expr::nat_lit(value);

    if atom_const == 0 {
        // atom_side is def-eq to `atom`, ground_side def-eq to `value`.
        // `h_oriented : atom_side = ground_side` is def-eq to `atom = value`.
        // Return it as a proof of `atom = value` (close_goal/kernel re-checks).
        return Some(h_oriented);
    }
    let c = u64::try_from(atom_const).ok()?;
    let c_lit = Expr::nat_lit(c);

    // `atom_side` is def-eq to `c + atom` or `atom + c`. Detect which addend
    // orientation the surface used and cancel the matching side. `h_oriented`'s
    // actual type (`<atom_side> = <ground_side>`) is def-eq to the canonical
    // cancellable equation we feed the cancel lemma — `ground_side` evaluates to
    // the same literal as `c + value` / `value + c`, so the kernel app check
    // accepts it, and `close_goal` re-checks the whole term (the soundness gate).
    if cancels_on_left(&atom_side, atom) {
        // c + atom = c + value  ⊢  atom = value   (Nat.add_left_cancel)
        // Nat.add_left_cancel {n m k} (h : n + m = n + k) : m = k.
        let cancel = Expr::const_(Name::from_string("Nat.add_left_cancel"), vec![]);
        Some(Expr::apps(
            cancel,
            [c_lit, atom.clone(), value_lit, h_oriented],
        ))
    } else {
        // atom + c = value + c  ⊢  atom = value   (Nat.add_right_cancel)
        // Nat.add_right_cancel {n m k} (h : n + m = k + m) : n = k.
        let cancel = Expr::const_(Name::from_string("Nat.add_right_cancel"), vec![]);
        Some(Expr::apps(
            cancel,
            [atom.clone(), c_lit, value_lit, h_oriented],
        ))
    }
}

/// Whether the literal addend in `atom_side` sits on the LEFT (`c + atom`, so we
/// cancel on the left) versus the RIGHT (`atom + c`). Defaults to left-cancel
/// when the structure is not a recognizable two-operand `add` — both forms are
/// def-eq up to `Nat.add_comm`, and the kernel re-check is the gate.
fn cancels_on_left(atom_side: &Expr, atom: &Expr) -> bool {
    let args = atom_side.get_app_args();
    if args.len() >= 2 {
        if let ExprKind::Const(op, _) = atom_side.get_app_fn().kind() {
            let op_s = op.to_string();
            if op_s == "Nat.add" || op_s == "HAdd.hAdd" || op_s == "Add.add" {
                let l = args[args.len() - 2];
                let r = args[args.len() - 1];
                // atom on the left => `atom + c` => cancel on the right.
                if l == atom && eval_nat_expr(r).is_some() {
                    return false;
                }
            }
        }
    }
    true
}

/// Substitute the known pins' values into `e` (pure value substitution, no
/// proof) — used to test pinnability.
fn substitute_known(e: &Expr, pins: &[Pin]) -> Expr {
    let mut out = e.clone();
    for pin in pins {
        out = replace_all(&out, &pin.atom, &Expr::nat_lit(pin.value));
    }
    out
}

/// Rewrite `e` by replacing each pinned atom with its literal value, returning
/// `(rewritten, proof : e = rewritten)`. The proof is a `congrArg`/`Eq.trans`
/// chain over the pin equalities.
fn rewrite_expr_with_pins(e: &Expr, pins: &[Pin]) -> (Expr, Expr) {
    let mut current = e.clone();
    let mut proof = mk_refl(e); // e = current
    for pin in pins {
        let value_lit = Expr::nat_lit(pin.value);
        // Replace every occurrence of `pin.atom` one at a time.
        loop {
            let Some((motive, next)) = replace_one(&current, &pin.atom, &value_lit) else {
                break;
            };
            // step : current = next  via congrArg motive pin.proof
            let step = mk_congr_arg(&pin.atom, &value_lit, &motive, &pin.proof);
            proof = mk_trans(e, &current, &next, &proof, &step);
            current = next;
        }
    }
    (current, proof)
}

/// Substitute pinned variables into the GOAL **proposition**, returning the
/// substituted prop and a proof `target_prop = substituted_prop` (an `Eq` over
/// `Prop`, i.e. `@Eq Prop target substituted`). Built by `congrArg`/`Eq.trans`
/// over the pin equalities, lifting each one through the goal expression.
fn substitute_pins_into_prop(target: &Expr, pins: &[Pin]) -> Option<(Expr, Expr)> {
    let mut current = target.clone();
    let mut proof = mk_refl_prop(target); // @Eq Prop target current
    for pin in pins {
        let value_lit = Expr::nat_lit(pin.value);
        loop {
            let Some((motive, next)) = replace_one(&current, &pin.atom, &value_lit) else {
                break;
            };
            // step : current = next  via congrArg (motive : Nat → Prop) pin.proof
            let step = mk_congr_arg_prop(&pin.atom, &value_lit, &motive, &pin.proof);
            proof = mk_trans_prop(target, &current, &next, &proof, &step);
            current = next;
        }
    }
    if current == *target {
        return None;
    }
    Some((current, proof))
}

/// Close the substituted goal (free variables now literals where pinned).
///
/// Delegates to the existing structural inequality/equality prover, or — for a
/// ground `≠` goal — to `Nat.noConfusion`. Returns `None` (fail closed) when the
/// residual goal is false / unsupported.
fn close_substituted_goal(substituted: &Expr, hyps: &[(Expr, Expr)]) -> Option<Expr> {
    // Equality / inequality / Nat.sub shapes: reuse the direct prover. The
    // substituted goal may still reference unpinned hyps (e.g. an inequality
    // hypothesis), so pass the full hyp list through.
    super::arith_linarith_nat_direct::try_prove_nat_inequality_direct_with_hyps(substituted, hyps)
}

/// Match `@Ne Nat a b` (≡ `a ≠ b`) and return `(a, b)`.
fn match_nat_ne(target: &Expr) -> Option<(Expr, Expr)> {
    let head = target.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if name.to_string() != "Ne" {
        return None;
    }
    let args = target.get_app_args();
    if args.len() != 3 {
        return None;
    }
    if !is_nat(args[0]) {
        return None;
    }
    Some((args[1].clone(), args[2].clone()))
}

// ---------------------------------------------------------------------------
// Generic single-occurrence replacement (Nat-typed and Prop-typed motives).
// ---------------------------------------------------------------------------

/// Replace every occurrence of `src` in `e` with `dst` (value substitution).
fn replace_all(e: &Expr, src: &Expr, dst: &Expr) -> Expr {
    if e == src {
        return dst.clone();
    }
    match e.kind() {
        ExprKind::App(f, a) => Expr::app(replace_all(f, src, dst), replace_all(a, src, dst)),
        _ => e.clone(),
    }
}

/// Replace every occurrence of `src` in `e` with `dst`, setting `*occurred` when
/// at least one replacement happened. Recurses through `App` spines (sufficient
/// for the comparison-shaped hypothesis types this module handles).
fn subst_all(e: &Expr, src: &Expr, dst: &Expr, occurred: &mut bool) -> Expr {
    if e == src {
        *occurred = true;
        return dst.clone();
    }
    match e.kind() {
        ExprKind::App(f, a) => Expr::app(
            subst_all(f, src, dst, occurred),
            subst_all(a, src, dst, occurred),
        ),
        _ => e.clone(),
    }
}

/// Replace ONE occurrence of `src` (a Nat-typed sub-term) in `whole`, returning
/// `(motive, whole[src := dst])` where `motive = fun (z : Nat) => whole[that
/// occurrence := z]`. The motive's binder type is always `Nat`; its body type is
/// inferred (`Nat` when `whole` is a Nat term, `Prop` when `whole` is the goal
/// proposition), so the single helper serves both the Nat-level and Prop-level
/// `congrArg` chains.
fn replace_one(whole: &Expr, src: &Expr, dst: &Expr) -> Option<(Expr, Expr)> {
    let mut done1 = false;
    let body = subst_first(whole, src, &Expr::bvar(0), &mut done1);
    if !done1 {
        return None;
    }
    let mut done2 = false;
    let next = subst_first(whole, src, dst, &mut done2);
    let motive = Expr::lam(BinderInfo::Default, nat(), body);
    Some((motive, next))
}

/// Substitute the FIRST (left-most, outer-most) occurrence of `target` in `e`.
fn subst_first(e: &Expr, target: &Expr, repl: &Expr, done: &mut bool) -> Expr {
    if *done {
        return e.clone();
    }
    if e == target {
        *done = true;
        return repl.clone();
    }
    match e.kind() {
        ExprKind::App(f, a) => {
            let nf = subst_first(f, target, repl, done);
            let na = subst_first(a, target, repl, done);
            Expr::app(nf, na)
        }
        _ => e.clone(),
    }
}

// ---------------------------------------------------------------------------
// Kernel term builders.
// ---------------------------------------------------------------------------

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn is_nat(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat")
}

fn nat_add(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// `@Eq.refl Nat a`.
fn mk_refl(a: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), a.clone()],
    )
}

/// `@Eq.refl Prop a` (level for `Prop` is `Sort 0` = level 1 universe arg).
fn mk_refl_prop(a: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [prop(), a.clone()],
    )
}

fn prop() -> Expr {
    Expr::sort(Level::zero())
}

/// `@Eq.symm Nat a b h : b = a`.
fn mk_symm(a: &Expr, b: &Expr, h: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), a.clone(), b.clone(), h.clone()],
    )
}

/// `@Eq.trans Nat a b c h1 h2 : a = c`.
fn mk_trans(a: &Expr, b: &Expr, c: &Expr, h1: &Expr, h2: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [
            nat(),
            a.clone(),
            b.clone(),
            c.clone(),
            h1.clone(),
            h2.clone(),
        ],
    )
}

/// `@Eq.trans Prop a b c h1 h2 : a = c`.
fn mk_trans_prop(a: &Expr, b: &Expr, c: &Expr, h1: &Expr, h2: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [
            prop(),
            a.clone(),
            b.clone(),
            c.clone(),
            h1.clone(),
            h2.clone(),
        ],
    )
}

/// `@congrArg.{1,1} Nat Nat x y f h : f x = f y` where `f : Nat → Nat`.
fn mk_congr_arg(x: &Expr, y: &Expr, f: &Expr, h: &Expr) -> Expr {
    let u = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![u.clone(), u]),
        [nat(), nat(), x.clone(), y.clone(), f.clone(), h.clone()],
    )
}

/// `@congrArg.{1,1} Nat Prop x y f h : f x = f y` where `f : Nat → Prop`.
fn mk_congr_arg_prop(x: &Expr, y: &Expr, f: &Expr, h: &Expr) -> Expr {
    let u = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![u.clone(), u]),
        [nat(), prop(), x.clone(), y.clone(), f.clone(), h.clone()],
    )
}

/// `@Eq.mpr a b (h : a = b) (hb : b) : a` — transport a residual proof of the
/// substituted goal `b` back to the original goal `a`.
fn mk_eq_mpr(a: &Expr, b: &Expr, h_ab: &Expr, hb: &Expr) -> Expr {
    // `Eq.mpr.{u}` with `α β : Sort u`; here `α = a : Prop = Sort 0`, so `u = 0`.
    Expr::apps(
        Expr::const_(Name::from_string("Eq.mpr"), vec![Level::zero()]),
        [a.clone(), b.clone(), h_ab.clone(), hb.clone()],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    fn eq_goal(l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat(), l, r],
        )
    }

    fn ne_goal(l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
            [nat(), l, r],
        )
    }

    #[test]
    fn test_pin_direct_eq_hyp() {
        // h : a = 2  ⊢  a + 1 = 3
        let a = atom("a");
        let h = atom("h");
        let hyp = eq_goal(a.clone(), Expr::nat_lit(2));
        let goal = eq_goal(nat_add(&a, &Expr::nat_lit(1)), Expr::nat_lit(3));
        let r = try_prove_goal_via_eq_hyps(&goal, &[(h, hyp)], None);
        assert!(r.is_some(), "a=2 ⊢ a+1=3 should reconstruct");
    }

    #[test]
    fn test_two_eq_hyps_solve_for_b() {
        // h : a + b = 5, h2 : a = 2  ⊢  b = 3
        let a = atom("a");
        let b = atom("b");
        let h = atom("h");
        let h2 = atom("h2");
        let hyp1 = eq_goal(nat_add(&a, &b), Expr::nat_lit(5));
        let hyp2 = eq_goal(a.clone(), Expr::nat_lit(2));
        let goal = eq_goal(b.clone(), Expr::nat_lit(3));
        let r = try_prove_goal_via_eq_hyps(&goal, &[(h, hyp1), (h2, hyp2)], None);
        assert!(r.is_some(), "a+b=5, a=2 ⊢ b=3 should reconstruct");
    }

    #[test]
    fn test_ne_goal_without_env_fails_closed() {
        // The `≠` residual needs the environment (ground `Nat.noConfusion`
        // witness); without it the solver fails closed. End-to-end `≠` proving
        // is covered by the `clean check` omega tests.
        let a = atom("a");
        let h = atom("h");
        let hyp = eq_goal(a.clone(), Expr::nat_lit(2));
        let goal = ne_goal(a.clone(), Expr::nat_lit(3));
        let r = try_prove_goal_via_eq_hyps(&goal, &[(h, hyp)], None);
        assert!(r.is_none(), "a≠3 needs env; without it must fail closed");
    }

    #[test]
    fn test_false_eq_goal_fails_closed() {
        // h : a = 2  ⊢  a + 1 = 4   (FALSE)
        let a = atom("a");
        let h = atom("h");
        let hyp = eq_goal(a.clone(), Expr::nat_lit(2));
        let goal = eq_goal(nat_add(&a, &Expr::nat_lit(1)), Expr::nat_lit(4));
        let r = try_prove_goal_via_eq_hyps(&goal, &[(h, hyp)], None);
        assert!(r.is_none(), "a=2 ⊢ a+1=4 is FALSE; must fail closed");
    }

    #[test]
    fn test_false_ne_goal_fails_closed() {
        // h : a = 2  ⊢  a ≠ 2   (FALSE — a IS 2)
        let a = atom("a");
        let h = atom("h");
        let hyp = eq_goal(a.clone(), Expr::nat_lit(2));
        let goal = ne_goal(a.clone(), Expr::nat_lit(2));
        let r = try_prove_goal_via_eq_hyps(&goal, &[(h, hyp)], None);
        assert!(r.is_none(), "a=2 ⊢ a≠2 is FALSE; must fail closed");
    }

    #[test]
    fn test_false_solve_b_fails_closed() {
        // h : a + b = 5, h2 : a = 2  ⊢  b = 4   (FALSE — b is 3)
        let a = atom("a");
        let b = atom("b");
        let h = atom("h");
        let h2 = atom("h2");
        let hyp1 = eq_goal(nat_add(&a, &b), Expr::nat_lit(5));
        let hyp2 = eq_goal(a.clone(), Expr::nat_lit(2));
        let goal = eq_goal(b.clone(), Expr::nat_lit(4));
        let r = try_prove_goal_via_eq_hyps(&goal, &[(h, hyp1), (h2, hyp2)], None);
        assert!(r.is_none(), "a+b=5, a=2 ⊢ b=4 is FALSE; must fail closed");
    }
}
