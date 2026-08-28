// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct (goal-driven) proof synthesis for linear **Int** goals.
//!
//! Sibling of [`super::arith_linarith_nat_eq`] (which is `Nat`-only). omega on
//! `Int` previously fell through to `linarith`/`ay_lra` and errored on the whole
//! linear-equality family (`a + 0 = a`, `a + b = b + a`, `-a + a = 0`), on
//! equality-from-`≤`-hypotheses (`a ≥ b, b ≥ a ⊢ a = b`), and on the
//! `False`-from-contradictory-equality-hypotheses case (`a + b = 3, a + b = 5 ⊢
//! False`). This module closes those `Int` gaps.
//!
//! ## Available registered `Int` lemmas (the toolbox)
//!
//! Everything here uses ONLY constants that `Environment::with_prelude()` loads
//! (verified by an env probe) — no new prelude/kernel constant is introduced.
//! The additive/order lemmas relied on are all sorry-free constructive prelude
//! `Declaration::Theorem`s (empty domain-axiom closure): `Int.add_comm`,
//! `Int.add_assoc`, `Int.add_zero`, `Int.zero_add`, `Int.neg_add_self`,
//! `Int.add_neg_self`, `Int.le_antisymm`, plus `Eq.refl` / `Eq.symm` /
//! `Eq.trans` / `congrArg` and (for the `False` case) the shared
//! `Nat.noConfusion`-based `Int` disequality builder in
//! [`super::decide_eq_noconfusion`].
//!
//! DEFERRED (kernel-touching, out of scope): a *literal-coefficient
//! multiplication* equality such as `a + a = 2 * a` needs `Int.two_mul` /
//! `Int.mul_comm` / `Int.right_distrib`, none of which the prelude registers.
//! Registering one would be a kernel change, so this module returns `None` for
//! that shape (omega then fails closed, matching the pre-existing behavior).
//!
//! ## Soundness
//!
//! Fail-closed and axiom-free. Every synthesized term is a candidate that the
//! caller re-checks with `state.close_goal` (`infer_type` + WHNF + `is_def_eq`)
//! and that `add_decl` re-checks on `clean check` — the trusted gate. A false
//! equality (`a + 1 = a`) fails the linear-form DECISION gate below and yields
//! `None`; a false `False`-from-hyps case leaves no contradictory literal pair
//! and yields `None`. No bogus term is ever emitted for a false goal.

use std::collections::HashMap;

use clean_kernel::expr::{BinderInfo, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

/// Canonical linear form of an `Int` expression: per-atom integer coefficients
/// plus a constant. Two expressions are equal as linear `Int` forms iff their
/// `IntForm`s are equal (identical constant AND identical non-zero coefficient
/// per atom).
#[derive(Debug, Clone, Default)]
struct IntForm {
    coeffs: HashMap<Expr, i64>,
    constant: i64,
}

impl IntForm {
    fn add_atom(&mut self, atom: Expr, coeff: i64) {
        *self.coeffs.entry(atom).or_insert(0) += coeff;
    }
    fn normalize(&mut self) {
        self.coeffs.retain(|_, c| *c != 0);
    }
    fn equals(&self, other: &IntForm) -> bool {
        self.constant == other.constant && self.coeffs == other.coeffs
    }
}

/// Parse `e` into an [`IntForm`], or `None` if `e` is not a linear `Int` term.
///
/// Handles the surface `HAdd` / `HSub` / `HMul` / `Neg` spines and the core
/// `Int.add` / `Int.sub` / `Int.mul` / `Int.neg` heads, `Int.ofNat`/`Int.zero`/
/// `Int.one` and `Nat`-literal constants, and a literal-coefficient product
/// `k * atom` / `atom * k`. A symbolic×symbolic product is non-linear → `None`.
fn parse_int_linear_form(e: &Expr) -> Option<IntForm> {
    let mut form = IntForm::default();
    accumulate(e, 1, &mut form)?;
    form.normalize();
    Some(form)
}

fn accumulate(e: &Expr, scale: i64, form: &mut IntForm) -> Option<()> {
    if let Some(v) = eval_int_const(e) {
        form.constant = form.constant.checked_add(scale.checked_mul(v)?)?;
        return Some(());
    }

    let args = e.get_app_args();
    let head = e.get_app_fn();
    if let ExprKind::Const(op, _) = head.kind() {
        let op_s = op.to_string();
        if args.len() >= 2 {
            let lhs = args[args.len() - 2];
            let rhs = args[args.len() - 1];
            // Addition.
            if op_s == "Int.add" || op_s == "HAdd.hAdd" || op_s == "Add.add" {
                accumulate(lhs, scale, form)?;
                return accumulate(rhs, scale, form);
            }
            // Subtraction: a - b  ⟹  a + (-b).
            if op_s == "Int.sub" || op_s == "HSub.hSub" || op_s == "Sub.sub" {
                accumulate(lhs, scale, form)?;
                return accumulate(rhs, scale.checked_neg()?, form);
            }
            // Literal-coefficient multiplication.
            if op_s == "Int.mul" || op_s == "HMul.hMul" || op_s == "Mul.mul" {
                if let Some(rv) = eval_int_const(rhs) {
                    return accumulate(lhs, scale.checked_mul(rv)?, form);
                }
                if let Some(lv) = eval_int_const(lhs) {
                    return accumulate(rhs, scale.checked_mul(lv)?, form);
                }
                // Symbolic × symbolic: non-linear. Fail closed.
                return None;
            }
        }
        // Negation `-x`  (surface `Neg.neg Int inst x` or core `Int.neg x`).
        if (op_s == "Int.neg" || op_s == "Neg.neg") && !args.is_empty() {
            let inner = args[args.len() - 1];
            return accumulate(inner, scale.checked_neg()?, form);
        }
    }

    // Any other symbolic head: a single atom with the carried coefficient.
    form.add_atom(e.clone(), scale);
    Some(())
}

/// Evaluate an `Int` (or wrapped `Nat`) constant expression to its integer
/// value, or `None` if not a ground literal. Handles `Int.ofNat <lit>`,
/// `Int.negSucc <lit>`, `Int.zero`/`Int.one`, bare `Nat` literals and
/// `Nat.zero`/`Nat.succ` chains, and `@OfNat.ofNat _ <lit> _` wrappers.
fn eval_int_const(e: &Expr) -> Option<i64> {
    match e.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => super::arithmetic::big_nat_to_i64(n),
        ExprKind::Const(name, _) => match name.to_string().as_str() {
            "Int.zero" | "Nat.zero" => Some(0),
            "Int.one" | "Nat.one" => Some(1),
            _ => None,
        },
        ExprKind::App(_, _) => {
            let head = e.get_app_fn();
            let args = e.get_app_args();
            let ExprKind::Const(name, _) = head.kind() else {
                return None;
            };
            match name.to_string().as_str() {
                "Int.ofNat" if args.len() == 1 => eval_int_const(args[0]),
                "Int.negSucc" if args.len() == 1 => {
                    Some(eval_int_const(args[0])?.checked_add(1)?.checked_neg()?)
                }
                "Nat.succ" if args.len() == 1 => eval_int_const(args[0])?.checked_add(1),
                // @OfNat.ofNat α n inst  — the value is `n`.
                n if n.contains("OfNat.ofNat") && args.len() >= 2 => eval_int_const(args[1]),
                _ => None,
            }
        }
        _ => None,
    }
}

// ===========================================================================
// Free-variable linear Int equality: `l = r`.
// ===========================================================================

/// Attempt to synthesize a kernel-checked proof for a linear `Int` equality goal
/// `@Eq Int l r`, directly from the goal (no hypotheses).
///
/// Returns `Some(candidate)` ONLY when the two sides have identical `Int` linear
/// forms AND a proof is constructible from the registered additive lemmas;
/// otherwise `None` (the caller falls through / fails closed). A FALSE equality
/// always yields `None` (linear forms differ). The candidate is re-checked by
/// `state.close_goal`.
pub(crate) fn try_prove_int_equality(target: &Expr) -> Option<Expr> {
    let (lhs, rhs) = match_int_eq(target)?;

    // DECISION GATE: provable iff the two linear forms are identical.
    let lf = parse_int_linear_form(&lhs)?;
    let rf = parse_int_linear_form(&rhs)?;
    if !lf.equals(&rf) {
        return None; // false / unequal — fail closed.
    }

    // Reflexivity shortcut (syntactically identical sides).
    if lhs == rhs {
        return Some(mk_refl(&lhs));
    }

    // Dispatch on the recognized provable shapes. The linear-form DECISION GATE
    // above has already established `l` and `r` are equal as linear forms, so any
    // candidate we build here is a proof of a TRUE equality; `close_goal`
    // re-checks the exact term, so a shape mismatch fails closed (not a false
    // proof). Ordered from most specific to most general.
    build_int_eq_proof(&lhs, &rhs)
}

/// Build a proof of the (already-decided-true) `Int` equality `l = r` from the
/// registered additive lemmas, or `None` for an uncovered / deferred shape.
///
/// Covered shapes (the target family + close relatives):
///   * `x + 0 = x`  /  `0 + x = x`  and their mirrors  → `Int.add_zero` /
///     `Int.zero_add` (possibly under `Eq.symm`).
///   * `x + y = y + x`  → `Int.add_comm`.
///   * `-a + a = 0`  /  `a + -a = 0`  and mirrors  → `Int.neg_add_self` /
///     `Int.add_neg_self`.
///   * single-atom def-eq reshapings  → reflexivity (kernel-gated).
fn build_int_eq_proof(lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    // `x + 0 = x` and `0 + x = x` (constant-elimination), either orientation.
    if let Some(p) = try_add_identity(lhs, rhs) {
        return Some(p);
    }
    // `-a + a = 0` / `a + -a = 0` (additive-inverse cancellation), either
    // orientation.
    if let Some(p) = try_neg_cancel(lhs, rhs) {
        return Some(p);
    }
    // `x + y = y + x` (commutation).
    if let (Some((lx, rx)), Some((ly, ry))) = (int_add_children(lhs), int_add_children(rhs)) {
        if lx == ry && rx == ly && lx != rx {
            return Some(mk_add_comm(&lx, &rx));
        }
    }
    // Reflexive fallback ONLY for a genuine def-eq reshaping of a single
    // unit-coefficient atom (constant `0`). A side whose linear form carries an
    // atom coefficient with magnitude `> 1` (e.g. `a + a` ⇒ `{a:2}`, or `2 * a`)
    // is NOT def-eq reflexive and its equality needs a literal-coefficient
    // multiplication lemma the prelude does not register — a DEFERRED,
    // kernel-touching shape. Return `None` for it (fail closed) rather than
    // emitting a bogus `Eq.refl` that would only be caught later by `close_goal`.
    let lf = parse_int_linear_form(lhs)?;
    let all_unit = lf.coeffs.values().all(|c| c.abs() == 1);
    if all_unit && lf.coeffs.len() <= 1 {
        return Some(mk_refl(lhs));
    }
    None
}

/// `x + 0 = x` / `0 + x = x` (and their `Eq.symm` mirrors) via `Int.add_zero` /
/// `Int.zero_add`. Returns `None` if neither side is `atom + 0` / `0 + atom`.
fn try_add_identity(lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    // Forward: `lhs` is `x + 0` or `0 + x` and `rhs == x`.
    if let Some(proof) = add_identity_for(lhs, rhs) {
        return Some(proof);
    }
    // Mirror: `rhs` is `x + 0` / `0 + x` and `lhs == x`; symm the forward proof.
    if let Some(proof) = add_identity_for(rhs, lhs) {
        // proof : rhs = lhs  ⟹  Eq.symm : lhs = rhs.
        return Some(mk_symm(rhs, lhs, &proof));
    }
    None
}

/// If `sum` is `x + 0` or `0 + x` with `x == target`, return a proof `sum =
/// target` (`Int.add_zero x` / `Int.zero_add x`).
fn add_identity_for(sum: &Expr, target: &Expr) -> Option<Expr> {
    let (l, r) = int_add_children(sum)?;
    if eval_int_const(&r) == Some(0) && l == *target {
        // Int.add_zero x : Int.add x 0 = x.
        return Some(Expr::apps(
            Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            [l],
        ));
    }
    if eval_int_const(&l) == Some(0) && r == *target {
        // Int.zero_add x : Int.add 0 x = x.
        return Some(Expr::apps(
            Expr::const_(Name::from_string("Int.zero_add"), vec![]),
            [r],
        ));
    }
    None
}

/// `-a + a = 0` / `a + -a = 0` (and `Eq.symm` mirrors) via `Int.neg_add_self` /
/// `Int.add_neg_self`. Returns `None` unless one side is such a cancellation and
/// the other is the zero constant.
fn try_neg_cancel(lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    if let Some(proof) = neg_cancel_for(lhs, rhs) {
        return Some(proof);
    }
    if let Some(proof) = neg_cancel_for(rhs, lhs) {
        return Some(mk_symm(rhs, lhs, &proof));
    }
    None
}

/// If `sum` is `(-a) + a` or `a + (-a)` and `zero` is the `0` constant, return a
/// proof `sum = 0` (`Int.neg_add_self a` / `Int.add_neg_self a`, whose RHS
/// `Int.zero` is def-eq to the surface `0` literal).
fn neg_cancel_for(sum: &Expr, zero: &Expr) -> Option<Expr> {
    if eval_int_const(zero) != Some(0) {
        return None;
    }
    let (l, r) = int_add_children(sum)?;
    // (-a) + a : l = -a, r = a.
    if let Some(a) = as_neg(&l) {
        if a == r {
            return Some(Expr::apps(
                Expr::const_(Name::from_string("Int.neg_add_self"), vec![]),
                [a],
            ));
        }
    }
    // a + (-a) : l = a, r = -a.
    if let Some(a) = as_neg(&r) {
        if a == l {
            return Some(Expr::apps(
                Expr::const_(Name::from_string("Int.add_neg_self"), vec![]),
                [a],
            ));
        }
    }
    None
}

/// If `e` is `-x` (`Int.neg x` or surface `Neg.neg Int _ x`), return `x`.
fn as_neg(e: &Expr) -> Option<Expr> {
    let head = e.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let name_s = name.to_string();
    let args = e.get_app_args();
    if (name_s == "Int.neg" || name_s == "Neg.neg") && !args.is_empty() {
        return Some(args[args.len() - 1].clone());
    }
    None
}

// ===========================================================================
// `a = b` from `a ≥ b, b ≥ a` (or `a ≤ b, b ≤ a`) via `Int.le_antisymm`.
// ===========================================================================

/// Attempt `@Eq Int a b` from a pair of `Int` `≤`/`≥` hypotheses that together
/// pin `a ≤ b` AND `b ≤ a`, via `Int.le_antisymm a b (h : Int.le a b) (h' :
/// Int.le b a)`.
///
/// Returns `None` unless BOTH `Int.le a b` and `Int.le b a` are derivable from
/// the hypotheses (as `Int.le`-typed proofs, up to the surface `≤`/`≥` heads,
/// which are def-eq to `Int.le`). A one-sided or unrelated set yields `None`
/// (fail closed); the candidate is re-checked by `state.close_goal`.
pub(crate) fn try_prove_int_eq_via_le_antisymm(
    target: &Expr,
    hyps: &[(Expr, Expr)],
) -> Option<Expr> {
    let (a, b) = match_int_eq(target)?;

    // Find a hyp proving `Int.le a b` and one proving `Int.le b a`.
    let h_ab = find_int_le_proof(hyps, &a, &b)?;
    let h_ba = find_int_le_proof(hyps, &b, &a)?;

    // Int.le_antisymm : ∀ a b, Int.le a b → Int.le b a → Eq Int a b.
    Some(Expr::apps(
        Expr::const_(Name::from_string("Int.le_antisymm"), vec![]),
        [a.clone(), b.clone(), h_ab, h_ba],
    ))
}

/// Find a hypothesis whose type asserts `Int.le lo hi` (in any surface form —
/// `@LE.le Int _ lo hi`, `Int.le lo hi`, or `@GE.ge Int _ hi lo`), returning its
/// fvar proof. The proof's declared type is def-eq to `Int.le lo hi`, so passing
/// it where `Int.le_antisymm` expects `Int.le lo hi` kernel-checks.
fn find_int_le_proof(hyps: &[(Expr, Expr)], lo: &Expr, hi: &Expr) -> Option<Expr> {
    for (proof, ty) in hyps {
        if let Some((l, h)) = match_int_le(ty) {
            if l == *lo && h == *hi {
                return Some(proof.clone());
            }
        }
    }
    None
}

/// Match an `Int` `≤`/`≥` proposition and return the `(lo, hi)` of the
/// equivalent `Int.le lo hi`.
///
/// - `@LE.le Int _ a b` / `Int.le a b` → `(a, b)`.
/// - `@GE.ge Int _ a b` / `Int.ge a b` → `(b, a)` (`a ≥ b ≡ b ≤ a`).
fn match_int_le(ty: &Expr) -> Option<(Expr, Expr)> {
    let head = ty.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let name_s = name.to_string();
    let args = ty.get_app_args();
    // Typeclass form: `@Rel Int inst a b` (4 args); direct form `Int.rel a b` (2).
    let (ty_arg, a, b) = if args.len() == 4 {
        (Some(args[0]), args[2].clone(), args[3].clone())
    } else if args.len() == 2 {
        (None, args[0].clone(), args[1].clone())
    } else {
        return None;
    };
    if let Some(t) = ty_arg {
        if !is_int_const(t) {
            return None;
        }
    } else if !name_s.starts_with("Int.") {
        return None;
    }
    match name_s.as_str() {
        "LE.le" | "Int.le" => Some((a, b)),
        "GE.ge" | "Int.ge" => Some((b, a)),
        _ => None,
    }
}

// ===========================================================================
// `False` from two contradictory `Int` equality hypotheses.
// ===========================================================================

/// Attempt `False` from a pair of `Int` equality hypotheses `h1 : e = c1` and
/// `h2 : e = c2` that share the same LHS `e` but pin it to DISTINCT ground
/// constants `c1 ≠ c2` (e.g. `a + b = 3` and `a + b = 5`).
///
/// Construction: `Eq.symm h1 : c1 = e`, `Eq.trans (symm h1) h2 : c1 = c2`, then
/// the shared `Nat.noConfusion`-based `Int` disequality witness `ne : c1 = c2 →
/// False` applied to it. Returns `None` unless a contradictory constant-pinning
/// pair exists (fail closed); the term is re-checked by `state.close_goal`.
pub(crate) fn try_prove_int_false_from_eq_hyps(
    env: &Environment,
    hyps: &[(Expr, Expr)],
) -> Option<Expr> {
    // Collect `Int` equality hyps parsed to `(proof, lhs_expr, lhs_form, rhs_value?)`.
    // We look for two hyps whose linear forms are IDENTICAL but whose ground
    // constant residuals differ. General shape: `hi : Li = Ri`. Move to
    // `formL_i - formR_i`; if that is a pure constant `k_i` (all atoms cancel),
    // then `hi` asserts the linear expression equals `-k_i` shifted... simpler:
    // two hyps `e = c1`, `e = c2` where `e` is the SAME expression (structural)
    // and `c1`, `c2` are distinct ground literals.
    let eqs: Vec<(Expr, Expr, Expr)> = hyps
        .iter()
        .filter_map(|(pf, ty)| {
            let (l, r) = match_int_eq(ty)?;
            Some((pf.clone(), l, r))
        })
        .collect();

    for i in 0..eqs.len() {
        for j in (i + 1)..eqs.len() {
            let (ref p1, ref l1, ref r1) = eqs[i];
            let (ref p2, ref l2, ref r2) = eqs[j];
            // Both must share the SAME symbolic side and pin it to distinct
            // ground constants. Try all four orientations (each hyp's constant
            // may be on either side), reducing to `sym = c` per hyp.
            let Some((sym1, c1, pf1)) = orient_eq_to_ground(l1, r1, p1) else {
                continue;
            };
            let Some((sym2, c2, pf2)) = orient_eq_to_ground(l2, r2, p2) else {
                continue;
            };
            if sym1 != sym2 || c1 == c2 {
                continue;
            }
            // pf1 : sym = C1 ; pf2 : sym = C2  (C1, C2 the constant literal exprs).
            let c1_lit = int_const_lit(c1);
            let c2_lit = int_const_lit(c2);
            // Eq.symm pf1 : C1 = sym ; Eq.trans that pf2 : C1 = C2.
            let symm1 = mk_symm(&sym1, &c1_lit, &pf1);
            let c1_eq_c2 = mk_trans(&c1_lit, &sym1, &c2_lit, &symm1, &pf2);
            // ne : C1 = C2 → False.
            let eq_level = Level::succ(Level::zero());
            let ne = super::decide_eq_noconfusion::build_noconfusion_ne_proof(
                env,
                &int_ty(),
                &c1_lit,
                &c2_lit,
                &eq_level,
            )?;
            return Some(Expr::app(ne, c1_eq_c2));
        }
    }
    None
}

/// If the equality `l = r` pins a symbolic side to a ground constant, return
/// `(symbolic_side, constant_value, oriented_proof : symbolic_side = C)`.
///
/// `oriented_proof` is `proof` when the constant is on the RHS, or `Eq.symm
/// proof` when it is on the LHS. Returns `None` if BOTH sides are ground or
/// NEITHER side is ground.
fn orient_eq_to_ground(l: &Expr, r: &Expr, proof: &Expr) -> Option<(Expr, i64, Expr)> {
    let lv = eval_int_const(l);
    let rv = eval_int_const(r);
    match (lv, rv) {
        (None, Some(c)) => Some((l.clone(), c, proof.clone())),
        (Some(c), None) => {
            // Eq.symm proof : r = l ; here l is the constant, so oriented side is r.
            Some((r.clone(), c, mk_symm(l, r, proof)))
        }
        _ => None, // both ground or both symbolic
    }
}

// ===========================================================================
// Shifted `Int` inequality from a single `≤` hypothesis.
// ===========================================================================

/// Prove a shifted `Int` inequality goal `GL REL GR` (`REL` ∈ {`<`, `≤`}) from a
/// single hypothesis `h : a ≤ b`, where each goal side is the corresponding
/// hypothesis side shifted by a GROUND literal offset:
///
/// ```text
/// GL ∈ { a, a + dl, a - dl }   GR ∈ { b, b + dr, b - dr }   (dl, dr ground)
/// (h : a ≤ b)  ⊢  a - 1 < b + 1     (the B7 `arith-int-bound` shape)
/// (h : a ≤ b)  ⊢  a - 2 ≤ b
/// (h : a ≤ b)  ⊢  a < b + 3
/// ```
///
/// **Decision (fail closed).** With signed offsets `dl`, `dr` and
/// `s = dl + (1 if strict else 0)`, `t = dr`, the goal follows from `a ≤ b`
/// (uniformly in `a`, `b`) iff `s ≤ t`; any other shape or slack returns
/// `None`, so FALSE goals (`a ≤ b ⊢ a + 1 ≤ b`) never get a candidate.
///
/// **Construction (all registered constructive prelude lemmas).**
/// `Int.lt x y` is definitionally `Int.le (x + 1) y`, so the goal is
/// `Int.le GL' GR` with `GL' = GL + 1` when strict. Build
///
/// 1. `p0 = @Int.add_le_add_right a b h s : a + s ≤ b + s`;
/// 2. when `s < t`, `q = @Int.add_le_add_left s t w b : b + s ≤ b + t`, where
///    `w = Int.NonNeg.mk (t - s)` is the ground witness of `s ≤ t`
///    (`Int.le s t` unfolds to `Int.NonNeg (t - s)`, which ground-reduces to
///    `Int.NonNeg (Int.ofNat (t - s))` — the constructor's type), and chain
///    `p = @Int.le_trans (a+s) (b+s) (b+t) p0 q : a + s ≤ b + t`;
/// 3. cast `a + s` back to the goal spine `GL'` via `Eq.mpr` over
///    `congrArg (fun x => Int.le x (b+t))`: the only non-def-eq reassociation
///    is `(a + dl) + 1 = a + s` (one `@Int.add_assoc a dl 1` instance, its
///    ground tail folded definitionally) and `a = a + 0`
///    (`Eq.symm (Int.add_zero a)`); the `b`-side spellings are def-eq as-is.
///
/// The result is a CANDIDATE only: the caller's `close_goal` re-checks it in
/// the kernel (strict inference + `is_def_eq` against the goal), so a wrong
/// offset split, lemma orientation, or non-reducing ground bridge is rejected,
/// never trusted. Zero domain-specific axioms.
pub(crate) fn try_prove_int_shifted_le_from_hyp(
    goal_target: &Expr,
    h_proof: &Expr,
    hyp_ty: &Expr,
) -> Option<Expr> {
    // Hypothesis: a plain non-strict `≤`/`≥` over Int (GE is flipped by the
    // matcher; its proposition is def-eq to the flipped `Int.le`).
    let (a, b) = match_int_le(hyp_ty)?;

    // Goal: `<` or `≤` over Int.
    let head = goal_target.get_app_fn();
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };
    let strict = match head_name.to_string().as_str() {
        "LT.lt" | "Int.lt" => true,
        "LE.le" | "Int.le" => false,
        _ => return None,
    };
    let args = goal_target.get_app_args();
    let (gl, gr) = if args.len() == 4 {
        if !is_int_const(args[0]) {
            return None;
        }
        (args[2].clone(), args[3].clone())
    } else if args.len() == 2 && head_name.to_string().starts_with("Int.") {
        (args[0].clone(), args[1].clone())
    } else {
        return None;
    };

    // Offset split against the hypothesis cores, then the slack decision.
    let dl = split_int_core_offset(&gl, &a)?;
    let dr = split_int_core_offset(&gr, &b)?;
    let s = dl.checked_add(i64::from(strict))?;
    let t = dr;
    if s > t {
        return None; // not implied by a uniform shift — fail closed.
    }

    let s_lit = int_const_lit(s);
    let t_lit = int_const_lit(t);
    let a_plus_s = mk_int_add(&a, &s_lit);
    let b_plus_s = mk_int_add(&b, &s_lit);
    let b_plus_t = mk_int_add(&b, &t_lit);

    // p : Int.le (a + s) (b + t).
    let p0 = Expr::apps(
        Expr::const_(Name::from_string("Int.add_le_add_right"), vec![]),
        [a.clone(), b.clone(), h_proof.clone(), s_lit.clone()],
    );
    let p = if s == t {
        p0
    } else {
        // Ground witness `s ≤ t`: `Int.NonNeg.mk (t-s) : Int.NonNeg (ofNat (t-s))`,
        // def-eq to `Int.le s t = Int.NonNeg (Int.sub t s)` (ground reduction).
        // Checked: an i64-overflowing shift declines the lane (fail closed)
        // instead of panicking in debug / minting a wrong witness in release.
        let m = match t.checked_sub(s) {
            Some(d) if d >= 0 => d as u64,
            _ => return None,
        };
        let ground_le = Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            Expr::nat_lit(m),
        );
        let q = Expr::apps(
            Expr::const_(Name::from_string("Int.add_le_add_left"), vec![]),
            [s_lit.clone(), t_lit.clone(), ground_le, b.clone()],
        );
        Expr::apps(
            Expr::const_(Name::from_string("Int.le_trans"), vec![]),
            [a_plus_s.clone(), b_plus_s.clone(), b_plus_t.clone(), p0, q],
        )
    };

    // LHS cast: `eq_l : GL' = a + s` where `GL' = GL + 1` (strict) / `GL`.
    let one = int_const_lit(1);
    let (gl_prime, eq_l) = if strict {
        let glp = mk_int_add(&gl, &one);
        if dl == 0 {
            // `GL + 1 = a + 1` is def-eq (GL == a, s == 1): no cast needed.
            (glp, None)
        } else {
            // `(a + dl) + 1 = a + (dl + 1)`; the ground tail `dl + 1` is def-eq
            // to `s`, so this single assoc instance is used at `GL' = a + s`.
            let assoc = Expr::apps(
                Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
                [a.clone(), int_const_lit(dl), one.clone()],
            );
            (glp, Some(assoc))
        }
    } else if dl == 0 {
        // `GL = a`, target LHS `a + 0`: `Eq.symm (Int.add_zero a) : a = a + 0`.
        let add_zero = Expr::app(
            Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            a.clone(),
        );
        (gl.clone(), Some(mk_symm(&a_plus_s, &a, &add_zero)))
    } else {
        // `GL = a ± g` is def-eq to `a + s` as spelled: no cast needed.
        (gl.clone(), None)
    };

    // RHS cast: only `GR == b` (t == 0) needs `b = b + 0`.
    let eq_r = if dr == 0 {
        let add_zero = Expr::app(
            Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            b.clone(),
        );
        Some(mk_symm(&b_plus_t, &b, &add_zero))
    } else {
        None
    };

    // Assemble: cast the LHS, then the RHS, each via `Eq.mpr ∘ congrArg`.
    let mut cur = p;
    let mut cur_lhs = a_plus_s.clone();
    if let Some(eq) = eq_l {
        let motive = Expr::lam(
            BinderInfo::Default,
            int_ty(),
            mk_int_le(&Expr::bvar(0), &b_plus_t),
        );
        let cong = mk_congr_arg_int_prop(&gl_prime, &a_plus_s, &motive, &eq);
        cur = mk_eq_mpr(
            &mk_int_le(&gl_prime, &b_plus_t),
            &mk_int_le(&a_plus_s, &b_plus_t),
            &cong,
            &cur,
        );
        cur_lhs = gl_prime;
    }
    if let Some(eq) = eq_r {
        let motive = Expr::lam(
            BinderInfo::Default,
            int_ty(),
            mk_int_le(&cur_lhs, &Expr::bvar(0)),
        );
        let cong = mk_congr_arg_int_prop(&gr, &b_plus_t, &motive, &eq);
        cur = mk_eq_mpr(
            &mk_int_le(&cur_lhs, &gr),
            &mk_int_le(&cur_lhs, &b_plus_t),
            &cong,
            &cur,
        );
    }
    Some(cur)
}

/// Split `e` into a ground offset relative to `core`:
/// `e == core` → `0`; `core + g` → `g`; `core - g` → `-g` (`g` ground).
/// Any other shape → `None` (fail closed).
fn split_int_core_offset(e: &Expr, core: &Expr) -> Option<i64> {
    if e == core {
        return Some(0);
    }
    let args = e.get_app_args();
    if args.len() >= 2 {
        if let ExprKind::Const(op, _) = e.get_app_fn().kind() {
            let op_s = op.to_string();
            let l = args[args.len() - 2];
            let r = args[args.len() - 1];
            if l != core {
                return None;
            }
            if op_s == "Int.add" || op_s == "HAdd.hAdd" || op_s == "Add.add" {
                return super::norm_num::eval_int_expr(r);
            }
            if op_s == "Int.sub" || op_s == "HSub.hSub" || op_s == "Sub.sub" {
                return super::norm_num::eval_int_expr(r)?.checked_neg();
            }
        }
    }
    None
}

// ===========================================================================
// Matchers.
// ===========================================================================

/// Match `@Eq Int l r` and return `(l, r)`.
fn match_int_eq(target: &Expr) -> Option<(Expr, Expr)> {
    let head = target.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if name.to_string() != "Eq" {
        return None;
    }
    let args = target.get_app_args();
    if args.len() != 3 || !is_int_const(args[0]) {
        return None;
    }
    Some((args[1].clone(), args[2].clone()))
}

fn is_int_const(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Int")
}

/// Extract `(a, b)` from `Int.add a b` / `HAdd.hAdd .. a b` / `Add.add a b`.
fn int_add_children(e: &Expr) -> Option<(Expr, Expr)> {
    let args = e.get_app_args();
    if args.len() >= 2 {
        if let ExprKind::Const(op, _) = e.get_app_fn().kind() {
            let op_s = op.to_string();
            if op_s == "Int.add" || op_s == "HAdd.hAdd" || op_s == "Add.add" {
                return Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()));
            }
        }
    }
    None
}

// ===========================================================================
// Term builders (all constants are registered prelude lemmas/recursors).
// ===========================================================================

fn int_ty() -> Expr {
    Expr::const_(Name::from_string("Int"), vec![])
}

/// Render an integer constant as an `Int` literal expression: `Int.ofNat n` for
/// `n ≥ 0`, `Int.negSucc (n-1)` for `n < 0`.
fn int_const_lit(v: i64) -> Expr {
    if v >= 0 {
        Expr::apps(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            [Expr::nat_lit(v as u64)],
        )
    } else {
        // negSucc m represents -(m+1); for value v (<0), m = -v - 1.
        let m = (-v - 1) as u64;
        Expr::apps(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            [Expr::nat_lit(m)],
        )
    }
}

/// `@Eq.refl Int a`.
fn mk_refl(a: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [int_ty(), a.clone()],
    )
}

/// `@Eq.symm Int a b h : b = a`.
fn mk_symm(a: &Expr, b: &Expr, h: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [int_ty(), a.clone(), b.clone(), h.clone()],
    )
}

/// `@Eq.trans Int a b c h1 h2 : a = c`.
fn mk_trans(a: &Expr, b: &Expr, c: &Expr, h1: &Expr, h2: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [
            int_ty(),
            a.clone(),
            b.clone(),
            c.clone(),
            h1.clone(),
            h2.clone(),
        ],
    )
}

/// `Int.add_comm a b : Int.add a b = Int.add b a`.
fn mk_add_comm(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Int.add_comm"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// `Int.add a b`.
fn mk_int_add(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Int.add"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// `Int.le a b`.
fn mk_int_le(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Int.le"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// `@congrArg.{1,1} Int Prop x y f h : @Eq.{1} Prop (f x) (f y)` where
/// `h : @Eq Int x y` and `f : Int → Prop`.
fn mk_congr_arg_int_prop(x: &Expr, y: &Expr, f: &Expr, h: &Expr) -> Expr {
    let u = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![u.clone(), u]),
        [
            int_ty(),
            Expr::sort(Level::zero()),
            x.clone(),
            y.clone(),
            f.clone(),
            h.clone(),
        ],
    )
}

/// `@Eq.mpr.{0} a_prop b_prop h p : a_prop` where `h : a_prop = b_prop` and
/// `p : b_prop`.
fn mk_eq_mpr(a_prop: &Expr, b_prop: &Expr, h: &Expr, p: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.mpr"), vec![Level::zero()]),
        [a_prop.clone(), b_prop.clone(), h.clone(), p.clone()],
    )
}
