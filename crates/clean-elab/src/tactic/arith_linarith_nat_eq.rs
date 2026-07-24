// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct (goal-driven) proof synthesis for linear Nat **equality** goals.
//!
//! Sibling of [`super::arith_linarith_nat_direct`], which handles the
//! `≤ / < / ≥ / >` family. This module closes the corresponding gap for `=`:
//! omega previously returned `NoProgress` on permutation equalities such as
//! `a + b = b + a` and `a + b + c = c + b + a`, because the `≤`-only direct
//! synthesizer never fires for an `@Eq Nat l r` head, the `reduce_eq` pre-pass
//! only discharges computationally-closing equalities (`a + 0 = a`), and the
//! constraint path negates an equality *goal* into an unsupported `Ne`.
//!
//! ## Decision (the soundness gate)
//!
//! Both sides are parsed into a canonical **linear form**: a map from atom
//! `Expr` to an `i64` coefficient, plus an `i64` constant. A linear Nat equality
//! `l = r` holds for *all* valuations iff the two linear forms are identical
//! (same coefficient per atom AND equal constant). The synthesizer returns
//! `Some(proof)` ONLY when the forms match AND the synthesis pass can build a
//! kernel-checkable rewrite chain for that shape; for any false equality (e.g.
//! `a + b = a`: `{a:1,b:1}` vs `{a:1}`) the forms differ, it returns `None`, and
//! omega falls through and ultimately fails closed. No bogus term is ever
//! emitted for a false equality.
//!
//! ## Coverage
//!
//! Provable shapes: additive permutations, constant folding, and literal-
//! coefficient multiplication — `a + b = b + a`, `(a + b) + c = (c + b) + a`,
//! `a + 0 = a`, `n + 1 = 1 + n`, `2 * a = a + a`, `3 * a = a + a + a`,
//! `a * 2 = a + a` (literal factor on either side).
//! A literal coefficient `k * atom` (or `atom * k`) is recognized by the
//! DECISION gate (so `2 * a = a` correctly FAILS) AND expanded by the synthesis
//! pass into the `k`-fold sum `atom + (atom + … + atom)` via a proof-carrying
//! `Nat.succ_mul` / `Nat.mul_succ` unfolding chain (base cases
//! `Nat.one_mul`/`Nat.mul_one` and `Nat.zero_mul`/`Nat.mul_zero`), all
//! foundational Nat lemmas with empty axiom closure. A *symbolic* factor on both
//! sides (`a * b`) is non-linear and rejected by the parser (fail closed).
//!
//! ## Synthesis (a normalizing rewrite chain)
//!
//! When the forms match, each side is normalized to the **same** canonical
//! right-folded sum by a chain of `Nat.add_comm` / `Nat.add_assoc` /
//! `congrArg` / `Eq.trans` / `Eq.symm` steps (all foundational, zero
//! domain-specific axioms). The proof is
//! `Eq.trans (l = canon) (Eq.symm (r = canon))`.
//!
//! Every synthesized term is handed to `state.close_goal`, which runs a genuine
//! `infer_type` + WHNF + `is_def_eq` check against the target, and the whole
//! theorem is re-checked by `add_decl` on `clean check`. A wrong reconstruction
//! is therefore *rejected*, never trusted: this preserves the safe-reject
//! soundness model and emits **zero** `trustedAy` / `trustedArith` axioms.

use std::collections::HashMap;

use clean_kernel::expr::{BinderInfo, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::nat_expr_eval::eval_nat_expr;

/// Canonical linear form of a Nat expression: per-atom integer coefficients
/// plus a constant. Two expressions are equal as linear Nat forms iff their
/// `LinearForm`s are equal.
#[derive(Debug, Clone, Default)]
pub(crate) struct LinearForm {
    /// Map from an atom `Expr` to its (non-zero) integer coefficient.
    pub(crate) coeffs: HashMap<Expr, i64>,
    /// The accumulated constant addend.
    pub(crate) constant: i64,
}

impl LinearForm {
    fn add_atom(&mut self, atom: Expr, coeff: i64) {
        let entry = self.coeffs.entry(atom).or_insert(0);
        *entry += coeff;
    }

    /// Drop atoms whose coefficient cancelled to zero (so equal forms compare
    /// equal regardless of cancellation order).
    fn normalize(&mut self) {
        self.coeffs.retain(|_, c| *c != 0);
    }

    /// Equal as linear forms: identical constant and identical non-zero
    /// coefficient per atom.
    fn equals(&self, other: &LinearForm) -> bool {
        self.constant == other.constant && self.coeffs == other.coeffs
    }
}

/// Recursively parse `e` into a [`LinearForm`].
///
/// Distributes over `Nat.add` / `HAdd.hAdd` / `Add.add` (sum of children),
/// `Nat.succ x` (constant + 1, then recurse on `x`), literal `* atom` and
/// `atom * literal` via `Nat.mul` / `HMul.hMul` / `Mul.mul` (scale the atom's
/// coefficient), bare literals via `eval_nat_expr` (into the constant), and any
/// other symbolic head as an atom with coefficient 1.
///
/// REQUIRES: `e` is a well-formed Nat expression.
/// ENSURES: On `Some(form)`, `e` is a linear Nat term whose value equals
///   `Σ coeff·atom + constant` for every valuation.
/// ENSURES: On `None`, `e` contains a non-linear sub-term (e.g. `a * b` with two
///   symbolic factors) — the caller must fail closed.
pub(crate) fn parse_nat_linear_form(e: &Expr) -> Option<LinearForm> {
    let mut form = LinearForm::default();
    accumulate(e, 1, &mut form)?;
    form.normalize();
    Some(form)
}

/// Accumulate `scale · e` into `form`. `scale` is the coefficient multiplier
/// carried down through multiplications.
fn accumulate(e: &Expr, scale: i64, form: &mut LinearForm) -> Option<()> {
    // Bare literal: fold into the constant.
    if let Some(v) = eval_nat_expr(e) {
        let v = i64::try_from(v).ok()?;
        form.constant = form.constant.checked_add(scale.checked_mul(v)?)?;
        return Some(());
    }

    if let ExprKind::App(f, arg) = e.kind() {
        // Nat.succ x  =>  constant + scale, then recurse on x.
        if let ExprKind::Const(name, _) = f.kind() {
            if name.to_string() == "Nat.succ" {
                form.constant = form.constant.checked_add(scale)?;
                return accumulate(arg, scale, form);
            }
        }

        let args = e.get_app_args();
        if args.len() >= 2 {
            if let ExprKind::Const(op, _) = e.get_app_fn().kind() {
                let op_s = op.to_string();
                let lhs = args[args.len() - 2];
                let rhs = args[args.len() - 1];
                // Addition: distribute.
                if op_s == "Nat.add" || op_s == "HAdd.hAdd" || op_s == "Add.add" {
                    accumulate(lhs, scale, form)?;
                    return accumulate(rhs, scale, form);
                }
                // Multiplication by a literal on either side: scale the atom.
                if op_s == "Nat.mul" || op_s == "HMul.hMul" || op_s == "Mul.mul" {
                    if let Some(rv) = eval_nat_expr(rhs) {
                        let rv = i64::try_from(rv).ok()?;
                        return accumulate(lhs, scale.checked_mul(rv)?, form);
                    }
                    if let Some(lv) = eval_nat_expr(lhs) {
                        let lv = i64::try_from(lv).ok()?;
                        return accumulate(rhs, scale.checked_mul(lv)?, form);
                    }
                    // Two symbolic factors: non-linear. Fail closed.
                    return None;
                }
            }
        }
    }

    // Any other symbolic head: a single atom with the carried coefficient.
    form.add_atom(e.clone(), scale);
    Some(())
}

/// Attempt to synthesize a kernel-checked proof for a linear Nat **equality**
/// goal directly from the goal (no hypotheses needed).
///
/// Succeeds when the goal is `@Eq Nat l r` (or `Eq l r` over Nat), `l`, `r`
/// have identical canonical linear forms, AND the shape is an additive
/// permutation / constant fold (e.g. `a + b = b + a`, `a + b + c = c + b + a`,
/// `a + 0 = a`). Shapes needing literal-coefficient expansion (`2 * a = a + a`)
/// are deferred (return `None`, fail closed).
///
/// The result is always re-checked by `state.close_goal`; this function only
/// proposes a candidate term.
///
/// REQUIRES: `target` is the current goal type.
/// ENSURES: On `Some(e)`, `e` is intended to have type `target`; soundness is
///   guaranteed by the caller's kernel re-check, not by this function.
/// ENSURES: On `None`, the goal is not a provable linear Nat equality shape
///   (caller must fall through / fail closed). In particular, a FALSE equality
///   always yields `None`.
pub(crate) fn try_prove_nat_equality_direct(target: &Expr) -> Option<Expr> {
    let (lhs, rhs) = match_nat_eq(target)?;

    // DECISION GATE: provable iff the two linear forms are identical.
    let lhs_form = parse_nat_linear_form(&lhs)?;
    let rhs_form = parse_nat_linear_form(&rhs)?;
    if !lhs_form.equals(&rhs_form) {
        return None; // false (or unequal) — fail closed.
    }

    // Reflexivity shortcut: syntactically identical sides.
    if lhs == rhs {
        return Some(mk_refl(&lhs));
    }

    // Ground-constant shortcut: when BOTH sides are closed Nat expressions that
    // evaluate to the SAME concrete value (e.g. `2 + 1 = 3`, the residual a
    // hypothesis substitution leaves behind), the additive-permutation
    // normalizer below cannot prove it (it treats the literals `2`, `1`, `3` as
    // distinct unorderable leaves), so emit `@Eq.refl Nat v` here. Both sides
    // reduce to the single literal `v` in the kernel, so the goal `lhs = rhs` is
    // def-eq to `v = v`; `close_goal` re-checks (the soundness gate). This fires
    // ONLY when the two evaluations are equal, so a false ground equality such as
    // `2 + 1 = 4` is already rejected by the decision gate above and never
    // reaches here.
    if let (Some(lv), Some(rv)) = (eval_nat_expr(&lhs), eval_nat_expr(&rhs)) {
        if lv == rv {
            return Some(mk_refl(&Expr::nat_lit(lv)));
        }
    }

    // Expand every literal-coefficient multiplication leaf (`k * atom` /
    // `atom * k`) into the `k`-fold additive sum `atom + (atom + … + atom)`,
    // producing a proof `side = expanded_side`. This lets the additive
    // permutation normalizer below reconcile shapes like `2 * a = a + a`
    // (`[2*a]` vs `[a, a]` become `[a, a]` vs `[a, a]`). The expansion chain uses
    // only foundational Nat lemmas (`Nat.succ_mul`/`Nat.mul_succ`/`Nat.one_mul`/
    // `Nat.zero_mul`/`Nat.mul_one`/`Nat.mul_zero`), so it adds zero
    // domain-specific axioms; the whole term is still kernel-rechecked by the
    // caller. A side with no mul leaf expands to itself with a reflexive proof.
    let (exp_l, expand_l) = expand_mul_leaves(&lhs)?; // expand_l : lhs = exp_l
    let (exp_r, expand_r) = expand_mul_leaves(&rhs)?; // expand_r : rhs = exp_r

    // Normalize both expanded sides to the SAME canonical right-folded sum, then
    // `Eq.trans (l = canon) (Eq.symm (r = canon))`.
    //
    // After sorting, any literal leaves form a contiguous run at the tail (their
    // `leaf_key` debug strings begin `Lit(`, which sorts after `App(`/`FVar(`).
    // Collapsing that run into a single literal makes the two sides' canonical
    // forms structurally identical even when the constant was *spread across
    // several literal leaves* (`a + 2 + (b + 1) + 0` vs `b + 2 + a + 1`), which
    // the per-leaf permutation prover alone cannot reconcile. The collapse proof
    // is `Eq.refl canon` re-typed at `canon = canon_folded`: it is accepted iff
    // `canon` and `canon_folded` are kernel-def-eq, which they are because the
    // literal tail `l1 + (l2 + … + lm)` reduces to the summed literal. The kernel
    // re-check is the soundness gate, so a non-def-eq fold is rejected.
    let (canon_l1, proof_l1) = normalize_to_canonical(&exp_l)?; // exp_l = canon_l1
    let (canon_r1, proof_r1) = normalize_to_canonical(&exp_r)?; // exp_r = canon_r1
                                                                // Compose the expansion with the canonicalization: `side = canon`.
    let canon_l0 = canon_l1;
    let canon_r0 = canon_r1;
    let proof_l0 = mk_trans(&lhs, &exp_l, &canon_l0, &expand_l, &proof_l1);
    let proof_r0 = mk_trans(&rhs, &exp_r, &canon_r0, &expand_r, &proof_r1);
    let (canon_l, fold_l) = fold_canonical_literal_tail(&canon_l0);
    let (canon_r, fold_r) = fold_canonical_literal_tail(&canon_r0);
    // The decision gate guarantees the multisets match, so the folded canonical
    // forms are syntactically identical; guard anyway and fail closed otherwise.
    if canon_l != canon_r {
        return None;
    }
    // proof_l : lhs = canon_l0 ; fold_l : canon_l0 = canon_l.
    let proof_l = mk_trans(&lhs, &canon_l0, &canon_l, &proof_l0, &fold_l);
    let proof_r = mk_trans(&rhs, &canon_r0, &canon_r, &proof_r0, &fold_r);
    let symm_r = mk_symm(&rhs, &canon_r, &proof_r);
    Some(mk_trans(&lhs, &canon_l, &rhs, &proof_l, &symm_r))
}

/// Collapse the trailing run of literal leaves in a canonical right-folded sum
/// into a single literal leaf, returning `(folded, proof : canon = folded)`.
///
/// `normalize_to_canonical` sorts leaves by `leaf_key`; literal leaves
/// (`Lit(...)`) sort after symbolic ones (`App(...)`/`FVar(...)`), so the
/// literals are a contiguous tail `… + (l1 + (l2 + … + lm))`. That nested sum is
/// kernel-def-eq to the single literal `Σ lᵢ`, so replacing it yields a
/// def-eq expression and the proof is `Eq.refl canon` re-typed at
/// `canon = folded` (accepted by the kernel iff genuinely def-eq).
///
/// When there is at most one literal leaf, or the literal values overflow `u64`
/// accumulation, the canonical form is returned unchanged with a reflexive
/// proof.
fn fold_canonical_literal_tail(canon: &Expr) -> (Expr, Expr) {
    let leaves = flatten_add_leaves(canon);
    // Split into symbolic prefix and literal tail.
    let mut split = leaves.len();
    for (i, leaf) in leaves.iter().enumerate() {
        if eval_nat_expr(leaf).is_some() {
            split = i;
            break;
        }
    }
    let symbolic = &leaves[..split];
    let literals = &leaves[split..];

    // Need at least two literal leaves to fold; and every tail leaf must be a
    // literal (a non-literal after the first literal would break the def-eq).
    if literals.len() < 2 || literals.iter().any(|l| eval_nat_expr(l).is_none()) {
        return (canon.clone(), mk_refl(canon));
    }
    let mut sum: u64 = 0;
    for l in literals {
        match eval_nat_expr(l).and_then(|v| sum.checked_add(v)) {
            Some(v) => sum = v,
            None => return (canon.clone(), mk_refl(canon)),
        }
    }
    let sum_lit = Expr::nat_lit(sum);

    // Rebuild the canonical right-fold with the single summed literal.
    let mut new_leaves: Vec<Expr> = symbolic.to_vec();
    new_leaves.push(sum_lit);
    let folded = rfold(&new_leaves);

    // `canon` is def-eq to `folded` (the literal tail reduces); prove by refl on
    // `canon`, re-typed at `canon = folded` by the kernel.
    (folded, mk_refl(canon))
}

/// Attempt to synthesize a kernel-checked proof for a linear Nat **equality**
/// goal `glhs = grhs` *from a set of hypothesis equalities* `{hi : ai = bi}`.
///
/// This is the hypothesis-carrying sibling of [`try_prove_nat_equality_direct`].
/// It closes goals such as `(h : a = b) ⊢ a + 1 = b + 1` (congruence over a
/// single hyp) and `(h1 : a = b) (h2 : b = c) ⊢ a + 1 = c + 1` (a threaded
/// substitution chain) that the goal-only synthesizer cannot reach because the
/// two sides have *different* atoms (`a` vs `b`) until the hyps are applied.
///
/// ## Decision (the soundness gate)
///
/// Let `D = glhs_form - grhs_form` (per-atom coefficient differences plus the
/// constant difference), and let each hyp contribute the relation vector
/// `vi = ai_form - bi_form` (a form that equals the zero element under the
/// hypothesis, since `ai = bi`). The goal `glhs = grhs` follows from the hyps in
/// the linear theory iff `D` lies in the integer lattice generated by
/// `{vi}` — i.e. `D = Σ ci·vi` for integers `ci`, with the constant balancing
/// too. We decide this by integer Gaussian elimination over the atom-coefficient
/// vectors (see [`reduce_against_hyps`]). If `D` does NOT reduce to the zero
/// form, the goal does not follow and we return `None` (fail closed). FALSE
/// goals such as `(h : a = b) ⊢ a = c` (`D = a - c`, and `c` is a free atom not
/// touched by `a - b`) therefore yield `None`.
///
/// ## Synthesis (substitution chain + residual normalizer)
///
/// When the decision succeeds with coefficients `{ci}`, we rewrite `glhs` toward
/// `grhs` by applying each hyp `|ci|` times in the direction given by `sign(ci)`
/// (`ai → bi` for `ci > 0`, `bi → ai` for `ci < 0`). Each single rewrite of one
/// occurrence of the source atom inside the current expression is lifted by
/// `congrArg motive h` (or `congrArg motive (Eq.symm h)`), where `motive` is the
/// current expression with that one occurrence abstracted to a bound variable;
/// the steps are threaded with `Eq.trans`. After all substitutions the residual
/// `current = grhs` is a pure additive permutation / constant fold, discharged
/// by the goal-only [`normalize_to_canonical`] chain and composed with
/// `Eq.symm`.
///
/// All builders (`congrArg`, `Eq.trans`, `Eq.symm`, `Eq.refl`, `Nat.add_comm`,
/// `Nat.add_assoc`) are foundational (zero domain-specific axioms). Every
/// synthesized term is re-checked by `state.close_goal`, so a wrong motive or a
/// bogus candidate is rejected, never trusted.
///
/// REQUIRES: `target` is the current goal type; each `hyps[i]` is
///   `(fvar_expr, hyp_type)` from the goal's local context.
/// ENSURES: On `Some(e)`, `e` is intended to have type `target` (kernel-rechecked
///   by the caller). On `None`, the goal is not a provable linear Nat equality
///   modulo the hypotheses — in particular every FALSE goal yields `None`.
pub(crate) fn try_prove_nat_equality_from_hyps(
    target: &Expr,
    hyps: &[(Expr, Expr)],
) -> Option<Expr> {
    let (glhs, grhs) = match_nat_eq(target)?;

    // Parse both goal sides; bail (fail closed) on any non-linear shape.
    let glhs_form = parse_nat_linear_form(&glhs)?;
    let grhs_form = parse_nat_linear_form(&grhs)?;

    // Collect equality hypotheses over Nat, with both sides parsed to forms.
    // Each entry: (fvar_proof, ai_expr, bi_expr, ai_form, bi_form).
    let mut eq_hyps: Vec<EqHyp> = Vec::new();
    for (fvar, ty) in hyps {
        let Some((hl, hr)) = match_nat_eq(ty) else {
            continue;
        };
        let (Some(hl_form), Some(hr_form)) =
            (parse_nat_linear_form(&hl), parse_nat_linear_form(&hr))
        else {
            continue;
        };
        eq_hyps.push(EqHyp {
            proof: fvar.clone(),
            lhs: hl,
            rhs: hr,
            relation: form_sub(&hl_form, &hr_form),
        });
    }

    // DECISION GATE: D = glhs_form - grhs_form must reduce to the zero form using
    // integer multiples of the hyp relation vectors {ai_form - bi_form}.
    let d = form_sub(&glhs_form, &grhs_form);
    let coeffs = reduce_against_hyps(&d, &eq_hyps)?;

    // If no hyp is actually needed, defer to the goal-only synthesizer (handles
    // the pure additive-permutation / constant-fold residual on its own).
    if coeffs.iter().all(|c| *c == 0) {
        return try_prove_nat_equality_direct(target);
    }

    // SYNTHESIS: rewrite `glhs` toward `grhs` by applying each hyp |ci| times in
    // the sign-given direction; lift every single-occurrence rewrite with
    // congrArg + Eq.trans. Then close the residual additive permutation.
    let mut current = glhs.clone();
    // proof : glhs = current (starts reflexive).
    let mut proof = mk_refl(&glhs);

    for (hyp, &c) in eq_hyps.iter().zip(coeffs.iter()) {
        if c == 0 {
            continue;
        }
        // Direction: c > 0 rewrites ai -> bi; c < 0 rewrites bi -> ai.
        let (src, dst, base_eq, count) = if c > 0 {
            (&hyp.lhs, &hyp.rhs, hyp.proof.clone(), c as usize)
        } else {
            // Eq.symm h : bi = ai
            (
                &hyp.rhs,
                &hyp.lhs,
                mk_symm(&hyp.lhs, &hyp.rhs, &hyp.proof),
                (-c) as usize,
            )
        };
        for _ in 0..count {
            // Replace ONE occurrence of `src` in `current` with `dst`.
            let (motive, next) = replace_one_occurrence(&current, src, dst)?;
            // step : current = next, via congrArg motive base_eq.
            let step = mk_congr_arg(src, dst, &motive, &base_eq);
            proof = mk_trans(&glhs, &current, &next, &proof, &step);
            current = next;
        }
    }

    // RESIDUAL: prove `current = grhs` (a pure additive permutation / fold) with
    // the goal-only normalizer, then compose. Guard with the decision invariant.
    if current == grhs {
        return Some(proof);
    }
    let residual_goal = mk_eq_goal(&current, &grhs);
    let residual = try_prove_nat_equality_direct(&residual_goal)?; // current = grhs
    Some(mk_trans(&glhs, &current, &grhs, &proof, &residual))
}

/// An equality hypothesis `proof : lhs = rhs` over Nat, with its linear relation
/// vector `lhs_form - rhs_form` (which equals the zero form under the hyp).
struct EqHyp {
    proof: Expr,
    lhs: Expr,
    rhs: Expr,
    relation: LinearForm,
}

/// `glhs_form - grhs_form`: per-atom coefficient difference plus constant
/// difference. Atoms cancelling to zero are dropped by `normalize`.
fn form_sub(a: &LinearForm, b: &LinearForm) -> LinearForm {
    let mut out = a.clone();
    for (atom, coeff) in &b.coeffs {
        out.add_atom(atom.clone(), -*coeff);
    }
    out.constant -= b.constant;
    out.normalize();
    out
}

/// Whether `f` is the zero linear form (no atoms, zero constant).
fn form_is_zero(f: &LinearForm) -> bool {
    f.constant == 0 && f.coeffs.is_empty()
}

/// Decide whether `d` lies in the integer lattice generated by the hyp relation
/// vectors, returning the integer coefficients `{ci}` (one per hyp) with
/// `d = Σ ci · relation_i` when it does, or `None` otherwise (fail closed).
///
/// Greedy integer elimination: process atoms in a deterministic order; for each
/// residual atom with a non-zero coefficient, find a hyp whose relation has that
/// atom and whose coefficient divides the residual's, subtract that multiple,
/// and accumulate the coefficient. Succeeds iff the residual reaches the zero
/// form (including the constant). This is sound by construction: the returned
/// `{ci}` literally satisfy `d = Σ ci·relation_i` (re-checked below), and the
/// caller's kernel re-check is the final gate.
fn reduce_against_hyps(d: &LinearForm, hyps: &[EqHyp]) -> Option<Vec<i64>> {
    let mut residual = d.clone();
    let mut coeffs = vec![0i64; hyps.len()];

    // Bound the iterations to avoid any pathological non-termination; each
    // successful step strictly reduces the number of non-zero atoms or the
    // constant magnitude, so this is generous.
    let max_iters = (hyps.len() + 1) * (d.coeffs.len() + 4) + 8;
    for _ in 0..max_iters {
        if form_is_zero(&residual) {
            // Verify d = Σ ci·relation_i exactly (defensive; cheap).
            return verify_combination(d, &coeffs, hyps).then_some(coeffs);
        }
        // Pick a pivot atom: any atom with a non-zero residual coefficient,
        // chosen deterministically by the stable leaf key.
        let pivot = residual
            .coeffs
            .iter()
            .filter(|(_, c)| **c != 0)
            .min_by_key(|(atom, _)| leaf_key(atom))
            .map(|(atom, c)| (atom.clone(), *c));

        let (atom, res_c) = match pivot {
            Some(p) => p,
            None => {
                // No atoms left but constant non-zero: only a constant-only hyp
                // relation can clear it.
                let mut progressed = false;
                for (i, hyp) in hyps.iter().enumerate() {
                    if !hyp.relation.coeffs.is_empty() || hyp.relation.constant == 0 {
                        continue;
                    }
                    if residual.constant % hyp.relation.constant == 0 {
                        let m = residual.constant / hyp.relation.constant;
                        residual.constant -= m * hyp.relation.constant;
                        coeffs[i] += m;
                        progressed = true;
                        break;
                    }
                }
                if progressed {
                    continue;
                }
                return None; // constant cannot be cleared; fail closed.
            }
        };

        // Find a hyp whose relation has this atom with a coefficient dividing
        // `res_c`, so we can eliminate it in one integer step.
        let mut progressed = false;
        for (i, hyp) in hyps.iter().enumerate() {
            let Some(&hyp_c) = hyp.relation.coeffs.get(&atom) else {
                continue;
            };
            if hyp_c == 0 || res_c % hyp_c != 0 {
                continue;
            }
            let m = res_c / hyp_c;
            // residual -= m · relation_i
            for (a2, c2) in &hyp.relation.coeffs {
                residual.add_atom(a2.clone(), -m * *c2);
            }
            residual.constant -= m * hyp.relation.constant;
            residual.normalize();
            coeffs[i] += m;
            progressed = true;
            break;
        }
        if !progressed {
            return None; // this atom cannot be eliminated; fail closed.
        }
    }
    None
}

/// Verify that `Σ coeffs[i]·relation_i == d` exactly (the soundness invariant the
/// reducer must satisfy before we trust the coefficients for synthesis).
fn verify_combination(d: &LinearForm, coeffs: &[i64], hyps: &[EqHyp]) -> bool {
    let mut acc = LinearForm::default();
    for (hyp, &c) in hyps.iter().zip(coeffs.iter()) {
        if c == 0 {
            continue;
        }
        for (atom, hc) in &hyp.relation.coeffs {
            acc.add_atom(atom.clone(), c * *hc);
        }
        acc.constant += c * hyp.relation.constant;
    }
    acc.normalize();
    form_is_zero(&form_sub(d, &acc))
}

/// `@Eq Nat l r`.
fn mk_eq_goal(l: &Expr, r: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat_ty(), l.clone(), r.clone()],
    )
}

/// Replace exactly ONE occurrence of `src` (by structural equality) inside
/// `whole` with the bound variable, returning `(motive, whole[src := dst])`
/// where `motive = fun (z : Nat) => whole[that occurrence := z]`.
///
/// The motive is built so that `motive src` is def-eq to `whole` and
/// `motive dst` is def-eq to the returned replaced expression, hence
/// `congrArg motive (h : src = dst) : whole = whole[src := dst]` kernel-checks.
///
/// Returns `None` if `src` does not occur in `whole` (the caller fails closed).
fn replace_one_occurrence(whole: &Expr, src: &Expr, dst: &Expr) -> Option<(Expr, Expr)> {
    // Build the motive body by replacing the first occurrence with bvar(0),
    // shifting pre-existing bound variables is unnecessary because the additive
    // Nat expressions we handle are closed (no binders); guard anyway.
    let mut replaced_body = false;
    let body = subst_first(whole, src, &Expr::bvar(0), &mut replaced_body);
    if !replaced_body {
        return None;
    }
    let mut replaced_dst = false;
    let next = subst_first(whole, src, dst, &mut replaced_dst);
    if !replaced_dst {
        return None;
    }
    let motive = Expr::lam(BinderInfo::Default, nat_ty(), body);
    Some((motive, next))
}

/// Substitute the FIRST (left-most, outer-most) occurrence of `target` in `e`
/// with `repl`, setting `done` once a replacement happened. Structural recursion
/// over `App` / `Lam` / `Pi` / `Let`; leaves match by structural equality.
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

/// Match `@Eq Nat l r` / `Eq Nat l r` and return `(l, r)` when the equality is
/// over `Nat`.
pub(crate) fn match_nat_eq(target: &Expr) -> Option<(Expr, Expr)> {
    let head = target.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if name.to_string() != "Eq" {
        return None;
    }
    let args = target.get_app_args();
    if args.len() != 3 {
        return None;
    }
    if !is_nat_type(args[0]) {
        return None;
    }
    Some((args[1].clone(), args[2].clone()))
}

fn is_nat_type(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat")
}

// ---------------------------------------------------------------------------
// Canonicalization: prove `e = rightfold(sorted leaves)`.
// ---------------------------------------------------------------------------

/// Flatten an additive Nat expression into its list of leaf atoms (in
/// left-to-right order), where a leaf is any non-`add` sub-term (atoms,
/// literals, `succ ...`, `lit * atom`, ...). Literals are kept as leaves so the
/// rewrite chain stays a pure `add` permutation.
fn flatten_add_leaves(e: &Expr) -> Vec<Expr> {
    fn go(e: &Expr, out: &mut Vec<Expr>) {
        let args = e.get_app_args();
        if args.len() >= 2 {
            if let ExprKind::Const(op, _) = e.get_app_fn().kind() {
                let op_s = op.to_string();
                if op_s == "Nat.add" || op_s == "HAdd.hAdd" || op_s == "Add.add" {
                    go(args[args.len() - 2], out);
                    go(args[args.len() - 1], out);
                    return;
                }
            }
        }
        out.push(e.clone());
    }
    let mut out = Vec::new();
    go(e, &mut out);
    out
}

/// Stable canonical key for a leaf `Expr` (its debug encoding), used to define a
/// total order for the canonical sorted sum. The ordering choice is irrelevant
/// to soundness (the kernel re-checks the synthesized rewrite chain); it only
/// needs to be deterministic and consistent between the two sides.
fn leaf_key(e: &Expr) -> String {
    format!("{e:?}")
}

/// Right-fold a non-empty leaf list `[x0, x1, ..., xn]` into
/// `x0 + (x1 + (... + xn))` (`Nat.add`-headed).
fn rfold(leaves: &[Expr]) -> Expr {
    let last = leaves.len() - 1;
    let mut acc = leaves[last].clone();
    for leaf in leaves[..last].iter().rev() {
        acc = nat_add(leaf.clone(), acc);
    }
    acc
}

/// Normalize `e` to its canonical sorted right-folded sum and return
/// `(canonical, proof : e = canonical)`.
///
/// Strategy:
///   1. Flatten `e` to its leaf list (proof `e = rfold(leaves)` via a
///      right-association chain).
///   2. Bubble-sort the right-folded list into canonical leaf order (each
///      adjacent swap is an `add_comm`/`add_assoc` step lifted by `congrArg`).
///
/// Returns `None` only if `e` is empty (cannot happen for a parsed Nat term) or
/// a builder invariant is violated; the caller fails closed.
pub(crate) fn normalize_to_canonical(e: &Expr) -> Option<(Expr, Expr)> {
    let leaves = flatten_add_leaves(e);
    if leaves.is_empty() {
        return None;
    }
    // Step 1: `e = rfold(leaves)`. Right-association of a left-nested `add`
    // tree is handled structurally by `prove_reassoc`.
    let folded = rfold(&leaves);
    let reassoc = prove_reassoc(e)?; // e = folded

    // Step 2: bubble-sort the right-folded list into canonical order.
    let mut current: Vec<Expr> = leaves;
    let mut proof = reassoc; // e = rfold(current)
    let mut current_lhs = folded; // rfold(current)
    let n = current.len();
    for i in 0..n {
        for j in 0..n - 1 - i {
            if leaf_key(&current[j]) > leaf_key(&current[j + 1]) {
                // Swap positions j, j+1 in the right-folded list.
                let (swap_proof, new_lhs) = swap_adjacent(&current, j)?;
                // proof : e = current_lhs ; swap_proof : current_lhs = new_lhs.
                proof = mk_trans(e, &current_lhs, &new_lhs, &proof, &swap_proof);
                current.swap(j, j + 1);
                current_lhs = new_lhs;
            }
        }
    }
    Some((current_lhs, proof))
}

/// Prove `e = rfold(flatten(e))` by re-associating the `add` tree to the right.
///
/// For a leaf, this is `Eq.refl e`. For `add l r`, recursively prove
/// `l = rfold(flatten l)` and `r = rfold(flatten r)`, lift them with `congrArg`
/// into `l + r = rfold(l) + rfold(r)`, then prove
/// `rfold(flatten l) + rfold(flatten r) = rfold(flatten l ++ flatten r)` by an
/// append-reassociation chain.
fn prove_reassoc(e: &Expr) -> Option<Expr> {
    // Leaf: reflexive.
    if !is_add(e) {
        return Some(mk_refl(e));
    }
    let (l, r) = nat_add_children(e)?;
    let l_leaves = flatten_add_leaves(&l);
    let r_leaves = flatten_add_leaves(&r);
    let l_fold = rfold(&l_leaves);
    let r_fold = rfold(&r_leaves);

    // hl : l = l_fold ; hr : r = r_fold
    let hl = prove_reassoc(&l)?;
    let hr = prove_reassoc(&r)?;
    // congr on `+`: l + r = l_fold + r_fold.
    let congr_l = mk_congr_add_right(&l, &l_fold, &r, &hl); // l + r = l_fold + r
    let congr_r = mk_congr_add_left(&l_fold, &r, &r_fold, &hr); // l_fold + r = l_fold + r_fold
    let lr = nat_add(l.clone(), r.clone());
    let lfold_r = nat_add(l_fold.clone(), r.clone());
    let lfold_rfold = nat_add(l_fold.clone(), r_fold.clone());
    let combined = mk_trans(&lr, &lfold_r, &lfold_rfold, &congr_l, &congr_r);

    // append: l_fold + r_fold = rfold(l_leaves ++ r_leaves).
    let mut all = l_leaves.clone();
    all.extend(r_leaves.iter().cloned());
    let target_fold = rfold(&all);
    if lfold_rfold == target_fold {
        return Some(combined);
    }
    let append = prove_append(&l_leaves, &r_leaves)?; // l_fold + r_fold = target_fold
    Some(mk_trans(
        &lr,
        &lfold_rfold,
        &target_fold,
        &combined,
        &append,
    ))
}

/// Prove `rfold(xs) + rfold(ys) = rfold(xs ++ ys)` for non-empty `xs`, `ys`.
///
/// Induct on `xs`:
///   - `xs = [x]`: `x + rfold(ys) = rfold([x] ++ ys)` is reflexive (the
///     right-fold of `[x, ys...]` IS `x + rfold(ys)`).
///   - `xs = x :: rest`: `(x + rfold(rest)) + rfold(ys)`
///       = `x + (rfold(rest) + rfold(ys))`        (add_assoc)
///       = `x + rfold(rest ++ ys)`                (congrArg of the IH)
///       = `rfold(x :: (rest ++ ys))`             (definitional fold).
fn prove_append(xs: &[Expr], ys: &[Expr]) -> Option<Expr> {
    debug_assert!(!xs.is_empty() && !ys.is_empty());
    let ys_fold = rfold(ys);
    if xs.len() == 1 {
        // x + rfold(ys) = rfold([x] ++ ys) — same expression, reflexive.
        let lhs = nat_add(xs[0].clone(), ys_fold);
        return Some(mk_refl(&lhs));
    }
    let x = &xs[0];
    let rest = &xs[1..];
    let rest_fold = rfold(rest);
    // lhs = (x + rest_fold) + ys_fold
    let lhs = nat_add(nat_add(x.clone(), rest_fold.clone()), ys_fold.clone());
    // assoc : (x + rest_fold) + ys_fold = x + (rest_fold + ys_fold)
    let assoc = mk_add_assoc(x, &rest_fold, &ys_fold);
    let mid = nat_add(x.clone(), nat_add(rest_fold.clone(), ys_fold.clone()));
    // IH : rest_fold + ys_fold = rfold(rest ++ ys)
    let ih = prove_append(rest, ys)?;
    let mut rest_ys = rest.to_vec();
    rest_ys.extend(ys.iter().cloned());
    let rest_ys_fold = rfold(&rest_ys);
    // congr : x + (rest_fold + ys_fold) = x + rfold(rest ++ ys)
    let inner_l = nat_add(rest_fold.clone(), ys_fold.clone());
    let congr = mk_congr_add_left(x, &inner_l, &rest_ys_fold, &ih);
    let final_rhs = nat_add(x.clone(), rest_ys_fold.clone());
    // assoc ; congr : lhs = x + rfold(rest ++ ys) = rfold(x :: rest ++ ys)
    Some(mk_trans(&lhs, &mid, &final_rhs, &assoc, &congr))
}

/// Prove a swap of the elements at right-folded positions `j`, `j+1`:
/// `rfold(list) = rfold(list with j, j+1 swapped)`. Returns the proof and the
/// new (swapped) right-folded expression.
fn swap_adjacent(list: &[Expr], j: usize) -> Option<(Expr, Expr)> {
    // Peel the `j`-element prefix; the swap happens at the head of the suffix.
    // suffix right-fold: a + (b + tail_fold)  -- where a = list[j], b = list[j+1].
    let a = &list[j];
    let b = &list[j + 1];
    let after = &list[j + 2..];

    // Build the suffix folds.
    let (b_tail, swapped_a_tail) = if after.is_empty() {
        // suffix = a + b ; swapped = b + a
        (b.clone(), a.clone())
    } else {
        let tail_fold = rfold(after);
        (
            nat_add(b.clone(), tail_fold.clone()),
            nat_add(a.clone(), tail_fold),
        )
    };
    // before: a + (b + tail) ; after: b + (a + tail)
    let suffix_before = nat_add(a.clone(), b_tail.clone());
    let suffix_after = nat_add(b.clone(), swapped_a_tail.clone());
    let swap_proof = prove_head_swap(a, b, after)?; // suffix_before = suffix_after

    // Lift the swap through the `j`-element prefix via nested congrArg on
    // `fun z => prefix[0] + (prefix[1] + ... + z)`.
    let prefix = &list[..j];
    let lifted = lift_through_prefix(prefix, &suffix_before, &suffix_after, &swap_proof);

    // Compute the full swapped right-folded expression.
    let mut new_list = list.to_vec();
    new_list.swap(j, j + 1);
    let new_fold = rfold(&new_list);
    Some((lifted, new_fold))
}

/// Prove the head swap `a + (b + tail) = b + (a + tail)` (or `a + b = b + a`
/// when `after` is empty), built from `add_comm` + `add_assoc`.
fn prove_head_swap(a: &Expr, b: &Expr, after: &[Expr]) -> Option<Expr> {
    if after.is_empty() {
        // a + b = b + a
        return Some(mk_add_comm(a, b));
    }
    let tail = rfold(after);
    // Eq.symm (add_assoc a b tail) : a + (b + tail) = (a + b) + tail
    let assoc1 = mk_add_assoc(a, b, &tail); // (a+b)+tail = a+(b+tail)
    let ab = nat_add(a.clone(), b.clone());
    let ab_tail = nat_add(ab.clone(), tail.clone());
    let a_bt = nat_add(a.clone(), nat_add(b.clone(), tail.clone()));
    let sym_assoc1 = mk_symm(&ab_tail, &a_bt, &assoc1); // a+(b+tail) = (a+b)+tail
                                                        // congrArg (fun z => z + tail) (add_comm a b) : (a+b)+tail = (b+a)+tail
    let comm = mk_add_comm(a, b); // a+b = b+a
    let ba = nat_add(b.clone(), a.clone());
    let congr = mk_congr_add_right(&ab, &ba, &tail, &comm); // (a+b)+tail = (b+a)+tail
    let ba_tail = nat_add(ba.clone(), tail.clone());
    // add_assoc b a tail : (b+a)+tail = b+(a+tail)
    let assoc2 = mk_add_assoc(b, a, &tail);
    let b_at = nat_add(b.clone(), nat_add(a.clone(), tail.clone()));
    // Chain: a+(b+tail) = (a+b)+tail = (b+a)+tail = b+(a+tail)
    let t1 = mk_trans(&a_bt, &ab_tail, &ba_tail, &sym_assoc1, &congr);
    Some(mk_trans(&a_bt, &ba_tail, &b_at, &t1, &assoc2))
}

/// Lift a proof `inner_before = inner_after` through a right-folded prefix
/// `p0 + (p1 + (... + ·))` by nested `congrArg (fun z => pk + z)`.
fn lift_through_prefix(
    prefix: &[Expr],
    inner_before: &Expr,
    inner_after: &Expr,
    proof: &Expr,
) -> Expr {
    let mut before = inner_before.clone();
    let mut after = inner_after.clone();
    let mut acc = proof.clone();
    for p in prefix.iter().rev() {
        acc = mk_congr_add_left(p, &before, &after, &acc);
        before = nat_add(p.clone(), before);
        after = nat_add(p.clone(), after);
    }
    acc
}

// ---------------------------------------------------------------------------
// Term builders (Eq / congrArg / Nat lemmas).
// ---------------------------------------------------------------------------

fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn nat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [lhs, rhs],
    )
}

fn is_add(e: &Expr) -> bool {
    if let ExprKind::Const(op, _) = e.get_app_fn().kind() {
        let op_s = op.to_string();
        (op_s == "Nat.add" || op_s == "HAdd.hAdd" || op_s == "Add.add")
            && e.get_app_args().len() >= 2
    } else {
        false
    }
}

/// `Nat.mul lhs rhs`.
fn nat_mul(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.mul"), vec![]),
        [lhs, rhs],
    )
}

// ---------------------------------------------------------------------------
// Literal-coefficient multiplication expansion.
//
// A leaf `k * atom` / `atom * k` (literal `k`, symbolic `atom`) is expanded into
// the additive right-fold `atom + (atom + … + atom)` (`k` copies), carried by a
// proof `k * atom = fold`. This turns `2 * a = a + a` into the pure additive
// permutation `a + a = a + a` that the canonical normalizer already discharges.
//
// The lemmas used are Clean's DEFAULT-prelude Nat lemmas (verified orientations):
//   * `Nat.succ_mul n m : Nat.mul (Nat.succ n) m = Nat.add m (Nat.mul n m)`
//   * `Nat.one_mul m     : Nat.mul 1 m = m`
//   * `Nat.zero_mul m    : Nat.mul 0 m = 0`
//   * `Nat.mul_succ a b  : Nat.mul a (Nat.succ b) = Nat.add a (Nat.mul a b)`
//   * `Nat.mul_one a     : Nat.mul a 1 = a`
//   * `Nat.mul_zero a    : Nat.mul a 0 = 0`
// The kernel accepts these with LITERAL arguments because `Nat.succ (lit k)` is
// def-eq to `lit (k+1)`, and `HMul.hMul Nat Nat Nat inst` is def-eq to `Nat.mul`,
// so the original surface `k * atom` leaf (an `HMul` spine) is proved equal to a
// `Nat.mul`-based expansion. All lemmas have empty axiom closure (foundational).
// ---------------------------------------------------------------------------

/// The side a literal factor sits on in a `mul` leaf.
#[derive(Clone, Copy)]
enum LitSide {
    /// `k * atom` — literal on the left (`Nat.succ_mul` orientation).
    Left,
    /// `atom * k` — literal on the right (`Nat.mul_succ` orientation).
    Right,
}

/// If `e` is a `Nat`/`H`/generic `mul` leaf `k * atom` or `atom * k` with a
/// literal `k` and a *symbolic* (non-literal) `atom`, return `(k, atom, side)`.
/// Returns `None` for non-mul leaves, symbolic×symbolic products (non-linear),
/// and literal×literal products (handled by the constant folder).
fn match_lit_mul(e: &Expr) -> Option<(u64, Expr, LitSide)> {
    let args = e.get_app_args();
    if args.len() < 2 {
        return None;
    }
    let ExprKind::Const(op, _) = e.get_app_fn().kind() else {
        return None;
    };
    let op_s = op.to_string();
    if op_s != "Nat.mul" && op_s != "HMul.hMul" && op_s != "Mul.mul" {
        return None;
    }
    let lhs = args[args.len() - 2];
    let rhs = args[args.len() - 1];
    // A whole-literal product is handled by `eval_nat_expr`/constant folding, not
    // here; and a symbolic×symbolic product is non-linear. Require exactly one
    // literal side.
    let l_val = eval_nat_expr(lhs);
    let r_val = eval_nat_expr(rhs);
    match (l_val, r_val) {
        (Some(k), None) => Some((k, rhs.clone(), LitSide::Left)),
        (None, Some(k)) => Some((k, lhs.clone(), LitSide::Right)),
        _ => None,
    }
}

/// Prove `k * atom = fold(k copies of atom)` (or `= 0` for `k == 0`), returning
/// `(expanded, proof)` where `expanded` is the `Nat.add`-headed right-fold
/// `atom + (atom + … + atom)` for `k >= 1`, or `Nat.lit 0` for `k == 0`.
///
/// The `mul_expr` argument is the ORIGINAL surface leaf (e.g. an `HMul` spine);
/// the proof is typed at `mul_expr = expanded`, which the kernel accepts because
/// the surface `mul` head is def-eq to `Nat.mul`.
///
/// ENSURES: `expanded` contains no `mul` (pure `Nat.add` / atom / literal).
/// ENSURES: On `Some`, the proof is a foundational-lemma chain (zero axioms).
fn expand_lit_mul(mul_expr: &Expr, k: u64, atom: &Expr, side: LitSide) -> Option<(Expr, Expr)> {
    match side {
        LitSide::Left => expand_lit_mul_left(mul_expr, k, atom),
        LitSide::Right => expand_lit_mul_right(mul_expr, k, atom),
    }
}

/// `k * atom` expansion via `Nat.succ_mul` / `Nat.one_mul` / `Nat.zero_mul`.
///
/// `k >= 2`:  `k * atom = atom + (k-1) * atom`      (`Nat.succ_mul (k-1) atom`)
///            then recurse on `(k-1) * atom` and lift by `congrArg (atom + ·)`.
/// `k == 1`:  `1 * atom = atom`                     (`Nat.one_mul atom`)
/// `k == 0`:  `0 * atom = 0`                        (`Nat.zero_mul atom`)
fn expand_lit_mul_left(mul_expr: &Expr, k: u64, atom: &Expr) -> Option<(Expr, Expr)> {
    if k == 0 {
        let zero = Expr::nat_lit(0);
        return Some((zero, mk_zero_mul(atom)));
    }
    if k == 1 {
        return Some((atom.clone(), mk_one_mul(atom)));
    }
    // k >= 2: succ_mul (k-1) atom : k * atom = atom + (k-1)*atom.
    let km1 = k - 1;
    let km1_lit = Expr::nat_lit(km1);
    let sub_mul = nat_mul(km1_lit.clone(), atom.clone()); // (k-1) * atom
    let step = mk_succ_mul(&km1_lit, atom); // k*atom = atom + (k-1)*atom
    let atom_plus_sub = nat_add(atom.clone(), sub_mul.clone());
    // Recurse: sub_mul = sub_expanded, then lift into atom + sub_expanded.
    let (sub_expanded, sub_proof) = expand_lit_mul_left(&sub_mul, km1, atom)?;
    let congr = mk_congr_add_left(atom, &sub_mul, &sub_expanded, &sub_proof);
    let final_rhs = nat_add(atom.clone(), sub_expanded);
    // mul_expr = atom + (k-1)*atom = atom + sub_expanded.
    Some((
        final_rhs.clone(),
        mk_trans(mul_expr, &atom_plus_sub, &final_rhs, &step, &congr),
    ))
}

/// `atom * k` expansion via `Nat.mul_succ` / `Nat.mul_one` / `Nat.mul_zero`.
///
/// `k >= 2`:  `atom * k = atom + atom * (k-1)`      (`Nat.mul_succ atom (k-1)`)
/// `k == 1`:  `atom * 1 = atom`                     (`Nat.mul_one atom`)
/// `k == 0`:  `atom * 0 = 0`                        (`Nat.mul_zero atom`)
fn expand_lit_mul_right(mul_expr: &Expr, k: u64, atom: &Expr) -> Option<(Expr, Expr)> {
    if k == 0 {
        let zero = Expr::nat_lit(0);
        return Some((zero, mk_mul_zero(atom)));
    }
    if k == 1 {
        return Some((atom.clone(), mk_mul_one(atom)));
    }
    let km1 = k - 1;
    let km1_lit = Expr::nat_lit(km1);
    let sub_mul = nat_mul(atom.clone(), km1_lit.clone()); // atom * (k-1)
    let step = mk_mul_succ(atom, &km1_lit); // atom*k = atom + atom*(k-1)
    let atom_plus_sub = nat_add(atom.clone(), sub_mul.clone());
    let (sub_expanded, sub_proof) = expand_lit_mul_right(&sub_mul, km1, atom)?;
    let congr = mk_congr_add_left(atom, &sub_mul, &sub_expanded, &sub_proof);
    let final_rhs = nat_add(atom.clone(), sub_expanded);
    Some((
        final_rhs.clone(),
        mk_trans(mul_expr, &atom_plus_sub, &final_rhs, &step, &congr),
    ))
}

/// Walk the additive structure of `e`, expanding every literal-coefficient
/// multiplication leaf into its additive fold, and return `(expanded, proof)`
/// with `proof : e = expanded`. Non-mul leaves (atoms, literals, `succ …`) are
/// preserved verbatim with a reflexive local proof.
///
/// The recursion mirrors [`prove_reassoc`]: an `add` node lifts its children's
/// expansion proofs with `congrArg` on `+`; a mul leaf is expanded by
/// [`expand_lit_mul`]; any other leaf is reflexive.
///
/// ENSURES: On `Some((exp, p))`, `exp` contains no linear-coefficient `mul` leaf
///   and `p : e = exp` is a foundational-lemma chain (zero domain axioms).
/// ENSURES: Returns `None` only if a builder invariant is violated (fail closed).
fn expand_mul_leaves(e: &Expr) -> Option<(Expr, Expr)> {
    // Additive node: recurse on both children, lift with congr on `+`.
    if is_add(e) {
        let (l, r) = nat_add_children(e)?;
        let (l_exp, l_proof) = expand_mul_leaves(&l)?; // l = l_exp
        let (r_exp, r_proof) = expand_mul_leaves(&r)?; // r = r_exp
                                                       // l + r = l_exp + r  (congr on left)
        let congr_l = mk_congr_add_right(&l, &l_exp, &r, &l_proof);
        // l_exp + r = l_exp + r_exp  (congr on right)
        let congr_r = mk_congr_add_left(&l_exp, &r, &r_exp, &r_proof);
        let lr = nat_add(l.clone(), r.clone());
        let lexp_r = nat_add(l_exp.clone(), r.clone());
        let lexp_rexp = nat_add(l_exp.clone(), r_exp.clone());
        let proof = mk_trans(&lr, &lexp_r, &lexp_rexp, &congr_l, &congr_r);
        return Some((lexp_rexp, proof));
    }

    // Literal-coefficient multiplication leaf: expand into the additive fold.
    if let Some((k, atom, side)) = match_lit_mul(e) {
        return expand_lit_mul(e, k, &atom, side);
    }

    // Any other leaf (atom, literal, `succ …`, symbolic×symbolic mul that the
    // parser already rejected upstream): unchanged, reflexive proof.
    Some((e.clone(), mk_refl(e)))
}

/// Extract `(a, b)` from `Nat.add a b` / `HAdd.hAdd .. a b` / `Add.add a b`.
fn nat_add_children(expr: &Expr) -> Option<(Expr, Expr)> {
    let args = expr.get_app_args();
    if args.len() >= 2 {
        if let ExprKind::Const(op, _) = expr.get_app_fn().kind() {
            let op_s = op.to_string();
            if op_s == "Nat.add" || op_s == "HAdd.hAdd" || op_s == "Add.add" {
                return Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()));
            }
        }
    }
    None
}

/// `@Eq.refl Nat a : @Eq Nat a a`.
fn mk_refl(a: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_ty(), a.clone()],
    )
}

/// `@Eq.symm Nat a b h : @Eq Nat b a` where `h : @Eq Nat a b`.
fn mk_symm(a: &Expr, b: &Expr, h: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_ty(), a.clone(), b.clone(), h.clone()],
    )
}

/// `@Eq.trans Nat a b c h1 h2 : @Eq Nat a c` where `h1 : a = b`, `h2 : b = c`.
fn mk_trans(a: &Expr, b: &Expr, c: &Expr, h1: &Expr, h2: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [
            nat_ty(),
            a.clone(),
            b.clone(),
            c.clone(),
            h1.clone(),
            h2.clone(),
        ],
    )
}

/// `Nat.add_comm a b : @Eq Nat (a + b) (b + a)`.
fn mk_add_comm(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.add_comm"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// `Nat.add_assoc a b c : @Eq Nat ((a + b) + c) (a + (b + c))`.
fn mk_add_assoc(a: &Expr, b: &Expr, c: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.add_assoc"), vec![]),
        [a.clone(), b.clone(), c.clone()],
    )
}

/// `Nat.succ_mul n m : @Eq Nat (Nat.mul (Nat.succ n) m) (Nat.add m (Nat.mul n m))`.
/// Applied with a literal `n`, the LHS is def-eq to `(n+1) * m`.
fn mk_succ_mul(n: &Expr, m: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.succ_mul"), vec![]),
        [n.clone(), m.clone()],
    )
}

/// `Nat.one_mul m : @Eq Nat (Nat.mul 1 m) m`.
fn mk_one_mul(m: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.one_mul"), vec![]),
        [m.clone()],
    )
}

/// `Nat.zero_mul m : @Eq Nat (Nat.mul 0 m) 0`.
fn mk_zero_mul(m: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.zero_mul"), vec![]),
        [m.clone()],
    )
}

/// `Nat.mul_succ a b : @Eq Nat (Nat.mul a (Nat.succ b)) (Nat.add a (Nat.mul a b))`.
/// Applied with a literal `b`, the LHS is def-eq to `a * (b+1)`.
fn mk_mul_succ(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.mul_succ"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// `Nat.mul_one a : @Eq Nat (Nat.mul a 1) a`.
fn mk_mul_one(a: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.mul_one"), vec![]),
        [a.clone()],
    )
}

/// `Nat.mul_zero a : @Eq Nat (Nat.mul a 0) 0`.
fn mk_mul_zero(a: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.mul_zero"), vec![]),
        [a.clone()],
    )
}

/// `congrArg (fun z => a + z) h : @Eq Nat (a + b1) (a + b2)` where
/// `h : @Eq Nat b1 b2`.
fn mk_congr_add_left(a: &Expr, b1: &Expr, b2: &Expr, h: &Expr) -> Expr {
    let motive = {
        // fun (z : Nat) => Nat.add a z
        let body = nat_add(a.clone(), Expr::bvar(0));
        Expr::lam(BinderInfo::Default, nat_ty(), body)
    };
    mk_congr_arg(b1, b2, &motive, h)
}

/// `congrArg (fun z => z + b) h : @Eq Nat (a1 + b) (a2 + b)` where
/// `h : @Eq Nat a1 a2`.
fn mk_congr_add_right(a1: &Expr, a2: &Expr, b: &Expr, h: &Expr) -> Expr {
    let motive = {
        // fun (z : Nat) => Nat.add z b
        let body = nat_add(Expr::bvar(0), b.clone());
        Expr::lam(BinderInfo::Default, nat_ty(), body)
    };
    mk_congr_arg(a1, a2, &motive, h)
}

/// `@congrArg.{1,1} Nat Nat x y f h : @Eq Nat (f x) (f y)` where
/// `h : @Eq Nat x y` and `f : Nat → Nat`.
fn mk_congr_arg(x: &Expr, y: &Expr, f: &Expr, h: &Expr) -> Expr {
    let u = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![u.clone(), u]),
        [
            nat_ty(),
            nat_ty(),
            x.clone(),
            y.clone(),
            f.clone(),
            h.clone(),
        ],
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
            [nat_ty(), l, r],
        )
    }

    #[test]
    fn test_parse_linear_form_add_comm_equal() {
        let a = atom("a");
        let b = atom("b");
        let lhs = parse_nat_linear_form(&nat_add(a.clone(), b.clone())).unwrap();
        let rhs = parse_nat_linear_form(&nat_add(b, a)).unwrap();
        assert!(lhs.equals(&rhs), "a+b and b+a must have equal linear forms");
    }

    #[test]
    fn test_parse_linear_form_false_not_equal() {
        let a = atom("a");
        let b = atom("b");
        let lhs = parse_nat_linear_form(&nat_add(a.clone(), b)).unwrap();
        let rhs = parse_nat_linear_form(&a).unwrap();
        assert!(!lhs.equals(&rhs), "a+b and a must differ");
    }

    #[test]
    fn test_two_mul_equals_a_plus_a_form() {
        // 2 * a  vs  a + a
        let a = atom("a");
        let two_a = Expr::apps(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            [Expr::nat_lit(2), a.clone()],
        );
        let a_plus_a = nat_add(a.clone(), a);
        let l = parse_nat_linear_form(&two_a).unwrap();
        let r = parse_nat_linear_form(&a_plus_a).unwrap();
        assert!(l.equals(&r), "2*a and a+a must have equal linear forms");
    }

    #[test]
    fn test_synthesize_returns_some_for_add_comm() {
        let a = atom("a");
        let b = atom("b");
        let goal = eq_goal(nat_add(a.clone(), b.clone()), nat_add(b, a));
        assert!(
            try_prove_nat_equality_direct(&goal).is_some(),
            "a+b=b+a must synthesize a proof"
        );
    }

    #[test]
    fn test_synthesize_returns_none_for_false_eq() {
        let a = atom("a");
        let b = atom("b");
        // a + b = a  (FALSE)
        let goal = eq_goal(nat_add(a.clone(), b), a);
        assert!(
            try_prove_nat_equality_direct(&goal).is_none(),
            "a+b=a is false and must NOT synthesize"
        );
    }

    #[test]
    fn test_synthesize_returns_none_for_a_eq_b() {
        let a = atom("a");
        let b = atom("b");
        let goal = eq_goal(a, b);
        assert!(
            try_prove_nat_equality_direct(&goal).is_none(),
            "a=b is false and must NOT synthesize"
        );
    }

    #[test]
    fn test_synthesize_ground_constant_fold_true() {
        // `2 + 1 = 3`: both sides ground and equal — the ground-constant fast
        // path emits `Eq.refl`. (Previously failed: the additive normalizer
        // treated `2`, `1`, `3` as distinct unorderable leaves.)
        let goal = eq_goal(
            nat_add(Expr::nat_lit(2), Expr::nat_lit(1)),
            Expr::nat_lit(3),
        );
        assert!(
            try_prove_nat_equality_direct(&goal).is_some(),
            "2 + 1 = 3 should synthesize via the ground-constant fast path"
        );
    }

    #[test]
    fn test_synthesize_ground_constant_fold_false() {
        // `2 + 1 = 4`: both sides ground but UNEQUAL — the decision gate rejects
        // it (the ground fast path never fires for unequal values).
        let goal = eq_goal(
            nat_add(Expr::nat_lit(2), Expr::nat_lit(1)),
            Expr::nat_lit(4),
        );
        assert!(
            try_prove_nat_equality_direct(&goal).is_none(),
            "2 + 1 = 4 is false and must NOT synthesize"
        );
    }

    #[test]
    fn test_synthesize_eq_from_hyp_pins_then_ground_folds() {
        // `(h : a = 2) ⊢ a + 1 = 3`: substituting `a := 2` leaves the ground
        // residual `2 + 1 = 3`, closed by the ground-constant fast path.
        let a = atom("a");
        let hyp_ty = eq_goal(a.clone(), Expr::nat_lit(2));
        let goal = eq_goal(nat_add(a.clone(), Expr::nat_lit(1)), Expr::nat_lit(3));
        let hyp_fvar = atom("h");
        assert!(
            try_prove_nat_equality_from_hyps(&goal, &[(hyp_fvar, hyp_ty)]).is_some(),
            "(h : a = 2) ⊢ a + 1 = 3 should synthesize"
        );
    }

    #[test]
    fn test_synthesize_returns_none_for_off_by_one() {
        let a = atom("a");
        let b = atom("b");
        // a + b = a + b + 1  (FALSE)
        let lhs = nat_add(a.clone(), b.clone());
        let rhs = nat_add(nat_add(a, b), Expr::nat_lit(1));
        let goal = eq_goal(lhs, rhs);
        assert!(
            try_prove_nat_equality_direct(&goal).is_none(),
            "a+b = a+b+1 is false and must NOT synthesize"
        );
    }

    /// Build `Nat.mul lhs rhs` in the test module (mirrors the production helper).
    fn tmul(lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            [lhs, rhs],
        )
    }

    #[test]
    fn test_synthesize_two_mul_left_eq_a_plus_a() {
        // 2 * a = a + a  (TRUE, literal factor on the left).
        let a = atom("a");
        let goal = eq_goal(tmul(Expr::nat_lit(2), a.clone()), nat_add(a.clone(), a));
        assert!(
            try_prove_nat_equality_direct(&goal).is_some(),
            "2 * a = a + a must now synthesize via succ_mul expansion"
        );
    }

    #[test]
    fn test_synthesize_three_mul_left_eq_a_plus_a_plus_a() {
        // 3 * a = a + a + a  (TRUE).
        let a = atom("a");
        let rhs = nat_add(nat_add(a.clone(), a.clone()), a.clone());
        let goal = eq_goal(tmul(Expr::nat_lit(3), a.clone()), rhs);
        assert!(
            try_prove_nat_equality_direct(&goal).is_some(),
            "3 * a = a + a + a must synthesize"
        );
    }

    #[test]
    fn test_synthesize_two_mul_right_eq_a_plus_a() {
        // a * 2 = a + a  (TRUE, literal factor on the right → mul_succ).
        let a = atom("a");
        let goal = eq_goal(tmul(a.clone(), Expr::nat_lit(2)), nat_add(a.clone(), a));
        assert!(
            try_prove_nat_equality_direct(&goal).is_some(),
            "a * 2 = a + a must synthesize via mul_succ expansion"
        );
    }

    #[test]
    fn test_synthesize_two_mul_eq_a_still_false() {
        // 2 * a = a  (FALSE): forms differ, must NOT synthesize even with the
        // expansion pass (the decision gate rejects before expansion).
        let a = atom("a");
        let goal = eq_goal(tmul(Expr::nat_lit(2), a.clone()), a);
        assert!(
            try_prove_nat_equality_direct(&goal).is_none(),
            "2 * a = a is FALSE and must NOT synthesize"
        );
    }

    #[test]
    fn test_synthesize_two_mul_eq_three_a_still_false() {
        // 2 * a = a + a + a  (FALSE): 2·a vs 3·a forms differ.
        let a = atom("a");
        let rhs = nat_add(nat_add(a.clone(), a.clone()), a.clone());
        let goal = eq_goal(tmul(Expr::nat_lit(2), a.clone()), rhs);
        assert!(
            try_prove_nat_equality_direct(&goal).is_none(),
            "2 * a = a + a + a is FALSE and must NOT synthesize"
        );
    }

    #[test]
    fn test_expand_mul_leaves_no_mul_is_reflexive() {
        // A mul-free expression expands to itself.
        let a = atom("a");
        let e = nat_add(a.clone(), a);
        let (exp, _p) = expand_mul_leaves(&e).expect("mul-free expansion");
        assert_eq!(exp, e, "mul-free expansion must be identity");
    }
}
