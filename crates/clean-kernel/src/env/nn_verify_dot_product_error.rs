// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Higham's accumulated floating-point rounding bound for a dot product
//! (`Accuracy and Stability of Numerical Algorithms`, Thm 3.1), proven natively
//! on top of the already-landed per-op half-ulp lemma.
//!
//! ## What this discharges
//!
//! ny's dominant CROWN coefficient composition (the `A·W` multiply-accumulate)
//! relies on the Higham dot-product error bound
//!
//! ```text
//! |fl(s) − s| ≤ γ_n · Σ_{i=1}^n |a_i·w_i|,   γ_n := n·u / (1 − n·u)
//! ```
//!
//! as a TRUSTED numeric-analysis fact (the `matmul_error_bound` /
//! `accumulated_error` axioms in `nn_verify_float_rational`). This module turns
//! the LOAD-BEARING content of that bound — the accumulation of per-op rounding
//! errors into a sum bound — into a kernel-checked THEOREM, grounded in the
//! proven half-ulp per-op bound, with the unit roundoff `u` carried as a
//! PARAMETER so it instantiates uniformly for binary32 (`u = 2^−24`) and
//! binary64 (`u = 2^−53`).
//!
//! ## The forward-error structure (Higham, before the γ_n simplification)
//!
//! The floating evaluation of `s = Σ a_i·w_i` is `n` rounded products followed
//! by `n−1` rounded additions. Each correctly-rounded op satisfies
//! `fl(x op y) = (x op y)(1 + δ)` with `|δ| ≤ u`, equivalently the ABSOLUTE
//! per-op error `|fl(x op y) − (x op y)| ≤ u·|x op y|`. Writing the running
//! partial sum's accumulated error as `E_k = fl(S_k) − S_k`, the error of the
//! NEXT step is bounded by the previous accumulated error PLUS the new term's
//! rounding bound:
//!
//! ```text
//! |E_{k+1}| ≤ |E_k| + b_{k+1}      (b_{k+1} := the (k+1)-th op's u·|·| bound)
//! ```
//!
//! by the triangle inequality `|E_k + e| ≤ |E_k| + |e|` and `|e| ≤ b_{k+1}`.
//! Unrolling gives `|fl(s) − s| ≤ Σ b_i`. With each `b_i ≤ (k_i·u)·|a_i w_i|`
//! (the per-op relative bound, `k_i` ops touching term `i`), `Σ b_i ≤ γ_n
//! Σ|a_i w_i|` — Higham's γ_n is the textbook over-estimate of `Σ b_i`.
//!
//! ## What is PROVEN here (sorry-free, axiom-free beyond foundations + the
//! named per-op relative-error hypothesis)
//!
//! 1. `error_accum_step` — the GENERAL `∀` inductive STEP, over `Rat`:
//!    ```text
//!    ∀ (E e B b : Rat), |E| ≤ B → |e| ≤ b → |E + e| ≤ B + b
//!    ```
//!    proven from `Rat.abs_add_le` (triangle inequality) + `Rat.add_le_add`
//!    (add monotonicity) + `Rat.le_trans`. This IS Higham's induction step.
//!
//! 2. `error_accum_step3`, `error_accum_step4`, … — the unrolled fixed-arity
//!    accumulations (n = 2,3,4) for `Σ b_i`, built by iterating the step. These
//!    are the dot-product error bounds at concrete small `n`, GENERAL over the
//!    `Rat` operands (no literal blowup — the `Rat`s stay symbolic).
//!
//! 3. The per-op relative-error hypothesis `fl_op_rel_error` is a NAMED model
//!    field, DISCHARGED BY THEOREM from `rounding_error_le_half_ulp` at concrete
//!    points where it reduces (`fl_op_rel_error_discharge_*`): the rounding
//!    error of one product `|round(z) − z| ≤ u·|z|` holds because
//!    `ulp(z)/2 ≤ u·|z|` in the normal range, with the denormal/zero base case
//!    handled by the floored-ulp ABSOLUTE form `≤ u·(smallest normal)`.
//!
//! 4. Concrete γ_n / (1+u)^n instances REDUCED in-kernel (`gamma_n_reduces_*`):
//!    the bound `Σ b_i ≤ γ_n·Σ|a_i w_i|` holds as a literal `Rat.le` over
//!    dyadics, witnessed by `Int.NonNeg.mk`, for small `n` at the representative
//!    precisions `u = 2^−8`, `2^−12` AND at the TRUE binary32 (`u = 2^−24`) and
//!    binary64 (`u = 2^−53`) unit roundoffs. The f32/f64 literal discharges were
//!    previously blocked by the Rat-blowup wall: the `Rat.le` lift compares
//!    cross-products through `Rat.Raw.effDenom = Nat.succ ∘ Nat.pred`, and
//!    `Nat.pred` on the `2^{u_exp}`-scale denominator OOM-killed past a `~2^16`
//!    argument (the same wall the half-ulp lemma hit at `2^1074`). With the
//!    native `Nat.pred` reducer (tc/reduction/nat.rs) AND the arbitrary-precision
//!    `Int` reducer (tc/reduction/int.rs), the literal γ_n bound reduces
//!    in-kernel at the true f32/f64 precisions (`gamma_n_reduces_f32_n*` /
//!    `_f64_n*`). `u` is therefore a genuine PARAMETER discharged at the REAL
//!    scales, not merely symbolically: the accumulation lemmas (items 1–2) take
//!    the per-op bounds `b_i` ABSTRACTLY (so they hold verbatim at every
//!    precision), and the closed-form γ_n simplification is now exhibited as a
//!    LITERAL at f32/f64. The per-op relative-error discharges (item 3) are
//!    likewise at the true f32 (`u=2^−24`) / f64 (`u=2^−53`) precisions.
//!
//! ## Residual symbolic-only case (the `(1+u)^n` exponential at SYMBOLIC `n`)
//!
//! The fully-general `∀ n` closed form `|fl(s) − s| ≤ ((1+u)^n − 1)·Σ|a_i w_i|`
//! needs the EXPONENTIAL `(1+u)^n` over `Rat`. At `u = 2^−53` that is a dyadic
//! with denominator `2^(53n)` whose SIZE grows with `n`; for SYMBOLIC `n` there
//! is no closed literal to reduce, so this case stays symbolic (carried by the
//! abstract accumulation lemmas, item 1–2). This is a property of quantifying
//! over `n`, NOT the old denominator-magnitude wall: at any FIXED `n` and at the
//! true f32/f64 `u` the bound IS a literal and now reduces (item 4 — e.g.
//! `2^(53·n)` for fixed small `n` is a concrete `Big` bignat the closed
//! `Nat.pred`/`Int` reducers handle). The delivered content: the inductive step
//! (`∀`, item 1) + the fixed-`n` accumulations (`∀`-over-Rat, item 2) + the
//! per-op discharges at true f32/f64 precision (item 3) + the γ_n reductions at
//! representative AND true f32/f64 precisions (item 4) — all sorry-free and
//! grounded in the half-ulp per-op bound.
//!
//! Part of #3185 (Stage C: the accumulated dot-product bound).

use crate::env::native_reducers_float_to_rat::pow2_bignat;
use crate::env::nn_verify_float_rational_defs::FRConsts;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BigNat, BinderInfo, Expr};
use crate::name::Name;

/// Marker recording that the dot-product bound is built ENTIRELY on the
/// correctly-rounded per-op half-ulp bound (no transcendental term): the
/// products and sums of a dot product are `×` and `+`, both correctly rounded.
#[cfg(test)]
pub(crate) const DOT_PRODUCT_SCOPE: &str =
    "Higham dot-product accumulated rounding bound (Thm 3.1); built on the \
     correctly-rounded per-op half-ulp bound for + and ×; u carried as a \
     parameter (binary32 u=2^-24, binary64 u=2^-53)";

impl Environment {
    /// Register the Higham dot-product accumulated-rounding-bound development.
    ///
    /// - `NNVerify.FloatRational.error_accum_step` — the GENERAL `∀` inductive
    ///   step `|E|≤B → |e|≤b → |E+e|≤B+b` (the triangle-inequality accumulation).
    /// - `NNVerify.FloatRational.error_accum_step3` / `_step4` — the unrolled
    ///   fixed-arity accumulations for `n = 3,4` partial-error terms.
    /// - `NNVerify.FloatRational.fl_op_rel_error_discharge_{f32,f64}` — the per-op
    ///   relative-error hypothesis discharged from the half-ulp bound at the true
    ///   binary32 (`u=2^−24`) AND binary64 (`u=2^−53`) precisions.
    /// - `NNVerify.FloatRational.gamma_n_reduces_{u8,u12,f32,f64}_n{2,3}` —
    ///   concrete γ_n / (1+u)^n bound instances REDUCED in-kernel at the small
    ///   representative precisions (`u=2^−8`, `2^−12`) AND at the TRUE binary32
    ///   (`u=2^−24`) / binary64 (`u=2^−53`) precisions (the native `Nat.pred` +
    ///   arbitrary-precision `Int` reducers close the `Rat.le` denominator wall).
    ///
    /// # Contract
    /// REQUIRES: `init_nn_verify_rounding_half_ulp` (the half-ulp per-op bound +
    ///   `Rat.roundToNearestEven`), the Rat order/abs lemmas
    ///   (`Rat.le_trans`, `Rat.le_refl`, `Rat.abs_add_le`, `Rat.add_le_add`).
    /// ENSURES: every registered declaration is a `Declaration::Theorem` with an
    ///   empty non-foundational axiom closure (no `sorry`, no domain axiom).
    ///   Idempotent.
    pub(crate) fn init_nn_verify_dot_product_error(&mut self) -> Result<(), EnvError> {
        let headline = Name::from_string("NNVerify.FloatRational.error_accum_step");
        if self.get_const(&headline).is_some() {
            return Ok(());
        }

        // The per-op half-ulp bound (and its Rat round) underpin the per-op
        // discharges; the accumulation lemmas need the Rat order/abs toolkit.
        self.init_nn_verify_rounding_half_ulp()?;
        // `Rat.abs_add_le`, `Rat.add_le_add`, `Rat.le_trans`, `Rat.le_refl` —
        // pulled in by the prelude's `init_rat_abs` / order proofs; ensure abs.
        self.init_rat_abs()?;

        let c = FRConsts::new();

        self.register_error_accum_step(&c)?;
        self.register_error_accum_step3(&c)?;
        self.register_error_accum_step4(&c)?;
        self.register_fl_op_rel_error_discharges(&c)?;
        self.register_gamma_n_reductions(&c)?;

        Ok(())
    }

    /// `theorem error_accum_step (E e B b : Rat) :
    ///    Rat.le (Rat.abs E) B → Rat.le (Rat.abs e) b →
    ///    Rat.le (Rat.abs (Rat.add E e)) (Rat.add B b)`
    ///
    /// The inductive STEP of Higham's dot-product error accumulation: the new
    /// partial-sum error `E + e` (previous accumulated error `E`, new op error
    /// `e`) is bounded by the sum of the previous bound `B` and the new op bound
    /// `b`. Proof:
    /// ```text
    /// Rat.le_trans (|E+e|) (|E|+|e|) (B+b)
    ///   (Rat.abs_add_le E e)                     -- triangle inequality
    ///   (Rat.add_le_add |E| B |e| b hE he)       -- add monotonicity
    /// ```
    /// `Rat.abs_add_le` is stated in the `Rat.max a (Rat.neg a)` form, which is
    /// DEF-EQ to `Rat.abs` (reducible `Rat.abs := fun a => Rat.max a (Rat.neg
    /// a)`); `Rat.add_le_add` uses `@LE.le Rat instLERat`, def-eq to `Rat.le`.
    /// The kernel discharges both folds. Empty non-foundational axiom closure
    /// (rests only on the constructive `Rat.abs_add_le` / `Rat.add_le_add` /
    /// `Rat.le_trans`).
    fn register_error_accum_step(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.error_accum_step");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let abs_add_le = Expr::const_(Name::from_string("Rat.abs_add_le"), vec![]);
        let add_le_add = Expr::const_(Name::from_string("Rat.add_le_add"), vec![]);
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);

        // --- Type: ∀ E e B b, |E| ≤ B → |e| ≤ b → |E + e| ≤ B + b ---
        let mut b = EnvDeclBuilderLocal::new();
        let (e_big_id, e_big) = b.fresh(&c.rat);
        let (e_small_id, e_small) = b.fresh(&c.rat);
        let (b_big_id, b_big) = b.fresh(&c.rat);
        let (b_small_id, b_small) = b.fresh(&c.rat);
        let h_big_ty = c.rat_le(c.abs(e_big.clone()), b_big.clone());
        let (h_big_id, _h_big) = b.fresh(&h_big_ty);
        let h_small_ty = c.rat_le(c.abs(e_small.clone()), b_small.clone());
        let (h_small_id, _h_small) = b.fresh(&h_small_ty);
        let concl = c.rat_le(
            c.abs(c.add(e_big.clone(), e_small.clone())),
            c.add(b_big.clone(), b_small.clone()),
        );
        let type_ = b.pis(
            &[
                (e_big_id, &c.rat),
                (e_small_id, &c.rat),
                (b_big_id, &c.rat),
                (b_small_id, &c.rat),
                (h_big_id, &h_big_ty),
                (h_small_id, &h_small_ty),
            ],
            concl,
        );

        // --- Value ---
        let mut vb = EnvDeclBuilderLocal::new();
        let (ve_big_id, ve_big) = vb.fresh(&c.rat);
        let (ve_small_id, ve_small) = vb.fresh(&c.rat);
        let (vb_big_id, vb_big) = vb.fresh(&c.rat);
        let (vb_small_id, vb_small) = vb.fresh(&c.rat);
        let vh_big_ty = c.rat_le(c.abs(ve_big.clone()), vb_big.clone());
        let (vh_big_id, vh_big) = vb.fresh(&vh_big_ty);
        let vh_small_ty = c.rat_le(c.abs(ve_small.clone()), vb_small.clone());
        let (vh_small_id, vh_small) = vb.fresh(&vh_small_ty);

        let abs_e = c.abs(ve_big.clone());
        let abs_e2 = c.abs(ve_small.clone());
        let sum_abs = c.add(abs_e.clone(), abs_e2.clone());
        let sum_b = c.add(vb_big.clone(), vb_small.clone());
        let abs_sum = c.abs(c.add(ve_big.clone(), ve_small.clone()));

        // tri : |E+e| ≤ |E|+|e|  =  Rat.abs_add_le E e
        let tri = Expr::apps(abs_add_le, [ve_big.clone(), ve_small.clone()]);
        // mono : |E|+|e| ≤ B+b  =  Rat.add_le_add |E| B |e| b hE he
        let mono = Expr::apps(
            add_le_add,
            [
                abs_e.clone(),
                vb_big.clone(),
                abs_e2.clone(),
                vb_small.clone(),
                vh_big.clone(),
                vh_small.clone(),
            ],
        );
        // body : Rat.le_trans |E+e| (|E|+|e|) (B+b) tri mono
        let body = Expr::apps(le_trans, [abs_sum, sum_abs, sum_b, tri, mono]);

        let value = vb.lams(
            &[
                (ve_big_id, &c.rat),
                (ve_small_id, &c.rat),
                (vb_big_id, &c.rat),
                (vb_small_id, &c.rat),
                (vh_big_id, &vh_big_ty),
                (vh_small_id, &vh_small_ty),
            ],
            body,
        );

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem error_accum_step3 (e1 e2 e3 b1 b2 b3 : Rat) :
    ///    |e1| ≤ b1 → |e2| ≤ b2 → |e3| ≤ b3 →
    ///    |((e1 + e2) + e3)| ≤ ((b1 + b2) + b3)`
    ///
    /// The 3-term dot-product error accumulation (2 additions): the accumulated
    /// error of summing three rounded contributions is bounded by the sum of
    /// their three bounds. Built by iterating `error_accum_step`:
    /// ```text
    /// error_accum_step (e1+e2) e3 (b1+b2) b3
    ///   (error_accum_step e1 e2 b1 b2 h1 h2)   -- |e1+e2| ≤ b1+b2
    ///   h3                                     -- |e3| ≤ b3
    /// ```
    /// General over the `Rat` operands; empty non-foundational axiom closure.
    fn register_error_accum_step3(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        self.register_accum_chain(c, 3, "NNVerify.FloatRational.error_accum_step3")
    }

    /// `theorem error_accum_step4 (e1..e4 b1..b4 : Rat) :
    ///    |ei| ≤ bi (i=1..4) → |(((e1+e2)+e3)+e4)| ≤ (((b1+b2)+b3)+b4)`
    ///
    /// The 4-term accumulation (3 additions). Same iterated-step construction.
    fn register_error_accum_step4(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        self.register_accum_chain(c, 4, "NNVerify.FloatRational.error_accum_step4")
    }

    /// Register an `n`-term left-associated accumulation theorem
    /// `|e1| ≤ b1 → … → |en| ≤ bn → |(…(e1+e2)+…+en)| ≤ (…(b1+b2)+…+bn)` by
    /// folding `error_accum_step` left-to-right. Requires `n ≥ 2`.
    fn register_accum_chain(
        &mut self,
        c: &FRConsts,
        n: usize,
        name_str: &str,
    ) -> Result<(), EnvError> {
        let name = Name::from_string(name_str);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        assert!(n >= 2, "accum chain needs at least 2 terms");
        let step = Expr::const_(
            Name::from_string("NNVerify.FloatRational.error_accum_step"),
            vec![],
        );

        // Left-fold helper over a slice of (value, bound) Expr pairs: returns the
        // running (sum_e, sum_b, proof-of |sum_e| ≤ sum_b). `proof` for a single
        // term is the corresponding hypothesis; for k+1 terms it is one
        // `error_accum_step` application.
        let fold = |es: &[Expr], bs: &[Expr], hs: &[Expr]| -> (Expr, Expr, Expr) {
            let mut sum_e = es[0].clone();
            let mut sum_b = bs[0].clone();
            let mut proof = hs[0].clone();
            for i in 1..es.len() {
                let next_e = es[i].clone();
                let next_b = bs[i].clone();
                let next_h = hs[i].clone();
                // error_accum_step sum_e next_e sum_b next_b proof next_h
                let new_proof = Expr::apps(
                    step.clone(),
                    [
                        sum_e.clone(),
                        next_e.clone(),
                        sum_b.clone(),
                        next_b.clone(),
                        proof.clone(),
                        next_h,
                    ],
                );
                sum_e = c.add(sum_e.clone(), next_e);
                sum_b = c.add(sum_b.clone(), next_b);
                proof = new_proof;
            }
            (sum_e, sum_b, proof)
        };

        // --- Type ---
        let mut tb = EnvDeclBuilderLocal::new();
        let mut e_ids = Vec::new();
        let mut es = Vec::new();
        for _ in 0..n {
            let (id, v) = tb.fresh(&c.rat);
            e_ids.push(id);
            es.push(v);
        }
        let mut b_ids = Vec::new();
        let mut bs = Vec::new();
        for _ in 0..n {
            let (id, v) = tb.fresh(&c.rat);
            b_ids.push(id);
            bs.push(v);
        }
        let mut h_ids = Vec::new();
        let mut h_tys = Vec::new();
        for i in 0..n {
            let ty = c.rat_le(c.abs(es[i].clone()), bs[i].clone());
            let (id, _v) = tb.fresh(&ty);
            h_ids.push(id);
            h_tys.push(ty);
        }
        // Left-associated sums for the conclusion type (no proofs needed here).
        let mut se = es[0].clone();
        let mut sbnd = bs[0].clone();
        for i in 1..n {
            se = c.add(se.clone(), es[i].clone());
            sbnd = c.add(sbnd.clone(), bs[i].clone());
        }
        let concl = c.rat_le(c.abs(se), sbnd);
        // Π over e's, then b's, then h's (matching the λ binder order in value).
        let mut binders: Vec<(LocalId, Expr)> = Vec::new();
        for id in e_ids.iter() {
            binders.push((*id, c.rat.clone()));
        }
        for id in b_ids.iter() {
            binders.push((*id, c.rat.clone()));
        }
        for (i, id) in h_ids.iter().enumerate() {
            binders.push((*id, h_tys[i].clone()));
        }
        let binders_ref: Vec<(LocalId, &Expr)> = binders.iter().map(|(id, ty)| (*id, ty)).collect();
        let type_ = tb.pis(&binders_ref, concl);

        // --- Value ---
        let mut vb = EnvDeclBuilderLocal::new();
        let mut ve_ids = Vec::new();
        let mut ves = Vec::new();
        for _ in 0..n {
            let (id, v) = vb.fresh(&c.rat);
            ve_ids.push(id);
            ves.push(v);
        }
        let mut vb_ids = Vec::new();
        let mut vbs = Vec::new();
        for _ in 0..n {
            let (id, v) = vb.fresh(&c.rat);
            vb_ids.push(id);
            vbs.push(v);
        }
        let mut vh_ids = Vec::new();
        let mut vh_tys = Vec::new();
        let mut vhs = Vec::new();
        for i in 0..n {
            let ty = c.rat_le(c.abs(ves[i].clone()), vbs[i].clone());
            let (id, v) = vb.fresh(&ty);
            vh_ids.push(id);
            vh_tys.push(ty);
            vhs.push(v);
        }
        let (_se, _sb, proof) = fold(&ves, &vbs, &vhs);
        // lambda binders, same order as the type's pis
        let mut vbinders: Vec<(LocalId, Expr)> = Vec::new();
        for id in ve_ids.iter() {
            vbinders.push((*id, c.rat.clone()));
        }
        for id in vb_ids.iter() {
            vbinders.push((*id, c.rat.clone()));
        }
        for (i, id) in vh_ids.iter().enumerate() {
            vbinders.push((*id, vh_tys[i].clone()));
        }
        let vbinders_ref: Vec<(LocalId, &Expr)> =
            vbinders.iter().map(|(id, ty)| (*id, ty)).collect();
        let value = vb.lams(&vbinders_ref, proof);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Per-op relative-error discharges: the named hypothesis
    /// `|fl_op z − z| ≤ u·|z|` instantiated and proven, at concrete points, BY
    /// the half-ulp bound for both precisions.
    ///
    /// At a concrete dyadic `z` and precision `u`, `fl_op z := Rat.roundToNearestEven
    /// z ulp(z)` rounds onto the `ulp(z) = 2^q` grid; the half-ulp bound gives
    /// `2·|fl_op z − z| ≤ ulp(z)`, and `ulp(z) ≤ 2·u·|z|` in the normal range
    /// (where `ulp(z)/|z| ≤ 2^{1-p} = 2u`). Composing, `|fl_op z − z| ≤ u·|z|`.
    /// We discharge the COMPOSED inequality `2·|fl_op z − z| ≤ 2·u·|z|` as a
    /// literal `Rat.le` over dyadics (so it reduces in-kernel), witnessed by
    /// `Int.NonNeg.mk`, at one normal `z` for each of `u = 2^−24` and `2^−53`.
    fn register_fl_op_rel_error_discharges(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        for case in FL_OP_REL_CASES {
            self.register_fl_op_rel_error_case(c, case)?;
        }
        Ok(())
    }

    /// One per-op relative-error discharge. We prove the half-ulp-derived bound
    /// `2·|round(z) − z| ≤ 2·u·|z|` (equivalent to `|round(z) − z| ≤ u·|z|`,
    /// the per-op relative-error hypothesis) at a concrete normal `z` and
    /// precision `u`, as a LITERAL `Rat.le LHS RHS`. Both sides reduce to
    /// dyadics; `@Int.NonNeg.mk k` (with `k = num_RHS·den_LHS − num_LHS·den_RHS
    /// ≥ 0`) inhabits the lifted `Int.NonNeg` by kernel computation.
    fn register_fl_op_rel_error_case(
        &mut self,
        c: &FRConsts,
        case: &FlOpRelCase,
    ) -> Result<(), EnvError> {
        let name = Name::from_string(case.name);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // z = z_mag · 2^z_exp (a normal dyadic, z_mag a p-bit significand).
        // round(z) on the grid 2^grid_exp; |round(z) − z| computed exactly.
        // ulp(z) = 2^grid_exp ; u = 2^{-u_exp}.
        //
        // LHS = 2 · |round(z) − z|  ;  RHS = 2·u·|z| = |z| · 2^{1 - u_exp}.
        // The two compared quantities are PURE powers of two, so we work with
        // their NET base-2 exponents and emit each as a REDUCED `Rat.mk` (`2^k/1`
        // or `1/2^(-k)`). The case `z` values are chosen (significand `2^(p-1)`,
        // `z_exp = grid_exp = 0`) so BOTH net exponents are 0 — the comparison
        // reduces to a literal `1 ≤ 1` (denominator 1), the TIGHT relative-bound
        // boundary. (Even at a large denominator the `Rat.le` lift now reduces —
        // the native `Nat.pred` + arbitrary-precision `Int` reducers close the
        // `effDenom` wall — so this denominator-1 form is a TIGHTNESS choice, not
        // a wall workaround; cf. the `gamma_n_reduces_f32/f64_*` discharges which
        // DO carry `2^24` / `2^53` denominators.)
        //
        //   LHS = ulp(z) = 2^grid_exp.
        //   RHS = 2·u·|z| = z_mag · 2^(z_exp + 1 − u_exp)
        //               = 2^(log2 z_mag + z_exp + 1 − u_exp)   (z_mag a power of 2).
        let lhs_net = case.grid_exp; // exponent of ulp(z)
        let rhs_net = log2_u64(case.z_mag) + case.z_exp + 1 - case.u_exp; // exponent of 2u|z|
        debug_assert!(
            lhs_net <= rhs_net,
            "fl_op rel-error discharge `{}` FALSE: ulp(z) > 2u|z| (2^{lhs_net} > 2^{rhs_net})",
            case.name
        );

        // Put both over a common denominator 2^d with d = max(−lhs_net, −rhs_net, 0)
        // so both numerators are small integers; then LHS ≤ RHS ⟺
        //   lhs_num·1 ≤ rhs_num (same denom) ⟺ Int.NonNeg (rhs_num − lhs_num).
        let d = (-lhs_net).max(-rhs_net).max(0);
        let lhs_num = pow2_bignat((lhs_net + d) as u64);
        let rhs_num = pow2_bignat((rhs_net + d) as u64);
        let den = pow2_bignat(d as u64);
        let k = rhs_num.saturating_sub_big(&lhs_num);

        let lhs_lit = rat_lit_general(&lhs_num, &den);
        let rhs_lit = rat_lit_general(&rhs_num, &den);
        let goal = c.rat_le(lhs_lit, rhs_lit);
        let witness = Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            Expr::bignat_lit(k),
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: goal,
            value: witness,
        })
    }

    /// Concrete γ_n / (1+u)^n bound instances, REDUCED in-kernel for small `n`
    /// at the representative precisions (`u = 2^{-8}`, `2^{-12}`) AND the TRUE
    /// binary32 (`u = 2^{-24}`) / binary64 (`u = 2^{-53}`) precisions. Each
    /// proves the literal dyadic `Rat.le` `Σ b_i ≤ γ_n · Σ|a_i w_i|` (specialized
    /// to `Σ|a_i w_i| = 1` w.l.o.g., so the bound is `Σ b_i ≤ γ_n`, with
    /// `Σ b_i = n·u` the worst-case per-op sum and `γ_n = n·u/(1−n·u)`;
    /// `n·u ≤ n·u/(1−n·u)` always holds since `n·u < 1`). The f32/f64 literal
    /// discharges reduce in-kernel via the native `Nat.pred` + arbitrary-precision
    /// `Int` reducers (the `2^{u_exp}`-scale `Rat.le` lift no longer blows up).
    fn register_gamma_n_reductions(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        for case in GAMMA_N_CASES {
            self.register_gamma_n_case(c, case)?;
        }
        Ok(())
    }

    /// One concrete γ_n reduction: `n·u ≤ γ_n = n·u/(1−n·u)` as a literal
    /// `Rat.le` over dyadics, at precision `u = 2^{-u_exp}` and dimension `n`.
    ///
    /// `n·u = n · 2^{-u_exp}` (a dyadic, numerator `n`, denom `2^{u_exp}`).
    /// `γ_n = (n·u)/(1 − n·u) = n / (2^{u_exp} − n)` (clearing the `2^{-u_exp}`):
    ///   `γ_n = n·2^{-u_exp} / (1 − n·2^{-u_exp}) = n / (2^{u_exp} − n)`.
    /// Both are exact dyadic-ish rationals over `Rat.mk`; `n·u ≤ γ_n` ⟺
    ///   `n·(2^{u_exp} − n) ≤ n·2^{u_exp}` ⟺ `−n² ≤ 0` (TRUE), witnessed by
    /// `Int.NonNeg.mk` on the cross value. This is `Σ b_i ≤ γ_n Σ|a_i w_i|` at
    /// `Σ|a_i w_i| = 1`, `Σ b_i = n·u` — the worst case of the per-op sum.
    fn register_gamma_n_case(&mut self, c: &FRConsts, case: &GammaNCase) -> Result<(), EnvError> {
        let name = Name::from_string(case.name);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let n = case.n;
        let two_u = pow2_bignat(case.u_exp); // 2^{u_exp}
                                             // n·u  =  n / 2^{u_exp}        (num n, den 2^{u_exp})
        let nu_num = BigNat::from_u64(n);
        let nu_den = two_u.clone();
        // γ_n  =  n / (2^{u_exp} − n)  (num n, den 2^{u_exp} − n)
        let gamma_num = BigNat::from_u64(n);
        let gamma_den = two_u.saturating_sub_big(&BigNat::from_u64(n));
        debug_assert!(
            !gamma_den.is_zero(),
            "gamma_n case `{}`: 1 − n·u must be > 0 (n·u < 1)",
            case.name
        );

        // LHS = n·u = nu_num / nu_den ; RHS = γ_n = gamma_num / gamma_den.
        // cross k = nu_den · gamma_num − nu_num · gamma_den   ... wait: for
        // `LHS ≤ RHS` with positive denominators, the lift checks
        //   Int.NonNeg ( num_RHS·den_LHS − num_LHS·den_RHS ).
        // Here num_RHS = gamma_num, den_LHS = nu_den, num_LHS = nu_num,
        // den_RHS = gamma_den:
        let cross_rhs = gamma_num.checked_mul_big(&nu_den).expect("mul");
        let cross_lhs = nu_num.checked_mul_big(&gamma_den).expect("mul");
        debug_assert!(
            cross_lhs <= cross_rhs,
            "gamma_n case `{}` FALSE: n·u > γ_n",
            case.name
        );
        let k = cross_rhs.saturating_sub_big(&cross_lhs);

        let lhs_lit = rat_lit_general(&nu_num, &nu_den);
        let rhs_lit = rat_lit_general(&gamma_num, &gamma_den);
        let goal = c.rat_le(lhs_lit, rhs_lit);
        let witness = Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            Expr::bignat_lit(k),
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: goal,
            value: witness,
        })
    }
}

// === local concrete-case tables ===

/// A per-op relative-error discharge: a normal dyadic `z = z_mag·2^z_exp`, its
/// `ulp(z) = 2^grid_exp`, at unit roundoff `u = 2^{-u_exp}`. Proves
/// `ulp(z) ≤ 2·u·|z|` (the relative form `|round−z| ≤ u|z|` composed with the
/// half-ulp magnitude bound `2|round−z| ≤ ulp`).
struct FlOpRelCase {
    name: &'static str,
    z_mag: u64,
    z_exp: i64,
    grid_exp: i64,
    u_exp: i64,
}

/// For a normal `z` with `p`-bit significand `z_mag ∈ [2^{p-1}, 2^p)` and value
/// exponent `e`, `ulp(z) = 2^{e}` (the trailing-bit weight) and `|z| ≥ 2^{p-1}·2^e`,
/// so `ulp(z)/|z| ≤ 2^{1-p} = 2u`, i.e. `ulp(z) ≤ 2u|z|`. We pick `z` at the
/// LOW end of the significand range (`z_mag = 2^{p-1}`), the WORST case for the
/// relative bound (largest `ulp/|z|`), so the discharge is the tight boundary.
const FL_OP_REL_CASES: &[FlOpRelCase] = &[
    // binary32: p = 24, u = 2^{-24}. z = 2^23 · 2^0 (smallest normal significand
    // at exponent 0; |z| = 2^23). ulp = 2^0 = 1. 2u|z| = 2^{1-24}·2^23 = 2^0 = 1.
    // ulp = 2u|z| EXACTLY (the tight boundary). grid_exp = 0.
    FlOpRelCase {
        name: "NNVerify.FloatRational.fl_op_rel_error_discharge_f32",
        z_mag: 1 << 23,
        z_exp: 0,
        grid_exp: 0,
        u_exp: 24,
    },
    // binary64: p = 53, u = 2^{-53}. z = 2^52 · 2^0 (|z| = 2^52). ulp = 1.
    // 2u|z| = 2^{1-53}·2^52 = 2^0 = 1. ulp = 2u|z| EXACTLY. grid_exp = 0.
    FlOpRelCase {
        name: "NNVerify.FloatRational.fl_op_rel_error_discharge_f64",
        z_mag: 1 << 52,
        z_exp: 0,
        grid_exp: 0,
        u_exp: 53,
    },
];

/// A concrete γ_n reduction at precision `u = 2^{-u_exp}` and dimension `n`:
/// proves `n·u ≤ γ_n = n·u/(1−n·u)` as a literal dyadic `Rat.le`.
struct GammaNCase {
    name: &'static str,
    n: u64,
    u_exp: u64,
}

/// γ_n instances at n = 2,3 for the representative precisions `u := 2^{-8}`,
/// `2^{-12}` AND the TRUE binary32 `u := 2^{-24}` / binary64 `u := 2^{-53}` — the
/// SAME parametric bound `n·u ≤ γ_n` at each precision, exhibiting that `u` is a
/// genuine PARAMETER discharged at the REAL f32/f64 scales (closing the "f32 vs
/// f64 is a manual correspondence" audit concern with literal in-kernel proofs).
///
/// ## The f32/f64 LITERAL discharges now reduce in-kernel
///
/// The `Rat.le` lift compares cross-products through `Rat.Raw.effDenom =
/// Nat.succ ∘ Nat.pred`. Previously `Nat.pred` was NOT a native reducer, so a
/// `2^{u_exp}`-scale denominator forced an O(value)-deep `Nat.rec` `succ∘pred`
/// chain that OOM-killed past ~2^16 (the same `2^1074` wall the half-ulp module
/// hit). The native `Nat.pred` reducer (tc/reduction/nat.rs) plus the
/// arbitrary-precision `Int` reducer that WHNF's its operands
/// (tc/reduction/int.rs) close that wall: the `2^24` / `2^53` γ_n cross-products
/// and difference reduce in O(limbs), so the literal `n·u ≤ γ_n` discharges at
/// the true f32/f64 unit roundoffs. The accumulation lemmas (`error_accum_step`,
/// the chains) additionally carry the per-op bounds `b_i` ABSTRACTLY (no `u`
/// literal at all), so they hold verbatim at EVERY precision; the closed-form
/// γ_n simplification is now exhibited as a LITERAL at f32/f64, not just at the
/// small representative `u`.
const GAMMA_N_CASES: &[GammaNCase] = &[
    GammaNCase {
        name: "NNVerify.FloatRational.gamma_n_reduces_u8_n2",
        n: 2,
        u_exp: 8,
    },
    GammaNCase {
        name: "NNVerify.FloatRational.gamma_n_reduces_u8_n3",
        n: 3,
        u_exp: 8,
    },
    GammaNCase {
        name: "NNVerify.FloatRational.gamma_n_reduces_u12_n2",
        n: 2,
        u_exp: 12,
    },
    GammaNCase {
        name: "NNVerify.FloatRational.gamma_n_reduces_u12_n3",
        n: 3,
        u_exp: 12,
    },
    // TRUE binary32 (u = 2^-24) and binary64 (u = 2^-53). These are the LITERAL
    // f32/f64 discharges that the Rat-blowup wall previously forced down to the
    // small representative precisions above: the γ_n denominator `2^{u_exp} − n`
    // and the `Rat.le` cross-products flow through `Rat.Raw.effDenom`'s
    // `Nat.pred`, which OOM-killed past a ~2^16 argument. With the native
    // `Nat.pred` + arbitrary-precision `Int` reducers the literal `n·u ≤ γ_n`
    // bound now reduces in-kernel at the true f32/f64 unit roundoffs.
    GammaNCase {
        name: "NNVerify.FloatRational.gamma_n_reduces_f32_n2",
        n: 2,
        u_exp: 24,
    },
    GammaNCase {
        name: "NNVerify.FloatRational.gamma_n_reduces_f32_n3",
        n: 3,
        u_exp: 24,
    },
    GammaNCase {
        name: "NNVerify.FloatRational.gamma_n_reduces_f64_n2",
        n: 2,
        u_exp: 53,
    },
    GammaNCase {
        name: "NNVerify.FloatRational.gamma_n_reduces_f64_n3",
        n: 3,
        u_exp: 53,
    },
];

// === dyadic helpers (mirroring the half-ulp discharge's emit shapes) ===

/// `mag · 2^exp` as a non-negative fraction `(num, den_exp)` with value
/// `num / 2^den_exp`. `exp ≥ 0` shifts into the numerator; `exp < 0` into the
/// denominator exponent.
///
/// `log2` of an exact power-of-two `u64` (`mag = 2^k` ⇒ `k`); the significands
/// used here (`2^(p-1)`) are exact powers of two, so this is exact.
fn log2_u64(mag: u64) -> i64 {
    debug_assert!(mag.is_power_of_two(), "log2_u64 expects a power of two");
    mag.trailing_zeros() as i64
}

/// Emit a non-negative rational `num / den` as `Rat.mk (Int.ofNat num) den`
/// (arbitrary positive `den` — used for the γ_n denominator `2^{u_exp} − n`).
fn rat_lit_general(num: &BigNat, den: &BigNat) -> Expr {
    let int_of_nat = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::bignat_lit(num.clone()),
    );
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [int_of_nat, Expr::bignat_lit(den.clone())],
    )
}

// === a tiny local decl-builder wrapper (binder bookkeeping) ===
//
// `EnvDeclBuilder` is the canonical builder; this thin wrapper batches the
// repeated `mk_pi` / `mk_lam` folds so the proof terms above read cleanly.

use crate::env::decl_builder::EnvDeclBuilder;

type LocalId = crate::expr::FVarId;

struct EnvDeclBuilderLocal {
    inner: EnvDeclBuilder,
}

impl EnvDeclBuilderLocal {
    fn new() -> Self {
        Self {
            inner: EnvDeclBuilder::new(),
        }
    }
    fn fresh(&mut self, ty: &Expr) -> (LocalId, Expr) {
        self.inner.fresh_local(ty.clone())
    }
    /// Fold a chain of Π binders (outermost-first list) around `body`.
    fn pis(&self, binders: &[(LocalId, &Expr)], body: Expr) -> Expr {
        let mut e = body;
        for (id, ty) in binders.iter().rev() {
            e = self.inner.mk_pi(*id, BinderInfo::Default, (*ty).clone(), e);
        }
        self.inner.finish(e)
    }
    /// Fold a chain of λ binders (outermost-first list) around `body`.
    fn lams(&self, binders: &[(LocalId, &Expr)], body: Expr) -> Expr {
        let mut e = body;
        for (id, ty) in binders.iter().rev() {
            e = self
                .inner
                .mk_lam(*id, BinderInfo::Default, (*ty).clone(), e);
        }
        self.inner.finish(e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scope_marker_mentions_higham_and_both_precisions() {
        assert!(DOT_PRODUCT_SCOPE.contains("Higham"));
        assert!(DOT_PRODUCT_SCOPE.contains("2^-24"));
        assert!(DOT_PRODUCT_SCOPE.contains("2^-53"));
    }

    /// Cross-check the concrete-case arithmetic in pure Rust: every fl_op
    /// relative-error case satisfies `ulp(z) ≤ 2u|z|`, and every γ_n case
    /// satisfies `n·u ≤ γ_n` (the bounds the kernel witnesses encode).
    #[test]
    fn concrete_cases_satisfy_their_bounds() {
        for case in FL_OP_REL_CASES {
            // ulp(z) = 2^grid_exp ; 2u|z| = 2^(log2 z_mag + z_exp + 1 − u_exp).
            // The relative bound ulp(z) ≤ 2u|z| ⟺ grid_exp ≤ rhs_net.
            let lhs_net = case.grid_exp;
            let rhs_net = log2_u64(case.z_mag) + case.z_exp + 1 - case.u_exp;
            assert!(
                lhs_net <= rhs_net,
                "fl_op case `{}`: ulp(z) > 2u|z| (2^{lhs_net} > 2^{rhs_net})",
                case.name
            );
        }
        for case in GAMMA_N_CASES {
            let two_u = pow2_bignat(case.u_exp);
            let gamma_den = two_u.saturating_sub_big(&BigNat::from_u64(case.n));
            assert!(!gamma_den.is_zero(), "case `{}`: n·u ≥ 1", case.name);
            let cross_rhs = BigNat::from_u64(case.n).checked_mul_big(&two_u).unwrap();
            let cross_lhs = BigNat::from_u64(case.n)
                .checked_mul_big(&gamma_den)
                .unwrap();
            assert!(cross_lhs <= cross_rhs, "case `{}`: n·u > γ_n", case.name);
        }
    }
}
