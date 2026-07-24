// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C008 unlock (R-weak): the `propagate_eq` / non-negativity helpers and the
//! constructive `NNVerify.ibp_tightness_step` proof term.
//!
//! Builds on the two zero-width preservation Theorems in
//! `nn_verify_ibp_tightness_step_proof` (`relu_bounds_preserves_eq`,
//! `linear_bounds_preserves_eq`). See that module's header for the R-weak
//! honesty caveat (the registered `eps_ball` is a zero-width placeholder).
//!
//! Helpers registered here (all sorry-free `Declaration::Theorem`s):
//!   - `NNVerify.infinity_norm_nonneg`: `0 ≤ infinity_norm m n W` (`Nat.rec` on
//!     `m`; base `0 ≤ Rat.zero`, succ `0 ≤ max(prefix, rowsum)` via
//!     `Rat.le_max_left` + `Rat.le_trans` from the IH);
//!   - `NNVerify.norm_product_nonneg`: `(∀ i, 0 ≤ f i) → 0 ≤ norm_product k f`
//!     (`Nat.rec` on `k`; base `0 ≤ Rat.one`, succ `0 ≤ last · prefix` via
//!     `Rat.mul_nonneg`);
//!   - `NNVerify.ibp_propagate_eq`: the eps-ball propagated through `k` layers
//!     stays zero-width — `∀ i, (ibp_propagate k …).lower i = (…).upper i`
//!     (`Nat.rec` on `k`; base = the zero-width eps-ball, succ = one
//!     `linear_bounds_preserves_eq` then one `relu_bounds_preserves_eq`).
//!
//! The step proof feeds `ibp_propagate_eq (k+1) …` to `NNVerify.ibp_width_zero`
//! (LHS collapses to `Rat.zero`) and closes the RHS `0 ≤ 2·eps·norm_product
//! (k+1) norms` with `Rat.mul_nonneg` (`0 ≤ 2·eps` from the base-case helpers,
//! `0 ≤ norm_product …` from `norm_product_nonneg` fed `infinity_norm_nonneg`
//! per layer), combined by `NNVerify.le_of_eq_of_le`.

use super::nn_verify_ibp_tightness::IbpTightnessConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `IntervalBounds.lower bnd i` (projection 0 applied at `i`).
fn lower_at(bnd: &Expr, i: &Expr) -> Expr {
    Expr::app(
        Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bnd.clone()),
        i.clone(),
    )
}

/// `IntervalBounds.upper bnd i` (projection 1 applied at `i`).
fn upper_at(bnd: &Expr, i: &Expr) -> Expr {
    Expr::app(
        Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bnd.clone()),
        i.clone(),
    )
}

/// `Eq.{1} Rat a b`.
fn rat_eq(c: &IbpTightnessConsts, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c.base.rat.clone(), a, b],
    )
}

/// `Nat.rec.{0}` — Prop-valued recursor.
fn nat_rec_prop() -> Expr {
    Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()])
}

impl Environment {
    /// Register the `propagate_eq` / non-negativity helpers. Idempotent.
    pub(super) fn register_ibp_tightness_step_value_support(
        &mut self,
        c: &IbpTightnessConsts,
    ) -> Result<(), EnvError> {
        self.register_infinity_norm_nonneg(c)?;
        self.register_norm_product_nonneg(c)?;
        self.register_ibp_propagate_eq(c)
    }

    /// `NNVerify.infinity_norm_nonneg : ∀ (m n : Nat) (W : NNMat m n),
    ///    LE.le Rat.zero (NNVerify.infinity_norm m n W)`.
    fn register_infinity_norm_nonneg(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.infinity_norm_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = c.base.rat_zero.clone();
        let le_max_left = Expr::const_(Name::from_string("Rat.le_max_left"), vec![]);
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
        let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);

        // concl at a given m: 0 ≤ infinity_norm m n W.
        let concl = |m: &Expr, n: &Expr, w: &Expr| -> Expr {
            c.base.rat_le(
                zero.clone(),
                c.infinity_norm_app(m.clone(), n.clone(), w.clone()),
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.base.nat.clone());
            let (n_id, n) = b.fresh_local(c.base.nat.clone());
            let mat_mn = c.base.mat_of(m.clone(), n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, concl(&m, &n, &w));
            let e = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };

        // Value: fun m n => Nat.rec (motive := fun m => ∀ W, 0 ≤ infinity_norm m n W)
        //                            base succ m, then apply to W.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.base.nat.clone());
            let (n_id, n) = b.fresh_local(c.base.nat.clone());

            // motive : Nat → Prop = fun mm => ∀ (W : NNMat mm n), 0 ≤ infinity_norm mm n W.
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (mm_id, mm) = ch.fresh_local(c.base.nat.clone());
                let mat = c.base.mat_of(mm.clone(), n.clone());
                let (w_id, w) = ch.fresh_local(mat.clone());
                let body = ch.mk_pi(w_id, BinderInfo::Default, mat, concl(&mm, &n, &w));
                ch.finish_child(ch.mk_lam(mm_id, BinderInfo::Default, c.base.nat.clone(), body))
            };

            // base : ∀ (W : NNMat 0 n), 0 ≤ infinity_norm 0 n W.
            //   infinity_norm 0 n W ι-reduces to Rat.zero, so Rat.le_refl Rat.zero.
            let base = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let mat0 = c.base.mat_of(c.nat_zero.clone(), n.clone());
                let (w_id, _w) = ch.fresh_local(mat0.clone());
                let proof = Expr::app(le_refl.clone(), zero.clone());
                ch.finish_child(ch.mk_lam(w_id, BinderInfo::Default, mat0, proof))
            };

            // succ : ∀ (mm : Nat), motive mm → motive (mm+1).
            let succ = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (mm_id, mm) = ch.fresh_local(c.base.nat.clone());
                let mat = c.base.mat_of(mm.clone(), n.clone());
                let ih_ty = {
                    let mut ci = EnvDeclBuilder::child_of(&ch);
                    let (w_id, w) = ci.fresh_local(mat.clone());
                    ci.finish_child(ci.mk_pi(
                        w_id,
                        BinderInfo::Default,
                        mat.clone(),
                        concl(&mm, &n, &w),
                    ))
                };
                let (ih_id, ih) = ch.fresh_local(ih_ty.clone());
                let mm_succ = Expr::app(c.nat_succ.clone(), mm.clone());
                let mat_succ = c.base.mat_of(mm_succ.clone(), n.clone());
                let inner = {
                    let mut ci = EnvDeclBuilder::child_of(&ch);
                    let (ws_id, ws) = ci.fresh_local(mat_succ.clone());
                    // infinity_norm (mm+1) n ws ι-reduces to max(prefix_norm, row_sum),
                    // where prefix_norm = infinity_norm mm n (prefix ws). Build the
                    // prefix matrix to apply the IH; both `prefix_norm` and `row_sum`
                    // appear in the reduced `Rat.max` so we must name them exactly.
                    let fin_mm = Expr::app(c.base.fin.clone(), mm.clone());
                    let fin_n = Expr::app(c.base.fin.clone(), n.clone());
                    // prefix ws := fun (i : Fin mm) (j : Fin n) => ws (castSucc i) j.
                    let prefix_ws = {
                        let mut c2 = EnvDeclBuilder::child_of(&ci);
                        let (i_id, i) = c2.fresh_local(fin_mm.clone());
                        let row = {
                            let mut c3 = EnvDeclBuilder::child_of(&c2);
                            let (j_id, j) = c3.fresh_local(fin_n.clone());
                            let cast_i = Expr::app(
                                Expr::app(c.fin_cast_succ.clone(), mm.clone()),
                                i.clone(),
                            );
                            let body = Expr::app(Expr::app(ws.clone(), cast_i), j);
                            c3.finish_child(c3.mk_lam(
                                j_id,
                                BinderInfo::Default,
                                fin_n.clone(),
                                body,
                            ))
                        };
                        c2.finish_child(c2.mk_lam(i_id, BinderInfo::Default, fin_mm.clone(), row))
                    };
                    // h_prefix : 0 ≤ infinity_norm mm n (prefix ws)  via ih (prefix ws).
                    let h_prefix = Expr::app(ih.clone(), prefix_ws.clone());
                    let prefix_norm = c.infinity_norm_app(mm.clone(), n.clone(), prefix_ws);
                    // row_sum := Fin.sum n (fun j => Rat.abs (ws (Fin.last mm) j)).
                    let row_sum = {
                        let last_i = Expr::app(c.fin_last.clone(), mm.clone());
                        let f = {
                            let mut c3 = EnvDeclBuilder::child_of(&ci);
                            let (j_id, j) = c3.fresh_local(fin_n.clone());
                            let w_last_j = Expr::app(Expr::app(ws.clone(), last_i.clone()), j);
                            let body = Expr::app(c.rat_abs.clone(), w_last_j);
                            c3.finish_child(c3.mk_lam(
                                j_id,
                                BinderInfo::Default,
                                fin_n.clone(),
                                body,
                            ))
                        };
                        c.base.sum(n.clone(), f)
                    };
                    // le_max_left prefix_norm row_sum : prefix_norm ≤ max prefix_norm row_sum.
                    let h_le_max =
                        Expr::apps(le_max_left.clone(), [prefix_norm.clone(), row_sum.clone()]);
                    let max_pr = Expr::apps(c.rat_max.clone(), [prefix_norm.clone(), row_sum]);
                    // le_trans 0 prefix_norm max h_prefix h_le_max : 0 ≤ max(...).
                    let proof = Expr::apps(
                        le_trans.clone(),
                        [zero.clone(), prefix_norm, max_pr, h_prefix, h_le_max],
                    );
                    ci.finish_child(ci.mk_lam(ws_id, BinderInfo::Default, mat_succ, proof))
                };
                let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_ty, inner);
                ch.finish_child(ch.mk_lam(mm_id, BinderInfo::Default, c.base.nat.clone(), r))
            };

            let rec = Expr::apps(nat_rec_prop(), [motive, base, succ, m.clone()]);
            // Nat.rec ... m : motive m = ∀ W, 0 ≤ infinity_norm m n W. Eta to (fun W => rec W).
            let e = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), rec);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.norm_product_nonneg : ∀ (k : Nat) (f : Fin k → Rat),
    ///    (∀ i, 0 ≤ f i) → 0 ≤ NNVerify.norm_product k f`.
    fn register_norm_product_nonneg(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.norm_product_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = c.base.rat_zero.clone();
        let zero_le_one = Expr::const_(Name::from_string("NNVerify.rat_zero_le_one"), vec![]);
        let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);

        let f_ty = |k: &Expr| {
            Expr::pi(
                BinderInfo::Default,
                Expr::app(c.base.fin.clone(), k.clone()),
                c.base.rat.clone(),
            )
        };
        // hyp : ∀ (i : Fin k), 0 ≤ f i.
        let hyp_ty = |outer: &EnvDeclBuilder, k: &Expr, f: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(outer);
            let fin_k = Expr::app(c.base.fin.clone(), k.clone());
            let (i_id, i) = ch.fresh_local(fin_k.clone());
            let body = c.base.rat_le(zero.clone(), Expr::app(f.clone(), i));
            ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, fin_k, body))
        };
        let concl = |k: &Expr, f: &Expr| -> Expr {
            c.base
                .rat_le(zero.clone(), c.norm_product_app(k.clone(), f.clone()))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.base.nat.clone());
            let ft = f_ty(&k);
            let (f_id, f) = b.fresh_local(ft.clone());
            let hyp = hyp_ty(&b, &k, &f);
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl(&k, &f));
            let e = b.mk_pi(f_id, BinderInfo::Default, ft, e);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.base.nat.clone());

            // motive : Nat → Prop = fun kk => ∀ (f : Fin kk → Rat), (∀ i, 0 ≤ f i) → 0 ≤ norm_product kk f.
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (kk_id, kk) = ch.fresh_local(c.base.nat.clone());
                let ft = f_ty(&kk);
                let (f_id, f) = ch.fresh_local(ft.clone());
                let hyp = hyp_ty(&ch, &kk, &f);
                let (h_id, _h) = ch.fresh_local(hyp.clone());
                let body = ch.mk_pi(h_id, BinderInfo::Default, hyp, concl(&kk, &f));
                let body = ch.mk_pi(f_id, BinderInfo::Default, ft, body);
                ch.finish_child(ch.mk_lam(kk_id, BinderInfo::Default, c.base.nat.clone(), body))
            };

            // base : ∀ (f : Fin 0 → Rat), (∀ i, 0 ≤ f i) → 0 ≤ norm_product 0 f.
            //   norm_product 0 f ι-reduces to Rat.one, so rat_zero_le_one.
            let base = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let ft = f_ty(&c.nat_zero.clone());
                let (f_id, f) = ch.fresh_local(ft.clone());
                let hyp = hyp_ty(&ch, &c.nat_zero.clone(), &f);
                let (h_id, _h) = ch.fresh_local(hyp.clone());
                let body = ch.mk_lam(h_id, BinderInfo::Default, hyp, zero_le_one.clone());
                ch.finish_child(ch.mk_lam(f_id, BinderInfo::Default, ft, body))
            };

            // succ : ∀ (kk : Nat), motive kk → motive (kk+1).
            let succ = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (kk_id, kk) = ch.fresh_local(c.base.nat.clone());
                // ih_ty : motive kk.
                let ih_ty = {
                    let mut ci = EnvDeclBuilder::child_of(&ch);
                    let ft = f_ty(&kk);
                    let (f_id, f) = ci.fresh_local(ft.clone());
                    let hyp = hyp_ty(&ci, &kk, &f);
                    let (h_id, _h) = ci.fresh_local(hyp.clone());
                    let body = ci.mk_pi(h_id, BinderInfo::Default, hyp, concl(&kk, &f));
                    ci.finish_child(ci.mk_pi(f_id, BinderInfo::Default, ft, body))
                };
                let (ih_id, ih) = ch.fresh_local(ih_ty.clone());
                let kk_succ = Expr::app(c.nat_succ.clone(), kk.clone());
                let ft_succ = f_ty(&kk_succ);
                let inner = {
                    let mut ci = EnvDeclBuilder::child_of(&ch);
                    let (f_id, f) = ci.fresh_local(ft_succ.clone());
                    let hyp = hyp_ty(&ci, &kk_succ, &f);
                    let (h_id, h) = ci.fresh_local(hyp.clone());
                    let fin_kk = Expr::app(c.base.fin.clone(), kk.clone());

                    // last_norm := f (Fin.last kk) ; prefix_f := fun i => f (castSucc i).
                    let last_i = Expr::app(c.fin_last.clone(), kk.clone());
                    let last_norm = Expr::app(f.clone(), last_i.clone());
                    let prefix_f = {
                        let mut c2 = EnvDeclBuilder::child_of(&ci);
                        let (i_id, i) = c2.fresh_local(fin_kk.clone());
                        let cast_i =
                            Expr::app(Expr::app(c.fin_cast_succ.clone(), kk.clone()), i.clone());
                        let body = Expr::app(f.clone(), cast_i);
                        c2.finish_child(c2.mk_lam(i_id, BinderInfo::Default, fin_kk.clone(), body))
                    };
                    // h_last : 0 ≤ last_norm  via h (Fin.last kk).
                    let h_last = Expr::app(h.clone(), last_i);
                    // h_prefix_hyp : ∀ (i : Fin kk), 0 ≤ prefix_f i  via fun i => h (castSucc i).
                    let h_prefix_hyp = {
                        let mut c2 = EnvDeclBuilder::child_of(&ci);
                        let (i_id, i) = c2.fresh_local(fin_kk.clone());
                        let cast_i =
                            Expr::app(Expr::app(c.fin_cast_succ.clone(), kk.clone()), i.clone());
                        let body = Expr::app(h.clone(), cast_i);
                        c2.finish_child(c2.mk_lam(i_id, BinderInfo::Default, fin_kk.clone(), body))
                    };
                    // h_prefix : 0 ≤ norm_product kk prefix_f  via ih prefix_f h_prefix_hyp.
                    let h_prefix = Expr::apps(ih.clone(), [prefix_f.clone(), h_prefix_hyp]);
                    let prefix_prod = c.norm_product_app(kk.clone(), prefix_f);
                    // norm_product (kk+1) f ι-reduces to last_norm · prefix_prod.
                    // proof : 0 ≤ last_norm · prefix_prod  via Rat.mul_nonneg.
                    let proof = Expr::apps(
                        mul_nonneg.clone(),
                        [last_norm, prefix_prod, h_last, h_prefix],
                    );
                    let body = ci.mk_lam(h_id, BinderInfo::Default, hyp, proof);
                    ci.finish_child(ci.mk_lam(f_id, BinderInfo::Default, ft_succ, body))
                };
                let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_ty, inner);
                ch.finish_child(ch.mk_lam(kk_id, BinderInfo::Default, c.base.nat.clone(), r))
            };

            let rec = Expr::apps(nat_rec_prop(), [motive, base, succ, k.clone()]);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), rec);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.ibp_propagate_eq : ∀ (k : Nat) (output_dim : Nat → Nat)
    ///   (weight …) (bias …) (center : NNVec (output_dim 0)) (eps : Rat),
    ///   ∀ (i : Fin (output_dim k)),
    ///     (ibp_propagate k output_dim weight bias (eps_ball (output_dim 0) center eps)).lower i
    ///       = (…).upper i`.
    ///
    /// `Nat.rec` on `k`: base = the zero-width eps-ball (`Eq.refl Rat.zero`),
    /// succ = `relu_bounds_preserves_eq` ∘ `linear_bounds_preserves_eq` applied
    /// to the IH.
    fn register_ibp_propagate_eq(&mut self, c: &IbpTightnessConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.ibp_propagate_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let relu_pres = Expr::const_(
            Name::from_string("NNVerify.relu_bounds_preserves_eq"),
            vec![],
        );
        let linear_pres = Expr::const_(
            Name::from_string("NNVerify.linear_bounds_preserves_eq"),
            vec![],
        );
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );

        // Build the propagated bounds at index expr `kk`:
        //   ibp_propagate kk output_dim weight bias (eps_ball (output_dim 0) center eps).
        let propagated = |kk: &Expr,
                          output_dim: &Expr,
                          weight: &Expr,
                          bias: &Expr,
                          center: &Expr,
                          eps: &Expr|
         -> Expr {
            let eb = c.eps_ball_app(
                c.out_dim(output_dim, c.nat_zero.clone()),
                center.clone(),
                eps.clone(),
            );
            c.ibp_propagate_app(
                kk.clone(),
                output_dim.clone(),
                weight.clone(),
                bias.clone(),
                eb,
            )
        };
        // concl at kk: ∀ (i : Fin (out_dim kk)), prop.lower i = prop.upper i.
        let concl = |outer: &EnvDeclBuilder,
                     kk: &Expr,
                     output_dim: &Expr,
                     weight: &Expr,
                     bias: &Expr,
                     center: &Expr,
                     eps: &Expr|
         -> Expr {
            let mut ch = EnvDeclBuilder::child_of(outer);
            let fin_d = Expr::app(c.base.fin.clone(), c.out_dim(output_dim, kk.clone()));
            let (i_id, i) = ch.fresh_local(fin_d.clone());
            let prop = propagated(kk, output_dim, weight, bias, center, eps);
            let body = rat_eq(c, lower_at(&prop, &i), upper_at(&prop, &i));
            ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, fin_d, body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.base.nat.clone());
            let od_ty = c.output_dim_ty();
            let (od_id, output_dim) = b.fresh_local(od_ty.clone());
            let w_ty = c.weight_family_ty(&b, &output_dim);
            let (w_id, weight) = b.fresh_local(w_ty.clone());
            let bias_ty = c.bias_family_ty(&b, &output_dim);
            let (bias_id, bias) = b.fresh_local(bias_ty.clone());
            let center_ty = c.center_ty(&output_dim);
            let (center_id, center) = b.fresh_local(center_ty.clone());
            let (eps_id, eps) = b.fresh_local(c.base.rat.clone());
            let body = concl(&b, &k, &output_dim, &weight, &bias, &center, &eps);
            let e = b.mk_pi(eps_id, BinderInfo::Default, c.base.rat.clone(), body);
            let e = b.mk_pi(center_id, BinderInfo::Default, center_ty, e);
            let e = b.mk_pi(bias_id, BinderInfo::Default, bias_ty, e);
            let e = b.mk_pi(w_id, BinderInfo::Default, w_ty, e);
            let e = b.mk_pi(od_id, BinderInfo::Default, od_ty, e);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.base.nat.clone());
            let od_ty = c.output_dim_ty();
            let (od_id, output_dim) = b.fresh_local(od_ty.clone());
            let w_ty = c.weight_family_ty(&b, &output_dim);
            let (w_id, weight) = b.fresh_local(w_ty.clone());
            let bias_ty = c.bias_family_ty(&b, &output_dim);
            let (bias_id, bias) = b.fresh_local(bias_ty.clone());
            let center_ty = c.center_ty(&output_dim);
            let (center_id, center) = b.fresh_local(center_ty.clone());
            let (eps_id, eps) = b.fresh_local(c.base.rat.clone());

            // motive : fun kk => concl kk.
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (kk_id, kk) = ch.fresh_local(c.base.nat.clone());
                let body = concl(&ch, &kk, &output_dim, &weight, &bias, &center, &eps);
                ch.finish_child(ch.mk_lam(kk_id, BinderInfo::Default, c.base.nat.clone(), body))
            };

            // base : concl 0. ibp_propagate 0 … ι-reduces to eps_ball, zero-width.
            let base = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_d0 = Expr::app(
                    c.base.fin.clone(),
                    c.out_dim(&output_dim, c.nat_zero.clone()),
                );
                let (i_id, _i) = ch.fresh_local(fin_d0.clone());
                // Both endpoints reduce to Rat.zero; Eq.refl Rat Rat.zero.
                let proof = Expr::apps(
                    eq_refl.clone(),
                    [c.base.rat.clone(), c.base.rat_zero.clone()],
                );
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_d0, proof))
            };

            // succ : ∀ (n : Nat), concl n → concl (n+1).
            let succ = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ch.fresh_local(c.base.nat.clone());
                let ih_ty = concl(&ch, &n, &output_dim, &weight, &bias, &center, &eps);
                let (ih_id, ih) = ch.fresh_local(ih_ty.clone());

                // prev := ibp_propagate n … (the IH's subject).
                let prev = propagated(&n, &output_dim, &weight, &bias, &center, &eps);
                let n_succ = Expr::app(c.nat_succ.clone(), n.clone());
                let out_n = c.out_dim(&output_dim, n.clone());
                let out_succ = c.out_dim(&output_dim, n_succ.clone());
                let w_n = Expr::app(weight.clone(), n.clone());
                let bias_n = Expr::app(bias.clone(), n.clone());

                // lb_eq : ∀ j, (linear_bounds out_succ out_n w_n bias_n prev).lower j = .upper j
                //   via linear_bounds_preserves_eq out_succ out_n w_n bias_n prev ih.
                let lb_eq = Expr::apps(
                    linear_pres.clone(),
                    [out_succ.clone(), out_n, w_n, bias_n, prev, ih],
                );
                let lb = {
                    // The linear bounds term (matches ibp_propagate's succ reduction).
                    let prev2 = propagated(&n, &output_dim, &weight, &bias, &center, &eps);
                    let w_n2 = Expr::app(weight.clone(), n.clone());
                    let bias_n2 = Expr::app(bias.clone(), n.clone());
                    c.linear_bounds_app(
                        out_succ.clone(),
                        c.out_dim(&output_dim, n.clone()),
                        w_n2,
                        bias_n2,
                        prev2,
                    )
                };
                // result : ∀ i, (relu_bounds out_succ lb).lower i = .upper i
                //   via relu_bounds_preserves_eq out_succ lb lb_eq.
                //   This is def-eq to `concl (n+1)` (ibp_propagate (n+1) reduces to relu(linear(prev))).
                let proof = Expr::apps(relu_pres.clone(), [out_succ, lb, lb_eq]);
                let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
                ch.finish_child(ch.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), r))
            };

            let rec = Expr::apps(nat_rec_prop(), [motive, base, succ, k.clone()]);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.base.rat.clone(), rec);
            let e = b.mk_lam(center_id, BinderInfo::Default, center_ty, e);
            let e = b.mk_lam(bias_id, BinderInfo::Default, bias_ty, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, w_ty, e);
            let e = b.mk_lam(od_id, BinderInfo::Default, od_ty, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the R-weak constructive proof term for `NNVerify.ibp_tightness_step`.
///
/// Shape (matching `build_ibp_tightness_step_type`):
/// ```text
/// fun (k) (output_dim) (weight) (bias) (center) (eps) (h_nonneg : 0 ≤ eps)
///     (_ih : bound at k) =>
///   le_of_eq_of_le LHS Rat.zero RHS h_width_zero h_rhs_nonneg
/// ```
/// where `LHS = ibp_width (out_dim (k+1)) (ibp_propagate (k+1) … (eps_ball …))`
/// collapses to `Rat.zero` via `ibp_width_zero … (ibp_propagate_eq (k+1) …)`,
/// and `RHS = 2·eps·norm_product (k+1) norms ≥ 0` via `Rat.mul_nonneg` from
/// `0 ≤ 2·eps` (base-case helpers) and `0 ≤ norm_product …`
/// (`norm_product_nonneg` fed `infinity_norm_nonneg` per layer).
pub(super) fn build_ibp_tightness_step_value(c: &IbpTightnessConsts) -> Expr {
    let le_of_eq_of_le = Expr::const_(Name::from_string("NNVerify.le_of_eq_of_le"), vec![]);
    let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
    let zero_le_two = Expr::const_(Name::from_string("NNVerify.rat_zero_le_two"), vec![]);
    let ibp_width_zero = Expr::const_(Name::from_string("NNVerify.ibp_width_zero"), vec![]);
    let propagate_eq = Expr::const_(Name::from_string("NNVerify.ibp_propagate_eq"), vec![]);
    let norm_product_nonneg =
        Expr::const_(Name::from_string("NNVerify.norm_product_nonneg"), vec![]);
    let infinity_norm_nonneg =
        Expr::const_(Name::from_string("NNVerify.infinity_norm_nonneg"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let od_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(od_ty.clone());
    let w_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, weight) = b.fresh_local(w_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, bias) = b.fresh_local(bias_ty.clone());
    let center_ty = c.center_ty(&output_dim);
    let (center_id, center) = b.fresh_local(center_ty.clone());
    let (eps_id, eps) = b.fresh_local(c.base.rat.clone());
    let nonneg_ty = c.base.rat_le(c.base.rat_zero.clone(), eps.clone());
    let (h_nonneg_id, h_nonneg) = b.fresh_local(nonneg_ty.clone());

    let k_succ = Expr::app(c.nat_succ.clone(), k.clone());
    let out_succ = c.out_dim(&output_dim, k_succ.clone());

    // ih type at k (consumed but unused — the step proves the bound directly).
    let ih_ty = {
        // Reuse the inner-bound prop builder from the proofs module via the
        // public re-export below. Built inline here to avoid a cross-module
        // private call: it is exactly `concl_bound k`.
        super::nn_verify_ibp_tightness_proofs::inner_bound_prop_at(
            c,
            &b,
            &k,
            &output_dim,
            &weight,
            &bias,
            &center,
            &eps,
        )
    };
    let (ih_id, _ih) = b.fresh_local(ih_ty.clone());

    // LHS = ibp_width (out_succ) (ibp_propagate (k+1) … (eps_ball …)).
    let eb = c.eps_ball_app(
        c.out_dim(&output_dim, c.nat_zero.clone()),
        center.clone(),
        eps.clone(),
    );
    let propagated = c.ibp_propagate_app(
        k_succ.clone(),
        output_dim.clone(),
        weight.clone(),
        bias.clone(),
        eb,
    );
    let lhs = c.ibp_width_app(out_succ.clone(), propagated.clone());

    // RHS = 2·eps·norm_product (k+1) norms.
    let norms = c.norm_lambda(&b, &k_succ, &output_dim, &weight);
    let two_eps = c.base.mul(c.two(), eps.clone());
    let np = c.norm_product_app(k_succ.clone(), norms.clone());
    let rhs = c.base.mul(two_eps.clone(), np.clone());

    // h_pe : ∀ i, propagated.lower i = .upper i  via ibp_propagate_eq (k+1) ….
    let h_pe = Expr::apps(
        propagate_eq,
        [
            k_succ.clone(),
            output_dim.clone(),
            weight.clone(),
            bias.clone(),
            center.clone(),
            eps.clone(),
        ],
    );
    // h_width_zero : LHS = Rat.zero  via ibp_width_zero out_succ propagated h_pe.
    let h_width_zero = Expr::apps(ibp_width_zero, [out_succ.clone(), propagated, h_pe]);

    // h_2eps : 0 ≤ 2·eps  via Rat.mul_nonneg 2 eps zero_le_two h_nonneg.
    let h_2eps = Expr::apps(
        mul_nonneg.clone(),
        [c.two(), eps.clone(), zero_le_two, h_nonneg],
    );
    // h_norms : ∀ (i : Fin (k+1)), 0 ≤ norms i.
    //   norms i = infinity_norm (out_dim (val+1)) (out_dim val) (weight val), and
    //   `infinity_norm_nonneg` proves `0 ≤ infinity_norm m n W` for any m n W, so
    //   `fun i => infinity_norm_nonneg (out_dim (val i + 1)) (out_dim (val i)) (weight (val i))`.
    let h_norms = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_succ = Expr::app(c.base.fin.clone(), k_succ.clone());
        let (i_id, i) = ch.fresh_local(fin_succ.clone());
        let idx = c.fin_val_app(&k_succ, i.clone());
        let out_i = c.out_dim(&output_dim, idx.clone());
        let out_succ_i = c.out_dim(&output_dim, Expr::app(c.nat_succ.clone(), idx.clone()));
        let w_i = Expr::app(weight.clone(), idx);
        let body = Expr::apps(infinity_norm_nonneg, [out_succ_i, out_i, w_i]);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_succ, body))
    };
    // h_np : 0 ≤ norm_product (k+1) norms  via norm_product_nonneg (k+1) norms h_norms.
    let h_np = Expr::apps(norm_product_nonneg, [k_succ, norms, h_norms]);
    // h_rhs : 0 ≤ 2·eps·norm_product …  via Rat.mul_nonneg (2·eps) np h_2eps h_np.
    let h_rhs = Expr::apps(mul_nonneg, [two_eps, np, h_2eps, h_np]);

    // le_of_eq_of_le LHS Rat.zero RHS h_width_zero h_rhs : LHS ≤ RHS.
    let body = Expr::apps(
        le_of_eq_of_le,
        [lhs, c.base.rat_zero.clone(), rhs, h_width_zero, h_rhs],
    );

    // Wrap binders: ih, h_nonneg, eps, center, bias, weight, output_dim, k.
    let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
    let e = b.mk_lam(h_nonneg_id, BinderInfo::Default, nonneg_ty, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.base.rat.clone(), e);
    let e = b.mk_lam(center_id, BinderInfo::Default, center_ty, e);
    let e = b.mk_lam(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, w_ty, e);
    let e = b.mk_lam(od_id, BinderInfo::Default, od_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}
