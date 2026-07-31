// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Registration entrypoints for GLUE-4 HALVED (the R2 halved-derivative
// hypotheses). `include!`d into `boolean_analysis_kkl_dualhc_half2.rs` — shares
// its `Half2Consts` and imports. See that module for the statements and proofs.
// Split out to keep each file under the 500-line convention. (Regular `//`
// comments: inner doc `//!` is not allowed at an `include!` site.)

impl Environment {
    /// Register GLUE-4 HALVED bridge lemmas. Idempotent; kernel-checked,
    /// `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_half2(&mut self) -> Result<(), EnvError> {
        self.register_half_deriv_chi_eq_sq()?;
        self.register_four_half_sq_eq_one()?;
        self.register_half_deriv_e_chi_eq_e()?;
        self.register_half_deriv_chi_sq_eq_chi()?;
        self.register_disagree_sq_le_four()?;
        self.register_half_deriv_chi_le_one()?;
        Ok(())
    }

    /// `BoolAnalysis.half_deriv_chi_le_one :`
    /// `∀ g, (g·g) ≤ 4 → (g·g)·(half·half) ≤ 1`.  R2's H4 for `chi := (g·g)·(h·h)`.
    /// Proof:
    /// `(g·g)·(h·h) ≤ 4·(h·h)`   [mul_le_right (h·h) (g·g) 4 (g²≤4) (0≤h·h)]
    ///             `= 1`          [four_half_sq_eq_one],  then `Eq.subst`.
    /// Kernel-checked, `Constructive`, empty closure.
    pub fn register_half_deriv_chi_le_one(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.half_deriv_chi_le_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_algebra_rat_halves()?;
        self.init_rat_field_inst()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_le_*, sq_nonneg
        self.register_four_half_sq_eq_one()?; // 4·(h·h) = 1

        let c = Half2Consts::new();
        let build = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.rat());
            let h = c.half();
            let gg = c.mul(g.clone(), g.clone());
            let hh = c.mul(h.clone(), h.clone());
            let four = c.four();
            let chi = c.mul(gg.clone(), hh.clone()); // (g·g)·(h·h)
            let four_hh = c.mul(four.clone(), hh.clone()); // 4·(h·h)
                                                           // hsq : (g·g) ≤ 4
            let hsq_ty = c.le(gg.clone(), four.clone());
            let (hs_id, hs) = b.fresh_local(hsq_ty.clone());
            let concl = c.le(chi.clone(), c.one());
            let tail = if for_value {
                // le1 : (g·g)·(h·h) ≤ 4·(h·h)
                let le1 = c.mul_le_right(
                    hh.clone(),
                    gg.clone(),
                    four.clone(),
                    hs,
                    c.sq_nonneg(h.clone()),
                );
                // eq1 : 4·(h·h) = 1
                let four_hh_eq_one = Expr::const_(
                    Name::from_string("BoolAnalysis.four_half_sq_eq_one"),
                    vec![],
                );
                // subst along eq1: motive t ↦ chi ≤ t.
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = d.fresh_local(c.rat());
                    let body = c.le(chi.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
                };
                c.subst(motive, four_hh.clone(), c.one(), four_hh_eq_one, le1)
            } else {
                concl
            };
            let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, BinderInfo::Default, ty, body)
                } else {
                    b.mk_pi(id, BinderInfo::Default, ty, body)
                }
            };
            let e = bind(&b, hs_id, hsq_ty, tail);
            let e = bind(&b, g_id, c.rat(), e);
            b.finish(e)
        };
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    /// `BoolAnalysis.disagree_sq_le_four : ∀ (a b : Bool), (g·g) ≤ 4`
    /// (`g := pm a − pm b ∈ {0,±2}`, so `g·g ∈ {0,4} ≤ 4`). The H4-feeder
    /// (`g² ≤ 4`) the indicator bound `chi ≤ 1` rests on. `Bool.rec` on `a`
    /// then `b`; each of the four leaves is
    /// `Rat.le_of_ble_eq_true (g·g) 4 (Eq.refl Bool.true)` — the concrete
    /// `Rat.ble (g·g) 4` native-reduces to `true` (`g·g` is integer-valued).
    /// Kernel-checked, `Constructive`, empty closure.
    pub fn register_disagree_sq_le_four(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.disagree_sq_le_four");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis()?; // pm
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_bool()?;
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true

        let c = Half2Consts::new();
        let bool_c = c.bool_.clone();
        let bt = c.bool_true.clone();
        let bf = c.bool_false.clone();
        let four = c.four();
        // P(a,b) := (g·g) ≤ 4 ;  leaf proof := le_of_ble_refl (g·g) 4.
        let gg = |a: Expr, b: Expr| {
            let g = c.g_bool(a, b);
            c.mul(g.clone(), g)
        };
        let concl_of = |a: Expr, b: Expr| c.le(gg(a, b), four.clone());
        let leaf_of = |a: Expr, b: Expr| c.le_of_ble_refl(gg(a, b), four.clone());

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, av) = b.fresh_local(bool_c.clone());
            let (b_id, bv) = b.fresh_local(bool_c.clone());
            let concl = concl_of(av.clone(), bv.clone());
            let e = b.mk_pi(b_id, BinderInfo::Default, bool_c.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut bld = EnvDeclBuilder::new();
            let (a_id, av) = bld.fresh_local(bool_c.clone());
            let (b_id, bv) = bld.fresh_local(bool_c.clone());
            // motive_a : fun a' => (g(a',b)·g(a',b)) ≤ 4
            let motive_a = {
                let mut d = EnvDeclBuilder::child_of(&bld);
                let (ap_id, ap) = d.fresh_local(bool_c.clone());
                let body = concl_of(ap.clone(), bv.clone());
                d.finish_child(d.mk_lam(ap_id, BinderInfo::Default, bool_c.clone(), body))
            };
            let inner_rec = |av_c: Expr, parent: &EnvDeclBuilder| -> Expr {
                let d = EnvDeclBuilder::child_of(parent);
                let motive_b = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (bp_id, bp) = e.fresh_local(bool_c.clone());
                    let body = concl_of(av_c.clone(), bp.clone());
                    e.finish_child(e.mk_lam(bp_id, BinderInfo::Default, bool_c.clone(), body))
                };
                let b_false = leaf_of(av_c.clone(), bf.clone());
                let b_true = leaf_of(av_c.clone(), bt.clone());
                let e = Expr::apps(
                    c.bool_rec_prop.clone(),
                    [motive_b, b_false, b_true, bv.clone()],
                );
                d.finish_child(e)
            };
            let a_false = inner_rec(bf.clone(), &bld);
            let a_true = inner_rec(bt.clone(), &bld);
            let rec_a = Expr::apps(
                c.bool_rec_prop.clone(),
                [motive_a, a_false, a_true, av.clone()],
            );
            let e = bld.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), rec_a);
            let e = bld.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e);
            bld.finish(e)
        };
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.half_deriv_chi_sq_eq_chi :`
    /// `∀ g, (g·g)·(g·g) = 4·(g·g) → chi·chi = chi`  (`chi := (g·g)·(half·half)`).
    /// R2's H3. Kernel-checked, `Constructive`, empty closure. See `h3_proof`.
    pub fn register_half_deriv_chi_sq_eq_chi(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.half_deriv_chi_sq_eq_chi");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_algebra_rat_halves()?;
        self.init_rat_field_inst()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_mul_comm_proof()?;

        let c = Half2Consts::new();
        let build = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.rat());
            let h = c.half();
            let gg = c.mul(g.clone(), g.clone());
            let hh = c.mul(h.clone(), h.clone());
            let chi = c.mul(gg.clone(), hh.clone());
            let four_gg = c.mul(c.four(), gg.clone());
            // hsq : (g·g)·(g·g) = 4·(g·g)
            let hsq_ty = c.eq(c.mul(gg.clone(), gg.clone()), four_gg);
            let (hs_id, hs) = b.fresh_local(hsq_ty.clone());
            let concl = c.eq(c.mul(chi.clone(), chi.clone()), chi.clone());
            let tail = if for_value {
                c.h3_proof(&b, g.clone(), hs)
            } else {
                concl
            };
            let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, BinderInfo::Default, ty, body)
                } else {
                    b.mk_pi(id, BinderInfo::Default, ty, body)
                }
            };
            let e = bind(&b, hs_id, hsq_ty, tail);
            let e = bind(&b, g_id, c.rat(), e);
            b.finish(e)
        };
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    /// `BoolAnalysis.half_deriv_e_chi_eq_e :`
    /// `∀ g, g·(g·g) = 4·g → (g·half)·((g·g)·(half·half)) = g·half`.
    /// R2's H2 for `e := g·half`, `chi := (g·g)·(half·half)`. Kernel-checked,
    /// `Constructive`, empty closure. See `h2_proof`.
    pub fn register_half_deriv_e_chi_eq_e(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.half_deriv_e_chi_eq_e");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_algebra_rat_halves()?;
        self.init_rat_field_inst()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_mul_comm_proof()?;

        let c = Half2Consts::new();
        let build = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.rat());
            let h = c.half();
            let gg = c.mul(g.clone(), g.clone());
            let hh = c.mul(h.clone(), h.clone());
            let gh = c.mul(g.clone(), h.clone());
            let chi = c.mul(gg.clone(), hh.clone());
            let four_g = c.mul(c.four(), g.clone());
            // hcube : g·(g·g) = 4·g
            let hcube_ty = c.eq(c.mul(g.clone(), gg.clone()), four_g);
            let (hc_id, hc) = b.fresh_local(hcube_ty.clone());
            let concl = c.eq(c.mul(gh.clone(), chi.clone()), gh.clone());
            let tail = if for_value {
                c.h2_proof(&b, g.clone(), hc)
            } else {
                concl
            };
            let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
                if for_value {
                    b.mk_lam(id, BinderInfo::Default, ty, body)
                } else {
                    b.mk_pi(id, BinderInfo::Default, ty, body)
                }
            };
            let e = bind(&b, hc_id, hcube_ty, tail);
            let e = bind(&b, g_id, c.rat(), e);
            b.finish(e)
        };
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }

    /// `BoolAnalysis.four_half_sq_eq_one : 4·(half·half) = 1`.
    /// Constant ring-algebra leaf. Kernel-checked, `Constructive`, empty closure.
    pub fn register_four_half_sq_eq_one(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.four_half_sq_eq_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_algebra_rat_halves()?; // Rat.two, Rat.two_ne_zero, mul_inv_cancel
        self.init_rat_field_inst()?; // mul_assoc, mul_one, one_mul, mmmc
        self.register_rat_mul_mul_mul_comm_theorem()?; // Rat.mul_mul_mul_comm

        let c = Half2Consts::new();
        let h = c.half();
        let hh = c.mul(h.clone(), h.clone());
        let lhs = c.mul(c.four(), hh);
        let ty = c.eq(lhs, c.one());
        let b = EnvDeclBuilder::new();
        let value = c.four_hh_eq_one(&b);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.half_deriv_chi_eq_sq : ∀ g, (g·g)·(half·half) = (g·half)·(g·half)`.
    /// This is R2's H1 for `e := g·half`, `chi := (g·g)·(half·half)` — pure
    /// `mul_mul_mul_comm` (symm). Kernel-checked, `Constructive`, empty closure.
    pub fn register_half_deriv_chi_eq_sq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.half_deriv_chi_eq_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_algebra_rat_halves()?;
        self.init_rat_field_inst()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;

        let c = Half2Consts::new();
        let build = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(c.rat());
            let h = c.half();
            let gg = c.mul(g.clone(), g.clone());
            let hh = c.mul(h.clone(), h.clone());
            let gh = c.mul(g.clone(), h.clone());
            let chi = c.mul(gg.clone(), hh.clone()); // (g·g)·(h·h)
            let ee = c.mul(gh.clone(), gh.clone()); // (g·h)·(g·h)
            let tail = if for_value {
                // mmmc g h g h : (g·h)·(g·h) = (g·g)·(h·h) ; symm gives chi = ee.
                let mmmc = c.mmmc(g.clone(), h.clone(), g.clone(), h.clone());
                c.symm(ee.clone(), chi.clone(), mmmc)
            } else {
                c.eq(chi, ee)
            };
            let e = if for_value {
                b.mk_lam(g_id, BinderInfo::Default, c.rat(), tail)
            } else {
                b.mk_pi(g_id, BinderInfo::Default, c.rat(), tail)
            };
            b.finish(e)
        };
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build(false),
            value: build(true),
        })
    }
}
