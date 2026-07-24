// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// RUNG-B main theorem assembly. Included from `boolean_analysis_kkl_rungb.rs`
// (shares `RungBConsts`). Registers:
//   * `BoolAnalysis.lowband_term_le`               (the per-S core)
//   * `BoolAnalysis.kkl_derivative_lowband_link`   (the rung)

impl Environment {
    /// Register the RUNG-B derivative→low-band link chain. Idempotent;
    /// kernel-checked, `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_rungb(&mut self) -> Result<(), EnvError> {
        self.register_lowband_term_le()?;
        self.register_kkl_derivative_lowband_link()?;
        Ok(())
    }

    /// `BoolAnalysis.lowband_term_le :
    ///   ∀ (size c : Rat) (b1 b2 : Bool),
    ///     0 ≤ c → 0 ≤ size → (b1 = true → Rat.one ≤ size)
    ///       → four·(ind (and b1 b2)·c) ≤ size·(ind b2·(four·c))`.
    ///
    /// The per-S band-domination core (nested `Bool.rec`). Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_lowband_term_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.lowband_term_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // ind, Rat carriers
        self.init_rat()?;
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_right, mul_nonneg
        self.register_rat_order_proofs()?; // Rat.le_refl
        self.register_ind_nonneg()?; // BoolAnalysis.ind_nonneg
        self.register_natcast_nonneg()?; // BoolAnalysis.natCast_nonneg (for 0 ≤ four)

        let c = RungBConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: lowband_term_type(&c),
            value: build_lowband_term_proof(&c),
        })
    }

    /// `BoolAnalysis.kkl_derivative_lowband_link :
    ///   ∀ (n k : Nat) (f : BoolFn n),
    ///     four · M_{1..k}[f]
    ///       ≤ Fin.sum n (fun i => subsetSum n (fun S => ind (S i) · w_band S))`,
    /// where `M_{1..k}[f] := subsetSum n m_lo_fn`,
    ///       `w_band S := ind (not (ble (k+1) |S|)) · (four · (f̂·f̂))`,
    ///       `m_lo_fn S := ind (and (ble 1 |S|) (not (ble (k+1) |S|))) · (f̂·f̂)`.
    ///
    /// `4·M_{1..k} ≤ Σ_i W^{≤k}[D_i f]` — the derivative→low-band spectral link.
    /// See module docs for the three-piece proof (Fubini double-count + scalar
    /// pull-out + pointwise band domination). Kernel-checked, `Constructive`,
    /// empty closure. Idempotent.
    pub fn register_kkl_derivative_lowband_link(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_derivative_lowband_link");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_set_size()?;
        self.register_set_size_nat()?;
        self.register_subset_sum_double_count()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_subset_sum_le_of_pointwise()?;
        self.register_lowband_term_le()?;
        self.register_fourier_sq_nonneg()?;
        self.register_set_size_nonneg()?;
        self.register_set_size_eq_natcast()?;
        self.register_nat_cast_le_of_ble()?;

        let c = RungBConsts::new();
        let ty = build_link_type(&c);
        let value = build_link_proof(&c);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Type:
/// `∀ (n k : Nat) (f : BoolFn n),
///    four · subsetSum n m_lo_fn
///      ≤ Fin.sum n (fun i => subsetSum n (coord_w_band_fn i))`.
fn build_link_type(c: &RungBConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());

    let m_lo = c.subset_sum_of(&n, c.m_lo_fn(&b, &n, &k, &f));
    let lhs = c.mul(c.four(), m_lo);

    // RHS: Fin.sum n (fun i => subsetSum n (fun S => ind (S i) · w_band S))
    let rhs_summand = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let g = c.coord_w_band_fn(&ch, &n, &k, &f, &i);
        let body = c.subset_sum_of(&n, g);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let rhs = c.fin_sum_of(&n, rhs_summand);

    let concl = c.rat_le(lhs, rhs);
    let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, concl);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn build_link_proof(c: &RungBConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());

    let four = c.four();
    let m_lo_fn = c.m_lo_fn(&b, &n, &k, &f);
    let m_lo = c.subset_sum_of(&n, m_lo_fn.clone());
    let big_a = c.mul(four.clone(), m_lo.clone()); // goal LHS

    let four_m_lo_fn = c.four_m_lo_fn(&b, &n, &k, &f);
    let ss_four_mlo = c.subset_sum_of(&n, four_m_lo_fn.clone());

    let w_band_fn = c.w_band_fn(&b, &n, &k, &f);
    let size_w_band_fn = c.size_w_band_fn(&b, &n, &k, &f);
    let ss_size_wband = c.subset_sum_of(&n, size_w_band_fn.clone());

    // goal RHS: Fin.sum n (fun i => subsetSum n (coord_w_band_fn i))
    let rhs_summand = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let g = c.coord_w_band_fn(&ch, &n, &k, &f, &i);
        let body = c.subset_sum_of(&n, g);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let rhs_sum = c.fin_sum_of(&n, rhs_summand);

    // ── (1) h_dc : rhs_sum = ss_size_wband   [subsetSum_double_count n w_band]
    let h_dc = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_double_count"),
            vec![],
        ),
        [n.clone(), w_band_fn.clone()],
    );

    // ── (2) h_smul : ss_four_mlo = big_a   [subsetSum_smul n four m_lo_fn]
    let h_smul = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]),
        [n.clone(), four.clone(), m_lo_fn.clone()],
    );

    // ── (3) pointwise : ∀ S, four_m_lo_fn S ≤ size_w_band_fn S
    //   := fun S => lowband_term_le (setSize n S) (f̂·f̂) b1 b2
    //                 (fourier_sq_nonneg n f S) (setSize_nonneg n S) (thr S)
    let pointwise = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (s_id, s) = ch.fresh_local(hcp.clone());

        let size = c.set_size_of(&n, &s);
        let csq = c.fsq(&n, &f, &s);
        let ss = c.set_size_nat_of(&n, &s);
        let b1 = c.ble1(ss.clone());
        let b2 = c.bnot(c.ble_succ_k(&k, ss.clone()));

        // h_c : 0 ≤ f̂·f̂   [fourier_sq_nonneg n f S]
        let h_c = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.fourier_sq_nonneg"), vec![]),
            [n.clone(), f.clone(), s.clone()],
        );
        // h_size : 0 ≤ setSize n S   [setSize_nonneg n S]
        let h_size = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.setSize_nonneg"), vec![]),
            [n.clone(), s.clone()],
        );
        // thr : b1 = true → Rat.one ≤ setSize n S
        //   := fun (h : ble 1 |S| = true) =>
        //        subst (motive t => mk(ofNat 1) 1 ≤ t)
        //              (mk(ofNat |S|) 1) (setSize n S)
        //              (symm (setSize_eq_natCast n S))
        //              (Nat.cast_le_of_ble 1 |S| h)
        //   (mk(ofNat 1) 1 ≡ Rat.one definitionally, so this inhabits the goal.)
        let thr = {
            let mut tb = EnvDeclBuilder::child_of(&ch);
            let ante = c.eq_bool(b1.clone(), c.bool_true.clone());
            let (h_id, hh) = tb.fresh_local(ante.clone());

            let one_nat = c.one_nat();
            // cast_le : mk(ofNat 1) 1 ≤ mk(ofNat |S|) 1   [Nat.cast_le_of_ble 1 |S| h]
            let cast_le = Expr::apps(
                Expr::const_(Name::from_string("Nat.cast_le_of_ble"), vec![]),
                [one_nat.clone(), ss.clone(), hh],
            );
            let natcast_one = c.natcast(one_nat);
            let natcast_ss = c.natcast(ss.clone());
            // h_eq : setSize n S = mk(ofNat |S|) 1   [setSize_eq_natCast n S]
            let h_eq = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.setSize_eq_natCast"), vec![]),
                [n.clone(), s.clone()],
            );
            // symm : mk(ofNat |S|) 1 = setSize n S
            let h_eq_sym = c.symm_rat(size.clone(), natcast_ss.clone(), h_eq);
            // motive t => mk(ofNat 1) 1 ≤ t
            let motive = {
                let mut mm = EnvDeclBuilder::child_of(&tb);
                let (t_id, t) = mm.fresh_local(c.rat());
                let body = c.rat_le(natcast_one.clone(), t);
                mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            // result : mk(ofNat 1) 1 ≤ setSize n S   (def-eq to Rat.one ≤ setSize n S)
            let result = c.subst_rat(motive, natcast_ss, size.clone(), h_eq_sym, cast_le);
            tb.finish_child(tb.mk_lam(h_id, BinderInfo::Default, ante, result))
        };

        let term = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.lowband_term_le"), vec![]),
            [size, csq, b1, b2, h_c, h_size, thr],
        );
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, term))
    };

    // h_le : ss_four_mlo ≤ ss_size_wband
    //   [subsetSum_le_of_pointwise n four_m_lo_fn size_w_band_fn pointwise]
    let h_le = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_le_of_pointwise"),
            vec![],
        ),
        [
            n.clone(),
            four_m_lo_fn.clone(),
            size_w_band_fn.clone(),
            pointwise,
        ],
    );

    // ── (4) chain.
    // step_a : big_a ≤ ss_size_wband
    //   subst (motive t => t ≤ ss_size_wband) ss_four_mlo big_a h_smul h_le
    let motive_a = {
        let mut mm = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mm.fresh_local(c.rat());
        let body = c.rat_le(t, ss_size_wband.clone());
        mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    let step_a = c.subst_rat(motive_a, ss_four_mlo.clone(), big_a.clone(), h_smul, h_le);

    // final : big_a ≤ rhs_sum
    //   subst (motive t => big_a ≤ t) ss_size_wband rhs_sum (symm h_dc) step_a
    let h_dc_sym = c.symm_rat(rhs_sum.clone(), ss_size_wband.clone(), h_dc);
    let motive_f = {
        let mut mm = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mm.fresh_local(c.rat());
        let body = c.rat_le(big_a.clone(), t);
        mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    let final_ = c.subst_rat(
        motive_f,
        ss_size_wband.clone(),
        rhs_sum.clone(),
        h_dc_sym,
        step_a,
    );

    let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, final_);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
