// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// PER-COORDINATE dual-HC MEASURE-IDENTITY builder (eR / h_meas). `include!`d into
// `boolean_analysis_kkl_dualhc_percoord_eqs.rs`. Regular `//` comments only.
//
// `build_h_meas` proves the measure identity `dualhc_per_coord` previously took
// as a hypothesis:
//
//   h_meas : (8^n·8^n)·((16·Inf)·(Inf·Inf)) = 16·(m³·8^n)
//
// where `m := subsetSum n (g²·(half·half))`, `8^n := Rat.powNat 8 n`, the LHS
// `16 := Rat.ofNat 16`, the RHS `16 := lit4·lit4`, `Inf := Influence n f i`. With
// the two PROVEN leaves
//   * `dualhc_m_pow2_eq_4pow_influence` : m·2^n = (2^n·2^n)·Inf  (⟹ m = 2^n·Inf
//     via `build_m_eq`),
//   * `powNat_eight_eq_two_cubed`       : 8^n = 2^n·(2^n·2^n),
// the `64^n`-bookkeeping collapses to a finite `Rat`-ring shuffle. Both sides are
// transported to the canonical `K := (D·D)·(16·(I·(I·I)))` (= `16·D²·I³`).

impl PerCoordConsts {
    fn m_pow2_inf_at(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.m_pow2_inf.clone(), [n.clone(), f.clone(), i.clone()])
    }
    fn eight_cubed_at(&self, n: &Expr) -> Expr {
        Expr::app(self.eight_cubed.clone(), n.clone())
    }
    /// `Rat.mul_natCast a b : mk(ofNat a) 1 · mk(ofNat b) 1 = mk(ofNat (a·b)) 1`.
    fn mul_natcast_at(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_natcast.clone(), [a, b])
    }
    /// `Rat.mul_mul_mul_comm a b cc d : (a·b)·(cc·d) = (a·cc)·(b·d)`.
    fn mmmc_at(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.mmmc.clone(), [a, b, cc, d])
    }
    /// `0 < 2` := `@Int.NonNeg.mk 1` (byte-matches `lit_pos 2`).
    fn two_pos(&self) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            self.nat_lit_er(1),
        )
    }
    /// `nat_lit k : Nat` — `Nat.succ^k Nat.zero`. (`er`-suffixed to avoid clashing
    /// with the `nat_lit` in the build sibling; PerCoordConsts has no bare Nat
    /// literal accessor.)
    fn nat_lit_er(&self, k: usize) -> Expr {
        let mut nat = self.nat_zero.clone();
        for _ in 0..k {
            nat = Expr::app(self.nat_succ.clone(), nat);
        }
        nat
    }
}

/// Build the measure identity `h_meas : cc·cube16 = rhs_bound` for `(n, f, i)`.
/// The `m`/`inf`/`8^n`/`16` spellings byte-match `build_per_coord`'s `h_meas_ty`.
fn build_h_meas(c: &PerCoordConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
    let half = c.half();
    let four = c.lit(4);
    let sixteen = c.mul(four.clone(), four.clone()); // RHS 16 = lit4·lit4
    let big_d = c.pow_of(8, n); // D := 8^n
    let q = c.pow_of(2, n); // Q := 2^n

    let g = c.deriv_lam(parent, n, f, i);
    let m = c.ssum(
        n,
        c.lam_hcp(parent, n, |x| {
            let gx = Expr::app(g.clone(), x.clone());
            c.mul(c.mul(gx.clone(), gx), c.mul(half.clone(), half.clone()))
        }),
    );
    let inf = c.influence_of(n, f, i);
    let s16 = c.ofnat(16); // LHS 16 = Rat.ofNat 16

    let dd = c.mul(big_d.clone(), big_d.clone()); // D·D
    let cube16 = c.mul(
        c.mul(s16.clone(), inf.clone()),
        c.mul(inf.clone(), inf.clone()),
    );
    let m_cube = c.mul(m.clone(), c.mul(m.clone(), m.clone()));
    let cc = dd.clone(); // cc = 8^n·8^n
    let cc_cube16 = c.mul(cc.clone(), cube16.clone()); // LHS_meas
    let rhs_bound = c.mul(sixteen.clone(), c.mul(m_cube.clone(), big_d.clone())); // RHS_meas

    // ── shared abbreviations ──
    let i_ii = c.mul(inf.clone(), c.mul(inf.clone(), inf.clone())); // I·(I·I)
    let ii = c.mul(inf.clone(), inf.clone()); // I·I
    let s16_iii = c.mul(s16.clone(), i_ii.clone()); // 16·(I·(I·I))
    let k_canon = c.mul(dd.clone(), s16_iii.clone()); // K := (D·D)·(16·(I·(I·I)))

    // ════ Path A : cc·cube16 = K ════
    // inner_a : (16·I)·(I·I) = 16·(I·(I·I))   mul_assoc 16 I (I·I).
    let inner_a = c.assoc(s16.clone(), inf.clone(), ii.clone());
    // a_eq : (D·D)·((16·I)·(I·I)) = (D·D)·(16·(I·(I·I)))   congr (D·D)·_ inner_a.
    let a_eq = c.congr_l(parent, &dd, cube16.clone(), s16_iii.clone(), inner_a);

    // ════ Path B : rhs_bound = K ════
    // bm : m = Q·I   (build_m_eq from dualhc_m_pow2_eq_4pow_influence + 2^n cancel).
    let h_m = c.m_pow2_inf_at(n, f, i); // m·Q = (Q·Q)·I
    let q_pos = Expr::apps(c.pow_pos.clone(), [c.lit(2), n.clone(), c.two_pos()]); // 0 < Q
    let q_ne = Expr::apps(c.ne_zero_of_pos.clone(), [q.clone(), q_pos]); // Q = 0 → False
    let q_cancel = Expr::apps(c.mul_inv_cancel.clone(), [q.clone(), q_ne]); // Q·inv Q = 1
    let bm = build_m_eq(c, parent, &m, &q, &inf, h_m, q_cancel); // m = Q·I
    let qi = c.mul(q.clone(), inf.clone()); // Q·I

    // bm3 : m·(m·m) = (Q·I)·((Q·I)·(Q·I))   congrArg (λz. z·(z·z)) bm.
    let cube_motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(z.clone(), c.mul(z.clone(), z.clone()));
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let qi_cube = c.mul(qi.clone(), c.mul(qi.clone(), qi.clone())); // (Q·I)·((Q·I)·(Q·I))
    let bm3 = Expr::apps(
        c.congr_arg1.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            m.clone(),
            qi.clone(),
            cube_motive,
            bm,
        ],
    );

    // reshuffle (Q·I)·((Q·I)·(Q·I)) = (Q·(Q·Q))·(I·(I·I)).
    //   sh1 : (Q·I)·(Q·I) = (Q·Q)·(I·I)   mmmc Q I Q I.
    let qq = c.mul(q.clone(), q.clone());
    let qq_ii = c.mul(qq.clone(), ii.clone());
    let sh1 = c.mmmc_at(q.clone(), inf.clone(), q.clone(), inf.clone());
    //   sh2 : (Q·I)·((Q·I)·(Q·I)) = (Q·I)·((Q·Q)·(I·I))   congr (Q·I)·_ sh1.
    let qi_qqii = c.mul(qi.clone(), qq_ii.clone());
    let sh2 = c.congr_l(
        parent,
        &qi,
        c.mul(qi.clone(), qi.clone()),
        qq_ii.clone(),
        sh1,
    );
    //   sh3 : (Q·I)·((Q·Q)·(I·I)) = (Q·(Q·Q))·(I·(I·I))   mmmc Q I (Q·Q) (I·I).
    let q_qq = c.mul(q.clone(), qq.clone()); // Q·(Q·Q)
    let qqq_iii = c.mul(q_qq.clone(), i_ii.clone());
    let sh3 = c.mmmc_at(q.clone(), inf.clone(), qq.clone(), ii.clone());
    //   bm3_resh : m·(m·m) = (Q·(Q·Q))·(I·(I·I)).
    let bm3_resh = {
        let ch = c.trans(m_cube.clone(), qi_cube.clone(), qi_qqii.clone(), bm3, sh2);
        c.trans(m_cube.clone(), qi_qqii.clone(), qqq_iii.clone(), ch, sh3)
    };
    // bD : 8^n = Q·(Q·Q)  (powNat_eight_eq_two_cubed n). symm → Q·(Q·Q) = 8^n.
    let b_d = c.eight_cubed_at(n); // D = Q·(Q·Q)
    let b_d_sym = c.symm(big_d.clone(), q_qq.clone(), b_d); // Q·(Q·Q) = D
                                                            //   m3_eq : m·(m·m) = D·(I·(I·I))   (replace Q·(Q·Q) → D on the left factor).
    let d_iii = c.mul(big_d.clone(), i_ii.clone());
    let resh_d = c.congr_r(parent, &i_ii, q_qq.clone(), big_d.clone(), b_d_sym);
    let m3_eq = c.trans(
        m_cube.clone(),
        qqq_iii.clone(),
        d_iii.clone(),
        bm3_resh,
        resh_d,
    );

    // b16 : lit4·lit4 = 16(=Rat.ofNat 16)   (mul_natCast 4 4; def-eq retype to s16).
    let b16 = c.mul_natcast_at(c.nat_lit_er(4), c.nat_lit_er(4)); // lit4·lit4 = mk(ofNat (4·4)) 1 ≡ s16

    // Substitute into rhs_bound = (lit4·lit4)·(m³·8^n):
    //   r_m3 : (lit4·lit4)·(m³·D) = (lit4·lit4)·((D·(I·(I·I)))·D)
    //          congr (lit4·lit4)·(_·D) m3_eq.
    let d_iii_d = c.mul(d_iii.clone(), big_d.clone()); // (D·(I·(I·I)))·D
                                                       // congr on the SECOND factor of rhs_bound: f := (lit4·lit4)·(_·D).
    let r_m3 = {
        let f_motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(c.rat.clone());
            let body = c.mul(sixteen.clone(), c.mul(z, big_d.clone()));
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        Expr::apps(
            c.congr_arg1.clone(),
            [
                c.rat.clone(),
                c.rat.clone(),
                m_cube.clone(),
                d_iii.clone(),
                f_motive,
                m3_eq,
            ],
        )
    };
    let rb_sub = c.mul(sixteen.clone(), d_iii_d.clone()); // (lit4·lit4)·((D·(I·(I·I)))·D)
                                                          //   r_16 : (lit4·lit4)·((D·(I·(I·I)))·D) = 16·((D·(I·(I·I)))·D)
                                                          //          congr (_·((D·(I·(I·I)))·D)) b16.
    let r_16 = c.congr_r(parent, &d_iii_d, sixteen.clone(), s16.clone(), b16);
    let s16_sub = c.mul(s16.clone(), d_iii_d.clone()); // 16·((D·(I·(I·I)))·D)

    // reshuffle 16·((D·(I·(I·I)))·D) = K = (D·D)·(16·(I·(I·I))).
    //   x := I·(I·I).
    let x = i_ii.clone();
    let d_x = c.mul(big_d.clone(), x.clone()); // D·x
                                               //   t1 : (D·x)·D = D·(x·D)   assoc D x D.
    let x_d = c.mul(x.clone(), big_d.clone());
    let d_xd = c.mul(big_d.clone(), x_d.clone());
    let t1 = c.assoc(big_d.clone(), x.clone(), big_d.clone());
    //   t2 : D·(x·D) = D·(D·x)   congr D·_ (comm x D).
    let d_dx = c.mul(big_d.clone(), d_x.clone());
    let t2 = c.congr_l(
        parent,
        &big_d,
        x_d.clone(),
        d_x.clone(),
        c.comm(x.clone(), big_d.clone()),
    );
    //   t3 : D·(D·x) = (D·D)·x   symm (assoc D D x).
    let dd_x = c.mul(dd.clone(), x.clone());
    let t3 = c.symm(
        dd_x.clone(),
        d_dx.clone(),
        c.assoc(big_d.clone(), big_d.clone(), x.clone()),
    );
    //   dxd_eq : (D·x)·D = (D·D)·x.
    let dxd_eq = {
        let ch = c.trans(d_iii_d.clone(), d_xd.clone(), d_dx.clone(), t1, t2);
        c.trans(d_iii_d.clone(), d_dx.clone(), dd_x.clone(), ch, t3)
    };
    //   u1 : 16·((D·x)·D) = 16·((D·D)·x)   congr 16·_ dxd_eq.
    let s16_ddx = c.mul(s16.clone(), dd_x.clone());
    let u1 = c.congr_l(parent, &s16, d_iii_d.clone(), dd_x.clone(), dxd_eq);
    //   u2 : 16·((D·D)·x) = (16·(D·D))·x   symm (assoc 16 (D·D) x).
    let s16_dd = c.mul(s16.clone(), dd.clone());
    let s16dd_x = c.mul(s16_dd.clone(), x.clone());
    let u2 = c.symm(
        s16dd_x.clone(),
        s16_ddx.clone(),
        c.assoc(s16.clone(), dd.clone(), x.clone()),
    );
    //   u3 : (16·(D·D))·x = ((D·D)·16)·x   congr (_·x) (comm 16 (D·D)).
    let dd_s16 = c.mul(dd.clone(), s16.clone());
    let dds16_x = c.mul(dd_s16.clone(), x.clone());
    let u3 = c.congr_r(
        parent,
        &x,
        s16_dd.clone(),
        dd_s16.clone(),
        c.comm(s16.clone(), dd.clone()),
    );
    //   u4 : ((D·D)·16)·x = (D·D)·(16·x)   assoc (D·D) 16 x.   [= K]
    let u4 = c.assoc(dd.clone(), s16.clone(), x.clone());

    // rhs_to_k : rhs_bound = K.
    let rhs_to_k = {
        let ch = c.trans(
            rhs_bound.clone(),
            rb_sub.clone(),
            s16_sub.clone(),
            r_m3,
            r_16,
        );
        let ch = c.trans(rhs_bound.clone(), s16_sub.clone(), s16_ddx.clone(), ch, u1);
        let ch = c.trans(rhs_bound.clone(), s16_ddx.clone(), s16dd_x.clone(), ch, u2);
        let ch = c.trans(rhs_bound.clone(), s16dd_x.clone(), dds16_x.clone(), ch, u3);
        c.trans(rhs_bound.clone(), dds16_x.clone(), k_canon.clone(), ch, u4)
    };

    // h_meas : cc·cube16 = rhs_bound   :=   a_eq ∘ symm rhs_to_k.
    let k_to_rhs = c.symm(rhs_bound.clone(), k_canon.clone(), rhs_to_k); // K = rhs_bound
    c.trans(
        cc_cube16.clone(),
        k_canon.clone(),
        rhs_bound.clone(),
        a_eq,
        k_to_rhs,
    )
}
