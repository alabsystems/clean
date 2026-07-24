// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_influence_chain.rs — the per-`S` integrand
// regroupings and the `subsetSum`-level leg statements/proofs for the
// `influence_fourier` assembly. Split out for the 500-line-per-file convention.

// ════════════ Leg: subsetSum_flip_spectral_split ════════════
//
// At a fixed sign point `x`:
//   Σ_S ((2·ind(S i))·A_S)·χ_S(x)
//     = (Σ_S A_S·χ_S(x)) − (Σ_S A_S·χ_S(hcFlip n x i)).
//
// Proof: per-`S` integrand identity (under `subsetSum_congr`)
//   ((2·ind(S i))·A_S)·χ_S(x) = (A_S·χ_S(x)) − (A_S·χ_S(hcFlip n x i)),
// then `subsetSum_sub` splits the cube sum.

impl InflConsts {
    /// Modified-derivative coefficient `a_fn := fun S => (2·ind(S i))·A_S` as a
    /// standalone `HCPoint n → Rat` (the `a` fed to `subsetSum_xside_core`).
    fn a_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, i: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let body = self.mul(
            self.mul(self.rat_two(), self.ind_(Expr::app(s.clone(), i.clone()))),
            self.amp(&sb, n, b, &s),
        );
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// LHS `S`-integrand `fun S => ((2·ind(S i))·A_S)·χ_S(x)`.
    fn split_lhs_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        b: &Expr,
        x: &Expr,
        i: &Expr,
    ) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let coeff = self.mul(
            self.mul(self.rat_two(), self.ind_(Expr::app(s.clone(), i.clone()))),
            self.amp(&sb, n, b, &s),
        );
        let body = self.mul(coeff, self.chi_(n, &s, x));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => A_S·χ_S(x)`.
    fn amp_chi_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, x: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let body = self.mul(self.amp(&sb, n, b, &s), self.chi_(n, &s, x));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => A_S·χ_S(hcFlip n x i)`.
    fn amp_chi_flip_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        b: &Expr,
        x: &Expr,
        i: &Expr,
    ) -> Expr {
        let xf = self.hc_flip_(n, x, i);
        self.amp_chi_fn(parent, n, b, &xf)
    }

    /// Per-`S` integrand identity:
    ///   ((2·is)·k)·c = (k·c) − (k·cf)
    /// where `is = ind(S i)`, `k = A_S`, `c = χ_S(x)`, `cf = χ_S(hcFlip n x i)`.
    fn per_s_split(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        b: &Expr,
        s: &Expr,
        x: &Expr,
        i: &Expr,
    ) -> Expr {
        let si = Expr::app(s.clone(), i.clone());
        let is_ = self.ind_(si.clone());
        let fs = self.flip_sign_(si);
        let k = self.amp(parent, n, b, s);
        let c = self.chi_(n, s, x);
        let cf = self.chi_(n, s, &self.hc_flip_(n, x, i));
        let two = self.rat_two();
        let one = self.rat_one.clone();

        let two_is = self.mul(two.clone(), is_.clone());
        let one_sub_fs = self.sub(one.clone(), fs.clone());
        let m = self.mul(k.clone(), c.clone()); // k·c

        // s0 : ((2·is)·k)·c
        let s0 = self.mul(self.mul(two_is.clone(), k.clone()), c.clone());

        // Step A: ((2·is)·k)·c = ((1−fs)·k)·c.
        //   absorb : (1−fs) = 2·is ; symm → 2·is = 1−fs ;
        //   congrArg(·k) → (2·is)·k = (1−fs)·k ; congrArg(·c) lift.
        let absorb = Expr::apps(
            self.flip_coeff_absorb.clone(),
            [Expr::app(s.clone(), i.clone())],
        );
        let absorb_sym = self.symm(one_sub_fs.clone(), two_is.clone(), absorb);
        let coef_eq =
            self.mul_right_congr(parent, &k, two_is.clone(), one_sub_fs.clone(), absorb_sym);
        let s1_l = self.mul(self.mul(one_sub_fs.clone(), k.clone()), c.clone());
        let step_a = self.mul_right_congr(
            parent,
            &c,
            self.mul(two_is.clone(), k.clone()),
            self.mul(one_sub_fs.clone(), k.clone()),
            coef_eq,
        );

        // Step B: ((1−fs)·k)·c = (1−fs)·(k·c)   via Rat.mul_assoc (1−fs) k c.
        let step_b = Expr::apps(
            self.rat_mul_assoc.clone(),
            [one_sub_fs.clone(), k.clone(), c.clone()],
        );
        let s2 = self.mul(one_sub_fs.clone(), m.clone()); // (1−fs)·(k·c)

        // Step C: (1−fs)·m = m − fs·m.
        //   c1 : (1−fs)·m = m·(1−fs)       (mul_comm)
        //   c2 : m·(1−fs) = m·1 − m·fs     (mul_sub m 1 fs)
        //   c3 : m·1 − m·fs = m − m·fs     (congrArg(·−(m·fs)) (mul_one m))
        //   c4 : m − m·fs = m − fs·m       (congrArg(m − ·) (mul_comm m fs))
        let m_one_sub_fs = self.mul(m.clone(), one_sub_fs.clone());
        let c1 = Expr::apps(self.rat_mul_comm.clone(), [one_sub_fs.clone(), m.clone()]);
        let c2 = Expr::apps(
            self.rat_mul_sub.clone(),
            [m.clone(), one.clone(), fs.clone()],
        );
        let m_one = self.mul(m.clone(), one.clone());
        let m_fs = self.mul(m.clone(), fs.clone());
        let fs_m = self.mul(fs.clone(), m.clone());
        // c3: rewrite m·1 → m inside (m·1 − m·fs)
        let mul_one_m = Expr::apps(self.rat_mul_one.clone(), [m.clone()]); // m·1 = m
        let c3 = self.sub_left_congr(parent, &m_fs, m_one.clone(), m.clone(), mul_one_m);
        // c4: rewrite m·fs → fs·m inside (m − m·fs)
        let comm_m_fs = Expr::apps(self.rat_mul_comm.clone(), [m.clone(), fs.clone()]); // m·fs = fs·m
        let c4 = self.sub_right_congr(parent, &m, m_fs.clone(), fs_m.clone(), comm_m_fs);

        let sub_m1_mfs = self.sub(m_one.clone(), m_fs.clone());
        let sub_m_mfs = self.sub(m.clone(), m_fs.clone());
        let sub_m_fsm = self.sub(m.clone(), fs_m.clone());
        // chain step C: (1−fs)·m = m·(1−fs) = m·1−m·fs = m−m·fs = m−fs·m
        let cc1 = self.trans(s2.clone(), m_one_sub_fs.clone(), sub_m1_mfs.clone(), c1, c2);
        let cc2 = self.trans(s2.clone(), sub_m1_mfs.clone(), sub_m_mfs.clone(), cc1, c3);
        let step_c = self.trans(s2.clone(), sub_m_mfs.clone(), sub_m_fsm.clone(), cc2, c4);

        // Step D: m − fs·m = (k·c) − (k·cf).
        //   fs·m = fs·(k·c) = k·(fs·c) = k·cf   (assoc/comm + chi_flip_spectral symm).
        //   d1 : fs·(k·c) = (fs·k)·c        symm (mul_assoc fs k c)
        //   d2 : (fs·k)·c = (k·fs)·c        congrArg(·c) (mul_comm fs k)
        //   d3 : (k·fs)·c = k·(fs·c)        mul_assoc k fs c
        //   d4 : k·(fs·c) = k·cf            congrArg(k·) (symm chi_flip_spectral)
        let fs_k = self.mul(fs.clone(), k.clone());
        let k_fs = self.mul(k.clone(), fs.clone());
        let fs_c = self.mul(fs.clone(), c.clone());
        let fsk_c = self.mul(fs_k.clone(), c.clone());
        let kfs_c = self.mul(k_fs.clone(), c.clone());
        let k_fsc = self.mul(k.clone(), fs_c.clone());
        let k_cf = self.mul(k.clone(), cf.clone());
        let assoc_fkc = Expr::apps(
            self.rat_mul_assoc.clone(),
            [fs.clone(), k.clone(), c.clone()],
        ); // (fs·k)·c = fs·(k·c)
        let d1 = self.symm(fsk_c.clone(), fs_m.clone(), assoc_fkc);
        let comm_fs_k = Expr::apps(self.rat_mul_comm.clone(), [fs.clone(), k.clone()]); // fs·k = k·fs
        let d2 = self.mul_right_congr(parent, &c, fs_k.clone(), k_fs.clone(), comm_fs_k);
        let d3 = Expr::apps(
            self.rat_mul_assoc.clone(),
            [k.clone(), fs.clone(), c.clone()],
        ); // (k·fs)·c = k·(fs·c)
           // chi_flip_spectral n S x i : χ_S(hcFlip n x i) = fs·χ_S(x) = fs·c
        let cfs = Expr::apps(
            self.chi_flip_spectral.clone(),
            [n.clone(), s.clone(), x.clone(), i.clone()],
        );
        let cfs_sym = self.symm(cf.clone(), fs_c.clone(), cfs); // fs·c = cf
        let d4 = self.mul_left_congr(parent, &k, fs_c.clone(), cf.clone(), cfs_sym);
        // fs·m = (fs·k)·c = (k·fs)·c = k·(fs·c) = k·cf
        let dd1 = self.trans(fs_m.clone(), fsk_c.clone(), kfs_c.clone(), d1, d2);
        let dd2 = self.trans(fs_m.clone(), kfs_c.clone(), k_fsc.clone(), dd1, d3);
        let fsm_eq_kcf = self.trans(fs_m.clone(), k_fsc.clone(), k_cf.clone(), dd2, d4); // fs·m = k·cf
                                                                                         // congrArg (m − ·) : (m − fs·m) = (m − k·cf)
        let step_d = self.sub_right_congr(parent, &m, fs_m.clone(), k_cf.clone(), fsm_eq_kcf);

        // Assemble: s0 = ((1−fs)·k)·c = (1−fs)·m = (m − fs·m) = (m − k·cf).
        let final_rhs = self.sub(m.clone(), k_cf.clone());
        let t1 = self.trans(s0.clone(), s1_l.clone(), s2.clone(), step_a, step_b);
        let t2 = self.trans(s0.clone(), s2.clone(), sub_m_fsm.clone(), t1, step_c);
        self.trans(s0, sub_m_fsm, final_rhs, t2, step_d)
    }

    /// `congrArg (fun z => z − right) h : a − right = bb − right`.
    fn sub_left_congr(
        &self,
        parent: &EnvDeclBuilder,
        right: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.sub(z, right.clone());
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }
    /// `congrArg (fun z => left − z) h : left − a = left − bb`.
    fn sub_right_congr(
        &self,
        parent: &EnvDeclBuilder,
        left: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.sub(left.clone(), z);
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }
}

fn flip_spectral_split_type(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let lhs = c.ssum(&n, c.split_lhs_fn(&b, &n, &bf, &x, &i));
    let rhs = c.sub(
        c.ssum(&n, c.amp_chi_fn(&b, &n, &bf, &x)),
        c.ssum(&n, c.amp_chi_flip_fn(&b, &n, &bf, &x, &i)),
    );
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(x_id, BinderInfo::Default, hcp, e);
    let e = b.mk_pi(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn flip_spectral_split_value(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    // after_fn : fun S => (A_S·χ_S(x)) − (A_S·χ_S(hcFlip n x i)).
    let after_fn = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let k = c.amp(&sb, &n, &bf, &s);
        let cc = c.chi_(&n, &s, &x);
        let cf = c.chi_(&n, &s, &c.hc_flip_(&n, &x, &i));
        let body = c.sub(c.mul(k.clone(), cc), c.mul(k, cf));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };

    // h_congr : ∀ S, ((2·is)·A_S)·χ_S(x) = (A_S·χ_S(x)) − (A_S·χ_S(flip))
    let h_congr = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let pf = c.per_s_split(&sb, &n, &bf, &s, &x, &i);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), pf))
    };

    // leg1 : Σ_S lhs = Σ_S after   (subsetSum_congr).
    let leg1 = Expr::apps(
        c.subset_sum_congr.clone(),
        [
            n.clone(),
            c.split_lhs_fn(&b, &n, &bf, &x, &i),
            after_fn,
            h_congr,
        ],
    );

    // leg2 : Σ_S after = (Σ_S A_S·χ_S(x)) − (Σ_S A_S·χ_S(flip))   (subsetSum_sub).
    let leg2 = Expr::apps(
        c.subset_sum_sub.clone(),
        [
            n.clone(),
            c.amp_chi_fn(&b, &n, &bf, &x),
            c.amp_chi_flip_fn(&b, &n, &bf, &x, &i),
        ],
    );

    let e0 = c.ssum(&n, c.split_lhs_fn(&b, &n, &bf, &x, &i));
    let e1 = c.ssum(&n, after_fn_clone(c, &b, &n, &bf, &x, &i));
    let rhs = c.sub(
        c.ssum(&n, c.amp_chi_fn(&b, &n, &bf, &x)),
        c.ssum(&n, c.amp_chi_flip_fn(&b, &n, &bf, &x, &i)),
    );
    let proof = c.trans(e0, e1, rhs, leg1, leg2);

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(x_id, BinderInfo::Default, hcp, e);
    let e = b.mk_lam(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// Rebuild `after_fn` (needed twice: once consumed by subsetSum_congr, once as
/// the e1 midpoint of the Eq.trans). Mirrors the closure in the value builder.
fn after_fn_clone(
    c: &InflConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    bf: &Expr,
    x: &Expr,
    i: &Expr,
) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = sb.fresh_local(hcp.clone());
    let k = c.amp(&sb, n, bf, &s);
    let cc = c.chi_(n, &s, x);
    let cf = c.chi_(n, &s, &c.hc_flip_(n, x, i));
    let body = c.sub(c.mul(k.clone(), cc), c.mul(k, cf));
    sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

// ════════════ Leg: subsetSum_flip_diff_decoded ════════════
//
// At a decoded point x = hcDecode n jx:
//   Σ_S ((2·ind(S i))·A_S)·χ_S(x)
//     = (2^n)·(b(x) − b(hcFlip n x i)).
//
// Combines `subsetSum_flip_spectral_split` (the gate-sum split) with the two
// inversions: `subsetSum_inversion_core` at jx and
// `subsetSum_inversion_core_flip` at (i, jx), then factors 2^n via Rat.mul_sub.

impl InflConsts {
    /// `subsetSum_inversion_core n b jx : Σ_S A_S·χ_S(hcDecode n jx) = (2^n)·b(hcDecode n jx)`.
    fn inv_core(&self, n: &Expr, b: &Expr, jx: &Expr) -> Expr {
        Expr::apps(
            self.inversion_core.clone(),
            [n.clone(), b.clone(), jx.clone()],
        )
    }
    /// `subsetSum_inversion_core_flip n b i jx :
    ///   Σ_S A_S·χ_S(hcFlip n (hcDecode n jx) i) = (2^n)·b(hcFlip n (hcDecode n jx) i)`.
    fn inv_core_flip(&self, n: &Expr, b: &Expr, i: &Expr, jx: &Expr) -> Expr {
        Expr::apps(
            self.inversion_core_flip.clone(),
            [n.clone(), b.clone(), i.clone(), jx.clone()],
        )
    }
}

fn flip_diff_decoded_type(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));
    let (jx_id, jx) = b.fresh_local(c.fin_of(&c.pow2(&n)));

    let x = c.hc_decode_(&n, &jx);
    let xf = c.hc_flip_(&n, &x, &i);
    let lhs = c.ssum(&n, c.split_lhs_fn(&b, &n, &bf, &x, &i));
    let diff = c.sub(Expr::app(bf.clone(), x.clone()), Expr::app(bf.clone(), xf));
    let rhs = c.mul(c.cube(&n), diff);
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(jx_id, BinderInfo::Default, c.fin_of(&c.pow2(&n)), concl);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), e);
    let e = b.mk_pi(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn flip_diff_decoded_value(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));
    let (jx_id, jx) = b.fresh_local(c.fin_of(&c.pow2(&n)));

    let x = c.hc_decode_(&n, &jx);
    let xf = c.hc_flip_(&n, &x, &i);

    // e0 := Σ_S ((2·is)·A_S)·χ_S(x).
    let e0 = c.ssum(&n, c.split_lhs_fn(&b, &n, &bf, &x, &i));
    // t1 := Σ_S A_S·χ_S(x) ; t2 := Σ_S A_S·χ_S(xf).
    let t1 = c.ssum(&n, c.amp_chi_fn(&b, &n, &bf, &x));
    let t2 = c.ssum(&n, c.amp_chi_flip_fn(&b, &n, &bf, &x, &i));
    let bx = Expr::app(bf.clone(), x.clone());
    let bxf = Expr::app(bf.clone(), xf.clone());
    let cube_bx = c.mul(c.cube(&n), bx.clone());
    let cube_bxf = c.mul(c.cube(&n), bxf.clone());

    // leg_split : e0 = t1 − t2.
    let leg_split = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_flip_spectral_split"),
            vec![],
        ),
        [n.clone(), bf.clone(), x.clone(), i.clone()],
    );
    // inv1 : t1 = (2^n)·b(x) ; inv2 : t2 = (2^n)·b(xf).
    let inv1 = c.inv_core(&n, &bf, &jx);
    let inv2 = c.inv_core_flip(&n, &bf, &i, &jx);

    // leg_sub1 : (t1 − t2) = (cube·bx − t2)   congrArg(·−t2) inv1.
    let leg_sub1 = c.sub_left_congr(&b, &t2, t1.clone(), cube_bx.clone(), inv1);
    // leg_sub2 : (cube·bx − t2) = (cube·bx − cube·bxf)  congrArg(cube·bx − ·) inv2.
    let leg_sub2 = c.sub_right_congr(&b, &cube_bx, t2.clone(), cube_bxf.clone(), inv2);
    // leg_factor : (cube·bx − cube·bxf) = cube·(bx − bxf)   symm (Rat.mul_sub cube bx bxf).
    let mul_sub = Expr::apps(c.rat_mul_sub.clone(), [c.cube(&n), bx.clone(), bxf.clone()]);
    let diff = c.sub(bx.clone(), bxf.clone());
    let cube_diff = c.mul(c.cube(&n), diff.clone());
    let sub_terms = c.sub(cube_bx.clone(), cube_bxf.clone());
    let leg_factor = c.symm(cube_diff.clone(), sub_terms.clone(), mul_sub);

    // chain: e0 = (t1−t2) = (cube·bx − t2) = (cube·bx − cube·bxf) = cube·(bx − bxf).
    let t1_minus_t2 = c.sub(t1.clone(), t2.clone());
    let mid1 = c.sub(cube_bx.clone(), t2.clone());
    let p1 = c.trans(
        e0.clone(),
        t1_minus_t2.clone(),
        mid1.clone(),
        leg_split,
        leg_sub1,
    );
    let p2 = c.trans(e0.clone(), mid1.clone(), sub_terms.clone(), p1, leg_sub2);
    let proof = c.trans(e0, sub_terms, cube_diff, p2, leg_factor);

    let e = b.mk_lam(jx_id, BinderInfo::Default, c.fin_of(&c.pow2(&n)), proof);
    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), e);
    let e = b.mk_lam(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_flip_diff_decoded` — at a decoded point
    /// `x = hcDecode n jx`, the modified-derivative coefficient sum equals the
    /// scaled flip difference:
    ///   Σ_S ((2·ind(S i))·A_S)·χ_S(x) = (2^n)·(b(x) − b(hcFlip n x i)),
    /// where `A_S = subsetSum n (fun y => b(y)·χ_S(y))`. Combines
    /// `subsetSum_flip_spectral_split` with the two Fourier inversions
    /// (`subsetSum_inversion_core` + `subsetSum_inversion_core_flip`).
    /// Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_subset_sum_flip_diff_decoded(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_flip_diff_decoded");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum_flip_spectral_split()?;
        self.register_subset_sum_inversion_core_theorem()?;
        self.register_hcflip_decode_roundtrip()?; // registers inversion_core_flip
        self.init_nn_verify_rat_ordering()?; // Rat.mul_sub

        // Re-check: `init_boolean_analysis` (above) may re-enter the full
        // influence chain and register this name already.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = InflConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: flip_diff_decoded_type(&c),
            value: flip_diff_decoded_value(&c),
        })
    }

    /// Register `BoolAnalysis.subsetSum_flip_spectral_split` — at a fixed sign
    /// point `x`, the modified-derivative coefficient sum splits as a flip
    /// difference:
    ///   Σ_S ((2·ind(S i))·A_S)·χ_S(x)
    ///     = (Σ_S A_S·χ_S(x)) − (Σ_S A_S·χ_S(hcFlip n x i)),
    /// where `A_S = subsetSum n (fun y => b(y)·χ_S(y))`. Kernel-checked,
    /// constructive. Idempotent.
    pub(crate) fn register_subset_sum_flip_spectral_split(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_flip_spectral_split");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_sub_theorem()?;
        self.register_flip_coeff_absorb()?;
        self.register_chi_flip_spectral()?;
        self.register_flip_sign()?;
        self.init_rat_field_inst()?; // Rat.mul_assoc/comm/one
        self.init_nn_verify_rat_ordering()?; // Rat.mul_sub

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = InflConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: flip_spectral_split_type(&c),
            value: flip_spectral_split_value(&c),
        })
    }
}

#[cfg(test)]
mod influence_chain_tests {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_subset_sum_flip_spectral_split_constructive() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_flip_spectral_split()
            .expect("register flip_spectral_split");
        env.register_subset_sum_flip_spectral_split()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.subsetSum_flip_spectral_split");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(name.clone(), vec![]))
            .expect("flip_spectral_split should type-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "flip_spectral_split closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }

    #[test]
    fn test_subset_sum_flip_diff_decoded_constructive() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_flip_diff_decoded()
            .expect("register flip_diff_decoded");
        env.register_subset_sum_flip_diff_decoded()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.subsetSum_flip_diff_decoded");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(name.clone(), vec![]))
            .expect("flip_diff_decoded should type-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "flip_diff_decoded closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
