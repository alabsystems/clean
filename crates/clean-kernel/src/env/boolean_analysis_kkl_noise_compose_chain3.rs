// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_noise_compose_chain2.rs — the eigen leg (4),
// the regroup/smul/semigroup legs (5–7), and the top-level `compose_value` for
// `noiseDensityW_compose_third`. Split out only for the 500-line-per-file
// convention; not a standalone module.

impl ComposeConsts {
    /// Inner eigen identity at a DECODED pivot `S = hcDecode n jS`:
    ///   `Σ_z χ_S(z)·W_{1/3}(z,y) = (cube·(1/3)^{|S|})·χ_S(y)`.
    /// `ss_congr` flips the product to the eigen lemma's native order
    /// `W_{1/3}(z,y)·χ_S(z)`, then `noiseDensity_apply_chi_eigen (1/3) n jS y`
    /// closes it.
    fn eigen_inner(&self, parent: &EnvDeclBuilder, n: &Expr, js: &Expr, y: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let s = self.hc_decode(n, js);
        // flip_fn z := χ_S z·W_{1/3}(z,y)   (my order)
        let flip_fn = {
            let mut zb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let body = self.mul(self.chi_(n, &s, &z), self.dens(&self.third(), n, &z, y));
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        // native_fn z := W_{1/3}(z,y)·χ_S z   (eigen lemma's order)
        let native_fn = {
            let mut zb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let body = self.mul(self.dens(&self.third(), n, &z, y), self.chi_(n, &s, &z));
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        // hyp_flip z : χ_S z·W = W·χ_S z   (mul_comm)
        let hyp_flip = {
            let mut zb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let body = self.mul_comm(self.chi_(n, &s, &z), self.dens(&self.third(), n, &z, y));
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        let sum_flip = self.ssum(n, flip_fn.clone()); // Σ_z χ·W
        let sum_native = self.ssum(n, native_fn.clone()); // Σ_z W·χ
        let step_flip = self.ss_congr(n, &flip_fn, &native_fn, hyp_flip); // sum_flip = sum_native
        let eig = self.eigen_at(&self.third(), n, js, y); // sum_native = (cube·(1/3)^|S|)·χ_S y
        let pw = self.pow(&self.third(), &self.set_size(n, &s));
        let rhs = self.mul(self.mul(self.cube(n), pw), self.chi_(n, &s, y));
        self.trans(sum_flip, sum_native, rhs, step_flip, eig)
    }

    /// Leg 4 (E3 → E4): per DECODED pivot, eigen-collapse the z-sum. Built as a
    /// `Fin.sum_congr (2^n) Fdec Gdec hyp` whose type
    /// `Fin.sum (2^n) Fdec = Fin.sum (2^n) Gdec` δ-folds (via the reducible
    /// `subsetSum`) to `subsetSum n e3_s_fn = subsetSum n e4_s_fn`. The surrounding
    /// `trans` supplies that folded type; the kernel accepts it by def-eq.
    fn leg4(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let pp = self.pow2(n);
        let fin_p = self.fin_of(&pp);
        // Fdec jS := coeff(S)·(Σ_z χ_S z·W)   [S := hcDecode jS]   (E3 body, decoded)
        let f_dec = {
            let mut jb = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = jb.fresh_local(fin_p.clone());
            let s = self.hc_decode(n, &j);
            let coeff = self.mul(
                self.pow(&self.third(), &self.set_size(n, &s)),
                self.chi_(n, &s, x),
            );
            let body = self.mul(coeff, self.eigen_zsum(&jb, n, &s, y));
            jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p.clone(), body))
        };
        // Gdec jS := coeff(S)·((cube·(1/3)^|S|)·χ_S y)   (E4 body, decoded)
        let g_dec = {
            let mut jb = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = jb.fresh_local(fin_p.clone());
            let s = self.hc_decode(n, &j);
            let pw = self.pow(&self.third(), &self.set_size(n, &s));
            let coeff = self.mul(pw.clone(), self.chi_(n, &s, x));
            let eig = self.mul(self.mul(self.cube(n), pw), self.chi_(n, &s, y));
            let body = self.mul(coeff, eig);
            jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p.clone(), body))
        };
        // hyp jS : Fdec jS = Gdec jS  via congr (coeff·_) (eigen_inner)
        let hyp = {
            let mut jb = EnvDeclBuilder::child_of(parent);
            let (j_id, j) = jb.fresh_local(fin_p.clone());
            let s = self.hc_decode(n, &j);
            let coeff = self.mul(
                self.pow(&self.third(), &self.set_size(n, &s)),
                self.chi_(n, &s, x),
            );
            let inner = self.eigen_inner(&jb, n, &j, y);
            let pw = self.pow(&self.third(), &self.set_size(n, &s));
            let inner_lhs = self.eigen_zsum(&jb, n, &s, y);
            let inner_rhs = self.mul(self.mul(self.cube(n), pw), self.chi_(n, &s, y));
            let motive = {
                let mut e = EnvDeclBuilder::child_of(&jb);
                let (t_id, t) = e.fresh_local(self.rat.clone());
                let body = self.mul(coeff.clone(), t);
                e.finish_child(e.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
            };
            let body = self.congr_rat(inner_lhs, inner_rhs, motive, inner);
            jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p.clone(), body))
        };
        self.fsum_congr(&pp, &f_dec, &g_dec, hyp)
    }

    /// Per-S leg-5 leaf: regroup E4's `(pw·χx)·((cube·pw)·χy)` into
    /// `cube·((pw·pw)·(χx·χy))`. Pure `Rat` algebra (assoc + the
    /// `mul_mul_mul_comm`-style four-factor regroup, done by hand with
    /// `mul_assoc`/`mul_comm`).
    ///
    /// Chain (write `a:=pw, b:=χx, c:=cube, d:=χy`):
    ///   `(a·b)·((c·a)·d)`
    ///     →[congr ((a·b)·_) (assoc c a d)]    (a·b)·(c·(a·d))
    ///     →[assoc (a·b) c (a·d)]              ((a·b)·c)·(a·d)
    ///     →[congr (_·(a·d)) (assoc a b c)]    (a·(b·c))·(a·d)
    ///     →[congr ((a·_)·(a·d)) (comm b c)]   (a·(c·b))·(a·d)
    ///     →[congr (_·(a·d)) (symm assoc a c b)] ((a·c)·b)·(a·d)
    ///     →[congr (_·(a·d)) (congr (_·b) (comm a c))] ((c·a)·b)·(a·d)
    ///     →[congr (_·(a·d)) (assoc c a b)]    (c·(a·b))·(a·d)
    ///     →[assoc c (a·b) (a·d)]              c·((a·b)·(a·d))
    ///     →[congr (c·_) (mmmc a b a d)]       c·((a·a)·(b·d))
    /// where `mmc a b a d : (a·b)·(a·d) = (a·a)·(b·d)` is `Rat.mul_mul_mul_comm`.
    fn leg5_leaf(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr, s: &Expr) -> Expr {
        let a = self.pow(&self.third(), &self.set_size(n, s)); // pw
        let b = self.chi_(n, s, x); // χx
        let cc = self.cube(n); // cube
        let d = self.chi_(n, s, y); // χy

        let mul = |u: Expr, v: Expr| self.mul(u, v);
        let rat = self.rat.clone();
        // motive built as a CHILD of `parent` so outer FVars (in `a,b,cc,d`) stay
        // scoped; `hole` fills the `t`-slot.
        let mk_motive = |hole: &dyn Fn(Expr) -> Expr| -> Expr {
            let mut e = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = e.fresh_local(rat.clone());
            let body = hole(t);
            e.finish_child(e.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
        };

        let ab = mul(a.clone(), b.clone());
        let ca = mul(cc.clone(), a.clone());
        let ad = mul(a.clone(), d.clone());
        let bc = mul(b.clone(), cc.clone());
        let cb = mul(cc.clone(), b.clone());

        // n0 = (a·b)·((c·a)·d)
        let n0 = mul(ab.clone(), mul(ca.clone(), d.clone()));
        // n1 = (a·b)·(c·(a·d))
        let n1 = mul(ab.clone(), mul(cc.clone(), ad.clone()));
        // n2 = ((a·b)·c)·(a·d)
        let n2 = mul(mul(ab.clone(), cc.clone()), ad.clone());
        // n3 = (a·(b·c))·(a·d)
        let n3 = mul(mul(a.clone(), bc.clone()), ad.clone());
        // n4 = (a·(c·b))·(a·d)
        let n4 = mul(mul(a.clone(), cb.clone()), ad.clone());
        // n5 = ((a·c)·b)·(a·d)
        let n5 = mul(mul(mul(a.clone(), cc.clone()), b.clone()), ad.clone());
        // n6 = ((c·a)·b)·(a·d)
        let n6 = mul(mul(mul(cc.clone(), a.clone()), b.clone()), ad.clone());
        // n7 = (c·(a·b))·(a·d)
        let n7 = mul(mul(cc.clone(), ab.clone()), ad.clone());
        // n8 = c·((a·b)·(a·d))
        let n8 = mul(cc.clone(), mul(ab.clone(), ad.clone()));
        // n9 = c·((a·a)·(b·d))   = target
        let n9 = mul(
            cc.clone(),
            mul(mul(a.clone(), a.clone()), mul(b.clone(), d.clone())),
        );

        // s1 : n0=n1  congr ((a·b)·_) (assoc c a d : (c·a)·d = c·(a·d))
        let s1 = self.congr_rat(
            mul(ca.clone(), d.clone()),
            mul(cc.clone(), ad.clone()),
            mk_motive(&|t| mul(ab.clone(), t)),
            self.mul_assoc(cc.clone(), a.clone(), d.clone()),
        );
        // s2 : n1=n2  symm (assoc (a·b) c (a·d) : ((a·b)·c)·(a·d) = (a·b)·(c·(a·d)))
        let s2 = self.symm(
            n2.clone(),
            n1.clone(),
            self.mul_assoc(ab.clone(), cc.clone(), ad.clone()),
        );
        // s3 : n2=n3  congr (_·(a·d)) (assoc a b c : (a·b)·c = a·(b·c))
        let s3 = self.congr_rat(
            mul(ab.clone(), cc.clone()),
            mul(a.clone(), bc.clone()),
            mk_motive(&|t| mul(t, ad.clone())),
            self.mul_assoc(a.clone(), b.clone(), cc.clone()),
        );
        // s4 : n3=n4  congr (_·(a·d)) (congr (a·_) (comm b c : b·c = c·b))
        let inner_bc = self.congr_rat(
            bc.clone(),
            cb.clone(),
            mk_motive(&|t| mul(a.clone(), t)),
            self.mul_comm(b.clone(), cc.clone()),
        );
        let s4 = self.congr_rat(
            mul(a.clone(), bc.clone()),
            mul(a.clone(), cb.clone()),
            mk_motive(&|t| mul(t, ad.clone())),
            inner_bc,
        );
        // s5 : n4=n5  congr (_·(a·d)) (symm (assoc a c b : (a·c)·b = a·(c·b)))
        let inner_acb = self.symm(
            mul(mul(a.clone(), cc.clone()), b.clone()),
            mul(a.clone(), cb.clone()),
            self.mul_assoc(a.clone(), cc.clone(), b.clone()),
        );
        let s5 = self.congr_rat(
            mul(a.clone(), cb.clone()),
            mul(mul(a.clone(), cc.clone()), b.clone()),
            mk_motive(&|t| mul(t, ad.clone())),
            inner_acb,
        );
        // s6 : n5=n6  congr (_·(a·d)) (congr (_·b) (comm a c : a·c = c·a))
        let inner_ac = self.congr_rat(
            mul(a.clone(), cc.clone()),
            mul(cc.clone(), a.clone()),
            mk_motive(&|t| mul(t, b.clone())),
            self.mul_comm(a.clone(), cc.clone()),
        );
        let s6 = self.congr_rat(
            mul(mul(a.clone(), cc.clone()), b.clone()),
            mul(mul(cc.clone(), a.clone()), b.clone()),
            mk_motive(&|t| mul(t, ad.clone())),
            inner_ac,
        );
        // s7 : n6=n7  congr (_·(a·d)) (assoc c a b : (c·a)·b = c·(a·b))
        let s7 = self.congr_rat(
            mul(mul(cc.clone(), a.clone()), b.clone()),
            mul(cc.clone(), ab.clone()),
            mk_motive(&|t| mul(t, ad.clone())),
            self.mul_assoc(cc.clone(), a.clone(), b.clone()),
        );
        // s8 : n7=n8  assoc c (a·b) (a·d) : (c·(a·b))·(a·d) = c·((a·b)·(a·d))
        let s8 = self.mul_assoc(cc.clone(), ab.clone(), ad.clone());
        // s9 : n8=n9  congr (c·_) (mmmc a b a d : (a·b)·(a·d) = (a·a)·(b·d))
        let mmmc = Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            [a.clone(), b.clone(), a.clone(), d.clone()],
        );
        let s9 = self.congr_rat(
            mul(ab.clone(), ad.clone()),
            mul(mul(a.clone(), a.clone()), mul(b.clone(), d.clone())),
            mk_motive(&|t| mul(cc.clone(), t)),
            mmmc,
        );

        let t1 = self.trans(n0.clone(), n1.clone(), n2.clone(), s1, s2);
        let t2 = self.trans(n0.clone(), n2.clone(), n3.clone(), t1, s3);
        let t3 = self.trans(n0.clone(), n3.clone(), n4.clone(), t2, s4);
        let t4 = self.trans(n0.clone(), n4.clone(), n5.clone(), t3, s5);
        let t5 = self.trans(n0.clone(), n5.clone(), n6.clone(), t4, s6);
        let t6 = self.trans(n0.clone(), n6.clone(), n7.clone(), t5, s7);
        let t7 = self.trans(n0.clone(), n7.clone(), n8.clone(), t6, s8);
        self.trans(n0, n8, n9, t7, s9)
    }

    /// Leg 5 (E4 → E5): `subsetSum_congr` over `leg5_leaf` per S.
    fn leg5(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let hyp = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let body = self.leg5_leaf(&sb, n, x, y, &s);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let e4 = self.e4_s_fn(parent, n, x, y);
        let e5 = self.e5_s_fn(parent, n, x, y);
        self.ss_congr(n, &e4, &e5, hyp)
    }

    /// Leg 6 (E5 → E6'): `subsetSum_smul n cube e6_inner_s_fn` —
    /// `Σ_S cube·(…) = cube·Σ_S(…)`.
    fn leg6(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let cube = self.cube(n);
        let inner = self.e6_inner_s_fn(parent, n, x, y);
        self.ss_smul(n, &cube, &inner)
    }

    /// Per-S leg-7 leaf: `(pw·pw)·(χx·χy) = (1/9)^{|S|}·(χx·χy)` via
    /// `congr (_·(χx·χy)) (noise_semigroup_third |S|)`.
    fn leg7_leaf(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr, s: &Expr) -> Expr {
        let pw = self.pow(&self.third(), &self.set_size(n, s));
        let wsq = self.mul(pw.clone(), pw.clone());
        let w9 = self.pow(&self.ninth(), &self.set_size(n, s));
        let chis = self.mul(self.chi_(n, s, x), self.chi_(n, s, y));
        let motive = self.mul_right_motive(parent, &chis);
        // semigroup at k := |S| = setSizeNat n S.
        let sg = self.semigroup_at(&self.set_size(n, s));
        self.congr_rat(wsq, w9, motive, sg)
    }

    /// Leg 7 (E6' inner → W_{1/9}): `congr (cube·_)` of `subsetSum_congr` over
    /// `leg7_leaf` per S. The folded RHS `cube·subsetSum n (w9_body_fn)` is def-eq
    /// to `cube·W_{1/9}(x,y)` (the stated RHS) by reducibility of `noiseDensityW`.
    fn leg7(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let cube = self.cube(n);
        let e6_inner = self.e6_inner_s_fn(parent, n, x, y);
        let w9_inner = self.w9_body_fn(parent, n, x, y);
        let hyp = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let body = self.leg7_leaf(&sb, n, x, y, &s);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let inner_congr = self.ss_congr(n, &e6_inner, &w9_inner, hyp); // Σ(wsq·χχ) = Σ(w9·χχ)
        let sum_e6 = self.ssum(n, e6_inner);
        let sum_w9 = self.ssum(n, w9_inner);
        let motive = {
            let mut e = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = e.fresh_local(self.rat.clone());
            let body = self.mul(cube.clone(), t);
            e.finish_child(e.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr_rat(sum_e6, sum_w9, motive, inner_congr)
    }
}

/// `λ n x y => Eq.trans … (the seven-leg chain E0=E1=…=E7≡RHS)`.
fn compose_value(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());

    // endpoints (subsetSum n of the integrands).
    let e0 = c.ssum(&n, c.e0_z_fn(&b, &n, &x, &y));
    let e1 = c.ssum(&n, c.e1_z_fn(&b, &n, &x, &y));
    let e2 = c.ssum(&n, c.e2_s_fn(&b, &n, &x, &y));
    let e3 = c.ssum(&n, c.e3_s_fn(&b, &n, &x, &y));
    let e4 = c.ssum(&n, c.e4_s_fn(&b, &n, &x, &y));
    let e5 = c.ssum(&n, c.e5_s_fn(&b, &n, &x, &y));
    // E6' = cube · Σ_S (e6_inner) ; final RHS = cube · W_{1/9}(x,y).
    let cube = c.cube(&n);
    let e6 = c.mul(cube.clone(), c.ssum(&n, c.e6_inner_s_fn(&b, &n, &x, &y)));
    let rhs = c.mul(cube.clone(), c.dens(&c.ninth(), &n, &x, &y));

    let l1 = c.leg1(&b, &n, &x, &y);
    let l2 = c.leg2(&b, &n, &x, &y);
    let l3 = c.leg3(&b, &n, &x, &y);
    let l4 = c.leg4(&b, &n, &x, &y);
    let l5 = c.leg5(&b, &n, &x, &y);
    let l6 = c.leg6(&b, &n, &x, &y);
    let l7 = c.leg7(&b, &n, &x, &y);

    // chain e0 = e1 = e2 = e3 = e4 = e5 = e6 = rhs.
    let t1 = c.trans(e0.clone(), e1.clone(), e2.clone(), l1, l2);
    let t2 = c.trans(e0.clone(), e2.clone(), e3.clone(), t1, l3);
    let t3 = c.trans(e0.clone(), e3.clone(), e4.clone(), t2, l4);
    let t4 = c.trans(e0.clone(), e4.clone(), e5.clone(), t3, l5);
    let t5 = c.trans(e0.clone(), e5.clone(), e6.clone(), t4, l6);
    let proof = c.trans(e0, e6, rhs, t5, l7);

    let val = b.mk_lam(y_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}
