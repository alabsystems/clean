// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// KKL UNCONDITIONAL dichotomy — proof body (the Classical.em case split).
// `include!`d into `boolean_analysis_kkl_maxinf_uncond_build2.rs`.

impl UncondConsts {
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    /// `congrArg (fun z => z·right) h : a·right = b·right`.
    fn congr_mul_r(
        &self,
        parent: &EnvDeclBuilder,
        right: &Expr,
        a: Expr,
        b: Expr,
        h: Expr,
    ) -> Expr {
        let ff = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.u1.clone(), self.u1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, ff, h],
        )
    }
    /// `congrArg (fun z => left·z) h : left·a = left·b`.
    fn congr_mul_l(&self, parent: &EnvDeclBuilder, left: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let ff = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.u1.clone(), self.u1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, ff, h],
        )
    }
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, b, cc],
        )
    }
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.one_mul"), vec![]), [a])
    }
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.add_zero"), vec![]), [a])
    }
    fn zero_add(&self, a: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.zero_add"), vec![]), [a])
    }
    /// `Rat.add_lt_add_right a b cc (a<b) : (a+cc) < (b+cc)`.
    fn add_lt_add_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.add_lt_add_right"), vec![]),
            [a, b, cc, h],
        )
    }
}

/// The full proof body: positivity scaffolding + `Classical.em` case split.
#[allow(clippy::too_many_arguments)]
fn build_uncond_body(
    c: &UncondConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    f: &Expr,
    kcast: &Expr,
    nn: &Expr,
    p: &Expr,
    q: &Expr,
    qq: &Expr,
    two_nn: &Expr,
    concl: &Expr,
    hpos: &Expr,
    hthr: &Expr,
    h0: &Expr,
) -> Expr {
    let i_tot = c.total_influence_of(n, f);
    let var = c.variance_of(n, f);
    let delta = c.inv(q.clone()); // δ := inv Q
    let tau = c.mul(delta.clone(), delta.clone()); // τ := δ·δ

    // ── positivity scaffolding ────────────────────────────────────────────────
    let hp_pos = c.p_pos(k); // 0 < P
    let hp_nn = c.le_of_pos(p.clone(), hp_pos.clone()); // 0 ≤ P

    // 1 < Q = P+1:  add_lt_add_right 0 P 1 (0<P) : (0+1)<(P+1); subst (0+1=1).
    let h_01_lt_q = c.add_lt_add_right(
        c.rat_zero.clone(),
        p.clone(),
        c.rat_one.clone(),
        hp_pos.clone(),
    );
    let one_lt_q = {
        // motive t := t < Q.
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.rat_lt(t, q.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        // (0+1) = 1.
        let e = c.zero_add(c.rat_one.clone());
        c.subst(
            motive,
            c.add(c.rat_zero.clone(), c.rat_one.clone()),
            c.rat_one.clone(),
            e,
            h_01_lt_q,
        )
    };
    // 0 < Q via lt_of_lt_of_le 0 1 Q (0<1) (1 ≤ Q from 1<Q).
    let one_le_q = c.le_of_lt_via(parent, c.rat_one.clone(), q.clone(), one_lt_q.clone());
    let hq_pos = c.lt_of_lt_of_le(
        c.rat_zero.clone(),
        c.rat_one.clone(),
        q.clone(),
        c.zero_lt_one(),
        one_le_q,
    );
    let hq_nn = c.le_of_pos(q.clone(), hq_pos.clone()); // 0 ≤ Q
    let hq_ne = c.ne_of_pos(q.clone(), hq_pos.clone()); // Q ≠ 0
    let hd_pos = c.inv_pos(q.clone(), hq_pos.clone()); // 0 < δ
    let hd_nn = c.le_of_pos(delta.clone(), hd_pos.clone()); // 0 ≤ δ

    // δ < 1 := inv_lt_of_one_lt_mul Q 1 (0<Q) (1 < 1·Q).
    // 1 < 1·Q:  subst (1·Q = Q) backwards into (1 < Q).
    let one_mul_q = c.one_mul(q.clone()); // 1·Q = Q
    let one_lt_one_q = {
        // motive t := 1 < t.  We have one_lt_q : 1 < Q; want 1 < 1·Q. subst (Q=1·Q)?
        // Use symm(one_mul_q) : Q = 1·Q, motive t := 1 < t, on (1<Q) gives 1<1·Q.
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.rat_lt(c.rat_one.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(
            motive,
            q.clone(),
            c.mul(c.rat_one.clone(), q.clone()),
            c.symm(c.mul(c.rat_one.clone(), q.clone()), q.clone(), one_mul_q),
            one_lt_q,
        )
    };
    let hd_lt_1 = Expr::apps(
        Expr::const_(Name::from_string("Rat.inv_lt_of_one_lt_mul"), vec![]),
        [q.clone(), c.rat_one.clone(), hq_pos.clone(), one_lt_one_q],
    );
    // τ = δ·δ < 1:  δ·δ ≤ 1·δ (mul_le_right δ 1 δ (δ≤1)(0≤δ)); 1·δ = δ; δ<1.
    let hdd1 = {
        // d≤1 from d<1.
        let hd_le_1 = c.le_of_lt_via(parent, delta.clone(), c.rat_one.clone(), hd_lt_1.clone());
        // δ·δ ≤ 1·δ.
        let h_dd_le_1d = c.mul_le_right(
            delta.clone(),
            delta.clone(),
            c.rat_one.clone(),
            hd_le_1,
            hd_nn.clone(),
        );
        // 1·δ = δ.
        let e_1d = c.one_mul(delta.clone());
        // δ·δ ≤ δ  (subst RHS 1·δ → δ; motive t := δ·δ ≤ t).
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.rat_le(tau.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_dd_le_d = c.subst(
            motive,
            c.mul(c.rat_one.clone(), delta.clone()),
            delta.clone(),
            e_1d,
            h_dd_le_1d,
        );
        // δ·δ < 1  (lt_of_le_of_lt τ δ 1 (τ≤δ)(δ<1)).
        c.lt_of_le_of_lt(
            tau.clone(),
            delta.clone(),
            c.rat_one.clone(),
            h_dd_le_d,
            hd_lt_1,
        )
    };

    // ── Classical.em (∃ i, τ ≤ Inf_i) ─────────────────────────────────────────
    let large_pred = large_infl_pred(c, parent, n, f, &tau); // fun i => τ ≤ Inf_i
    let exists_large = Expr::apps(
        Expr::const_(Name::from_string("Exists"), vec![c.u1.clone()]),
        [c.fin_of(n), large_pred.clone()],
    );
    let not_exists = u_not(exists_large.clone());
    let em = Expr::apps(
        Expr::const_(Name::from_string("Classical.em"), vec![]),
        [exists_large.clone()],
    );

    // Case A: yes-branch.
    let case_a = build_case_a(
        c,
        parent,
        n,
        f,
        k,
        kcast,
        nn,
        p,
        q,
        qq,
        two_nn,
        &tau,
        &var,
        &i_tot,
        &large_pred,
        &exists_large,
        concl,
        hthr,
        h0,
        &hp_nn,
        &hq_nn,
        &hd_nn,
        &hq_pos,
    );
    // Case B: no-branch.
    let case_b = build_case_b(
        c,
        parent,
        n,
        k,
        f,
        kcast,
        &delta,
        &tau,
        &i_tot,
        &large_pred,
        &not_exists,
        concl,
        hpos,
        h0,
        &hd_nn,
        &hdd1,
        &hp_nn,
        &hq_nn,
        &hq_ne,
        &hd_pos,
        p,
        q,
    );

    u_or_elim(
        parent,
        exists_large,
        not_exists,
        concl.clone(),
        em,
        case_a,
        case_b,
    )
}

/// `fun (i : Fin n) => Rat.le τ (Influence n f i)` — the large-influence pred.
fn large_infl_pred(
    c: &UncondConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    tau: &Expr,
) -> Expr {
    let fin_n = c.fin_of(n);
    let mut d = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = d.fresh_local(fin_n.clone());
    let body = c.rat_le(tau.clone(), c.influence_of(n, f, &i));
    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

impl UncondConsts {
    /// `a ≤ b` from `h : a < b` via `And.left (Iff.mp (lt_iff_le_not_le a b) h)`.
    fn le_of_lt_via(&self, _parent: &EnvDeclBuilder, a: Expr, b: Expr, h: Expr) -> Expr {
        let le_ab = self.rat_le(a.clone(), b.clone());
        let not_le_ba = u_not(self.rat_le(b.clone(), a.clone()));
        let and_ty = u_and(le_ab.clone(), not_le_ba.clone());
        let lt_ab = self.rat_lt(a.clone(), b.clone());
        let iff = u_lt_iff(a.clone(), b.clone());
        let mp = u_iff_mp(lt_ab, and_ty, iff, h);
        u_and_left(le_ab, not_le_ba, mp)
    }
}

include!("boolean_analysis_kkl_maxinf_uncond_cases.rs");
