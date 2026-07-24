// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by ..._rung3b_collapse.rs — the top-level `parseval_chain`.

impl CoreConsts {
    /// `F1 S x = subsetSum n (fun y => g S x · g S y)` — the legB swap kernel,
    /// as a bundle `HCPoint n → HCPoint n → Rat`.
    fn f1_bundle(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let inner = {
            let mut xb = EnvDeclBuilder::child_of(&sb);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let y_sum = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let body = self.mul(self.g(n, a, &s, &x), self.g(n, a, &s, &y));
                let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
                self.ssum(n, f)
            };
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), y_sum))
        };
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, inner))
    }
}

/// `fun (jx : Fin P) => g (hcDecode n jx)` — explicit `subsetSum`↔`Fin.sum`
/// bridge integrand for the outer index in legE.
fn dec_outer(c: &CoreConsts, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_p = c.fin_of(&c.pow2(n));
    let (jx_id, jx) = b.fresh_local(fin_p.clone());
    let body = Expr::app(g.clone(), c.hc_decode(n, &jx));
    b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, fin_p, body))
}

fn parseval_chain(c: &CoreConsts, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
    let hcp = c.hcpoint_of(n);

    // endpoint expressions (all subsetSum n (·_fn)).
    let e0 = c.ssum(n, c.lhs_s_fn(parent, n, a));
    let e1 = c.ssum(n, c.e1_s_fn(parent, n, a));
    let e2 = c.ssum(n, c.e2_x_fn(parent, n, a));
    let e3 = c.ssum(n, c.e3_x_fn(parent, n, a));
    let e4 = c.ssum(n, c.e4_x_fn(parent, n, a));
    let e5 = c.ssum(n, c.e5_x_fn(parent, n, a));
    let rhs = c.mul(c.cube(n), c.ssum(n, c.a_sq_fn(parent, n, a)));

    // legA : e0 = e1   (subsetSum_sq_to_double n g_bundle).
    let leg_a = Expr::apps(
        c.subset_sum_sq_to_double.clone(),
        [n.clone(), c.g_bundle(parent, n, a)],
    );

    // legB : e1 = e2   (subsetSum_swap n F1).
    let leg_b = Expr::apps(
        c.subset_sum_swap.clone(),
        [n.clone(), c.f1_bundle(parent, n, a)],
    );

    // legC : e2 = e3   (subsetSum_congr over x of per-x subsetSum_swap F2x).
    let leg_c = {
        let h = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            // F2x S y = g S x · g S y
            let f2x = {
                let mut sb = EnvDeclBuilder::child_of(&xb);
                let (s_id, s) = sb.fresh_local(hcp.clone());
                let inner = {
                    let mut yb = EnvDeclBuilder::child_of(&sb);
                    let (y_id, y) = yb.fresh_local(hcp.clone());
                    let body = c.mul(c.g(n, a, &s, &x), c.g(n, a, &s, &y));
                    yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
                };
                sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), inner))
            };
            let swap = Expr::apps(c.subset_sum_swap.clone(), [n.clone(), f2x]);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), swap))
        };
        Expr::apps(
            c.subset_sum_congr.clone(),
            [
                n.clone(),
                c.e2_x_fn(parent, n, a),
                c.e3_x_fn(parent, n, a),
                h,
            ],
        )
    };

    // legD : e3 = e4   (subsetSum_congr over x of subsetSum_congr over y leg_d_xy).
    let leg_d = {
        let h = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            // per-x: subsetSum n (fun y => Σ_S gSx·gSy) = subsetSum n (fun y => (ax·ay)·Π(x,y))
            //   subsetSum_congr n before_y after_y (fun y => leg_d_xy)
            let before_y = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let s_sum = {
                    let mut sb = EnvDeclBuilder::child_of(&yb);
                    let (s_id, s) = sb.fresh_local(hcp.clone());
                    let body = c.mul(c.g(n, a, &s, &x), c.g(n, a, &s, &y));
                    let f =
                        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body));
                    c.ssum(n, f)
                };
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), s_sum))
            };
            let after_y = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let ax_ay = c.mul(
                    Expr::app(a.clone(), x.clone()),
                    Expr::app(a.clone(), y.clone()),
                );
                let prod = c.fprod(n, c.prod_int(&yb, n, &x, &y));
                let body = c.mul(ax_ay, prod);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            let h_y = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let pf = leg_d_xy(c, &yb, n, a, &x, &y);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), pf))
            };
            let inner = Expr::apps(
                c.subset_sum_congr.clone(),
                [n.clone(), before_y, after_y, h_y],
            );
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), inner))
        };
        Expr::apps(
            c.subset_sum_congr.clone(),
            [
                n.clone(),
                c.e3_x_fn(parent, n, a),
                c.e4_x_fn(parent, n, a),
                h,
            ],
        )
    };

    // legE : e4 = e5   (Fin.sum_congr P over the decoded outer index).
    let leg_e = {
        let before = dec_outer(c, parent, n, &c.e4_x_fn(parent, n, a));
        let after = dec_outer(c, parent, n, &c.e5_x_fn(parent, n, a));
        let h = {
            let mut jb = EnvDeclBuilder::child_of(parent);
            let fin_p = c.fin_of(&c.pow2(n));
            let (jx_id, jx) = jb.fresh_local(fin_p.clone());
            let pf = leg_e_jx(c, &jb, n, a, &jx);
            jb.finish_child(jb.mk_lam(jx_id, BinderInfo::Default, fin_p, pf))
        };
        Expr::apps(c.fin_sum_congr(), [c.pow2(n), before, after, h])
    };

    // legF : e5 = cube · subsetSum n (a_sq)   (regroup mul_comm + subsetSum_smul).
    let leg_f = {
        // e5_x = (ax·ax)·cube ; regroup to cube·(ax·ax) via mul_comm (per x).
        let regroup_fn = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let ax = Expr::app(a.clone(), x.clone());
            let body = c.mul(c.cube(n), c.mul(ax.clone(), ax));
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        let h_regroup = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let ax = Expr::app(a.clone(), x.clone());
            let ax_ax = c.mul(ax.clone(), ax);
            // mul_comm (ax·ax) cube : (ax·ax)·cube = cube·(ax·ax).
            let body = c.mul_comm(ax_ax, c.cube(n));
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        let leg_f1 = Expr::apps(
            c.subset_sum_congr.clone(),
            [n.clone(), c.e5_x_fn(parent, n, a), regroup_fn, h_regroup],
        );
        // subsetSum_smul n cube (a_sq) : Σ_x cube·(ax·ax) = cube·Σ_x(ax·ax).
        let leg_f2 = Expr::apps(
            c.subset_sum_smul.clone(),
            [n.clone(), c.cube(n), c.a_sq_fn(parent, n, a)],
        );
        let mid = c.ssum(n, regroup_fn_e5(c, parent, n, a));
        c.trans(e5.clone(), mid, rhs.clone(), leg_f1, leg_f2)
    };

    // Assemble: e0 = e1 = e2 = e3 = e4 = e5 = rhs.
    let t1 = c.trans(e0.clone(), e1.clone(), e2.clone(), leg_a, leg_b);
    let t2 = c.trans(e0.clone(), e2.clone(), e3.clone(), t1, leg_c);
    let t3 = c.trans(e0.clone(), e3.clone(), e4.clone(), t2, leg_d);
    let t4 = c.trans(e0.clone(), e4, e5.clone(), t3, leg_e);
    c.trans(e0, e5, rhs, t4, leg_f)
}

/// `fun x => cube·(a x·a x)` — the legF regroup integrand (matches `regroup_fn`).
fn regroup_fn_e5(c: &CoreConsts, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
    let mut xb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = xb.fresh_local(hcp.clone());
    let ax = Expr::app(a.clone(), x.clone());
    let body = c.mul(c.cube(n), c.mul(ax.clone(), ax));
    xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
}
