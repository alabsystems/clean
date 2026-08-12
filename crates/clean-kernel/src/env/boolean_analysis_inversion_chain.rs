// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_inversion_legs.rs — the leg proofs and the
// top-level `inversion_chain`.

impl InvConsts {
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn fin_sum_congr(&self) -> Expr {
        Expr::const_(Name::from_string("Fin.sum_congr"), vec![])
    }
    fn mul_assoc(&self, a: Expr, bb: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, bb, cc],
        )
    }
    /// `congrArg (fun z => z·right) h : a·right = bb·right`.
    fn mul_right_congr(
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
            let body = self.mul(z, right.clone());
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }
}

/// Per-S permutation `χx·(by·χy) = by·(χx·χy)` (a commutative-monoid 3-swap),
/// from the landed `Rat.mul_assoc` / `Rat.mul_comm`:
///   χx·(by·χy) =[symm assoc]  (χx·by)·χy
///              =[comm·χy]      (by·χx)·χy
///              =[assoc]        by·(χx·χy).
fn leg_c_per_s(
    c: &InvConsts,
    parent: &EnvDeclBuilder,
    chi_x: &Expr,
    by: &Expr,
    chi_y: &Expr,
) -> Expr {
    let lhs = c.mul(chi_x.clone(), c.mul(by.clone(), chi_y.clone())); // χx·(by·χy)
    let p1 = c.mul(c.mul(chi_x.clone(), by.clone()), chi_y.clone()); // (χx·by)·χy
    let p2 = c.mul(c.mul(by.clone(), chi_x.clone()), chi_y.clone()); // (by·χx)·χy
    let rhs = c.mul(by.clone(), c.mul(chi_x.clone(), chi_y.clone())); // by·(χx·χy)

    // s1 : lhs = p1   (Eq.symm (mul_assoc χx by χy)).
    let assoc1 = c.mul_assoc(chi_x.clone(), by.clone(), chi_y.clone()); // (χx·by)·χy = χx·(by·χy)
    let s1 = c.symm(p1.clone(), lhs.clone(), assoc1);
    // s2 : p1 = p2   (congrArg (·χy) (mul_comm χx by)).
    let comm = c.mul_comm(chi_x.clone(), by.clone()); // χx·by = by·χx
    let s2 = c.mul_right_congr(
        parent,
        chi_y,
        c.mul(chi_x.clone(), by.clone()),
        c.mul(by.clone(), chi_x.clone()),
        comm,
    );
    // s3 : p2 = rhs   (mul_assoc by χx χy).
    let s3 = c.mul_assoc(by.clone(), chi_x.clone(), chi_y.clone());

    let t1 = c.trans(lhs.clone(), p1, p2.clone(), s1, s2);
    c.trans(lhs, p2, rhs, t1, s3)
}

/// Leg C (per y under e2→e3): `Σ_S χ_S(x)·(b(y)·χ_S(y)) = b(y)·Π(x,y)`.
fn leg_c_y(c: &InvConsts, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, x: &Expr, y: &Expr) -> Expr {
    let hcp = c.hcpoint_of(n);
    let by = Expr::app(b.clone(), y.clone());

    // chi_chi integrand: fun S => χ_S(x)·χ_S(y)
    let chi_chi_fn = {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let body = c.mul(c.chi_(n, &s, x), c.chi_(n, &s, y));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    // regrouped integrand: fun S => b(y)·(χ_S(x)·χ_S(y))
    let regrouped_fn = {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let body = c.mul(by.clone(), c.mul(c.chi_(n, &s, x), c.chi_(n, &s, y)));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };

    // leg1 : Σ_S before = Σ_S regrouped   (subsetSum_congr + per-S 3-swap)
    let before_fn = before_fn_clone(c, parent, n, b, x, y);
    let h_regroup = {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let chi_x = c.chi_(n, &s, x);
        let chi_y = c.chi_(n, &s, y);
        let body = leg_c_per_s(c, &sb, &chi_x, &by, &chi_y);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    let leg1 = Expr::apps(
        c.subset_sum_congr.clone(),
        [n.clone(), before_fn, regrouped_fn, h_regroup],
    );

    // leg2 : Σ_S regrouped = b(y)·Σ_S(χ_Sx·χ_Sy)   (subsetSum_smul)
    let leg2 = Expr::apps(
        c.subset_sum_smul.clone(),
        [n.clone(), by.clone(), chi_chi_fn.clone()],
    );

    // leg3 : b(y)·Σ_S(χ_Sx·χ_Sy) = b(y)·Π(x,y)   (congrArg (b(y)·) δ)
    let delta = Expr::apps(
        c.subset_chi_bilinear.clone(),
        [n.clone(), x.clone(), y.clone()],
    );
    let ss_chi = c.ssum(n, chi_chi_fn);
    let prod = c.fprod(n, c.prod_int(parent, n, x, y));
    let leg3 = c.mul_left_congr(parent, &by, ss_chi.clone(), prod.clone(), delta);

    // chain: before = regrouped = b(y)·Σχχ = b(y)·Π
    let ss_before = c.ssum(n, before_fn_clone(c, parent, n, b, x, y));
    let ss_regrouped = c.ssum(n, regrouped_fn_clone(c, parent, n, b, x, y));
    let mid = c.mul(by.clone(), ss_chi);
    let target = c.mul(by, prod);
    let t1 = c.trans(ss_before.clone(), ss_regrouped, mid.clone(), leg1, leg2);
    c.trans(ss_before, mid, target, t1, leg3)
}

// Re-builders (alpha-equal copies for the chain endpoints).
fn before_fn_clone(
    c: &InvConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    b: &Expr,
    x: &Expr,
    y: &Expr,
) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = sb.fresh_local(hcp.clone());
    let by = Expr::app(b.clone(), y.clone());
    let by_chi = c.mul(by, c.chi_(n, &s, y));
    let body = c.mul(c.chi_(n, &s, x), by_chi);
    sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
}
fn regrouped_fn_clone(
    c: &InvConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    b: &Expr,
    x: &Expr,
    y: &Expr,
) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = sb.fresh_local(hcp.clone());
    let by = Expr::app(b.clone(), y.clone());
    let body = c.mul(by, c.mul(c.chi_(n, &s, x), c.chi_(n, &s, y)));
    sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

include!("boolean_analysis_inversion_chain2.rs");
