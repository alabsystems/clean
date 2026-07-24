// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_inversion_proof.rs — the `inv_core_type` /
// `inv_core_value` builders for `subsetSum_inversion_core`. Split out only for
// the 500-line-per-file convention; not a standalone module.

// ── statement ──────────────────────────────────────────────────────────────

impl InvConsts {
    /// `fun (y : HCPoint n) => b y · chi n S y` — the inner integrand at fixed S.
    fn inner_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, s: &Expr) -> Expr {
        let mut bld = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = bld.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(b.clone(), y.clone()), self.chi_(n, s, &y));
        bld.finish_child(bld.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }
    /// LHS `S`-integrand `fun S => (Σ_y b(y)·χ_S(y))·χ_S(x)`.
    fn lhs_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, x: &Expr) -> Expr {
        let mut bld = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = bld.fresh_local(hcp.clone());
        let inner = self.ssum(n, self.inner_fn(&bld, n, b, &s));
        let body = self.mul(inner, self.chi_(n, &s, x));
        bld.finish_child(bld.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

fn inv_core_type(c: &InvConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let fin_p = c.fin_of(&c.pow2(&n));
    let (jx_id, jx) = b.fresh_local(fin_p.clone());
    let x = c.hc_decode(&n, &jx);
    let lhs = c.ssum(&n, c.lhs_s_fn(&b, &n, &bf, &x));
    let rhs = c.mul(c.cube(&n), Expr::app(bf.clone(), x.clone()));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(jx_id, BinderInfo::Default, fin_p, concl);
    let r = b.mk_pi(bf_id, BinderInfo::Default, b_ty, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

// ── proof ──────────────────────────────────────────────────────────────────

fn inv_core_value(c: &InvConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let fin_p = c.fin_of(&c.pow2(&n));
    let (jx_id, jx) = b.fresh_local(fin_p.clone());
    let proof = inversion_chain(c, &b, &n, &bf, &jx);
    let val = b.mk_lam(jx_id, BinderInfo::Default, fin_p, proof);
    let val = b.mk_lam(bf_id, BinderInfo::Default, b_ty, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl InvConsts {
    // ── stage-expression builders (functions HCPoint→… under subsetSum) ──

    /// `fun S => Σ_y χ_S(x)·(b(y)·χ_S(y))` — after legA (per-S smul).
    fn e1_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, x: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let chi_sx = self.chi_(n, &s, x);
        let y_sum = {
            let mut yb = EnvDeclBuilder::child_of(&sb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let by_chi = self.mul(Expr::app(b.clone(), y.clone()), self.chi_(n, &s, &y));
            let body = self.mul(chi_sx.clone(), by_chi);
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, y_sum))
    }

    /// `fun y => Σ_S χ_S(x)·(b(y)·χ_S(y))` — after legB (swap S↔y).
    fn e2_y_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, x: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let s_sum = {
            let mut sb = EnvDeclBuilder::child_of(&yb);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let by_chi = self.mul(Expr::app(b.clone(), y.clone()), self.chi_(n, &s, &y));
            let body = self.mul(self.chi_(n, &s, x), by_chi);
            let f = sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, s_sum))
    }

    /// `fun y => b(y)·Π_i(1+pm(x i)pm(y i))` — after legC (δ + smul per y).
    fn e3_y_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, x: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let by = Expr::app(b.clone(), y.clone());
        let prod = self.fprod(n, self.prod_int(&yb, n, x, &y));
        let body = self.mul(by, prod);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }

    /// `fun y => b(y)·2^n` — after legD (diagonal collapse per y).
    fn e4_y_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let by = Expr::app(b.clone(), y.clone());
        let body = self.mul(by, self.cube(n));
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }
}

include!("boolean_analysis_inversion_chain.rs");
