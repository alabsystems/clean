// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_parseval_rung3b.rs — the `core_type` /
// `core_value` builders for `subsetSum_parseval_core`. Split out only for the
// 500-line-per-file convention; not a standalone module.

// ── statement ──────────────────────────────────────────────────────────────

impl CoreConsts {
    /// `fun (x : HCPoint n) => a x · chi n S x` — inner integrand at fixed S.
    fn g_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.g(n, a, s, &x);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// LHS `S`-integrand `fun S => (Σ_x aχ_Sx)·(Σ_x aχ_Sx)`.
    fn lhs_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let inner = self.ssum(n, self.g_fn(&b, n, a, &s));
        let body = self.mul(inner.clone(), inner);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// RHS `x`-integrand `fun x => a x · a x`.
    fn a_sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let ax = Expr::app(a.clone(), x.clone());
        let body = self.mul(ax.clone(), ax);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// The `g`-bundle as `HCPoint n → HCPoint n → Rat`: `fun S x => a x · χ_S x`.
    fn g_bundle(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let inner = self.g_fn(&b, n, a, &s);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, inner))
    }
}

fn core_type(c: &CoreConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let a_ty = c.hcpoint_to_rat(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());
    let lhs = c.ssum(&n, c.lhs_s_fn(&b, &n, &a));
    let rhs = c.mul(c.cube(&n), c.ssum(&n, c.a_sq_fn(&b, &n, &a)));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(a_id, BinderInfo::Default, a_ty, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

// ── proof ──────────────────────────────────────────────────────────────────

fn core_value(c: &CoreConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let a_ty = c.hcpoint_to_rat(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());
    let proof = parseval_chain(c, &b, &n, &a);
    let val = b.mk_lam(a_id, BinderInfo::Default, a_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl CoreConsts {
    // ── stage-expression builders (all functions HCPoint→… as subsetSum) ──

    /// `fun S => Σ_x Σ_y (g S x · g S y)` — the double-sum after sq_to_double.
    fn e1_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let body = self.dbl_xy(&b, n, a, &s);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `Σ_x Σ_y (g S x · g S y)` at fixed S.
    fn dbl_xy(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, s: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let inner = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let body = self.mul(self.g(n, a, s, &x), self.g(n, a, s, &y));
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, inner));
        self.ssum(n, f)
    }

    /// `fun x => Σ_S Σ_y (g S x · g S y)` — after first swap (S↔x).
    fn e2_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let s_sum = {
            let mut sb = EnvDeclBuilder::child_of(&xb);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let y_sum = {
                let mut yb = EnvDeclBuilder::child_of(&sb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let body = self.mul(self.g(n, a, &s, &x), self.g(n, a, &s, &y));
                let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
                self.ssum(n, f)
            };
            let f = sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), y_sum));
            self.ssum(n, f)
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, s_sum))
    }

    /// `fun x => Σ_y Σ_S (g S x · g S y)` — after second swap (S↔y per-x).
    fn e3_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let y_sum = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let s_sum = {
                let mut sb = EnvDeclBuilder::child_of(&yb);
                let (s_id, s) = sb.fresh_local(hcp.clone());
                let body = self.mul(self.g(n, a, &s, &x), self.g(n, a, &s, &y));
                let f = sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body));
                self.ssum(n, f)
            };
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), s_sum));
            self.ssum(n, f)
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, y_sum))
    }

    /// `fun x => Σ_y (a x·a y)·Π_i(1+pm(x i)pm(y i))` — after δ + smul (per x,y).
    fn e4_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let y_sum = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let ax_ay = self.mul(
                Expr::app(a.clone(), x.clone()),
                Expr::app(a.clone(), y.clone()),
            );
            let prod = self.fprod(n, self.prod_int(&yb, n, &x, &y));
            let body = self.mul(ax_ay, prod);
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        let f = self.ssum(n, y_sum);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, f))
    }

    /// `fun x => (a x·a x)·(2^n/1)` — after diagonal collapse (per x).
    fn e5_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let ax = Expr::app(a.clone(), x.clone());
        let body = self.mul(self.mul(ax.clone(), ax), self.cube(n));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

include!("boolean_analysis_parseval_rung3b_chain.rs");
