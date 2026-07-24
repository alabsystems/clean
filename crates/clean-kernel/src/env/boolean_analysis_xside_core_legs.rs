// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_xside_core.rs — `xcore_type` / `xcore_value` and
// the full chain for `subsetSum_xside_core`. The dual of the rung3b parseval
// core: OUTER sum over the sign point `x`, SQUARED inner sum over the gate `S`,
// `g S x = a S · χ_S(x)`. Split out for the 500-line rule.

// ── statement ──────────────────────────────────────────────────────────────

impl XCoreConsts {
    /// `fun (S : HCPoint n) => a S · chi n S x` — inner integrand at fixed `x`.
    fn g_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let body = self.g(n, a, &s, x);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// LHS `x`-integrand `fun x => (Σ_S aχ_Sx)·(Σ_S aχ_Sx)`.
    fn lhs_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let inner = self.ssum(n, self.g_fn(&b, n, a, &x));
        let body = self.mul(inner.clone(), inner);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// RHS `S`-integrand `fun S => a S · a S`.
    fn a_sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let as_ = Expr::app(a.clone(), s.clone());
        let body = self.mul(as_.clone(), as_);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// The `g`-bundle `fun x S => a S · χ_S x` : `HCPoint n → HCPoint n → Rat`.
    fn g_bundle(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let inner = self.g_fn(&b, n, a, &x);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, inner))
    }
}

fn xcore_type(c: &XCoreConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let a_ty = c.hcpoint_to_rat(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());
    let lhs = c.ssum(&n, c.lhs_x_fn(&b, &n, &a));
    let rhs = c.mul(c.cube(&n), c.ssum(&n, c.a_sq_fn(&b, &n, &a)));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(a_id, BinderInfo::Default, a_ty, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

// ── proof ──────────────────────────────────────────────────────────────────

fn xcore_value(c: &XCoreConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let a_ty = c.hcpoint_to_rat(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());
    let proof = xcore_chain(c, &b, &n, &a);
    let val = b.mk_lam(a_id, BinderInfo::Default, a_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl XCoreConsts {
    // ── stage-expression builders (all functions HCPoint→… as subsetSum) ──

    /// `fun x => Σ_S Σ_T (g S x · g T x)` — the double-sum after sq_to_double.
    fn e1_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.dbl_st(&b, n, a, &x);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `Σ_S Σ_T (g S x · g T x)` at fixed `x`.
    fn dbl_st(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, x: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let inner = {
            let mut tb = EnvDeclBuilder::child_of(&sb);
            let (t_id, t) = tb.fresh_local(hcp.clone());
            let body = self.mul(self.g(n, a, &s, x), self.g(n, a, &t, x));
            let f = tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        let f = sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, inner));
        self.ssum(n, f)
    }

    /// `fun S => Σ_x Σ_T (g S x · g T x)` — after first swap (x↔S).
    fn e2_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let x_sum = {
            let mut xb = EnvDeclBuilder::child_of(&sb);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let t_sum = {
                let mut tb = EnvDeclBuilder::child_of(&xb);
                let (t_id, t) = tb.fresh_local(hcp.clone());
                let body = self.mul(self.g(n, a, &s, &x), self.g(n, a, &t, &x));
                let f = tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body));
                self.ssum(n, f)
            };
            let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), t_sum));
            self.ssum(n, f)
        };
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, x_sum))
    }

    /// `fun S => Σ_T Σ_x (g S x · g T x)` — after second swap (x↔T per-S).
    fn e3_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let t_sum = {
            let mut tb = EnvDeclBuilder::child_of(&sb);
            let (t_id, t) = tb.fresh_local(hcp.clone());
            let x_sum = {
                let mut xb = EnvDeclBuilder::child_of(&tb);
                let (x_id, x) = xb.fresh_local(hcp.clone());
                let body = self.mul(self.g(n, a, &s, &x), self.g(n, a, &t, &x));
                let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body));
                self.ssum(n, f)
            };
            let f = tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), x_sum));
            self.ssum(n, f)
        };
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, t_sum))
    }

    /// `fun S => Σ_T (a S·a T)·Π_i(1+pm(S i)pm(T i))` — after δ + smul (per S,T).
    fn e4_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let t_sum = {
            let mut tb = EnvDeclBuilder::child_of(&sb);
            let (t_id, t) = tb.fresh_local(hcp.clone());
            let as_at = self.mul(
                Expr::app(a.clone(), s.clone()),
                Expr::app(a.clone(), t.clone()),
            );
            let prod = self.fprod(n, self.prod_int(&tb, n, &s, &t));
            let body = self.mul(as_at, prod);
            tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
        };
        let f = self.ssum(n, t_sum);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, f))
    }

    /// `fun S => (a S·a S)·(2^n/1)` — after diagonal collapse (per S).
    fn e5_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let as_ = Expr::app(a.clone(), s.clone());
        let body = self.mul(self.mul(as_.clone(), as_), self.cube(n));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `F1 x S = Σ_T (g S x · g T x)` bundle for the legB swap.
    fn f1_bundle(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let inner = {
            let mut sb = EnvDeclBuilder::child_of(&xb);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let t_sum = {
                let mut tb = EnvDeclBuilder::child_of(&sb);
                let (t_id, t) = tb.fresh_local(hcp.clone());
                let body = self.mul(self.g(n, a, &s, &x), self.g(n, a, &t, &x));
                let f = tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body));
                self.ssum(n, f)
            };
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), t_sum))
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, inner))
    }
}

include!("boolean_analysis_xside_core_chain.rs");
