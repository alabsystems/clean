// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parseval RUNG 3 (stage 3a) — lift the product-of-sums expansion to
//! `subsetSum`.
//!
//! `BoolAnalysis.subsetSum_sq_to_double :
//!     ∀ (n : Nat) (g : HCPoint n → HCPoint n → Rat),
//!       subsetSum n (fun S => Rat.mul (subsetSum n (g S)) (subsetSum n (g S)))
//!         = subsetSum n (fun S =>
//!             subsetSum n (fun x => subsetSum n (fun y =>
//!               Rat.mul (g S x) (g S y))))`
//!
//! The first Fubini stage: the square of an inner cube-sum is the double
//! cube-sum of the product. Proved by `subsetSum_congr` over `S`, discharging
//! the per-`S` goal with RUNG 1's `Fin.sum_mul_sum` (both `subsetSum`s δ-unfold
//! to `Fin.sum (2^n) (· ∘ hcDecode)`, and the nested `subsetSum`s on the RHS
//! δ-unfold to the matching double `Fin.sum (2^n)`). Kernel-checked,
//! constructive (closure ⊆ `subsetSum_congr` / `Fin.sum_mul_sum` ∪ defs — no
//! domain axiom).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct Rung3aConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_mul_sum: Expr,
    fin_sum_swap: Expr,
    fin_sum_smul: Expr,
    fin_sum_sub: Expr,
    eq1: Expr,
}

impl Rung3aConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_mul_sum: Expr::const_(Name::from_string("Fin.sum_mul_sum"), vec![]),
            fin_sum_swap: Expr::const_(Name::from_string("Fin.sum_swap"), vec![]),
            fin_sum_smul: Expr::const_(Name::from_string("Fin.sum_smul"), vec![]),
            fin_sum_sub: Expr::const_(Name::from_string("Fin.sum_sub"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1]),
        }
    }

    fn one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn two(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.one())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two(), n.clone()])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `HCPoint n → HCPoint n → Rat`.
    fn g_ty(&self, n: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let inner = Expr::pi(BinderInfo::Default, hcp.clone(), self.rat.clone());
        Expr::pi(BinderInfo::Default, hcp, inner)
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn hc_decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }

    /// `fun (x : HCPoint n) => Rat.mul (g S x) (g S y)` is built per-context;
    /// here the LHS `S`-integrand `fun S => (subsetSum n (g S))·(subsetSum n (g S))`.
    fn lhs_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let gs = Expr::app(g.clone(), s.clone());
        let inner = self.ssum(n, gs);
        let body = self.mul(inner.clone(), inner);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `fun S => subsetSum n (fun x => subsetSum n (fun y => g S x · g S y))`.
    fn rhs_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let gs = Expr::app(g.clone(), s.clone());
        let outer = {
            let mut xb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let gsx = Expr::app(gs.clone(), x.clone());
            let inner = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let gsy = Expr::app(gs.clone(), y.clone());
                let body = self.mul(gsx.clone(), gsy);
                let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
                self.ssum(n, f)
            };
            let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), inner));
            self.ssum(n, f)
        };
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, outer))
    }
}

fn ty(c: &Rung3aConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.g_ty(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let lhs = c.ssum(&n, c.lhs_fn(&b, &n, &g));
    let rhs = c.ssum(&n, c.rhs_fn(&b, &n, &g));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn value(c: &Rung3aConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.g_ty(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());

    let lhs_fn = c.lhs_fn(&b, &n, &g);
    let rhs_fn = c.rhs_fn(&b, &n, &g);

    // per-S proof:  (subsetSum n (g S))·(subsetSum n (g S))
    //                 = subsetSum n (fun x => subsetSum n (fun y => g S x · g S y))
    //   Both sides δ-unfold to the Fin.sum (2^n) forms matching
    //   Fin.sum_mul_sum P P (decoded (g S)) (decoded (g S)).
    let h = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let gs = Expr::app(g.clone(), s.clone());
        // decoded (g S) : fun (j : Fin (2^n)) => g S (hcDecode n j)
        let dec = {
            let mut jb = EnvDeclBuilder::child_of(&sb);
            let fin_p = c.fin_of(&c.pow2(&n));
            let (j_id, j) = jb.fresh_local(fin_p.clone());
            let body = Expr::app(gs.clone(), c.hc_decode(&n, &j));
            jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p, body))
        };
        let pp = c.pow2(&n);
        let body = Expr::apps(
            c.fin_sum_mul_sum.clone(),
            [pp.clone(), pp, dec.clone(), dec],
        );
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    };

    let proof = Expr::apps(c.subset_sum_congr.clone(), [n.clone(), lhs_fn, rhs_fn, h]);
    let val = b.mk_lam(g_id, BinderInfo::Default, g_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

// ════════════════════ stage 3b: subsetSum_swap (Fubini) ════════════════════

impl Rung3aConsts {
    /// `fun (S : HCPoint n) => subsetSum n (fun x => f S x)` — outer/inner sum
    /// nesting for the swap, with `f : HCPoint n → HCPoint n → Rat`.
    /// `outer_first = true`  ⟹ `fun S => Σ_x f S x` (S outer, x inner).
    /// `outer_first = false` ⟹ `fun x => Σ_S f S x` (x outer, S inner).
    fn nest(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, outer_first: bool) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (o_id, o) = b.fresh_local(hcp.clone());
        let inner = {
            let mut ib = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = ib.fresh_local(hcp.clone());
            // f applied as f S x: when outer_first, o = S, i = x; else o = x, i = S.
            let (s, x) = if outer_first {
                (o.clone(), i.clone())
            } else {
                (i.clone(), o.clone())
            };
            let body = Expr::apps(f.clone(), [s, x]);
            let lam = ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, lam)
        };
        b.finish_child(b.mk_lam(o_id, BinderInfo::Default, hcp, inner))
    }
}

fn swap_ty(c: &Rung3aConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.g_ty(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let lhs = c.ssum(&n, c.nest(&b, &n, &f, true));
    let rhs = c.ssum(&n, c.nest(&b, &n, &f, false));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn swap_value(c: &Rung3aConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.g_ty(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());

    // F2 : Fin P → Fin P → Rat := fun j i => f (hcDecode n j) (hcDecode n i).
    //   LHS δ-unfolds to Fin.sum P (fun j => Fin.sum P (fun i => F2 j i)),
    //   RHS δ-unfolds to Fin.sum P (fun i => Fin.sum P (fun j => F2 j i));
    //   Fin.sum_swap P P F2 bridges them.
    let pp = c.pow2(&n);
    let fin_p = c.fin_of(&pp);
    let f2 = {
        let mut jb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = jb.fresh_local(fin_p.clone());
        let sj = c.hc_decode(&n, &j);
        let inner = {
            let mut ib = EnvDeclBuilder::child_of(&jb);
            let (i_id, i) = ib.fresh_local(fin_p.clone());
            let xi = c.hc_decode(&n, &i);
            let body = Expr::apps(f.clone(), [sj.clone(), xi]);
            ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_p.clone(), body))
        };
        jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p.clone(), inner))
    };
    let proof = Expr::apps(c.fin_sum_swap.clone(), [pp.clone(), pp, f2]);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

// ════════════════════ stage 3c: subsetSum_smul ═════════════════════════════

impl Rung3aConsts {
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    /// `fun (S : HCPoint n) => Rat.mul cc (f S)` — the scaled `subsetSum` integrand.
    fn scaled_fn(&self, parent: &EnvDeclBuilder, n: &Expr, cc: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let body = self.mul(cc.clone(), Expr::app(f.clone(), s));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

fn smul_ty(c: &Rung3aConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (cc_id, cc) = b.fresh_local(c.rat.clone());
    let f_ty = c.hcpoint_to_rat(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let lhs = c.ssum(&n, c.scaled_fn(&b, &n, &cc, &f));
    let rhs = c.mul(cc.clone(), c.ssum(&n, f.clone()));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
    let r = b.mk_pi(cc_id, BinderInfo::Default, c.rat.clone(), r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn smul_value(c: &Rung3aConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (cc_id, cc) = b.fresh_local(c.rat.clone());
    let f_ty = c.hcpoint_to_rat(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());

    // decoded f : fun (j : Fin P) => f (hcDecode n j).
    let pp = c.pow2(&n);
    let fin_p = c.fin_of(&pp);
    let dec = {
        let mut jb = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = jb.fresh_local(fin_p.clone());
        let body = Expr::app(f.clone(), c.hc_decode(&n, &j));
        jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p, body))
    };
    // Fin.sum_smul P cc (decoded f) : Σ_P (cc · (decoded f) j) = cc · Σ_P (decoded f)
    //   LHS δ-folds to subsetSum n (fun S => cc·f S); RHS to cc·subsetSum n f.
    let proof = Expr::apps(c.fin_sum_smul.clone(), [pp, cc.clone(), dec]);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_ty, proof);
    let val = b.mk_lam(cc_id, BinderInfo::Default, c.rat.clone(), val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

// ════════════════════ stage 3d: subsetSum_sub (additivity) ═════════════════

impl Rung3aConsts {
    /// `fun (S : HCPoint n) => Rat.sub (G S) (H S)` — pointwise-difference integrand.
    fn diff_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, h: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let body = Expr::apps(
            self.rat_sub.clone(),
            [Expr::app(g.clone(), s.clone()), Expr::app(h.clone(), s)],
        );
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

fn sub_ty(c: &Rung3aConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(f_ty.clone());
    let (h_id, h) = b.fresh_local(f_ty.clone());
    let lhs = c.ssum(&n, c.diff_fn(&b, &n, &g, &h));
    let rhs = Expr::apps(
        c.rat_sub.clone(),
        [c.ssum(&n, g.clone()), c.ssum(&n, h.clone())],
    );
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(h_id, BinderInfo::Default, f_ty.clone(), concl);
    let r = b.mk_pi(g_id, BinderInfo::Default, f_ty, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn sub_value(c: &Rung3aConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(f_ty.clone());
    let (h_id, h) = b.fresh_local(f_ty.clone());

    let pp = c.pow2(&n);
    let fin_p = c.fin_of(&pp);
    // decoded g / decoded h : fun (j : Fin P) => g/h (hcDecode n j).
    let dec = |f: &Expr, b: &EnvDeclBuilder| {
        let mut jb = EnvDeclBuilder::child_of(b);
        let (j_id, j) = jb.fresh_local(fin_p.clone());
        let body = Expr::app(f.clone(), c.hc_decode(&n, &j));
        jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p.clone(), body))
    };
    let dec_g = dec(&g, &b);
    let dec_h = dec(&h, &b);
    // Fin.sum_sub P (decoded g) (decoded h) : Σ_P ((dg j)−(dh j)) = Σ_P dg − Σ_P dh
    //   LHS δ-folds to subsetSum n (fun S => G S − H S); RHS to subsetSum n G − subsetSum n H.
    let proof = Expr::apps(c.fin_sum_sub.clone(), [pp, dec_g, dec_h]);
    let val = b.mk_lam(h_id, BinderInfo::Default, f_ty.clone(), proof);
    let val = b.mk_lam(g_id, BinderInfo::Default, f_ty, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_sub` — RUNG-3 stage 3d, additivity
    /// (subtraction) at the `subsetSum` level: `Σ_S (G S − H S) = Σ_S G S − Σ_S H S`.
    /// Derived from the constructive `Fin.sum_sub`. Kernel-checked, constructive.
    /// Idempotent.
    pub(crate) fn register_subset_sum_sub_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_sub");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.register_subset_sum()?;
        self.init_fin_sum()?; // registers the constructive Fin.sum_sub theorem
        self.register_fin_sum_sub_theorem()?;

        let c = Rung3aConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: sub_ty(&c),
            value: sub_value(&c),
        })
    }

    /// Register `BoolAnalysis.subsetSum_smul` — RUNG-3 stage 3c, scalar
    /// homogeneity at the `subsetSum` level: `Σ_S c·f S = c·Σ_S f S`. Derived
    /// from `Fin.sum_smul`. Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_subset_sum_smul_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_smul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.register_subset_sum()?;
        self.init_fin_sum()?;
        self.register_fin_sum_smul_theorem()?;

        let c = Rung3aConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: smul_ty(&c),
            value: smul_value(&c),
        })
    }

    /// Register `BoolAnalysis.subsetSum_swap` — RUNG-3 stage 3b, finite Fubini
    /// at the `subsetSum` level: `Σ_S Σ_x f S x = Σ_x Σ_S f S x`. Derived from
    /// `Fin.sum_swap` (both sides δ-unfold to the matching double `Fin.sum`).
    /// Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_subset_sum_swap_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_swap");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.register_subset_sum()?;
        self.init_fin_sum()?;
        self.register_fin_sum_swap_theorem()?;

        let c = Rung3aConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: swap_ty(&c),
            value: swap_value(&c),
        })
    }

    /// Register `BoolAnalysis.subsetSum_sq_to_double` — RUNG-3 stage 3a, the
    /// product-of-`subsetSum`s expansion. Kernel-checked, constructive.
    /// Idempotent.
    pub(crate) fn register_subset_sum_sq_to_double_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_sq_to_double");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.init_fin_sum()?;
        self.register_fin_sum_mul_theorem()?;
        self.register_fin_sum_mul_sum_theorem()?;

        let c = Rung3aConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty(&c),
            value: value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    fn check(env: &Environment, name: &str) {
        let n = Name::from_string(name);
        let info = env.get_const(&n).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ty = tc
            .infer_type(&Expr::const_(n, vec![]))
            .unwrap_or_else(|_| panic!("{name} should type-check"));
    }

    #[test]
    fn test_subset_sum_sq_to_double_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_subset_sum_sq_to_double_theorem()
            .expect("register_subset_sum_sq_to_double_theorem");
        check(&env, "BoolAnalysis.subsetSum_sq_to_double");
    }

    #[test]
    fn test_subset_sum_swap_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_subset_sum_swap_theorem()
            .expect("register_subset_sum_swap_theorem");
        check(&env, "BoolAnalysis.subsetSum_swap");
    }

    #[test]
    fn test_subset_sum_smul_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_subset_sum_smul_theorem()
            .expect("register_subset_sum_smul_theorem");
        env.register_subset_sum_smul_theorem().expect("idempotent");
        check(&env, "BoolAnalysis.subsetSum_smul");
        let n = Name::from_string("BoolAnalysis.subsetSum_smul");
        let deps = env.axiom_deps(&n).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "subsetSum_smul closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
    }

    #[test]
    fn test_subset_sum_sub_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_subset_sum_sub_theorem()
            .expect("register_subset_sum_sub_theorem");
        env.register_subset_sum_sub_theorem().expect("idempotent");
        check(&env, "BoolAnalysis.subsetSum_sub");
        let n = Name::from_string("BoolAnalysis.subsetSum_sub");
        let deps = env.axiom_deps(&n).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "subsetSum_sub closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
    }
}
