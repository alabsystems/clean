// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Noise-operator self-adjointness over the un-normalized Boolean cube — the
//! pivot of the dual-HC self-adjoint/divide argument.
//!
//! ## Why this lemma exists
//!
//! `boolean_analysis_noise_density_symm.rs` landed the SYMMETRY atoms
//! `noiseDensityW_symm` (`dens x y = dens y x`) and `noiseDensityW_pair_symm`.
//! This file consumes them (together with the landed Fubini brick
//! `subsetSum_swap` and the scalar-homogeneity brick `subsetSum_smul`) to close
//! the FULL operator identity
//!
//! ```text
//!   <T_ρ g, h> = <g, T_ρ h>          (T_ρ self-adjoint, un-normalized cube ⟨·,·⟩)
//! ```
//!
//! Everything here is RATIONAL — the inner products are `Fin.sum`s of `Rat`
//! products (`subsetSum`), and `noiseDensityW ρ n x y : Rat`. NO real/sqrt
//! carrier is touched. The dual-HC bound ABOVE self-adjointness still needs the
//! fractional `(4/3,4)` Hölder over the campaign's real carrier — that is a
//! separate, non-colliding rung. This file retires NO axiom; it is chain input
//! toward dual-HC.
//!
//! ## Convention (matches `noise_spectral_core` / the dual-HC consumer)
//!
//! The un-normalized cube inner product is `⟨u,v⟩ = subsetSum n (fun p => u p · v p)`.
//! The noise operator is `(T_ρ g)(y) = subsetSum n (fun x => noiseDensityW ρ n y x · g x)`.
//! So, fully expanded over `subsetSum`:
//!
//! ```text
//! <T_ρ g, h> = subsetSum n (fun y => h y · subsetSum n (fun x => dens y x · g x))
//! <g, T_ρ h> = subsetSum n (fun x => g x · subsetSum n (fun y => dens x y · h y))
//! ```
//!
//! where `dens a b := noiseDensityW ρ n a b`.
//!
//! ## The theorem (constructive, EMPTY domain-axiom closure)
//!
//! ```text
//! BoolAnalysis.noise_self_adjoint :
//!   ∀ (ρ : Rat) (n : Nat) (g h : HCPoint n → Rat),
//!     subsetSum n (fun y => h y · subsetSum n (fun x => noiseDensityW ρ n y x · g x))
//!   = subsetSum n (fun x => g x · subsetSum n (fun y => noiseDensityW ρ n x y · h y))
//!
//! BoolAnalysis.noise_self_adjoint_at_third :
//!   the ρ = 1/3 specialization (the form the dual-HC argument consumes).
//! ```
//!
//! ## The proof (multi-rung Fubini, closed)
//!
//! ```text
//!   <T_ρ g,h> = Σ_y h y·(Σ_x dens y x·g x)
//!     →[congr_y · symm(subsetSum_smul)]  Σ_y Σ_x h y·(dens y x·g x)       (pull h y in)
//!     →[subsetSum_swap (y↔x)]            Σ_x Σ_y h y·(dens y x·g x)       (Fubini)
//!     →[congr_x · congr_y · LEAF]        Σ_x Σ_y g x·(dens x y·h y)       (per-(x,y) symm)
//!     →[congr_x · subsetSum_smul]        Σ_x g x·(Σ_y dens x y·h y) = <g,T_ρ h>
//! ```
//!
//! The per-`(x,y)` LEAF `h y·(dens y x·g x) = g x·(dens x y·h y)` is proved from
//! foundations: `Rat.mul_assoc`/`Rat.mul_comm` to regroup the three factors plus
//! `noiseDensityW_symm` to flip `dens y x → dens x y`. Every cited brick is
//! constructive with an EMPTY admitted-axiom closure, so the whole is
//! `ProofQuality::Constructive`, empty closure. No axiom added or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms. The `noiseDensityW` / `subsetSum` / integrand builds are
/// byte-for-byte the conventions in `boolean_analysis_noise_density_symm.rs` and
/// `boolean_analysis_noise_spectral.rs`, so all terms stay def-eq to the
/// carriers the bricks rewrite.
struct SelfAdjConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    rat_mul: Expr,
    mul_comm: Expr,
    mul_assoc: Expr,
    hcpoint: Expr,
    noise_density: Expr,
    noise_density_symm: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_swap: Expr,
    subset_sum_smul: Expr,
    eq1: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl SelfAdjConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            rat_mul: k("Rat.mul"),
            mul_comm: k("Rat.mul_comm"),
            mul_assoc: k("Rat.mul_assoc"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            noise_density: k("BoolAnalysis.noiseDensityW"),
            noise_density_symm: k("BoolAnalysis.noiseDensityW_symm"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_swap: k("BoolAnalysis.subsetSum_swap"),
            subset_sum_smul: k("BoolAnalysis.subsetSum_smul"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `HCPoint n → Rat`.
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
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
    /// `noiseDensityW ρ n a b`.
    fn dens(&self, rho: &Expr, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.noise_density.clone(),
            [rho.clone(), n.clone(), a.clone(), b.clone()],
        )
    }
    /// `noiseDensityW_symm ρ n a b : dens a b = dens b a`.
    fn dens_symm(&self, rho: &Expr, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.noise_density_symm.clone(),
            [rho.clone(), n.clone(), a.clone(), b.clone()],
        )
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `Eq.symm Rat l r h : r = l`  (from `h : l = r`).
    fn symm(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), l, r, h])
    }
    /// `Eq.trans Rat a b c h1 h2 : a = c`.
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `congrArg.{1,1} Rat Rat from to f h : f from = f to`.
    fn congr(&self, from: Expr, to: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, f, h],
        )
    }
    /// `subsetSum_congr n G H hpw : subsetSum n G = subsetSum n H`.
    fn ssum_congr(&self, n: &Expr, g: Expr, h: Expr, hpw: Expr) -> Expr {
        Expr::apps(self.subset_sum_congr.clone(), [n.clone(), g, h, hpw])
    }

    // ── the named cube quantities (def-eq to the goal subterms) ─────────────

    /// Inner LHS x-sum `T(y) := subsetSum n (fun x => dens y x · g x)`.
    fn t_of_y(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, y: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(self.dens(rho, n, y, &x), Expr::app(g.clone(), x.clone()));
        let f = b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }
    /// LHS y-integrand `fun y => h y · T(y)`  (the `<T_ρ g, h>` body).
    fn lhs_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, h: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = b.fresh_local(hcp.clone());
        let body = self.mul(
            Expr::app(h.clone(), y.clone()),
            self.t_of_y(&b, rho, n, g, &y),
        );
        b.finish_child(b.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }
    /// Inner RHS y-sum `U(x) := subsetSum n (fun y => dens x y · h y)`.
    fn u_of_x(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, h: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = b.fresh_local(hcp.clone());
        let body = self.mul(self.dens(rho, n, x, &y), Expr::app(h.clone(), y.clone()));
        let f = b.finish_child(b.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }
    /// RHS x-integrand `fun x => g x · U(x)`  (the `<g, T_ρ h>` body).
    fn rhs_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, h: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(
            Expr::app(g.clone(), x.clone()),
            self.u_of_x(&b, rho, n, h, &x),
        );
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    // ── the double-sum normal forms (the Fubini middle ground) ──────────────

    /// `fun x => dens y x · g x` — the per-y inner-sum integrand (so
    /// `subsetSum n (this)` is syntactically `T(y)`).
    fn dxg_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, y: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(self.dens(rho, n, y, &x), Expr::app(g.clone(), x.clone()));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun y => dens x y · h y` — the per-x inner-sum integrand (so
    /// `subsetSum n (this)` is syntactically `U(x)`).
    fn dyh_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, h: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = b.fresh_local(hcp.clone());
        let body = self.mul(self.dens(rho, n, x, &y), Expr::app(h.clone(), y.clone()));
        b.finish_child(b.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }

    /// `MID_L := subsetSum n (fun y => subsetSum n (fun x => h y·(dens y x·g x)))`
    /// — the LHS-side double sum (y outer, x inner) after pulling `h y` inward.
    fn mid_l(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, h: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = b.fresh_local(hcp.clone());
        let inner = {
            let mut xb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let dg = self.mul(self.dens(rho, n, &y, &x), Expr::app(g.clone(), x.clone()));
            let body = self.mul(Expr::app(h.clone(), y.clone()), dg);
            let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        b.finish_child(b.mk_lam(y_id, BinderInfo::Default, hcp, inner))
    }

    /// The `subsetSum_swap` integrand `fun y x => h y·(dens y x·g x)` (y is the
    /// `S` slot, x the second). `subsetSum n (fun y => subsetSum n (fun x => f y x))`
    /// is def-eq (β) to `MID_L`.
    fn swap_f(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, h: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = b.fresh_local(hcp.clone());
        let inner = {
            let mut xb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let dg = self.mul(self.dens(rho, n, &y, &x), Expr::app(g.clone(), x.clone()));
            let body = self.mul(Expr::app(h.clone(), y.clone()), dg);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        b.finish_child(b.mk_lam(y_id, BinderInfo::Default, hcp, inner))
    }

    /// `SWAPPED_L := subsetSum n (fun x => subsetSum n (fun y => h y·(dens y x·g x)))`
    /// — the `subsetSum_swap` RHS (x outer, y inner). Built explicitly so it is
    /// the syntactic endpoint of `subsetSum_swap n (swap_f)`.
    fn swapped_l(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, h: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let inner = {
            let mut yb = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let dg = self.mul(self.dens(rho, n, &y, &x), Expr::app(g.clone(), x.clone()));
            let body = self.mul(Expr::app(h.clone(), y.clone()), dg);
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, inner))
    }

    /// `MID_R := subsetSum n (fun x => subsetSum n (fun y => g x·(dens x y·h y)))`
    /// — the RHS-side double sum (x outer, y inner). After the leaf rewrite from
    /// `SWAPPED_L`; before pulling `g x` back out.
    fn mid_r(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, h: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let inner = {
            let mut yb = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let dh = self.mul(self.dens(rho, n, &x, &y), Expr::app(h.clone(), y.clone()));
            let body = self.mul(Expr::app(g.clone(), x.clone()), dh);
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, inner))
    }
}

/// `subsetSum_smul n c f : subsetSum n (fun p => c·f p) = c·subsetSum n f`.
fn ssum_smul(c: &SelfAdjConsts, n: &Expr, scalar: Expr, f: Expr) -> Expr {
    Expr::apps(c.subset_sum_smul.clone(), [n.clone(), scalar, f])
}

/// The conclusion `Eq` at fixed `ρ, n, g, h`:
/// `<T_ρ g, h> = <g, T_ρ h>` over the un-normalized cube ⟨·,·⟩.
fn self_adjoint_concl(
    c: &SelfAdjConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    g: &Expr,
    h: &Expr,
) -> Expr {
    let lhs = c.ssum(n, c.lhs_fn(parent, rho, n, g, h));
    let rhs = c.ssum(n, c.rhs_fn(parent, rho, n, g, h));
    c.eq_rat(lhs, rhs)
}

fn self_adjoint_type(c: &SelfAdjConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let (h_id, h) = b.fresh_local(fn_ty.clone());
    let concl = self_adjoint_concl(c, &b, &rho, &n, &g, &h);
    let e = b.mk_pi(h_id, BinderInfo::Default, fn_ty.clone(), concl);
    let e = b.mk_pi(g_id, BinderInfo::Default, fn_ty, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

fn self_adjoint_value(c: &SelfAdjConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let (h_id, h) = b.fresh_local(fn_ty.clone());

    let hcp = c.hcpoint_of(&n);

    // Named endpoints of the chain (full sums — each helper returns the OUTER
    // integrand `fun outer => subsetSum n (...)`, wrapped here in `subsetSum`).
    let lhs = c.ssum(&n, c.lhs_fn(&b, &rho, &n, &g, &h)); // <T_ρ g, h>
    let mid_l = c.ssum(&n, c.mid_l(&b, &rho, &n, &g, &h)); // Σ_y Σ_x h y·(dens y x·g x)
    let swapped_l = c.ssum(&n, c.swapped_l(&b, &rho, &n, &g, &h)); // Σ_x Σ_y h y·(dens y x·g x)
    let mid_r = c.ssum(&n, c.mid_r(&b, &rho, &n, &g, &h)); // Σ_x Σ_y g x·(dens x y·h y)
    let rhs = c.ssum(&n, c.rhs_fn(&b, &rho, &n, &g, &h)); // <g, T_ρ h>

    // ── Leg 1: lhs = mid_l   (pull `h y` into the inner x-sum, per y) ───────
    // For each y: `h y · T(y) = subsetSum n (fun x => h y·(dens y x·g x))`.
    //   subsetSum_smul n (h y) (dxg_fn y) : Σ_x (h y)·(dens y x·g x) = (h y)·T(y).
    //   Eq.symm flips it to `(h y)·T(y) = Σ_x (h y)·(dens y x·g x)`.
    // Lift over y via subsetSum_congr (lhs_fn → mid_l integrand).
    let leg1 = {
        // pointwise hyp: fun y => Eq.symm (subsetSum_smul n (h y) (dxg_fn y))
        let hpw = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = d.fresh_local(hcp.clone());
            let hy = Expr::app(h.clone(), y.clone());
            let dxg = c.dxg_fn(&d, &rho, &n, &g, &y);
            let smul = ssum_smul(c, &n, hy.clone(), dxg.clone());
            // smul : subsetSum n (fun x => (h y)·(dens y x·g x)) = (h y)·subsetSum n (dxg)
            let scaled_sum = c.ssum(&n, {
                // fun x => (h y)·(dens y x·g x)  — subsetSum_smul's scaled integrand.
                let mut xb = EnvDeclBuilder::child_of(&d);
                let (x_id, x) = xb.fresh_local(hcp.clone());
                let dg = c.mul(c.dens(&rho, &n, &y, &x), Expr::app(g.clone(), x.clone()));
                let body = c.mul(hy.clone(), dg);
                xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
            });
            let plain = c.mul(hy.clone(), c.ssum(&n, dxg)); // (h y)·T(y)
            let body = c.symm(scaled_sum, plain, smul);
            d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        c.ssum_congr(
            &n,
            c.lhs_fn(&b, &rho, &n, &g, &h),
            c.mid_l(&b, &rho, &n, &g, &h),
            hpw,
        )
    };

    // ── Leg 2: mid_l = swapped_l   (Fubini swap y↔x) ────────────────────────
    // subsetSum_swap n (swap_f) : Σ_y Σ_x f y x = Σ_x Σ_y f y x.
    // f y x = h y·(dens y x·g x); its LHS/RHS are def-eq (β) to mid_l / swapped_l.
    let leg2 = Expr::apps(
        c.subset_sum_swap.clone(),
        [n.clone(), c.swap_f(&b, &rho, &n, &g, &h)],
    );

    // ── Leg 3: swapped_l = mid_r   (per-(x,y) symmetry LEAF, double congr) ──
    // LEAF(x,y): h y·(dens y x·g x) = g x·(dens x y·h y).
    //   1. h y·(dens y x·g x) = (h y·dens y x)·g x          [symm assoc]
    //   2. (h y·dens y x)·g x = g x·(h y·dens y x)          [comm]
    //   3. g x·(h y·dens y x) = g x·(dens y x·h y)          [congr (g x·) comm]
    //   4. g x·(dens y x·h y) = g x·(dens x y·h y)          [congr (g x·(_·h y)) dens_symm]
    let leg3 = {
        let inner_hyp = |xb: &EnvDeclBuilder, x: &Expr| -> Expr {
            let mut d = EnvDeclBuilder::child_of(xb);
            let (y_id, y) = d.fresh_local(hcp.clone());
            let hy = Expr::app(h.clone(), y.clone());
            let gx = Expr::app(g.clone(), x.clone());
            let dyx = c.dens(&rho, &n, &y, x);
            let dxy = c.dens(&rho, &n, x, &y);

            let l0 = c.mul(hy.clone(), c.mul(dyx.clone(), gx.clone())); // h y·(dens y x·g x)
            let m1 = c.mul(c.mul(hy.clone(), dyx.clone()), gx.clone()); // (h y·dens y x)·g x
            let m2 = c.mul(gx.clone(), c.mul(hy.clone(), dyx.clone())); // g x·(h y·dens y x)
            let m3 = c.mul(gx.clone(), c.mul(dyx.clone(), hy.clone())); // g x·(dens y x·h y)
            let r0 = c.mul(gx.clone(), c.mul(dxy.clone(), hy.clone())); // g x·(dens x y·h y)

            // step 1: l0 = m1  via symm (assoc (h y) (dens y x) (g x))
            let s1 = {
                let assoc = c.assoc(hy.clone(), dyx.clone(), gx.clone()); // m1 = l0
                c.symm(m1.clone(), l0.clone(), assoc)
            };
            // step 2: m1 = m2  via comm (h y·dens y x) (g x)
            let s2 = c.comm(c.mul(hy.clone(), dyx.clone()), gx.clone());
            // step 3: m2 = m3  via congr (fun t => g x·t) (comm (h y) (dens y x))
            let s3 = {
                let f = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (t_id, t) = e.fresh_local(c.rat.clone());
                    e.finish_child(e.mk_lam(
                        t_id,
                        BinderInfo::Default,
                        c.rat.clone(),
                        c.mul(gx.clone(), t),
                    ))
                };
                c.congr(
                    c.mul(hy.clone(), dyx.clone()),
                    c.mul(dyx.clone(), hy.clone()),
                    f,
                    c.comm(hy.clone(), dyx.clone()),
                )
            };
            // step 4: m3 = r0  via congr (fun t => g x·(t·h y)) (dens_symm ρ n y x)
            let s4 = {
                let f = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (t_id, t) = e.fresh_local(c.rat.clone());
                    let body = c.mul(gx.clone(), c.mul(t, hy.clone()));
                    e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.congr(dyx.clone(), dxy.clone(), f, c.dens_symm(&rho, &n, &y, x))
            };

            // chain l0 = m1 = m2 = m3 = r0
            let t12 = c.trans(l0.clone(), m1.clone(), m2.clone(), s1, s2);
            let t13 = c.trans(l0.clone(), m2.clone(), m3.clone(), t12, s3);
            let body = c.trans(l0.clone(), m3.clone(), r0.clone(), t13, s4);
            d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };

        // outer hyp over x: fun x => subsetSum_congr n (swapped inner) (mid_r inner) (inner_hyp x)
        let hpw = {
            let mut xb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = xb.fresh_local(hcp.clone());

            // swapped inner integrand: fun y => h y·(dens y x·g x)
            let swapped_inner = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let dg = c.mul(c.dens(&rho, &n, &y, &x), Expr::app(g.clone(), x.clone()));
                let body = c.mul(Expr::app(h.clone(), y.clone()), dg);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            // mid_r inner integrand: fun y => g x·(dens x y·h y)
            let midr_inner = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let dh = c.mul(c.dens(&rho, &n, &x, &y), Expr::app(h.clone(), y.clone()));
                let body = c.mul(Expr::app(g.clone(), x.clone()), dh);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            let body = c.ssum_congr(&n, swapped_inner, midr_inner, inner_hyp(&xb, &x));
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        c.ssum_congr(
            &n,
            c.swapped_l(&b, &rho, &n, &g, &h),
            c.mid_r(&b, &rho, &n, &g, &h),
            hpw,
        )
    };

    // ── Leg 4: mid_r = rhs   (pull `g x` back out of the inner y-sum, per x) ─
    // For each x: subsetSum n (fun y => g x·(dens x y·h y)) = g x·U(x)
    //   = subsetSum_smul n (g x) (dyh_fn x).
    let leg4 = {
        let hpw = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = d.fresh_local(hcp.clone());
            let gx = Expr::app(g.clone(), x.clone());
            let dyh = c.dyh_fn(&d, &rho, &n, &h, &x);
            // subsetSum_smul n (g x) (dyh) : Σ_y (g x)·(dens x y·h y) = (g x)·U(x).
            let body = ssum_smul(c, &n, gx, dyh);
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        c.ssum_congr(
            &n,
            c.mid_r(&b, &rho, &n, &g, &h),
            c.rhs_fn(&b, &rho, &n, &g, &h),
            hpw,
        )
    };

    // ── Chain: lhs = mid_l = swapped_l = mid_r = rhs ────────────────────────
    let t12 = c.trans(lhs.clone(), mid_l.clone(), swapped_l.clone(), leg1, leg2);
    let t13 = c.trans(lhs.clone(), swapped_l.clone(), mid_r.clone(), t12, leg3);
    let proof = c.trans(lhs.clone(), mid_r.clone(), rhs.clone(), t13, leg4);

    let e = b.mk_lam(h_id, BinderInfo::Default, fn_ty.clone(), proof);
    let e = b.mk_lam(g_id, BinderInfo::Default, fn_ty, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ── ρ = 1/3 specialization (the dual-HC consumer's form) ────────────────────

/// `1/3 := Rat.mk (Int.ofNat 1) 3` — byte-for-byte the `hc24_at_third` ρ build.
fn rho_third(c: &SelfAdjConsts) -> Expr {
    let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let one_nat = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
    let mut three_nat = c.nat_zero.clone();
    for _ in 0..3 {
        three_nat = Expr::app(c.nat_succ.clone(), three_nat.clone());
    }
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [Expr::app(int_of_nat, one_nat), three_nat],
    )
}

fn self_adjoint_third_type(c: &SelfAdjConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let (h_id, h) = b.fresh_local(fn_ty.clone());
    let rho = rho_third(c);
    let concl = self_adjoint_concl(c, &b, &rho, &n, &g, &h);
    let e = b.mk_pi(h_id, BinderInfo::Default, fn_ty.clone(), concl);
    let e = b.mk_pi(g_id, BinderInfo::Default, fn_ty, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn self_adjoint_third_value(c: &SelfAdjConsts) -> Expr {
    // fun n g h => noise_self_adjoint (1/3) n g h
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let (h_id, h) = b.fresh_local(fn_ty.clone());
    let rho = rho_third(c);
    let body = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.noise_self_adjoint"), vec![]),
        [rho, n.clone(), g.clone(), h.clone()],
    );
    let e = b.mk_lam(h_id, BinderInfo::Default, fn_ty.clone(), body);
    let e = b.mk_lam(g_id, BinderInfo::Default, fn_ty, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register the noise-operator self-adjointness facts. Idempotent. Standalone
    /// (not wired into `init_boolean_analysis`); no axiom added or removed.
    pub fn init_boolean_analysis_noise_self_adjoint(&mut self) -> Result<(), EnvError> {
        self.register_noise_self_adjoint()?;
        self.register_noise_self_adjoint_at_third()?;
        Ok(())
    }

    /// `BoolAnalysis.noise_self_adjoint :
    ///    ∀ ρ n g h, <T_ρ g, h> = <g, T_ρ h>` (un-normalized cube ⟨·,·⟩).
    /// The full operator self-adjointness, the pivot of the dual-HC argument.
    /// Constructive, EMPTY closure.
    pub fn register_noise_self_adjoint(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_self_adjoint");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_density_w()?; // noiseDensityW (+ subsetSum, powNat, chi)
        self.register_noise_density_w_symm()?; // the density symmetry atom
        self.register_subset_sum_congr()?;
        self.register_subset_sum_swap_theorem()?; // finite Fubini
        self.register_subset_sum_smul_theorem()?; // scalar homogeneity
                                                  // Rat.mul_comm / Rat.mul_assoc (structural quotient lemmas).
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = SelfAdjConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: self_adjoint_type(&c),
            value: self_adjoint_value(&c),
        })
    }

    /// `BoolAnalysis.noise_self_adjoint_at_third :
    ///    ∀ n g h, <T_{1/3} g, h> = <g, T_{1/3} h>`.
    /// The ρ = 1/3 specialization consumed by the dual-HC self-adjoint/divide
    /// step. Constructive, EMPTY closure (a trivial instantiation of the general
    /// `noise_self_adjoint`). Idempotent.
    pub fn register_noise_self_adjoint_at_third(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_self_adjoint_at_third");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_noise_self_adjoint()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = SelfAdjConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: self_adjoint_third_type(&c),
            value: self_adjoint_third_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &[
        "BoolAnalysis.noise_self_adjoint",
        "BoolAnalysis.noise_self_adjoint_at_third",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_noise_self_adjoint()
            .expect("init_boolean_analysis_noise_self_adjoint");
        env.init_boolean_analysis_noise_self_adjoint()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_noise_self_adjoint_all_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} transitive axiom closure must be empty"
            );
        }
    }

    /// REFUTE GATE: the kernel check is load-bearing, not vacuous. Build a
    /// CORRUPTED, GENUINELY-FALSE "self-adjointness" type that replaces the RHS
    /// `<g, T_ρ h>` with `<g, T_ρ g>` (the inner `h y` is swapped to `g y`). For
    /// a generic dictator/parity-style witness `g ≠ h` the two sides differ —
    /// e.g. at `n = 1` with `g = χ_∅` (constant 1) and `h = χ_{0}` (parity), LHS
    /// = `<T_ρ g, h>` while the corrupted RHS = `<g, T_ρ g>`, which are unequal.
    /// So the genuine proof value must FAIL to check against this type; if it did
    /// not, the self-adjointness statement would be vacuous. We also confirm the
    /// corruption actually changed the type.
    #[test]
    fn test_noise_self_adjoint_refute_false_target() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let c = SelfAdjConsts::new();

        let genuine = env
            .get_const(&Name::from_string("BoolAnalysis.noise_self_adjoint"))
            .expect("registered");
        let value = genuine.value.clone().expect("proof present");

        // Corrupted type: RHS = <g, T_ρ g> instead of <g, T_ρ h> (inner h y → g y).
        let bad_ty = {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, rho) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fn_ty = c.hcpoint_to_rat(&n);
            let (g_id, g) = b.fresh_local(fn_ty.clone());
            let (h_id, h) = b.fresh_local(fn_ty.clone());
            let hcp = c.hcpoint_of(&n);

            let lhs = c.ssum(&n, c.lhs_fn(&b, &rho, &n, &g, &h));
            // BAD rhs: fun x => g x · subsetSum n (fun y => dens x y · g y)  (g for h).
            let bad_rhs_fn = {
                let mut xb = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = xb.fresh_local(hcp.clone());
                let inner = {
                    let mut yb = EnvDeclBuilder::child_of(&xb);
                    let (y_id, y) = yb.fresh_local(hcp.clone());
                    let dg = c.mul(c.dens(&rho, &n, &x, &y), Expr::app(g.clone(), y.clone()));
                    let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), dg));
                    c.ssum(&n, f)
                };
                let body = c.mul(Expr::app(g.clone(), x.clone()), inner);
                xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
            };
            let bad_rhs = c.ssum(&n, bad_rhs_fn);
            let concl = c.eq_rat(lhs, bad_rhs);
            let e = b.mk_pi(h_id, BinderInfo::Default, fn_ty.clone(), concl);
            let e = b.mk_pi(g_id, BinderInfo::Default, fn_ty, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        // The corruption must actually change the type (else the test is moot).
        assert_ne!(
            bad_ty, genuine.type_,
            "corrupted type must differ from the genuine type"
        );
        // The genuine proof must NOT inhabit the false target.
        assert!(
            tc.check_type(&value, &bad_ty).is_err(),
            "REFUTE FAILED: genuine proof checked against the FALSE <g,T_ρ g> \
             target — the self-adjointness kernel-check would be vacuous"
        );
    }
}
