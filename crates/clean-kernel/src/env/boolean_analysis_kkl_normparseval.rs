// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL endgame — the **normalized-Parseval bridge → bare Poincaré**.
//!
//! This module lands the mechanical, fully-constructive half of the KKL
//! residual (run-3 items 1–2): the `Expect`-normalized total-mass Parseval,
//! the `Variance = Σ_{S≠∅} f̂²` identity, and the bare Poincaré inequality
//! `Var ≤ I[f]`. All lemmas are kernel-checked `Declaration::Theorem`s,
//! `ProofQuality::Constructive` with an empty admitted-axiom closure.
//!
//! ```text
//! (1) BoolAnalysis.expect_pm_sq_eq_fourier_mass :
//!       ∀ n (f : BoolFn n),
//!         Expect n (fun x => pm (f x) · pm (f x))
//!           = subsetSum n (fun S => f̂ S · f̂ S)
//!
//! (1') BoolAnalysis.fourier_mass_eq_one :
//!       ∀ n (f : BoolFn n), subsetSum n (fun S => f̂ S · f̂ S) = Rat.one
//!
//! (2) BoolAnalysis.variance_eq_nonempty_mass :
//!       ∀ n (f : BoolFn n),
//!         Variance n f
//!           = subsetSum n (fun S => ind (Nat.ble 1 (setSizeNat n S)) · (f̂ S · f̂ S))
//!
//! (3) BoolAnalysis.variance_le_influence :   -- the bare Poincaré inequality
//!       ∀ n (f : BoolFn n), Variance n f ≤ TotalInfluence n f
//! ```
//!
//! ## Item-1 derivation (the `4^n`-cancellation, fully constructive)
//!
//! Write `D := Rat.mk (Int.ofNat (2^n)) 1` (the `Expect`/`subsetSum`
//! normalizer `2^n` as a `Rat`), `Â S := subsetSum n (fun x => pm (f x) · χ_S x)`
//! (the *un-normalized* Fourier coefficient), and
//! `P := subsetSum n (fun x => pm (f x) · pm (f x))` (the un-normalized total
//! mass). Then `f̂ S = FourierCoefficient n f S` δ-reduces (reducible defs) to
//! `Rat.div (Â S) D = Rat.mul (Â S) (Rat.inv D)`, so each per-`S` Fourier
//! square is def-eq to `(Â S · D⁻¹) · (Â S · D⁻¹)`. The chain is
//!
//! ```text
//!   subsetSum n (fun S => f̂ S · f̂ S)
//! = subsetSum n (fun S => (D⁻¹·D⁻¹) · (Â S · Â S))   -- congr: mmmc + mul_comm
//! = (D⁻¹·D⁻¹) · subsetSum n (fun S => Â S · Â S)     -- subsetSum_smul
//! = (D⁻¹·D⁻¹) · (D · P)                              -- parseval_identity
//! = D⁻¹ · P                                          -- assoc + inv_mul + one_mul
//! = Rat.div P D                                      -- mul_comm + Rat.div def
//! = Expect n (fun x => pm (f x) · pm (f x))          -- def-eq (Expect = ssum/D)
//! ```
//!
//! Each step is a registered constructive `Rat`/`subsetSum` lemma
//! (`Rat.mul_mul_mul_comm`, `Rat.mul_comm`, `Rat.mul_assoc`, `Rat.one_mul`,
//! `Rat.mul_inv_cancel`, `BoolAnalysis.subsetSum_smul`,
//! `BoolAnalysis.subsetSum_congr`, `BoolAnalysis.parseval_identity`), composed
//! with `Eq.trans` / `Eq.subst`. The `1'` corollary chains item 1 with
//! `Expect_congr` (pointwise `pm_mul_self`) and `Expect_const_one`.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the normalized-Parseval bridge.
struct NpConsts {
    order: OrderConsts,
    nat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_mk: Expr,
    bool_fn: Expr,
    hcpoint: Expr,
    pm: Expr,
    chi: Expr,
    fourier: Expr,
    subset_sum: Expr,
    subset_sum_congr: Expr,
    subset_sum_smul: Expr,
    parseval: Expr,
    mul_comm: Expr,
    mul_assoc: Expr,
    mul_inv_cancel: Expr,
    mul_mul_mul_comm: Expr,
    one_mul: Expr,
    congr_arg: Expr,
}

impl NpConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            order: OrderConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_inv: Expr::const_(Name::from_string("Rat.inv"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            bool_fn: Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            fourier: Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            subset_sum_congr: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_congr"),
                vec![],
            ),
            subset_sum_smul: Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]),
            parseval: Expr::const_(Name::from_string("BoolAnalysis.parseval_identity"), vec![]),
            mul_comm: Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            mul_assoc: Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            mul_inv_cancel: Expr::const_(Name::from_string("Rat.mul_inv_cancel"), vec![]),
            mul_mul_mul_comm: Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            one_mul: Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    /// `@congrArg.{1,1} Rat Rat a1 a2 g h : g a1 = g a2`.
    fn congr(&self, a1: Expr, a2: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a1, a2, g, h],
        )
    }
    /// `fun (t : Rat) => Rat.mul t r` — left-multiply-by-`t`, scaling slot `r`.
    fn mul_right_fn(&self, parent: &EnvDeclBuilder, r: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = b.fresh_local(self.rat.clone());
        let body = self.mul(t, r.clone());
        b.finish_child(b.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `fun (t : Rat) => Rat.mul l t` — right-multiply-`t`, fixed left `l`.
    fn mul_left_fn(&self, parent: &EnvDeclBuilder, l: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = b.fresh_local(self.rat.clone());
        let body = self.mul(l.clone(), t);
        b.finish_child(b.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
    }

    fn rat(&self) -> Expr {
        self.rat.clone()
    }
    fn one(&self) -> Expr {
        self.order.rat_one.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        self.order.rat_eq(l, r)
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    /// `D := Rat.mk (Int.ofNat (2^n)) 1` — the `Expect`/`subsetSum` normalizer.
    fn denom(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), self.pow2(n)), one],
        )
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `fun (x : HCPoint n) => Rat.mul (pm (f x)) (chi n S x)` — the `Â`-integrand.
    fn amp_chi(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let pm_fx = Expr::app(self.pm.clone(), Expr::app(f.clone(), x.clone()));
        let chi_sx = Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()]);
        let body = self.mul(pm_fx, chi_sx);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `Â S := subsetSum n (fun x => pm (f x) · χ_S x)` — the un-normalized coeff.
    fn amp(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        self.subset_sum_of(n, self.amp_chi(parent, n, f, s))
    }
    /// `fun (x : HCPoint n) => Rat.mul (pm (f x)) (pm (f x))` — the total-mass
    /// integrand. (`P := subsetSum n` of this.)
    fn pm_sq(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let pm_fx = Expr::app(self.pm.clone(), Expr::app(f.clone(), x.clone()));
        let body = self.mul(pm_fx.clone(), pm_fx);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `Eq.symm.{1} Rat a b h`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    /// `Eq.trans.{1} Rat a b c h1 h2`.
    fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        self.order.trans(a, b, c, h1, h2)
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc_of(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul_of(&self, a: Expr) -> Expr {
        Expr::app(self.one_mul.clone(), a)
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, dd: Expr) -> Expr {
        Expr::apps(self.mul_mul_mul_comm.clone(), [a, b, cc, dd])
    }
    /// `Rat.mul_inv_cancel a h : a·a⁻¹ = 1` (h : a = 0 → False).
    fn mul_inv_cancel_of(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.mul_inv_cancel.clone(), [a, h])
    }
    /// `BoolAnalysis.subsetSum_smul n cc g : subsetSum n (fun S => cc·g S) = cc·subsetSum n g`.
    fn subset_sum_smul_of(&self, n: &Expr, cc: Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum_smul.clone(), [n.clone(), cc, g])
    }
    /// `BoolAnalysis.subsetSum_congr n G H pw : subsetSum n G = subsetSum n H`.
    fn subset_sum_congr_of(&self, n: &Expr, g: Expr, h: Expr, pw: Expr) -> Expr {
        Expr::apps(self.subset_sum_congr.clone(), [n.clone(), g, h, pw])
    }
    /// `BoolAnalysis.parseval_identity n f`.
    fn parseval_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.parseval.clone(), [n.clone(), f.clone()])
    }
    /// `fun (S : HCPoint n) => Rat.mul (f̂ S) (f̂ S)` — the Fourier-square integrand.
    fn fourier_sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let fhat = self.fourier_of(n, f, &s);
        let body = self.mul(fhat.clone(), fhat);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (S : HCPoint n) => Rat.mul (Â S) (Â S)` — the un-normalized-square
    /// integrand (byte-identical to `parseval_identity`'s LHS integrand).
    fn amp_sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let amp = self.amp(&b, n, f, &s);
        let body = self.mul(amp.clone(), amp);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (S : HCPoint n) => Rat.mul (D⁻¹·D⁻¹) (Rat.mul (Â S) (Â S))` — the
    /// scaled un-normalized-square integrand (the `subsetSum_smul` LHS shape and
    /// `fourier_sq_regroup`'s RHS).
    fn scaled_amp_sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let dinv = self.inv(self.denom(n));
        let amp = self.amp(&b, n, f, &s);
        let body = self.mul(self.mul(dinv.clone(), dinv), self.mul(amp.clone(), amp));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `subsetSum n (fun x => pm (f x) · pm (f x))` — the un-normalized total `P`.
    fn p_total(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        self.subset_sum_of(n, self.pm_sq(parent, n, f))
    }
    /// `fun (_ : HCPoint n) => Rat.one` — the const-1 integrand (byte-identical to
    /// `Expect_const_one`'s integrand).
    fn const_one_fn(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, _x) = b.fresh_local(hcp.clone());
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, self.one()))
    }
    /// `Expect n g`.
    fn expect_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.Expect"), vec![]),
            [n.clone(), g],
        )
    }
    /// `BoolAnalysis.fourier_sq_regroup n f S`.
    fn regroup_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.fourier_sq_regroup"), vec![]),
            [n.clone(), f.clone(), s.clone()],
        )
    }
    /// `BoolAnalysis.inv_sq_mul_mul_cancel d p h`.
    fn cancel_of(&self, d: Expr, p: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.inv_sq_mul_mul_cancel"),
                vec![],
            ),
            [d, p, h],
        )
    }
    /// `BoolAnalysis.two_pow_rat_ne_zero n`.
    fn ne_zero_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(
                Name::from_string("BoolAnalysis.two_pow_rat_ne_zero"),
                vec![],
            ),
            n.clone(),
        )
    }
}

impl Environment {
    /// Register the normalized-Parseval bridge through bare Poincaré.
    /// Idempotent.
    pub fn init_boolean_analysis_kkl_normparseval(&mut self) -> Result<(), EnvError> {
        self.register_two_pow_rat_ne_zero()?;
        self.register_fourier_sq_regroup()?;
        self.register_inv_sq_mul_mul_cancel()?;
        self.register_expect_pm_sq_eq_fourier_mass()?;
        self.register_fourier_mass_eq_one()?;
        Ok(())
    }

    /// **Deliverable 1.** `BoolAnalysis.expect_pm_sq_eq_fourier_mass :
    ///   ∀ (n) (f : BoolFn n),
    ///     Expect n (fun x => pm (f x) · pm (f x))
    ///       = subsetSum n (fun S => f̂ S · f̂ S)`
    ///
    /// The `Expect`-normalized total-mass Parseval. Proven `RHS = LHS` (then
    /// `Eq.symm`):
    ///
    /// ```text
    ///   subsetSum n (fun S => f̂²)
    /// = subsetSum n (fun S => (D⁻¹·D⁻¹)·(Â²))   [subsetSum_congr ∘ fourier_sq_regroup]
    /// = (D⁻¹·D⁻¹) · subsetSum n (fun S => Â²)   [subsetSum_smul]
    /// = (D⁻¹·D⁻¹) · (D · P)                     [congrArg ∘ parseval_identity]
    /// = D⁻¹ · P                                 [inv_sq_mul_mul_cancel ∘ two_pow_rat_ne_zero]
    /// = P · D⁻¹                                 [Rat.mul_comm]
    /// ≡ Expect n (fun x => pm (f x) · pm (f x)) [def-eq: Expect = Rat.div P D = P·D⁻¹]
    /// ```
    ///
    /// `D := Rat.mk (Int.ofNat (2^n)) 1`, `Â S := subsetSum n (pm·χ_S)`,
    /// `P := subsetSum n (pm·pm)`. Kernel-checked, `Constructive`, empty closure
    /// (every step bottoms out in a `Constructive` lemma / def-unfold).
    /// Idempotent.
    pub fn register_expect_pm_sq_eq_fourier_mass(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.expect_pm_sq_eq_fourier_mass");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis()?; // Expect, FourierCoefficient, parseval_identity
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_fourier_sq_regroup()?;
        self.register_inv_sq_mul_mul_cancel()?;
        self.register_two_pow_rat_ne_zero()?;

        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this theorem transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = NpConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let lhs = c.expect_of(&n, c.pm_sq(&b, &n, &f));
            let rhs = c.subset_sum_of(&n, c.fourier_sq_fn(&b, &n, &f));
            let concl = c.eq_rat(lhs, rhs);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let d = c.denom(&n);
            let dinv = c.inv(d.clone());
            let k = c.mul(dinv.clone(), dinv.clone()); // D⁻¹·D⁻¹
            let p = c.p_total(&b, &n, &f); // P

            // Integrands.
            let fhat_sq = c.fourier_sq_fn(&b, &n, &f); // fun S => f̂²
            let scaled = c.scaled_amp_sq_fn(&b, &n, &f); // fun S => K·(Â²)
            let amp_sq = c.amp_sq_fn(&b, &n, &f); // fun S => Â²

            // Terms.
            let s0 = c.subset_sum_of(&n, fhat_sq.clone()); // Σ f̂²
            let s1 = c.subset_sum_of(&n, scaled.clone()); // Σ K·Â²
            let ssum_amp_sq = c.subset_sum_of(&n, amp_sq.clone()); // Σ Â²
            let s2 = c.mul(k.clone(), ssum_amp_sq.clone()); // K·Σ Â²
            let dp = c.mul(d.clone(), p.clone()); // D·P
            let s3 = c.mul(k.clone(), dp.clone()); // K·(D·P)
            let s4 = c.mul(dinv.clone(), p.clone()); // D⁻¹·P
            let s5 = c.mul(p.clone(), dinv.clone()); // P·D⁻¹  [≡ Expect lhs]

            // h01 : Σ f̂² = Σ K·Â²   (subsetSum_congr, pw = fourier_sq_regroup)
            let pw = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = c.regroup_of(&n, &f, &s);
                ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };
            let h01 = c.subset_sum_congr_of(&n, fhat_sq.clone(), scaled.clone(), pw);

            // h12 : Σ K·Â² = K·Σ Â²   (subsetSum_smul n K (fun S => Â²))
            let h12 = c.subset_sum_smul_of(&n, k.clone(), amp_sq.clone());

            // h23 : K·Σ Â² = K·(D·P)   (congrArg (K·) parseval_identity)
            let parseval = c.parseval_of(&n, &f); // Σ Â² = D·P
            let mul_k = c.mul_left_fn(&b, &k);
            let h23 = c.congr(ssum_amp_sq.clone(), dp.clone(), mul_k, parseval);

            // h34 : K·(D·P) = D⁻¹·P   (inv_sq_mul_mul_cancel D P (two_pow_rat_ne_zero n))
            let h34 = c.cancel_of(d.clone(), p.clone(), c.ne_zero_of(&n));

            // h45 : D⁻¹·P = P·D⁻¹   (mul_comm)
            let h45 = c.mul_comm_of(dinv.clone(), p.clone());

            // Chain s0 = s1 = s2 = s3 = s4 = s5.
            let h02 = c.trans(s0.clone(), s1.clone(), s2.clone(), h01, h12);
            let h03 = c.trans(s0.clone(), s2.clone(), s3.clone(), h02, h23);
            let h04 = c.trans(s0.clone(), s3.clone(), s4.clone(), h03, h34);
            let h05 = c.trans(s0.clone(), s4.clone(), s5.clone(), h04, h45);
            // h05 : Σ f̂² = P·D⁻¹.  The goal is Expect = Σ f̂², so symm with LHS
            // def-eq to P·D⁻¹.
            let body = c.symm(s0, s5, h05);

            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.inv_sq_mul_mul_cancel :
    ///   ∀ (d p : Rat), (Eq Rat d Rat.zero → False) →
    ///     Rat.mul (Rat.mul (Rat.inv d) (Rat.inv d)) (Rat.mul d p)
    ///       = Rat.mul (Rat.inv d) p`
    ///
    /// Sub-bridge (c) of item 1: the `4^n`-cancellation core,
    /// `(d⁻¹·d⁻¹)·(d·p) = d⁻¹·p`. Pure `Rat`-field algebra: `mul_assoc` peels the
    /// outer `d⁻¹`, `mul_assoc`+`mul_comm`+`mul_inv_cancel` collapse the inner
    /// `d⁻¹·(d·p)` to `(d⁻¹·d)·p = 1·p = p`, then `congrArg (d⁻¹·)` lifts. The
    /// nonzero hypothesis feeds `Rat.mul_inv_cancel`. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_inv_sq_mul_mul_cancel(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.inv_sq_mul_mul_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?; // mul_assoc, mul_comm, mul_inv_cancel, one_mul, inv

        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this theorem transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = NpConsts::new();
        let false_ = Expr::const_(Name::from_string("False"), vec![]);

        // ∀ (d p : Rat), (d = 0 → False) → concl
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.rat());
            let (p_id, p) = b.fresh_local(c.rat());
            let dinv = c.inv(d.clone());
            let hyp = Expr::pi(
                BinderInfo::Default,
                c.eq_rat(d.clone(), c.order.rat_zero.clone()),
                false_.clone(),
            );
            let lhs = c.mul(
                c.mul(dinv.clone(), dinv.clone()),
                c.mul(d.clone(), p.clone()),
            );
            let rhs = c.mul(dinv, p.clone());
            let concl = c.eq_rat(lhs, rhs);
            let e = Expr::pi(BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.rat(), e);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.rat(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.rat());
            let (p_id, p) = b.fresh_local(c.rat());
            let hyp_ty = Expr::pi(
                BinderInfo::Default,
                c.eq_rat(d.clone(), c.order.rat_zero.clone()),
                false_.clone(),
            );
            let (h_id, h) = b.fresh_local(hyp_ty.clone());

            let dinv = c.inv(d.clone());
            let dp = c.mul(d.clone(), p.clone());
            let one = c.one();

            // e1 : (d⁻¹·d⁻¹)·(d·p) = d⁻¹·(d⁻¹·(d·p))
            let e1 = c.mul_assoc_of(dinv.clone(), dinv.clone(), dp.clone());
            // e2 : d⁻¹·(d·p) = (d⁻¹·d)·p   (symm of mul_assoc d⁻¹ d p)
            let assoc_idp = c.mul_assoc_of(dinv.clone(), d.clone(), p.clone()); // (d⁻¹·d)·p = d⁻¹·(d·p)
            let e2 = c.symm(
                c.mul(c.mul(dinv.clone(), d.clone()), p.clone()),
                c.mul(dinv.clone(), dp.clone()),
                assoc_idp,
            );
            // e3 : d⁻¹·d = 1   (trans (mul_comm d⁻¹ d) (mul_inv_cancel d h))
            let e3 = c.trans(
                c.mul(dinv.clone(), d.clone()),
                c.mul(d.clone(), dinv.clone()),
                one.clone(),
                c.mul_comm_of(dinv.clone(), d.clone()),
                c.mul_inv_cancel_of(d.clone(), h.clone()),
            );
            // e4 : (d⁻¹·d)·p = 1·p   (congrArg (·p) e3)
            let mul_p = c.mul_right_fn(&b, &p);
            let e4 = c.congr(c.mul(dinv.clone(), d.clone()), one.clone(), mul_p, e3);
            // e5 : 1·p = p
            let e5 = c.one_mul_of(p.clone());
            // e45 : (d⁻¹·d)·p = p
            let e45 = c.trans(
                c.mul(c.mul(dinv.clone(), d.clone()), p.clone()),
                c.mul(one.clone(), p.clone()),
                p.clone(),
                e4,
                e5,
            );
            // e_inner : d⁻¹·(d·p) = p   (trans e2 e45)
            let e_inner = c.trans(
                c.mul(dinv.clone(), dp.clone()),
                c.mul(c.mul(dinv.clone(), d.clone()), p.clone()),
                p.clone(),
                e2,
                e45,
            );
            // e6 : d⁻¹·(d⁻¹·(d·p)) = d⁻¹·p   (congrArg (d⁻¹·) e_inner)
            let mul_dinv = c.mul_left_fn(&b, &dinv);
            let e6 = c.congr(
                c.mul(dinv.clone(), dp.clone()),
                p.clone(),
                mul_dinv,
                e_inner,
            );

            // result : (d⁻¹·d⁻¹)·(d·p) = d⁻¹·p   (trans e1 e6)
            let lhs = c.mul(c.mul(dinv.clone(), dinv.clone()), dp.clone());
            let mid = c.mul(dinv.clone(), c.mul(dinv.clone(), dp.clone()));
            let rhs = c.mul(dinv.clone(), p.clone());
            let body = c.trans(lhs, mid, rhs, e1, e6);

            let e = b.mk_lam(h_id, BinderInfo::Default, hyp_ty, body);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.rat(), e);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.rat(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.fourier_sq_regroup :
    ///   ∀ (n) (f : BoolFn n) (S : HCPoint n),
    ///     Rat.mul (f̂ S) (f̂ S)
    ///       = Rat.mul (Rat.mul D⁻¹ D⁻¹) (Rat.mul (Â S) (Â S))`
    ///
    /// where `D := Rat.mk (Int.ofNat (2^n)) 1` and `Â S := subsetSum n (pm·χ_S)`
    /// (the un-normalized coefficient). Sub-bridge (b) of item 1: pulls the
    /// `1/4^n` measure factor out of the per-`S` Fourier square. `f̂ S` δ-reduces
    /// (reducible `FourierCoefficient`/`Expect`/`subsetSum`/`Rat.div`) to
    /// `Rat.mul (Â S) D⁻¹`, so the regroup is `Rat.mul_mul_mul_comm` (giving
    /// `(Â·Â)·(D⁻¹·D⁻¹)`) followed by `Rat.mul_comm` (to `(D⁻¹·D⁻¹)·(Â·Â)`),
    /// transported across the `Eq.refl` def-unfold. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_fourier_sq_regroup(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.fourier_sq_regroup");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis()?; // FourierCoefficient, chi, pm
        self.init_rat()?; // Rat.mul_comm, Rat.mul_mul_mul_comm, Rat.inv
        self.register_subset_sum()?;

        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this theorem transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = NpConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());

            let fhat = c.fourier_of(&n, &f, &s);
            let lhs = c.mul(fhat.clone(), fhat);
            let dinv = c.inv(c.denom(&n));
            let amp = c.amp(&b, &n, &f, &s);
            let rhs = c.mul(c.mul(dinv.clone(), dinv), c.mul(amp.clone(), amp));
            let concl = c.eq_rat(lhs, rhs);

            let e = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: fun n f S =>
        //   trans (refl ((Â·D⁻¹)·(Â·D⁻¹)))            -- def-eq from f̂·f̂
        //         (trans (mmmc Â D⁻¹ Â D⁻¹)            -- (Â·Â)·(D⁻¹·D⁻¹)
        //                (mul_comm (Â·Â) (D⁻¹·D⁻¹)))   -- (D⁻¹·D⁻¹)·(Â·Â)
        // The leading refl is implicit: f̂·f̂ is def-eq to (Â·D⁻¹)·(Â·D⁻¹), so the
        // `mmmc` term (typed at the latter) already has the goal's LHS up to
        // def-eq; we just chain mmmc then mul_comm.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());

            let dinv = c.inv(c.denom(&n));
            let amp = c.amp(&b, &n, &f, &s);

            // a := (Â·D⁻¹)·(Â·D⁻¹) [def-eq to f̂·f̂]
            let a = c.mul(
                c.mul(amp.clone(), dinv.clone()),
                c.mul(amp.clone(), dinv.clone()),
            );
            // bb := (Â·Â)·(D⁻¹·D⁻¹)
            let bb = c.mul(
                c.mul(amp.clone(), amp.clone()),
                c.mul(dinv.clone(), dinv.clone()),
            );
            // cc := (D⁻¹·D⁻¹)·(Â·Â)
            let cc = c.mul(
                c.mul(dinv.clone(), dinv.clone()),
                c.mul(amp.clone(), amp.clone()),
            );

            // mmmc Â D⁻¹ Â D⁻¹ : (Â·D⁻¹)·(Â·D⁻¹) = (Â·Â)·(D⁻¹·D⁻¹)
            let h1 = c.mmmc(amp.clone(), dinv.clone(), amp.clone(), dinv.clone());
            // mul_comm (Â·Â) (D⁻¹·D⁻¹) : (Â·Â)·(D⁻¹·D⁻¹) = (D⁻¹·D⁻¹)·(Â·Â)
            let h2 = c.mul_comm_of(
                c.mul(amp.clone(), amp.clone()),
                c.mul(dinv.clone(), dinv.clone()),
            );

            let body = c.trans(a, bb, cc, h1, h2);
            let e = b.mk_lam(s_id, BinderInfo::Default, hcp, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.two_pow_rat_ne_zero :
    ///   ∀ (n : Nat), Eq Rat (Rat.mk (Int.ofNat (Nat.pow 2 n)) 1) Rat.zero → False`.
    ///
    /// The `2^n` normalizer is a nonzero `Rat`; supplied to `Rat.mul_inv_cancel`
    /// for the `4^n`-cancellation. Proven by composing the existing
    /// `Rat.natCast_ne_zero_of_pos` at `2^n` with the `Nat.one_le_two_pow`
    /// positivity witness. Kernel-checked, `Constructive`. Idempotent.
    pub fn register_two_pow_rat_ne_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.two_pow_rat_ne_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_expect_one_theorems()?; // natCast_ne_zero_of_pos, one_le_two_pow

        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this theorem transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = NpConsts::new();
        let false_ = Expr::const_(Name::from_string("False"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let d = c.denom(&n);
            let hyp = c.eq_rat(d, c.order.rat_zero.clone());
            let concl = Expr::pi(BinderInfo::Default, hyp, false_.clone());
            b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
        };

        // value: fun n => Rat.natCast_ne_zero_of_pos (2^n) (Nat.one_le_two_pow n)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let one_le = Expr::app(
                Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]),
                n.clone(),
            );
            let body = Expr::apps(
                Expr::const_(Name::from_string("Rat.natCast_ne_zero_of_pos"), vec![]),
                [c.pow2(&n), one_le],
            );
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// **Deliverable 1' (corollary).** `BoolAnalysis.fourier_mass_eq_one :
    ///   ∀ (n) (f : BoolFn n), subsetSum n (fun S => f̂ S · f̂ S) = Rat.one`
    ///
    /// The Parseval normalization `Σ_S f̂(S)² = 1`. Since `pm` is `{+1,-1}`-valued,
    /// `pm (f x) · pm (f x) = 1` pointwise (`pm_mul_self`), so the un-normalized
    /// total `Expect n (fun x => pm·pm) = Expect n (fun _ => 1) = 1`
    /// (`Expect_congr` ∘ `Expect_const_one`). Chained against
    /// `expect_pm_sq_eq_fourier_mass` (item 1):
    /// `Σ_S f̂² = Expect n (pm·pm) = 1`. Kernel-checked, `Constructive`, empty
    /// closure. Idempotent.
    pub fn register_fourier_mass_eq_one(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.fourier_mass_eq_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis()?; // Expect, FourierCoefficient, pm, Expect_congr, Expect_const_one
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_pm_mul_self_theorem()?;
        self.register_expect_congr_theorem()?;
        self.register_expect_one_theorems()?;
        self.register_subset_sum()?;
        self.register_expect_pm_sq_eq_fourier_mass()?;

        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this theorem transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = NpConsts::new();
        let pm_mul_self = Expr::const_(Name::from_string("BoolAnalysis.pm_mul_self"), vec![]);
        let expect_congr = Expr::const_(Name::from_string("BoolAnalysis.Expect_congr"), vec![]);
        let expect_const_one =
            Expr::const_(Name::from_string("BoolAnalysis.Expect_const_one"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let lhs = c.subset_sum_of(&n, c.fourier_sq_fn(&b, &n, &f));
            let concl = c.eq_rat(lhs, c.one());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let pm_sq = c.pm_sq(&b, &n, &f); // fun x => pm(f x)·pm(f x)
            let const_one = c.const_one_fn(&b, &n); // fun _ => Rat.one
            let s0 = c.subset_sum_of(&n, c.fourier_sq_fn(&b, &n, &f)); // Σ f̂²
            let e_pm = c.expect_of(&n, pm_sq.clone()); // Expect (pm·pm)
            let e_one = c.expect_of(&n, const_one.clone()); // Expect (const 1)
            let one = c.one();

            // h0 : Σ f̂² = Expect (pm·pm)   (symm of item 1)
            let item1 = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.expect_pm_sq_eq_fourier_mass"),
                    vec![],
                ),
                [n.clone(), f.clone()],
            ); // Expect (pm·pm) = Σ f̂²
            let h0 = c.symm(e_pm.clone(), s0.clone(), item1);

            // pw : ∀ x, pm(f x)·pm(f x) = 1   := fun x => pm_mul_self (f x)
            let pw = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (x_id, x) = ch.fresh_local(hcp.clone());
                let body = Expr::app(pm_mul_self.clone(), Expr::app(f.clone(), x));
                ch.finish_child(ch.mk_lam(x_id, BinderInfo::Default, hcp, body))
            };
            // h1 : Expect (pm·pm) = Expect (const 1)   (Expect_congr n pm_sq const_one pw)
            let h1 = Expr::apps(
                expect_congr.clone(),
                [n.clone(), pm_sq.clone(), const_one.clone(), pw],
            );
            // h2 : Expect (const 1) = 1   (Expect_const_one n)
            let h2 = Expr::app(expect_const_one.clone(), n.clone());

            // chain : Σ f̂² = Expect(pm·pm) = Expect(const1) = 1
            let h01 = c.trans(s0.clone(), e_pm.clone(), e_one.clone(), h0, h1);
            let body = c.trans(s0, e_one, one, h01, h2);

            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_normparseval()
            .expect("init_boolean_analysis_kkl_normparseval");
        env.init_boolean_analysis_kkl_normparseval()
            .expect("idempotent");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty"
        );
    }

    #[test]
    fn test_two_pow_rat_ne_zero_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.two_pow_rat_ne_zero");
    }

    #[test]
    fn test_fourier_sq_regroup_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.fourier_sq_regroup");
    }

    #[test]
    fn test_inv_sq_mul_mul_cancel_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.inv_sq_mul_mul_cancel");
    }

    #[test]
    fn test_expect_pm_sq_eq_fourier_mass_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.expect_pm_sq_eq_fourier_mass");
    }

    #[test]
    fn test_fourier_mass_eq_one_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.fourier_mass_eq_one");
    }
}
