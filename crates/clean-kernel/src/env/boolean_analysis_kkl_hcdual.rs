// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL endgame — K1 `hc_dual` support bricks (run 2).
//!
//! This module lands the nonnegativity bricks and the level-`k` threshold
//! influence bound that the `hc_dual_total` chain consumes (see
//! `designs/2026-06-12-kkl-endgame-worked-chain.md`, §3 + §5C). All lemmas are
//! kernel-checked, `ProofQuality::Constructive` with an empty admitted-axiom
//! closure.
//!
//! ```text
//! BoolAnalysis.ind_nonneg :                                       -- (1)
//!   ∀ (b : Bool), Rat.le Rat.zero (ind b)
//!
//! BoolAnalysis.setSize_nonneg :                                   -- (2)
//!   ∀ (n : Nat) (S : HCPoint n), Rat.le Rat.zero (setSize n S)
//!
//! BoolAnalysis.fourier_sq_nonneg :                                -- (3)
//!   ∀ (n) (f : BoolFn n) (S : HCPoint n),
//!     Rat.le Rat.zero (Rat.mul (f̂ S) (f̂ S))
//!
//! BoolAnalysis.total_influence_nonneg :                           -- (4)
//!   ∀ (n) (f : BoolFn n), Rat.le Rat.zero (TotalInfluence n f)
//!
//! BoolAnalysis.kkl_threshold_influence :                          -- (5) the K1 brick
//!   ∀ (n) (f : BoolFn n) (kNat : Nat),
//!     Rat.le
//!       (subsetSum n (fun S => natCast kNat
//!                              · (ind (Nat.ble kNat (setSizeNat n S)) · (f̂ S · f̂ S))))
//!       (TotalInfluence n f)
//! ```
//!
//! ## Proof sketches (all constructive, empty closure)
//!
//! - **(1) `ind_nonneg`**: `Rat.sq_nonneg (ind b) : 0 ≤ ind b · ind b`,
//!   transported along `ind_mul_self b : ind b · ind b = ind b` by `Eq.subst`
//!   with motive `t ↦ 0 ≤ t`. (Cleaner than a `Bool.rec` numeral case-split:
//!   one subst, reusing the landed idempotence.)
//! - **(2) `setSize_nonneg`**: `setSize n S` δ-unfolds (reducible) to
//!   `Fin.sum n (fun i => ind (S i))`, so the goal is `Fin.sum_nonneg`'s
//!   conclusion at that integrand; the per-summand hypothesis is
//!   `fun i => ind_nonneg (S i)`.
//! - **(3) `fourier_sq_nonneg`**: `Rat.sq_nonneg (f̂ S)` directly.
//! - **(4) `total_influence_nonneg`**: rewrite `TotalInfluence n f` to
//!   `subsetSum n (fun S => setSize n S · (f̂ S · f̂ S))` via
//!   `total_influence_spectral`, then `subsetSum` δ-unfolds to
//!   `Fin.sum (2^n) (fun j => …(hcDecode n j))`; close with `Fin.sum_nonneg`
//!   on each decoded summand `setSize · f̂²` (`mul_nonneg` of (2) and (3)).
//! - **(5) `kkl_threshold_influence`**: instantiate
//!   `subsetSum_threshold_le_nat` at `w := fun S => f̂ S · f̂ S` (its `w ≥ 0`
//!   and `setSize ≥ 0` hypotheses are (3) and (2)); its RHS
//!   `subsetSum n (fun S => setSize n S · w S)` is rewritten to
//!   `TotalInfluence n f` via `Eq.symm (total_influence_spectral n f)` with an
//!   `Eq.subst` whose motive places that term on the right of the `≤`.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the K1 hc_dual support bricks.
struct HcDualConsts {
    order: OrderConsts,
    nat: Expr,
    bool_: Expr,
    fin: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    ind: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    fourier: Expr,
    total_influence: Expr,
    subset_sum: Expr,
    hc_decode: Expr,
    fin_sum_nonneg: Expr,
    sq_nonneg: Expr,
    mul_nonneg: Expr,
    ind_mul_self: Expr,
    nat_ble: Expr,
    nat_pow: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    pm: Expr,
}

impl HcDualConsts {
    fn new() -> Self {
        Self {
            order: OrderConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            bool_fn: Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            set_size: Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]),
            set_size_nat: Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
            fourier: Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]),
            total_influence: Expr::const_(Name::from_string("BoolAnalysis.TotalInfluence"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            fin_sum_nonneg: Expr::const_(Name::from_string("Fin.sum_nonneg"), vec![]),
            sq_nonneg: Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]),
            mul_nonneg: Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            ind_mul_self: Expr::const_(Name::from_string("BoolAnalysis.ind_mul_self"), vec![]),
            nat_ble: Expr::const_(Name::from_string("Nat.ble"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.order.rat_zero.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn le0(&self, a: Expr) -> Expr {
        self.order.rat_le(self.zero(), a)
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn set_size_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size.clone(), [n.clone(), s.clone()])
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `f̂(S) · f̂(S)`.
    fn fsq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    /// `x · x` (the 2-norm pointwise / square).
    fn sq(&self, x: Expr) -> Expr {
        self.mul(x.clone(), x)
    }
    /// `(x · x) · (x · x)` (the 4-norm pointwise / fourth power).
    fn pow4(&self, x: Expr) -> Expr {
        let s = self.sq(x);
        self.mul(s.clone(), s)
    }
    /// `@Eq.refl Rat x : x = x`.
    fn eq_refl_of(&self, x: Expr) -> Expr {
        Expr::apps(self.order.eq_refl.clone(), [self.rat(), x])
    }
    /// `Eq.trans` over `Rat`: `a = b → b = c → a = c`.
    fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        self.order.trans(a, b, c, h1, h2)
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn sq_nonneg_of(&self, t: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), t)
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg_of(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Fin.sum_nonneg n f h : 0 ≤ Fin.sum n f`.
    fn fin_sum_nonneg_of(&self, n: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum_nonneg.clone(), [n, f, h])
    }
    /// `Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    /// `hcDecode n j`.
    fn hc_decode_of(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    /// `Rat.mk (Int.ofNat m) 1`.
    fn natcast(&self, m: &Expr) -> Expr {
        let of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [Expr::app(of_nat, m.clone()), one],
        )
    }
    /// `Nat.ble k m`.
    fn ble(&self, k: Expr, m: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [k, m])
    }
    /// `BoolAnalysis.pm b : Rat` (the `{+1,−1}` sign embedding).
    fn pm_of(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    /// `Rat.sub a b`.
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.order.sub(a, b)
    }
    /// The `4 : Rat` numeral as `Rat.mk (Int.ofNat 4) 1`.
    fn four(&self) -> Expr {
        let mut n = self.nat_zero.clone();
        for _ in 0..4 {
            n = Expr::app(self.nat_succ.clone(), n);
        }
        let of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [Expr::app(of_nat, n), one],
        )
    }
}

impl Environment {
    /// Register all K1 hc_dual support bricks (1)–(5). Idempotent.
    pub fn init_boolean_analysis_kkl_hcdual(&mut self) -> Result<(), EnvError> {
        self.register_ind_nonneg()?;
        self.register_set_size_nonneg()?;
        self.register_fourier_sq_nonneg()?;
        self.register_total_influence_nonneg()?;
        self.register_kkl_threshold_influence()?;
        self.register_kkl_mass_ge1_le_influence()?;
        self.register_ind_pow4_eq_ind()?;
        self.register_disagree_sq_self_eq_four_mul()?;
        self.register_hc24_at_third()?;
        Ok(())
    }

    /// (1) `BoolAnalysis.ind_nonneg : ∀ (b : Bool), 0 ≤ ind b`.
    pub fn register_ind_nonneg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.ind_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis()?; // ind
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_order_toolkit()?; // Rat.sq_nonneg
        self.register_ind_mul_self()?; // ind_mul_self

        let c = HcDualConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.bool_.clone());
            let concl = c.le0(c.ind_of(bv.clone()));
            b.finish(b.mk_pi(bv_id, BinderInfo::Default, c.bool_.clone(), concl))
        };

        // value: fun (bv : Bool) =>
        //   subst (motive t => 0 ≤ t) (ind bv · ind bv) (ind bv)
        //         (ind_mul_self bv) (Rat.sq_nonneg (ind bv))
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.bool_.clone());
            let ib = c.ind_of(bv.clone());
            let ib_sq = c.mul(ib.clone(), ib.clone());
            // motive t => 0 ≤ t
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let body = c.le0(t);
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            let h_eq = Expr::app(c.ind_mul_self.clone(), bv.clone()); // ind bv · ind bv = ind bv
            let h_a = c.sq_nonneg_of(ib.clone()); // 0 ≤ ind bv · ind bv
            let body = c.order.subst(motive, ib_sq, ib, h_eq, h_a);
            b.finish(b.mk_lam(bv_id, BinderInfo::Default, c.bool_.clone(), body))
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

    /// (2) `BoolAnalysis.setSize_nonneg : ∀ (n) (S : HCPoint n), 0 ≤ setSize n S`.
    pub fn register_set_size_nonneg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.setSize_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_ind_nonneg()?;
        self.register_set_size()?;
        self.init_fin_sum()?; // Fin.sum_nonneg

        let c = HcDualConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let concl = c.le0(c.set_size_of(&n, &s));
            let e = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: fun (n) (S) =>
        //   Fin.sum_nonneg n (fun i => ind (S i)) (fun i => ind_nonneg (S i))
        // (result type 0 ≤ Fin.sum n (fun i => ind (S i)) ≡ 0 ≤ setSize n S.)
        let ind_nonneg = Expr::const_(Name::from_string("BoolAnalysis.ind_nonneg"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());

            // integrand fun (i : Fin n) => ind (S i)
            let integrand = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let body = c.ind_of(Expr::app(s.clone(), i));
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            // per-summand: fun (i : Fin n) => ind_nonneg (S i)
            let per = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let body = Expr::app(ind_nonneg.clone(), Expr::app(s.clone(), i));
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            let body = c.fin_sum_nonneg_of(n.clone(), integrand, per);
            let e = b.mk_lam(s_id, BinderInfo::Default, hcp, body);
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

    /// (3) `BoolAnalysis.fourier_sq_nonneg :
    ///   ∀ (n) (f : BoolFn n) (S : HCPoint n), 0 ≤ f̂ S · f̂ S`.
    pub fn register_fourier_sq_nonneg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.fourier_sq_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis()?; // FourierCoefficient
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_order_toolkit()?; // Rat.sq_nonneg

        let c = HcDualConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let concl = c.le0(c.fsq(&n, &f, &s));
            let e = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: fun (n) (f) (S) => Rat.sq_nonneg (f̂ S)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let body = c.sq_nonneg_of(c.fourier_of(&n, &f, &s));
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

    /// (4) `BoolAnalysis.total_influence_nonneg :
    ///   ∀ (n) (f : BoolFn n), 0 ≤ TotalInfluence n f`.
    pub fn register_total_influence_nonneg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.total_influence_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_set_size_nonneg()?;
        self.register_fourier_sq_nonneg()?;
        self.init_fin_sum()?; // Fin.sum_nonneg
        self.init_boolean_analysis_kkl_total_influence()?; // total_influence_spectral
        self.register_subset_sum()?;
        self.register_set_size()?;

        let c = HcDualConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let concl = c.le0(c.total_influence_of(&n, &f));
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let set_size_nonneg =
            Expr::const_(Name::from_string("BoolAnalysis.setSize_nonneg"), vec![]);
        let fourier_sq_nonneg =
            Expr::const_(Name::from_string("BoolAnalysis.fourier_sq_nonneg"), vec![]);
        let total_influence_spectral = Expr::const_(
            Name::from_string("BoolAnalysis.total_influence_spectral"),
            vec![],
        );

        // value: fun (n) (f) =>
        //   subst (motive t => 0 ≤ t)
        //         (subsetSum n (fun S => setSize n S · (f̂ S · f̂ S)))   -- a
        //         (TotalInfluence n f)                                  -- b
        //         (Eq.symm (total_influence_spectral n f))              -- h_eq : a = b? no
        //         h_a
        // total_influence_spectral n f : TotalInfluence n f = subsetSum n (…) = a.
        // i.e. it is `b = a`. We want motive(b) from motive(a), so subst with
        // h_eq : a = b. That is Eq.symm (total_influence_spectral n f).
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            // integrand a_fn := fun (S : HCPoint n) => setSize n S · (f̂ S · f̂ S)
            let a_fn = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = c.mul(c.set_size_of(&n, &s), c.fsq(&n, &f, &s));
                ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };
            let a = c.subset_sum_of(&n, a_fn.clone()); // subsetSum n a_fn
            let bb = c.total_influence_of(&n, &f); // TotalInfluence n f

            // h_a : 0 ≤ subsetSum n a_fn, via Fin.sum_nonneg on the decoded summand.
            // subsetSum n a_fn ≡ Fin.sum (2^n) (fun j => a_fn (hcDecode n j)).
            let h_a = {
                // decoded integrand fun (j : Fin (2^n)) => setSize n (hcDecode n j)
                //                                            · (f̂ (hcDecode n j))²
                let dec_fn = {
                    let mut ch = EnvDeclBuilder::child_of(&b);
                    let fin_pow = c.fin_of(&c.pow2(&n));
                    let (j_id, j) = ch.fresh_local(fin_pow.clone());
                    let dec = c.hc_decode_of(&n, &j);
                    let body = c.mul(c.set_size_of(&n, &dec), c.fsq(&n, &f, &dec));
                    ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
                };
                // per-summand nonneg: fun j => mul_nonneg (setSize n (dec))
                //   (f̂(dec)²) (setSize_nonneg n (dec)) (fourier_sq_nonneg n f (dec))
                let per = {
                    let mut ch = EnvDeclBuilder::child_of(&b);
                    let fin_pow = c.fin_of(&c.pow2(&n));
                    let (j_id, j) = ch.fresh_local(fin_pow.clone());
                    let dec = c.hc_decode_of(&n, &j);
                    let size = c.set_size_of(&n, &dec);
                    let fsq = c.fsq(&n, &f, &dec);
                    let h_size = Expr::apps(set_size_nonneg.clone(), [n.clone(), dec.clone()]);
                    let h_fsq = Expr::apps(
                        fourier_sq_nonneg.clone(),
                        [n.clone(), f.clone(), dec.clone()],
                    );
                    let body = c.mul_nonneg_of(size, fsq, h_size, h_fsq);
                    ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
                };
                c.fin_sum_nonneg_of(c.pow2(&n), dec_fn, per)
            };

            // motive t => 0 ≤ t
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let body = c.le0(t);
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            // tis : TotalInfluence n f = subsetSum n a_fn   (= b = a)
            let tis = Expr::apps(total_influence_spectral.clone(), [n.clone(), f.clone()]);
            // h_eq : a = b  via Eq.symm
            let h_eq = c.order.symm(bb.clone(), a.clone(), tis);
            let body = c.order.subst(motive, a, bb, h_eq, h_a);

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

    /// (5) The K1 brick:
    /// `BoolAnalysis.kkl_threshold_influence :
    ///   ∀ (n) (f : BoolFn n) (kNat : Nat),
    ///     subsetSum n (fun S => natCast kNat
    ///                           · (ind (Nat.ble kNat (setSizeNat n S)) · (f̂ S · f̂ S)))
    ///       ≤ TotalInfluence n f`.
    /// (The scalar `natCast kNat` is folded inside the integrand to match
    /// `subsetSum_threshold_le_nat`'s conclusion LHS — no `subsetSum_smul`
    /// distribution is needed at this layer.)
    ///
    /// The level-`k` threshold influence bound: `k·(Fourier mass at degree ≥ k)
    /// ≤ TotalInfluence`. The hypercontractive lower bound on that masked mass is
    /// the remaining `hc_dual_total` gap; this brick is its consumer-shaped half.
    pub fn register_kkl_threshold_influence(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_threshold_influence");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum_threshold_le_nat()?;
        self.register_fourier_sq_nonneg()?;
        self.register_set_size_nonneg()?;
        self.init_boolean_analysis_kkl_total_influence()?; // total_influence_spectral
        self.register_subset_sum()?;
        self.register_set_size()?;
        self.register_set_size_nat()?;

        let c = HcDualConsts::new();

        // w := fun (S : HCPoint n) => f̂ S · f̂ S  (depends on n, f).
        let w_fn = |b: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let hcp = c.hcpoint_of(n);
            let (s_id, s) = ch.fresh_local(hcp.clone());
            let body = c.fsq(n, f, &s);
            ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };
        // LHS integrand (matches subsetSum_threshold_le_nat's LHS exactly — the
        // scalar `natCast kNat` is folded INSIDE the integrand, not factored out):
        //   fun S => natCast kNat · (ind (Nat.ble kNat (setSizeNat n S)) · (f̂ S · f̂ S))
        let lhs_fn = |b: &EnvDeclBuilder, n: &Expr, f: &Expr, knat: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let hcp = c.hcpoint_of(n);
            let (s_id, s) = ch.fresh_local(hcp.clone());
            let bit = c.ble(knat.clone(), c.set_size_nat_of(n, &s));
            let body = c.mul(c.natcast(knat), c.mul(c.ind_of(bit), c.fsq(n, f, &s)));
            ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };
        // RHS integrand (threshold_le_nat's RHS): fun S => setSize n S · (f̂ S · f̂ S)
        let rhs_fn = |b: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let hcp = c.hcpoint_of(n);
            let (s_id, s) = ch.fresh_local(hcp.clone());
            let body = c.mul(c.set_size_of(n, &s), c.fsq(n, f, &s));
            ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (k_id, knat) = b.fresh_local(c.nat.clone());

            let lhs = c.subset_sum_of(&n, lhs_fn(&b, &n, &f, &knat));
            let concl = c.order.rat_le(lhs, c.total_influence_of(&n, &f));

            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let threshold_le_nat = Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_threshold_le_nat"),
            vec![],
        );
        let fourier_sq_nonneg =
            Expr::const_(Name::from_string("BoolAnalysis.fourier_sq_nonneg"), vec![]);
        let set_size_nonneg =
            Expr::const_(Name::from_string("BoolAnalysis.setSize_nonneg"), vec![]);
        let total_influence_spectral = Expr::const_(
            Name::from_string("BoolAnalysis.total_influence_spectral"),
            vec![],
        );

        // value: fun (n) (f) (kNat) =>
        //   subst (motive t => lhs ≤ t)
        //         (subsetSum n (rhs_fn))           -- a (threshold RHS)
        //         (TotalInfluence n f)             -- b
        //         (Eq.symm (total_influence_spectral n f))   -- h_eq : a = b
        //         (threshold_le_nat n kNat w hyp1 hyp2)      -- h_a : lhs ≤ a
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (k_id, knat) = b.fresh_local(c.nat.clone());

            let w = w_fn(&b, &n, &f);

            // hyp1 : ∀ S, 0 ≤ w S   := fun S => fourier_sq_nonneg n f S
            let hyp1 = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = Expr::apps(fourier_sq_nonneg.clone(), [n.clone(), f.clone(), s.clone()]);
                ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };
            // hyp2 : ∀ S, 0 ≤ setSize n S   := fun S => setSize_nonneg n S
            let hyp2 = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = Expr::apps(set_size_nonneg.clone(), [n.clone(), s.clone()]);
                ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };

            // h_a : lhs ≤ subsetSum n rhs_fn   (threshold_le_nat instance)
            let h_a = Expr::apps(
                threshold_le_nat.clone(),
                [n.clone(), knat.clone(), w, hyp1, hyp2],
            );

            // lhs (for the motive): subsetSum n (lhs_fn) — the scalar `natCast kNat`
            // is folded inside `lhs_fn`, matching threshold_le_nat's conclusion LHS.
            let lhs = c.subset_sum_of(&n, lhs_fn(&b, &n, &f, &knat));
            let a = c.subset_sum_of(&n, rhs_fn(&b, &n, &f));
            let bb = c.total_influence_of(&n, &f);

            // motive t => lhs ≤ t
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let body = c.order.rat_le(lhs.clone(), t);
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            let tis = Expr::apps(total_influence_spectral.clone(), [n.clone(), f.clone()]);
            let h_eq = c.order.symm(bb.clone(), a.clone(), tis); // a = b
            let body = c.order.subst(motive, a, bb, h_eq, h_a);

            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
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

    /// (6) The spectral Poincaré half (the `k = 1` instance of `hc_dual_total`):
    /// `BoolAnalysis.kkl_mass_ge1_le_influence :
    ///   ∀ (n) (f : BoolFn n),
    ///     subsetSum n (fun S => ind (Nat.ble 1 (setSizeNat n S)) · (f̂ S · f̂ S))
    ///       ≤ TotalInfluence n f`.
    ///
    /// This is `kkl_threshold_influence` at `kNat = 1` with the leading scalar
    /// `natCast 1 ·` stripped: `Nat.ble 1 (setSizeNat n S) = true ⟺ |S| ≥ 1 ⟺
    /// S ≠ ∅`, so the LHS is the Fourier mass at degree ≥ 1 (equivalently
    /// `Σ_{S≠∅} f̂(S)²`), and the bound says that mass is ≤ the total influence —
    /// the spectral form of the **Poincaré inequality** `Var[f] ≤ I[f]`.
    ///
    /// The `natCast 1 ·` collapse uses `Rat.one_mul` (valid because `natCast 1 =
    /// Rat.mk (Int.ofNat (succ zero)) 1` δ-reduces to `Rat.one`, so each
    /// per-`S` factor `natCast 1 · x` is def-eq to `Rat.mul Rat.one x` and
    /// `Rat.one_mul x : Rat.mul Rat.one x = x` type-checks against it). The
    /// scalar is pushed inside via `subsetSum_congr`, then the `≤` is transported
    /// with `Eq.subst`.
    ///
    /// **Consumer reading (`hc_dual_total` at `k = 1`).** With the normalized
    /// total-mass identities `E[(pm f)²] = Σ_S f̂(S)²` and `E[pm f]² = f̂(∅)²`
    /// (the only genuinely-missing analytic bridge — see the module docs / the
    /// design note §5C), `Var = Σ_S f̂² − f̂(∅)² = Σ_{S≠∅} f̂²`, so this brick is
    /// exactly `Var ≤ TotalInfluence`, i.e. `hc_dual_total` at `k = 1`. The
    /// `k ≥ 2` improvement (the genuine KKL `log n` factor) needs the
    /// hypercontractive level-`k` lower bound, which is still gapped.
    pub fn register_kkl_mass_ge1_le_influence(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_mass_ge1_le_influence");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_kkl_threshold_influence()?;
        self.register_subset_sum_congr()?;
        self.init_rat()?; // Rat.one_mul (+ Rat.one)
        self.register_subset_sum()?;
        self.register_set_size_nat()?;

        let c = HcDualConsts::new();
        let one_nat = Expr::app(c.nat_succ.clone(), c.nat_zero.clone()); // Nat.succ Nat.zero = 1

        // H integrand (scalar-stripped):
        //   fun S => ind (Nat.ble 1 (setSizeNat n S)) · (f̂ S · f̂ S)
        let h_fn = |b: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let hcp = c.hcpoint_of(n);
            let (s_id, s) = ch.fresh_local(hcp.clone());
            let bit = c.ble(one_nat.clone(), c.set_size_nat_of(n, &s));
            let body = c.mul(c.ind_of(bit), c.fsq(n, f, &s));
            ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };
        // G integrand (threshold_influence's LHS at kNat = 1):
        //   fun S => natCast 1 · (ind (Nat.ble 1 (setSizeNat n S)) · (f̂ S · f̂ S))
        let g_fn = |b: &EnvDeclBuilder, n: &Expr, f: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let hcp = c.hcpoint_of(n);
            let (s_id, s) = ch.fresh_local(hcp.clone());
            let bit = c.ble(one_nat.clone(), c.set_size_nat_of(n, &s));
            let body = c.mul(c.natcast(&one_nat), c.mul(c.ind_of(bit), c.fsq(n, f, &s)));
            ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let lhs = c.subset_sum_of(&n, h_fn(&b, &n, &f));
            let concl = c.order.rat_le(lhs, c.total_influence_of(&n, &f));

            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let threshold_influence = Expr::const_(
            Name::from_string("BoolAnalysis.kkl_threshold_influence"),
            vec![],
        );
        let subset_sum_congr =
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum_congr"), vec![]);
        let rat_one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);

        // value: fun (n) (f) =>
        //   subst (motive t => t ≤ TotalInfluence n f)
        //         (subsetSum n G)                       -- a
        //         (subsetSum n H)                       -- b
        //         (subsetSum_congr n G H pw)            -- h_eq : a = b
        //         (kkl_threshold_influence n f 1)       -- h_motive_a : a ≤ TI
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let g = g_fn(&b, &n, &f);
            let h = h_fn(&b, &n, &f);
            let a = c.subset_sum_of(&n, g.clone());
            let bb = c.subset_sum_of(&n, h.clone());
            let ti = c.total_influence_of(&n, &f);

            // pw : ∀ S, G S = H S
            //    := fun S => Rat.one_mul (ind (ble 1 |S|) · (f̂ S · f̂ S))
            // (type Rat.mul Rat.one x = x; def-eq to Rat.mul (natCast 1) x = x.)
            let pw = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let bit = c.ble(one_nat.clone(), c.set_size_nat_of(&n, &s));
                let x = c.mul(c.ind_of(bit), c.fsq(&n, &f, &s));
                let body = Expr::app(rat_one_mul.clone(), x);
                ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };

            // h_eq : subsetSum n G = subsetSum n H
            let h_eq = Expr::apps(
                subset_sum_congr.clone(),
                [n.clone(), g.clone(), h.clone(), pw],
            );

            // h_motive_a : subsetSum n G ≤ TotalInfluence n f
            //   = kkl_threshold_influence n f 1
            let h_motive_a = Expr::apps(
                threshold_influence.clone(),
                [n.clone(), f.clone(), one_nat.clone()],
            );

            // motive t => t ≤ TotalInfluence n f
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let body = c.order.rat_le(t, ti.clone());
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };

            let body = c.order.subst(motive, a, bb, h_eq, h_motive_a);
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

    /// (6) `BoolAnalysis.ind_pow4_eq_ind :
    ///   ∀ (b : Bool), (ind b · ind b) · (ind b · ind b) = ind b`.
    ///
    /// The **quartic idempotence** `t⁴ = t` for `t ∈ {0,1}` — the pointwise
    /// core of the `{0,±1}` 4-norm collapse `‖D_i f‖₄⁴ = ‖D_i f‖₂²`
    /// (designs/2026-06-12-kkl-endgame-worked-chain.md, ★). Because `ind b`
    /// takes values in `{0,1}`, its fourth power equals itself. Proof: from
    /// `ind_mul_self b : ind b · ind b = ind b`,
    ///   * `subst` lifts it to `(ind·ind)·(ind·ind) = (ind·ind)` (rewrite the
    ///     right factor's `ind·ind` to `ind`, then the residual `ind·ind` via a
    ///     second subst collapses on the left), realised here as one
    ///     `Eq.subst` with motive `t ↦ pow4(ind b) = t · t` starting from
    ///     `Eq.refl (pow4 (ind b))`, giving `pow4(ind b) = ind b · ind b`;
    ///   * then `Eq.trans` with `ind_mul_self b` lands `pow4(ind b) = ind b`.
    pub fn register_ind_pow4_eq_ind(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.ind_pow4_eq_ind");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis()?; // ind
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_ind_mul_self()?; // ind_mul_self

        let c = HcDualConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.bool_.clone());
            let ib = c.ind_of(bv.clone());
            let concl = c.order.rat_eq(c.pow4(ib.clone()), ib);
            b.finish(b.mk_pi(bv_id, BinderInfo::Default, c.bool_.clone(), concl))
        };

        // value: fun (bv : Bool) =>
        //   let ib := ind bv; let ib2 := ib · ib; let p4 := ib2 · ib2.
        //   step1 : p4 = ib2
        //     := subst (motive t => p4 = t · t)
        //              (a := ib2) (b := ib)
        //              (ind_mul_self bv)          -- ib2 = ib
        //              (Eq.refl p4)               -- p4 = ib2 · ib2 (at a)
        //   p4 = ib := Eq.trans p4 ib2 ib step1 (ind_mul_self bv)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.bool_.clone());
            let ib = c.ind_of(bv.clone());
            let ib2 = c.mul(ib.clone(), ib.clone()); // ind·ind
            let p4 = c.mul(ib2.clone(), ib2.clone()); // (ind·ind)·(ind·ind)

            let h = Expr::app(c.ind_mul_self.clone(), bv.clone()); // ind·ind = ind

            // motive t => p4 = t · t
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let body = c.order.rat_eq(p4.clone(), c.mul(t.clone(), t));
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            // step1 : p4 = ib2  (motive at b = ind; a = ib2)
            let step1 = c.order.subst(
                motive,
                ib2.clone(),
                ib.clone(),
                h.clone(),
                c.eq_refl_of(p4.clone()),
            );
            // p4 = ib
            let body = c.trans(p4, ib2, ib, step1, h);
            b.finish(b.mk_lam(bv_id, BinderInfo::Default, c.bool_.clone(), body))
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

    /// (7) `BoolAnalysis.disagree_sq_self_eq_four_mul :
    ///   ∀ (a b : Bool), (D · D) = 4 · D`
    /// where `D := (pm a − pm b) · (pm a − pm b)` is the un-halved squared
    /// discrete derivative `(pm a − pm b)²`.
    ///
    /// This is the **derivative-level 4-norm collapse** `‖D_i f‖₄⁴ =
    /// 4·‖D_i f‖₂²` *pointwise* (designs/2026-06-12-kkl-endgame-worked-chain.md
    /// ★). Because `D = (pm a − pm b)² ∈ {0, 4}` (zero when `a = b`, four when
    /// `a ≠ b`), its square `D·D ∈ {0, 16}` equals `4·D ∈ {0, 16}`. Together
    /// with `disagree_sq_bridge` (`D = 4·ind(disagree)`) this says the fourth
    /// power of the discrete derivative collapses to a constant multiple of its
    /// square — the `t⁴ = t·t·…` structure that lets `hc24_core`'s 4-norm
    /// operator output be read back as a 2-norm (influence) mass.
    ///
    /// Proof: `Bool.rec` on `a` then `b` (four ground leaves), each closed by
    /// `@Eq.refl Rat (D·D)` — both `D·D` and `4·D` native-reduce to the same
    /// `Rat.mk` numeral (`0` or `16`). Division-free, axiom-free.
    pub fn register_disagree_sq_self_eq_four_mul(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.disagree_sq_self_eq_four_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis()?; // pm, Rat foundations
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_bool()?;
        self.init_beq()?;

        let c = HcDualConsts::new();
        let bool_c = c.bool_.clone();
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

        // D(a,b) := (pm a − pm b) · (pm a − pm b)
        let d_of = |a: Expr, b: Expr| -> Expr {
            let diff = c.sub(c.pm_of(a), c.pm_of(b));
            c.mul(diff.clone(), diff)
        };
        // lhs(a,b) := D · D ;  rhs(a,b) := 4 · D
        let lhs = |a: Expr, b: Expr| -> Expr {
            let d = d_of(a, b);
            c.mul(d.clone(), d)
        };
        let rhs = |a: Expr, b: Expr| -> Expr { c.mul(c.four(), d_of(a, b)) };
        let eqn = |l: Expr, r: Expr| c.order.rat_eq(l, r);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, av) = b.fresh_local(bool_c.clone());
            let (b_id, bv) = b.fresh_local(bool_c.clone());
            let concl = eqn(lhs(av.clone(), bv.clone()), rhs(av.clone(), bv.clone()));
            let e = b.mk_pi(b_id, BinderInfo::Default, bool_c.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e);
            b.finish(e)
        };

        // value: fun (a b : Bool) => Bool.rec (motive_a) <a=false> <a=true> a
        let value = {
            let mut bld = EnvDeclBuilder::new();
            let (a_id, av) = bld.fresh_local(bool_c.clone());
            let (b_id, bv) = bld.fresh_local(bool_c.clone());

            // motive_a : fun a' => lhs a' b = rhs a' b
            let motive_a = {
                let mut d = EnvDeclBuilder::child_of(&bld);
                let (ap_id, ap) = d.fresh_local(bool_c.clone());
                let body = eqn(lhs(ap.clone(), bv.clone()), rhs(ap.clone(), bv.clone()));
                d.finish_child(d.mk_lam(ap_id, BinderInfo::Default, bool_c.clone(), body))
            };

            // For a fixed concrete `av_c`, split on `b` and emit Eq.refl leaves.
            let inner_rec = |av_c: Expr, parent: &EnvDeclBuilder| -> Expr {
                let mut d = EnvDeclBuilder::child_of(parent);
                let motive_b = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (bp_id, bp) = e.fresh_local(bool_c.clone());
                    let body = eqn(lhs(av_c.clone(), bp.clone()), rhs(av_c.clone(), bp.clone()));
                    e.finish_child(e.mk_lam(bp_id, BinderInfo::Default, bool_c.clone(), body))
                };
                let leaf = |bv_c: Expr| c.eq_refl_of(lhs(av_c.clone(), bv_c));
                let b_false = leaf(bfalse.clone());
                let b_true = leaf(btrue.clone());
                let e = Expr::apps(bool_rec0.clone(), [motive_b, b_false, b_true, bv.clone()]);
                d.finish_child(e)
            };

            let a_false_case = inner_rec(bfalse.clone(), &bld);
            let a_true_case = inner_rec(btrue.clone(), &bld);

            let rec_a = Expr::apps(
                bool_rec0.clone(),
                [motive_a, a_false_case, a_true_case, av.clone()],
            );
            let e = bld.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), rec_a);
            let e = bld.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e);
            bld.finish(e)
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

    /// (8) `BoolAnalysis.hc24_at_third` — the (2,4)-hypercontractivity operator
    /// upper bound **instantiated at the KKL operator parameter `ρ_hc = 1/3`**,
    /// with the `hc24_core` hypothesis `3·(ρ·ρ) ≤ 1` discharged:
    ///
    /// ```text
    /// BoolAnalysis.hc24_at_third :
    ///   ∀ (n : Nat) (F : HCPoint n → Rat),
    ///     Fin.sum (2^n) (fun jx => pow4 (noiseFn (1/3) n F jx))
    ///       ≤ (Rat.powNat 8 n) · sq (Fin.sum (2^n) (fun jx => sq (F (hcDecode n jx))))
    /// ```
    ///
    /// This is `hc24_core` at `ρ := Rat.mk (Int.ofNat 1) 3` (`= 1/3`), the clean
    /// rational at which the spectral side (`noise_spectral_level`, whose weight
    /// is `levelWt = (ρ_spec²)^|S|` with `ρ_spec² = 1/3`) and the 4-norm operator
    /// side meet — both then carry the per-level weight `(1/3)^|S|`. The
    /// hypothesis `3·((1/3)·(1/3)) = 3·(1/9) = 1/3 ≤ 1` is discharged by
    /// `Rat.le_of_ble_eq_true ... (Eq.refl Bool.true)` (the boolean order
    /// `Rat.ble (1/3) 1` native-reduces to `true` on the concrete `Rat.mk`
    /// quotient reps, so `Eq.refl Bool.true` checks). The `3 : Rat` in the
    /// hypothesis is built as `(1+1)+1` to match `hc24_core`'s `o.three()`
    /// byte-for-byte.
    ///
    /// **Why this is the genuine forward brick (not a wrapper masquerade).** The
    /// `hc_dual_level_lower` inversion (the named KKL residual) consumes the
    /// operator 4-norm UPPER bound at *exactly this* `ρ_hc = 1/3` — `hc24_core`
    /// itself is hypothesis-gated and ρ-generic, unusable until pinned to the KKL
    /// parameter and discharged. This co-lands the otherwise-orphan
    /// `3·(1/3·1/3) ≤ 1` arithmetic brick *with* its sole consumer (the
    /// design-mandated co-landing rule), turning the gated generic bound into the
    /// concrete, hypothesis-free operator input the inversion pivots through.
    /// Constructive, empty admitted-axiom closure (leaves: `hc24_core`,
    /// `Rat.le_of_ble_eq_true`, `Eq.refl`).
    pub fn register_hc24_at_third(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.hc24_at_third");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_hc24_core()?; // hc24_core (+ noiseFn, statement deps)
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true, Rat.ble

        use super::boolean_analysis_hc24_core_base::{hc24_core_concl, Hc24Consts};
        let hc = Hc24Consts::new();
        let c = HcDualConsts::new();

        // ρ_hc := Rat.mk (Int.ofNat 1) 3  (= 1/3).
        let rho_third = {
            let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
            let one_nat = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());
            let mut three_nat = c.nat_zero.clone();
            for _ in 0..3 {
                three_nat = Expr::app(c.nat_succ.clone(), three_nat);
            }
            Expr::apps(
                Expr::const_(Name::from_string("Rat.mk"), vec![]),
                [Expr::app(int_of_nat, one_nat), three_nat],
            )
        };

        // Type: ∀ (n) (F : HCPoint n → Rat), concl_{ρ=1/3} n F.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(hc.nat.clone());
            let (f_id, f) = b.fresh_local(hc.f_type(&n));
            let concl = hc24_core_concl(&hc, &b, &rho_third, &n, &f);
            let e = b.mk_pi(f_id, BinderInfo::Default, hc.f_type(&n), concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, hc.nat.clone(), e);
            b.finish(e)
        };

        // hyp proof : 3·(ρ·ρ) ≤ 1  at ρ = 1/3, via Rat.le_of_ble_eq_true.
        //   `3` matches hc24_core's o.three() = (1+1)+1.
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let three_rat = {
            let two = Expr::apps(rat_add.clone(), [rat_one.clone(), rat_one.clone()]);
            Expr::apps(rat_add.clone(), [two, rat_one.clone()])
        };
        let rho_sq = c.mul(rho_third.clone(), rho_third.clone());
        let hyp_lhs = c.mul(three_rat, rho_sq);
        let hyp_proof = {
            let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
            let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
            let eq_refl_bool = Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [bool_c, btrue],
            );
            Expr::apps(
                Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
                [hyp_lhs, rat_one, eq_refl_bool],
            )
        };

        // Value: fun (n) (F) => hc24_core (1/3) n F hyp_proof.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(hc.nat.clone());
            let (f_id, f) = b.fresh_local(hc.f_type(&n));
            let body = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.hc24_core"), vec![]),
                [rho_third.clone(), n.clone(), f.clone(), hyp_proof],
            );
            let e = b.mk_lam(f_id, BinderInfo::Default, hc.f_type(&n), body);
            let e = b.mk_lam(n_id, BinderInfo::Default, hc.nat.clone(), e);
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

    const LEMMAS: &[&str] = &[
        "BoolAnalysis.ind_nonneg",
        "BoolAnalysis.setSize_nonneg",
        "BoolAnalysis.fourier_sq_nonneg",
        "BoolAnalysis.total_influence_nonneg",
        "BoolAnalysis.kkl_threshold_influence",
        "BoolAnalysis.kkl_mass_ge1_le_influence",
        "BoolAnalysis.ind_pow4_eq_ind",
        "BoolAnalysis.disagree_sq_self_eq_four_mul",
        "BoolAnalysis.hc24_at_third",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_hcdual()
            .expect("init_boolean_analysis_kkl_hcdual");
        env.init_boolean_analysis_kkl_hcdual().expect("idempotent");
        env
    }

    #[test]
    fn test_kkl_hcdual_all_constructive_theorems() {
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
                "{name} closure must be empty"
            );
        }
    }
}
