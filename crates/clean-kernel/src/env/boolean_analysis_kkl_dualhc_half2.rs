// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — **GLUE-4 HALVED**: the abstract ring-algebra bridge from the
//! integer `{0,±2}` cube identities to R2's halved-derivative hypotheses.
//!
//! R2 (`sum_prod_pow4_le_m3_sumpow4`) consumes, per index `x`, the facts about
//! `e := g·h` (`h := half := Rat.inv Rat.two`) and `chi := (g·g)·(h·h)`:
//!
//! ```text
//!   H1 : chi = e·e               -- (g·g)·(h·h) = (g·h)·(g·h)
//!   H2 : e·chi = e               -- (g·h)·((g·g)·(h·h)) = g·h
//!   H3 : chi·chi = chi           -- ((g·g)·(h·h))·((g·g)·(h·h)) = (g·g)·(h·h)
//! ```
//!
//! These are NOT `Eq.refl`-closable even on concrete `g ∈ {0,±2}`: the live
//! `Rat` is a QUOTIENT carrier whose `Rat.mul` reduces `Rat.mk` reps WITHOUT
//! gcd-reduction (e.g. `(mk 4 1)·(mk 1 4)` reduces to `mk 4 4`, not `mk 1 1`),
//! so half-scaled values land on non-canonical reps. They follow by RING ALGEBRA
//! over the INTEGER-valued cube identities
//! (`deriv_cube_eq_four_deriv : g·(g·g)=4·g`,
//! `disagree_sq_self_eq_four_mul : (g·g)·(g·g)=4·(g·g)`) and the constant
//! `half` facts (`4·(h·h)=1`, `4·(h·(h·h))=h`, `4·((h·h)·(h·h))=h·h`), each
//! discharged via `mul_inv_cancel two two_ne_zero` and the distributive /
//! associative / commutative `Rat` field laws.
//!
//! This module takes the integer identities as EXPLICIT hypotheses and is
//! parameterised over an abstract `g : Rat`, so it is pure field algebra:
//!
//! ```text
//! BoolAnalysis.half_deriv_chi_eq_sq :
//!   ∀ (g : Rat), Rat.mul (Rat.mul g g) (Rat.mul half half)
//!              = Rat.mul (Rat.mul g half) (Rat.mul g half)          -- H1 (chi = e·e)
//!
//! BoolAnalysis.half_deriv_e_chi_eq_e :
//!   ∀ (g : Rat),
//!     Rat.mul g (Rat.mul g g) = Rat.mul four g                       -- (g³ = 4g)
//!   → Rat.mul (Rat.mul g half) (Rat.mul (Rat.mul g g) (Rat.mul half half))
//!       = Rat.mul g half                                             -- H2 (e·chi = e)
//!
//! BoolAnalysis.half_deriv_chi_sq_eq_chi :
//!   ∀ (g : Rat),
//!     Rat.mul (Rat.mul g g) (Rat.mul g g) = Rat.mul four (Rat.mul g g)  -- (g²·g²=4g²)
//!   → Rat.mul (Rat.mul (Rat.mul g g) (Rat.mul half half))
//!             (Rat.mul (Rat.mul g g) (Rat.mul half half))
//!       = Rat.mul (Rat.mul g g) (Rat.mul half half)                  -- H3 (chi² = chi)
//! ```
//!
//! where `half := Rat.inv Rat.two` and `four := Rat.mk (Int.ofNat 4) 1` (spelled
//! to match the integer cube identities). Kernel-checked `Declaration::Theorem`,
//! `ProofQuality::Constructive`, EMPTY admitted-axiom closure. No axiom added or
//! removed.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms + ring-algebra leaf kit for GLUE-4 HALVED.
struct Half2Consts {
    order: OrderConsts,
    rat: Expr,
    rat_one: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_two: Expr,
    rat_inv: Expr,
    two_ne_zero: Expr,
    mul_inv_cancel: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    mul_one: Expr,
    one_mul: Expr,
    mul_mul_mul_comm: Expr,
    congr_arg: Expr,
    // Bool side (for H4's g²≤4 leaf + the descent-to-influence binding).
    bool_: Expr,
    bool_true: Expr,
    bool_false: Expr,
    bool_rec_prop: Expr,
    pm: Expr,
    rat_sub: Expr,
    le_of_ble: Expr,
    mul_le_right: Expr,
    sq_nonneg: Expr,
    eq_subst: Expr,
}

impl Half2Consts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            rat: k("Rat"),
            rat_one: k("Rat.one"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_two: k("Rat.two"),
            rat_inv: k("Rat.inv"),
            two_ne_zero: k("Rat.two_ne_zero"),
            mul_inv_cancel: k("Rat.mul_inv_cancel"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            mul_one: k("Rat.mul_one"),
            one_mul: k("Rat.one_mul"),
            mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            pm: k("BoolAnalysis.pm"),
            rat_sub: k("Rat.sub"),
            le_of_ble: k("Rat.le_of_ble_eq_true"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            sq_nonneg: k("Rat.sq_nonneg"),
            eq_subst: Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            ),
        }
    }

    fn rat(&self) -> Expr {
        self.rat.clone()
    }
    fn one(&self) -> Expr {
        self.rat_one.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    /// `half := Rat.inv Rat.two`.
    fn half(&self) -> Expr {
        Expr::app(self.rat_inv.clone(), self.rat_two.clone())
    }
    /// `four := Rat.mk (Int.ofNat 4) 1` — matches the integer cube identities.
    fn four(&self) -> Expr {
        let mut four_nat = self.nat_zero.clone();
        for _ in 0..4 {
            four_nat = Expr::app(self.nat_succ.clone(), four_nat);
        }
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), four_nat), one],
        )
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.order.trans(a, b, cc, h1, h2)
    }
    /// chain three equalities a=b=c=d.
    fn trans3(
        &self,
        a: Expr,
        b: Expr,
        cc: Expr,
        d: Expr,
        h_ab: Expr,
        h_bc: Expr,
        h_cd: Expr,
    ) -> Expr {
        let h_bd = self.trans(b.clone(), cc, d.clone(), h_bc, h_cd);
        self.trans(a, b, d, h_ab, h_bd)
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.one_mul.clone(), a)
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.mul_mul_mul_comm.clone(), [a, b, cc, d])
    }
    /// `congrArg.{1,1} Rat Rat a b f (h:a=b) : f a = f b`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.congr_arg.clone(), [self.rat(), self.rat(), a, b, f, h])
    }
    /// `Rat.mul_inv_cancel two two_ne_zero : Rat.two · half = 1`.
    fn two_half_eq_one(&self) -> Expr {
        Expr::apps(
            self.mul_inv_cancel.clone(),
            [self.rat_two.clone(), self.two_ne_zero.clone()],
        )
    }
    /// `@Eq.refl Rat x`.
    fn eq_refl(&self, x: Expr) -> Expr {
        Expr::apps(self.order.eq_refl.clone(), [self.rat(), x])
    }
    /// `four = two·two` by `Eq.refl` (`(1+1)·(1+1)` reduces to `Rat.mk 4 1`).
    fn four_eq_two_two(&self) -> Expr {
        // refl needs LHS = four; checked against type four = two·two.
        self.eq_refl(self.four())
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn pm_of(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    /// `g(a,b) := pm a − pm b`.
    fn g_bool(&self, a: Expr, b: Expr) -> Expr {
        self.sub(self.pm_of(a), self.pm_of(b))
    }
    /// `Rat.le_of_ble_eq_true a b (Eq.refl Bool.true) : a ≤ b` (requires the
    /// concrete `Rat.ble a b` to native-reduce to `true`).
    fn le_of_ble_refl(&self, a: Expr, b: Expr) -> Expr {
        let eq_refl_bool = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [self.bool_.clone(), self.bool_true.clone()],
        );
        Expr::apps(self.le_of_ble.clone(), [a, b, eq_refl_bool])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (h_bc:b≤c) (h_0a:0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, cc, h_bc, h_0a])
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    /// `Eq.subst.{1} Rat motive a b h_eq h_ma : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_ma: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat(), motive, a, b, h_eq, h_ma],
        )
    }

    /// Build `fun t => f(t)` over `Rat` for `congrArg`.
    fn lam_rat<F: Fn(&EnvDeclBuilder, Expr) -> Expr>(&self, parent: &EnvDeclBuilder, f: F) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = d.fresh_local(self.rat());
        let body = f(&d, t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat(), body))
    }

    // ── The constant `half`-power identities (proofs as Expr) ───────────────

    /// `4·(half·half) = 1`. Proof:
    /// `4·(h·h) = (two·two)·(h·h)`   [congrArg (·(h·h)) (four=two·two)]
    ///         `= (two·h)·(two·h)`    [mmmc two two h h]
    ///         `= 1·1`                [congr both legs via two·h=1]
    ///         `= 1`                  [one_mul 1].
    fn four_hh_eq_one(&self, b: &EnvDeclBuilder) -> Expr {
        let h = self.half();
        let hh = self.mul(h.clone(), h.clone());
        let four = self.four();
        let two = self.rat_two.clone();
        let one = self.one();
        let th = self.mul(two.clone(), h.clone()); // two·h
        let tt = self.mul(two.clone(), two.clone()); // two·two

        // step1 : 4·(h·h) = (two·two)·(h·h)
        let f1 = self.lam_rat(b, |_d, t| self.mul(t, hh.clone()));
        let s1 = self.congr_arg(four.clone(), tt.clone(), f1, self.four_eq_two_two());
        // step2 : (two·two)·(h·h) = (two·h)·(two·h)
        let s2 = self.mmmc(two.clone(), two.clone(), h.clone(), h.clone());
        // step3 : (two·h)·(two·h) = 1·1   via two congr legs of two·h=1
        let thl = self.two_half_eq_one(); // two·h = 1
                                          //   (two·h)·(two·h) = 1·(two·h)   [congrArg (·(two·h)) thl]
        let f3a = self.lam_rat(b, |_d, t| self.mul(t, th.clone()));
        let s3a = self.congr_arg(th.clone(), one.clone(), f3a, thl.clone());
        //   1·(two·h) = 1·1               [congrArg (1·) thl]
        let f3b = self.lam_rat(b, |_d, t| self.mul(one.clone(), t));
        let s3b = self.congr_arg(th.clone(), one.clone(), f3b, thl.clone());
        let one_th = self.mul(one.clone(), th.clone());
        let one_one = self.mul(one.clone(), one.clone());
        let s3 = self.trans(
            self.mul(th.clone(), th.clone()),
            one_th.clone(),
            one_one.clone(),
            s3a,
            s3b,
        );
        // step4 : 1·1 = 1
        let s4 = self.one_mul(one.clone());
        // chain: 4·(h·h) = (two·two)·(h·h) = (two·h)·(two·h) = 1·1 = 1
        let lhs = self.mul(four.clone(), hh.clone());
        let v0 = self.trans3(
            lhs.clone(),
            self.mul(tt.clone(), hh.clone()),
            self.mul(th.clone(), th.clone()),
            one_one.clone(),
            s1,
            s2,
            s3,
        );
        self.trans(lhs, one_one, one, v0, s4)
    }

    /// `four·(a·b) = a·(four·b)`. Proof:
    /// `4·(a·b) = (4·a)·b`   [symm mul_assoc 4 a b]
    ///         `= (a·4)·b`    [congrArg (·b) (mul_comm 4 a)]
    ///         `= a·(4·b)`    [mul_assoc a 4 b].
    fn move_four_left(&self, b: &EnvDeclBuilder, a: Expr, bb: Expr) -> Expr {
        let four = self.four();
        let four_a = self.mul(four.clone(), a.clone()); // 4·a
        let a_four = self.mul(a.clone(), four.clone()); // a·4
        let ab = self.mul(a.clone(), bb.clone()); // a·b
                                                  // step1 : 4·(a·b) = (4·a)·b
        let s1 = self.symm(
            self.mul(four_a.clone(), bb.clone()),
            self.mul(four.clone(), ab.clone()),
            self.mul_assoc(four.clone(), a.clone(), bb.clone()),
        );
        // step2 : (4·a)·b = (a·4)·b
        let f2 = self.lam_rat(b, |_d, t| self.mul(t, bb.clone()));
        let s2 = self.congr_arg(
            four_a.clone(),
            a_four.clone(),
            f2,
            self.mul_comm(four.clone(), a.clone()),
        );
        // step3 : (a·4)·b = a·(4·b)
        let s3 = self.mul_assoc(a.clone(), four.clone(), bb.clone());
        self.trans3(
            self.mul(four.clone(), ab.clone()),
            self.mul(four_a.clone(), bb.clone()),
            self.mul(a_four.clone(), bb.clone()),
            self.mul(a.clone(), self.mul(four.clone(), bb.clone())),
            s1,
            s2,
            s3,
        )
    }

    /// `four·(a·(h·h)) = a`, given `four_hh_eq_one : 4·(h·h) = 1`.  Proof:
    /// `4·(a·(h·h)) = a·(4·(h·h))`   [move_four_left a (h·h)]
    ///             `= a·1`           [congrArg (a·) four_hh_eq_one]
    ///             `= a`             [mul_one a].
    fn four_a_hh_eq_a(&self, b: &EnvDeclBuilder, a: Expr) -> Expr {
        let h = self.half();
        let hh = self.mul(h.clone(), h.clone());
        let four = self.four();
        let one = self.one();
        let a_hh = self.mul(a.clone(), hh.clone());
        let four_a_hh = self.mul(four.clone(), a_hh.clone()); // 4·(a·hh)
        let a_four_hh = self.mul(a.clone(), self.mul(four.clone(), hh.clone())); // a·(4·hh)
        let a_one = self.mul(a.clone(), one.clone()); // a·1
                                                      // s1 : 4·(a·hh) = a·(4·hh)
        let s1 = self.move_four_left(b, a.clone(), hh.clone());
        // s2 : a·(4·hh) = a·1
        let f2 = self.lam_rat(b, |_d, t| self.mul(a.clone(), t));
        let s2 = self.congr_arg(
            self.mul(four.clone(), hh.clone()),
            one.clone(),
            f2,
            self.four_hh_eq_one(b),
        );
        // s3 : a·1 = a
        let s3 = self.mul_one(a.clone());
        self.trans3(four_a_hh, a_four_hh, a_one, a, s1, s2, s3)
    }

    /// H2 proof body: `(g·h)·((g·g)·(h·h)) = g·h`, given `hcube : g·(g·g) = 4·g`.
    /// Chain:
    /// `(g·h)·((g·g)·(h·h)) = (g·(g·g))·(h·(h·h))`  [mmmc g h (g·g) (h·h)]
    ///                     `= (4·g)·(h·(h·h))`       [congrArg (·(h·(h·h))) hcube]
    ///                     `= (g·4)·(h·(h·h))`       [congrArg (·…) (mul_comm 4 g)]
    ///                     `= g·(4·(h·(h·h)))`       [mul_assoc g 4 (h·(h·h))]
    ///                     `= g·h`.                  [congrArg (g·) (4·(h·(h·h))=h)]
    fn h2_proof(&self, b: &EnvDeclBuilder, g: Expr, hcube: Expr) -> Expr {
        let h = self.half();
        let hh = self.mul(h.clone(), h.clone()); // h·h
        let h_hh = self.mul(h.clone(), hh.clone()); // h·(h·h)
        let gg = self.mul(g.clone(), g.clone()); // g·g
        let gh = self.mul(g.clone(), h.clone()); // g·h
        let chi = self.mul(gg.clone(), hh.clone()); // (g·g)·(h·h)
        let four = self.four();
        let g_ggcube = self.mul(g.clone(), gg.clone()); // g·(g·g)
        let four_g = self.mul(four.clone(), g.clone()); // 4·g
        let g_four = self.mul(g.clone(), four.clone()); // g·4

        let lhs = self.mul(gh.clone(), chi.clone()); // (g·h)·((g·g)·(h·h))
                                                     // A : lhs = (g·(g·g))·(h·(h·h))
        let mid_a = self.mul(g_ggcube.clone(), h_hh.clone());
        let s_a = self.mmmc(g.clone(), h.clone(), gg.clone(), hh.clone());
        // B : (g·(g·g))·(h·(h·h)) = (4·g)·(h·(h·h))   [congr left factor, hcube]
        let f_b = self.lam_rat(b, |_d, t| self.mul(t, h_hh.clone()));
        let mid_b = self.mul(four_g.clone(), h_hh.clone());
        let s_b = self.congr_arg(g_ggcube.clone(), four_g.clone(), f_b, hcube);
        // C : (4·g)·(h·(h·h)) = (g·4)·(h·(h·h))   [congr left, mul_comm 4 g]
        let f_c = self.lam_rat(b, |_d, t| self.mul(t, h_hh.clone()));
        let mid_c = self.mul(g_four.clone(), h_hh.clone());
        let s_c = self.congr_arg(
            four_g.clone(),
            g_four.clone(),
            f_c,
            self.mul_comm(four.clone(), g.clone()),
        );
        // D : (g·4)·(h·(h·h)) = g·(4·(h·(h·h)))   [mul_assoc g 4 (h·(h·h))]
        let four_hhh = self.mul(four.clone(), h_hh.clone()); // 4·(h·(h·h))
        let mid_d = self.mul(g.clone(), four_hhh.clone());
        let s_d = self.mul_assoc(g.clone(), four.clone(), h_hh.clone());
        // E : g·(4·(h·(h·h))) = g·h   [congrArg (g·) (4·(h·(h·h))=h)]
        let f_e = self.lam_rat(b, |_d, t| self.mul(g.clone(), t));
        let four_hhh_eq_h = self.four_a_hh_eq_a(b, h.clone()); // 4·(h·(h·h)) = h
        let s_e = self.congr_arg(four_hhh.clone(), h.clone(), f_e, four_hhh_eq_h);

        // Chain A,B,C,D,E.
        let v_ab = self.trans(lhs.clone(), mid_a.clone(), mid_b.clone(), s_a, s_b);
        let v_abc = self.trans(lhs.clone(), mid_b.clone(), mid_c.clone(), v_ab, s_c);
        let v_abcd = self.trans(lhs.clone(), mid_c.clone(), mid_d.clone(), v_abc, s_d);
        self.trans(lhs, mid_d, gh, v_abcd, s_e)
    }

    /// H3 proof body: `chi·chi = chi` for `chi := (g·g)·(h·h)`, given
    /// `hsq : (g·g)·(g·g) = 4·(g·g)`. With `G := g·g`, `H := h·h`, `chi = G·H`:
    /// `(G·H)·(G·H) = (G·G)·(H·H)`   [mmmc G H G H]
    ///             `= (4·G)·(H·H)`    [congr (·(H·H)) hsq]
    ///             `= (G·4)·(H·H)`    [congr (mul_comm 4 G)]
    ///             `= G·(4·(H·H))`    [mul_assoc G 4 (H·H)]
    ///             `= G·H`.           [congr (G·) (4·(H·H)=H), via four_a_hh_eq_a(h·h)]
    fn h3_proof(&self, b: &EnvDeclBuilder, g: Expr, hsq: Expr) -> Expr {
        let h = self.half();
        let cap_g = self.mul(g.clone(), g.clone()); // G = g·g
        let cap_h = self.mul(h.clone(), h.clone()); // H = h·h
        let chi = self.mul(cap_g.clone(), cap_h.clone()); // G·H
        let four = self.four();
        let gg_gg = self.mul(cap_g.clone(), cap_g.clone()); // G·G
        let four_g = self.mul(four.clone(), cap_g.clone()); // 4·G
        let g_four = self.mul(cap_g.clone(), four.clone()); // G·4
        let hh_hh = self.mul(cap_h.clone(), cap_h.clone()); // H·H

        let lhs = self.mul(chi.clone(), chi.clone()); // (G·H)·(G·H)
                                                      // A : (G·H)·(G·H) = (G·G)·(H·H)
        let mid_a = self.mul(gg_gg.clone(), hh_hh.clone());
        let s_a = self.mmmc(cap_g.clone(), cap_h.clone(), cap_g.clone(), cap_h.clone());
        // B : (G·G)·(H·H) = (4·G)·(H·H)
        let f_b = self.lam_rat(b, |_d, t| self.mul(t, hh_hh.clone()));
        let mid_b = self.mul(four_g.clone(), hh_hh.clone());
        let s_b = self.congr_arg(gg_gg.clone(), four_g.clone(), f_b, hsq);
        // C : (4·G)·(H·H) = (G·4)·(H·H)
        let f_c = self.lam_rat(b, |_d, t| self.mul(t, hh_hh.clone()));
        let mid_c = self.mul(g_four.clone(), hh_hh.clone());
        let s_c = self.congr_arg(
            four_g.clone(),
            g_four.clone(),
            f_c,
            self.mul_comm(four.clone(), cap_g.clone()),
        );
        // D : (G·4)·(H·H) = G·(4·(H·H))
        let four_hh = self.mul(four.clone(), hh_hh.clone()); // 4·(H·H)
        let mid_d = self.mul(cap_g.clone(), four_hh.clone());
        let s_d = self.mul_assoc(cap_g.clone(), four.clone(), hh_hh.clone());
        // E : G·(4·(H·H)) = G·H  [congr (G·) (4·(H·H)=H)]
        let f_e = self.lam_rat(b, |_d, t| self.mul(cap_g.clone(), t));
        let four_hh_eq_h = self.four_a_hh_eq_a(b, cap_h.clone()); // 4·((h·h)·(h·h)) = h·h
        let s_e = self.congr_arg(four_hh.clone(), cap_h.clone(), f_e, four_hh_eq_h);

        let v_ab = self.trans(lhs.clone(), mid_a.clone(), mid_b.clone(), s_a, s_b);
        let v_abc = self.trans(lhs.clone(), mid_b.clone(), mid_c.clone(), v_ab, s_c);
        let v_abcd = self.trans(lhs.clone(), mid_c.clone(), mid_d.clone(), v_abc, s_d);
        self.trans(lhs, mid_d, chi, v_abcd, s_e)
    }
}

// Registration entrypoints live in the sibling build file to keep each file
// under the 500-line convention.
include!("boolean_analysis_kkl_dualhc_half2_build.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_half2()
            .expect("init_boolean_analysis_kkl_dualhc_half2");
        env.init_boolean_analysis_kkl_dualhc_half2()
            .expect("idempotent");
        env
    }

    fn assert_constructive_theorem(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
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
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_four_half_sq_eq_one() {
        let env = env();
        assert_constructive_theorem(&env, "BoolAnalysis.four_half_sq_eq_one");
    }

    #[test]
    fn test_half_deriv_chi_eq_sq() {
        let env = env();
        assert_constructive_theorem(&env, "BoolAnalysis.half_deriv_chi_eq_sq");
    }

    #[test]
    fn test_half_deriv_e_chi_eq_e() {
        let env = env();
        assert_constructive_theorem(&env, "BoolAnalysis.half_deriv_e_chi_eq_e");
    }

    #[test]
    fn test_half_deriv_chi_sq_eq_chi() {
        let env = env();
        assert_constructive_theorem(&env, "BoolAnalysis.half_deriv_chi_sq_eq_chi");
    }

    #[test]
    fn test_disagree_sq_le_four() {
        let env = env();
        assert_constructive_theorem(&env, "BoolAnalysis.disagree_sq_le_four");
    }

    #[test]
    fn test_half_deriv_chi_le_one() {
        let env = env();
        assert_constructive_theorem(&env, "BoolAnalysis.half_deriv_chi_le_one");
    }
}
