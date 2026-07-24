// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer (ported from the sqrt layer; cbrtDyadicApprox mirrors dyadicApprox) — the TELESCOPING bound `a_{n+d} ≤ a_n + inv(2^n)`
//! (Stage B3, sqrt run #4, rung 6e).
//!
//! # Why this module exists
//!
//! The dyadic `IsCauchy` proof (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.5 rung 6) needs the
//! UPPER telescoping bound: from any index `n`, advancing by `d` steps grows
//! the approximation by at most `inv(2^n)`. With monotonicity (the LOWER side)
//! this gives the two-sided Cauchy estimate.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.cbrtDyadicApprox_le_add_inv : ∀ x n d,
//!       Rat.le (Rat.cbrtDyadicApprox x (Nat.add n d))
//!              (Rat.add (Rat.cbrtDyadicApprox x n) (inv (ofNat 2^n)))`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proof: `Nat.rec` on the gap `d`, motive `M d := ∀ n, a_{n+d} ≤ a_n + iv_n`
//!
//! - Base `d=0`: `a_{n+0} ≡ a_n` (defeq); `a_n ≤ a_n + iv_n` from
//!   `add_le_add_left 0 iv_n (0≤iv_n) a_n` (`a_n+0 ≤ a_n+iv_n`) transported along
//!   `add_zero a_n`.
//! - Step `d → succ d` at fixed `n`: peel the FIRST step.
//!   * `ih (succ n) : a_{succ n + d} ≤ a_{succ n} + iv_{n+1}`.
//!   * `congrArg (dyadicApprox x) (Nat.succ_add n d)` rewrites the LHS index
//!     `succ n + d → succ(n+d)` (defeq `n + succ d`, the goal LHS). →
//!     `step1 : a_{n+succ d} ≤ a_{succ n} + iv_{n+1}`.
//!   * single-step UPPER `dyadicApprox_succ_le x n : a_{succ n} ≤ a_n + iv_{n+1}`;
//!     `add_le_add_right` ⟹ `a_{succ n}+iv_{n+1} ≤ (a_n+iv_{n+1})+iv_{n+1}`.
//!   * `(a_n+iv_{n+1})+iv_{n+1} = a_n + (iv_{n+1}+iv_{n+1}) = a_n + iv_n`
//!     (`add_assoc` + the doubling `inv_two_pow_succ_add_self`); transport ⟹
//!     `step3 : a_{succ n}+iv_{n+1} ≤ a_n + iv_n`.
//!   * `le_trans step1 step3 : a_{n+succ d} ≤ a_n + iv_n`.
//!
//! # Universe note
//!
//! `Nat.rec` Prop-motive is at universe 0. `Eq`/`Eq.subst`/`Eq.trans`/`congrArg`
//! over `Nat`/`Rat : Sort 1` are at universe 1.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for the telescoping rung.
pub(crate) struct CbrtTeleConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_pow: Expr,
    nat_succ_add: Expr,
    nat_rec_prop: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    rat_dyadic_approx: Expr,
    rat_dyadic_approx_succ_le: Expr,
    rat_inv_two_pow_succ_add_self: Expr,
    rat_zero_lt_inv_two_pow: Expr,
    rat_add_le_add_left: Expr,
    rat_add_le_add_right: Expr,
    rat_add_assoc: Expr,
    rat_add_zero: Expr,
    rat_le_trans: Expr,
    rat_lt_iff_le_not_le: Expr,
    eq_rat: Expr,
    eq_refl: Expr,
    eq_subst: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
}

impl CbrtTeleConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let l0 = Level::zero();
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_add: k("Nat.add"),
            nat_pow: k("Nat.pow"),
            nat_succ_add: k("Nat.succ_add"),
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![l0]),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_dyadic_approx: k("Rat.cbrtDyadicApprox"),
            rat_dyadic_approx_succ_le: k("Rat.cbrtDyadicApprox_succ_le"),
            rat_inv_two_pow_succ_add_self: k("Rat.inv_two_pow_succ_add_self"),
            rat_zero_lt_inv_two_pow: k("Rat.zero_lt_inv_two_pow"),
            rat_add_le_add_left: k("Rat.add_le_add_left"),
            rat_add_le_add_right: k("Rat.add_le_add_right"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_zero: k("Rat.add_zero"),
            rat_le_trans: k("Rat.le_trans"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            and_c: k("And"),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn npow2(&self, n: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), n])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn not_(&self, p: Expr) -> Expr {
        Expr::app(self.not_c.clone(), p)
    }
    fn and(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    /// `inv(ofNat 2^n)`.
    fn iv(&self, n: Expr) -> Expr {
        self.inv(self.ofnat(self.npow2(n)))
    }
    fn approx(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_approx.clone(), [x.clone(), n])
    }
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    fn eq_refl(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), a])
    }
    fn eq_subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    /// `@congrArg.{1,1} Nat Rat a a' f h : f a = f a'`.
    fn congr_arg_nat_rat(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    /// `Nat.succ_add a b : Nat.add (succ a) b = succ(Nat.add a b)`.
    fn succ_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_succ_add.clone(), [a, b])
    }
    /// `add_le_add_left a b (h:a≤b) c : (c+a) ≤ (c+b)`.
    fn add_le_add_left(&self, a: Expr, b: Expr, h: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add_left.clone(), [a, b, h, cc])
    }
    /// `add_le_add_right a b c (h:a≤b) : (a+c) ≤ (b+c)`.
    fn add_le_add_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add_right.clone(), [a, b, cc, h])
    }
    /// `add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    /// `add_zero a : a+0 = a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    /// `le_trans a b c (h1:a≤b)(h2:b≤c) : a≤c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, cc, h1, h2])
    }
    /// `dyadicApprox_succ_le x n : a_{succ n} ≤ a_n + iv_{n+1}`.
    fn approx_succ_le(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_approx_succ_le.clone(), [x.clone(), n])
    }
    /// `inv_two_pow_succ_add_self n : iv_{n+1} + iv_{n+1} = iv_n`.
    fn double(&self, n: Expr) -> Expr {
        Expr::app(self.rat_inv_two_pow_succ_add_self.clone(), n)
    }
    /// `0 ≤ x` from `0 < x`.
    fn le_of_pos(&self, x: Expr, h_pos: Expr) -> Expr {
        let le0x = self.le(self.rat_zero.clone(), x.clone());
        let not_le_x0 = self.not_(self.le(x.clone(), self.rat_zero.clone()));
        let and_ty = self.and(le0x.clone(), not_le_x0.clone());
        let lt0x = self.lt(self.rat_zero.clone(), x.clone());
        let iff = Expr::apps(
            self.rat_lt_iff_le_not_le.clone(),
            [self.rat_zero.clone(), x],
        );
        let mp = Expr::apps(self.iff_mp.clone(), [lt0x, and_ty, iff, h_pos]);
        Expr::apps(self.and_left.clone(), [le0x, not_le_x0, mp])
    }

    /// The motive body `M-at-d-n := le (a_{n+d}) (a_n + iv_n)` (a `Prop`).
    fn body_at(&self, x: &Expr, n: Expr, d: Expr) -> Expr {
        let lhs = self.approx(x, self.nadd(n.clone(), d));
        let rhs = self.add(self.approx(x, n.clone()), self.iv(n));
        self.le(lhs, rhs)
    }
    /// The motive `M := fun d => ∀ n, body_at x n d`.
    fn motive(&self, x: &Expr, parent: &EnvDeclBuilder) -> Expr {
        let mut md = EnvDeclBuilder::child_of(parent);
        let (d_id, d) = md.fresh_local(self.nat.clone());
        let forall_n = {
            let mut mn = EnvDeclBuilder::child_of(&md);
            let (n_id, n) = mn.fresh_local(self.nat.clone());
            let body = self.body_at(x, n.clone(), d.clone());
            mn.finish_child(mn.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), body))
        };
        md.finish_child(md.mk_lam(d_id, BinderInfo::Default, self.nat.clone(), forall_n))
    }
}

impl Environment {
    /// Register `Rat.cbrtDyadicApprox_le_add_inv`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_cbrt_cauchy_tele(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_nat()?;
        self.register_nat_succ_add_proof()?;
        self.init_algebra_nnreal_cbrt_seq()?; // dyadicApprox, ofNat, Nat.pow
        self.init_algebra_nnreal_cbrt_cauchy_step()?; // dyadicApprox_succ_le, zero_lt_inv_two_pow
        self.init_algebra_nnreal_sqrt_cauchy_double()?; // inv_two_pow_succ_add_self
        self.init_algebra_rat_inv_dyadic_step()?; // zero_lt_inv_two_pow
                                                  // Rat.add_le_add_left, add_assoc, add_zero, le_trans.
        self.init_rat_quotient_poc()?;
        // Rat.add_le_add_right.
        self.register_rat_add_le_add_right()?;
        self.init_rat_linear_order()?;
        self.register_rat_order_proofs()?;

        let c = CbrtTeleConsts::new();
        self.register_cbrt_dyadic_approx_le_add_inv(&c)?;
        Ok(())
    }

    fn register_cbrt_dyadic_approx_le_add_inv(
        &mut self,
        c: &CbrtTeleConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicApprox_le_add_inv");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let concl = c.body_at(&x, n.clone(), d.clone());
            let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (d_id, d) = b.fresh_local(c.nat.clone());

            let motive = c.motive(&x, &b);

            // base : M 0 = ∀ n, le (a_{n+0})(a_n + iv_n).  a_{n+0} ≡ a_n defeq.
            let base = {
                let mut bb = EnvDeclBuilder::child_of(&b);
                let (bn_id, bn) = bb.fresh_local(c.nat.clone());
                let a_bn = c.approx(&x, bn.clone());
                let iv_bn = c.iv(bn.clone());
                let iv_nonneg = c.le_of_pos(
                    iv_bn.clone(),
                    Expr::app(c.rat_zero_lt_inv_two_pow.clone(), bn.clone()),
                );
                // add_le_add_left 0 iv_bn (0≤iv_bn) a_bn : le (a_bn+0)(a_bn+iv_bn).
                let step =
                    c.add_le_add_left(c.rat_zero.clone(), iv_bn.clone(), iv_nonneg, a_bn.clone());
                let a_bn_plus_zero = c.add(a_bn.clone(), c.rat_zero.clone());
                let a_bn_plus_iv = c.add(a_bn.clone(), iv_bn.clone());
                // transport a_bn+0 → a_bn (add_zero): motive t := le t (a_bn+iv_bn).
                let motive_b = {
                    let mut mb = EnvDeclBuilder::child_of(&bb);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(t, a_bn_plus_iv.clone());
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let proof = c.eq_subst(
                    motive_b,
                    a_bn_plus_zero,
                    a_bn.clone(),
                    c.add_zero(a_bn.clone()),
                    step,
                );
                // proof : le a_bn (a_bn+iv_bn).  Goal (M 0 at bn) is le (a_{bn+0})(a_bn+iv_bn),
                // and a_{bn+0} ≡ a_bn defeq.
                bb.finish_child(bb.mk_lam(bn_id, BinderInfo::Default, c.nat.clone(), proof))
            };

            // step : ∀ d', M d' → M (succ d').
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&b);
                let (dp_id, dp) = sb.fresh_local(c.nat.clone());
                // ih : M d' = ∀ n, le (a_{n+d'})(a_n + iv_n).
                let ih_ty = {
                    let mut mh = EnvDeclBuilder::child_of(&sb);
                    let (hn_id, hn) = mh.fresh_local(c.nat.clone());
                    let body = c.body_at(&x, hn.clone(), dp.clone());
                    mh.finish_child(mh.mk_pi(hn_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

                // body : ∀ n, le (a_{n + succ d'})(a_n + iv_n).
                let inner = {
                    let mut ib = EnvDeclBuilder::child_of(&sb);
                    let (sn_id, sn) = ib.fresh_local(c.nat.clone());

                    let a_n = c.approx(&x, sn.clone());
                    let iv_n = c.iv(sn.clone());
                    let a_n_plus_iv_n = c.add(a_n.clone(), iv_n.clone());
                    let iv_s = c.iv(c.succ(sn.clone()));
                    let a_succ_n = c.approx(&x, c.succ(sn.clone()));
                    let a_succ_n_plus_iv_s = c.add(a_succ_n.clone(), iv_s.clone());

                    // ih (succ n) : le (a_{succ n + d'})(a_{succ n} + iv_{n+1}).
                    let ih_app = Expr::app(ih.clone(), c.succ(sn.clone()));
                    let idx_succ_n_d = c.nadd(c.succ(sn.clone()), dp.clone());
                    let a_idx = c.approx(&x, idx_succ_n_d.clone());
                    // idx_eq : a_{succ n + d'} = a_{succ(n+d')}  (congrArg over Nat.succ_add).
                    let idx_succ_nd = c.succ(c.nadd(sn.clone(), dp.clone()));
                    let a_succ_nd = c.approx(&x, idx_succ_nd.clone());
                    let approx_fn = {
                        let mut fb = EnvDeclBuilder::child_of(&ib);
                        let (m_id, m) = fb.fresh_local(c.nat.clone());
                        let body = c.approx(&x, m.clone());
                        fb.finish_child(fb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
                    };
                    let idx_eq = c.congr_arg_nat_rat(
                        idx_succ_n_d.clone(),
                        idx_succ_nd.clone(),
                        approx_fn,
                        c.succ_add(sn.clone(), dp.clone()),
                    );
                    // transport ih_app's LHS along idx_eq: motive t := le t (a_{succ n}+iv_{n+1}).
                    let motive_idx = {
                        let mut mb = EnvDeclBuilder::child_of(&ib);
                        let (t_id, t) = mb.fresh_local(c.rat.clone());
                        let body = c.le(t, a_succ_n_plus_iv_s.clone());
                        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                    };
                    let step1 =
                        c.eq_subst(motive_idx, a_idx.clone(), a_succ_nd.clone(), idx_eq, ih_app);
                    // step1 : le (a_{succ(n+d')})(a_{succ n} + iv_{n+1}).
                    // a_{succ(n+d')} defeq a_{n + succ d'} = goal LHS.

                    // hstep : a_{succ n} ≤ a_n + iv_{n+1}.
                    let hstep = c.approx_succ_le(&x, sn.clone());
                    // add_le_add_right (a_{succ n})(a_n+iv_{n+1}) iv_{n+1} hstep
                    //   : le (a_{succ n}+iv_{n+1})((a_n+iv_{n+1})+iv_{n+1}).
                    let an_plus_ivs = c.add(a_n.clone(), iv_s.clone());
                    let lhs_big = c.add(an_plus_ivs.clone(), iv_s.clone());
                    let step2 = c.add_le_add_right(
                        a_succ_n.clone(),
                        an_plus_ivs.clone(),
                        iv_s.clone(),
                        hstep,
                    );
                    // step2 : le (a_{succ n}+iv_{n+1})((a_n+iv_{n+1})+iv_{n+1}).

                    // eq_rhs : (a_n+iv_{n+1})+iv_{n+1} = a_n + iv_n.
                    //   e_assoc : (a_n+iv_{n+1})+iv_{n+1} = a_n + (iv_{n+1}+iv_{n+1}).
                    let ivs_plus_ivs = c.add(iv_s.clone(), iv_s.clone());
                    let an_plus_ivsivs = c.add(a_n.clone(), ivs_plus_ivs.clone());
                    let e_assoc = c.add_assoc(a_n.clone(), iv_s.clone(), iv_s.clone());
                    //   e_dbl : a_n + (iv_{n+1}+iv_{n+1}) = a_n + iv_n
                    //     transport doubling under motive t := an_plus_ivsivs = (a_n + t).
                    let dbl = c.double(sn.clone());
                    let motive_dbl = {
                        let mut mb = EnvDeclBuilder::child_of(&ib);
                        let (t_id, t) = mb.fresh_local(c.rat.clone());
                        let body = c.eq_ty(an_plus_ivsivs.clone(), c.add(a_n.clone(), t));
                        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                    };
                    let e_dbl = c.eq_subst(
                        motive_dbl,
                        ivs_plus_ivs.clone(),
                        iv_n.clone(),
                        dbl,
                        c.eq_refl(an_plus_ivsivs.clone()),
                    );
                    let eq_rhs = c.eq_trans(
                        lhs_big.clone(),
                        an_plus_ivsivs.clone(),
                        a_n_plus_iv_n.clone(),
                        e_assoc,
                        e_dbl,
                    );
                    // transport step2's RHS lhs_big → a_n+iv_n along eq_rhs:
                    //   motive t := le (a_{succ n}+iv_{n+1}) t.
                    let motive_s3 = {
                        let mut mb = EnvDeclBuilder::child_of(&ib);
                        let (t_id, t) = mb.fresh_local(c.rat.clone());
                        let body = c.le(a_succ_n_plus_iv_s.clone(), t);
                        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                    };
                    let step3 = c.eq_subst(
                        motive_s3,
                        lhs_big.clone(),
                        a_n_plus_iv_n.clone(),
                        eq_rhs,
                        step2,
                    );
                    // step3 : le (a_{succ n}+iv_{n+1})(a_n + iv_n).

                    // le_trans (a_{succ(n+d')})(a_{succ n}+iv_{n+1})(a_n+iv_n) step1 step3.
                    let proof = c.le_trans(
                        a_succ_nd.clone(),
                        a_succ_n_plus_iv_s.clone(),
                        a_n_plus_iv_n.clone(),
                        step1,
                        step3,
                    );
                    // proof : le (a_{succ(n+d')})(a_n+iv_n).  Goal LHS a_{n+succ d'} ≡ a_{succ(n+d')}.
                    ib.finish_child(ib.mk_lam(sn_id, BinderInfo::Default, c.nat.clone(), proof))
                };

                let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, inner);
                let lam = sb.mk_lam(dp_id, BinderInfo::Default, c.nat.clone(), lam);
                sb.finish_child(lam)
            };

            // @Nat.rec.{0} motive base step d : M d = ∀ n, le (a_{n+d})(a_n+iv_n).
            // Apply to n.
            let rec = Expr::apps(c.nat_rec_prop.clone(), [motive, base, step, d.clone()]);
            let applied = Expr::app(rec, n.clone());

            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), applied);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

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

    const THEOREMS: &[&str] = &["Rat.cbrtDyadicApprox_le_add_inv"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cbrt_cauchy_tele()
            .expect("init_algebra_nnreal_cbrt_cauchy_tele");
        env.init_algebra_nnreal_cbrt_cauchy_tele()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dyadic_tele_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_dyadic_tele_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
