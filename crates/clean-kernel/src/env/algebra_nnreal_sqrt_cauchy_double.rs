// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the dyadic DOUBLING identity
//! `inv(2^{n+1}) + inv(2^{n+1}) = inv(2^n)` (Stage B3, sqrt run #4, rung 6d).
//!
//! # Why this module exists
//!
//! The telescoping `IsCauchy` step (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.5 rung 6) absorbs two
//! consecutive `inv(2^{n+1})` increments into a single `inv(2^n)`. That is the
//! geometric content `2·2^-(n+1) = 2^-n`, here as the subtraction-free `Rat`
//! identity below.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.inv_ofNat_two_add_self : inv(ofNat 2) + inv(ofNat 2) = 1`.
//! - `Rat.inv_two_pow_succ_add_self : ∀ n,
//!       Rat.add (inv (ofNat 2^{n+1})) (inv (ofNat 2^{n+1})) = inv (ofNat 2^n)`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proofs
//!
//! `inv_ofNat_two_add_self`: `inv2 + inv2 = 1·inv2 + 1·inv2` (`one_mul ⁻¹` ×2)
//! `= (1+1)·inv2` (`right_distrib ⁻¹`) `= ofNat 2·inv2` (`1+1 = ofNat 2` via
//! `add_natCast_one 1`, `ofNat 1 ≡ Rat.one` defeq) `= 1` (`mul_inv_cancel`;
//! `ofNat 2 ≠ 0` from `zero_lt_ofNat_two_pow 1`, `ofNat 2 ≡ ofNat(2^1)` defeq).
//!
//! `inv_two_pow_succ_add_self`: `iv_s = iv_n·inv2` (`inv_two_pow_succ`); so
//! `iv_s + iv_s = iv_n·inv2 + iv_n·inv2 = iv_n·(inv2 + inv2)` (`left_distrib ⁻¹`)
//! `= iv_n·1` (`inv_ofNat_two_add_self`) `= iv_n` (`mul_one`).
//!
//! # Universe note
//!
//! `Eq`/`Eq.refl`/`Eq.subst`/`Eq.trans`/`Eq.symm` over `Rat : Sort 1` are at
//! universe 1.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for the doubling rung.
pub(crate) struct DoubleConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    rat: Expr,
    rat_one: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_ofnat: Expr,
    rat_ofnat_mul: Expr,
    rat_inv_two_pow_succ: Expr,
    rat_add_natcast_one: Expr,
    rat_right_distrib: Expr,
    rat_left_distrib: Expr,
    rat_mul_inv_cancel: Expr,
    rat_one_mul: Expr,
    rat_mul_one: Expr,
    rat_ne_zero_of_pos: Expr,
    rat_zero_lt_ofnat_two_pow: Expr,
    rat_inv_ofnat_two_add_self: Expr,
    eq_rat: Expr,
    eq_refl: Expr,
    eq_subst: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
}

impl DoubleConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            rat: k("Rat"),
            rat_one: k("Rat.one"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_ofnat: k("Rat.ofNat"),
            rat_ofnat_mul: k("Rat.ofNat_mul"),
            rat_inv_two_pow_succ: k("Rat.inv_two_pow_succ"),
            rat_add_natcast_one: k("Rat.add_natCast_one"),
            rat_right_distrib: k("Rat.right_distrib"),
            rat_left_distrib: k("Rat.left_distrib"),
            rat_mul_inv_cancel: k("Rat.mul_inv_cancel"),
            rat_one_mul: k("Rat.one_mul"),
            rat_mul_one: k("Rat.mul_one"),
            rat_ne_zero_of_pos: k("Rat.ne_zero_of_pos"),
            rat_zero_lt_ofnat_two_pow: k("Rat.zero_lt_ofNat_two_pow"),
            rat_inv_ofnat_two_add_self: k("Rat.inv_ofNat_two_add_self"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1]),
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
    fn npow2(&self, n: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), n])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
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
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `right_distrib a b c : (a+b)·c = a·c + b·c`.
    fn right_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_right_distrib.clone(), [a, b, cc])
    }
    /// `left_distrib a b c : a·(b+c) = a·b + a·c`.
    fn left_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_left_distrib.clone(), [a, b, cc])
    }
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, h])
    }
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a)
    }
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a)
    }
    fn add_natcast_one(&self, k: Expr) -> Expr {
        Expr::app(self.rat_add_natcast_one.clone(), k)
    }
    fn inv_two_pow_succ(&self, n: Expr) -> Expr {
        Expr::app(self.rat_inv_two_pow_succ.clone(), n)
    }
    fn ne_zero_of_pos(&self, b: Expr, hpos: Expr) -> Expr {
        Expr::apps(self.rat_ne_zero_of_pos.clone(), [b, hpos])
    }
}

impl Environment {
    /// Register the dyadic doubling identities. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_cauchy_double(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_nat()?;
        self.init_algebra_nnreal_sqrt_dyadic()?; // ofNat, Nat.pow
        self.init_algebra_rat_inv_dyadic_step()?; // inv_two_pow_succ, zero_lt_ofNat_two_pow, ne_zero_of_pos
        self.register_rat_ofnat_mul()?;
        self.init_rat_field_inst()?; // right_distrib, left_distrib, one_mul, mul_one, mul_inv_cancel
        self.register_fin_sum_const_one_theorems()?; // add_natCast_one

        let c = DoubleConsts::new();
        self.register_inv_ofnat_two_add_self(&c)?;
        self.register_inv_two_pow_succ_add_self(&c)?;
        Ok(())
    }

    /// `Rat.inv_ofNat_two_add_self : inv(ofNat 2) + inv(ofNat 2) = 1`.
    fn register_inv_ofnat_two_add_self(&mut self, c: &DoubleConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_ofNat_two_add_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let one = c.rat_one.clone();
        let of2 = c.ofnat(c.nat_lit(2));
        let inv2 = c.inv(of2.clone());

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let concl = c.eq_ty(c.add(inv2.clone(), inv2.clone()), one.clone());
            b.finish(concl)
        };
        let value = {
            // one_inv2 := 1·inv2.
            let one_inv2 = c.mul(one.clone(), inv2.clone());
            let one_plus_one = c.add(one.clone(), one.clone());
            let onep1_inv2 = c.mul(one_plus_one.clone(), inv2.clone());
            let of2_inv2 = c.mul(of2.clone(), inv2.clone());
            let inv2_plus_inv2 = c.add(inv2.clone(), inv2.clone());
            let one_inv2_plus = c.add(one_inv2.clone(), one_inv2.clone());

            // s_om_l : inv2 = 1·inv2  := Eq.symm (one_mul inv2).
            let om_l = c.one_mul(inv2.clone()); // 1·inv2 = inv2
            let s_om_l = c.eq_symm(one_inv2.clone(), inv2.clone(), om_l);
            // L0 : inv2 + inv2 = 1·inv2 + inv2  (transport s_om_l on the FIRST summand,
            //   motive t := (inv2 + inv2) = (t + inv2)).
            let l0 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::new();
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(inv2_plus_inv2.clone(), c.add(t, inv2.clone()));
                    mb.finish(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    inv2.clone(),
                    one_inv2.clone(),
                    s_om_l.clone(),
                    c.eq_refl(inv2_plus_inv2.clone()),
                )
            };
            // L1 : 1·inv2 + inv2 = 1·inv2 + 1·inv2  (transport s_om_l on the SECOND summand,
            //   motive t := (1·inv2 + inv2) = (1·inv2 + t)).
            let oneinv2_plus_inv2 = c.add(one_inv2.clone(), inv2.clone());
            let l1 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::new();
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    // motive t := (1·inv2 + inv2) = (1·inv2 + t).
                    let body = c.eq_ty(oneinv2_plus_inv2.clone(), c.add(one_inv2.clone(), t));
                    mb.finish(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    inv2.clone(),
                    one_inv2.clone(),
                    s_om_l,
                    c.eq_refl(oneinv2_plus_inv2.clone()),
                )
            };
            // L2 : 1·inv2 + 1·inv2 = (1+1)·inv2  := Eq.symm (right_distrib 1 1 inv2).
            let rd = c.right_distrib(one.clone(), one.clone(), inv2.clone());
            let l2 = c.eq_symm(onep1_inv2.clone(), one_inv2_plus.clone(), rd);
            // L3 : (1+1)·inv2 = ofNat 2·inv2  (transport (1+1 = ofNat 2) under motive t := (1+1)·inv2 = t·inv2).
            //   ancl1 : ofNat 1 + 1 = ofNat 2 ; ofNat 1 ≡ 1 defeq so this is (1+1 = ofNat 2).
            let ancl1 = c.add_natcast_one(c.nat_lit(1));
            let l3 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::new();
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(onep1_inv2.clone(), c.mul(t, inv2.clone()));
                    mb.finish(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    one_plus_one.clone(),
                    of2.clone(),
                    ancl1,
                    c.eq_refl(onep1_inv2.clone()),
                )
            };
            // L4 : ofNat 2·inv2 = 1  := mul_inv_cancel (ofNat 2) (ofNat 2 ≠ 0).
            let of2_ne = c.ne_zero_of_pos(
                of2.clone(),
                Expr::app(c.rat_zero_lt_ofnat_two_pow.clone(), c.nat_lit(1)),
            );
            let l4 = c.mul_inv_cancel(of2.clone(), of2_ne);

            // chain: inv2+inv2 = 1·inv2+inv2 = 1·inv2+1·inv2 = (1+1)·inv2 = ofNat2·inv2 = 1.
            let t01 = c.eq_trans(
                inv2_plus_inv2.clone(),
                oneinv2_plus_inv2.clone(),
                one_inv2_plus.clone(),
                l0,
                l1,
            );
            let t012 = c.eq_trans(
                inv2_plus_inv2.clone(),
                one_inv2_plus.clone(),
                onep1_inv2.clone(),
                t01,
                l2,
            );
            let t0123 = c.eq_trans(
                inv2_plus_inv2.clone(),
                onep1_inv2.clone(),
                of2_inv2.clone(),
                t012,
                l3,
            );
            c.eq_trans(
                inv2_plus_inv2.clone(),
                of2_inv2.clone(),
                one.clone(),
                t0123,
                l4,
            )
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.inv_two_pow_succ_add_self : ∀ n,
    ///   add (inv(ofNat 2^{n+1}))(inv(ofNat 2^{n+1})) = inv(ofNat 2^n)`.
    fn register_inv_two_pow_succ_add_self(&mut self, c: &DoubleConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_two_pow_succ_add_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let of2 = c.ofnat(c.nat_lit(2));
        let inv2 = c.inv(of2.clone());
        let one = c.rat_one.clone();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let iv_s = c.inv(c.ofnat(c.npow2(c.succ(n.clone()))));
            let iv_n = c.inv(c.ofnat(c.npow2(n.clone())));
            let concl = c.eq_ty(c.add(iv_s.clone(), iv_s), iv_n);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());

            let iv_s = c.inv(c.ofnat(c.npow2(c.succ(n.clone()))));
            let iv_n = c.inv(c.ofnat(c.npow2(n.clone())));
            let ivn_inv2 = c.mul(iv_n.clone(), inv2.clone());
            let ivs_plus_ivs = c.add(iv_s.clone(), iv_s.clone());
            let ivn_inv2_plus_self = c.add(ivn_inv2.clone(), ivn_inv2.clone());
            let ivn_times_inv2_plus_inv2 = c.mul(iv_n.clone(), c.add(inv2.clone(), inv2.clone()));
            let ivn_one = c.mul(iv_n.clone(), one.clone());

            // e2 : iv_s = iv_n·inv2.
            let e2 = c.inv_two_pow_succ(n.clone());
            // L0 : iv_s + iv_s = (iv_n·inv2) + iv_s   (transport e2 on first summand).
            let ivn_inv2_plus_ivs = c.add(ivn_inv2.clone(), iv_s.clone());
            let l0 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(ivs_plus_ivs.clone(), c.add(t, iv_s.clone()));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    iv_s.clone(),
                    ivn_inv2.clone(),
                    e2.clone(),
                    c.eq_refl(ivs_plus_ivs.clone()),
                )
            };
            // L1 : (iv_n·inv2) + iv_s = (iv_n·inv2) + (iv_n·inv2)  (transport e2 on second summand).
            let l1 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(ivn_inv2_plus_ivs.clone(), c.add(ivn_inv2.clone(), t));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    iv_s.clone(),
                    ivn_inv2.clone(),
                    e2,
                    c.eq_refl(ivn_inv2_plus_ivs.clone()),
                )
            };
            // L2 : (iv_n·inv2)+(iv_n·inv2) = iv_n·(inv2+inv2)  := Eq.symm (left_distrib iv_n inv2 inv2).
            let ld = c.left_distrib(iv_n.clone(), inv2.clone(), inv2.clone());
            let l2 = c.eq_symm(
                ivn_times_inv2_plus_inv2.clone(),
                ivn_inv2_plus_self.clone(),
                ld,
            );
            // L3 : iv_n·(inv2+inv2) = iv_n·1  (transport inv2+inv2 = 1).
            let dbl = Expr::const_(Name::from_string("Rat.inv_ofNat_two_add_self"), vec![]);
            let l3 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(ivn_times_inv2_plus_inv2.clone(), c.mul(iv_n.clone(), t));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    c.add(inv2.clone(), inv2.clone()),
                    one.clone(),
                    dbl,
                    c.eq_refl(ivn_times_inv2_plus_inv2.clone()),
                )
            };
            // L4 : iv_n·1 = iv_n  := mul_one iv_n.
            let l4 = c.mul_one(iv_n.clone());

            let t01 = c.eq_trans(
                ivs_plus_ivs.clone(),
                ivn_inv2_plus_ivs.clone(),
                ivn_inv2_plus_self.clone(),
                l0,
                l1,
            );
            let t012 = c.eq_trans(
                ivs_plus_ivs.clone(),
                ivn_inv2_plus_self.clone(),
                ivn_times_inv2_plus_inv2.clone(),
                t01,
                l2,
            );
            let t0123 = c.eq_trans(
                ivs_plus_ivs.clone(),
                ivn_times_inv2_plus_inv2.clone(),
                ivn_one.clone(),
                t012,
                l3,
            );
            let body = c.eq_trans(
                ivs_plus_ivs.clone(),
                ivn_one.clone(),
                iv_n.clone(),
                t0123,
                l4,
            );

            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
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

    const THEOREMS: &[&str] = &[
        "Rat.inv_ofNat_two_add_self",
        "Rat.inv_two_pow_succ_add_self",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_cauchy_double()
            .expect("init_algebra_nnreal_sqrt_cauchy_double");
        env.init_algebra_nnreal_sqrt_cauchy_double()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dyadic_double_present_and_kernel_check() {
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
    fn test_dyadic_double_constructive_empty_closure() {
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
