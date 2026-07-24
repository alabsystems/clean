// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat GCD/LCM core operations and basic properties.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Nat GCD/LCM operations and properties
    ///
    /// Adds:
    /// - Nat.dvd : Nat → Nat → Prop (divisibility predicate)
    /// - Nat.gcd : Nat → Nat → Nat (greatest common divisor)
    /// - Nat.lcm : Nat → Nat → Nat (least common multiple)
    /// - Nat.gcd_dvd_left : ∀ a b, dvd (gcd a b) a
    /// - Nat.gcd_dvd_right : ∀ a b, dvd (gcd a b) b
    /// - Nat.dvd_gcd : ∀ c a b, dvd c a → dvd c b → dvd c (gcd a b)
    /// - Nat.gcd_mul_lcm : ∀ a b, Eq (mul (gcd a b) (lcm a b)) (mul a b)
    /// - Nat.gcd_comm : ∀ a b, Eq (gcd a b) (gcd b a)
    /// - Nat.lcm_comm : ∀ a b, Eq (lcm a b) (lcm b a)
    /// - Nat.dvd_refl : ∀ a, dvd a a
    /// - Nat.dvd_trans : ∀ a b c, dvd a b → dvd b c → dvd a c
    /// - Nat.one_dvd : ∀ a, dvd 1 a
    /// - Nat.dvd_zero : ∀ a, dvd a 0
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_gcd_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_gcd(&mut self) -> Result<(), EnvError> {
        if self.nat_gcd_init {
            return Ok(());
        }

        // Dependencies: need Nat type, equality, and Exists for Nat.dvd.
        self.init_nat()?;
        self.init_eq()?;
        self.init_exists()?;
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Nat.dvd : Nat → Nat → Prop
        // dvd a b means ∃ c : Nat, b = a * c (a divides b)
        let dvd_type = Expr::pi(
            BinderInfo::Default,
            nat_type.clone(),
            Expr::pi(BinderInfo::Default, nat_type.clone(), prop.clone()),
        );

        // The definition uses Exists: ∃ c : Nat, b = a * c
        // dvd := fun a b => ∃ c : Nat, Eq Nat b (mul a c)
        let dvd_value = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let (b_id, bv) = bl.fresh_local(nat_type.clone());
            let predicate = {
                let mut sub = EnvDeclBuilder::child_of(&bl);
                let (c_id, c) = sub.fresh_local(nat_type.clone());
                let a_times_c = Expr::app(Expr::app(nat_mul.clone(), a.clone()), c);
                let eq = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                            nat_type.clone(),
                        ),
                        bv.clone(),
                    ),
                    a_times_c,
                );
                let lam = sub.mk_lam(c_id, BinderInfo::Default, nat_type.clone(), eq);
                sub.finish_child(lam)
            };
            let body = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Exists"),
                        vec![Level::succ(Level::zero())],
                    ),
                    nat_type.clone(),
                ),
                predicate,
            );
            let r = bl.mk_lam(b_id, BinderInfo::Default, nat_type.clone(), body);
            let r = bl.mk_lam(a_id, BinderInfo::Default, nat_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.dvd"),
            level_params: vec![],
            type_: dvd_type.clone(),
            value: dvd_value,
            is_reducible: true,
        })?;

        // Nat.gcd : Nat → Nat → Nat
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.gcd"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                nat_type.clone(),
                Expr::pi(BinderInfo::Default, nat_type.clone(), nat_type.clone()),
            ),
        })?;

        // Nat.lcm : Nat → Nat → Nat
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.lcm"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                nat_type.clone(),
                Expr::pi(BinderInfo::Default, nat_type.clone(), nat_type.clone()),
            ),
        })?;

        let nat_dvd = Expr::const_(Name::from_string("Nat.dvd"), vec![]);
        let nat_gcd = Expr::const_(Name::from_string("Nat.gcd"), vec![]);
        let nat_lcm = Expr::const_(Name::from_string("Nat.lcm"), vec![]);

        // Nat.gcd_dvd_left : ∀ a b : Nat, dvd (gcd a b) a
        let gcd_dvd_left_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let (b_id, bv) = bl.fresh_local(nat_type.clone());
            let gcd_a_b = Expr::app(Expr::app(nat_gcd.clone(), a.clone()), bv);
            let body = Expr::app(Expr::app(nat_dvd.clone(), gcd_a_b), a);
            let r = bl.mk_pi(b_id, BinderInfo::Default, nat_type.clone(), body);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.gcd_dvd_left"),
            level_params: vec![],
            type_: gcd_dvd_left_type,
        })?;

        // Nat.gcd_dvd_right : ∀ a b : Nat, dvd (gcd a b) b
        let gcd_dvd_right_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let (b_id, bv) = bl.fresh_local(nat_type.clone());
            let gcd_a_b = Expr::app(Expr::app(nat_gcd.clone(), a), bv.clone());
            let body = Expr::app(Expr::app(nat_dvd.clone(), gcd_a_b), bv);
            let r = bl.mk_pi(b_id, BinderInfo::Default, nat_type.clone(), body);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.gcd_dvd_right"),
            level_params: vec![],
            type_: gcd_dvd_right_type,
        })?;

        // Nat.dvd_gcd : ∀ c a b : Nat, dvd c a → dvd c b → dvd c (gcd a b)
        let dvd_gcd_type = {
            let mut bl = EnvDeclBuilder::new();
            let (c_id, c) = bl.fresh_local(nat_type.clone());
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let (b_id, bv) = bl.fresh_local(nat_type.clone());
            let dvd_c_a = Expr::app(Expr::app(nat_dvd.clone(), c.clone()), a.clone());
            let dvd_c_b = Expr::app(Expr::app(nat_dvd.clone(), c.clone()), bv.clone());
            let gcd_a_b = Expr::app(Expr::app(nat_gcd.clone(), a), bv);
            let dvd_c_gcd = Expr::app(Expr::app(nat_dvd.clone(), c), gcd_a_b);
            let (h1_id, _) = bl.fresh_local(dvd_c_a.clone());
            let (h2_id, _) = bl.fresh_local(dvd_c_b.clone());
            let r = bl.mk_pi(h2_id, BinderInfo::Default, dvd_c_b, dvd_c_gcd);
            let r = bl.mk_pi(h1_id, BinderInfo::Default, dvd_c_a, r);
            let r = bl.mk_pi(b_id, BinderInfo::Default, nat_type.clone(), r);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), r);
            let r = bl.mk_pi(c_id, BinderInfo::Default, nat_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dvd_gcd"),
            level_params: vec![],
            type_: dvd_gcd_type,
        })?;

        // Nat.gcd_mul_lcm : ∀ a b : Nat, Eq (mul (gcd a b) (lcm a b)) (mul a b)
        let gcd_mul_lcm_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let (b_id, bv) = bl.fresh_local(nat_type.clone());
            let gcd_a_b = Expr::app(Expr::app(nat_gcd.clone(), a.clone()), bv.clone());
            let lcm_a_b = Expr::app(Expr::app(nat_lcm.clone(), a.clone()), bv.clone());
            let lhs = Expr::app(Expr::app(nat_mul.clone(), gcd_a_b), lcm_a_b);
            let a_times_b = Expr::app(Expr::app(nat_mul.clone(), a), bv);
            let eq = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        nat_type.clone(),
                    ),
                    lhs,
                ),
                a_times_b,
            );
            let r = bl.mk_pi(b_id, BinderInfo::Default, nat_type.clone(), eq);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.gcd_mul_lcm"),
            level_params: vec![],
            type_: gcd_mul_lcm_type,
        })?;

        // Nat.gcd_comm : ∀ a b : Nat, Eq (gcd a b) (gcd b a)
        let gcd_comm_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let (b_id, bv) = bl.fresh_local(nat_type.clone());
            let gcd_a_b = Expr::app(Expr::app(nat_gcd.clone(), a.clone()), bv.clone());
            let gcd_b_a = Expr::app(Expr::app(nat_gcd.clone(), bv), a);
            let eq = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        nat_type.clone(),
                    ),
                    gcd_a_b,
                ),
                gcd_b_a,
            );
            let r = bl.mk_pi(b_id, BinderInfo::Default, nat_type.clone(), eq);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.gcd_comm"),
            level_params: vec![],
            type_: gcd_comm_type,
        })?;

        // Nat.lcm_comm : ∀ a b : Nat, Eq (lcm a b) (lcm b a)
        let lcm_comm_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let (b_id, bv) = bl.fresh_local(nat_type.clone());
            let lcm_a_b = Expr::app(Expr::app(nat_lcm.clone(), a.clone()), bv.clone());
            let lcm_b_a = Expr::app(Expr::app(nat_lcm.clone(), bv), a);
            let eq = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        nat_type.clone(),
                    ),
                    lcm_a_b,
                ),
                lcm_b_a,
            );
            let r = bl.mk_pi(b_id, BinderInfo::Default, nat_type.clone(), eq);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.lcm_comm"),
            level_params: vec![],
            type_: lcm_comm_type,
        })?;

        // Extended properties (dvd_refl, dvd_trans, one_dvd, dvd_zero, assoc, zero/one, self)
        self.init_nat_gcd_extended_props()?;

        self.nat_gcd_init = true;
        Ok(())
    }

    /// Check if Nat GCD/LCM axioms have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_gcd_init == true`
    pub(crate) fn has_nat_gcd(&self) -> bool {
        self.nat_gcd_init
    }
}
