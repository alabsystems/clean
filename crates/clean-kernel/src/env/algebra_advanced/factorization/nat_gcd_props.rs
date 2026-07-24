// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Nat GCD properties (dvd_refl, dvd_trans, assoc, zero/one identities, self).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize extended Nat GCD/LCM properties.
    ///
    /// Called by `init_nat_gcd` after core definitions are added.
    /// Adds: dvd_refl, dvd_trans, one_dvd, dvd_zero, gcd_assoc, lcm_assoc,
    /// gcd_zero_left/right, lcm_zero_left/right, gcd_one_left/right, gcd_self, lcm_self
    pub(super) fn init_nat_gcd_extended_props(&mut self) -> Result<(), EnvError> {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero.clone(),
        );
        let nat_dvd = Expr::const_(Name::from_string("Nat.dvd"), vec![]);
        let nat_gcd = Expr::const_(Name::from_string("Nat.gcd"), vec![]);
        let nat_lcm = Expr::const_(Name::from_string("Nat.lcm"), vec![]);

        // Nat.dvd_refl : ∀ a : Nat, dvd a a
        let dvd_refl_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let body = Expr::app(Expr::app(nat_dvd.clone(), a.clone()), a);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), body);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dvd_refl"),
            level_params: vec![],
            type_: dvd_refl_type,
        })?;

        // Nat.dvd_trans : ∀ a b c : Nat, dvd a b → dvd b c → dvd a c
        let dvd_trans_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let (b_id, bv) = bl.fresh_local(nat_type.clone());
            let (c_id, c) = bl.fresh_local(nat_type.clone());
            let dvd_a_b = Expr::app(Expr::app(nat_dvd.clone(), a.clone()), bv.clone());
            let dvd_b_c = Expr::app(Expr::app(nat_dvd.clone(), bv), c.clone());
            let dvd_a_c = Expr::app(Expr::app(nat_dvd.clone(), a), c);
            let (h1_id, _) = bl.fresh_local(dvd_a_b.clone());
            let (h2_id, _) = bl.fresh_local(dvd_b_c.clone());
            let r = bl.mk_pi(h2_id, BinderInfo::Default, dvd_b_c, dvd_a_c);
            let r = bl.mk_pi(h1_id, BinderInfo::Default, dvd_a_b, r);
            let r = bl.mk_pi(c_id, BinderInfo::Default, nat_type.clone(), r);
            let r = bl.mk_pi(b_id, BinderInfo::Default, nat_type.clone(), r);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dvd_trans"),
            level_params: vec![],
            type_: dvd_trans_type,
        })?;

        // Nat.one_dvd : ∀ a : Nat, dvd 1 a
        let one_dvd_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let body = Expr::app(Expr::app(nat_dvd.clone(), nat_one.clone()), a);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), body);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.one_dvd"),
            level_params: vec![],
            type_: one_dvd_type,
        })?;

        // Nat.dvd_zero : ∀ a : Nat, dvd a 0
        let dvd_zero_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let body = Expr::app(Expr::app(nat_dvd.clone(), a), nat_zero.clone());
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), body);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dvd_zero"),
            level_params: vec![],
            type_: dvd_zero_type,
        })?;

        // Helper: build Eq Nat lhs rhs
        let mk_nat_eq = |lhs: Expr, rhs: Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        nat_type.clone(),
                    ),
                    lhs,
                ),
                rhs,
            )
        };

        // Nat.gcd_assoc : ∀ a b c : Nat, Eq (gcd (gcd a b) c) (gcd a (gcd b c))
        let gcd_assoc_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let (b_id, bv) = bl.fresh_local(nat_type.clone());
            let (c_id, c) = bl.fresh_local(nat_type.clone());
            let gcd_a_b = Expr::app(Expr::app(nat_gcd.clone(), a.clone()), bv.clone());
            let lhs = Expr::app(Expr::app(nat_gcd.clone(), gcd_a_b), c.clone());
            let gcd_b_c = Expr::app(Expr::app(nat_gcd.clone(), bv), c);
            let rhs = Expr::app(Expr::app(nat_gcd.clone(), a), gcd_b_c);
            let eq = mk_nat_eq(lhs, rhs);
            let r = bl.mk_pi(c_id, BinderInfo::Default, nat_type.clone(), eq);
            let r = bl.mk_pi(b_id, BinderInfo::Default, nat_type.clone(), r);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.gcd_assoc"),
            level_params: vec![],
            type_: gcd_assoc_type,
        })?;

        // Nat.lcm_assoc : ∀ a b c : Nat, Eq (lcm (lcm a b) c) (lcm a (lcm b c))
        let lcm_assoc_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let (b_id, bv) = bl.fresh_local(nat_type.clone());
            let (c_id, c) = bl.fresh_local(nat_type.clone());
            let lcm_a_b = Expr::app(Expr::app(nat_lcm.clone(), a.clone()), bv.clone());
            let lhs = Expr::app(Expr::app(nat_lcm.clone(), lcm_a_b), c.clone());
            let lcm_b_c = Expr::app(Expr::app(nat_lcm.clone(), bv), c);
            let rhs = Expr::app(Expr::app(nat_lcm.clone(), a), lcm_b_c);
            let eq = mk_nat_eq(lhs, rhs);
            let r = bl.mk_pi(c_id, BinderInfo::Default, nat_type.clone(), eq);
            let r = bl.mk_pi(b_id, BinderInfo::Default, nat_type.clone(), r);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.lcm_assoc"),
            level_params: vec![],
            type_: lcm_assoc_type,
        })?;

        // Nat.gcd_zero_left : ∀ a : Nat, Eq (gcd 0 a) a
        let gcd_zero_left_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let gcd_zero_a = Expr::app(Expr::app(nat_gcd.clone(), nat_zero.clone()), a.clone());
            let eq = mk_nat_eq(gcd_zero_a, a);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), eq);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.gcd_zero_left"),
            level_params: vec![],
            type_: gcd_zero_left_type,
        })?;

        // Nat.gcd_zero_right : ∀ a : Nat, Eq (gcd a 0) a
        let gcd_zero_right_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let gcd_a_zero = Expr::app(Expr::app(nat_gcd.clone(), a.clone()), nat_zero.clone());
            let eq = mk_nat_eq(gcd_a_zero, a);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), eq);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.gcd_zero_right"),
            level_params: vec![],
            type_: gcd_zero_right_type,
        })?;

        // Nat.lcm_zero_left : ∀ a : Nat, Eq (lcm 0 a) 0
        let lcm_zero_left_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let lcm_zero_a = Expr::app(Expr::app(nat_lcm.clone(), nat_zero.clone()), a);
            let eq = mk_nat_eq(lcm_zero_a, nat_zero.clone());
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), eq);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.lcm_zero_left"),
            level_params: vec![],
            type_: lcm_zero_left_type,
        })?;

        // Nat.lcm_zero_right : ∀ a : Nat, Eq (lcm a 0) 0
        let lcm_zero_right_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let lcm_a_zero = Expr::app(Expr::app(nat_lcm.clone(), a), nat_zero.clone());
            let eq = mk_nat_eq(lcm_a_zero, nat_zero.clone());
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), eq);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.lcm_zero_right"),
            level_params: vec![],
            type_: lcm_zero_right_type,
        })?;

        // Nat.gcd_one_left : ∀ a : Nat, Eq (gcd 1 a) 1
        let gcd_one_left_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let gcd_one_a = Expr::app(Expr::app(nat_gcd.clone(), nat_one.clone()), a);
            let eq = mk_nat_eq(gcd_one_a, nat_one.clone());
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), eq);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.gcd_one_left"),
            level_params: vec![],
            type_: gcd_one_left_type,
        })?;

        // Nat.gcd_one_right : ∀ a : Nat, Eq (gcd a 1) 1
        let gcd_one_right_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let gcd_a_one = Expr::app(Expr::app(nat_gcd.clone(), a), nat_one.clone());
            let eq = mk_nat_eq(gcd_a_one, nat_one.clone());
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), eq);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.gcd_one_right"),
            level_params: vec![],
            type_: gcd_one_right_type,
        })?;

        // Nat.gcd_self : ∀ a : Nat, Eq (gcd a a) a
        let gcd_self_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let gcd_a_a = Expr::app(Expr::app(nat_gcd.clone(), a.clone()), a.clone());
            let eq = mk_nat_eq(gcd_a_a, a);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), eq);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.gcd_self"),
            level_params: vec![],
            type_: gcd_self_type,
        })?;

        // Nat.lcm_self : ∀ a : Nat, Eq (lcm a a) a
        let lcm_self_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(nat_type.clone());
            let lcm_a_a = Expr::app(Expr::app(nat_lcm.clone(), a.clone()), a.clone());
            let eq = mk_nat_eq(lcm_a_a, a);
            let r = bl.mk_pi(a_id, BinderInfo::Default, nat_type.clone(), eq);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.lcm_self"),
            level_params: vec![],
            type_: lcm_self_type,
        })?;

        Ok(())
    }
}
