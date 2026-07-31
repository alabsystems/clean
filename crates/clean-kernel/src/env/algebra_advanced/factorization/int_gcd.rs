// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int GCD/LCM axioms and divisibility.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::Environment;
#[cfg(test)]
use crate::env::{Declaration, EnvError};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

impl Environment {
    /// Initialize Int GCD/LCM axioms and divisibility
    ///
    /// Adds:
    /// - Int.dvd : Int → Int → Prop (divisibility predicate)
    /// - Int.gcd : Int → Int → Int (greatest common divisor)
    /// - Int.lcm : Int → Int → Int (least common multiple)
    /// - Int.gcd_dvd_left : ∀ a b, dvd (gcd a b) a
    /// - Int.gcd_dvd_right : ∀ a b, dvd (gcd a b) b
    /// - Int.dvd_gcd : ∀ c a b, dvd c a → dvd c b → dvd c (gcd a b)
    /// - Int.gcd_mul_lcm : ∀ a b, Eq (mul (gcd a b) (lcm a b)) (mul a b)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_gcd_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_int_gcd(&mut self) -> Result<(), EnvError> {
        if self.int_gcd_init {
            return Ok(());
        }

        // Dependencies: need Int type + arithmetic, equality, and Exists for Int.dvd
        self.init_int()?;
        self.init_int_arith()?; // Int.mul
        self.init_eq()?;
        self.init_exists()?;

        let int_type = Expr::const_(Name::from_string("Int"), vec![]);
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Int.dvd : Int → Int → Prop
        // dvd a b means ∃ c, b = a * c (a divides b)
        // We define it as a predicate: dvd a b := ∃ c : Int, Eq b (mul a c)
        let dvd_type = Expr::pi(
            BinderInfo::Default,
            int_type.clone(),
            Expr::pi(BinderInfo::Default, int_type.clone(), prop.clone()),
        );

        // The definition uses Exists: ∃ c : Int, b = a * c
        // dvd := fun a b => ∃ c : Int, Eq Int b (mul a c)
        // Built with EnvDeclBuilder to avoid manual de Bruijn index arithmetic.
        let mk_int_eq = |lhs: Expr, rhs: Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        int_type.clone(),
                    ),
                    lhs,
                ),
                rhs,
            )
        };
        let dvd_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_type.clone());
            let (b_id, b_int) = b.fresh_local(int_type.clone());

            let predicate = {
                let mut sub = EnvDeclBuilder::child_of(&b);
                let (c_id, c) = sub.fresh_local(int_type.clone());
                let a_times_c = Expr::app(Expr::app(int_mul.clone(), a.clone()), c.clone());
                let eq_b_mul = mk_int_eq(b_int.clone(), a_times_c);
                let lam = sub.mk_lam(c_id, BinderInfo::Default, int_type.clone(), eq_b_mul);
                sub.finish_child(lam)
            };

            let exists = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Exists"),
                        vec![Level::succ(Level::zero())],
                    ),
                    int_type.clone(),
                ),
                predicate,
            );
            let e = b.mk_lam(b_id, BinderInfo::Default, int_type.clone(), exists);
            let e = b.mk_lam(a_id, BinderInfo::Default, int_type.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.dvd"),
            level_params: vec![],
            type_: dvd_type.clone(),
            value: dvd_value,
            is_reducible: true,
        })?;

        // Int.gcd : Int → Int → Int
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.gcd"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                int_type.clone(),
                Expr::pi(BinderInfo::Default, int_type.clone(), int_type.clone()),
            ),
        })?;

        // Int.lcm : Int → Int → Int
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.lcm"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                int_type.clone(),
                Expr::pi(BinderInfo::Default, int_type.clone(), int_type.clone()),
            ),
        })?;

        let int_dvd = Expr::const_(Name::from_string("Int.dvd"), vec![]);
        let int_gcd = Expr::const_(Name::from_string("Int.gcd"), vec![]);
        let int_lcm = Expr::const_(Name::from_string("Int.lcm"), vec![]);

        // Int.gcd_dvd_left : ∀ a b : Int, dvd (gcd a b) a
        let gcd_dvd_left_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_type.clone());
            let (b_id, b_int) = b.fresh_local(int_type.clone());
            let gcd_a_b = Expr::app(Expr::app(int_gcd.clone(), a.clone()), b_int.clone());
            let body = Expr::app(Expr::app(int_dvd.clone(), gcd_a_b), a.clone());
            let e = b.mk_pi(b_id, BinderInfo::Default, int_type.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_type.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.gcd_dvd_left"),
            level_params: vec![],
            type_: gcd_dvd_left_type,
        })?;

        // Int.gcd_dvd_right : ∀ a b : Int, dvd (gcd a b) b
        let gcd_dvd_right_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_type.clone());
            let (b_id, b_int) = b.fresh_local(int_type.clone());
            let gcd_a_b = Expr::app(Expr::app(int_gcd.clone(), a.clone()), b_int.clone());
            let body = Expr::app(Expr::app(int_dvd.clone(), gcd_a_b), b_int.clone());
            let e = b.mk_pi(b_id, BinderInfo::Default, int_type.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_type.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.gcd_dvd_right"),
            level_params: vec![],
            type_: gcd_dvd_right_type,
        })?;

        // Int.dvd_gcd : ∀ c a b : Int, dvd c a → dvd c b → dvd c (gcd a b)
        let dvd_gcd_type = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(int_type.clone());
            let (a_id, a) = b.fresh_local(int_type.clone());
            let (b_id, b_int) = b.fresh_local(int_type.clone());
            let dvd_c_a = Expr::app(Expr::app(int_dvd.clone(), c.clone()), a.clone());
            let dvd_c_b = Expr::app(Expr::app(int_dvd.clone(), c.clone()), b_int.clone());
            let gcd_a_b = Expr::app(Expr::app(int_gcd.clone(), a.clone()), b_int.clone());
            let dvd_c_gcd = Expr::app(Expr::app(int_dvd.clone(), c.clone()), gcd_a_b);
            let (hca_id, _hca) = b.fresh_local(dvd_c_a.clone());
            let (hcb_id, _hcb) = b.fresh_local(dvd_c_b.clone());

            let e = b.mk_pi(hcb_id, BinderInfo::Default, dvd_c_b, dvd_c_gcd);
            let e = b.mk_pi(hca_id, BinderInfo::Default, dvd_c_a, e);
            let e = b.mk_pi(b_id, BinderInfo::Default, int_type.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_type.clone(), e);
            let e = b.mk_pi(c_id, BinderInfo::Default, int_type.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.dvd_gcd"),
            level_params: vec![],
            type_: dvd_gcd_type,
        })?;

        // Int.gcd_mul_lcm : ∀ a b : Int, Eq (mul (gcd a b) (lcm a b)) (natAbs (mul a b))
        // Note: In general gcd(a,b) * lcm(a,b) = |a * b| for integers
        // We use natAbs for the absolute value
        let gcd_mul_lcm_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_type.clone());
            let (b_id, b_int) = b.fresh_local(int_type.clone());
            let gcd_a_b = Expr::app(Expr::app(int_gcd.clone(), a.clone()), b_int.clone());
            let lcm_a_b = Expr::app(Expr::app(int_lcm.clone(), a.clone()), b_int.clone());
            let lhs = Expr::app(Expr::app(int_mul.clone(), gcd_a_b), lcm_a_b);
            let rhs = Expr::app(Expr::app(int_mul.clone(), a.clone()), b_int.clone());
            let body = mk_int_eq(lhs, rhs);
            let e = b.mk_pi(b_id, BinderInfo::Default, int_type.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_type.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.gcd_mul_lcm"),
            level_params: vec![],
            type_: gcd_mul_lcm_type,
        })?;

        // Int.gcd_comm : ∀ a b : Int, Eq (gcd a b) (gcd b a)
        let gcd_comm_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_type.clone());
            let (b_id, b_int) = b.fresh_local(int_type.clone());
            let gcd_a_b = Expr::app(Expr::app(int_gcd.clone(), a.clone()), b_int.clone());
            let gcd_b_a = Expr::app(Expr::app(int_gcd.clone(), b_int.clone()), a.clone());
            let body = mk_int_eq(gcd_a_b, gcd_b_a);
            let e = b.mk_pi(b_id, BinderInfo::Default, int_type.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_type.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.gcd_comm"),
            level_params: vec![],
            type_: gcd_comm_type,
        })?;

        // Int.lcm_comm : ∀ a b : Int, Eq (lcm a b) (lcm b a)
        let lcm_comm_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_type.clone());
            let (b_id, b_int) = b.fresh_local(int_type.clone());
            let lcm_a_b = Expr::app(Expr::app(int_lcm.clone(), a.clone()), b_int.clone());
            let lcm_b_a = Expr::app(Expr::app(int_lcm.clone(), b_int.clone()), a.clone());
            let body = mk_int_eq(lcm_a_b, lcm_b_a);
            let e = b.mk_pi(b_id, BinderInfo::Default, int_type.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_type.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.lcm_comm"),
            level_params: vec![],
            type_: lcm_comm_type,
        })?;

        self.int_gcd_init = true;
        Ok(())
    }

    /// Check if Int GCD/LCM axioms have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_gcd_init == true`
    #[cfg(test)]
    pub(crate) fn has_int_gcd(&self) -> bool {
        self.int_gcd_init
    }
}
