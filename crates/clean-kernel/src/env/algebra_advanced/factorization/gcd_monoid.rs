// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! GcdMonoid typeclass and Nat instance.

use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::Declaration;
use crate::env::{Constructor, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the GcdMonoid typeclass
    ///
    /// GcdMonoid is a typeclass for commutative monoids with gcd and lcm operations.
    /// In Mathlib it extends CommMonoid with:
    /// - gcd : α → α → α
    /// - lcm : α → α → α
    /// - gcd_dvd_left : ∀ a b, gcd a b ∣ a
    /// - gcd_dvd_right : ∀ a b, gcd a b ∣ b
    /// - dvd_gcd : ∀ {c a b}, c ∣ a → c ∣ b → c ∣ gcd a b
    /// - gcd_mul_lcm : ∀ a b, Associated (gcd a b * lcm a b) (a * b)
    /// - lcm_zero_left : ∀ a, lcm 0 a = 0
    /// - lcm_zero_right : ∀ a, lcm a 0 = 0
    ///
    /// For simplicity, we use exact equality instead of Associated (appropriate for Nat).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.gcd_monoid_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_gcd_monoid(&mut self) -> Result<(), EnvError> {
        if self.gcd_monoid_init {
            return Ok(());
        }

        // Dependencies
        self.init_comm_monoid()?;
        self.init_eq()?;
        self.init_exists()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1) // Type u

        // GcdMonoid extends CommMonoid with 10 new fields:
        // Fields from CommMonoid (5):
        // 0: mul : α → α → α
        // 1: mul_assoc
        // 2: one : α
        // 3: one_mul
        // 4: mul_one
        // 5: mul_comm
        //
        // New GcdMonoid fields (10):
        // 6: gcd : α → α → α
        // 7: lcm : α → α → α
        // 8: gcd_dvd_left : ∀ a b, Dvd.dvd (gcd a b) a (where Dvd.dvd is ∃ c, a = gcd * c)
        // 9: gcd_dvd_right : ∀ a b, Dvd.dvd (gcd a b) b
        // 10: dvd_gcd : ∀ {c a b}, Dvd.dvd c a → Dvd.dvd c b → Dvd.dvd c (gcd a b)
        // 11: gcd_mul_lcm : ∀ a b, Eq (mul (gcd a b) (lcm a b)) (mul a b)
        // 12: lcm_zero_left : ∀ a, Eq (lcm zero a) zero (where zero is monoid's identity)
        // 13: lcm_zero_right : ∀ a, Eq (lcm a zero) zero
        // 14: gcd_zero_left : ∀ a, Eq (gcd zero a) a
        // 15: gcd_zero_right : ∀ a, Eq (gcd a zero) a
        //
        // Note: We need a zero element for GcdMonoid. In Mathlib, GcdMonoid extends
        // CommMonoidWithZero. We'll add a zero field.

        // Actually, let's simplify. GcdMonoid in our formalization:
        // - Extends CommMonoid (already has mul, one, associativity, commutativity)
        // - Adds: zero, gcd, lcm, and their properties

        // Build GcdMonoid.mk constructor type with EnvDeclBuilder
        // Fields: mul, mul_assoc, one, one_mul, mul_one, mul_comm,
        //         zero, zero_mul, mul_zero, gcd, lcm,
        //         gcd_dvd_left, gcd_dvd_right, gcd_mul_lcm,
        //         lcm_zero_left, lcm_zero_right
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let exists_const = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(u_level.clone())],
        );

        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());

            // Field 0: mul : α → α → α
            let mul_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = s.fresh_local(alpha.clone());
                let (y_id, _) = s.fresh_local(alpha.clone());
                let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), alpha.clone());
                s.finish_child(s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r))
            };
            let (mul_id, mul) = b.fresh_local(mul_type.clone());

            // Field 1: mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
            let mul_assoc_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let (c_id, c) = s.fresh_local(alpha.clone());
                let mul_a_b = Expr::app(Expr::app(mul.clone(), a.clone()), bv.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), mul_a_b), c.clone());
                let mul_b_c = Expr::app(Expr::app(mul.clone(), bv), c);
                let rhs = Expr::app(Expr::app(mul.clone(), a), mul_b_c);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    rhs,
                );
                let r = s.mk_pi(c_id, BinderInfo::Default, alpha.clone(), eq);
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r))
            };
            let (mul_assoc_id, _) = b.fresh_local(mul_assoc_type.clone());

            // Field 2: one : α
            let (one_id, one) = b.fresh_local(alpha.clone());

            // Field 3: one_mul : ∀ a, mul one a = a
            let one_mul_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), one.clone()), a.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    a,
                );
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq))
            };
            let (one_mul_id, _) = b.fresh_local(one_mul_type.clone());

            // Field 4: mul_one : ∀ a, mul a one = a
            let mul_one_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), a.clone()), one.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    a,
                );
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq))
            };
            let (mul_one_id, _) = b.fresh_local(mul_one_type.clone());

            // Field 5: mul_comm : ∀ a b, mul a b = mul b a
            let mul_comm_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), a.clone()), bv.clone());
                let rhs = Expr::app(Expr::app(mul.clone(), bv), a);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    rhs,
                );
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r))
            };
            let (mul_comm_id, _) = b.fresh_local(mul_comm_type.clone());

            // Field 6: zero : α
            let (zero_id, zero) = b.fresh_local(alpha.clone());

            // Field 7: zero_mul : ∀ a, mul zero a = zero
            let zero_mul_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), zero.clone()), a);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    zero.clone(),
                );
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq))
            };
            let (zero_mul_id, _) = b.fresh_local(zero_mul_type.clone());

            // Field 8: mul_zero : ∀ a, mul a zero = zero
            let mul_zero_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), a), zero.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    zero.clone(),
                );
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq))
            };
            let (mul_zero_id, _) = b.fresh_local(mul_zero_type.clone());

            // Field 9: gcd : α → α → α
            let gcd_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = s.fresh_local(alpha.clone());
                let (y_id, _) = s.fresh_local(alpha.clone());
                let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), alpha.clone());
                s.finish_child(s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r))
            };
            let (gcd_id, gcd) = b.fresh_local(gcd_type.clone());

            // Field 10: lcm : α → α → α
            let lcm_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = s.fresh_local(alpha.clone());
                let (y_id, _) = s.fresh_local(alpha.clone());
                let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), alpha.clone());
                s.finish_child(s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r))
            };
            let (lcm_id, lcm) = b.fresh_local(lcm_type.clone());

            // Helper: build ∃ c : α, Eq α lhs_val (mul rhs_base c)
            let mk_dvd_exists = |b: &EnvDeclBuilder, lhs_val: Expr, rhs_base: Expr| -> Expr {
                let mut s = EnvDeclBuilder::child_of(b);
                let (c_id, c) = s.fresh_local(alpha.clone());
                let rhs = Expr::app(Expr::app(mul.clone(), rhs_base), c);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs_val),
                    rhs,
                );
                let pred = s.mk_lam(c_id, BinderInfo::Default, alpha.clone(), eq);
                let pred = s.finish_child(pred);
                Expr::app(Expr::app(exists_const.clone(), alpha.clone()), pred)
            };

            // Field 11: gcd_dvd_left : ∀ a b, ∃ c, a = mul (gcd a b) c
            let gcd_dvd_left_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let gcd_a_b = Expr::app(Expr::app(gcd.clone(), a.clone()), bv);
                let body = mk_dvd_exists(&s, a, gcd_a_b);
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), body);
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r))
            };
            let (gcd_dvd_left_id, _) = b.fresh_local(gcd_dvd_left_type.clone());

            // Field 12: gcd_dvd_right : ∀ a b, ∃ c, b = mul (gcd a b) c
            let gcd_dvd_right_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let gcd_a_b = Expr::app(Expr::app(gcd.clone(), a), bv.clone());
                let body = mk_dvd_exists(&s, bv, gcd_a_b);
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), body);
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r))
            };
            let (gcd_dvd_right_id, _) = b.fresh_local(gcd_dvd_right_type.clone());

            // Field 13: gcd_mul_lcm : ∀ a b, mul (gcd a b) (lcm a b) = mul a b
            let gcd_mul_lcm_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let gcd_a_b = Expr::app(Expr::app(gcd.clone(), a.clone()), bv.clone());
                let lcm_a_b = Expr::app(Expr::app(lcm.clone(), a.clone()), bv.clone());
                let lhs = Expr::app(Expr::app(mul.clone(), gcd_a_b), lcm_a_b);
                let rhs = Expr::app(Expr::app(mul.clone(), a), bv);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    rhs,
                );
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r))
            };
            let (gcd_mul_lcm_id, _) = b.fresh_local(gcd_mul_lcm_type.clone());

            // Field 14: lcm_zero_left : ∀ a, lcm zero a = zero
            let lcm_zero_left_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(lcm.clone(), zero.clone()), a);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    zero.clone(),
                );
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq))
            };
            let (lcm_zero_left_id, _) = b.fresh_local(lcm_zero_left_type.clone());

            // Field 15: lcm_zero_right : ∀ a, lcm a zero = zero
            let lcm_zero_right_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(lcm.clone(), a), zero.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    zero.clone(),
                );
                s.finish_child(s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq))
            };
            let (lcm_zero_right_id, _) = b.fresh_local(lcm_zero_right_type.clone());

            // Result type: GcdMonoid α
            let result = Expr::app(
                Expr::const_(Name::from_string("GcdMonoid"), vec![u_level.clone()]),
                alpha.clone(),
            );

            // Chain mk_pi in reverse field order (innermost first)
            let r = b.mk_pi(
                lcm_zero_right_id,
                BinderInfo::Default,
                lcm_zero_right_type,
                result,
            );
            let r = b.mk_pi(lcm_zero_left_id, BinderInfo::Default, lcm_zero_left_type, r);
            let r = b.mk_pi(gcd_mul_lcm_id, BinderInfo::Default, gcd_mul_lcm_type, r);
            let r = b.mk_pi(gcd_dvd_right_id, BinderInfo::Default, gcd_dvd_right_type, r);
            let r = b.mk_pi(gcd_dvd_left_id, BinderInfo::Default, gcd_dvd_left_type, r);
            let r = b.mk_pi(lcm_id, BinderInfo::Default, lcm_type, r);
            let r = b.mk_pi(gcd_id, BinderInfo::Default, gcd_type, r);
            let r = b.mk_pi(mul_zero_id, BinderInfo::Default, mul_zero_type, r);
            let r = b.mk_pi(zero_mul_id, BinderInfo::Default, zero_mul_type, r);
            let r = b.mk_pi(zero_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(mul_comm_id, BinderInfo::Default, mul_comm_type, r);
            let r = b.mk_pi(mul_one_id, BinderInfo::Default, mul_one_type, r);
            let r = b.mk_pi(one_mul_id, BinderInfo::Default, one_mul_type, r);
            let r = b.mk_pi(one_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(mul_assoc_id, BinderInfo::Default, mul_assoc_type, r);
            let r = b.mk_pi(mul_id, BinderInfo::Default, mul_type, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("GcdMonoid"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    type_u.clone(),
                    Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
                ),
                constructors: vec![Constructor {
                    name: Name::from_string("GcdMonoid.mk"),
                    type_: ctor_type,
                }],
            }],
        })?;

        self.gcd_monoid_init = true;
        Ok(())
    }

    /// Check if GcdMonoid typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.gcd_monoid_init == true`
    #[cfg(test)]
    pub(crate) fn has_gcd_monoid(&self) -> bool {
        self.gcd_monoid_init
    }

    /// Initialize the Nat GcdMonoid instance
    ///
    /// Nat forms a GcdMonoid with Nat.mul, Nat.one, Nat.zero, Nat.gcd, Nat.lcm
    /// and all the associated properties.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_gcd_monoid_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_nat_gcd_monoid_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_gcd_monoid_inst_init {
            return Ok(());
        }

        // Dependencies
        self.init_gcd_monoid()?;
        self.init_nat_gcd()?;
        self.init_nat_mul_inst()?;
        self.init_nat_arith_lemmas()?; // Nat.mul_assoc, Nat.one_mul, Nat.mul_one, Nat.mul_comm, etc.

        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);

        // The instance is GcdMonoid.mk applied to all Nat operations
        // GcdMonoid.mk {Nat} Nat.mul Nat.mul_assoc Nat.one Nat.one_mul Nat.mul_one Nat.mul_comm
        //              Nat.zero Nat.zero_mul Nat.mul_zero Nat.gcd Nat.lcm
        //              Nat.gcd_dvd_left Nat.gcd_dvd_right Nat.gcd_mul_lcm
        //              Nat.lcm_zero_left Nat.lcm_zero_right
        let inst_value = {
            // GcdMonoid.mk.{u} takes {α : Type u}. Nat : Type 0, so u = 0.
            let mk = Expr::const_(Name::from_string("GcdMonoid.mk"), vec![Level::zero()]);
            let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
            let nat_mul_assoc = Expr::const_(Name::from_string("Nat.mul_assoc"), vec![]);
            let nat_one = Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::const_(Name::from_string("Nat.zero"), vec![]),
            );
            let nat_one_mul = Expr::const_(Name::from_string("Nat.one_mul"), vec![]);
            let nat_mul_one = Expr::const_(Name::from_string("Nat.mul_one"), vec![]);
            let nat_mul_comm = Expr::const_(Name::from_string("Nat.mul_comm"), vec![]);
            let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let nat_zero_mul = Expr::const_(Name::from_string("Nat.zero_mul"), vec![]);
            let nat_mul_zero = Expr::const_(Name::from_string("Nat.mul_zero"), vec![]);
            let nat_gcd = Expr::const_(Name::from_string("Nat.gcd"), vec![]);
            let nat_lcm = Expr::const_(Name::from_string("Nat.lcm"), vec![]);
            let nat_gcd_dvd_left = Expr::const_(Name::from_string("Nat.gcd_dvd_left"), vec![]);
            let nat_gcd_dvd_right = Expr::const_(Name::from_string("Nat.gcd_dvd_right"), vec![]);
            let nat_gcd_mul_lcm = Expr::const_(Name::from_string("Nat.gcd_mul_lcm"), vec![]);
            let nat_lcm_zero_left = Expr::const_(Name::from_string("Nat.lcm_zero_left"), vec![]);
            let nat_lcm_zero_right = Expr::const_(Name::from_string("Nat.lcm_zero_right"), vec![]);

            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                Expr::app(
                                                    Expr::app(
                                                        Expr::app(
                                                            Expr::app(
                                                                Expr::app(
                                                                    Expr::app(
                                                                        Expr::app(
                                                                            Expr::app(
                                                                                mk,
                                                                                nat_type.clone(),
                                                                            ),
                                                                            nat_mul,
                                                                        ),
                                                                        nat_mul_assoc,
                                                                    ),
                                                                    nat_one,
                                                                ),
                                                                nat_one_mul,
                                                            ),
                                                            nat_mul_one,
                                                        ),
                                                        nat_mul_comm,
                                                    ),
                                                    nat_zero,
                                                ),
                                                nat_zero_mul,
                                            ),
                                            nat_mul_zero,
                                        ),
                                        nat_gcd,
                                    ),
                                    nat_lcm,
                                ),
                                nat_gcd_dvd_left,
                            ),
                            nat_gcd_dvd_right,
                        ),
                        nat_gcd_mul_lcm,
                    ),
                    nat_lcm_zero_left,
                ),
                nat_lcm_zero_right,
            )
        };

        // GcdMonoid.{u} takes {α : Type u}. Nat : Type 0, so u = 0.
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("GcdMonoid"), vec![Level::zero()]),
            nat_type,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instGcdMonoidNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_gcd_monoid_inst_init = true;
        Ok(())
    }

    /// Check if Nat GcdMonoid instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_gcd_monoid_inst_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_gcd_monoid_inst(&self) -> bool {
        self.nat_gcd_monoid_inst_init
    }
}
