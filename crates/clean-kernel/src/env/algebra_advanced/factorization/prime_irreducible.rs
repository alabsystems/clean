// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat.Prime and Irreducible predicates.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Associated and Irreducible predicates
    ///
    /// These are needed for UniqueFactorizationDomain:
    /// - Associated a b := ∃ u : Units α, a = b * u  (for Nat, this simplifies to a = b)
    /// - Irreducible p := p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, p = a * b → IsUnit a ∨ IsUnit b
    /// - Prime p := p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b
    /// - IsUnit a := ∃ b, a * b = 1
    ///
    /// For Nat:
    /// - Associated a b means a = b (since only unit is 1)
    /// - IsUnit a means a = 1
    /// - Irreducible means prime (for Nat, irreducible = prime)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_prime_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_prime(&mut self) -> Result<(), EnvError> {
        if self.nat_prime_init {
            return Ok(());
        }

        // Dependencies
        self.init_nat_gcd()?;
        self.init_eq()?;
        self.init_true_false()?;
        self.init_classical()?; // Or (used in Nat.Prime.dvd_mul)
        self.init_and()?; // And (used in Nat.exists_prime_and_dvd)

        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero.clone(),
        );
        let nat_dvd = Expr::const_(Name::from_string("Nat.dvd"), vec![]);
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Nat.Prime : Nat → Prop
        // Prime p := p ≠ 0 ∧ p ≠ 1 ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b
        // For simplicity, we use the definition: Prime p means p > 1 and divisors are only 1 and p
        // Nat.Prime p := ∃ (h1 : Ne p 0), ∃ (h2 : Ne p 1), ∀ a b : Nat, dvd p (mul a b) → Or (dvd p a) (dvd p b)
        let prime_type = Expr::pi(BinderInfo::Default, nat_type.clone(), prop.clone());

        // Define Prime as an axiom for now (the definition is complex)
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.Prime"),
            level_params: vec![],
            type_: prime_type.clone(),
        })?;

        // Nat.prime_def : ∀ p, Prime p ↔ (p ≠ 0 ∧ p ≠ 1 ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b)
        // This is complex with iff, so we'll add basic properties instead

        // Nat.Prime.ne_zero : ∀ {p}, Prime p → Ne p 0
        let prime_ne_zero_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nat_type.clone());
            let prime_p = Expr::app(
                Expr::const_(Name::from_string("Nat.Prime"), vec![]),
                p.clone(),
            );
            let ne_p_zero = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
                        nat_type.clone(),
                    ),
                    p,
                ),
                nat_zero.clone(),
            );
            let (proof_id, _) = b.fresh_local(prime_p.clone());
            let r = b.mk_pi(proof_id, BinderInfo::Default, prime_p, ne_p_zero);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, nat_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.Prime.ne_zero"),
            level_params: vec![],
            type_: prime_ne_zero_type,
        })?;

        // Nat.Prime.ne_one : ∀ {p}, Prime p → Ne p 1
        let prime_ne_one_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nat_type.clone());
            let prime_p = Expr::app(
                Expr::const_(Name::from_string("Nat.Prime"), vec![]),
                p.clone(),
            );
            let ne_p_one = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
                        nat_type.clone(),
                    ),
                    p,
                ),
                nat_one.clone(),
            );
            let (proof_id, _) = b.fresh_local(prime_p.clone());
            let r = b.mk_pi(proof_id, BinderInfo::Default, prime_p, ne_p_one);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, nat_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.Prime.ne_one"),
            level_params: vec![],
            type_: prime_ne_one_type,
        })?;

        // Nat.Prime.dvd_mul : ∀ {p a b}, Prime p → dvd p (mul a b) → Or (dvd p a) (dvd p b)
        let prime_dvd_mul_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nat_type.clone());
            let (a_id, a) = b.fresh_local(nat_type.clone());
            let (bv_id, bv) = b.fresh_local(nat_type.clone());
            let prime_p = Expr::app(
                Expr::const_(Name::from_string("Nat.Prime"), vec![]),
                p.clone(),
            );
            let a_times_b = Expr::app(Expr::app(nat_mul.clone(), a.clone()), bv.clone());
            let dvd_p_ab = Expr::app(Expr::app(nat_dvd.clone(), p.clone()), a_times_b);
            let dvd_p_a = Expr::app(Expr::app(nat_dvd.clone(), p.clone()), a);
            let dvd_p_b = Expr::app(Expr::app(nat_dvd.clone(), p), bv);
            let or_dvd = Expr::app(
                Expr::app(Expr::const_(Name::from_string("Or"), vec![]), dvd_p_a),
                dvd_p_b,
            );
            let (h2_id, _) = b.fresh_local(dvd_p_ab.clone());
            let (h1_id, _) = b.fresh_local(prime_p.clone());
            let r = b.mk_pi(h2_id, BinderInfo::Default, dvd_p_ab, or_dvd);
            let r = b.mk_pi(h1_id, BinderInfo::Default, prime_p, r);
            let r = b.mk_pi(bv_id, BinderInfo::Implicit, nat_type.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, nat_type.clone(), r);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, nat_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.Prime.dvd_mul"),
            level_params: vec![],
            type_: prime_dvd_mul_type,
        })?;

        // Nat.prime_two : Prime 2
        let two = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_one.clone(),
        );
        let prime_two_type = Expr::app(
            Expr::const_(Name::from_string("Nat.Prime"), vec![]),
            two.clone(),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.prime_two"),
            level_params: vec![],
            type_: prime_two_type,
        })?;

        // Nat.prime_three : Prime 3
        let three = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            two.clone(),
        );
        let prime_three_type =
            Expr::app(Expr::const_(Name::from_string("Nat.Prime"), vec![]), three);

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.prime_three"),
            level_params: vec![],
            type_: prime_three_type,
        })?;

        // Nat.exists_prime_and_dvd : ∀ {n}, n ≠ 1 → ∃ p, Prime p ∧ dvd p n
        // This is a key property for UFD
        let exists_prime_dvd_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_type.clone());
            let ne_n_one = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
                        nat_type.clone(),
                    ),
                    n.clone(),
                ),
                nat_one.clone(),
            );
            // ∃ p : Nat, Prime p ∧ dvd p n
            let predicate = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (p_id, p) = s.fresh_local(nat_type.clone());
                let prime_p = Expr::app(
                    Expr::const_(Name::from_string("Nat.Prime"), vec![]),
                    p.clone(),
                );
                let dvd_p_n = Expr::app(Expr::app(nat_dvd.clone(), p), n.clone());
                let body = Expr::app(
                    Expr::app(Expr::const_(Name::from_string("And"), vec![]), prime_p),
                    dvd_p_n,
                );
                let r = s.mk_lam(p_id, BinderInfo::Default, nat_type.clone(), body);
                s.finish_child(r)
            };
            let exists_p = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Exists"),
                        vec![Level::succ(Level::zero())],
                    ),
                    nat_type.clone(),
                ),
                predicate,
            );
            let (h_id, _) = b.fresh_local(ne_n_one.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, ne_n_one, exists_p);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.exists_prime_and_dvd"),
            level_params: vec![],
            type_: exists_prime_dvd_type,
        })?;

        self.nat_prime_init = true;
        Ok(())
    }

    /// Check if Nat Prime has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_prime_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_prime(&self) -> bool {
        self.nat_prime_init
    }

    /// Initialize Irreducible predicate for integral domains
    ///
    /// Irreducible {α : Type u} [CommMonoidWithZero α] (p : α) : Prop
    /// An element p is irreducible if:
    /// - p ≠ 0
    /// - p is not a unit
    /// - if p = a * b, then a is a unit or b is a unit
    ///
    /// For Nat: irreducible n ↔ n > 1 ∧ ∀ a b, n = a * b → a = 1 ∨ b = 1
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.irreducible_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_irreducible(&mut self) -> Result<(), EnvError> {
        if self.irreducible_init {
            return Ok(());
        }

        // Dependencies
        self.init_integral_domain()?;
        self.init_nat_prime()?;
        self.init_eq()?;
        self.init_true_false()?; // Provides Or

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1) // Type u
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Irreducible : {α : Type u} → [IntegralDomain α] → α → Prop
        let irreducible_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let inst_ty = Expr::app(
                Expr::const_(Name::from_string("IntegralDomain"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, _) = b.fresh_local(inst_ty.clone());
            let (p_id, _) = b.fresh_local(alpha.clone());
            let r = b.mk_pi(p_id, BinderInfo::Default, alpha.clone(), prop.clone());
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Irreducible"),
            level_params: vec![u.clone()],
            type_: irreducible_type,
        })?;

        // Irreducible.ne_zero : ∀ {α} [IntegralDomain α] {p}, Irreducible p → Ne p 0
        let irr_ne_zero_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let inst_ty = Expr::app(
                Expr::const_(Name::from_string("IntegralDomain"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, inst) = b.fresh_local(inst_ty.clone());
            let (p_id, p) = b.fresh_local(alpha.clone());
            let irreducible_p = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Irreducible"), vec![u_level.clone()]),
                        alpha.clone(),
                    ),
                    inst.clone(),
                ),
                p.clone(),
            );
            let zero = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("IntegralDomain.zero"),
                        vec![u_level.clone()],
                    ),
                    alpha.clone(),
                ),
                inst,
            );
            let ne_p_zero = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Ne"), vec![Level::succ(u_level.clone())]),
                        alpha.clone(),
                    ),
                    p,
                ),
                zero,
            );
            let (h_id, _) = b.fresh_local(irreducible_p.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, irreducible_p, ne_p_zero);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, alpha.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Irreducible.ne_zero"),
            level_params: vec![u.clone()],
            type_: irr_ne_zero_type,
        })?;

        // Irreducible.not_unit : ∀ {α} [IntegralDomain α] {p}, Irreducible p → ¬IsUnit p
        // IsUnit is defined as: ∃ u, u * a = 1
        // For now we add a simpler property

        // Irreducible.isUnit_or_isUnit : ∀ {α} [IntegralDomain α] {p a b},
        //   Irreducible p → Eq p (mul a b) → Or (IsUnit a) (IsUnit b)
        // This is the key property, but requires IsUnit definition

        // For Nat specifically, we can state:
        // Nat.Irreducible : Nat → Prop (prime numbers are irreducible in Nat)
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);

        // Nat.Irreducible is essentially Nat.Prime for naturals (in a UFD, irreducible = prime)
        let nat_irr_type = Expr::pi(BinderInfo::Default, nat_type.clone(), prop.clone());

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.Irreducible"),
            level_params: vec![],
            type_: nat_irr_type,
        })?;

        // Nat.Prime.irreducible : ∀ {p}, Nat.Prime p → Nat.Irreducible p
        let prime_impl_irr_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nat_type.clone());
            let prime_p = Expr::app(
                Expr::const_(Name::from_string("Nat.Prime"), vec![]),
                p.clone(),
            );
            let irr_p = Expr::app(
                Expr::const_(Name::from_string("Nat.Irreducible"), vec![]),
                p,
            );
            let (h_id, _) = b.fresh_local(prime_p.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, prime_p, irr_p);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, nat_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.Prime.irreducible"),
            level_params: vec![],
            type_: prime_impl_irr_type,
        })?;

        // Nat.Irreducible.prime : ∀ {p}, Nat.Irreducible p → Nat.Prime p
        let irr_impl_prime_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nat_type.clone());
            let irr_p = Expr::app(
                Expr::const_(Name::from_string("Nat.Irreducible"), vec![]),
                p.clone(),
            );
            let prime_p = Expr::app(Expr::const_(Name::from_string("Nat.Prime"), vec![]), p);
            let (h_id, _) = b.fresh_local(irr_p.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, irr_p, prime_p);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, nat_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.Irreducible.prime"),
            level_params: vec![],
            type_: irr_impl_prime_type,
        })?;

        self.irreducible_init = true;
        Ok(())
    }

    /// Check if Irreducible has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.irreducible_init == true`
    #[cfg(test)]
    pub(crate) fn has_irreducible(&self) -> bool {
        self.irreducible_init
    }
}
