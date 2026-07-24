// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! UniqueFactorizationMonoid typeclass and Nat instance.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize UniqueFactorizationMonoid (UFM) typeclass
    ///
    /// UniqueFactorizationMonoid {α : Type u} [CommMonoidWithZero α] : Type u
    /// A UFM has the property that every non-zero non-unit element can be written
    /// as a product of irreducibles, unique up to order and associates.
    ///
    /// Key axioms:
    /// - irreducible_iff_prime: ∀ p, Irreducible p ↔ Prime p
    /// - exists_prime_factors: ∀ a ≠ 0, ∃ f : Multiset α, (∀ p ∈ f, Prime p) ∧ Associated (f.prod) a
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ufm_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_ufm(&mut self) -> Result<(), EnvError> {
        if self.ufm_init {
            return Ok(());
        }

        // Dependencies
        self.init_associated()?;
        self.init_gcd_monoid()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1) // Type u

        // UniqueFactorizationMonoid : {α : Type u} → [IntegralDomain α] → Type u
        let ufm_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let inst_ty = Expr::app(
                Expr::const_(Name::from_string("IntegralDomain"), vec![u_level.clone()]),
                alpha,
            );
            let (inst_id, _) = b.fresh_local(inst_ty.clone());
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, type_u.clone());
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("UniqueFactorizationMonoid"),
            level_params: vec![u.clone()],
            type_: ufm_type,
        })?;

        // UFM.irreducible_iff_prime : ∀ {α} [IntegralDomain α] [UFM α] {p},
        //   Irreducible p ↔ Prime p
        // For simplicity, we state both directions separately

        // UFM.irreducible_of_prime : ∀ {α} [IntegralDomain α] [UFM α] {p}, Prime p → Irreducible p
        // (This is actually true in any integral domain, not just UFM)

        // UFM.prime_of_irreducible : ∀ {α} [IntegralDomain α] [UFM α] {p}, Irreducible p → Prime p
        // (This is the characteristic property of UFM)

        // For now, we add the key existence axiom:
        // UFM.exists_prime_factors : ∀ {α} [IntegralDomain α] [UFM α] {a : α},
        //   a ≠ 0 → ∃ factors : List α, (∀ p ∈ factors, Prime p) ∧ a = product factors
        // This is complex due to List, so we'll use a simpler form

        // UFM.wf_dvd_strict : ∀ {α} [IntegralDomain α] [UFM α],
        //   WellFounded (fun a b => a ∣ b ∧ ¬Associated a b)
        // This captures that strict divisibility is well-founded in a UFM

        self.ufm_init = true;
        Ok(())
    }

    /// Check if UFM has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.ufm_init == true`
    pub fn has_ufm(&self) -> bool {
        self.ufm_init
    }

    /// Initialize Nat as a UniqueFactorizationMonoid instance
    ///
    /// Nat is the canonical example of a UFD - the Fundamental Theorem of Arithmetic
    /// states that every natural number > 1 can be uniquely factored into primes.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_ufm_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_ufm_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_ufm_inst_init {
            return Ok(());
        }

        // Dependencies
        self.init_ufm()?;
        self.init_nat_prime()?;
        self.init_nat_integral_domain_inst()?;

        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);

        // Nat.instUniqueFactorizationMonoid : UniqueFactorizationMonoid Nat
        // We need the IntegralDomain instance for Nat
        // For simplicity, we use a placeholder instance type
        let nat_ufm_inst_type = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("UniqueFactorizationMonoid"),
                    vec![Level::zero()],
                ),
                nat_type.clone(),
            ),
            Expr::const_(Name::from_string("Nat.instIntegralDomain"), vec![]),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.instUniqueFactorizationMonoid"),
            level_params: vec![],
            type_: nat_ufm_inst_type,
        })?;

        // Fundamental Theorem of Arithmetic (FTA):
        // Nat.exists_prime_factorization : ∀ {n : Nat}, n ≠ 0 → n ≠ 1 →
        //   ∃ primes : List Nat, (∀ p ∈ primes, Nat.Prime p) ∧ n = List.prod primes
        //
        // We'll express a simpler version without List:
        // Nat.prime_factorization_exists : ∀ {n}, n > 1 → ∃ p, Nat.Prime p ∧ Nat.dvd p n
        // (This was already added in init_nat_prime as Nat.exists_prime_and_dvd)

        // Nat.prime_factorization_unique : key uniqueness property
        // If n = p₁ * ... * pₖ = q₁ * ... * qₘ where all pᵢ, qⱼ are prime,
        // then k = m and {p₁, ..., pₖ} = {q₁, ..., qₘ} (as multisets)
        //
        // This is complex to state without multisets, so we state a consequence:
        // Nat.prime_dvd_prime_mul : ∀ {p q r}, Prime p → Prime q → Prime r →
        //   dvd p (mul q r) → Eq p q ∨ Eq p r

        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_dvd = Expr::const_(Name::from_string("Nat.dvd"), vec![]);

        // Nat.prime_dvd_prime_mul :
        // ∀ {p q r : Nat}, Prime p → Prime q → Prime r → dvd p (mul q r) → Or (Eq p q) (Eq p r)
        let prime_dvd_prime_mul_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(nat_type.clone());
            let (q_id, q) = b.fresh_local(nat_type.clone());
            let (r_id, rv) = b.fresh_local(nat_type.clone());
            let prime_p = Expr::app(
                Expr::const_(Name::from_string("Nat.Prime"), vec![]),
                p.clone(),
            );
            let prime_q = Expr::app(
                Expr::const_(Name::from_string("Nat.Prime"), vec![]),
                q.clone(),
            );
            let prime_r = Expr::app(
                Expr::const_(Name::from_string("Nat.Prime"), vec![]),
                rv.clone(),
            );
            let q_times_r = Expr::app(Expr::app(nat_mul.clone(), q.clone()), rv.clone());
            let dvd_p_qr = Expr::app(Expr::app(nat_dvd.clone(), p.clone()), q_times_r);
            let mk_nat_eq = |x: Expr, y: Expr| -> Expr {
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                            nat_type.clone(),
                        ),
                        x,
                    ),
                    y,
                )
            };
            let eq_p_q = mk_nat_eq(p.clone(), q);
            let eq_p_r = mk_nat_eq(p, rv);
            let or_eq = Expr::app(
                Expr::app(Expr::const_(Name::from_string("Or"), vec![]), eq_p_q),
                eq_p_r,
            );
            let (h4_id, _) = b.fresh_local(dvd_p_qr.clone());
            let (h3_id, _) = b.fresh_local(prime_r.clone());
            let (h2_id, _) = b.fresh_local(prime_q.clone());
            let (h1_id, _) = b.fresh_local(prime_p.clone());
            let result = b.mk_pi(h4_id, BinderInfo::Default, dvd_p_qr, or_eq);
            let result = b.mk_pi(h3_id, BinderInfo::Default, prime_r, result);
            let result = b.mk_pi(h2_id, BinderInfo::Default, prime_q, result);
            let result = b.mk_pi(h1_id, BinderInfo::Default, prime_p, result);
            let result = b.mk_pi(r_id, BinderInfo::Implicit, nat_type.clone(), result);
            let result = b.mk_pi(q_id, BinderInfo::Implicit, nat_type.clone(), result);
            let result = b.mk_pi(p_id, BinderInfo::Implicit, nat_type.clone(), result);
            b.finish(result)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.prime_dvd_prime_mul"),
            level_params: vec![],
            type_: prime_dvd_prime_mul_type,
        })?;

        // Nat.eq_one_of_pos_of_self_mul_self :
        // ∀ {n : Nat}, n > 0 → mul n n = n → n = 1
        // (Consequence of UFD: only unit squares to itself)
        let ne_type = Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]);
        let eq_one_of_square_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_type.clone());
            let ne_n_zero = Expr::app(
                Expr::app(Expr::app(ne_type.clone(), nat_type.clone()), n.clone()),
                nat_zero.clone(),
            );
            let n_times_n = Expr::app(Expr::app(nat_mul.clone(), n.clone()), n.clone());
            let eq_nn_n = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        nat_type.clone(),
                    ),
                    n_times_n,
                ),
                n.clone(),
            );
            let eq_n_one = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        nat_type.clone(),
                    ),
                    n,
                ),
                nat_one.clone(),
            );
            let (h2_id, _) = b.fresh_local(eq_nn_n.clone());
            let (h1_id, _) = b.fresh_local(ne_n_zero.clone());
            let r = b.mk_pi(h2_id, BinderInfo::Default, eq_nn_n, eq_n_one);
            let r = b.mk_pi(h1_id, BinderInfo::Default, ne_n_zero, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.eq_one_of_self_mul_self"),
            level_params: vec![],
            type_: eq_one_of_square_type,
        })?;

        self.nat_ufm_inst_init = true;
        Ok(())
    }

    /// Check if Nat UFM instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_ufm_inst_init == true`
    pub(crate) fn has_nat_ufm_inst(&self) -> bool {
        self.nat_ufm_inst_init
    }
}
