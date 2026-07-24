// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Commutative ring instances and IntegralDomain
//!
//! This module contains:
//! - Nat/Int CommSemiring instances
//! - Int CommRing instance
//! - Nat/Int IntegralDomain instances

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Nat CommSemiring instance
    ///
    /// Nat forms a CommSemiring with all Semiring fields plus Nat.mul_comm
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_comm_semiring_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_comm_semiring_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_comm_semiring_inst_init {
            return Ok(());
        }

        self.init_comm_semiring()?;
        self.init_nat()?;
        self.init_nat_arith_lemmas()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ, nat_zero.clone());

        // Instance type: CommSemiring Nat
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("CommSemiring"), vec![Level::zero()]),
            nat_const.clone(),
        );

        // Instance value: CommSemiring.mk with 16 args
        let inst_value = Expr::app(
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
                                                                            Expr::const_(
                                                                                Name::from_string(
                                                                                    "CommSemiring.mk",
                                                                                ),
                                                                                // Nat : Type 0, so universe param is 0
                                                                                vec![Level::zero()],
                                                                            ),
                                                                            nat_const.clone(),
                                                                        ),
                                                                        nat_add,
                                                                    ),
                                                                    Expr::const_(
                                                                        Name::from_string(
                                                                            "Nat.add_assoc",
                                                                        ),
                                                                        vec![],
                                                                    ),
                                                                ),
                                                                nat_zero,
                                                            ),
                                                            Expr::const_(
                                                                Name::from_string("Nat.zero_add"),
                                                                vec![],
                                                            ),
                                                        ),
                                                        Expr::const_(
                                                            Name::from_string("Nat.add_zero"),
                                                            vec![],
                                                        ),
                                                    ),
                                                    Expr::const_(
                                                        Name::from_string("Nat.add_comm"),
                                                        vec![],
                                                    ),
                                                ),
                                                nat_mul,
                                            ),
                                            Expr::const_(
                                                Name::from_string("Nat.mul_assoc"),
                                                vec![],
                                            ),
                                        ),
                                        nat_one,
                                    ),
                                    Expr::const_(Name::from_string("Nat.one_mul"), vec![]),
                                ),
                                Expr::const_(Name::from_string("Nat.mul_one"), vec![]),
                            ),
                            Expr::const_(Name::from_string("Nat.zero_mul"), vec![]),
                        ),
                        Expr::const_(Name::from_string("Nat.mul_zero"), vec![]),
                    ),
                    Expr::const_(Name::from_string("Nat.left_distrib"), vec![]),
                ),
                Expr::const_(Name::from_string("Nat.right_distrib"), vec![]),
            ),
            Expr::const_(Name::from_string("Nat.mul_comm"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instCommSemiringNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_comm_semiring_inst_init = true;
        Ok(())
    }

    /// Check if Nat CommSemiring instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_comm_semiring_inst_init == true`
    pub(crate) fn has_nat_comm_semiring_inst(&self) -> bool {
        self.nat_comm_semiring_inst_init
    }

    /// Initialize the Int CommSemiring instance
    ///
    /// Int forms a CommSemiring with all Semiring fields plus Int.mul_comm
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_comm_semiring_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_comm_semiring_inst(&mut self) -> Result<(), EnvError> {
        if self.int_comm_semiring_inst_init {
            return Ok(());
        }

        self.init_comm_semiring()?;
        self.init_int_arith()?;
        self.init_int_arith_lemmas()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
        let int_one = Expr::app(int_of_nat, Expr::app(nat_succ, nat_zero));

        // Instance type: CommSemiring Int
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("CommSemiring"), vec![Level::zero()]),
            int_const.clone(),
        );

        // Instance value: CommSemiring.mk with 16 args
        let inst_value = Expr::app(
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
                                                                            Expr::const_(
                                                                                Name::from_string(
                                                                                    "CommSemiring.mk",
                                                                                ),
                                                                                // Int : Type 0, so universe param is 0
                                                                                vec![Level::zero()],
                                                                            ),
                                                                            int_const.clone(),
                                                                        ),
                                                                        int_add,
                                                                    ),
                                                                    Expr::const_(
                                                                        Name::from_string(
                                                                            "Int.add_assoc",
                                                                        ),
                                                                        vec![],
                                                                    ),
                                                                ),
                                                                int_zero,
                                                            ),
                                                            Expr::const_(
                                                                Name::from_string("Int.zero_add"),
                                                                vec![],
                                                            ),
                                                        ),
                                                        Expr::const_(
                                                            Name::from_string("Int.add_zero"),
                                                            vec![],
                                                        ),
                                                    ),
                                                    Expr::const_(
                                                        Name::from_string("Int.add_comm"),
                                                        vec![],
                                                    ),
                                                ),
                                                int_mul,
                                            ),
                                            Expr::const_(
                                                Name::from_string("Int.mul_assoc"),
                                                vec![],
                                            ),
                                        ),
                                        int_one,
                                    ),
                                    Expr::const_(Name::from_string("Int.one_mul"), vec![]),
                                ),
                                Expr::const_(Name::from_string("Int.mul_one"), vec![]),
                            ),
                            Expr::const_(Name::from_string("Int.zero_mul"), vec![]),
                        ),
                        Expr::const_(Name::from_string("Int.mul_zero"), vec![]),
                    ),
                    Expr::const_(Name::from_string("Int.left_distrib"), vec![]),
                ),
                Expr::const_(Name::from_string("Int.right_distrib"), vec![]),
            ),
            Expr::const_(Name::from_string("Int.mul_comm"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instCommSemiringInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_comm_semiring_inst_init = true;
        Ok(())
    }

    /// Check if Int CommSemiring instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_comm_semiring_inst_init == true`
    pub(crate) fn has_int_comm_semiring_inst(&self) -> bool {
        self.int_comm_semiring_inst_init
    }

    /// Initialize the Int CommRing instance
    ///
    /// Int forms a CommRing with all Ring fields plus Int.mul_comm
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_comm_ring_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_comm_ring_inst(&mut self) -> Result<(), EnvError> {
        if self.int_comm_ring_inst_init {
            return Ok(());
        }

        self.init_comm_ring()?;
        self.init_int_arith()?;
        self.init_int_arith_lemmas()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let int_neg = Expr::const_(Name::from_string("Int.neg"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
        let int_one = Expr::app(int_of_nat, Expr::app(nat_succ, nat_zero));

        // Instance type: CommRing Int
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("CommRing"), vec![Level::zero()]),
            int_const.clone(),
        );

        // Instance value: CommRing.mk with 18 args
        let inst_value = Expr::app(
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
                                                                                Expr::app(
                                                                                    Expr::const_(
                                                                                        Name::from_string("CommRing.mk"),
                                                                                        vec![Level::zero()],
                                                                                    ),
                                                                                    int_const.clone(),
                                                                                ),
                                                                                int_add,
                                                                            ),
                                                                            Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
                                                                        ),
                                                                        int_zero,
                                                                    ),
                                                                    Expr::const_(Name::from_string("Int.zero_add"), vec![]),
                                                                ),
                                                                Expr::const_(Name::from_string("Int.add_zero"), vec![]),
                                                            ),
                                                            Expr::const_(Name::from_string("Int.add_comm"), vec![]),
                                                        ),
                                                        int_mul,
                                                    ),
                                                    Expr::const_(Name::from_string("Int.mul_assoc"), vec![]),
                                                ),
                                                int_one,
                                            ),
                                            Expr::const_(Name::from_string("Int.one_mul"), vec![]),
                                        ),
                                        Expr::const_(Name::from_string("Int.mul_one"), vec![]),
                                    ),
                                    Expr::const_(Name::from_string("Int.zero_mul"), vec![]),
                                ),
                                Expr::const_(Name::from_string("Int.mul_zero"), vec![]),
                            ),
                            Expr::const_(Name::from_string("Int.left_distrib"), vec![]),
                        ),
                        Expr::const_(Name::from_string("Int.right_distrib"), vec![]),
                    ),
                    int_neg,
                ),
                Expr::const_(Name::from_string("Int.neg_add_self"), vec![]),
            ),
            Expr::const_(Name::from_string("Int.mul_comm"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instCommRingInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_comm_ring_inst_init = true;
        Ok(())
    }

    /// Check if Int CommRing instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_comm_ring_inst_init == true`
    pub(crate) fn has_int_comm_ring_inst(&self) -> bool {
        self.int_comm_ring_inst_init
    }

    /// Initialize Int as an IntegralDomain
    ///
    /// Int is an integral domain since if a * b = 0 then a = 0 or b = 0.
    /// This creates instIntegralDomainInt : IntegralDomain Int
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_integral_domain_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_integral_domain_inst(&mut self) -> Result<(), EnvError> {
        if self.int_integral_domain_inst_init {
            return Ok(());
        }

        // Dependencies: IntegralDomain typeclass and Int type
        self.init_integral_domain()?;
        self.init_int()?;
        self.init_int_arith()?;
        self.init_int_arith_lemmas()?;
        self.init_classical()?; // Or is defined in init_classical (#1488)

        let int_type = Expr::const_(Name::from_string("Int"), vec![]);
        let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
        let int_one = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let one_val = Expr::app(int_one.clone(), Expr::nat_lit(1));
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let int_neg = Expr::const_(Name::from_string("Int.neg"), vec![]);

        // Instance type: IntegralDomain Int
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("IntegralDomain"), vec![Level::zero()]),
            int_type.clone(),
        );

        // For the no_zero_divisors property, we need a proof axiom
        // no_zero_divisors : ∀ a b : Int, a * b = 0 → (a = 0) ∨ (b = 0)
        let no_zero_divisors_proof_type = {
            // Int : Type 0 = Sort(1), so Eq needs universe 1 (#1488).
            let eq_int = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_type.clone());
            let (b_id, bv) = b.fresh_local(int_type.clone());

            let mul_a_b = Expr::app(Expr::app(int_mul.clone(), a.clone()), bv.clone());
            let premise = Expr::app(
                Expr::app(Expr::app(eq_int.clone(), int_type.clone()), mul_a_b),
                int_zero.clone(),
            );
            let (premise_id, _) = b.fresh_local(premise.clone());

            let eq_a_zero = Expr::app(
                Expr::app(Expr::app(eq_int.clone(), int_type.clone()), a),
                int_zero.clone(),
            );
            let eq_b_zero = Expr::app(
                Expr::app(Expr::app(eq_int, int_type.clone()), bv),
                int_zero.clone(),
            );
            let conclusion = Expr::app(
                Expr::app(Expr::const_(Name::from_string("Or"), vec![]), eq_a_zero),
                eq_b_zero,
            );

            let r = b.mk_pi(premise_id, BinderInfo::Default, premise, conclusion);
            let r = b.mk_pi(b_id, BinderInfo::Default, int_type.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, int_type.clone(), r);
            b.finish(r)
        };

        // Add axiom for Int.no_zero_divisors
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.no_zero_divisors"),
            level_params: vec![],
            type_: no_zero_divisors_proof_type.clone(),
        })?;

        // Now build the IntegralDomain.mk application with all 19 fields
        // IntegralDomain.mk {α} add add_assoc zero zero_add add_zero add_comm
        //                   mul mul_assoc one one_mul mul_one zero_mul mul_zero
        //                   left_distrib right_distrib neg add_left_neg mul_comm no_zero_divisors

        let inst_value = {
            let mk = Expr::const_(Name::from_string("IntegralDomain.mk"), vec![Level::zero()]);

            // Get proof constants that we assume exist from Int arithmetic lemmas
            let int_add_assoc = Expr::const_(Name::from_string("Int.add_assoc"), vec![]);
            let int_zero_add = Expr::const_(Name::from_string("Int.zero_add"), vec![]);
            let int_add_zero = Expr::const_(Name::from_string("Int.add_zero"), vec![]);
            let int_add_comm = Expr::const_(Name::from_string("Int.add_comm"), vec![]);
            let int_mul_assoc = Expr::const_(Name::from_string("Int.mul_assoc"), vec![]);
            let int_one_mul = Expr::const_(Name::from_string("Int.one_mul"), vec![]);
            let int_mul_one = Expr::const_(Name::from_string("Int.mul_one"), vec![]);
            let int_zero_mul = Expr::const_(Name::from_string("Int.zero_mul"), vec![]);
            let int_mul_zero = Expr::const_(Name::from_string("Int.mul_zero"), vec![]);
            let int_left_distrib = Expr::const_(Name::from_string("Int.left_distrib"), vec![]);
            let int_right_distrib = Expr::const_(Name::from_string("Int.right_distrib"), vec![]);
            let int_add_left_neg = Expr::const_(Name::from_string("Int.neg_add_self"), vec![]);
            let int_mul_comm = Expr::const_(Name::from_string("Int.mul_comm"), vec![]);
            let int_no_zero_div = Expr::const_(Name::from_string("Int.no_zero_divisors"), vec![]);

            // Apply mk to Int type and all proofs
            let e = Expr::app(mk, int_type.clone());
            let e = Expr::app(e, int_add);
            let e = Expr::app(e, int_add_assoc);
            let e = Expr::app(e, int_zero.clone());
            let e = Expr::app(e, int_zero_add);
            let e = Expr::app(e, int_add_zero);
            let e = Expr::app(e, int_add_comm);
            let e = Expr::app(e, int_mul);
            let e = Expr::app(e, int_mul_assoc);
            let e = Expr::app(e, one_val);
            let e = Expr::app(e, int_one_mul);
            let e = Expr::app(e, int_mul_one);
            let e = Expr::app(e, int_zero_mul);
            let e = Expr::app(e, int_mul_zero);
            let e = Expr::app(e, int_left_distrib);
            let e = Expr::app(e, int_right_distrib);
            let e = Expr::app(e, int_neg);
            let e = Expr::app(e, int_add_left_neg);
            let e = Expr::app(e, int_mul_comm);
            Expr::app(e, int_no_zero_div)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instIntegralDomainInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_integral_domain_inst_init = true;
        Ok(())
    }

    /// Check if Int IntegralDomain instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_integral_domain_inst_init == true`
    pub(crate) fn has_int_integral_domain_inst(&self) -> bool {
        self.int_integral_domain_inst_init
    }

    /// Initialize Nat as an IntegralDomain
    ///
    /// Nat is axiomatized as an IntegralDomain for use in UniqueFactorizationMonoid.
    /// Mathematically Nat lacks negation, but Lean 4 Mathlib uses this instance
    /// for the UFM hierarchy. We declare it as an axiom.
    ///
    /// Creates Nat.instIntegralDomain : IntegralDomain Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_integral_domain_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_integral_domain_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_integral_domain_inst_init {
            return Ok(());
        }

        // Dependencies: IntegralDomain typeclass and Nat type
        self.init_integral_domain()?;
        self.init_nat()?;

        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);

        // Instance type: IntegralDomain Nat
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("IntegralDomain"), vec![Level::zero()]),
            nat_type,
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.instIntegralDomain"),
            level_params: vec![],
            type_: inst_type,
        })?;

        self.nat_integral_domain_inst_init = true;
        Ok(())
    }

    /// Check if Nat IntegralDomain instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_integral_domain_inst_init == true`
    pub(crate) fn has_nat_integral_domain_inst(&self) -> bool {
        self.nat_integral_domain_inst_init
    }
}
