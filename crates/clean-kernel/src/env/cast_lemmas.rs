// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cast-normalization simp lemmas for proof-carrying cast tactics (#2516).
//!
//! This module provides the theorem inventory that `push_cast`, `norm_cast`,
//! `zify`, and `qify` need to produce real `Eq` proofs instead of trusting
//! `trustedArith`.
//!
//! Declarations:
//! - `Rat.ofInt` coercion (Int → Rat)
//! - Proposition-transfer lemmas (Nat→Int, Int→Rat)
//! - Arithmetic cast-movement lemmas (Rat.ofInt_add, Rat.ofInt_mul)

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize cast-normalization simp lemmas for proof-carrying cast tactics.
    ///
    /// Adds:
    /// - `Rat.ofInt : Int → Rat` (coercion, defined as `λ n => Rat.mk n 1`)
    /// - `Nat.cast_eq_prop` : proposition transfer for Eq across Nat→Int
    /// - `Nat.cast_le_prop` : proposition transfer for ≤ across Nat→Int
    /// - `Nat.cast_lt_prop` : proposition transfer for < across Nat→Int
    /// - `Int.cast_eq_prop` : proposition transfer for Eq across Int→Rat
    /// - `Int.cast_le_prop` : proposition transfer for ≤ across Int→Rat
    /// - `Int.cast_lt_prop` : proposition transfer for < across Int→Rat
    /// - `Rat.ofInt_add` : cast distributes over addition
    /// - `Rat.ofInt_mul` : cast distributes over multiplication
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.cast_simp_lemmas_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_cast_simp_lemmas(&mut self) -> Result<(), EnvError> {
        if self.cast_simp_lemmas_init {
            return Ok(());
        }

        // Dependencies: Rat arithmetic + Int/Nat ordering + Int/Nat conv lemmas
        self.init_rat_arith()?;
        self.init_int_nat_conv_lemmas()?;
        self.init_int_ord()?; // Int.le, Int.lt
        self.init_le()?; // LE typeclass + Nat.le
        self.init_lt()?; // LT typeclass + Nat.lt
        self.init_rat_ord()?; // Rat.le, Rat.lt
        self.init_eq()?;

        self.add_rat_of_int()?;
        self.add_nat_proposition_transfer_lemmas()?;
        self.add_int_proposition_transfer_lemmas()?;
        self.add_rat_of_int_arith_lemmas()?;

        self.cast_simp_lemmas_init = true;
        Ok(())
    }

    /// Add `Rat.ofInt : Int → Rat` defined as `λ n : Int => Rat.mk n 1`.
    fn add_rat_of_int(&mut self) -> Result<(), EnvError> {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let nat_one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );

        let rat_of_int_type = Expr::pi(BinderInfo::Default, int_const.clone(), rat_const);

        // λ n : Int => Rat.mk n 1
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(int_const.clone());
        let body = Expr::app(Expr::app(rat_mk, n), nat_one);
        let value = {
            let e = b.mk_lam(n_id, BinderInfo::Default, int_const, body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.ofInt"),
            level_params: vec![],
            type_: rat_of_int_type,
            value,
            is_reducible: true,
        })
    }

    /// Add Nat→Int proposition-transfer lemmas as axioms.
    ///
    /// These are `Eq Prop` lemmas (not `Iff`) because clean's simp engine
    /// currently consumes `Eq`, not arbitrary `Iff`.
    fn add_nat_proposition_transfer_lemmas(&mut self) -> Result<(), EnvError> {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let prop = Expr::prop();
        let eq_prop = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        let mut b = EnvDeclBuilder::new();

        let mk_prop_eq = |lhs: Expr, rhs: Expr| {
            Expr::app(
                Expr::app(Expr::app(eq_prop.clone(), prop.clone()), lhs),
                rhs,
            )
        };

        // Nat.cast_eq_prop : ∀ a b : Nat,
        //   Eq Prop (Eq Nat a b) (Eq Int (Int.ofNat a) (Int.ofNat b))
        {
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());

            let eq_nat = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let eq_int = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let lhs = Expr::app(
                Expr::app(Expr::app(eq_nat, nat_const.clone()), a.clone()),
                bv.clone(),
            );
            let rhs = Expr::app(
                Expr::app(
                    Expr::app(eq_int, int_const.clone()),
                    Expr::app(int_of_nat.clone(), a),
                ),
                Expr::app(int_of_nat.clone(), bv),
            );
            let body = mk_prop_eq(lhs, rhs);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            let type_ = b.finish(e);

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.cast_eq_prop"),
                level_params: vec![],
                type_,
            })?;
        }

        // Nat.cast_le_prop : ∀ a b : Nat,
        //   Eq Prop (Nat.le a b) (Int.le (Int.ofNat a) (Int.ofNat b))
        {
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());
            let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
            let int_le = Expr::const_(Name::from_string("Int.le"), vec![]);
            let lhs = Expr::app(Expr::app(nat_le, a.clone()), bv.clone());
            let rhs = Expr::app(
                Expr::app(int_le, Expr::app(int_of_nat.clone(), a)),
                Expr::app(int_of_nat.clone(), bv),
            );
            let body = mk_prop_eq(lhs, rhs);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            let type_ = b.finish(e);

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.cast_le_prop"),
                level_params: vec![],
                type_,
            })?;
        }

        // Nat.cast_lt_prop : ∀ a b : Nat,
        //   Eq Prop (Nat.lt a b) (Int.lt (Int.ofNat a) (Int.ofNat b))
        {
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (b_id, bv) = b.fresh_local(nat_const.clone());
            let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
            let int_lt = Expr::const_(Name::from_string("Int.lt"), vec![]);
            let lhs = Expr::app(Expr::app(nat_lt, a.clone()), bv.clone());
            let rhs = Expr::app(
                Expr::app(int_lt, Expr::app(int_of_nat.clone(), a)),
                Expr::app(int_of_nat.clone(), bv),
            );
            let body = mk_prop_eq(lhs, rhs);
            let e = b.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            let type_ = b.finish(e);

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Nat.cast_lt_prop"),
                level_params: vec![],
                type_,
            })?;
        }

        Ok(())
    }

    /// Add Int→Rat proposition-transfer lemmas as axioms.
    fn add_int_proposition_transfer_lemmas(&mut self) -> Result<(), EnvError> {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_of_int = Expr::const_(Name::from_string("Rat.ofInt"), vec![]);
        let prop = Expr::prop();
        let eq_prop = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        let mut b = EnvDeclBuilder::new();

        let mk_prop_eq = |lhs: Expr, rhs: Expr| {
            Expr::app(
                Expr::app(Expr::app(eq_prop.clone(), prop.clone()), lhs),
                rhs,
            )
        };

        // Int.cast_eq_prop : ∀ a b : Int,
        //   Eq Prop (Eq Int a b) (Eq Rat (Rat.ofInt a) (Rat.ofInt b))
        {
            let (a_id, a) = b.fresh_local(int_const.clone());
            let (b_id, bv) = b.fresh_local(int_const.clone());
            let eq_int = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let eq_rat = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
            let lhs = Expr::app(
                Expr::app(Expr::app(eq_int, int_const.clone()), a.clone()),
                bv.clone(),
            );
            let rhs = Expr::app(
                Expr::app(
                    Expr::app(eq_rat, rat_const.clone()),
                    Expr::app(rat_of_int.clone(), a),
                ),
                Expr::app(rat_of_int.clone(), bv),
            );
            let body = mk_prop_eq(lhs, rhs);
            let e = b.mk_pi(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            let type_ = b.finish(e);

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.cast_eq_prop"),
                level_params: vec![],
                type_,
            })?;
        }

        // Int.cast_le_prop : ∀ a b : Int,
        //   Eq Prop (Int.le a b) (Rat.le (Rat.ofInt a) (Rat.ofInt b))
        {
            let (a_id, a) = b.fresh_local(int_const.clone());
            let (b_id, bv) = b.fresh_local(int_const.clone());
            let int_le = Expr::const_(Name::from_string("Int.le"), vec![]);
            let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
            let lhs = Expr::app(Expr::app(int_le, a.clone()), bv.clone());
            let rhs = Expr::app(
                Expr::app(rat_le, Expr::app(rat_of_int.clone(), a)),
                Expr::app(rat_of_int.clone(), bv),
            );
            let body = mk_prop_eq(lhs, rhs);
            let e = b.mk_pi(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            let type_ = b.finish(e);

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.cast_le_prop"),
                level_params: vec![],
                type_,
            })?;
        }

        // Int.cast_lt_prop : ∀ a b : Int,
        //   Eq Prop (Int.lt a b) (Rat.lt (Rat.ofInt a) (Rat.ofInt b))
        {
            let (a_id, a) = b.fresh_local(int_const.clone());
            let (b_id, bv) = b.fresh_local(int_const.clone());
            let int_lt = Expr::const_(Name::from_string("Int.lt"), vec![]);
            let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
            let lhs = Expr::app(Expr::app(int_lt, a.clone()), bv.clone());
            let rhs = Expr::app(
                Expr::app(rat_lt, Expr::app(rat_of_int.clone(), a)),
                Expr::app(rat_of_int.clone(), bv),
            );
            let body = mk_prop_eq(lhs, rhs);
            let e = b.mk_pi(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            let type_ = b.finish(e);

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.cast_lt_prop"),
                level_params: vec![],
                type_,
            })?;
        }

        Ok(())
    }

    /// Add Rat.ofInt arithmetic cast-movement lemmas.
    ///
    /// - `Rat.ofInt_add : ∀ m n : Int, Eq Rat (Rat.ofInt (Int.add m n)) (Rat.add (Rat.ofInt m) (Rat.ofInt n))`
    /// - `Rat.ofInt_mul : ∀ m n : Int, Eq Rat (Rat.ofInt (Int.mul m n)) (Rat.mul (Rat.ofInt m) (Rat.ofInt n))`
    fn add_rat_of_int_arith_lemmas(&mut self) -> Result<(), EnvError> {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_of_int = Expr::const_(Name::from_string("Rat.ofInt"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let eq_rat = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        let mut b = EnvDeclBuilder::new();

        let mk_rat_eq = |lhs: Expr, rhs: Expr| {
            Expr::app(
                Expr::app(Expr::app(eq_rat.clone(), rat_const.clone()), lhs),
                rhs,
            )
        };

        // Rat.ofInt_add
        {
            let (m_id, m) = b.fresh_local(int_const.clone());
            let (n_id, n) = b.fresh_local(int_const.clone());
            let lhs = Expr::app(
                rat_of_int.clone(),
                Expr::app(Expr::app(int_add, m.clone()), n.clone()),
            );
            let rhs = Expr::app(
                Expr::app(rat_add, Expr::app(rat_of_int.clone(), m)),
                Expr::app(rat_of_int.clone(), n),
            );
            let body = mk_rat_eq(lhs, rhs);
            let e = b.mk_pi(n_id, BinderInfo::Default, int_const.clone(), body);
            let e = b.mk_pi(m_id, BinderInfo::Default, int_const.clone(), e);
            let type_ = b.finish(e);

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.ofInt_add"),
                level_params: vec![],
                type_,
            })?;
        }

        // Rat.ofInt_mul
        {
            let (m_id, m) = b.fresh_local(int_const.clone());
            let (n_id, n) = b.fresh_local(int_const.clone());
            let lhs = Expr::app(
                rat_of_int.clone(),
                Expr::app(Expr::app(int_mul, m.clone()), n.clone()),
            );
            let rhs = Expr::app(
                Expr::app(rat_mul, Expr::app(rat_of_int.clone(), m)),
                Expr::app(rat_of_int.clone(), n),
            );
            let body = mk_rat_eq(lhs, rhs);
            let e = b.mk_pi(n_id, BinderInfo::Default, int_const.clone(), body);
            let e = b.mk_pi(m_id, BinderInfo::Default, int_const.clone(), e);
            let type_ = b.finish(e);

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Rat.ofInt_mul"),
                level_params: vec![],
                type_,
            })?;
        }

        Ok(())
    }
}
