// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int EuclideanDomain instance initialization for Environment
//!
//! Constructs the Int instance of EuclideanDomain using Int.div, Int.mod,
//! and the euclideanLt well-founded relation on Int.natAbs.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Int EuclideanDomain instance
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_euclidean_domain_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_int_euclidean_domain_inst(&mut self) -> Result<(), EnvError> {
        if self.int_euclidean_domain_inst_init {
            return Ok(());
        }

        // Dependencies
        self.init_euclidean_domain()?;
        self.init_int()?;
        self.init_int_arith()?;
        self.init_int_arith_lemmas()?;
        self.init_int_nontrivial_inst()?;
        self.init_lt()?; // Nat.lt for Int.euclideanLt

        let int_type = Expr::const_(Name::from_string("Int"), vec![]);
        let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
        let int_one = Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(1),
        );
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let int_neg = Expr::const_(Name::from_string("Int.neg"), vec![]);

        // Instance type: EuclideanDomain Int
        // EuclideanDomain.{u} : Type u → Type u.  Int : Type 0, so u = 0.
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("EuclideanDomain"), vec![Level::zero()]),
            int_type.clone(),
        );

        // Int.div / Int.mod : Int → Int → Int.
        //
        // `add_decl_if_absent` (not `add_decl`): `init_int_arith` now registers
        // these as `Opaque` data declarations (native-reduced T-division), so in
        // any env that already ran `init_int_arith` they are present. Reuse the
        // existing declaration rather than failing with `DuplicateName`. The
        // Euclidean-domain `div_zero` / `div_add_mod` axioms below state
        // *properties* of `Int.div` / `Int.mod` and hold regardless of whether
        // the operations are `Opaque` or `Axiom`-shaped. (Track PP)
        let int_binop_ty = Expr::pi(
            BinderInfo::Default,
            int_type.clone(),
            Expr::pi(BinderInfo::Default, int_type.clone(), int_type.clone()),
        );
        self.add_decl_if_absent(Declaration::Axiom {
            name: Name::from_string("Int.div"),
            level_params: vec![],
            type_: int_binop_ty.clone(),
        })?;
        self.add_decl_if_absent(Declaration::Axiom {
            name: Name::from_string("Int.mod"),
            level_params: vec![],
            type_: int_binop_ty,
        })?;

        // Add div_zero axiom: ∀ a, div a 0 = 0
        let eq_int_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let div_zero_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_type.clone());
            let div_a_0 = Expr::app(
                Expr::app(Expr::const_(Name::from_string("Int.div"), vec![]), a),
                int_zero.clone(),
            );
            let eq = Expr::app(
                Expr::app(Expr::app(eq_int_const.clone(), int_type.clone()), div_a_0),
                int_zero.clone(),
            );
            let r = b.mk_pi(a_id, BinderInfo::Default, int_type.clone(), eq);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.div_zero"),
            level_params: vec![],
            type_: div_zero_type,
        })?;

        // Add div_add_mod axiom: ∀ a b, b * div a b + mod a b = a
        let div_mod_eq_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_type.clone());
            let (bv_id, bv) = b.fresh_local(int_type.clone());
            let div_a_b = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Int.div"), vec![]),
                    a.clone(),
                ),
                bv.clone(),
            );
            let mod_a_b = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Int.mod"), vec![]),
                    a.clone(),
                ),
                bv.clone(),
            );
            let b_mul_div = Expr::app(Expr::app(int_mul.clone(), bv), div_a_b);
            let lhs = Expr::app(Expr::app(int_add.clone(), b_mul_div), mod_a_b);
            let eq = Expr::app(
                Expr::app(Expr::app(eq_int_const.clone(), int_type.clone()), lhs),
                a,
            );
            let r = b.mk_pi(bv_id, BinderInfo::Default, int_type.clone(), eq);
            let r = b.mk_pi(a_id, BinderInfo::Default, int_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.div_add_mod"),
            level_params: vec![],
            type_: div_mod_eq_type,
        })?;

        // Add Int.natAbs for the well-founded relation
        // Int.natAbs : Int → Nat
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.natAbs"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                int_type.clone(),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
        })?;

        // The well-founded relation r on Int is: r a b ↔ natAbs a < natAbs b
        // We define this as a definition Int.euclideanLt
        let euclidean_lt_type = Expr::pi(
            BinderInfo::Default,
            int_type.clone(),
            Expr::pi(
                BinderInfo::Default,
                int_type.clone(),
                Expr::from_kind(ExprKind::Sort(Level::zero())), // Prop
            ),
        );

        // euclideanLt a b := Nat.lt (natAbs a) (natAbs b)
        let euclidean_lt_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(int_type.clone());
            let (bv_id, bv) = b.fresh_local(int_type.clone());
            let abs_a = Expr::app(Expr::const_(Name::from_string("Int.natAbs"), vec![]), a);
            let abs_b = Expr::app(Expr::const_(Name::from_string("Int.natAbs"), vec![]), bv);
            let body = Expr::app(
                Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), abs_a),
                abs_b,
            );
            let r = b.mk_lam(bv_id, BinderInfo::Default, int_type.clone(), body);
            let r = b.mk_lam(a_id, BinderInfo::Default, int_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Int.euclideanLt"),
            level_params: vec![],
            type_: euclidean_lt_type.clone(),
            value: euclidean_lt_value,
            is_reducible: true,
        })?;

        // Axiom: WellFounded Int.euclideanLt
        let wf_euclidean_lt_type = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("WellFounded"),
                    vec![Level::succ(Level::zero())],
                ),
                int_type.clone(),
            ),
            Expr::const_(Name::from_string("Int.euclideanLt"), vec![]),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.euclideanLt_wf"),
            level_params: vec![],
            type_: wf_euclidean_lt_type,
        })?;

        // Axiom: remainder_lt for Int
        // ∀ a {b}, b ≠ 0 → euclideanLt (mod a b) b
        let remainder_lt_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(int_type.clone());
            let (bv_id, bv) = bl.fresh_local(int_type.clone());
            let b_ne_zero = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
                        int_type.clone(),
                    ),
                    bv.clone(),
                ),
                int_zero.clone(),
            );
            let (ne_id, _) = bl.fresh_local(b_ne_zero.clone());
            let mod_a_b = Expr::app(
                Expr::app(Expr::const_(Name::from_string("Int.mod"), vec![]), a),
                bv.clone(),
            );
            let r_mod_b = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Int.euclideanLt"), vec![]),
                    mod_a_b,
                ),
                bv,
            );
            let r = bl.mk_pi(ne_id, BinderInfo::Default, b_ne_zero, r_mod_b);
            let r = bl.mk_pi(bv_id, BinderInfo::Implicit, int_type.clone(), r);
            let r = bl.mk_pi(a_id, BinderInfo::Default, int_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.mod_lt"),
            level_params: vec![],
            type_: remainder_lt_type,
        })?;

        // Axiom: mul_left_not_lt for Int
        // ∀ a {b}, b ≠ 0 → ¬euclideanLt (a * b) a
        let mul_not_lt_type = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(int_type.clone());
            let (bv_id, bv) = bl.fresh_local(int_type.clone());
            let b_ne_zero = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
                        int_type.clone(),
                    ),
                    bv.clone(),
                ),
                int_zero.clone(),
            );
            let (ne_id, _) = bl.fresh_local(b_ne_zero.clone());
            let a_mul_b = Expr::app(Expr::app(int_mul.clone(), a.clone()), bv);
            let r_prod_a = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Int.euclideanLt"), vec![]),
                    a_mul_b,
                ),
                a,
            );
            let not_r = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), r_prod_a);
            let r = bl.mk_pi(ne_id, BinderInfo::Default, b_ne_zero, not_r);
            let r = bl.mk_pi(bv_id, BinderInfo::Implicit, int_type.clone(), r);
            let r = bl.mk_pi(a_id, BinderInfo::Default, int_type.clone(), r);
            bl.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.mul_not_lt"),
            level_params: vec![],
            type_: mul_not_lt_type,
        })?;

        // Now build the EuclideanDomain.mk instance
        // EuclideanDomain.mk {Int} add add_assoc zero ... quotient quotient_zero ...
        let inst_value = {
            // EuclideanDomain.mk.{u} — u = 0 for Int
            let mk = Expr::const_(Name::from_string("EuclideanDomain.mk"), vec![Level::zero()]);

            // Get all the proof constants
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

            // Nontrivial proof - we extract it from the instance
            // Nontrivial.exists_pair_ne.{u} — u = 0 for Int : Type 0
            let nontrivial_proof = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Nontrivial.exists_pair_ne"),
                        vec![Level::zero()],
                    ),
                    int_type.clone(),
                ),
                Expr::const_(Name::from_string("instNontrivialInt"), vec![]),
            );

            let int_div = Expr::const_(Name::from_string("Int.div"), vec![]);
            let int_div_zero = Expr::const_(Name::from_string("Int.div_zero"), vec![]);
            let int_mod = Expr::const_(Name::from_string("Int.mod"), vec![]);
            let int_div_add_mod = Expr::const_(Name::from_string("Int.div_add_mod"), vec![]);
            let int_euclidean_lt = Expr::const_(Name::from_string("Int.euclideanLt"), vec![]);
            let int_euclidean_lt_wf = Expr::const_(Name::from_string("Int.euclideanLt_wf"), vec![]);
            let int_mod_lt = Expr::const_(Name::from_string("Int.mod_lt"), vec![]);
            let int_mul_not_lt = Expr::const_(Name::from_string("Int.mul_not_lt"), vec![]);

            // Apply mk to all fields
            let e = Expr::app(mk, int_type.clone());
            let e = Expr::app(e, int_add);
            let e = Expr::app(e, int_add_assoc);
            let e = Expr::app(e, int_zero.clone());
            let e = Expr::app(e, int_zero_add);
            let e = Expr::app(e, int_add_zero);
            let e = Expr::app(e, int_add_comm);
            let e = Expr::app(e, int_mul);
            let e = Expr::app(e, int_mul_assoc);
            let e = Expr::app(e, int_one);
            let e = Expr::app(e, int_one_mul);
            let e = Expr::app(e, int_mul_one);
            let e = Expr::app(e, int_zero_mul);
            let e = Expr::app(e, int_mul_zero);
            let e = Expr::app(e, int_left_distrib);
            let e = Expr::app(e, int_right_distrib);
            let e = Expr::app(e, int_neg);
            let e = Expr::app(e, int_add_left_neg);
            let e = Expr::app(e, int_mul_comm);
            let e = Expr::app(e, nontrivial_proof);
            let e = Expr::app(e, int_div);
            let e = Expr::app(e, int_div_zero);
            let e = Expr::app(e, int_mod);
            let e = Expr::app(e, int_div_add_mod);
            let e = Expr::app(e, int_euclidean_lt);
            let e = Expr::app(e, int_euclidean_lt_wf);
            let e = Expr::app(e, int_mod_lt);
            Expr::app(e, int_mul_not_lt)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instEuclideanDomainInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_euclidean_domain_inst_init = true;
        Ok(())
    }

    /// Check if Int EuclideanDomain instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_euclidean_domain_inst_init == true`
    #[cfg(test)]
    pub(crate) fn has_int_euclidean_domain_inst(&self) -> bool {
        self.int_euclidean_domain_inst_init
    }
}
