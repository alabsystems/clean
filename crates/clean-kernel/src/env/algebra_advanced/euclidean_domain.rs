// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! EuclideanDomain typeclass initialization for Environment
//!
//! EuclideanDomain extends CommRing and Nontrivial with quotient, remainder,
//! and a well-founded relation (27 total fields).

use crate::env::algebra_ring_fields::RingBaseFields;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize EuclideanDomain typeclass
    /// class EuclideanDomain (R : Type u) extends CommRing R, Nontrivial R where
    ///   quotient : R → R → R
    ///   quotient_zero : ∀ a, quotient a 0 = 0
    ///   remainder : R → R → R
    ///   quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a
    ///   r : R → R → Prop
    ///   r_wellFounded : WellFounded r
    ///   remainder_lt : ∀ a {b}, b ≠ 0 → r (remainder a b) b
    ///   mul_left_not_lt : ∀ a {b}, b ≠ 0 → ¬r (a * b) a
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.euclidean_domain_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_euclidean_domain(&mut self) -> Result<(), EnvError> {
        if self.euclidean_domain_init {
            return Ok(());
        }

        // Dependencies
        self.init_comm_ring()?;
        self.init_nontrivial()?;
        self.init_well_founded()?;
        self.init_true_false()?; // For Not and Ne

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1) // Type u

        // EuclideanDomain extends CommRing (18 fields) and Nontrivial (1 field) = 19 base fields
        // Plus 8 new fields = 27 fields total
        //
        // Fields from CommRing (18):
        // 0: add : α → α → α
        // 1: add_assoc
        // 2: zero : α
        // 3: zero_add
        // 4: add_zero
        // 5: add_comm
        // 6: mul : α → α → α
        // 7: mul_assoc
        // 8: one : α
        // 9: one_mul
        // 10: mul_one
        // 11: zero_mul
        // 12: mul_zero
        // 13: left_distrib
        // 14: right_distrib
        // 15: neg : α → α
        // 16: add_left_neg
        // 17: mul_comm
        //
        // Field from Nontrivial (1):
        // 18: exists_pair_ne
        //
        // New EuclideanDomain fields (8):
        // 19: quotient : α → α → α
        // 20: quotient_zero : ∀ a, quotient a 0 = 0
        // 21: remainder : α → α → α
        // 22: quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a
        // 23: r : α → α → Prop
        // 24: r_wellFounded : WellFounded r
        // 25: remainder_lt : ∀ a {b}, b ≠ 0 → r (remainder a b) b
        // 26: mul_left_not_lt : ∀ a {b}, b ≠ 0 → ¬r (a * b) a

        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let class_name = Name::from_string("EuclideanDomain");
        let class_const = Expr::const_(class_name.clone(), vec![u_level.clone()]);
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Build EuclideanDomain constructor type with EnvDeclBuilder
        // 27 fields: 17 Ring base + mul_comm + 1 Nontrivial + 8 new
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let ring = RingBaseFields::build(&mut b, &type_u, &eq_const);

            // Field 17: mul_comm
            let mul_comm_type = ring.build_mul_comm_type(&b, &eq_const);
            let (mul_comm_id, _) = b.fresh_local(mul_comm_type.clone());

            // Alias ring fields for use in EuclideanDomain-specific fields below
            let alpha = ring.alpha.clone();
            let add = ring.add.clone();
            let zero = ring.zero.clone();
            let mul = ring.mul.clone();

            // Field 18: exists_pair_ne : ∃ x y : α, x ≠ y (from Nontrivial)
            let exists_pair_ne_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                // outer lambda: fun (x : α) =>
                let (x_id, x) = s.fresh_local(alpha.clone());
                // inner: Exists α (fun (y : α) => Ne α x y)
                let mut s2 = EnvDeclBuilder::child_of(&s);
                let (y_id, y) = s2.fresh_local(alpha.clone());
                let ne_x_y = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Ne"),
                                vec![Level::succ(u_level.clone())],
                            ),
                            alpha.clone(),
                        ),
                        x.clone(),
                    ),
                    y,
                );
                let inner_pred = s2.mk_lam(y_id, BinderInfo::Default, alpha.clone(), ne_x_y);
                let inner_pred = s2.finish_child(inner_pred);
                let inner_exists = Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Exists"),
                            vec![Level::succ(u_level.clone())],
                        ),
                        alpha.clone(),
                    ),
                    inner_pred,
                );
                let outer_pred = s.mk_lam(x_id, BinderInfo::Default, alpha.clone(), inner_exists);
                let outer_pred = s.finish_child(outer_pred);
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Exists"),
                            vec![Level::succ(u_level.clone())],
                        ),
                        alpha.clone(),
                    ),
                    outer_pred,
                )
            };
            let (exists_pair_ne_id, _) = b.fresh_local(exists_pair_ne_type.clone());

            // Field 19: quotient : α → α → α
            let quotient_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = s.fresh_local(alpha.clone());
                let (y_id, _) = s.fresh_local(alpha.clone());
                let r = alpha.clone();
                let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (quotient_id, quotient) = b.fresh_local(quotient_type.clone());

            // Field 20: quotient_zero : ∀ a, quotient a 0 = 0
            let quotient_zero_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let lhs = Expr::app(Expr::app(quotient.clone(), a), zero.clone());
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    zero.clone(),
                );
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), eq);
                s.finish_child(r)
            };
            let (quotient_zero_id, _) = b.fresh_local(quotient_zero_type.clone());

            // Field 21: remainder : α → α → α
            let remainder_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = s.fresh_local(alpha.clone());
                let (y_id, _) = s.fresh_local(alpha.clone());
                let r = alpha.clone();
                let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (remainder_id, remainder) = b.fresh_local(remainder_type.clone());

            // Field 22: quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a
            let div_mod_eq_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let quot_a_b = Expr::app(Expr::app(quotient.clone(), a.clone()), bv.clone());
                let b_mul_quot = Expr::app(Expr::app(mul.clone(), bv.clone()), quot_a_b);
                let rem_a_b = Expr::app(Expr::app(remainder.clone(), a.clone()), bv);
                let lhs = Expr::app(Expr::app(add.clone(), b_mul_quot), rem_a_b);
                let eq = Expr::app(
                    Expr::app(Expr::app(eq_const.clone(), alpha.clone()), lhs),
                    a,
                );
                let r = s.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), eq);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (div_mod_eq_id, _) = b.fresh_local(div_mod_eq_type.clone());

            // Field 23: r : α → α → Prop
            let r_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = s.fresh_local(alpha.clone());
                let (y_id, _) = s.fresh_local(alpha.clone());
                let r = prop.clone();
                let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
                let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (r_id, r_var) = b.fresh_local(r_type.clone());

            // Field 24: r_wellFounded : WellFounded r
            // WellFounded.{u} takes {α : Sort u}, but EuclideanDomain.{u} has {α : Type u}.
            // Type u = Sort (u+1), so WellFounded needs universe u+1 here.
            let r_wf_type = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("WellFounded"),
                        vec![Level::succ(u_level.clone())],
                    ),
                    alpha.clone(),
                ),
                r_var.clone(),
            );
            let (r_wf_id, _) = b.fresh_local(r_wf_type.clone());

            // Field 25: remainder_lt : ∀ a {b}, b ≠ 0 → r (remainder a b) b
            let remainder_lt_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let b_ne_zero = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Ne"),
                                vec![Level::succ(u_level.clone())],
                            ),
                            alpha.clone(),
                        ),
                        bv.clone(),
                    ),
                    zero.clone(),
                );
                let rem_a_b = Expr::app(Expr::app(remainder.clone(), a), bv.clone());
                let r_rem_b = Expr::app(Expr::app(r_var.clone(), rem_a_b), bv);
                let r = Expr::pi(BinderInfo::Default, b_ne_zero, r_rem_b);
                let r = s.mk_pi(bv_id, BinderInfo::Implicit, alpha.clone(), r);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (remainder_lt_id, _) = b.fresh_local(remainder_lt_type.clone());

            // Field 26: mul_left_not_lt : ∀ a {b}, b ≠ 0 → ¬r (a * b) a
            let mul_left_not_lt_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let (bv_id, bv) = s.fresh_local(alpha.clone());
                let b_ne_zero = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Ne"),
                                vec![Level::succ(u_level.clone())],
                            ),
                            alpha.clone(),
                        ),
                        bv.clone(),
                    ),
                    zero.clone(),
                );
                let a_mul_b = Expr::app(Expr::app(mul.clone(), a.clone()), bv);
                let r_prod_a = Expr::app(Expr::app(r_var.clone(), a_mul_b), a);
                let not_r = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), r_prod_a);
                let r = Expr::pi(BinderInfo::Default, b_ne_zero, not_r);
                let r = s.mk_pi(bv_id, BinderInfo::Implicit, alpha.clone(), r);
                let r = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                s.finish_child(r)
            };
            let (mul_left_not_lt_id, _) = b.fresh_local(mul_left_not_lt_type.clone());

            // Result: EuclideanDomain α
            let result = Expr::app(class_const.clone(), alpha.clone());
            let r = b.mk_pi(
                mul_left_not_lt_id,
                BinderInfo::Default,
                mul_left_not_lt_type,
                result,
            );
            let r = b.mk_pi(remainder_lt_id, BinderInfo::Default, remainder_lt_type, r);
            let r = b.mk_pi(r_wf_id, BinderInfo::Default, r_wf_type, r);
            let r = b.mk_pi(r_id, BinderInfo::Default, r_type, r);
            let r = b.mk_pi(div_mod_eq_id, BinderInfo::Default, div_mod_eq_type, r);
            let r = b.mk_pi(remainder_id, BinderInfo::Default, remainder_type, r);
            let r = b.mk_pi(quotient_zero_id, BinderInfo::Default, quotient_zero_type, r);
            let r = b.mk_pi(quotient_id, BinderInfo::Default, quotient_type, r);
            let r = b.mk_pi(
                exists_pair_ne_id,
                BinderInfo::Default,
                exists_pair_ne_type,
                r,
            );
            let r = b.mk_pi(mul_comm_id, BinderInfo::Default, mul_comm_type, r);
            let r = ring.fold_pi(&b, &type_u, r);
            b.finish(r)
        };

        // Build the EuclideanDomain inductive type with 27 fields
        let ind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let r = type_u.clone();
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let euclidean_domain_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("EuclideanDomain"),
                type_: ind_type,
                constructors: vec![Constructor {
                    name: Name::from_string("EuclideanDomain.mk"),
                    type_: ctor_type,
                }],
            }],
        };

        self.add_inductive(euclidean_domain_ind)?;

        // Register structure fields for Expr::proj support
        let mut field_names = RingBaseFields::field_names();
        field_names.push(Name::from_string("mul_comm")); // 17
        field_names.push(Name::from_string("exists_pair_ne")); // 18
        field_names.push(Name::from_string("quotient")); // 19
        field_names.push(Name::from_string("quotient_zero")); // 20
        field_names.push(Name::from_string("remainder")); // 21
        field_names.push(Name::from_string("quotient_mul_add_remainder_eq")); // 22
        field_names.push(Name::from_string("r")); // 23
        field_names.push(Name::from_string("r_wellFounded")); // 24
        field_names.push(Name::from_string("remainder_lt")); // 25
        field_names.push(Name::from_string("mul_left_not_lt")); // 26
        self.register_structure_fields(Name::from_string("EuclideanDomain"), field_names)?;

        // Add key projections using Expr::proj
        // quotient projection (field 19)
        let quotient_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let (x_id, _) = b.fresh_local(alpha.clone());
            let (y_id, _) = b.fresh_local(alpha.clone());
            let r = alpha.clone();
            let r = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(class_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let quotient_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let body = Expr::proj(class_name.clone(), 19, inst);
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(class_const.clone(), alpha.clone()),
                body,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("EuclideanDomain.quotient"),
            level_params: vec![u.clone()],
            type_: quotient_proj_type,
            value: quotient_proj_value,
            is_reducible: true,
        })?;

        // remainder projection (field 21)
        let remainder_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let (x_id, _) = b.fresh_local(alpha.clone());
            let (y_id, _) = b.fresh_local(alpha.clone());
            let r = alpha.clone();
            let r = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(class_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let remainder_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(class_const.clone(), alpha.clone()));
            let body = Expr::proj(class_name.clone(), 21, inst);
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(class_const.clone(), alpha.clone()),
                body,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("EuclideanDomain.remainder"),
            level_params: vec![u.clone()],
            type_: remainder_proj_type,
            value: remainder_proj_value,
            is_reducible: true,
        })?;

        self.euclidean_domain_init = true;
        Ok(())
    }

    /// Check if EuclideanDomain typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.euclidean_domain_init == true`
    #[cfg(test)]
    pub(crate) fn has_euclidean_domain(&self) -> bool {
        self.euclidean_domain_init
    }
}
