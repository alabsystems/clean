// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nontrivial typeclass and Int instance initialization for Environment
//!
//! Nontrivial states there exist two distinct elements in a type.
//! The Int instance proves Int is nontrivial via 0 ≠ 1.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Nontrivial typeclass
    /// Nontrivial is a predicate stating there exist two distinct elements
    /// class Nontrivial (α : Type*) : Prop where
    ///   exists_pair_ne : ∃ x y : α, x ≠ y
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nontrivial_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_nontrivial(&mut self) -> Result<(), EnvError> {
        if self.nontrivial_init {
            return Ok(());
        }

        // Dependencies: Exists (for ∃) and Ne (for ≠)
        self.init_exists()?;
        self.init_true_false()?; // Ne is defined here

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1) // Type u

        let ne_const = Expr::const_(Name::from_string("Ne"), vec![Level::succ(u_level.clone())]);
        let exists_const = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(u_level.clone())],
        );
        let nontrivial_name = Name::from_string("Nontrivial");
        let nontrivial_const = Expr::const_(nontrivial_name.clone(), vec![u_level.clone()]);

        // exists_pair_ne : ∃ x y : α, x ≠ y
        // = Exists α (fun x => Exists α (fun y => Ne α x y))
        // Build as a child of the ctor builder so α is available as a named FVar
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());

            // Build ∃ x y : α, x ≠ y using child builders for the lambda predicates
            let exists_pair_ne_type = {
                // inner_pred = fun y : α => Ne α x y (needs x from outer scope)
                // outer_pred = fun x : α => Exists α inner_pred
                // result = Exists α outer_pred
                let mut outer = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = outer.fresh_local(alpha.clone());
                let inner_pred = {
                    let mut inner = EnvDeclBuilder::child_of(&outer);
                    let (y_id, y) = inner.fresh_local(alpha.clone());
                    let ne_x_y = Expr::app(
                        Expr::app(Expr::app(ne_const.clone(), alpha.clone()), x.clone()),
                        y,
                    );
                    let r = inner.mk_lam(y_id, BinderInfo::Default, alpha.clone(), ne_x_y);
                    inner.finish_child(r)
                };
                let inner_exists =
                    Expr::app(Expr::app(exists_const.clone(), alpha.clone()), inner_pred);
                let outer_pred_body = inner_exists;
                let outer_pred =
                    outer.mk_lam(x_id, BinderInfo::Default, alpha.clone(), outer_pred_body);
                Expr::app(
                    Expr::app(exists_const.clone(), alpha.clone()),
                    outer.finish_child(outer_pred),
                )
            };
            let (epn_id, _) = b.fresh_local(exists_pair_ne_type.clone());

            // Result: Nontrivial α
            let result = Expr::app(nontrivial_const.clone(), alpha.clone());
            let r = b.mk_pi(epn_id, BinderInfo::Default, exists_pair_ne_type, result);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // Inductive type: Nontrivial : Type u → Prop
        let ind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let r = Expr::from_kind(ExprKind::Sort(Level::zero()));
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let nontrivial_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: nontrivial_name.clone(),
                type_: ind_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Nontrivial.mk"),
                    type_: ctor_type,
                }],
            }],
        };

        self.add_inductive(nontrivial_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            nontrivial_name.clone(),
            vec![Name::from_string("exists_pair_ne")], // 0
        )?;

        // Nontrivial.exists_pair_ne: {α : Type u} → [inst : Nontrivial α] → ∃ x y : α, x ≠ y
        let proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _) = b.fresh_local(Expr::app(nontrivial_const.clone(), alpha.clone()));
            // Rebuild exists_pair_ne_type in this scope
            let epn = {
                let mut outer = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = outer.fresh_local(alpha.clone());
                let inner_pred = {
                    let mut inner = EnvDeclBuilder::child_of(&outer);
                    let (y_id, y) = inner.fresh_local(alpha.clone());
                    let ne_x_y = Expr::app(
                        Expr::app(Expr::app(ne_const.clone(), alpha.clone()), x.clone()),
                        y,
                    );
                    let r = inner.mk_lam(y_id, BinderInfo::Default, alpha.clone(), ne_x_y);
                    inner.finish_child(r)
                };
                let inner_exists =
                    Expr::app(Expr::app(exists_const.clone(), alpha.clone()), inner_pred);
                let outer_pred =
                    outer.mk_lam(x_id, BinderInfo::Default, alpha.clone(), inner_exists);
                Expr::app(
                    Expr::app(exists_const.clone(), alpha.clone()),
                    outer.finish_child(outer_pred),
                )
            };
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(nontrivial_const.clone(), alpha.clone()),
                epn,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(Expr::app(nontrivial_const.clone(), alpha.clone()));
            let body = Expr::proj(nontrivial_name.clone(), 0, inst);
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(nontrivial_const.clone(), alpha.clone()),
                body,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nontrivial.exists_pair_ne"),
            level_params: vec![u.clone()],
            type_: proj_type,
            value: proj_value,
            is_reducible: true,
        })?;

        self.nontrivial_init = true;
        Ok(())
    }

    /// Check if Nontrivial typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nontrivial_init == true`
    #[cfg(test)]
    pub(crate) fn has_nontrivial(&self) -> bool {
        self.nontrivial_init
    }

    /// Initialize Int Nontrivial instance
    /// Proves that Int is nontrivial (0 ≠ 1)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_nontrivial_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_nontrivial_inst(&mut self) -> Result<(), EnvError> {
        if self.int_nontrivial_inst_init {
            return Ok(());
        }

        self.init_nontrivial()?;
        self.init_int()?;

        let int_type = Expr::const_(Name::from_string("Int"), vec![]);
        let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
        let int_one = Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(1),
        );

        // Instance type: Nontrivial Int
        // Nontrivial.{u} : Type u → Prop. Int : Type 0, so u = 0.
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Nontrivial"), vec![Level::zero()]),
            int_type.clone(),
        );

        // We need to provide: ∃ x y : Int, x ≠ y
        // Proof: Exists.intro 0 (Exists.intro 1 (proof that 0 ≠ 1))
        // We use an axiom for Int.zero_ne_one
        let zero_ne_one_type = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
                    int_type.clone(),
                ),
                int_zero.clone(),
            ),
            int_one.clone(),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Int.zero_ne_one"),
            level_params: vec![],
            type_: zero_ne_one_type.clone(),
        })?;

        // Build the exists proof
        // ∃ x : Int, ∃ y : Int, x ≠ y
        // = Exists.intro Int 0 (Exists.intro Int 1 Int.zero_ne_one)
        let ne_int_const = Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]);
        let exists_int_const = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(Level::zero())],
        );
        let exists_intro_const = Expr::const_(
            Name::from_string("Exists.intro"),
            vec![Level::succ(Level::zero())],
        );

        // Inner predicate: fun y : Int => Ne Int 0 y
        let inner_pred = {
            let mut b = EnvDeclBuilder::new();
            let (y_id, y) = b.fresh_local(int_type.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(ne_int_const.clone(), int_type.clone()),
                    int_zero.clone(),
                ),
                y,
            );
            let r = b.mk_lam(y_id, BinderInfo::Default, int_type.clone(), body);
            b.finish(r)
        };

        let inner_exists_proof = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(exists_intro_const.clone(), int_type.clone()),
                    inner_pred.clone(),
                ),
                int_one.clone(),
            ),
            Expr::const_(Name::from_string("Int.zero_ne_one"), vec![]),
        );

        // Outer predicate: fun x : Int => Exists Int (fun y => Ne Int x y)
        let outer_pred = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(int_type.clone());
            let inner_lam = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = s.fresh_local(int_type.clone());
                let body = Expr::app(
                    Expr::app(Expr::app(ne_int_const.clone(), int_type.clone()), x),
                    y,
                );
                let r = s.mk_lam(y_id, BinderInfo::Default, int_type.clone(), body);
                s.finish_child(r)
            };
            let body = Expr::app(
                Expr::app(exists_int_const.clone(), int_type.clone()),
                inner_lam,
            );
            let r = b.mk_lam(x_id, BinderInfo::Default, int_type.clone(), body);
            b.finish(r)
        };

        let exists_proof = Expr::app(
            Expr::app(
                Expr::app(Expr::app(exists_intro_const, int_type.clone()), outer_pred),
                int_zero.clone(),
            ),
            inner_exists_proof,
        );

        // Instance value: Nontrivial.mk exists_proof
        // Int : Type 0 = Sort 1.  Nontrivial.mk.{u} takes {α : Type u},
        // so u = 0 for Int.
        let inst_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nontrivial.mk"), vec![Level::zero()]),
                int_type.clone(),
            ),
            exists_proof,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instNontrivialInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_nontrivial_inst_init = true;
        Ok(())
    }

    /// Check if Int Nontrivial instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_nontrivial_inst_init == true`
    #[cfg(test)]
    pub(crate) fn has_int_nontrivial_inst(&self) -> bool {
        self.int_nontrivial_inst_init
    }
}
