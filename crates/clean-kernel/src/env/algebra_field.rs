// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rational number field instances for Environment
//!
//! Contains LinearOrder, LinearOrderedField instances for Rat:
//! - init_rat_linear_order: Preorder, PartialOrder, LinearOrder
//! - init_linear_ordered_field: LinearOrderedField typeclass
//! - init_rat_ordered_field_axioms: Ordered field axioms
//! - init_rat_linear_ordered_field_inst: Final LinearOrderedField Rat instance
//!
//! The Rat Field instance (init_rat_field_inst) is in `algebra_field_inst.rs`.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Constructor, InductiveDecl, InductiveType};
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
#[cfg(test)]
use crate::expr::{BinderInfo, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize LinearOrder instance for Rat
    ///
    /// This adds:
    /// - Rat.le_refl, Rat.le_trans, Rat.le_antisymm, Rat.lt_irrefl (axioms)
    /// - Rat.lt_iff_le_not_le (axiom)
    /// - instPreorderRat : Preorder Rat
    /// - instPartialOrderRat : PartialOrder Rat
    /// - Rat.le_total : axiom ∀ a b : Rat, Or (Rat.le a b) (Rat.le b a)
    /// - instLinearOrderRat : LinearOrder Rat
    ///
    /// Requires: init_rat_ord() for Rat.le, Rat.lt, instLERat, instLTRat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_linear_order_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_rat_linear_order(&mut self) -> Result<(), EnvError> {
        if self.rat_linear_order_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_rat_ord()?; // Provides Rat.le, Rat.lt, instLERat, instLTRat
        self.init_preorder()?; // Provides Preorder typeclass
        self.init_partial_order()?; // Provides PartialOrder typeclass
        self.init_linear_order()?; // Provides LinearOrder typeclass
        self.init_iff()?; // Provides Iff (used by Rat.lt_iff_le_not_le)
        self.init_and()?; // Provides And (used by lt_iff_le_not_le body)
        self.init_true_false()?; // Provides Not (used by le_not_le)

        // #3470 Lane #2/#3: register the genuinely-provable Rat ordering lemmas
        // (Rat.le_refl, Rat.le_total, Rat.zero_lt_one, Rat.lt_iff_le_not_le) as
        // kernel-checked `Declaration::Theorem`s BEFORE the instances below
        // consume them. Each registration is idempotent and skips a name that
        // is already present, so the remaining still-admitted lemmas below
        // (Rat.le_trans, Rat.le_antisymm) keep their `Declaration::Axiom` form.
        self.register_rat_order_proofs()?;

        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let _le_const = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let _eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        // Note: Rat.le_refl / Rat.le_total / Rat.lt_iff_le_not_le are now
        // kernel-checked Theorems (see `register_rat_order_proofs`), so the
        // `Rat.lt` / `Not` / `Or` / `Iff` / `And` constants they referenced are
        // no longer needed in this initializer.

        // ========================================
        // Rat.le_refl : ∀ a : Rat, Rat.le a a
        //
        // #3470 Lane #2/#3: now a kernel-checked `Declaration::Theorem`
        // (`λ a => @Int.le_refl (cross a a)`), registered above by
        // `register_rat_order_proofs`. No longer a `Declaration::Axiom`.
        // ========================================

        // ========================================
        // Rat.le_trans : ∀ a b c : Rat, Rat.le a b → Rat.le b c → Rat.le a c
        //
        // SOUNDNESS FIX: this was previously a `Declaration::Axiom` that is
        // PROVABLY FALSE under the free-inductive `Rat.mk : Int -> Nat` carrier
        // (no `denom > 0` invariant) — e.g. `mk 5 1 ≤ mk 0 0 ≤ mk (-5) 1` both
        // hold under naive cross-multiplication, yet `mk 5 1 ≤ mk (-5) 1` is
        // false. `Rat.le` / `Rat.lt` are now defined over the EFFECTIVE
        // denominator `Rat.effDenom` (never 0; definitionally `denom` for
        // well-formed Rats), making the order a genuine preorder. `Rat.le_trans`
        // is registered here as a GENUINE kernel-checked `Declaration::Theorem`
        // (see `algebra_rat_le_trans_proof.rs`), reducing to the constructive Int
        // cross-multiplication transitivity `Int.le_cross_trans`. No fabrication:
        // the kernel rejects the proof term unless it inhabits the stated type.
        // ========================================
        self.register_rat_le_trans_proof()?;

        // ========================================
        // Rat.le_antisymm : ∀ a b : Rat, Rat.le a b → Rat.le b a → Eq a b
        //
        // WS-A ATOMIC LIVE SWITCH (step 3, payoff): over the QUOTIENT carrier
        // this is a GENUINE kernel-checked `Declaration::Theorem` (it was FALSE
        // over the free carrier, where `mk 1 1` / `mk 2 2` are `≤` both ways yet
        // structurally distinct; the quotient identifies them via `Quot.sound`).
        // Registered (with the SAME name + type) by the payoff helper.
        // ========================================
        self.rat_quotient_payoff_into_live()?;

        // ========================================
        // Rat.lt_iff_le_not_le : ∀ a b : Rat, Iff (Rat.lt a b) (And (Rat.le a b) (Not (Rat.le b a)))
        //
        // #3470 Lane #2/#3: now a kernel-checked `Declaration::Theorem`
        // (`λ a b => @Int.lt_iff_le_not_le (cross a b) (cross b a)`), registered
        // above by `register_rat_order_proofs`. Honest classification:
        // `AxiomDependent { Int.lt_iff_le_not_le }` (the residual trust is the
        // single more-primitive Int axiom), NOT a fresh Rat axiom.
        // ========================================

        // ========================================
        // instPreorderRat : Preorder Rat
        // Preorder.mk @Rat instLERat instLTRat Rat.le_refl Rat.le_trans
        //
        // Previously an Axiom (#1628, #1526) because projection reduction
        // could not reduce LE.le @Rat instLERat to Rat.le. That limitation
        // is now fixed (#3222), so this is a proper Definition.
        // ========================================
        let inst_preorder_rat_type = Expr::app(
            Expr::const_(Name::from_string("Preorder"), vec![Level::zero()]),
            rat_const.clone(),
        );

        let inst_preorder_rat_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Preorder.mk"), vec![Level::zero()]),
                            rat_const.clone(),
                        ),
                        Expr::const_(Name::from_string("instLERat"), vec![]),
                    ),
                    Expr::const_(Name::from_string("instLTRat"), vec![]),
                ),
                Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
            ),
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instPreorderRat"),
            level_params: vec![],
            type_: inst_preorder_rat_type,
            value: inst_preorder_rat_value,
            is_reducible: true,
        })?;

        // ========================================
        // instPartialOrderRat : PartialOrder Rat
        // PartialOrder.mk @Rat instPreorderRat Rat.le_antisymm
        //
        // Previously an Axiom (#1628, #1526). Now a proper Definition (#3222).
        // ========================================
        let inst_partial_order_rat_type = Expr::app(
            Expr::const_(Name::from_string("PartialOrder"), vec![Level::zero()]),
            rat_const.clone(),
        );

        let inst_partial_order_rat_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("PartialOrder.mk"), vec![Level::zero()]),
                    rat_const.clone(),
                ),
                Expr::const_(Name::from_string("instPreorderRat"), vec![]),
            ),
            Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instPartialOrderRat"),
            level_params: vec![],
            type_: inst_partial_order_rat_type,
            value: inst_partial_order_rat_value,
            is_reducible: true,
        })?;

        // ========================================
        // Rat.le_total : ∀ a b : Rat, Or (Rat.le a b) (Rat.le b a)
        //
        // #3470 Lane #2/#3: now a kernel-checked `Declaration::Theorem`
        // (`λ a b => @Int.le_total (cross a b) (cross b a)`), registered above
        // by `register_rat_order_proofs`. `Int.le_total` is itself a
        // constructive theorem, so `Rat.le_total` is genuinely `Constructive`.
        // ========================================

        // ========================================
        // instLinearOrderRat : LinearOrder Rat
        // LinearOrder.mk @Rat instPartialOrderRat Rat.le_total
        //
        // Previously an Axiom (#1628, #1526). Now a proper Definition (#3222).
        // ========================================
        let inst_linear_order_rat_type = Expr::app(
            Expr::const_(Name::from_string("LinearOrder"), vec![Level::zero()]),
            rat_const.clone(),
        );

        let inst_linear_order_rat_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LinearOrder.mk"), vec![Level::zero()]),
                    rat_const.clone(),
                ),
                Expr::const_(Name::from_string("instPartialOrderRat"), vec![]),
            ),
            Expr::const_(Name::from_string("Rat.le_total"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLinearOrderRat"),
            level_params: vec![],
            type_: inst_linear_order_rat_type,
            value: inst_linear_order_rat_value,
            is_reducible: true,
        })?;

        self.rat_linear_order_init = true;
        Ok(())
    }

    /// Check if Rat LinearOrder instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_linear_order_init == true`
    #[cfg(test)]
    pub(crate) fn has_rat_linear_order(&self) -> bool {
        self.rat_linear_order_init
    }

    /// Initialize the LinearOrderedField typeclass
    ///
    /// LinearOrderedField combines Field with LinearOrder and ordered field axioms.
    ///
    /// class LinearOrderedField (α : Type u) where
    ///   -- Field instance
    ///   toField : Field α
    ///   -- LinearOrder instance
    ///   toLinearOrder : LinearOrder α
    ///   -- Instance fields (flattened from LinearOrder hierarchy)
    ///   [toLE : LE α]
    ///   [toLT : LT α]
    ///   -- Ordered field axioms
    ///   add_le_add_left : ∀ a b : α, le a b → ∀ c : α, le (add c a) (add c b)
    ///   mul_pos : ∀ a b : α, lt zero a → lt zero b → lt zero (mul a b)
    ///   zero_lt_one : lt zero one
    ///
    /// This is 7 fields total.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.linear_ordered_field_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_linear_ordered_field(&mut self) -> Result<(), EnvError> {
        if self.linear_ordered_field_init {
            return Ok(());
        }

        // Dependencies
        self.init_field()?;
        self.init_linear_order()?;
        self.init_le()?;
        self.init_lt()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1) // Type u

        // Build constructor type using EnvDeclBuilder to avoid manual bvar arithmetic.
        // LinearOrderedField.mk : ∀ {α : Type u},
        //   (toField : Field α) →
        //   (toLinearOrder : LinearOrder α) →
        //   [toLE : LE α] → [toLT : LT α] →
        //   (add_le_add_left : ∀ a b : α, LE.le α inst a b → ...) →
        //   (mul_pos : ∀ a b : α, LT.lt α inst 0 a → ...) →
        //   (zero_lt_one : LT.lt α inst 0 1) →
        //   LinearOrderedField α
        let mk_type = {
            let mut bldr = EnvDeclBuilder::new();

            let (alpha_id, alpha) = bldr.fresh_local(type_u.clone());

            // Field α
            let field_alpha = Expr::app(
                Expr::const_(Name::from_string("Field"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (to_field_id, to_field) = bldr.fresh_local(field_alpha.clone());

            // LinearOrder α
            let linear_order_alpha = Expr::app(
                Expr::const_(Name::from_string("LinearOrder"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (to_linear_order_id, _to_linear_order) =
                bldr.fresh_local(linear_order_alpha.clone());

            // LE α and LT α instance fields (flattened from LinearOrder hierarchy)
            let le_alpha = Expr::app(
                Expr::const_(Name::from_string("LE"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (to_le_id, le_inst) = bldr.fresh_local(le_alpha.clone());

            let lt_alpha = Expr::app(
                Expr::const_(Name::from_string("LT"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (to_lt_id, lt_inst) = bldr.fresh_local(lt_alpha.clone());

            // Helper: LE.le {α} [inst] a b (4 args, matching order_structures.rs pattern)
            let le_le = |a: &Expr, b: &Expr| -> Expr {
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("LE.le"), vec![u_level.clone()]),
                                alpha.clone(),
                            ),
                            le_inst.clone(),
                        ),
                        a.clone(),
                    ),
                    b.clone(),
                )
            };

            // Helper: LT.lt {α} [inst] a b (4 args)
            let lt_lt = |a: &Expr, b: &Expr| -> Expr {
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("LT.lt"), vec![u_level.clone()]),
                                alpha.clone(),
                            ),
                            lt_inst.clone(),
                        ),
                        a.clone(),
                    ),
                    b.clone(),
                )
            };

            // add_le_add_left : ∀ a b : α, LE.le α inst a b → ∀ c : α, LE.le α inst (add c a) (add c b)
            let add_le_add_left_field_type = {
                let mut sub = EnvDeclBuilder::child_of(&bldr);
                let (a_id, a) = sub.fresh_local(alpha.clone());
                let (b_id, b) = sub.fresh_local(alpha.clone());

                let le_a_b = le_le(&a, &b);
                let (h_id, _h) = sub.fresh_local(le_a_b.clone());

                let (c_id, c) = sub.fresh_local(alpha.clone());

                // Field.add {α} inst
                let add_const = Expr::const_(Name::from_string("Field.add"), vec![u_level.clone()]);
                let add_inst = Expr::app(Expr::app(add_const, alpha.clone()), to_field.clone());
                let add_c_a = Expr::app(Expr::app(add_inst.clone(), c.clone()), a.clone());
                let add_c_b = Expr::app(Expr::app(add_inst, c.clone()), b.clone());

                let le_result = le_le(&add_c_a, &add_c_b);

                let e = sub.mk_pi(c_id, BinderInfo::Default, alpha.clone(), le_result);
                let e = sub.mk_pi(h_id, BinderInfo::Default, le_a_b, e);
                let e = sub.mk_pi(b_id, BinderInfo::Default, alpha.clone(), e);
                // Don't call sub.finish() — result still contains outer FVars (alpha, to_field, etc.)
                // which will be closed by the outer builder's mk_pi calls.
                sub.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e)
            };
            let (add_le_id, _add_le) = bldr.fresh_local(add_le_add_left_field_type.clone());

            // mul_pos : ∀ a b : α, LT.lt α inst 0 a → LT.lt α inst 0 b → LT.lt α inst 0 (mul a b)
            let mul_pos_field_type = {
                let mut sub = EnvDeclBuilder::child_of(&bldr);
                let (a_id, a) = sub.fresh_local(alpha.clone());
                let (b_id, b) = sub.fresh_local(alpha.clone());

                let zero_const =
                    Expr::const_(Name::from_string("Field.zero"), vec![u_level.clone()]);
                let zero = Expr::app(
                    Expr::app(zero_const.clone(), alpha.clone()),
                    to_field.clone(),
                );

                let lt_zero_a = lt_lt(&zero, &a);
                let (ha_id, _ha) = sub.fresh_local(lt_zero_a.clone());

                let lt_zero_b = lt_lt(&zero, &b);
                let (hb_id, _hb) = sub.fresh_local(lt_zero_b.clone());

                // Field.mul {α} inst a b
                let mul_const = Expr::const_(Name::from_string("Field.mul"), vec![u_level.clone()]);
                let mul_inst = Expr::app(Expr::app(mul_const, alpha.clone()), to_field.clone());
                let mul_a_b = Expr::app(Expr::app(mul_inst, a.clone()), b.clone());

                let lt_zero_mul = lt_lt(&zero, &mul_a_b);

                let e = sub.mk_pi(hb_id, BinderInfo::Default, lt_zero_b, lt_zero_mul);
                let e = sub.mk_pi(ha_id, BinderInfo::Default, lt_zero_a, e);
                let e = sub.mk_pi(b_id, BinderInfo::Default, alpha.clone(), e);
                // Don't call sub.finish() — result still contains outer FVars (alpha, to_field, etc.)
                // which will be closed by the outer builder's mk_pi calls.
                sub.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e)
            };
            let (mul_pos_id, _mul_pos) = bldr.fresh_local(mul_pos_field_type.clone());

            // zero_lt_one : LT.lt α inst 0 1
            let zero_lt_one_field_type = {
                let zero_const =
                    Expr::const_(Name::from_string("Field.zero"), vec![u_level.clone()]);
                let one_const = Expr::const_(Name::from_string("Field.one"), vec![u_level.clone()]);
                let zero = Expr::app(Expr::app(zero_const, alpha.clone()), to_field.clone());
                let one = Expr::app(Expr::app(one_const, alpha.clone()), to_field.clone());
                lt_lt(&zero, &one)
            };
            let (zero_lt_one_id, _zero_lt_one) = bldr.fresh_local(zero_lt_one_field_type.clone());

            // Result: LinearOrderedField α
            let linear_ordered_field_const = Expr::const_(
                Name::from_string("LinearOrderedField"),
                vec![u_level.clone()],
            );
            let result = Expr::app(linear_ordered_field_const, alpha.clone());

            // Close binders innermost-first
            let e = bldr.mk_pi(
                zero_lt_one_id,
                BinderInfo::Default,
                zero_lt_one_field_type,
                result,
            );
            let e = bldr.mk_pi(mul_pos_id, BinderInfo::Default, mul_pos_field_type, e);
            let e = bldr.mk_pi(
                add_le_id,
                BinderInfo::Default,
                add_le_add_left_field_type,
                e,
            );
            let e = bldr.mk_pi(to_lt_id, BinderInfo::InstImplicit, lt_alpha, e);
            let e = bldr.mk_pi(to_le_id, BinderInfo::InstImplicit, le_alpha, e);
            let e = bldr.mk_pi(
                to_linear_order_id,
                BinderInfo::Default,
                linear_order_alpha,
                e,
            );
            let e = bldr.mk_pi(to_field_id, BinderInfo::Default, field_alpha, e);
            let e = bldr.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            bldr.finish(e)
        };

        // LinearOrderedField type: Type u → Type u
        // Note: Type u = Sort (succ u), so the result is also Sort (succ u)
        let lof_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
        );

        // Create the inductive type
        let lof_decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1, // α is the parameter
            types: vec![InductiveType {
                name: Name::from_string("LinearOrderedField"),
                type_: lof_type,
                constructors: vec![Constructor {
                    name: Name::from_string("LinearOrderedField.mk"),
                    type_: mk_type,
                }],
            }],
        };

        self.add_inductive(lof_decl)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            Name::from_string("LinearOrderedField"),
            vec![
                Name::from_string("toField"),
                Name::from_string("toLinearOrder"),
                Name::from_string("toLE"),
                Name::from_string("toLT"),
                Name::from_string("add_le_add_left"),
                Name::from_string("mul_pos"),
                Name::from_string("zero_lt_one"),
            ],
        )?;

        let lof_const = |u: Level| Expr::const_(Name::from_string("LinearOrderedField"), vec![u]);

        // Add projections
        // LinearOrderedField.toField : {α : Type u} → [inst : LinearOrderedField α] → Field α
        let to_field_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let inst_ty = Expr::app(lof_const(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(inst_ty.clone());
            let result = Expr::app(
                Expr::const_(Name::from_string("Field"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, result);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Value: λ {α} [inst] => inst.0
        let to_field_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let inst_ty = Expr::app(lof_const(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(inst_ty.clone());
            let body = Expr::proj(Name::from_string("LinearOrderedField"), 0, inst.clone());
            let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, inst_ty, body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("LinearOrderedField.toField"),
            level_params: vec![u.clone()],
            type_: to_field_proj_type,
            value: to_field_proj_value,
            is_reducible: true,
        })?;

        // LinearOrderedField.toLinearOrder : {α : Type u} → [inst : LinearOrderedField α] → LinearOrder α
        let to_lo_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let inst_ty = Expr::app(lof_const(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(inst_ty.clone());
            let result = Expr::app(
                Expr::const_(Name::from_string("LinearOrder"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_ty, result);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Value: λ {α} [inst] => inst.1
        let to_lo_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let inst_ty = Expr::app(lof_const(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(inst_ty.clone());
            let body = Expr::proj(Name::from_string("LinearOrderedField"), 1, inst.clone());
            let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, inst_ty, body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("LinearOrderedField.toLinearOrder"),
            level_params: vec![u.clone()],
            type_: to_lo_proj_type,
            value: to_lo_proj_value,
            is_reducible: true,
        })?;

        self.linear_ordered_field_init = true;
        Ok(())
    }

    /// Check if LinearOrderedField typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.linear_ordered_field_init == true`
    #[cfg(test)]
    pub(crate) fn has_linear_ordered_field(&self) -> bool {
        self.linear_ordered_field_init
    }

    /// Initialize Rat ordered field axioms
    ///
    /// This adds the axioms needed for Rat to be a LinearOrderedField:
    /// - Rat.add_le_add_left : ∀ a b : Rat, Rat.le a b → ∀ c, Rat.le (Rat.add c a) (Rat.add c b)
    /// - Rat.mul_pos : ∀ a b : Rat, Rat.lt Rat.zero a → Rat.lt Rat.zero b → Rat.lt Rat.zero (Rat.mul a b)
    /// - Rat.zero_lt_one : Rat.lt Rat.zero Rat.one
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_ordered_field_axioms_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_rat_ordered_field_axioms(&mut self) -> Result<(), EnvError> {
        if self.rat_ordered_field_axioms_init {
            return Ok(());
        }

        // Dependencies
        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;

        // #3470 Lane #2/#3: `Rat.zero_lt_one` is now a kernel-checked
        // `Declaration::Theorem` (concrete `@Int.NonNeg.mk Nat.zero` witness),
        // registered here so it is present before `instLinearOrderedFieldRat`
        // consumes it. Idempotent / skip-if-present.
        self.register_rat_order_proofs()?;

        // WS-A ATOMIC LIVE SWITCH (step 3, payoff): `Rat.add_le_add_left` and
        // `Rat.le_add_of_nonneg_right` were both PROVABLY FALSE over the free
        // carrier (a `denom = 0` representative collapses `Rat.add`'s denominator
        // and the bare numerators get compared). Over the QUOTIENT carrier they
        // are GENUINE kernel-checked `Declaration::Theorem`s (same name + type),
        // registered by the payoff helper.
        self.rat_quotient_payoff_into_live()?;

        // Rat.mul_pos : ∀ a b : Rat, Rat.lt Rat.zero a → Rat.lt Rat.zero b → Rat.lt Rat.zero (Rat.mul a b)
        //
        // #3470 Lane #2/#3: now a kernel-checked `Declaration::Theorem`,
        // registered by `register_rat_order_proofs` at the top of this
        // initializer. Provable WITHOUT denominator cancellation because
        // `Rat.num Rat.zero ≡ Int.zero` makes the denominators drop out of every
        // `Rat.lt Rat.zero _` proposition; it reduces to the constructive
        // `Int.mul_pos` (with `Int.zero_mul` / `Int.mul_one` transports).
        // No longer a `Declaration::Axiom`.

        // Rat.zero_lt_one : Rat.lt Rat.zero Rat.one
        //
        // #3470 Lane #2/#3: now a kernel-checked `Declaration::Theorem`
        // (concrete `@Int.NonNeg.mk Nat.zero` witness), registered by
        // `register_rat_order_proofs` at the top of this initializer. No longer
        // a `Declaration::Axiom`.

        // Rat.le_add_of_nonneg_right is registered as a genuine quotient theorem
        // by `rat_quotient_payoff_into_live()` above (see the WS-A note).

        // Rat.mul_nonneg : ∀ a b : Rat, Rat.le Rat.zero a → Rat.le Rat.zero b → Rat.le Rat.zero (Rat.mul a b)
        //
        // Ordered field consequence: non-negative times non-negative is
        // non-negative. Now a kernel-checked `Declaration::Theorem`, registered
        // by `register_rat_order_proofs` (`register_rat_mul_nonneg`) at the top
        // of this initializer (idempotent / skip-if-present). Provable WITHOUT
        // denominator cancellation (and WITHOUT the unsound
        // `Rat.mk_eq_mk_of_cross_eq` bridge) because `Rat.num Rat.zero ≡
        // Int.zero` makes the denominators drop out of every `Rat.le Rat.zero _`
        // proposition; it reduces to the constructive `Int.mul_nonneg` (with
        // `Int.zero_mul` / `Int.mul_one` transports) — the exact `Rat.le` analog
        // of the `Rat.lt`-based `Rat.mul_pos`. No longer a `Declaration::Axiom`.

        self.rat_ordered_field_axioms_init = true;
        Ok(())
    }

    /// Check if Rat ordered field axioms have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_ordered_field_axioms_init == true`
    #[cfg(test)]
    pub(crate) fn has_rat_ordered_field_axioms(&self) -> bool {
        self.rat_ordered_field_axioms_init
    }

    /// Initialize Rat as a LinearOrderedField instance
    ///
    /// This creates instLinearOrderedFieldRat : LinearOrderedField Rat
    /// which combines instFieldRat, instLinearOrderRat, and the ordered field axioms.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_linear_ordered_field_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_rat_linear_ordered_field_inst(&mut self) -> Result<(), EnvError> {
        if self.rat_linear_ordered_field_inst_init {
            return Ok(());
        }

        // Dependencies
        self.init_linear_ordered_field()?;
        self.init_rat_field_inst()?;
        self.init_rat_linear_order()?;
        self.init_rat_ordered_field_axioms()?;

        let rat_type = Expr::const_(Name::from_string("Rat"), vec![]);

        // Instance type: LinearOrderedField Rat
        // Rat : Type 0, so LinearOrderedField.{0}
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("LinearOrderedField"), vec![Level::zero()]),
            rat_type.clone(),
        );

        // LinearOrderedField.mk @Rat instFieldRat instLinearOrderRat
        //   instLERat instLTRat Rat.add_le_add_left Rat.mul_pos Rat.zero_lt_one
        //
        // Previously an Axiom (#1628, #1526). Now a proper Definition (#3222).
        let inst_value = {
            let mk = Expr::const_(
                Name::from_string("LinearOrderedField.mk"),
                vec![Level::zero()],
            );
            let e = Expr::app(mk, rat_type.clone()); // @Rat
            let e = Expr::app(e, Expr::const_(Name::from_string("instFieldRat"), vec![]));
            let e = Expr::app(
                e,
                Expr::const_(Name::from_string("instLinearOrderRat"), vec![]),
            );
            let e = Expr::app(e, Expr::const_(Name::from_string("instLERat"), vec![]));
            let e = Expr::app(e, Expr::const_(Name::from_string("instLTRat"), vec![]));
            let e = Expr::app(
                e,
                Expr::const_(Name::from_string("Rat.add_le_add_left"), vec![]),
            );
            let e = Expr::app(e, Expr::const_(Name::from_string("Rat.mul_pos"), vec![]));
            Expr::app(
                e,
                Expr::const_(Name::from_string("Rat.zero_lt_one"), vec![]),
            )
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLinearOrderedFieldRat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.rat_linear_ordered_field_inst_init = true;
        Ok(())
    }

    /// Check if Rat LinearOrderedField instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_linear_ordered_field_inst_init == true`
    #[cfg(test)]
    pub(crate) fn has_rat_linear_ordered_field_inst(&self) -> bool {
        self.rat_linear_ordered_field_inst_init
    }
}
