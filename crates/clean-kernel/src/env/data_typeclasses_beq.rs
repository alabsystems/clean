// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! BEq typeclass initialization for Environment
//!
//! This module contains:
//! - BEq typeclass and instances (Nat, Bool, Ordering)

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the BEq typeclass (Boolean Equality)
    ///
    /// BEq provides a decidable equality operation returning Bool:
    /// ```lean
    /// class BEq (α : Type u) where
    ///   beq : α → α → Bool
    /// ```
    ///
    /// Also adds basic instances for Nat, Bool, and Ordering.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.beq_init == true`
    /// ENSURES: On success, required dependencies (`bool`, `nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_beq(&mut self) -> Result<(), EnvError> {
        if self.beq_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_bool()?;
        self.init_nat()?;
        // `instBEqList`/`List.beq` (registered at the tail of this method via
        // `init_beq_list`) require `List` to be present. `with_prelude` already
        // runs `init_list` earlier, but standalone `init_beq()` callers (tests)
        // do not — and `init_list` is idempotent, so requesting it here is safe.
        self.init_list()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);

        let beq_const = |u: Level| Expr::const_(Name::from_string("BEq"), vec![u]);

        // BEq.mk : {α : Type u} → (α → α → Bool) → BEq α
        let beq_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            // f : α → α → Bool
            let f_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a1_id, _a1) = c.fresh_local(alpha.clone());
                let (a2_id, _a2) = c.fresh_local(alpha.clone());
                let r = bool_const.clone();
                let r = c.mk_pi(a2_id, BinderInfo::Default, alpha.clone(), r);
                let r = c.mk_pi(a1_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let r = Expr::app(beq_const(u_level.clone()), alpha.clone());
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let beq_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("BEq"),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    type_u.clone(),
                    Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
                ),
                constructors: vec![Constructor {
                    name: Name::from_string("BEq.mk"),
                    type_: beq_mk_type,
                }],
            }],
        };

        self.add_inductive(beq_ind)?;

        // Register BEq as a structure with one field (beq).
        self.register_structure_fields(Name::from_string("BEq"), vec![Name::from_string("beq")])?;

        // Register BEq as a typeclass so instance synthesis can find it.
        // BEq has 1 parameter (α : Type u), no output params.
        self.register_class(KernelClassInfo {
            name: Name::from_string("BEq"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // BEq.beq : {α : Type u} → [inst : BEq α] → α → α → Bool
        let beq_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) =
                b.fresh_local(Expr::app(beq_const(u_level.clone()), alpha.clone()));
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b2_id, _b2) = b.fresh_local(alpha.clone());
            let r = bool_const.clone();
            let r = b.mk_pi(b2_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(beq_const(u_level.clone()), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let beq_rec =
            |u1: Level, u2: Level| Expr::const_(Name::from_string("BEq.rec"), vec![u1, u2]);

        // BEq.beq value: λ {α} [inst] (a b : α) => (BEq.rec α motive minor inst) a b
        let beq_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) =
                b.fresh_local(Expr::app(beq_const(u_level.clone()), alpha.clone()));
            let (a_id, a_var) = b.fresh_local(alpha.clone());
            let (b2_id, b_var) = b.fresh_local(alpha.clone());

            // Motive: λ (_ : BEq α) => α → α → Bool
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) =
                    c.fresh_local(Expr::app(beq_const(u_level.clone()), alpha.clone()));
                let inner = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, _x) = d.fresh_local(alpha.clone());
                    let (y_id, _y) = d.fresh_local(alpha.clone());
                    let r = bool_const.clone();
                    let r = d.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
                    let r = d.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                    d.finish_child(r)
                };
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    Expr::app(beq_const(u_level.clone()), alpha.clone()),
                    inner,
                );
                c.finish_child(r)
            };

            // Minor: λ (f : α → α → Bool) => f
            let minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let f_ty = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, _x) = d.fresh_local(alpha.clone());
                    let (y_id, _y) = d.fresh_local(alpha.clone());
                    let r = bool_const.clone();
                    let r = d.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
                    let r = d.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                    d.finish_child(r)
                };
                let (f_id, f) = c.fresh_local(f_ty.clone());
                let r = f;
                let r = c.mk_lam(f_id, BinderInfo::Default, f_ty, r);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    beq_rec(Level::succ(u_level.clone()), u_level.clone()),
                                    alpha.clone(),
                                ),
                                motive,
                            ),
                            minor,
                        ),
                        inst,
                    ),
                    a_var,
                ),
                b_var,
            );
            let r = b.mk_lam(b2_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(beq_const(u_level.clone()), alpha.clone()),
                r,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("BEq.beq"),
            level_params: vec![u.clone()],
            type_: beq_type,
            value: beq_value,
            is_reducible: true,
        })?;

        // instBEqNat : BEq Nat := ⟨Nat.beq⟩
        //
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate — the
        // instance wraps the import-gated `Nat.beq` seed (see
        // order_nat_cmp.rs::init_nat_cmp); the genuine olean `instBEqNat`
        // imports through the checked path. Default lane byte-identical.
        if !self.suppress_lossy_structure_stubs {
            self.init_nat_cmp()?;
            let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
            let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);

            let beq_nat_type = Expr::app(
                Expr::const_(Name::from_string("BEq"), vec![Level::zero()]),
                nat_const.clone(),
            );
            let beq_nat_value = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("BEq.mk"), vec![Level::zero()]),
                    nat_const.clone(),
                ),
                nat_beq,
            );

            self.add_decl(Declaration::Definition {
                name: Name::from_string("instBEqNat"),
                level_params: vec![],
                type_: beq_nat_type,
                value: beq_nat_value,
                is_reducible: true,
            })?;

            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instBEqNat"),
                class_name: Name::from_string("BEq"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        // instBEqInt : BEq Int := ⟨Int.beq⟩
        //
        // Mirrors `instBEqNat`. `Int.beq` is registered as an Opaque op (backed
        // by the `Int.beq` native reducer) in `init_int_arith`. Backs `==`/`!=`
        // over `Int` (`rhs == 0`, `w1 != width`, … in trust-ir's
        // `Semantics/Arith.lean`); without it those left a `[BEq Int]` argument
        // unfilled ("contains free variables"). (Track EF)
        //
        // IMPORT MODE: the Int arithmetic cluster is suppressed (see
        // `init_int_arith`), so `Int.beq` does not exist to wrap — skip the
        // instance; the genuine olean `instBEqInt` imports instead.
        if !self.suppress_lossy_structure_stubs {
            self.init_int_arith()?;
            let int_const = Expr::const_(Name::from_string("Int"), vec![]);
            let int_beq = Expr::const_(Name::from_string("Int.beq"), vec![]);
            let beq_int_type = Expr::app(
                Expr::const_(Name::from_string("BEq"), vec![Level::zero()]),
                int_const.clone(),
            );
            let beq_int_value = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("BEq.mk"), vec![Level::zero()]),
                    int_const.clone(),
                ),
                int_beq,
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instBEqInt"),
                level_params: vec![],
                type_: beq_int_type,
                value: beq_int_value,
                is_reducible: true,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instBEqInt"),
                class_name: Name::from_string("BEq"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        // instBEqBool : BEq Bool
        // Bool.beq is defined via pattern matching
        // true == true = true, false == false = true, _ = false
        let bool_type = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );

        // Bool.beq : Bool → Bool → Bool
        // beq b1 b2 := Bool.rec (Bool.rec false true b2) (Bool.rec true false b2) b1
        // i.e., beq false false = true, beq false true = false
        //       beq true false = false, beq true true = true
        let bool_beq_motive = Expr::lam(BinderInfo::Default, bool_type.clone(), bool_type.clone());

        // For b1 = false: Bool.rec false true b2
        let false_case = Expr::app(
            Expr::app(
                Expr::app(bool_rec.clone(), bool_beq_motive.clone()),
                bool_true.clone(), // false == false = true
            ),
            bool_false.clone(), // false == true = false
        );

        // For b1 = true: Bool.rec true false b2
        let true_case = Expr::app(
            Expr::app(
                Expr::app(bool_rec.clone(), bool_beq_motive.clone()),
                bool_false.clone(), // true == false = false
            ),
            bool_true.clone(), // true == true = true
        );

        let bool_beq_value = {
            let mut b = EnvDeclBuilder::new();
            let (b1_id, b1) = b.fresh_local(bool_type.clone());
            let (b2_id, b2) = b.fresh_local(bool_type.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(bool_rec.clone(), bool_beq_motive.clone()),
                        Expr::app(false_case, b2.clone()),
                    ),
                    Expr::app(true_case, b2),
                ),
                b1,
            );
            let r = b.mk_lam(b2_id, BinderInfo::Default, bool_type.clone(), body);
            let r = b.mk_lam(b1_id, BinderInfo::Default, bool_type.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Bool.beq"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                bool_type.clone(),
                Expr::pi(BinderInfo::Default, bool_type.clone(), bool_type.clone()),
            ),
            value: bool_beq_value,
            is_reducible: true,
        })?;

        let beq_bool_type = Expr::app(
            Expr::const_(Name::from_string("BEq"), vec![Level::zero()]),
            bool_type.clone(),
        );
        let beq_bool_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("BEq.mk"), vec![Level::zero()]),
                bool_type.clone(),
            ),
            Expr::const_(Name::from_string("Bool.beq"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instBEqBool"),
            level_params: vec![],
            type_: beq_bool_type,
            value: beq_bool_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instBEqBool"),
            class_name: Name::from_string("BEq"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // instBEqOrdering : BEq Ordering
        self.init_ordering()?;
        let ordering_const = Expr::const_(Name::from_string("Ordering"), vec![]);
        let ordering_rec = Expr::const_(
            Name::from_string("Ordering.rec"),
            vec![Level::succ(Level::zero())],
        );

        // Ordering.beq o1 o2 uses double pattern match
        // beq o1 o2 := Ordering.rec (inner_lt o2) (inner_eq o2) (inner_gt o2) o1
        // where inner_lt o2 = Ordering.rec true false false o2, etc.
        let ord_beq_motive = Expr::lam(
            BinderInfo::Default,
            ordering_const.clone(),
            bool_type.clone(),
        );

        // Inner case functions (partially applied, waiting for o2)
        let inner_lt = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(ordering_rec.clone(), ord_beq_motive.clone()),
                    bool_true.clone(), // lt == lt
                ),
                bool_false.clone(), // lt == eq
            ),
            bool_false.clone(), // lt == gt
        );

        let inner_eq = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(ordering_rec.clone(), ord_beq_motive.clone()),
                    bool_false.clone(), // eq == lt
                ),
                bool_true.clone(), // eq == eq
            ),
            bool_false.clone(), // eq == gt
        );

        let inner_gt = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(ordering_rec.clone(), ord_beq_motive.clone()),
                    bool_false.clone(), // gt == lt
                ),
                bool_false.clone(), // gt == eq
            ),
            bool_true.clone(), // gt == gt
        );

        // beq o1 o2 := Ordering.rec motive (inner_lt o2) (inner_eq o2) (inner_gt o2) o1
        let ordering_beq_value = {
            let mut b = EnvDeclBuilder::new();
            let (o1_id, o1) = b.fresh_local(ordering_const.clone());
            let (o2_id, o2) = b.fresh_local(ordering_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(ordering_rec.clone(), ord_beq_motive.clone()),
                            Expr::app(inner_lt, o2.clone()),
                        ),
                        Expr::app(inner_eq, o2.clone()),
                    ),
                    Expr::app(inner_gt, o2),
                ),
                o1,
            );
            let r = b.mk_lam(o2_id, BinderInfo::Default, ordering_const.clone(), body);
            let r = b.mk_lam(o1_id, BinderInfo::Default, ordering_const.clone(), r);
            b.finish(r)
        };

        let ordering_beq_type = {
            let mut b = EnvDeclBuilder::new();
            let (o1_id, _o1) = b.fresh_local(ordering_const.clone());
            let (o2_id, _o2) = b.fresh_local(ordering_const.clone());
            let r = bool_type.clone();
            let r = b.mk_pi(o2_id, BinderInfo::Default, ordering_const.clone(), r);
            let r = b.mk_pi(o1_id, BinderInfo::Default, ordering_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Ordering.beq"),
            level_params: vec![],
            type_: ordering_beq_type,
            value: ordering_beq_value,
            is_reducible: true,
        })?;

        let beq_ordering_type = Expr::app(
            Expr::const_(Name::from_string("BEq"), vec![Level::zero()]),
            ordering_const.clone(),
        );
        let beq_ordering_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("BEq.mk"), vec![Level::zero()]),
                ordering_const,
            ),
            Expr::const_(Name::from_string("Ordering.beq"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instBEqOrdering"),
            level_params: vec![],
            type_: beq_ordering_type,
            value: beq_ordering_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instBEqOrdering"),
            class_name: Name::from_string("BEq"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // Parametric `BEq (List α)` instance (depends on List + BEq + Bool.and,
        // all registered above / by init_nat).
        self.init_beq_list()?;

        // `BEq Char` / `BEq String` / parametric `BEq (Option α)` (the String
        // instance depends on `List.beq` + `instBEqChar`, so this runs after
        // `init_beq_list`).
        self.init_beq_optstr()?;

        self.beq_init = true;
        Ok(())
    }

    /// Check if BEq typeclass has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_beq` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_beq(&self) -> bool {
        self.beq_init
    }
}
