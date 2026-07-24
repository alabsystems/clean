// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat min/max and Ord typeclass for Environment
//!
//! This module contains:
//! - Nat.min, Nat.max (min/max operations via Nat.ble)
//! - Ord typeclass (compare : α → α → Ordering)
//! - Instances: instOrdNat, instOrdBool, instOrdOrdering

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Nat min/max operations
    ///
    /// Nat.min : Nat → Nat → Nat (returns smaller value)
    /// Nat.max : Nat → Nat → Nat (returns larger value)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_minmax_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_minmax(&mut self) -> Result<(), EnvError> {
        if self.nat_minmax_init {
            return Ok(());
        }

        // Ensure dependencies
        self.init_nat()?;
        self.init_nat_cmp()?;
        self.init_bool()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_ble = Expr::const_(Name::from_string("Nat.ble"), vec![]);
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );

        // Nat.min m n := if m ≤ n then m else n
        // Using Bool.rec: Bool.rec n m (Nat.ble m n)
        // i.e., if (m ≤ n) = false then n, if (m ≤ n) = true then m
        let min_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(nat_const.clone());
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let r = nat_const.clone();
            let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let min_motive = Expr::lam(BinderInfo::Default, bool_ty.clone(), nat_const.clone());

        // min m n = Bool.rec (motive) n m (ble m n)
        // false -> n (m > n, return n)
        // true -> m (m ≤ n, return m)
        let min_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_const.clone()); // m
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(bool_rec.clone(), min_motive.clone()),
                        n.clone(), // false case: n
                    ),
                    m.clone(), // true case: m
                ),
                Expr::app(
                    Expr::app(nat_ble.clone(), m), // ble m
                    n,                             // n
                ),
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.min"),
            level_params: vec![],
            type_: min_type,
            value: min_value,
            is_reducible: true,
        })?;

        // Nat.max m n := if m ≤ n then n else m
        // Using Bool.rec: Bool.rec m n (Nat.ble m n)
        // i.e., if (m ≤ n) = false then m, if (m ≤ n) = true then n
        let max_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(nat_const.clone());
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let r = nat_const.clone();
            let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        let max_motive = Expr::lam(BinderInfo::Default, bool_ty, nat_const.clone());

        // max m n = Bool.rec (motive) m n (ble m n)
        // false -> m (m > n, return m)
        // true -> n (m ≤ n, return n)
        let max_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(nat_const.clone()); // m
            let (n_id, n) = b.fresh_local(nat_const.clone()); // n
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(bool_rec.clone(), max_motive),
                        m.clone(), // false case: m
                    ),
                    n.clone(), // true case: n
                ),
                Expr::app(
                    Expr::app(nat_ble, m), // ble m
                    n,                     // n
                ),
            );
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.max"),
            level_params: vec![],
            type_: max_type,
            value: max_value,
            is_reducible: true,
        })?;

        self.nat_minmax_init = true;
        Ok(())
    }

    /// Check if Nat min/max operations have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_minmax_init == true`
    pub(crate) fn has_nat_minmax(&self) -> bool {
        self.nat_minmax_init
    }

    /// Register one homogeneous binary-op typeclass (`Min` / `Max`) plus its
    /// reducible projection method (`Min.min` / `Max.max`) and a lowercase
    /// surface alias (`min` / `max`).
    ///
    /// Models `init_add` / `init_neg` (homogeneous one-type-parameter classes):
    /// ```text
    /// class Min (α : Type u) where
    ///   min : α → α → α
    /// Min.min : {α : Type u} → [Min α] → α → α → α
    /// min     : {α : Type u} → [Min α] → α → α → α := Min.min   -- export alias
    /// ```
    ///
    /// `class_name = "Min"`, `ctor_name = "Min.mk"`, `method_name = "Min.min"`,
    /// `alias_name = "min"`.
    fn init_binop_class(
        &mut self,
        class_name: &str,
        ctor_name: &str,
        field_name: &str,
        method_name: &str,
        alias_name: &str,
    ) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)

        let class_const = |u: Level| Expr::const_(Name::from_string(class_name), vec![u]);

        // Min : Type u → Type u
        let class_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(type_u.clone());
            let e = type_u.clone();
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Min.mk : {α : Type u} → (α → α → α) → Min α
        let mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            // field type: α → α → α
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b2_id, _b2) = b.fresh_local(alpha.clone());
            let field_body = alpha.clone();
            let field_type = b.mk_pi(b2_id, BinderInfo::Default, alpha.clone(), field_body);
            let field_type = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), field_type);
            let (field_id, _field) = b.fresh_local(field_type.clone());
            let e = Expr::app(class_const(u_level.clone()), alpha.clone());
            let e = b.mk_pi(field_id, BinderInfo::Default, field_type, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let class_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string(class_name),
                type_: class_type,
                constructors: vec![Constructor {
                    name: Name::from_string(ctor_name),
                    type_: mk_type,
                }],
            }],
        };

        self.add_inductive(class_ind)?;

        // Register structure fields for Expr::proj support.
        self.register_structure_fields(
            Name::from_string(class_name),
            vec![Name::from_string(field_name)],
        )?;

        // Register `Min`/`Max` as homogeneous one-param classes (no out-params)
        // so the elaborator's instance resolution recognises `Min α` goals.
        self.register_class(KernelClassInfo {
            name: Name::from_string(class_name),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // Min.min : {α : Type u} → [inst : Min α] → α → α → α
        let method_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) =
                b.fresh_local(Expr::app(class_const(u_level.clone()), alpha.clone()));
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (b_id, _b) = b.fresh_local(alpha.clone());
            let e = alpha.clone();
            let e = b.mk_pi(b_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(class_const(u_level.clone()), alpha.clone()),
                e,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Min.min value = λ {α} [inst : Min α] => Expr.proj(class, 0, inst)
        let method_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) =
                b.fresh_local(Expr::app(class_const(u_level.clone()), alpha.clone()));
            let body = Expr::proj(Name::from_string(class_name), 0, inst);
            let e = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(class_const(u_level.clone()), alpha.clone()),
                body,
            );
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string(method_name),
            level_params: vec![u.clone()],
            type_: method_type.clone(),
            value: method_value,
            is_reducible: true,
        })?;

        // Lowercase surface alias `min`/`max` := Min.min/Max.max (`export Min (min)`).
        // Surface `min a b` resolves the bare identifier to this const, which is a
        // reducible eta-alias of the projection method, so it whnf-reduces through
        // the instance to the bare `Nat.min`/`Nat.max` op. Same type as the method.
        let alias_value = Expr::const_(Name::from_string(method_name), vec![u_level.clone()]);
        self.add_decl(Declaration::Definition {
            name: Name::from_string(alias_name),
            level_params: vec![u],
            type_: method_type,
            value: alias_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Initialize the `Min` and `Max` homogeneous typeclasses plus their
    /// lowercase surface aliases.
    ///
    /// ```text
    /// class Min (α : Type u) where min : α → α → α
    /// class Max (α : Type u) where max : α → α → α
    /// ```
    ///
    /// Without these registered, surface `min a b` / `max a b` (a bare lowercase
    /// identifier) fails to resolve to any environment constant; the elaborator
    /// then over-applies it (`TooManyArguments`). All emitted declarations are
    /// inductives / reducible `Definition`s (no `Axiom`), so the domain-specific
    /// axiom count is unchanged.
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.minmax_class_init == true`
    /// ENSURES: Idempotent.
    pub(crate) fn init_minmax_class(&mut self) -> Result<(), EnvError> {
        if self.minmax_class_init {
            return Ok(());
        }

        self.init_binop_class("Min", "Min.mk", "min", "Min.min", "min")?;
        self.init_binop_class("Max", "Max.mk", "max", "Max.max", "max")?;

        self.minmax_class_init = true;
        Ok(())
    }

    /// Check if the Min/Max typeclasses have been initialized.
    pub(crate) fn has_minmax_class(&self) -> bool {
        self.minmax_class_init
    }

    /// Initialize the `Min Nat` / `Max Nat` instances backed by the bare
    /// `Nat.min` / `Nat.max` operations:
    /// ```text
    /// instance instMinNat : Min Nat := Min.mk Nat Nat.min
    /// instance instMaxNat : Max Nat := Max.mk Nat Nat.max
    /// ```
    ///
    /// `@Min.min Nat instMinNat a b` is definitionally `Nat.min a b` (projection
    /// of the constructor that stores `Nat.min`), so any proof valid for the bare
    /// `Nat.min` form remains kernel-valid for the surface form. Both instances
    /// are reducible `Definition`s (no `Axiom`), so the domain-specific axiom
    /// count is unchanged.
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.nat_minmax_inst_init == true`
    /// ENSURES: Idempotent.
    pub(crate) fn init_nat_minmax_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_minmax_inst_init {
            return Ok(());
        }

        self.init_minmax_class()?;
        self.init_nat_minmax()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        // instMinNat : Min Nat := Min.mk Nat Nat.min
        let min_inst_type = Expr::app(
            Expr::const_(Name::from_string("Min"), vec![Level::zero()]),
            nat_const.clone(),
        );
        let min_inst_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Min.mk"), vec![Level::zero()]),
                nat_const.clone(),
            ),
            Expr::const_(Name::from_string("Nat.min"), vec![]),
        );
        self.add_decl(Declaration::Definition {
            name: Name::from_string("instMinNat"),
            level_params: vec![],
            type_: min_inst_type,
            value: min_inst_value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instMinNat"),
            class_name: Name::from_string("Min"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // instMaxNat : Max Nat := Max.mk Nat Nat.max
        let max_inst_type = Expr::app(
            Expr::const_(Name::from_string("Max"), vec![Level::zero()]),
            nat_const.clone(),
        );
        let max_inst_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Max.mk"), vec![Level::zero()]),
                nat_const,
            ),
            Expr::const_(Name::from_string("Nat.max"), vec![]),
        );
        self.add_decl(Declaration::Definition {
            name: Name::from_string("instMaxNat"),
            level_params: vec![],
            type_: max_inst_type,
            value: max_inst_value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instMaxNat"),
            class_name: Name::from_string("Max"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.nat_minmax_inst_init = true;
        Ok(())
    }

    /// Check if the Min/Max Nat instances have been initialized.
    pub(crate) fn has_nat_minmax_inst(&self) -> bool {
        self.nat_minmax_inst_init
    }

    /// Initialize Ord typeclass
    ///
    /// class Ord (α : Type u) where
    ///   compare : α → α → Ordering
    ///
    /// Provides a total ordering on a type via the compare function.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ord_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_ord(&mut self) -> Result<(), EnvError> {
        if self.ord_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_ordering()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let ordering_const = Expr::const_(Name::from_string("Ordering"), vec![]);

        // Ord : Type u → Type u
        let ord_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _a) = b.fresh_local(type_u.clone());
            let r = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
            let r = b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // Ord.mk : {α : Type u} → (α → α → Ordering) → Ord α
        let ord_const = Expr::const_(Name::from_string("Ord"), vec![u_level.clone()]);
        let ord_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone()); // α : Type u
                                                                   // compare : α → α → Ordering
            let cmp_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let (y_id, _y) = c.fresh_local(alpha.clone());
                let r = ordering_const.clone();
                let r = c.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (cmp_id, _cmp) = b.fresh_local(cmp_ty.clone());
            let r = Expr::app(ord_const.clone(), alpha.clone()); // Ord α
            let r = b.mk_pi(cmp_id, BinderInfo::Default, cmp_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let ord_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Ord"),
                type_: ord_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Ord.mk"),
                    type_: ord_mk_type,
                }],
            }],
        };

        self.add_inductive(ord_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            Name::from_string("Ord"),
            vec![Name::from_string("compare")],
        )?;

        // Register Ord as a typeclass so instance synthesis discovers it. Without
        // this the elaborator's `init_instances_from_env` (which iterates
        // `env.classes()`) never queries `Ord`'s instances, so `instOrdNat` &c.
        // stay invisible to `resolve_instance`. Ord has 1 param (α : Type u), no
        // output params. Mirrors `init_beq`'s `register_class`.
        self.register_class(KernelClassInfo {
            name: Name::from_string("Ord"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // Ord.compare : {α : Type u} → [inst : Ord α] → α → α → Ordering
        let compare_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone()); // α : Type u
            let (inst_id, _inst) = b.fresh_local(Expr::app(ord_const.clone(), alpha.clone())); // inst : Ord α
            let (a_id, _a) = b.fresh_local(alpha.clone()); // a : α
            let (b2_id, _b2) = b.fresh_local(alpha.clone()); // b : α
            let r = ordering_const.clone();
            let r = b.mk_pi(b2_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(ord_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // Ord.compare value = λ {α} [inst : Ord α] (a b : α) =>
        //   (Expr::proj("Ord", 0, inst)) a b
        let compare_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone()); // α
            let (inst_id, inst) = b.fresh_local(Expr::app(ord_const.clone(), alpha.clone())); // inst : Ord α
            let (a_id, a) = b.fresh_local(alpha.clone()); // a : α
            let (b2_id, b2) = b.fresh_local(alpha.clone()); // b : α
            let body = Expr::app(
                Expr::app(
                    Expr::proj(Name::from_string("Ord"), 0, inst),
                    a, // a
                ),
                b2, // b
            );
            let r = b.mk_lam(b2_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(ord_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Ord.compare"),
            level_params: vec![u.clone()],
            type_: compare_type,
            value: compare_value,
            is_reducible: true,
        })?;

        // --- Ord instance cluster: instOrdNat / instOrdBool / instOrdOrdering
        //     (+ their Clean-only compare-fn spellings) ---
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 closing census
        // 2026-07-15, ring 2 of the Nat core-arithmetic suppression
        // 4676c9cc8/cd5a4432): Lean v4.30's Init.Data.Ord.Basic stores
        //   instOrdNat      := ⟨fun x y => compareOfLessAndEq x y⟩
        //   instOrdBool     := ⟨match-compiled two-Bool matcher⟩
        //   instOrdOrdering := ⟨compareOn (·.ctorIdx)⟩
        // — anonymous lambdas over the now-genuine `Nat.decLt`/`decEq` and
        // `Ordering.ctorIdx`, with NO named `Nat.compare`/`Bool.compare`/
        // `Ordering.compare` constants at all. Clean's rec-spelled wrapper
        // seeds are never definitionally equal to those stuck matcher forms,
        // so every seeded twin blocked the genuine olean definition at the
        // import value-defeq dedup ("duplicate of seeded constant
        // instOrdNat/instOrdBool/instOrdOrdering: value not definitionally
        // equal", census root Init.Data.Ord.Basic 3 rows) and the surviving
        // Clean spellings then failed the genuine `Nat.compare_*` /
        // `Nat.instTransOrd` / grevlex lemma re-checks (Init.Data.Nat.Compare
        // 10, Init.Data.Order.Ord 3, Init.Grind.Ring.CommSolver 20 rows).
        //
        // SOUNDNESS: the gate only WITHHOLDS the Clean-native seeds in the
        // import-only prelude; the genuine olean instances register through
        // the normal CHECKED `add_decl` import path and are re-checked by the
        // unmodified kernel. The `Ord` class + `Ord.compare` projection above
        // are import-faithful (defeq to v4.30's) and stay in both lanes. The
        // proof-execution lane (`Environment::new()`) is byte-identical.
        if !self.suppress_lossy_structure_stubs {
            // instOrdNat : Ord Nat := ⟨Nat.compare⟩
            // Nat : Type 0, so Ord.{0}
            self.init_nat_cmp()?;
            let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
            let nat_compare = Expr::const_(Name::from_string("Nat.compare"), vec![]);

            let ord_nat_type = Expr::app(
                Expr::const_(Name::from_string("Ord"), vec![Level::zero()]),
                nat_const.clone(),
            );
            let ord_nat_value = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Ord.mk"), vec![Level::zero()]),
                    nat_const.clone(),
                ),
                nat_compare,
            );

            self.add_decl(Declaration::Definition {
                name: Name::from_string("instOrdNat"),
                level_params: vec![],
                type_: ord_nat_type,
                value: ord_nat_value,
                is_reducible: true,
            })?;
            // Make it discoverable by instance synthesis (`resolve_instance`), not
            // merely present as a definition — mirrors `instBEqNat`.
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instOrdNat"),
                class_name: Name::from_string("Ord"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });

            // instOrdBool : Ord Bool
            // Bool.compare via pattern matching on Ordering
            // false < true, so false.compare true = .lt, true.compare false = .gt
            let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
            let ordering_lt = Expr::const_(Name::from_string("Ordering.lt"), vec![]);
            let ordering_eq = Expr::const_(Name::from_string("Ordering.eq"), vec![]);
            let ordering_gt = Expr::const_(Name::from_string("Ordering.gt"), vec![]);
            let bool_rec = Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            );

            // Bool.compare : Bool → Bool → Ordering
            // compare b1 b2 := Bool.rec (Bool.rec eq gt b2) (Bool.rec lt eq b2) b1
            // false.compare false = eq, false.compare true = lt
            // true.compare false = gt, true.compare true = eq
            let bool_compare_type = Expr::pi(
                BinderInfo::Default,
                bool_const.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    bool_const.clone(),
                    ordering_const.clone(),
                ),
            );

            // Motive for Bool.rec: λ _ : Bool => Ordering
            let bool_motive = Expr::lam(
                BinderInfo::Default,
                bool_const.clone(),
                ordering_const.clone(),
            );

            // Bool.compare : λ b1 b2 =>
            //   Bool.rec (Bool.rec eq lt b2) (Bool.rec gt eq b2) b1
            let bool_compare_value = {
                let mut b = EnvDeclBuilder::new();
                let (b1_id, b1) = b.fresh_local(bool_const.clone()); // b1
                let (b2_id, b2) = b.fresh_local(bool_const.clone()); // b2

                // Inner rec for b2 when b1=false: Bool.rec eq lt b2
                let inner_false = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(bool_rec.clone(), bool_motive.clone()),
                            ordering_eq.clone(),
                        ),
                        ordering_lt.clone(),
                    ),
                    b2.clone(),
                );

                // Inner rec for b2 when b1=true: Bool.rec gt eq b2
                let inner_true = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(bool_rec.clone(), bool_motive.clone()),
                            ordering_gt.clone(),
                        ),
                        ordering_eq.clone(),
                    ),
                    b2,
                );

                // Outer motive: λ _ : Bool => Ordering
                let outer_motive = Expr::lam(
                    BinderInfo::Default,
                    bool_const.clone(),
                    ordering_const.clone(),
                );

                let body = Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(bool_rec.clone(), outer_motive), inner_false),
                        inner_true,
                    ),
                    b1,
                );
                let r = b.mk_lam(b2_id, BinderInfo::Default, bool_const.clone(), body);
                let r = b.mk_lam(b1_id, BinderInfo::Default, bool_const.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Bool.compare"),
                level_params: vec![],
                type_: bool_compare_type,
                value: bool_compare_value,
                is_reducible: true,
            })?;

            // instOrdBool : Ord Bool := ⟨Bool.compare⟩
            // Bool : Type 0, so Ord.{0}
            let ord_bool_type = Expr::app(
                Expr::const_(Name::from_string("Ord"), vec![Level::zero()]),
                bool_const.clone(),
            );
            let ord_bool_value = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Ord.mk"), vec![Level::zero()]),
                    bool_const.clone(),
                ),
                Expr::const_(Name::from_string("Bool.compare"), vec![]),
            );

            self.add_decl(Declaration::Definition {
                name: Name::from_string("instOrdBool"),
                level_params: vec![],
                type_: ord_bool_type,
                value: ord_bool_value,
                is_reducible: true,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instOrdBool"),
                class_name: Name::from_string("Ord"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });

            // instOrdOrdering : Ord Ordering
            // Ordering.compare via pattern matching
            // lt < eq < gt
            let ordering_compare_type = {
                let mut b = EnvDeclBuilder::new();
                let (o1_id, _o1) = b.fresh_local(ordering_const.clone());
                let (o2_id, _o2) = b.fresh_local(ordering_const.clone());
                let r = ordering_const.clone();
                let r = b.mk_pi(o2_id, BinderInfo::Default, ordering_const.clone(), r);
                let r = b.mk_pi(o1_id, BinderInfo::Default, ordering_const.clone(), r);
                b.finish(r)
            };

            let ordering_rec = Expr::const_(
                Name::from_string("Ordering.rec"),
                vec![Level::succ(Level::zero())],
            );

            // Motive for inner Ordering.rec: λ _ : Ordering => Ordering
            let simple_motive_inner = Expr::lam(
                BinderInfo::Default,
                ordering_const.clone(),
                ordering_const.clone(),
            );

            // Build inner compare functions for each o1 case using builder
            let mk_inner = |v_lt: Expr, v_eq: Expr, v_gt: Expr| {
                let mut b = EnvDeclBuilder::new();
                let (o2_id, o2) = b.fresh_local(ordering_const.clone());
                let body = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(ordering_rec.clone(), simple_motive_inner.clone()),
                                v_lt,
                            ),
                            v_eq,
                        ),
                        v_gt,
                    ),
                    o2,
                );
                let r = b.mk_lam(o2_id, BinderInfo::Default, ordering_const.clone(), body);
                b.finish(r)
            };

            // lt.compare: lt->eq, eq->lt, gt->lt
            let case_lt_fn = mk_inner(
                ordering_eq.clone(),
                ordering_lt.clone(),
                ordering_lt.clone(),
            );

            // eq.compare: lt->gt, eq->eq, gt->lt
            let case_eq_fn = mk_inner(
                ordering_gt.clone(),
                ordering_eq.clone(),
                ordering_lt.clone(),
            );

            // gt.compare: lt->gt, eq->gt, gt->eq
            let case_gt_fn = mk_inner(
                ordering_gt.clone(),
                ordering_gt.clone(),
                ordering_eq.clone(),
            );

            // Outer motive: λ _ : Ordering => Ordering → Ordering
            let outer_motive_ord = Expr::lam(
                BinderInfo::Default,
                ordering_const.clone(),
                Expr::pi(
                    BinderInfo::Default,
                    ordering_const.clone(),
                    ordering_const.clone(),
                ),
            );

            // Full compare: λ o1 o2 => (Ordering.rec outer_motive case_lt_fn case_eq_fn case_gt_fn o1) o2
            let ordering_compare_value = {
                let mut b = EnvDeclBuilder::new();
                let (o1_id, o1) = b.fresh_local(ordering_const.clone());
                let (o2_id, o2) = b.fresh_local(ordering_const.clone());
                let body = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(ordering_rec.clone(), outer_motive_ord),
                                    case_lt_fn,
                                ),
                                case_eq_fn,
                            ),
                            case_gt_fn,
                        ),
                        o1,
                    ),
                    o2,
                );
                let r = b.mk_lam(o2_id, BinderInfo::Default, ordering_const.clone(), body);
                let r = b.mk_lam(o1_id, BinderInfo::Default, ordering_const.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Ordering.compare"),
                level_params: vec![],
                type_: ordering_compare_type,
                value: ordering_compare_value,
                is_reducible: true,
            })?;

            // instOrdOrdering : Ord Ordering := ⟨Ordering.compare⟩
            // Ordering : Type 0, so Ord.{0}
            let ord_ordering_type = Expr::app(
                Expr::const_(Name::from_string("Ord"), vec![Level::zero()]),
                ordering_const.clone(),
            );
            let ord_ordering_value = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Ord.mk"), vec![Level::zero()]),
                    ordering_const.clone(),
                ),
                Expr::const_(Name::from_string("Ordering.compare"), vec![]),
            );

            self.add_decl(Declaration::Definition {
                name: Name::from_string("instOrdOrdering"),
                level_params: vec![],
                type_: ord_ordering_type,
                value: ord_ordering_value,
                is_reducible: true,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instOrdOrdering"),
                class_name: Name::from_string("Ord"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        } // end !suppress_lossy_structure_stubs (Ord instance cluster)

        self.ord_init = true;
        Ok(())
    }

    /// Check if Ord typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.ord_init == true`
    pub(crate) fn has_ord(&self) -> bool {
        self.ord_init
    }
}
