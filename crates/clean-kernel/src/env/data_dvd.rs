// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `Dvd` divisibility class (Brick P1 — unregistered prelude heads).
//!
//! Registers the Lean 4 core class behind the `∣` notation as a fully
//! kernel-checked single-constructor structure (no axioms), its projection,
//! and the `Nat` instance with the real existential body:
//!
//! ```text
//! class Dvd (α : Type _) where
//!   dvd : α → α → Prop
//! instance : Dvd Nat where
//!   dvd a b := Exists (fun c => b = a * c)
//! ```
//!
//! Lean sources (toolchain `v4.30.0-rc2`): `Init/Prelude.lean:1557` (`Dvd`),
//! `Init/Data/Nat/Div/Basic.lean:24` (the `Nat` instance, inside
//! `namespace Nat`).
//!
//! Without this head, `a ∣ b` (audit row e05 in
//! `docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md`) resolved `Dvd.dvd` via
//! auto-implicit and failed `TooManyArguments { Sort(u) }`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `α → α → Prop` — the `dvd` field type.
fn dvd_field_ty(parent: &EnvDeclBuilder, alpha: &Expr) -> Expr {
    let mut c = EnvDeclBuilder::child_of(parent);
    let (a_id, _a) = c.fresh_local(alpha.clone());
    let (b_id, _b) = c.fresh_local(alpha.clone());
    let r = Expr::sort(Level::zero());
    let r = c.mk_pi(b_id, BinderInfo::Default, alpha.clone(), r);
    let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
    c.finish_child(r)
}

impl Environment {
    /// Register the `Dvd` class and its `Dvd.dvd` projection, all as
    /// fully-checked declarations.
    ///
    /// Lean fidelity: `Init/Prelude.lean:1557`
    /// `class Dvd (α : Type _) where dvd : α → α → Prop` — one universe, no
    /// outParams, `Prop`-valued field, hence `Dvd : Type u → Type u`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.dvd_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_dvd(&mut self) -> Result<(), EnvError> {
        if self.dvd_init {
            return Ok(());
        }

        let dvd_name = Name::from_string("Dvd");
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let class_const = Expr::const_(dvd_name.clone(), vec![u_level]);

        // Dvd.mk : {α : Type u} → (dvd : α → α → Prop) → Dvd α
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let field_ty = dvd_field_ty(&b, &alpha);
            let (field_id, _) = b.fresh_local(field_ty.clone());
            let class_ty = Expr::app(class_const.clone(), alpha.clone());
            let r = b.mk_pi(field_id, BinderInfo::Default, field_ty, class_ty);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: dvd_name.clone(),
                // (α : Type u) → Type u — the field `α → α → Prop` lives at
                // `Sort (u+1)` (any arrow into `Prop`'s type), so the class
                // former lands back at `Type u`, exactly Lean.
                type_: Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone()),
                constructors: vec![Constructor {
                    name: Name::from_string("Dvd.mk"),
                    type_: ctor_type,
                }],
            }],
        })?;

        self.register_structure_fields(dvd_name.clone(), vec![Name::from_string("dvd")])?;

        self.register_class(KernelClassInfo {
            name: dvd_name.clone(),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // Dvd.dvd : {α : Type u} → [self : Dvd α] → α → α → Prop
        let proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let class_ty = Expr::app(class_const.clone(), alpha.clone());
            let (inst_id, _) = b.fresh_local(class_ty.clone());
            let field_ty = dvd_field_ty(&b, &alpha);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, class_ty, field_ty);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let class_ty = Expr::app(class_const.clone(), alpha.clone());
            let (inst_id, inst) = b.fresh_local(class_ty.clone());
            let body = Expr::proj(dvd_name.clone(), 0, inst);
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, class_ty, body);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Dvd.dvd"),
            level_params: vec![u],
            type_: proj_type,
            value: proj_value,
            is_reducible: true,
        })?;

        self.dvd_init = true;
        Ok(())
    }

    /// Register `instDvdNat : Dvd Nat := Dvd.mk (fun a b => ∃ c, b = a * c)`
    /// — a checked Definition with the real existential body (no axioms, no
    /// sorry).
    ///
    /// Lean fidelity: `Init/Data/Nat/Div/Basic.lean:24`
    /// `instance : Dvd Nat where dvd a b := Exists (fun c => b = a * c)`.
    /// The multiplication is spelled with the prelude's `Nat.mul` constant
    /// (upstream's elaborated body routes the same value through
    /// `HMul.hMul … instMulNat`).
    ///
    /// IMPORT MODE (`suppress_lossy_structure_stubs`): withheld — upstream's
    /// instance (namespaced `Nat.…` in `v4.30`) spells the body through the
    /// `Mul Nat` instance chain, so pre-seeding a `Nat.mul`-spelled twin
    /// would diverge from the genuine olean value; the genuine instance
    /// imports through the checked path instead. The default lane is
    /// unchanged.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_dvd_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_dvd_inst(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.nat_dvd_inst_init {
            return Ok(());
        }

        self.init_dvd()?;
        self.init_nat()?; // Nat, Nat.mul
        self.init_eq()?;
        self.init_exists()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        // Nat : Type 0 = Sort 1, so Eq/Exists instantiate at level 1 and the
        // Dvd class at universe 0.
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let exists_const = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(Level::zero())],
        );
        let dvd_const = Expr::const_(Name::from_string("Dvd"), vec![Level::zero()]);
        let dvd_mk = Expr::const_(Name::from_string("Dvd.mk"), vec![Level::zero()]);

        let inst_type = Expr::app(dvd_const, nat_const.clone());

        // fun (a b : Nat) => Exists (fun (c : Nat) => Eq Nat b (Nat.mul a c))
        let dvd_fun = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat_const.clone());
            let (bb_id, bb) = b.fresh_local(nat_const.clone());
            let pred = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (c_id, cc) = c.fresh_local(nat_const.clone());
                let a_mul_c = Expr::apps(nat_mul.clone(), [a.clone(), cc]);
                let eq = Expr::apps(eq_const.clone(), [nat_const.clone(), bb.clone(), a_mul_c]);
                let r = c.mk_lam(c_id, BinderInfo::Default, nat_const.clone(), eq);
                c.finish_child(r)
            };
            let body = Expr::apps(exists_const.clone(), [nat_const.clone(), pred]);
            let r = b.mk_lam(bb_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), r);
            b.finish(r)
        };

        let inst_value = Expr::apps(dvd_mk, [nat_const, dvd_fun]);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instDvdNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instDvdNat"),
            class_name: Name::from_string("Dvd"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.nat_dvd_inst_init = true;
        Ok(())
    }
}
