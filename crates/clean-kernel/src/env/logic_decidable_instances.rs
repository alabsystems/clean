// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Canonical `Decidable True` / `Decidable False` instances.
//!
//! `init_decidable` registers the `Decidable` inductive plus its constructors,
//! but never defines the canonical endpoint instances. Without them,
//! `resolve_decidable(True)` / `resolve_decidable(False)` find no instance and
//! the elaborator falls back to a synthetic `sorry` for the `[Decidable c]`
//! argument of `ite`. A `sorry` instance is not a real `Decidable.isTrue` /
//! `Decidable.isFalse` constructor, so the kernel's `ite` reducer cannot fire
//! and `if True then a else b` never reduces to `a`.
//!
//! This module defines, kernel-checks, and registers:
//!
//! ```text
//! instDecidableTrue  : Decidable True  := Decidable.isTrue  True  True.intro
//! instDecidableFalse : Decidable False := Decidable.isFalse False (fun h : False => h)
//! ```
//!
//! Both values are *saturated constructors*, so they ι-reduce in the `ite`
//! reducer: `@ite α True  instDecidableTrue  a b ⟶ a`,
//! `@ite α False instDecidableFalse a b ⟶ b`. `add_decl` type-checks each body
//! against its declared type, so an ill-typed instance is rejected at
//! registration. Axiom closure is empty (only `Decidable`/`Decidable.isTrue`/
//! `Decidable.isFalse`/`True`/`True.intro`/`False` — no `Axiom`).
//!
//! `instDecidableFalse`'s value uses `fun (h : False) => h : False → False`,
//! which is exactly `¬False` (`False → False`), the argument `Decidable.isFalse`
//! demands for `p = False`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment, KernelInstanceInfo};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register `instDecidableTrue` and `instDecidableFalse`.
    ///
    /// Idempotent; axiom-free. Requires `init_true_false` + `init_decidable`
    /// (both auto-initialised here if not already present — neither has a cycle
    /// with this method).
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `Decidable True` / `Decidable False` resolve to the
    ///          canonical `isTrue` / `isFalse` instances.
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`.
    pub fn init_decidable_true_false(&mut self) -> Result<(), EnvError> {
        if self.decidable_true_false_inst_init {
            return Ok(());
        }

        self.init_true_false()?;
        self.init_decidable()?;

        let true_const = Expr::const_(Name::from_string("True"), vec![]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);

        // instDecidableTrue : Decidable True := @Decidable.isTrue True True.intro
        if self
            .get_const(&Name::from_string("instDecidableTrue"))
            .is_none()
        {
            let inst_type = Expr::app(decidable.clone(), true_const.clone());
            // @Decidable.isTrue : (p : Prop) → p → Decidable p
            let inst_value = Expr::apps(is_true, [true_const.clone(), true_intro]);

            self.add_decl(Declaration::Definition {
                name: Name::from_string("instDecidableTrue"),
                level_params: vec![],
                type_: inst_type,
                value: inst_value,
                is_reducible: true,
            })?;

            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instDecidableTrue"),
                class_name: Name::from_string("Decidable"),
                priority: 100,
                type_: None,
                value: None,
            });
        }

        // instDecidableFalse : Decidable False := @Decidable.isFalse False (fun h : False => h)
        if self
            .get_const(&Name::from_string("instDecidableFalse"))
            .is_none()
        {
            let inst_type = Expr::app(decidable.clone(), false_const.clone());
            // not_false : False → False  ==  fun (h : False) => h
            let id_false = {
                let mut b = EnvDeclBuilder::new();
                let (h_id, h) = b.fresh_local(false_const.clone());
                let lam = b.mk_lam(h_id, BinderInfo::Default, false_const.clone(), h);
                b.finish(lam)
            };
            // @Decidable.isFalse : (p : Prop) → (p → False) → Decidable p
            let inst_value = Expr::apps(is_false, [false_const.clone(), id_false]);

            self.add_decl(Declaration::Definition {
                name: Name::from_string("instDecidableFalse"),
                level_params: vec![],
                type_: inst_type,
                value: inst_value,
                is_reducible: true,
            })?;

            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instDecidableFalse"),
                class_name: Name::from_string("Decidable"),
                priority: 100,
                type_: None,
                value: None,
            });
        }

        self.decidable_true_false_inst_init = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    #[test]
    fn test_decidable_true_false_instances_type_check_and_axiom_free() {
        let env = Environment::with_prelude();
        for name in ["instDecidableTrue", "instDecidableFalse"] {
            let n = Name::from_string(name);
            let info = env
                .get_const(&n)
                .unwrap_or_else(|| panic!("{name} must be registered in the prelude"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} is a Definition"
            );

            let tc = TypeChecker::with_mode(&env, env.mode());
            let value = info.value.as_ref().expect("must have a body");
            let inferred = tc
                .infer_type(value)
                .unwrap_or_else(|e| panic!("{name} body must type-check: {e:?}"));
            assert!(
                tc.is_def_eq(&inferred, &info.type_),
                "{name} body type must be def-eq to declared type"
            );

            let deps = env.axiom_deps(&n).unwrap_or_default();
            assert!(deps.is_empty(), "{name} must be axiom-free, got {deps:?}");
        }
    }

    #[test]
    fn test_decidable_true_false_registered_as_instances() {
        let env = Environment::with_prelude();
        assert!(env.is_instance(&Name::from_string("instDecidableTrue")));
        assert!(env.is_instance(&Name::from_string("instDecidableFalse")));
    }

    /// End-to-end: `@ite Nat True instDecidableTrue 1 2` reduces to `1`,
    /// `@ite Nat False instDecidableFalse 1 2` reduces to `2`. A FALSE
    /// reduction (True → else / False → then) must NOT happen.
    #[test]
    fn test_ite_reduces_with_canonical_decidable_instances() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let one = Expr::nat_lit(1);
        let two = Expr::nat_lit(2);
        let ite = Expr::const_(Name::from_string("ite"), vec![Level::zero()]);

        // @ite Nat True instDecidableTrue 1 2 ⟶ 1
        let t = Expr::const_(Name::from_string("True"), vec![]);
        let inst_t = Expr::const_(Name::from_string("instDecidableTrue"), vec![]);
        let ite_true = Expr::apps(
            ite.clone(),
            [nat.clone(), t, inst_t, one.clone(), two.clone()],
        );
        let r = tc.whnf(&ite_true);
        assert!(
            matches!(r.kind(), ExprKind::Lit(_)),
            "ite True should reduce to a literal, got {r:?}"
        );
        assert!(tc.is_def_eq(&r, &one), "ite True must reduce to THEN (1)");

        // @ite Nat False instDecidableFalse 1 2 ⟶ 2
        let f = Expr::const_(Name::from_string("False"), vec![]);
        let inst_f = Expr::const_(Name::from_string("instDecidableFalse"), vec![]);
        let ite_false = Expr::apps(ite, [nat, f, inst_f, one.clone(), two.clone()]);
        let r2 = tc.whnf(&ite_false);
        assert!(tc.is_def_eq(&r2, &two), "ite False must reduce to ELSE (2)");
        // Soundness: must NOT reduce to the then-branch.
        assert!(
            !tc.is_def_eq(&r2, &one),
            "ite False must NOT reduce to THEN (1)"
        );
    }
}
