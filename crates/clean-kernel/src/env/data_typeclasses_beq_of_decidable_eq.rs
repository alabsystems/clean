// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parametric `instBEqOfDecidableEq` bridge: `[DecidableEq α] → BEq α`.
//!
//! Mirrors Lean 4 core's `instBEqOfDecidableEq`:
//! ```lean
//! instance instBEqOfDecidableEq {α : Type u} [DecidableEq α] : BEq α :=
//!   { beq := fun a b => decide (a = b) }
//! ```
//!
//! Registers:
//! - `instBEqOfDecidableEq : {α : Type u} → [DecidableEq α] → BEq α`
//!   — a parametric instance so that `==` (which desugars to `BEq.beq`) resolves
//!   on any `deriving DecidableEq` type that does *not* also `deriving BEq`
//!   (e.g. `ValueId`, `AllocId`). Without this bridge, `a == b` on such a type
//!   left a fresh meta for the missing `BEq α`, producing the
//!   "contains free variables" kernel-registration failure on
//!   `ValueMap.set`/`PermissionMap.set`.
//!
//! The bridge term is a genuine closed kernel term — no axioms, no `sorry`:
//! it is `BEq.mk α (fun a b => decide (Eq α a b) (decEq α inst a b))`, where
//! `decide : {p : Prop} → [Decidable p] → Bool` is the sound `Decidable.rec`
//! Bool form and `decEq α inst a b : Decidable (Eq α a b)` extracts the
//! decision from the `DecidableEq α` instance. The kernel re-checks the term;
//! its axiom closure is empty (see the tests at the tail of this file).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register the parametric `instBEqOfDecidableEq` bridge.
    ///
    /// Runs at the tail of `init_decidable_eq`, by which point `BEq`/`BEq.mk`
    /// (from `init_beq`, which `with_prelude` runs first), `Eq`, `Decidable`,
    /// the Bool-valued `decide`, `DecidableEq`, and `decEq` are all available.
    ///
    /// Guarded: if any prerequisite is missing (a sparser env that reaches
    /// `init_decidable_eq` without `init_beq`/`decide`), the bridge is skipped
    /// cleanly rather than producing an ill-typed term.
    pub(crate) fn init_beq_of_decidable_eq(&mut self) -> Result<(), EnvError> {
        // Prerequisites. `with_prelude` guarantees all of these; standalone or
        // minimal callers may not, so skip rather than fail.
        let have_prereqs = self.get_const(&Name::from_string("BEq")).is_some()
            && self.get_const(&Name::from_string("BEq.mk")).is_some()
            && self.get_const(&Name::from_string("Eq")).is_some()
            && self.get_const(&Name::from_string("DecidableEq")).is_some()
            && self.get_const(&Name::from_string("decEq")).is_some()
            && self.get_const(&Name::from_string("decide")).is_some();
        if !have_prereqs {
            return Ok(());
        }
        // Idempotent.
        if self
            .get_const(&Name::from_string("instBEqOfDecidableEq"))
            .is_some()
        {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        // α : Type u  =  Sort (u+1). Mirrors Lean's `{α : Type u}` binder; BEq
        // is `BEq.{u} (α : Sort (u+1))`, so `Eq`/`DecidableEq`/`decEq` are
        // instantiated at level `u+1`.
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let succ_u = Level::succ(u_level.clone());

        let beq_const = Expr::const_(Name::from_string("BEq"), vec![u_level.clone()]);
        let beq_mk = Expr::const_(Name::from_string("BEq.mk"), vec![u_level.clone()]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![succ_u.clone()]);
        let dec_eq_alpha_const =
            Expr::const_(Name::from_string("DecidableEq"), vec![succ_u.clone()]);
        let dec_eq_fn = Expr::const_(Name::from_string("decEq"), vec![succ_u.clone()]);
        // `decide : {p : Prop} → [Decidable p] → Bool` — registered with no level
        // params (it lives at `Prop`); applied below with `p` and the explicit
        // `Decidable p` witness from `decEq`.
        let decide_fn = Expr::const_(Name::from_string("decide"), vec![]);

        // instBEqOfDecidableEq type:
        //   {α : Type u} → [inst : DecidableEq α] → BEq α
        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let dec_eq_alpha = Expr::app(dec_eq_alpha_const.clone(), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(dec_eq_alpha.clone());
            let r = Expr::app(beq_const.clone(), alpha.clone());
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, dec_eq_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // instBEqOfDecidableEq value:
        //   λ {α : Type u} [inst : DecidableEq α] =>
        //     BEq.mk α (λ (a b : α) =>
        //       decide (Eq α a b) (decEq α inst a b))
        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let dec_eq_alpha = Expr::app(dec_eq_alpha_const.clone(), alpha.clone());
            let (inst_id, inst) = b.fresh_local(dec_eq_alpha.clone());

            // beq fn : λ (a b : α) => decide (Eq α a b) (decEq α inst a b)
            let beq_fn = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a_var) = c.fresh_local(alpha.clone());
                let (b2_id, b_var) = c.fresh_local(alpha.clone());

                // Eq α a b  :  Prop
                let eq_a_b = Expr::apps(
                    eq_const.clone(),
                    [alpha.clone(), a_var.clone(), b_var.clone()],
                );
                // decEq α inst a b  :  Decidable (Eq α a b)
                let dec_proof = Expr::apps(
                    dec_eq_fn.clone(),
                    [alpha.clone(), inst.clone(), a_var.clone(), b_var.clone()],
                );
                // decide (Eq α a b) (decEq α inst a b)  :  Bool
                let body = Expr::apps(decide_fn.clone(), [eq_a_b, dec_proof]);

                let body = c.mk_lam(b2_id, BinderInfo::Default, alpha.clone(), body);
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body))
            };

            // BEq.mk α beq_fn  :  BEq α
            let body = Expr::apps(beq_mk.clone(), [alpha.clone(), beq_fn]);

            let body = b.mk_lam(inst_id, BinderInfo::InstImplicit, dec_eq_alpha, body);
            let body = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(body)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instBEqOfDecidableEq"),
            level_params: vec![u.clone()],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instBEqOfDecidableEq"),
            class_name: Name::from_string("BEq"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    /// `instBEqOfDecidableEq` is registered as a `Definition` (not an axiom) by
    /// `with_prelude`, and its declared type type-checks via `infer_type` —
    /// proving the closed bridge term is well-formed.
    #[test]
    fn test_beq_of_decidable_eq_type_checks() {
        let env = Environment::with_prelude();

        let name = "instBEqOfDecidableEq";
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{name} must be a Definition, not an Axiom"
        );
        assert!(info.value.is_some(), "{name} must retain its value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![Level::zero()]))
            .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
    }

    /// The axiom closure of `instBEqOfDecidableEq` is EMPTY — no `sorryAx`, no
    /// fake/trusted axiom anywhere in the term. This is the no-fake guard.
    #[test]
    fn test_beq_of_decidable_eq_axiom_closure_empty() {
        let env = Environment::with_prelude();
        let name = "instBEqOfDecidableEq";
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} is registered"));
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            names.is_empty(),
            "{name} must have empty axiom closure, got {names:?}"
        );
    }

    /// The bridge is registered as a `BEq`-class instance so `==` resolves.
    #[test]
    fn test_beq_of_decidable_eq_is_registered_instance() {
        let env = Environment::with_prelude();
        assert!(
            env.is_instance(&Name::from_string("instBEqOfDecidableEq")),
            "instBEqOfDecidableEq must be a registered BEq instance"
        );
    }
}
