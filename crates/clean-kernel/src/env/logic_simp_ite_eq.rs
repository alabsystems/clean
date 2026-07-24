// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Simp-targeted reflexive/ite equalities: `eq_self`, `ite_true`, `ite_false`.
//!
//! These are real `Declaration::Theorem`s with kernel-constructed proof terms
//! (NO `sorry`, NO axiom). They let `simp` close reflexive-equality and
//! canonical-`ite` goals:
//!
//! ```text
//! eq_self  : {α : Sort u} → (a : α) → @Eq Prop (@Eq α a a) True
//! ite_true : {α : Sort u} → (a b : α) →
//!            @Eq α (@ite α True  instDecidableTrue  a b) a
//! ite_false: {α : Sort u} → (a b : α) →
//!            @Eq α (@ite α False instDecidableFalse a b) b
//! ```
//!
//! Proof terms:
//! - `eq_self`: `propext (@Eq α a a) True (Iff.intro fwd bwd)` where
//!   `fwd := fun _ => True.intro` and `bwd := fun _ => @Eq.refl α a`. Axiom
//!   closure `{propext}` (FOUNDATIONAL).
//! - `ite_true`: `@Eq.refl α a` — the canonical `instDecidableTrue` instance
//!   ι-reduces `@ite α True instDecidableTrue a b` to `a` (the kernel already
//!   reduces this; see `logic_decidable_instances`), so `a = a` closes by refl.
//!   Axiom closure empty.
//! - `ite_false`: dually `@Eq.refl α b`. Axiom closure empty.
//!
//! SOUNDNESS: every value is routed through the checked `add_decl`, so the
//! kernel re-verifies the proof. `ite_true`/`ite_false` are valid ONLY because
//! the kernel genuinely reduces the canonical-instance `ite` to its
//! then/else branch — an over-reduction would make the `Eq.refl` body fail to
//! type-check and `add_decl` would reject the decl. The False variant reduces
//! to the ELSE branch only. NO domain-specific axiom is introduced.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `eq_self`, `ite_true`, `ite_false`. Idempotent; axiom-free
    /// beyond `propext` (FOUNDATIONAL) for `eq_self`.
    pub(crate) fn register_simp_ite_eq_lemmas(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_true_false()?;
        self.init_iff()?;
        self.init_propext()?;
        self.init_decidable()?;
        self.init_ite()?;
        self.init_decidable_true_false()?;

        let is_thm = |env: &Environment, n: &str| {
            env.get_const(&Name::from_string(n))
                .is_some_and(|c| c.kind == super::types::ConstantKind::Theorem)
        };
        if is_thm(self, "eq_self") && is_thm(self, "ite_true") && is_thm(self, "ite_false") {
            return Ok(());
        }

        self.register_eq_self()?;
        self.register_ite_true_false(true)?;
        self.register_ite_true_false(false)?;
        Ok(())
    }

    /// `eq_self.{u} : {α : Sort u} → (a : α) → @Eq Prop (@Eq α a a) True`
    ///
    /// value: `fun {α} (a) => propext (@Eq α a a) True
    ///           (Iff.intro (@Eq α a a) True (fun _ => True.intro)
    ///                                       (fun _ => @Eq.refl α a))`
    fn register_eq_self(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("eq_self"))
            .is_some_and(|c| c.kind == super::types::ConstantKind::Theorem)
        {
            return Ok(());
        }

        let u = Name::from_string("u");
        let lu = Level::param(u.clone());
        let sort_u = Expr::sort(lu.clone());
        let prop = Expr::sort(Level::zero());

        // @Eq.{u} α a a : Prop
        let eq_u = Expr::const_(Name::from_string("Eq"), vec![lu.clone()]);
        let eq_refl_u = Expr::const_(Name::from_string("Eq.refl"), vec![lu.clone()]);
        // @Eq.{1} Prop _ _  (equality at Prop : Sort 1)
        let eq_prop = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let true_c = Expr::const_(Name::from_string("True"), vec![]);
        let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
        let iff_intro = Expr::const_(Name::from_string("Iff.intro"), vec![]);
        let propext = Expr::const_(Name::from_string("propext"), vec![]);

        // Type.
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            // @Eq α a a
            let refl_prop = Expr::apps(eq_u.clone(), [alpha.clone(), a.clone(), a.clone()]);
            // @Eq Prop (@Eq α a a) True
            let concl = Expr::apps(eq_prop.clone(), [prop.clone(), refl_prop, true_c.clone()]);
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), concl);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // Value.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let refl_prop = Expr::apps(eq_u.clone(), [alpha.clone(), a.clone(), a.clone()]);

            // fwd : (@Eq α a a) → True := fun _ => True.intro
            let fwd = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (h_id, _h) = d.fresh_local(refl_prop.clone());
                d.finish_child(d.mk_lam(
                    h_id,
                    BinderInfo::Default,
                    refl_prop.clone(),
                    true_intro.clone(),
                ))
            };
            // bwd : True → (@Eq α a a) := fun _ => @Eq.refl α a
            let bwd = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (h_id, _h) = d.fresh_local(true_c.clone());
                let refl = Expr::apps(eq_refl_u.clone(), [alpha.clone(), a.clone()]);
                d.finish_child(d.mk_lam(h_id, BinderInfo::Default, true_c.clone(), refl))
            };
            // Iff.intro (@Eq α a a) True fwd bwd
            let iff = Expr::apps(
                iff_intro.clone(),
                [refl_prop.clone(), true_c.clone(), fwd, bwd],
            );
            // propext (@Eq α a a) True iff
            let pe = Expr::apps(propext.clone(), [refl_prop, true_c.clone(), iff]);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), pe);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // SOUNDNESS: real kernel-checked `propext`-based proof; routed through
        // `add_decl`, so the kernel re-verifies it. Transitive axiom closure
        // `{propext}` ⊆ FOUNDATIONAL_AXIOMS; domain-specific axiom count
        // unchanged. NOT an Axiom, NOT unchecked.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("eq_self"),
            level_params: vec![u],
            type_,
            value,
        })
    }

    /// `ite_true.{u}  : {α : Sort u} → (a b : α) →
    ///                    @Eq α (@ite α True  instDecidableTrue  a b) a`
    /// `ite_false.{u} : {α : Sort u} → (a b : α) →
    ///                    @Eq α (@ite α False instDecidableFalse a b) b`
    ///
    /// value: `fun {α} (a b) => @Eq.refl α <result>` — the canonical instance
    /// ι-reduces the `ite` to `<result>`, so the goal is `<result> = <result>`.
    fn register_ite_true_false(&mut self, is_true: bool) -> Result<(), EnvError> {
        let name = if is_true { "ite_true" } else { "ite_false" };
        if self
            .get_const(&Name::from_string(name))
            .is_some_and(|c| c.kind == super::types::ConstantKind::Theorem)
        {
            return Ok(());
        }

        let u = Name::from_string("u");
        let lu = Level::param(u.clone());
        let sort_u = Expr::sort(lu.clone());

        let eq_u = Expr::const_(Name::from_string("Eq"), vec![lu.clone()]);
        let eq_refl_u = Expr::const_(Name::from_string("Eq.refl"), vec![lu.clone()]);
        let ite = Expr::const_(Name::from_string("ite"), vec![lu.clone()]);
        let (cond, inst) = if is_true {
            (
                Expr::const_(Name::from_string("True"), vec![]),
                Expr::const_(Name::from_string("instDecidableTrue"), vec![]),
            )
        } else {
            (
                Expr::const_(Name::from_string("False"), vec![]),
                Expr::const_(Name::from_string("instDecidableFalse"), vec![]),
            )
        };

        // Type: {α} → (a b : α) → @Eq α (@ite α cond inst a b) <result>
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (bv_id, bv) = b.fresh_local(alpha.clone());
            let result = if is_true { a.clone() } else { bv.clone() };
            let lhs = Expr::apps(
                ite.clone(),
                [
                    alpha.clone(),
                    cond.clone(),
                    inst.clone(),
                    a.clone(),
                    bv.clone(),
                ],
            );
            let concl = Expr::apps(eq_u.clone(), [alpha.clone(), lhs, result]);
            let r = b.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), concl);
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // Value: fun {α} (a b) => @Eq.refl α <result>
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (bv_id, bv) = b.fresh_local(alpha.clone());
            let result = if is_true { a.clone() } else { bv.clone() };
            let refl = Expr::apps(eq_refl_u.clone(), [alpha.clone(), result]);
            let r = b.mk_lam(bv_id, BinderInfo::Default, alpha.clone(), refl);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // SOUNDNESS: `value` is `@Eq.refl α <result>`. This type-checks against
        // the stated type ONLY because the kernel genuinely ι-reduces
        // `@ite α cond inst a b` to `<result>` (the canonical Decidable
        // instance reduces to `Decidable.isTrue`/`isFalse`). `add_decl`
        // re-verifies the body; an over-reduction would make the refl fail to
        // type-check and the decl would be rejected. Axiom closure empty;
        // domain-specific axiom count unchanged.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![u],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_simp_ite_eq_lemmas_type_check_and_axiom_profile() {
        let mut env = Environment::with_prelude();
        env.register_simp_ite_eq_lemmas().expect("register");
        env.register_simp_ite_eq_lemmas().expect("idempotent");

        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["eq_self", "ite_true", "ite_false"] {
            let n = Name::from_string(name);
            let _ = tc
                .infer_type(&Expr::const_(
                    n.clone(),
                    vec![Level::param(Name::from_string("u"))],
                ))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
            assert_eq!(
                env.get_const(&n).expect("registered").kind,
                ConstantKind::Theorem
            );
        }

        // eq_self axiom closure ⊆ {propext}; ite_true/ite_false are axiom-free.
        for (name, allowed) in [
            ("eq_self", vec!["propext"]),
            ("ite_true", vec![]),
            ("ite_false", vec![]),
        ] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .expect("registered");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            for d in &names {
                assert!(
                    allowed.contains(&d.as_str()),
                    "{name} axiom closure must be ⊆ {allowed:?}, found {d:?} (full {names:?})"
                );
            }
        }
    }

    /// Present through the full prelude builder (the path the CLI + simp use).
    #[test]
    fn test_simp_ite_eq_lemmas_present_in_prelude() {
        let env = Environment::with_prelude();
        for name in ["eq_self", "ite_true", "ite_false"] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} must resolve in the default prelude env"
            );
        }
    }
}
