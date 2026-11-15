// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.8.0 core's `Inhabited` / `Nonempty` instances that `default`,
//! `deriving Inhabited` and `deriving Nonempty` need and the builtin prelude
//! lacked (trust-ir gaps G57, ledger class (127), and the substrate of G43 /
//! G55, classes (113) / (125)).
//!
//! Each is declared exactly as the pinned toolchain prints it (`set_option
//! pp.all true`, `#print`), with Lean's priority 1000
//! (`getInstancePriority?`); Lean marks none of them `@[reducible]`
//! (`getReducibilityStatus`: `semireducible`), and neither does this module:
//!
//! ```text
//! def instInhabitedExcept.{u, v} : {ε : Type u} → {α : Type v} →
//!     [inst : Inhabited.{u + 1} ε] → Inhabited.{max (v + 1) (u + 1)} (Except.{u, v} ε α) :=
//!   fun {ε} {α} [inst] => @Inhabited.mk.{max (u + 1) (v + 1)} (Except.{u, v} ε α)
//!     (@Except.error.{u, v} ε α (@Inhabited.default.{u + 1} ε inst))
//!
//! def instInhabitedOfMonad.{u, v} : {α : Type u} → {m : Type u → Type v} →
//!     [inst : Monad.{u, v} m] → [inst : Inhabited.{u + 1} α] → Inhabited.{v + 1} (m α) :=
//!   fun {α} {m} [inst] [inst_1] => @Inhabited.mk.{v + 1} (m α)
//!     (@Pure.pure.{u, v} m (@Applicative.toPure.{u, v} m (@Monad.toApplicative.{u, v} m inst)) α
//!       (@Inhabited.default.{u + 1} α inst_1))
//!
//! def String.instInhabited : Inhabited.{1} String := @Inhabited.mk.{1} String ""
//!
//! def instNonemptyOfInhabited.{u} : ∀ {α : Sort u} [inst : Inhabited.{u} α], Nonempty.{u} α :=
//!   fun {α} [inst] => @Nonempty.intro.{u} α (@Inhabited.default.{u} α inst)
//!
//! noncomputable def Classical.ofNonempty.{u} : {α : Sort u} → [inst : Nonempty.{u} α] → α :=
//!   fun {α} [inst] => @Classical.choice.{u} α (@Classical.ofNonempty.proof_1.{u} α inst)
//! ```
//!
//! `Classical.ofNonempty.proof_1` is Lean's auxiliary theorem `∀ {α} [inst :
//! Nonempty α], Nonempty α`; its Lean proof is `@inferInstance (Nonempty α)
//! inst`, which δ-reduces to the `inst` used here (the builtin prelude has no
//! `inferInstance`, and a theorem's proof is irrelevant). Lean declares
//! `Nonempty` a `class inductive`; it is registered as a class here so its
//! one instance is found.
//!
//! Everything is a kernel-checked definition or theorem. The only axiom
//! reached is the foundational `Classical.choice`, through
//! `Classical.ofNonempty` — as in Lean (`#print axioms Classical.ofNonempty`:
//! `[Classical.choice]`). In `CleanMode::Cubical`, which has no classical
//! axioms, the two classical declarations are skipped.

use crate::env::data_monad_classes::monad_inst;
use crate::env::monad_term::{cst, lparam, monad_kind, type_at, Tele};
use crate::env::{
    Declaration, EnvError, Environment, KernelClassInfo, KernelInstanceInfo,
    LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Declare and register the instances of the module doc. Requires
    /// `Inhabited`, `String`, `Nonempty`, the two-universe `Except` and the
    /// `Monad` class.
    pub(crate) fn init_inhabited_core_instances(&mut self) -> Result<(), EnvError> {
        let (u, v) = (lparam("u"), lparam("v"));
        let su = Level::succ(u.clone());
        let sv = Level::succ(v.clone());
        let inhabited =
            |l: &Level, ty: Expr| Expr::app(cst("Inhabited", std::slice::from_ref(l)), ty);
        let default = |l: &Level, ty: Expr, inst: Expr| {
            Expr::apps(
                cst("Inhabited.default", std::slice::from_ref(l)),
                [ty, inst],
            )
        };
        let lps = |names: &[&str]| names.iter().map(|n| Name::from_string(n)).collect();

        // instInhabitedExcept
        {
            let mut t = Tele::new();
            let e = t.imp(type_at(&u));
            let a = t.imp(type_at(&v));
            let inst = t.inst(inhabited(&su, e.clone()));
            let except = Expr::apps(
                cst("Except", &[u.clone(), v.clone()]),
                [e.clone(), a.clone()],
            );
            let ty = inhabited(&Level::max(sv.clone(), su.clone()), except.clone());
            let err = Expr::apps(
                cst("Except.error", &[u.clone(), v.clone()]),
                [e.clone(), a, default(&su, e, inst)],
            );
            let val = Expr::apps(
                cst("Inhabited.mk", &[Level::max(su.clone(), sv.clone())]),
                [except, err],
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instInhabitedExcept"),
                level_params: lps(&["u", "v"]),
                type_: t.pi(ty),
                value: t.lam(val),
                is_reducible: false,
            })?;
        }

        // instInhabitedOfMonad
        {
            let mut t = Tele::new();
            let a = t.imp(type_at(&u));
            let m = t.imp(monad_kind(&u, &v));
            let monad = t.inst(Expr::app(cst("Monad", &[u.clone(), v.clone()]), m.clone()));
            let inst = t.inst(inhabited(&su, a.clone()));
            let ma = Expr::app(m.clone(), a.clone());
            let ty = inhabited(&sv, ma.clone());
            let mi = monad_inst(&u, &v, &m, &monad);
            let val = Expr::apps(
                cst("Inhabited.mk", std::slice::from_ref(&sv)),
                [ma, mi.pure(a.clone(), default(&su, a, inst))],
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instInhabitedOfMonad"),
                level_params: lps(&["u", "v"]),
                type_: t.pi(ty),
                value: t.lam(val),
                is_reducible: false,
            })?;
        }

        // String.instInhabited
        {
            let one = Level::succ(Level::zero());
            let string = cst("String", &[]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("String.instInhabited"),
                level_params: vec![],
                type_: inhabited(&one, string.clone()),
                value: Expr::apps(
                    cst("Inhabited.mk", std::slice::from_ref(&one)),
                    [string, Expr::str_lit("")],
                ),
                is_reducible: false,
            })?;
        }

        for name in [
            "instInhabitedExcept",
            "instInhabitedOfMonad",
            "String.instInhabited",
        ] {
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string(name),
                class_name: Name::from_string("Inhabited"),
                priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        Ok(())
    }

    /// `Nonempty` as a class, `instNonemptyOfInhabited`, and
    /// `Classical.ofNonempty` (module doc). Requires `Inhabited` and the
    /// classical block (`init_classical`, which declares `Nonempty`).
    pub(crate) fn init_nonempty_core_instances(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Nonempty")).is_none() {
            return Ok(());
        }
        let u = lparam("u");
        let sort_u = Expr::sort(u.clone());
        let nonempty = |ty: Expr| Expr::app(cst("Nonempty", std::slice::from_ref(&u)), ty);
        let nonempty_name = Name::from_string("Nonempty");
        if !self.is_class(&nonempty_name) {
            self.register_class(KernelClassInfo {
                name: nonempty_name.clone(),
                num_params: 1,
                out_params: vec![],
                semi_out_params: vec![],
            });
        }

        // instNonemptyOfInhabited
        {
            let mut t = Tele::new();
            let a = t.imp(sort_u.clone());
            let inst = t.inst(Expr::app(
                cst("Inhabited", std::slice::from_ref(&u)),
                a.clone(),
            ));
            let val = Expr::apps(
                cst("Nonempty.intro", std::slice::from_ref(&u)),
                [
                    a.clone(),
                    Expr::apps(
                        cst("Inhabited.default", std::slice::from_ref(&u)),
                        [a.clone(), inst],
                    ),
                ],
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instNonemptyOfInhabited"),
                level_params: vec![Name::from_string("u")],
                type_: t.pi(nonempty(a)),
                value: t.lam(val),
                is_reducible: false,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instNonemptyOfInhabited"),
                class_name: nonempty_name,
                priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        // Classical.ofNonempty (and its proof_1), only where the classical
        // axiom exists (not in cubical mode).
        if self
            .get_const(&Name::from_string("Classical.choice"))
            .is_none()
        {
            return Ok(());
        }
        {
            let mut t = Tele::new();
            let a = t.imp(sort_u.clone());
            let inst = t.inst(nonempty(a.clone()));
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Classical.ofNonempty.proof_1"),
                level_params: vec![Name::from_string("u")],
                type_: t.pi(nonempty(a)),
                value: t.lam(inst),
            })?;
        }
        {
            let mut t = Tele::new();
            let a = t.imp(sort_u);
            let inst = t.inst(nonempty(a.clone()));
            let proof = Expr::apps(
                cst("Classical.ofNonempty.proof_1", std::slice::from_ref(&u)),
                [a.clone(), inst],
            );
            let val = Expr::apps(
                cst("Classical.choice", std::slice::from_ref(&u)),
                [a.clone(), proof],
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Classical.ofNonempty"),
                level_params: vec![Name::from_string("u")],
                type_: t.pi(a),
                value: t.lam(val),
                is_reducible: false,
            })?;
            // Lean's `noncomputable def Classical.ofNonempty`: it has no code,
            // so a compiled definition or `#eval` that uses it is refused
            // (review r6, X1; docs/DECISIONS.md R134).
            self.mark_noncomputable(Name::from_string("Classical.ofNonempty"));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::env::Environment;
    use crate::expr::Expr;
    use crate::level::Level;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn c(name: &str, levels: Vec<Level>) -> Expr {
        Expr::const_(Name::from_string(name), levels)
    }

    /// G57: the instances are registered, with Lean's universe arity.
    #[test]
    fn test_inhabited_core_instances_are_registered() {
        let env = Environment::try_with_prelude().expect("default prelude");
        for (name, class, arity) in [
            ("instInhabitedExcept", "Inhabited", 2),
            ("instInhabitedOfMonad", "Inhabited", 2),
            ("String.instInhabited", "Inhabited", 0),
            ("instNonemptyOfInhabited", "Nonempty", 1),
        ] {
            let ci = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("`{name}` must be declared"));
            assert_eq!(ci.level_params.len(), arity, "`{name}` universe arity");
            assert!(
                env.get_class_instances(&Name::from_string(class))
                    .iter()
                    .any(|i| i.name == Name::from_string(name)),
                "`{name}` must be a registered `{class}` instance"
            );
        }
        assert!(env
            .get_const(&Name::from_string("Classical.ofNonempty"))
            .is_some());
    }

    /// Review r6, X1: Lean declares `noncomputable def Classical.ofNonempty`;
    /// Clean's prelude carries the same mark, which the front door's
    /// computability check and `#eval` read.
    #[test]
    fn test_of_nonempty_is_marked_noncomputable() {
        let env = Environment::try_with_prelude().expect("default prelude");
        assert!(env.is_noncomputable(&Name::from_string("Classical.ofNonempty")));
    }

    /// G57: `default : Except String Nat` is `.error ""` by definitional
    /// unfolding (Lean 4.8.0's `instInhabitedExcept`), never `.ok 0`.
    #[test]
    fn test_inhabited_except_default_is_error_of_default() {
        let env = Environment::try_with_prelude().expect("default prelude");
        let z = Level::zero();
        let one = Level::succ(Level::zero());
        let string = c("String", vec![]);
        let nat = c("Nat", vec![]);
        let inst = Expr::apps(
            c("instInhabitedExcept", vec![z.clone(), z.clone()]),
            [
                string.clone(),
                nat.clone(),
                c("String.instInhabited", vec![]),
            ],
        );
        let except = Expr::apps(
            c("Except", vec![z.clone(), z.clone()]),
            [string.clone(), nat.clone()],
        );
        let dflt = Expr::apps(c("Inhabited.default", vec![one]), [except, inst]);
        let error_empty = Expr::apps(
            c("Except.error", vec![z.clone(), z.clone()]),
            [string.clone(), nat.clone(), Expr::str_lit("")],
        );
        let ok_zero = Expr::apps(
            c("Except.ok", vec![z.clone(), z]),
            [string, nat, Expr::nat_lit(0)],
        );
        let tc = TypeChecker::new(&env);
        assert!(
            tc.is_def_eq(&dflt, &error_empty),
            "default must be `.error \"\"`"
        );
        assert!(
            !tc.is_def_eq(&dflt, &ok_zero),
            "default must never be `.ok 0`"
        );
    }
}
