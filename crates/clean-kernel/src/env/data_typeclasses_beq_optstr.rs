// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `BEq` instances for `Char`, `String`, and `Option α`.
//!
//! These mirror the parametric `instBEqList` strategy (kernel module
//! `data_typeclasses_beq_list`): a genuine `*.beq` boolean-equality function
//! built from the type's recursor (no axioms, no `sorry`), wrapped in a
//! `BEq.mk` instance and registered with `register_instance` so that
//! structure/enum `deriving BEq` over a `String`, `Option Nat`, etc. field
//! resolves the corresponding `BEq` instead of leaving a fresh meta (the
//! "contains free variables" registration failure).
//!
//! Registers:
//! - `Char.beq : Char → Char → Bool` (compares the underlying `Char.val : Nat`)
//!   and `instBEqChar : BEq Char`.
//! - `String.beq : String → String → Bool` (compares the underlying
//!   `String.data : List Char` via `List.beq` + `instBEqChar`) and
//!   `instBEqString : BEq String`.
//! - `Option.beq : {α} → [BEq α] → Option α → Option α → Bool` (none/none=true,
//!   some/some=`BEq.beq`, else false) and the parametric
//!   `instBEqOption : {α} → [BEq α] → BEq (Option α)`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Char.beq`/`instBEqChar`, `String.beq`/`instBEqString`, and the
    /// parametric `Option.beq`/`instBEqOption`.
    ///
    /// Runs at the tail of `init_beq`, after `init_beq_list` (so `List.beq` and
    /// `instBEqList` are available for the `String` instance). Char/String/Option
    /// inductives plus `Nat.beq`, `Bool`, and `BEq`/`BEq.beq`/`BEq.mk` are all
    /// available by this point; the explicit idempotent `init_*` calls below make
    /// the function safe for standalone `init_beq()` test callers too.
    pub(crate) fn init_beq_optstr(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): `instBEqOption` same-name-collides with the genuine
        // v4.31 derived instance (Init/Core.lean `deriving instance BEq for
        // Option`) with a DIFFERENT value shape (Clean wraps a hand-rolled
        // `Option.beq`, which is itself absent upstream), and the loader's
        // dedup keeps the value-bearing prelude stub — shadowing the genuine
        // instance corpus-wide. In import mode skip the cluster so the
        // genuine derived instance imports. Default lane byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Ensure the underlying inductives exist (idempotent).
        self.init_char()?;
        self.init_string()?;
        self.init_option()?;

        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);

        // ----------------------------------------------------------------
        // Char.beq : Char → Char → Bool
        //   := λ (c1 c2 : Char) => Nat.beq (Char.toNat c1) (Char.toNat c2)
        // (`Char.toNat` — the code-point `Nat` — NOT `Char.val`, which is a
        // `UInt32` under the genuine v4.30 Char shape; carrier-parity P2.)
        // ----------------------------------------------------------------
        let char_const = Expr::const_(Name::from_string("Char"), vec![]);
        let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
        let char_val = Expr::const_(Name::from_string("Char.toNat"), vec![]);

        let char_beq_type = {
            let mut b = EnvDeclBuilder::new();
            let (c1_id, _c1) = b.fresh_local(char_const.clone());
            let (c2_id, _c2) = b.fresh_local(char_const.clone());
            let r = bool_const.clone();
            let r = b.mk_pi(c2_id, BinderInfo::Default, char_const.clone(), r);
            let r = b.mk_pi(c1_id, BinderInfo::Default, char_const.clone(), r);
            b.finish(r)
        };

        let char_beq_value = {
            let mut b = EnvDeclBuilder::new();
            let (c1_id, c1) = b.fresh_local(char_const.clone());
            let (c2_id, c2) = b.fresh_local(char_const.clone());
            // Nat.beq (Char.val c1) (Char.val c2)
            let body = Expr::apps(
                nat_beq.clone(),
                [
                    Expr::app(char_val.clone(), c1),
                    Expr::app(char_val.clone(), c2),
                ],
            );
            let r = b.mk_lam(c2_id, BinderInfo::Default, char_const.clone(), body);
            let r = b.mk_lam(c1_id, BinderInfo::Default, char_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Char.beq"),
            level_params: vec![],
            type_: char_beq_type,
            value: char_beq_value,
            is_reducible: true,
        })?;

        // instBEqChar : BEq Char := BEq.mk Char Char.beq
        let beq_char_type = Expr::app(
            Expr::const_(Name::from_string("BEq"), vec![Level::zero()]),
            char_const.clone(),
        );
        let beq_char_value = Expr::apps(
            Expr::const_(Name::from_string("BEq.mk"), vec![Level::zero()]),
            [
                char_const.clone(),
                Expr::const_(Name::from_string("Char.beq"), vec![]),
            ],
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instBEqChar"),
            level_params: vec![],
            type_: beq_char_type,
            value: beq_char_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instBEqChar"),
            class_name: Name::from_string("BEq"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // ----------------------------------------------------------------
        // String.beq : String → String → Bool
        //   := λ (s1 s2 : String) =>
        //        List.beq.{0} Char instBEqChar (String.data s1) (String.data s2)
        // ----------------------------------------------------------------
        let string_const = Expr::const_(Name::from_string("String"), vec![]);
        let string_data = Expr::const_(Name::from_string("String.data"), vec![]);
        // List.beq.{0} : {α} → [BEq α] → List α → List α → Bool, here α := Char.
        let list_beq_char = Expr::apps(
            Expr::const_(Name::from_string("List.beq"), vec![Level::zero()]),
            [
                char_const.clone(),
                Expr::const_(Name::from_string("instBEqChar"), vec![]),
            ],
        );

        let string_beq_type = {
            let mut b = EnvDeclBuilder::new();
            let (s1_id, _s1) = b.fresh_local(string_const.clone());
            let (s2_id, _s2) = b.fresh_local(string_const.clone());
            let r = bool_const.clone();
            let r = b.mk_pi(s2_id, BinderInfo::Default, string_const.clone(), r);
            let r = b.mk_pi(s1_id, BinderInfo::Default, string_const.clone(), r);
            b.finish(r)
        };

        let string_beq_value = {
            let mut b = EnvDeclBuilder::new();
            let (s1_id, s1) = b.fresh_local(string_const.clone());
            let (s2_id, s2) = b.fresh_local(string_const.clone());
            let body = Expr::apps(
                list_beq_char.clone(),
                [
                    Expr::app(string_data.clone(), s1),
                    Expr::app(string_data.clone(), s2),
                ],
            );
            let r = b.mk_lam(s2_id, BinderInfo::Default, string_const.clone(), body);
            let r = b.mk_lam(s1_id, BinderInfo::Default, string_const.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("String.beq"),
            level_params: vec![],
            type_: string_beq_type,
            value: string_beq_value,
            is_reducible: true,
        })?;

        // instBEqString : BEq String := BEq.mk String String.beq
        let beq_string_type = Expr::app(
            Expr::const_(Name::from_string("BEq"), vec![Level::zero()]),
            string_const.clone(),
        );
        let beq_string_value = Expr::apps(
            Expr::const_(Name::from_string("BEq.mk"), vec![Level::zero()]),
            [
                string_const.clone(),
                Expr::const_(Name::from_string("String.beq"), vec![]),
            ],
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instBEqString"),
            level_params: vec![],
            type_: beq_string_type,
            value: beq_string_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instBEqString"),
            class_name: Name::from_string("BEq"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // ----------------------------------------------------------------
        // Option.beq : {α : Type u} → [inst : BEq α] → Option α → Option α → Bool
        //   := λ {α} [inst] (o1 o2 : Option α) =>
        //        Option.rec.{u+1,u} α (motive := λ _ : Option α => Option α → Bool)
        //          noneCase someCase o1 o2
        // where
        //   noneCase := λ (m2 : Option α) =>
        //                 Option.rec.{1,u} α (λ _ => Bool) Bool.true (λ _ => Bool.false) m2
        //   someCase := λ (a1 : α) =>
        //                 λ (m2 : Option α) =>
        //                   Option.rec.{1,u} α (λ _ => Bool)
        //                     Bool.false
        //                     (λ (a2 : α) => BEq.beq α inst a1 a2)
        //                     m2
        // ----------------------------------------------------------------
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

        let beq_const = Expr::const_(Name::from_string("BEq"), vec![u_level.clone()]);
        let beq_beq = Expr::const_(Name::from_string("BEq.beq"), vec![u_level.clone()]);
        let beq_mk = Expr::const_(Name::from_string("BEq.mk"), vec![u_level.clone()]);

        let option_const = |lvl: Level| Expr::const_(Name::from_string("Option"), vec![lvl]);
        let option_alpha_of =
            |alpha: &Expr| Expr::app(option_const(u_level.clone()), alpha.clone());
        let option_rec = |motive_lvl: Level| {
            Expr::const_(
                Name::from_string("Option.rec"),
                vec![motive_lvl, u_level.clone()],
            )
        };
        // Bool : Sort 1; (Option α → Bool) : Sort (u+1).
        let lvl_bool = Level::succ(Level::zero()); // 1
        let lvl_fn = Level::succ(u_level.clone()); // u + 1

        let option_beq_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let option_alpha = option_alpha_of(&alpha);
            let (inst_id, inst) = b.fresh_local(Expr::app(beq_const.clone(), alpha.clone()));
            let (o1_id, o1) = b.fresh_local(option_alpha.clone());
            let (o2_id, o2) = b.fresh_local(option_alpha.clone());

            // Outer motive: λ (_ : Option α) => (Option α → Bool)
            let outer_motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = c.fresh_local(option_alpha.clone());
                let fn_ty = Expr::pi(
                    BinderInfo::Default,
                    option_alpha.clone(),
                    bool_const.clone(),
                );
                c.finish_child(c.mk_lam(m_id, BinderInfo::Default, option_alpha.clone(), fn_ty))
            };

            // noneCase := λ (m2 : Option α) =>
            //   Option.rec.{1,u} α (λ _ : Option α => Bool)
            //     Bool.true (λ (_a2 : α) => Bool.false) m2
            let none_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m2_id, m2) = c.fresh_local(option_alpha.clone());

                let inner_motive = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (w_id, _w) = d.fresh_local(option_alpha.clone());
                    d.finish_child(d.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        option_alpha.clone(),
                        bool_const.clone(),
                    ))
                };
                // some case for isNone: λ (_a2 : α) => Bool.false
                let inner_some = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (a2_id, _a2) = d.fresh_local(alpha.clone());
                    d.finish_child(d.mk_lam(
                        a2_id,
                        BinderInfo::Default,
                        alpha.clone(),
                        bool_false.clone(),
                    ))
                };
                let rec_app = Expr::apps(
                    option_rec(lvl_bool.clone()),
                    [
                        alpha.clone(),
                        inner_motive,
                        bool_true.clone(),
                        inner_some,
                        m2,
                    ],
                );
                c.finish_child(c.mk_lam(m2_id, BinderInfo::Default, option_alpha.clone(), rec_app))
            };

            // someCase := λ (a1 : α) => λ (m2 : Option α) =>
            //   Option.rec.{1,u} α (λ _ : Option α => Bool)
            //     Bool.false
            //     (λ (a2 : α) => BEq.beq α inst a1 a2)
            //     m2
            let some_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a1_id, a1) = c.fresh_local(alpha.clone());
                let (m2_id, m2) = c.fresh_local(option_alpha.clone());

                let inner_motive = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (w_id, _w) = d.fresh_local(option_alpha.clone());
                    d.finish_child(d.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        option_alpha.clone(),
                        bool_const.clone(),
                    ))
                };
                // inner some: λ (a2 : α) => BEq.beq α inst a1 a2
                let inner_some = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (a2_id, a2) = d.fresh_local(alpha.clone());
                    let head_eq = Expr::apps(
                        beq_beq.clone(),
                        [alpha.clone(), inst.clone(), a1.clone(), a2],
                    );
                    d.finish_child(d.mk_lam(a2_id, BinderInfo::Default, alpha.clone(), head_eq))
                };

                let rec_app = Expr::apps(
                    option_rec(lvl_bool.clone()),
                    [
                        alpha.clone(),
                        inner_motive,
                        bool_false.clone(),
                        inner_some,
                        m2,
                    ],
                );
                let body = c.mk_lam(m2_id, BinderInfo::Default, option_alpha.clone(), rec_app);
                c.finish_child(c.mk_lam(a1_id, BinderInfo::Default, alpha.clone(), body))
            };

            // Option.rec.{u+1,u} α outer_motive none_case some_case o1 : Option α → Bool
            // then applied to o2.
            let outer_rec = Expr::apps(
                option_rec(lvl_fn.clone()),
                [alpha.clone(), outer_motive, none_case, some_case, o1],
            );
            let body = Expr::app(outer_rec, o2);

            let body = b.mk_lam(o2_id, BinderInfo::Default, option_alpha.clone(), body);
            let body = b.mk_lam(o1_id, BinderInfo::Default, option_alpha.clone(), body);
            let body = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(beq_const.clone(), alpha.clone()),
                body,
            );
            let body = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(body)
        };

        // Option.beq type: {α : Type u} → [BEq α] → Option α → Option α → Bool
        let option_beq_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let option_alpha = option_alpha_of(&alpha);
            let (inst_id, _inst) = b.fresh_local(Expr::app(beq_const.clone(), alpha.clone()));
            let (o1_id, _o1) = b.fresh_local(option_alpha.clone());
            let (o2_id, _o2) = b.fresh_local(option_alpha.clone());
            let r = bool_const.clone();
            let r = b.mk_pi(o2_id, BinderInfo::Default, option_alpha.clone(), r);
            let r = b.mk_pi(o1_id, BinderInfo::Default, option_alpha.clone(), r);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(beq_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Option.beq"),
            level_params: vec![u.clone()],
            type_: option_beq_type,
            value: option_beq_value,
            is_reducible: true,
        })?;

        // instBEqOption : {α : Type u} → [BEq α] → BEq (Option α)
        //   := λ {α} [inst] => BEq.mk (Option α) (Option.beq α inst)
        let inst_option_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let option_alpha = option_alpha_of(&alpha);
            let (inst_id, _inst) = b.fresh_local(Expr::app(beq_const.clone(), alpha.clone()));
            let r = Expr::app(beq_const.clone(), option_alpha);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(beq_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let inst_option_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let option_alpha = option_alpha_of(&alpha);
            let (inst_id, inst) = b.fresh_local(Expr::app(beq_const.clone(), alpha.clone()));

            // Option.beq α inst : Option α → Option α → Bool
            let option_beq_applied = Expr::apps(
                Expr::const_(Name::from_string("Option.beq"), vec![u_level.clone()]),
                [alpha.clone(), inst.clone()],
            );
            // BEq.mk (Option α) (Option.beq α inst)
            let body = Expr::apps(beq_mk.clone(), [option_alpha, option_beq_applied]);

            let body = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(beq_const.clone(), alpha.clone()),
                body,
            );
            let body = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(body)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instBEqOption"),
            level_params: vec![u.clone()],
            type_: inst_option_type,
            value: inst_option_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instBEqOption"),
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

    /// Every new `*.beq` function and `instBEq*` instance is registered as a
    /// `Definition` (not an axiom) by `with_prelude`, and its declared type
    /// type-checks via `infer_type` — proving the closed term is well-formed.
    #[test]
    fn test_optstr_beq_and_inst_type_check() {
        let env = Environment::with_prelude();

        // (name, number of universe level params)
        for (name, n_levels) in [
            ("Char.beq", 0usize),
            ("instBEqChar", 0),
            ("String.beq", 0),
            ("instBEqString", 0),
            ("Option.beq", 1),
            ("instBEqOption", 1),
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a Definition, not an Axiom"
            );
            assert!(info.value.is_some(), "{name} must retain its value");

            let levels: Vec<Level> = (0..n_levels).map(|_| Level::zero()).collect();
            let tc = TypeChecker::with_mode(&env, env.mode());
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(name), levels))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        }
    }

    /// The axiom closure of every new decl is EMPTY — no `sorryAx`, no
    /// fake/trusted axiom anywhere in the term. This is the no-fake guard.
    #[test]
    fn test_optstr_beq_axiom_closure_empty() {
        let env = Environment::with_prelude();
        for name in [
            "Char.beq",
            "instBEqChar",
            "String.beq",
            "instBEqString",
            "Option.beq",
            "instBEqOption",
        ] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} is registered"));
            let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                names.is_empty(),
                "{name} must have empty axiom closure, got {names:?}"
            );
        }
    }
}
