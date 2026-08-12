// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Decidable typeclass and Classical axioms
//!
//! This module contains:
//! - Decidable inductive type (Decidable.isFalse, Decidable.isTrue)
//! - Classical axioms (Nonempty, Or, Classical.choice, Classical.em, Classical.byContradiction)
//!
//! Split from logic.rs for #307.

use super::decl_builder::EnvDeclBuilder;
use super::*;

impl Environment {
    /// Initialize Decidable typeclass
    ///
    /// inductive Decidable (p : Prop) : Type where
    ///   | isFalse (h : ¬p) : Decidable p
    ///   | isTrue (h : p) : Decidable p
    ///
    /// This enables constructive decision procedures.
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.has_decidable() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    /// ENSURES: Adds Decidable, Decidable.isFalse, Decidable.isTrue, Decidable.rec
    pub fn init_decidable(&mut self) -> Result<(), EnvError> {
        if self.decidable_init {
            return Ok(());
        }

        // Initialize `True`/`False` FIRST so `Decidable.isFalse` is built with the
        // real `(p → False)` negation type, never the impredicative `∀ q, q`
        // fallback below. Without this, an env that reaches `init_decidable`
        // before `init_true_false` permanently locks in the fallback shape, and a
        // later concrete `Decidable` instance whose `isFalse` branch targets the
        // real `False` (e.g. `Nat.decEq`) fails to type-check. `init_true_false`
        // only depends on `init_eq`, so there is no cycle. (Robustness fix for the
        // call-order hazard; complements the same ordering in `init_decidable_eq`.)
        self.init_true_false()?;

        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))); // Type = Sort 1
        let decidable_const = Expr::const_(Name::from_string("Decidable"), vec![]);

        // Decidable type: Prop → Type
        let decidable_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _) = b.fresh_local(prop.clone());
            let r = type_.clone();
            let r = b.mk_pi(p_id, BinderInfo::Default, prop.clone(), r);
            b.finish(r)
        };

        // Use Const("False") when init_true_false has been called, so that
        // Decidable.isFalse's type references the same False constant that
        // proof terms use. Before init_true_false, fall back to the impredicative
        // encoding ∀(q : Prop), q. Part of #302.
        let false_type = if self.true_false_init {
            Expr::const_(Name::from_string("False"), vec![])
        } else {
            let mut b = EnvDeclBuilder::new();
            let (q_id, q_var) = b.fresh_local(prop.clone());
            let r = b.mk_pi(q_id, BinderInfo::Default, prop.clone(), q_var);
            b.finish(r)
        };

        // Decidable.isFalse : ∀ (p : Prop), (p → False) → Decidable p
        let is_false_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p_var) = b.fresh_local(prop.clone());
            // h : p → False
            let not_p = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(p_var.clone());
                c.mk_pi(x_id, BinderInfo::Default, p_var.clone(), false_type.clone())
            };
            let (h_id, _) = b.fresh_local(not_p.clone());
            let r = Expr::app(decidable_const.clone(), p_var);
            let r = b.mk_pi(h_id, BinderInfo::Default, not_p, r);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        // Decidable.isTrue : ∀ (p : Prop), p → Decidable p
        let is_true_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p_var) = b.fresh_local(prop.clone());
            let (h_id, _) = b.fresh_local(p_var.clone());
            let r = Expr::app(decidable_const.clone(), p_var.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, p_var, r);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        let decidable_decl = InductiveDecl {
            level_params: vec![],
            num_params: 1, // p is the parameter
            types: vec![InductiveType {
                name: Name::from_string("Decidable"),
                type_: decidable_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Decidable.isFalse"),
                        type_: is_false_type,
                    },
                    Constructor {
                        name: Name::from_string("Decidable.isTrue"),
                        type_: is_true_type,
                    },
                ],
            }],
        };

        self.add_inductive(decidable_decl)?;

        // `Decidable.decide (p : Prop) [inst : Decidable p] : Bool`
        //
        // FAITHFUL to Lean (src/Init/Prelude.lean):
        //
        //   @[inline_if_reduce, nospecialize] def Decidable.decide
        //       (p : Prop) [inst : Decidable p] : Bool :=
        //     inst.casesOn (fun _ => false) (fun _ => true)
        //   export Decidable (isTrue isFalse decide)
        //
        // Lean's `decide` is the EXPORT ALIAS of `Decidable.decide`; both return
        // `Bool` via large elimination over the `Decidable p` instance. clean
        // previously registered `Decidable.decide` as a reducible IDENTITY
        // returning `Decidable p` (NOT Bool) and a SEPARATE `decide` constant
        // returning Bool. That shape mismatch made Mathlib bodies that insert the
        // Decidable→Bool coercion (e.g. `decide (n > N)` inside a `Bool &&`) fail
        // with "expected Bool, got Decidable …". This corrects `Decidable.decide`
        // to Lean's Bool-valued `casesOn` form and makes `decide` its alias.
        //
        // SOUNDNESS: this is a shape correction to MATCH Lean exactly, NOT a defeq
        // relaxation. The kernel RE-CHECKS the `Decidable.rec` body below at
        // registration (`add_decl`); the term is axiom-free (mentions only
        // `Decidable`/its rec, `Bool`/`Bool.true`/`Bool.false`, and `False`).
        //
        // Built only when `Bool`/`False` are present (they are during the
        // prelude: `init_bool`/`init_true_false` precede this). Guarded so a
        // minimal env that reaches `init_decidable` without `Bool` simply keeps
        // the legacy `Decidable p` identity form rather than producing an
        // ill-typed term. `decide`'s alias is registered only inside the same
        // guard so it never references a nonexistent Bool-valued head.
        let have_bool = self.get_const(&Name::from_string("Bool")).is_some()
            && self.get_const(&Name::from_string("Bool.true")).is_some()
            && self.get_const(&Name::from_string("Bool.false")).is_some();

        if have_bool && self.true_false_init {
            let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
            let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
            let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
            let false_const = Expr::const_(Name::from_string("False"), vec![]);

            // Type: (p : Prop) → [inst : Decidable p] → Bool
            let decide_bool_type = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p_var) = b.fresh_local(prop.clone());
                let decidable_p = Expr::app(decidable_const.clone(), p_var.clone());
                let (inst_id, _) = b.fresh_local(decidable_p.clone());
                let r = b.mk_pi(
                    inst_id,
                    BinderInfo::InstImplicit,
                    decidable_p,
                    bool_const.clone(),
                );
                let r = b.mk_pi(p_id, BinderInfo::Default, prop.clone(), r);
                b.finish(r)
            };

            // value: fun {p} (inst : Decidable p) =>
            //   @Decidable.rec.{1} p (fun _ => Bool)
            //     (fun (_ : p → False) => Bool.false)   -- isFalse minor
            //     (fun (_ : p)         => Bool.true)    -- isTrue  minor
            //     inst
            let decide_bool_value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p_var) = b.fresh_local(prop.clone());
                let decidable_p = Expr::app(decidable_const.clone(), p_var.clone());
                let (inst_id, inst) = b.fresh_local(decidable_p.clone());

                // motive : Decidable p → Sort 1  ==  fun (_ : Decidable p) => Bool
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (d_id, _d) = c.fresh_local(decidable_p.clone());
                    c.finish_child(c.mk_lam(
                        d_id,
                        BinderInfo::Default,
                        decidable_p.clone(),
                        bool_const.clone(),
                    ))
                };
                // isFalse minor : (h : p → False) => Bool.false
                let minor_false = {
                    let not_p = {
                        let mut d = EnvDeclBuilder::child_of(&b);
                        let (x_id, _) = d.fresh_local(p_var.clone());
                        d.finish_child(d.mk_pi(
                            x_id,
                            BinderInfo::Default,
                            p_var.clone(),
                            false_const.clone(),
                        ))
                    };
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, _) = c.fresh_local(not_p.clone());
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, not_p, bool_false.clone()))
                };
                // isTrue minor : (h : p) => Bool.true
                let minor_true = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, _) = c.fresh_local(p_var.clone());
                    c.finish_child(c.mk_lam(
                        h_id,
                        BinderInfo::Default,
                        p_var.clone(),
                        bool_true.clone(),
                    ))
                };
                // @Decidable.rec.{1} p motive minor_false minor_true inst
                let dec_rec = Expr::const_(
                    Name::from_string("Decidable.rec"),
                    vec![Level::succ(Level::zero())],
                );
                let body = Expr::apps(
                    dec_rec,
                    [p_var.clone(), motive, minor_false, minor_true, inst],
                );
                let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, decidable_p, body);
                let r = b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), r);
                b.finish(r)
            };

            // `Decidable.decide` — the Bool-valued canonical form (Lean's).
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Decidable.decide"),
                level_params: vec![],
                type_: decide_bool_type.clone(),
                value: decide_bool_value,
                is_reducible: true,
            })?;

            // `decide` — the export ALIAS of `Decidable.decide`:
            //   decide := fun {p} (inst : Decidable p) => @Decidable.decide p inst
            // Same type, body is the eta-expanded application of the canonical
            // head. The kernel re-checks it; both delta-unfold to the same
            // casesOn term, so the registered `decide` native reducer
            // (native_reducers_decidable_ext.rs) stays consistent.
            let decide_alias_value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p_var) = b.fresh_local(prop.clone());
                let decidable_p = Expr::app(decidable_const.clone(), p_var.clone());
                let (inst_id, inst) = b.fresh_local(decidable_p.clone());
                let decidable_decide = Expr::const_(Name::from_string("Decidable.decide"), vec![]);
                let body = Expr::apps(decidable_decide, [p_var.clone(), inst]);
                let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, decidable_p, body);
                let r = b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("decide"),
                level_params: vec![],
                type_: decide_bool_type,
                value: decide_alias_value,
                is_reducible: true,
            })?;
        } else {
            // Minimal env without Bool: keep the legacy reducible identity form
            // `Decidable.decide {p} [inst] : Decidable p := inst` so a Bool-free
            // prelude still type-checks. (Bool-valued correctness is only needed
            // once Bool exists, which it always does in the real prelude.)
            let decide_type = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p_var) = b.fresh_local(prop.clone());
                let decidable_p = Expr::app(decidable_const.clone(), p_var.clone());
                let (inst_id, _) = b.fresh_local(decidable_p.clone());
                let r = b.mk_pi(
                    inst_id,
                    BinderInfo::InstImplicit,
                    decidable_p.clone(),
                    decidable_p,
                );
                let r = b.mk_pi(p_id, BinderInfo::Default, prop.clone(), r);
                b.finish(r)
            };
            let decide_value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p_var) = b.fresh_local(prop.clone());
                let decidable_p = Expr::app(decidable_const.clone(), p_var.clone());
                let (inst_id, inst) = b.fresh_local(decidable_p.clone());
                let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, decidable_p, inst);
                let r = b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Decidable.decide"),
                level_params: vec![],
                type_: decide_type,
                value: decide_value,
                is_reducible: true,
            })?;
        }

        self.decidable_init = true;
        Ok(())
    }

    /// Check if Decidable typeclass has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_decidable()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[cfg(test)]
    pub(crate) fn has_decidable(&self) -> bool {
        self.decidable_init
    }

    /// Initialize Classical axioms
    ///
    /// Classical.choice : {α : Sort u} → Nonempty α → α
    /// Classical.em : (p : Prop) → p ∨ ¬p  (excluded middle)
    ///
    /// These axioms enable classical (non-constructive) reasoning.
    ///
    /// # Contract
    ///
    /// REQUIRES: `init_true_false()` called (auto-initialized if not)
    /// ENSURES: On success, `self.has_classical() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    /// ENSURES: Adds Nonempty, Classical.choice, Classical.em, etc.
    pub fn init_classical(&mut self) -> Result<(), EnvError> {
        if self.classical_init {
            return Ok(());
        }

        // Cubical mode is incompatible with classical axioms (#1379).
        // Classical axioms (LEM, Choice) conflict with Cubical Type Theory's
        // computational equality semantics (Path/hcomp/transp/Glue).
        if self.mode == crate::mode::CleanMode::Cubical {
            return Err(crate::mode::ModeError::FeatureNotAvailable {
                current: self.mode,
                feature: "Classical axioms".to_string(),
            }
            .into());
        }

        // Classical logic requires True/False to be initialized first
        if !self.true_false_init {
            self.init_true_false()?;
        }

        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Use the actual False constant, not an impredicative encoding
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        // Nonempty : Sort u → Prop
        let nonempty_const =
            Expr::const_(Name::from_string("Nonempty"), vec![Level::param(u.clone())]);

        let nonempty_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(sort_u.clone());
            let r = prop.clone();
            let r = b.mk_pi(a_id, BinderInfo::Default, sort_u.clone(), r);
            b.finish(r)
        };

        // Nonempty.intro : ∀ (α : Sort u), α → Nonempty α
        let nonempty_intro_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(sort_u.clone());
            let (v_id, _) = b.fresh_local(a_var.clone());
            let r = Expr::app(nonempty_const.clone(), a_var.clone());
            let r = b.mk_pi(v_id, BinderInfo::Default, a_var, r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        let nonempty_decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Nonempty"),
                type_: nonempty_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Nonempty.intro"),
                    type_: nonempty_intro_type,
                }],
            }],
        };

        self.add_inductive(nonempty_decl)?;

        // Classical.choice : {α : Sort u} → Nonempty α → α
        // Classical.choice : {α : Sort u} → Nonempty α → α
        let choice_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(sort_u.clone());
            let ne_a = Expr::app(nonempty_const.clone(), a_var.clone());
            let (h_id, _) = b.fresh_local(ne_a.clone());
            let r = a_var;
            let r = b.mk_pi(h_id, BinderInfo::Default, ne_a, r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Classical.choice"),
            level_params: vec![u.clone()],
            type_: choice_type,
        })?;

        // NOTE: Classical.epsilon is NOT an axiom in Lean 4 — it is a noncomputable def
        // derived from Classical.choice via strongIndefiniteDescription. It will be loaded
        // from .olean imports. Only Classical.choice is a true axiom.

        // Classical.em (excluded middle) requires Or
        self.init_or()?;

        let or_const = Expr::const_(Name::from_string("Or"), vec![]);

        // Classical.em : (p : Prop) → Or p (p → False)
        let em_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p_var) = b.fresh_local(prop.clone());
            // ¬p = p → False
            let not_p = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(p_var.clone());
                c.mk_pi(
                    x_id,
                    BinderInfo::Default,
                    p_var.clone(),
                    false_const.clone(),
                )
            };
            let r = Expr::app(Expr::app(or_const.clone(), p_var), not_p);
            let r = b.mk_pi(p_id, BinderInfo::Default, prop.clone(), r);
            b.finish(r)
        };

        // Guarded swap (Diaconescu's theorem): prefer the kernel-CHECKED
        // `Classical.em` theorem proved from `Classical.choice` + `propext` +
        // `funext` (see `classical_em_proof.rs`). If the proof-term builder or
        // type-check fails for any reason, fall back to the historical axiom so
        // a build can never regress to *missing* the constant. The swap drops
        // `Classical.em` from the foundational-axiom census; its transitive
        // axiom closure is `{propext, funext, Classical.choice}` (all
        // foundational).
        match self.register_classical_em_theorem() {
            Ok(()) => {}
            Err(_) => {
                self.add_decl(Declaration::Axiom {
                    name: Name::from_string("Classical.em"),
                    level_params: vec![],
                    type_: em_type,
                })?;
            }
        }

        // Classical.byContradiction : {p : Prop} → ((p → False) → False) → p
        let by_contradiction_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p_var) = b.fresh_local(prop.clone());
            // (p → False) → False
            let h_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let not_p_inner = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, _) = d.fresh_local(p_var.clone());
                    d.mk_pi(
                        x_id,
                        BinderInfo::Default,
                        p_var.clone(),
                        false_const.clone(),
                    )
                };
                let (np_id, _) = c.fresh_local(not_p_inner.clone());
                c.mk_pi(np_id, BinderInfo::Default, not_p_inner, false_const.clone())
            };
            let (h_id, _) = b.fresh_local(h_ty.clone());
            let r = p_var;
            let r = b.mk_pi(h_id, BinderInfo::Default, h_ty, r);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        // Guarded swap: prefer the kernel-CHECKED `Classical.byContradiction`
        // theorem proved from `Classical.em` (Diaconescu). Falls back to the
        // axiom on any builder/type-check failure. Drops `byContradiction` from
        // the foundational-axiom census; its closure reaches `Classical.em`'s
        // closure `{propext, funext, Classical.choice}`.
        match self.register_classical_by_contradiction_theorem() {
            Ok(()) => {}
            Err(_) => {
                self.add_decl(Declaration::Axiom {
                    name: Name::from_string("Classical.byContradiction"),
                    level_params: vec![],
                    type_: by_contradiction_type,
                })?;
            }
        }

        self.classical_init = true;

        // Upgrade environment mode to Classical if currently in a compatible
        // but weaker mode. Without this, add_decl creates a TypeChecker in
        // Constructive mode even after classical axioms are available, causing
        // ClassicalChoice expressions to be rejected by mode checks before
        // reaching actual type validation (#1335).
        if matches!(
            self.mode,
            crate::mode::CleanMode::Constructive | crate::mode::CleanMode::Impredicative
        ) {
            self.mode = crate::mode::CleanMode::Classical;
        }

        Ok(())
    }

    /// Check if Classical axioms have been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_classical()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[cfg(test)]
    pub(crate) fn has_classical(&self) -> bool {
        self.classical_init
    }
}

#[cfg(test)]
mod decide_bool_tests {
    use super::*;
    use crate::tc::TypeChecker;

    /// The Bool-valued `decide` constant exists in the prelude, type-checks,
    /// and is AXIOM-FREE — its body is genuine large elimination via
    /// `Decidable.rec` and mentions only `Decidable`/`Bool`/`False` (no Axiom).
    /// This is the term the Prop→Bool coercion (Track PP) inserts.
    #[test]
    fn decide_bool_constant_is_axiom_free_and_type_checks() {
        let env = Environment::with_prelude();

        let info = env
            .get_const(&Name::from_string("decide"))
            .expect("`decide` must be registered in the prelude");
        // It is a Definition (data), not an Axiom.
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "`decide` must be a Definition, got {:?}",
            info.kind
        );

        let tc = TypeChecker::new(&env);
        // The declared type must type-check.
        let _ = tc
            .infer_type(&info.type_)
            .expect("`decide` type must type-check");
        // The body must type-check and be def-eq to the declared type.
        let value = info.value.as_ref().expect("`decide` must have a body");
        let inferred = tc.infer_type(value).expect("`decide` body must type-check");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "`decide` body type must be def-eq to its declared type"
        );

        // Axiom-free: empty axiom closure.
        let deps = env
            .axiom_deps(&Name::from_string("decide"))
            .unwrap_or_default();
        assert!(
            deps.is_empty(),
            "`decide` must have an EMPTY axiom closure; deps = {deps:?}"
        );
    }

    /// `Decidable.decide` (the Lean-canonical Bool-valued form) genuinely
    /// dispatches via `Decidable.rec` (real large elimination), not a stub, and
    /// `decide` is its export alias. This is the A3 prelude-shape correction:
    /// clean previously registered `Decidable.decide` as a `Decidable p`-valued
    /// identity; it now matches Lean's `Bool`-valued `casesOn` form.
    #[test]
    fn decide_bool_body_uses_decidable_rec() {
        let env = Environment::with_prelude();

        fn mentions(e: &Expr, target: &str) -> bool {
            match e.kind() {
                ExprKind::Const(n, _) => n.to_string() == target,
                ExprKind::App(f, a) => mentions(f, target) || mentions(a, target),
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    mentions(t, target) || mentions(b, target)
                }
                _ => false,
            }
        }

        // `Decidable.decide` is the canonical Bool-valued form built on
        // `Decidable.rec`.
        let dd = env
            .get_const(&Name::from_string("Decidable.decide"))
            .expect("`Decidable.decide` must be registered in the prelude");
        let dd_value = dd
            .value
            .as_ref()
            .expect("`Decidable.decide` must have a body");
        assert!(
            mentions(dd_value, "Decidable.rec"),
            "`Decidable.decide` body must dispatch via Decidable.rec"
        );
        assert!(
            mentions(dd_value, "Bool.true") && mentions(dd_value, "Bool.false"),
            "`Decidable.decide` body must produce Bool.true / Bool.false"
        );

        // `Decidable.decide`'s declared RETURN type is `Bool` (A3): the result of
        // applying it is `Bool`, never `Decidable p`. Confirm via the head of the
        // codomain — the type is `{p} → [Decidable p] → Bool`.
        let tc = TypeChecker::new(&env);
        let _ = tc
            .infer_type(&dd.type_)
            .expect("`Decidable.decide` type must type-check");
        assert!(
            mentions(&dd.type_, "Bool"),
            "`Decidable.decide` declared type must mention Bool (Bool-valued)"
        );

        // `decide` is the export alias of `Decidable.decide`.
        let de = env.get_const(&Name::from_string("decide")).unwrap();
        let de_value = de.value.as_ref().unwrap();
        assert!(
            mentions(de_value, "Decidable.decide"),
            "`decide` body must be the alias `@Decidable.decide p inst`"
        );
        assert!(
            mentions(&de.type_, "Bool"),
            "`decide` declared type must mention Bool (Bool-valued)"
        );
    }

    /// `Decidable.decide` is axiom-free and type-checks (the A3 canonical form).
    #[test]
    fn decidable_decide_is_bool_valued_and_axiom_free() {
        let env = Environment::with_prelude();
        let info = env
            .get_const(&Name::from_string("Decidable.decide"))
            .expect("`Decidable.decide` must be registered in the prelude");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "`Decidable.decide` must be a Definition, got {:?}",
            info.kind
        );
        let tc = TypeChecker::new(&env);
        let value = info
            .value
            .as_ref()
            .expect("`Decidable.decide` must have a body");
        let inferred = tc
            .infer_type(value)
            .expect("`Decidable.decide` body must type-check");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "`Decidable.decide` body type must be def-eq to its declared type"
        );
        let deps = env
            .axiom_deps(&Name::from_string("Decidable.decide"))
            .unwrap_or_default();
        assert!(
            deps.is_empty(),
            "`Decidable.decide` must have an EMPTY axiom closure; deps = {deps:?}"
        );
    }
}
