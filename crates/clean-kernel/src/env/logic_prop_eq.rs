// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Prop-level simplification equalities: `and_true`, `true_and`, `and_false`,
//! `false_and`, `or_true`, `true_or`, `or_false`, `false_or`, `and_self`,
//! `or_self`.
//!
//! Each lemma is registered as a real `Declaration::Theorem` whose value is a
//! kernel-constructed `propext (Iff.intro fwd bwd)` proof term — NOT an axiom
//! and NOT a `Theorem`-wrapping-`Axiom` restatement. The transitive axiom
//! closure of every lemma is `{propext}` (a FOUNDATIONAL axiom), so the
//! domain-specific axiom count in `data/axiom_audit.json` stays flat.
//!
//! Before this module these names were never registered as kernel
//! `Declaration`s. The simp machinery (`clean-elab` `lemmas_builtin.rs`) gates
//! each Prop-Eq rewrite on `env.get_const(name).is_some()`, so it silently
//! skipped the whole family (`simp` raised `NoProgress` on `(p ∧ True) = p`),
//! and any explicit `:= and_true` reference auto-bound the identifier as an
//! implicit variable and failed the kernel. Registering the family fixes both
//! arms at once.

use super::decl_builder::EnvDeclBuilder;
use super::*;

/// Kernel constants reused when building the `propext`-based proof terms.
struct PropEqConsts {
    prop: Expr,
    and_const: Expr,
    or_const: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    or_inl: Expr,
    or_inr: Expr,
    or_rec: Expr,
    true_const: Expr,
    true_intro: Expr,
    false_const: Expr,
    false_elim: Expr,
    iff_intro: Expr,
    propext: Expr,
    /// `Eq.{1}` — equality at `Prop : Sort 1`.
    eq_const: Expr,
}

impl PropEqConsts {
    fn new() -> Self {
        Self {
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            and_const: Expr::const_(Name::from_string("And"), vec![]),
            or_const: Expr::const_(Name::from_string("Or"), vec![]),
            and_intro: Expr::const_(Name::from_string("And.intro"), vec![]),
            and_left: Expr::const_(Name::from_string("And.left"), vec![]),
            and_right: Expr::const_(Name::from_string("And.right"), vec![]),
            or_inl: Expr::const_(Name::from_string("Or.inl"), vec![]),
            or_inr: Expr::const_(Name::from_string("Or.inr"), vec![]),
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            true_const: Expr::const_(Name::from_string("True"), vec![]),
            true_intro: Expr::const_(Name::from_string("True.intro"), vec![]),
            false_const: Expr::const_(Name::from_string("False"), vec![]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            iff_intro: Expr::const_(Name::from_string("Iff.intro"), vec![]),
            propext: Expr::const_(Name::from_string("propext"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        }
    }

    /// `And l r`
    fn and(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.and_const.clone(), [l, r])
    }
    /// `Or l r`
    fn or(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.or_const.clone(), [l, r])
    }
    /// `@Eq Prop lhs rhs`
    fn eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.prop.clone(), lhs, rhs])
    }
    /// `propext lhs rhs iff`
    fn propext(&self, lhs: Expr, rhs: Expr, iff: Expr) -> Expr {
        Expr::apps(self.propext.clone(), [lhs, rhs, iff])
    }
    /// `Iff.intro lhs rhs fwd bwd`
    fn iff_intro(&self, lhs: Expr, rhs: Expr, fwd: Expr, bwd: Expr) -> Expr {
        Expr::apps(self.iff_intro.clone(), [lhs, rhs, fwd, bwd])
    }
}

impl Environment {
    /// Register the Prop-level simp equalities as real, kernel-checked
    /// `propext`-based theorems.
    ///
    /// Registers: `and_true`, `true_and`, `and_false`, `false_and`, `or_true`,
    /// `true_or`, `or_false`, `false_or`, `and_self`, `or_self`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `And`, `Or` (+`Or.rec`), `Iff`, `True`/`False`, `propext`, `Eq`
    ///           are registerable (this method seeds them via the idempotent
    ///           `init_*` calls below).
    /// ENSURES: On success each lemma resolves via `env.get_const(name)`.
    /// ENSURES: Idempotent — re-invocation is a no-op.
    /// ENSURES: Each lemma's transitive axiom closure is `{propext}` ⊆
    ///          FOUNDATIONAL_AXIOMS; the domain-specific axiom count is
    ///          unchanged.
    pub fn init_prop_eq_lemmas(&mut self) -> Result<(), EnvError> {
        if self.prop_eq_lemmas_init {
            return Ok(());
        }

        // Seed dependencies (all idempotent).
        self.init_eq()?;
        self.init_true_false()?;
        self.init_and()?;
        self.init_or()?;
        self.init_iff()?;
        self.init_propext()?;

        let c = PropEqConsts::new();

        self.register_and_true(&c)?;
        self.register_true_and(&c)?;
        self.register_and_false(&c)?;
        self.register_false_and(&c)?;
        self.register_or_true(&c)?;
        self.register_true_or(&c)?;
        self.register_or_false(&c)?;
        self.register_false_or(&c)?;
        self.register_and_self(&c)?;
        self.register_or_self(&c)?;

        self.prop_eq_lemmas_init = true;
        Ok(())
    }

    /// Register one `∀ (p : Prop), @Eq Prop lhs(p) rhs(p)` lemma whose value is
    /// `fun (p : Prop) => propext lhs rhs (Iff.intro lhs rhs fwd bwd)`.
    ///
    /// `build_lhs_rhs` returns `(lhs, rhs)` from the bound `p`. `build_fwd`/
    /// `build_bwd` each receive `(p, lhs, rhs)` and return the implication proof
    /// term (already a `lhs → rhs` / `rhs → lhs` lambda).
    fn register_prop_eq_lemma(
        &mut self,
        name: &str,
        c: &PropEqConsts,
        build_lhs_rhs: impl Fn(&PropEqConsts, &Expr) -> (Expr, Expr),
        build_fwd: impl Fn(&PropEqConsts, &EnvDeclBuilder, &Expr, &Expr, &Expr) -> Expr,
        build_bwd: impl Fn(&PropEqConsts, &EnvDeclBuilder, &Expr, &Expr, &Expr) -> Expr,
    ) -> Result<(), EnvError> {
        // Type: ∀ (p : Prop), @Eq Prop lhs rhs
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.prop.clone());
            let (lhs, rhs) = build_lhs_rhs(c, &p);
            let body = c.eq(lhs, rhs);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.prop.clone(), body);
            b.finish(e)
        };

        // Value: fun (p : Prop) => propext lhs rhs (Iff.intro lhs rhs fwd bwd)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.prop.clone());
            let (lhs, rhs) = build_lhs_rhs(c, &p);
            let fwd = build_fwd(c, &b, &p, &lhs, &rhs);
            let bwd = build_bwd(c, &b, &p, &lhs, &rhs);
            let iff = c.iff_intro(lhs.clone(), rhs.clone(), fwd, bwd);
            let pe = c.propext(lhs, rhs, iff);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.prop.clone(), pe);
            b.finish(e)
        };

        // SOUNDNESS: Real kernel-checked proof term. `value` is
        // `fun p => propext _ _ (Iff.intro _ _ fwd bwd)` built from the And/Or
        // constructors + Or.rec / False.elim / True.intro. Routed through the
        // normal checked `add_decl`, so the kernel re-verifies the propext
        // proof. Transitive axiom closure = {propext} ⊆ FOUNDATIONAL_AXIOMS;
        // domain-specific axiom count unchanged. NOT an Axiom, NOT unchecked.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `and_true : ∀ (p : Prop), (p ∧ True) = p`
    fn register_and_true(&mut self, c: &PropEqConsts) -> Result<(), EnvError> {
        self.register_prop_eq_lemma(
            "and_true",
            c,
            |c, p| (c.and(p.clone(), c.true_const.clone()), p.clone()),
            // fwd : (p ∧ True) → p := fun h => And.left p True h
            |c, outer, p, lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(lhs.clone());
                let body = Expr::apps(c.and_left.clone(), [p.clone(), c.true_const.clone(), h]);
                let lam = e.mk_lam(h_id, BinderInfo::Default, lhs.clone(), body);
                e.finish_child(lam)
            },
            // bwd : p → (p ∧ True) := fun h => And.intro p True h True.intro
            |c, outer, p, _lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(p.clone());
                let body = Expr::apps(
                    c.and_intro.clone(),
                    [p.clone(), c.true_const.clone(), h, c.true_intro.clone()],
                );
                let lam = e.mk_lam(h_id, BinderInfo::Default, p.clone(), body);
                e.finish_child(lam)
            },
        )
    }

    /// `true_and : ∀ (p : Prop), (True ∧ p) = p`
    fn register_true_and(&mut self, c: &PropEqConsts) -> Result<(), EnvError> {
        self.register_prop_eq_lemma(
            "true_and",
            c,
            |c, p| (c.and(c.true_const.clone(), p.clone()), p.clone()),
            // fwd : (True ∧ p) → p := fun h => And.right True p h
            |c, outer, p, lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(lhs.clone());
                let body = Expr::apps(c.and_right.clone(), [c.true_const.clone(), p.clone(), h]);
                let lam = e.mk_lam(h_id, BinderInfo::Default, lhs.clone(), body);
                e.finish_child(lam)
            },
            // bwd : p → (True ∧ p) := fun h => And.intro True p True.intro h
            |c, outer, p, _lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(p.clone());
                let body = Expr::apps(
                    c.and_intro.clone(),
                    [c.true_const.clone(), p.clone(), c.true_intro.clone(), h],
                );
                let lam = e.mk_lam(h_id, BinderInfo::Default, p.clone(), body);
                e.finish_child(lam)
            },
        )
    }

    /// `and_false : ∀ (p : Prop), (p ∧ False) = False`
    fn register_and_false(&mut self, c: &PropEqConsts) -> Result<(), EnvError> {
        self.register_prop_eq_lemma(
            "and_false",
            c,
            |c, p| {
                (
                    c.and(p.clone(), c.false_const.clone()),
                    c.false_const.clone(),
                )
            },
            // fwd : (p ∧ False) → False := fun h => And.right p False h
            |c, outer, p, lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(lhs.clone());
                let body = Expr::apps(c.and_right.clone(), [p.clone(), c.false_const.clone(), h]);
                let lam = e.mk_lam(h_id, BinderInfo::Default, lhs.clone(), body);
                e.finish_child(lam)
            },
            // bwd : False → (p ∧ False) := fun h => False.elim (p ∧ False) h
            |c, outer, _p, lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(c.false_const.clone());
                let body = Expr::apps(c.false_elim.clone(), [lhs.clone(), h]);
                let lam = e.mk_lam(h_id, BinderInfo::Default, c.false_const.clone(), body);
                e.finish_child(lam)
            },
        )
    }

    /// `false_and : ∀ (p : Prop), (False ∧ p) = False`
    fn register_false_and(&mut self, c: &PropEqConsts) -> Result<(), EnvError> {
        self.register_prop_eq_lemma(
            "false_and",
            c,
            |c, p| {
                (
                    c.and(c.false_const.clone(), p.clone()),
                    c.false_const.clone(),
                )
            },
            // fwd : (False ∧ p) → False := fun h => And.left False p h
            |c, outer, p, lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(lhs.clone());
                let body = Expr::apps(c.and_left.clone(), [c.false_const.clone(), p.clone(), h]);
                let lam = e.mk_lam(h_id, BinderInfo::Default, lhs.clone(), body);
                e.finish_child(lam)
            },
            // bwd : False → (False ∧ p) := fun h => False.elim (False ∧ p) h
            |c, outer, _p, lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(c.false_const.clone());
                let body = Expr::apps(c.false_elim.clone(), [lhs.clone(), h]);
                let lam = e.mk_lam(h_id, BinderInfo::Default, c.false_const.clone(), body);
                e.finish_child(lam)
            },
        )
    }

    /// `or_true : ∀ (p : Prop), (p ∨ True) = True`
    fn register_or_true(&mut self, c: &PropEqConsts) -> Result<(), EnvError> {
        self.register_prop_eq_lemma(
            "or_true",
            c,
            |c, p| (c.or(p.clone(), c.true_const.clone()), c.true_const.clone()),
            // fwd : (p ∨ True) → True := fun _ => True.intro
            |c, outer, _p, lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, _h) = e.fresh_local(lhs.clone());
                let lam = e.mk_lam(h_id, BinderInfo::Default, lhs.clone(), c.true_intro.clone());
                e.finish_child(lam)
            },
            // bwd : True → (p ∨ True) := fun _ => Or.inr p True True.intro
            |c, outer, p, _lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, _h) = e.fresh_local(c.true_const.clone());
                let body = Expr::apps(
                    c.or_inr.clone(),
                    [p.clone(), c.true_const.clone(), c.true_intro.clone()],
                );
                let lam = e.mk_lam(h_id, BinderInfo::Default, c.true_const.clone(), body);
                e.finish_child(lam)
            },
        )
    }

    /// `true_or : ∀ (p : Prop), (True ∨ p) = True`
    fn register_true_or(&mut self, c: &PropEqConsts) -> Result<(), EnvError> {
        self.register_prop_eq_lemma(
            "true_or",
            c,
            |c, p| (c.or(c.true_const.clone(), p.clone()), c.true_const.clone()),
            // fwd : (True ∨ p) → True := fun _ => True.intro
            |c, outer, _p, lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, _h) = e.fresh_local(lhs.clone());
                let lam = e.mk_lam(h_id, BinderInfo::Default, lhs.clone(), c.true_intro.clone());
                e.finish_child(lam)
            },
            // bwd : True → (True ∨ p) := fun _ => Or.inl True p True.intro
            |c, outer, p, _lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, _h) = e.fresh_local(c.true_const.clone());
                let body = Expr::apps(
                    c.or_inl.clone(),
                    [c.true_const.clone(), p.clone(), c.true_intro.clone()],
                );
                let lam = e.mk_lam(h_id, BinderInfo::Default, c.true_const.clone(), body);
                e.finish_child(lam)
            },
        )
    }

    /// `or_false : ∀ (p : Prop), (p ∨ False) = p`
    fn register_or_false(&mut self, c: &PropEqConsts) -> Result<(), EnvError> {
        self.register_prop_eq_lemma(
            "or_false",
            c,
            |c, p| (c.or(p.clone(), c.false_const.clone()), p.clone()),
            // fwd : (p ∨ False) → p :=
            //   fun h => Or.rec (motive := fun _ => p) (fun hp => hp)
            //                   (fun hf => False.elim p hf) h
            |c, outer, p, lhs, _rhs| {
                let mut b = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = b.fresh_local(lhs.clone());
                let motive = mk_const_motive(c, &b, p.clone(), c.false_const.clone(), p.clone());
                // inl : p → p := fun hp => hp
                let inl = {
                    let mut e = EnvDeclBuilder::child_of(&b);
                    let (hp_id, hp) = e.fresh_local(p.clone());
                    let lam = e.mk_lam(hp_id, BinderInfo::Default, p.clone(), hp);
                    e.finish_child(lam)
                };
                // inr : False → p := fun hf => False.elim p hf
                let inr = {
                    let mut e = EnvDeclBuilder::child_of(&b);
                    let (hf_id, hf) = e.fresh_local(c.false_const.clone());
                    let body = Expr::apps(c.false_elim.clone(), [p.clone(), hf]);
                    let lam = e.mk_lam(hf_id, BinderInfo::Default, c.false_const.clone(), body);
                    e.finish_child(lam)
                };
                let body = Expr::apps(
                    c.or_rec.clone(),
                    [p.clone(), c.false_const.clone(), motive, inl, inr, h],
                );
                let lam = b.mk_lam(h_id, BinderInfo::Default, lhs.clone(), body);
                b.finish_child(lam)
            },
            // bwd : p → (p ∨ False) := fun h => Or.inl p False h
            |c, outer, p, _lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(p.clone());
                let body = Expr::apps(c.or_inl.clone(), [p.clone(), c.false_const.clone(), h]);
                let lam = e.mk_lam(h_id, BinderInfo::Default, p.clone(), body);
                e.finish_child(lam)
            },
        )
    }

    /// `false_or : ∀ (p : Prop), (False ∨ p) = p`
    fn register_false_or(&mut self, c: &PropEqConsts) -> Result<(), EnvError> {
        self.register_prop_eq_lemma(
            "false_or",
            c,
            |c, p| (c.or(c.false_const.clone(), p.clone()), p.clone()),
            // fwd : (False ∨ p) → p :=
            //   Or.rec (motive := fun _ => p) (fun hf => False.elim p hf) (fun hp => hp) h
            |c, outer, p, lhs, _rhs| {
                let mut b = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = b.fresh_local(lhs.clone());
                let motive = mk_const_motive(c, &b, c.false_const.clone(), p.clone(), p.clone());
                // inl : False → p  := fun hf => False.elim p hf
                let inl = {
                    let mut e = EnvDeclBuilder::child_of(&b);
                    let (hf_id, hf) = e.fresh_local(c.false_const.clone());
                    let body = Expr::apps(c.false_elim.clone(), [p.clone(), hf]);
                    let lam = e.mk_lam(hf_id, BinderInfo::Default, c.false_const.clone(), body);
                    e.finish_child(lam)
                };
                // inr : p → p := fun hp => hp
                let inr = {
                    let mut e = EnvDeclBuilder::child_of(&b);
                    let (hp_id, hp) = e.fresh_local(p.clone());
                    let lam = e.mk_lam(hp_id, BinderInfo::Default, p.clone(), hp);
                    e.finish_child(lam)
                };
                let body = Expr::apps(
                    c.or_rec.clone(),
                    [c.false_const.clone(), p.clone(), motive, inl, inr, h],
                );
                let lam = b.mk_lam(h_id, BinderInfo::Default, lhs.clone(), body);
                b.finish_child(lam)
            },
            // bwd : p → (False ∨ p) := fun h => Or.inr False p h
            |c, outer, p, _lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(p.clone());
                let body = Expr::apps(c.or_inr.clone(), [c.false_const.clone(), p.clone(), h]);
                let lam = e.mk_lam(h_id, BinderInfo::Default, p.clone(), body);
                e.finish_child(lam)
            },
        )
    }

    /// `and_self : ∀ (p : Prop), (p ∧ p) = p`
    fn register_and_self(&mut self, c: &PropEqConsts) -> Result<(), EnvError> {
        self.register_prop_eq_lemma(
            "and_self",
            c,
            |c, p| (c.and(p.clone(), p.clone()), p.clone()),
            // fwd : (p ∧ p) → p := fun h => And.left p p h
            |c, outer, p, lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(lhs.clone());
                let body = Expr::apps(c.and_left.clone(), [p.clone(), p.clone(), h]);
                let lam = e.mk_lam(h_id, BinderInfo::Default, lhs.clone(), body);
                e.finish_child(lam)
            },
            // bwd : p → (p ∧ p) := fun h => And.intro p p h h
            |c, outer, p, _lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(p.clone());
                let body = Expr::apps(c.and_intro.clone(), [p.clone(), p.clone(), h.clone(), h]);
                let lam = e.mk_lam(h_id, BinderInfo::Default, p.clone(), body);
                e.finish_child(lam)
            },
        )
    }

    /// `or_self : ∀ (p : Prop), (p ∨ p) = p`
    fn register_or_self(&mut self, c: &PropEqConsts) -> Result<(), EnvError> {
        self.register_prop_eq_lemma(
            "or_self",
            c,
            |c, p| (c.or(p.clone(), p.clone()), p.clone()),
            // fwd : (p ∨ p) → p :=
            //   Or.rec (motive := fun _ => p) (fun hp => hp) (fun hp => hp) h
            |c, outer, p, lhs, _rhs| {
                let mut b = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = b.fresh_local(lhs.clone());
                let motive = mk_const_motive(c, &b, p.clone(), p.clone(), p.clone());
                let id_branch = |b: &EnvDeclBuilder| {
                    let mut e = EnvDeclBuilder::child_of(b);
                    let (hp_id, hp) = e.fresh_local(p.clone());
                    let lam = e.mk_lam(hp_id, BinderInfo::Default, p.clone(), hp);
                    e.finish_child(lam)
                };
                let inl = id_branch(&b);
                let inr = id_branch(&b);
                let body = Expr::apps(
                    c.or_rec.clone(),
                    [p.clone(), p.clone(), motive, inl, inr, h],
                );
                let lam = b.mk_lam(h_id, BinderInfo::Default, lhs.clone(), body);
                b.finish_child(lam)
            },
            // bwd : p → (p ∨ p) := fun h => Or.inl p p h
            |c, outer, p, _lhs, _rhs| {
                let mut e = EnvDeclBuilder::child_of(outer);
                let (h_id, h) = e.fresh_local(p.clone());
                let body = Expr::apps(c.or_inl.clone(), [p.clone(), p.clone(), h]);
                let lam = e.mk_lam(h_id, BinderInfo::Default, p.clone(), body);
                e.finish_child(lam)
            },
        )
    }
}

/// `motive := fun (_ : Or a b) => out` — the non-dependent `Or.rec` motive.
fn mk_const_motive(c: &PropEqConsts, outer: &EnvDeclBuilder, a: Expr, b: Expr, out: Expr) -> Expr {
    let mut m = EnvDeclBuilder::child_of(outer);
    let or_ty = c.or(a, b);
    let (h_id, _h) = m.fresh_local(or_ty.clone());
    let lam = m.mk_lam(h_id, BinderInfo::Default, or_ty, out);
    m.finish_child(lam)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;

    const FAMILY: [&str; 10] = [
        "and_true",
        "true_and",
        "and_false",
        "false_and",
        "or_true",
        "true_or",
        "or_false",
        "false_or",
        "and_self",
        "or_self",
    ];

    fn registered() -> Environment {
        let mut env = Environment::new();
        env.init_prop_eq_lemmas().expect("registration");
        // Idempotent re-invocation is a no-op.
        env.init_prop_eq_lemmas()
            .expect("idempotent re-registration");
        env
    }

    /// Every family member is registered as a `Declaration::Theorem` (NOT an
    /// Axiom) and retains its `propext`-based proof value. This is the fix for
    /// the symptom that the whole family returned `None` from `get_const`.
    #[test]
    fn test_prop_eq_family_registered_as_theorems() {
        let env = registered();
        for name in FAMILY {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be a Theorem, not {:?}",
                info.kind
            );
            assert!(
                info.value.is_some(),
                "{name} must retain its proof value (not a body-less Axiom)"
            );
        }
    }

    /// Each lemma's transitive axiom closure is `⊆ {propext}` — propext is a
    /// FOUNDATIONAL axiom, so the domain-specific axiom count is unchanged.
    /// In particular NO domain-specific axiom appears.
    #[test]
    fn test_prop_eq_family_axiom_closure_is_propext_only() {
        let env = registered();
        for name in FAMILY {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered, axiom_deps should be Some"));
            let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            for d in &dep_names {
                assert_eq!(
                    d, "propext",
                    "{name} axiom closure must be ⊆ {{propext}}, found {d:?} (full: {dep_names:?})"
                );
            }
        }
    }

    /// The family is reachable through the full prelude builder (the path the
    /// `clean check` CLI and the simp machinery use), and each lemma's proof
    /// type-checks there (`with_prelude` runs `add_decl` on every one).
    #[test]
    fn test_prop_eq_family_present_in_prelude() {
        let env = Environment::with_prelude();
        for name in FAMILY {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} must resolve in the default prelude env"
            );
        }
    }

    /// The forward proof of `or_false` (and the other Or-eliminating lemmas)
    /// is rooted at `@Or.rec`, ruling out an axiom-wrapping masquerade.
    #[test]
    fn test_or_false_proof_uses_or_rec() {
        use crate::expr::ExprKind;
        let env = registered();
        let info = env
            .get_const(&Name::from_string("or_false"))
            .expect("or_false registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel the outer `fun (p : Prop) =>` binder.
        let body = match value.kind() {
            ExprKind::Lam(_, _, inner) => (**inner).clone(),
            k => panic!("expected outer λ, got {k:?}"),
        };
        // Body is `propext lhs rhs (Iff.intro lhs rhs fwd bwd)`; the fwd arm
        // (4th arg of Iff.intro) is the Or.rec lambda. Just assert Or.rec
        // appears somewhere in the proof spine.
        fn mentions(e: &Expr, name: &str) -> bool {
            match e.kind() {
                ExprKind::Const(n, _) => n.to_string() == name,
                ExprKind::App(f, a) => mentions(f, name) || mentions(a, name),
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    mentions(t, name) || mentions(b, name)
                }
                _ => false,
            }
        }
        assert!(
            mentions(&body, "Or.rec"),
            "or_false forward proof must eliminate via Or.rec"
        );
        assert!(
            mentions(&body, "propext"),
            "or_false proof must be propext-based"
        );
    }
}
