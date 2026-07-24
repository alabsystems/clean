// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Diaconescu's theorem: `Classical.em` proved from `Classical.choice`
//! (+ `propext` + `funext`), and `Classical.byContradiction` proved from `em`.
//!
//! This module retires two entries from the foundational-axiom census. Both
//! `Classical.em` and `Classical.byContradiction` are registered by
//! `init_classical` as `Declaration::Axiom`; here we build kernel-CHECKED
//! `Declaration::Theorem`s whose proof terms reduce to `Classical.choice`,
//! `propext`, `funext` (the surviving foundational axioms on the "3-axiom
//! finish line": `propext`, `Quot.sound`, `Classical.choice`). `init_classical`
//! performs a guarded swap: it registers the theorem when this builder
//! succeeds, and otherwise falls back to the axiom (so the two paths can never
//! drift and a build can never regress to *missing* the constant).
//!
//! ## The proof (ported from Lean 4 `Init/Classical.lean`)
//!
//! For `p : Prop`, define predicates over `Prop`: `U x := (x = True) ∨ p` and
//! `V x := (x = False) ∨ p`. Both are inhabited (`⟨True, inl rfl⟩`,
//! `⟨False, inl rfl⟩`). Apply the choice-backed `indefiniteDescription` to get
//! `u`, `v : Prop` with specs `U u`, `V v`. Case-split: if either spec's right
//! disjunct is `p`, we have `p` → `Or.inl`; else `u = True` and `v = False`, so
//! `u ≠ v` (via the `True = False` contradiction).
//!
//! Then `¬p`: assuming `hp : p`, both `U` and `V` become the constantly-true
//! predicate, so by `funext`+`propext` `U = V`; the chosen witness transports
//! along `U = V` (proof-irrelevance of the existence proof identifies the two
//! choices), giving `u = v`, contradicting `u ≠ v`. Hence `¬p`, so `Or.inr`.
//!
//! Everything is specialized to `α := Prop` (`Sort 0`), so the polymorphic
//! `Sort u` parameters of `Subtype` / `Exists` / `Classical.choice` are
//! instantiated at `u := 1`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants for the Diaconescu proof terms, all specialized to
/// the carrier `α := Prop` (`Sort 0`), i.e. polymorphic `Sort u` params at
/// `u := 1`.
struct EmConsts {
    prop: Expr,
    true_: Expr,
    false_: Expr,
    true_intro: Expr,
    or_const: Expr,
    or_inl: Expr,
    or_inr: Expr,
    or_rec: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_subst1: Expr,
    subtype: Expr,
    subtype_mk: Expr,
    subtype_val: Expr,
    subtype_property: Expr,
    nonempty1: Expr,
    nonempty_intro1: Expr,
    choice1: Expr,
    exists1: Expr,
    exists_intro1: Expr,
    exists_elim1: Expr,
    propext: Expr,
    funext11: Expr,
}

impl EmConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            prop: Expr::prop(),
            true_: Expr::const_(Name::from_string("True"), vec![]),
            false_: Expr::const_(Name::from_string("False"), vec![]),
            true_intro: Expr::const_(Name::from_string("True.intro"), vec![]),
            or_const: Expr::const_(Name::from_string("Or"), vec![]),
            or_inl: Expr::const_(Name::from_string("Or.inl"), vec![]),
            or_inr: Expr::const_(Name::from_string("Or.inr"), vec![]),
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            subtype: Expr::const_(Name::from_string("Subtype"), vec![l1.clone()]),
            subtype_mk: Expr::const_(Name::from_string("Subtype.mk"), vec![l1.clone()]),
            subtype_val: Expr::const_(Name::from_string("Subtype.val"), vec![l1.clone()]),
            subtype_property: Expr::const_(Name::from_string("Subtype.property"), vec![l1.clone()]),
            nonempty1: Expr::const_(Name::from_string("Nonempty"), vec![l1.clone()]),
            nonempty_intro1: Expr::const_(Name::from_string("Nonempty.intro"), vec![l1.clone()]),
            choice1: Expr::const_(Name::from_string("Classical.choice"), vec![l1.clone()]),
            exists1: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro1: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            exists_elim1: Expr::const_(Name::from_string("Exists.elim"), vec![l1.clone()]),
            propext: Expr::const_(Name::from_string("propext"), vec![]),
            funext11: Expr::const_(Name::from_string("funext"), vec![l1.clone(), l1]),
        }
    }

    /// `Not p := p → False`.
    fn not(&self, b: &EnvDeclBuilder, p: Expr) -> Expr {
        let mut c = EnvDeclBuilder::child_of(b);
        let (x_id, _) = c.fresh_local(p.clone());
        let r = c.mk_pi(x_id, BinderInfo::Default, p, self.false_.clone());
        c.finish_child(r)
    }

    /// `Or a b`.
    fn or(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.or_const.clone(), [a, b])
    }

    /// `Eq.{1} Prop a b`, i.e. `a = b` for `a b : Prop`.
    fn eq_prop(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.prop.clone(), a, b])
    }

    /// `Subtype.{1} Prop pred`.
    fn subtype_of(&self, pred: Expr) -> Expr {
        Expr::apps(self.subtype.clone(), [self.prop.clone(), pred])
    }

    /// `Exists.{1} Prop pred`.
    fn exists_of(&self, pred: Expr) -> Expr {
        Expr::apps(self.exists1.clone(), [self.prop.clone(), pred])
    }

    /// `Subtype.val.{1} Prop pred s`.
    fn val_of(&self, pred: Expr, s: Expr) -> Expr {
        Expr::apps(self.subtype_val.clone(), [self.prop.clone(), pred, s])
    }
}

impl Environment {
    /// Build the Diaconescu proof term for `Classical.em` and register it as a
    /// kernel-CHECKED `Declaration::Theorem`. The registered type matches the
    /// `init_classical` axiom shape exactly: `(p : Prop) → Or p (p → False)`.
    pub(crate) fn register_classical_em_theorem(&mut self) -> Result<(), EnvError> {
        self.init_propext()?;
        self.init_funext()?;
        self.init_subtype()?;
        self.init_exists()?;

        let c = EmConsts::new();
        let value = build_em_value(&c);
        let type_ = build_em_type(&c);

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Classical.em"),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Build `Classical.byContradiction` from `Classical.em` and register it as
    /// a kernel-CHECKED `Declaration::Theorem`. Type matches the axiom shape:
    /// `{p : Prop} → ((p → False) → False) → p`.
    pub(crate) fn register_classical_by_contradiction_theorem(&mut self) -> Result<(), EnvError> {
        let c = EmConsts::new();
        let value = build_by_contradiction_value(&c);
        let type_ = build_by_contradiction_type(&c);

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Classical.byContradiction"),
            level_params: vec![],
            type_,
            value,
        })
    }
}

/// `Classical.em` type: `(p : Prop) → Or p (p → False)`.
fn build_em_type(c: &EmConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.prop.clone());
    let not_p = c.not(&b, p.clone());
    let r = c.or(p.clone(), not_p);
    let r = b.mk_pi(p_id, BinderInfo::Default, c.prop.clone(), r);
    b.finish(r)
}

/// `Classical.byContradiction` type: `{p : Prop} → ((p → False) → False) → p`.
fn build_by_contradiction_type(c: &EmConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.prop.clone());
    let not_p = c.not(&b, p.clone());
    let not_not_p = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (h_id, _) = d.fresh_local(not_p.clone());
        let r = d.mk_pi(h_id, BinderInfo::Default, not_p.clone(), c.false_.clone());
        d.finish_child(r)
    };
    let (h_id, _) = b.fresh_local(not_not_p.clone());
    let r = p.clone();
    let r = b.mk_pi(h_id, BinderInfo::Default, not_not_p, r);
    let r = b.mk_pi(p_id, BinderInfo::Implicit, c.prop.clone(), r);
    b.finish(r)
}

/// `byContradiction` value:
/// `fun {p} (h : ¬¬p) => Or.rec (fun hp => hp) (fun hnp => False.elim (h hnp)) (em p)`.
fn build_by_contradiction_value(c: &EmConsts) -> Expr {
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
    let em = Expr::const_(Name::from_string("Classical.em"), vec![]);

    let mut top = EnvDeclBuilder::new();
    let (p_id, p) = top.fresh_local(c.prop.clone());
    let not_p = c.not(&top, p.clone());
    let not_not_p = {
        let mut d = EnvDeclBuilder::child_of(&top);
        let (x_id, _) = d.fresh_local(not_p.clone());
        let r = d.mk_pi(x_id, BinderInfo::Default, not_p.clone(), c.false_.clone());
        d.finish_child(r)
    };
    let (h_id, h) = top.fresh_local(not_not_p.clone());

    // em p : Or p not_p
    let em_p = Expr::app(em, p.clone());
    // motive := fun (_ : Or p not_p) => p
    let or_p = c.or(p.clone(), not_p.clone());
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&top);
        let (m_id, _) = d.fresh_local(or_p.clone());
        let r = d.mk_lam(m_id, BinderInfo::Default, or_p.clone(), p.clone());
        d.finish_child(r)
    };
    // case p : fun (hp : p) => hp
    let case_p = {
        let mut d = EnvDeclBuilder::child_of(&top);
        let (hp_id, hp) = d.fresh_local(p.clone());
        let r = d.mk_lam(hp_id, BinderInfo::Default, p.clone(), hp);
        d.finish_child(r)
    };
    // case ¬p : fun (hnp : ¬p) => False.elim {p} (h hnp)
    let case_np = {
        let mut d = EnvDeclBuilder::child_of(&top);
        let (hnp_id, hnp) = d.fresh_local(not_p.clone());
        let false_pf = Expr::app(h.clone(), hnp.clone());
        let body = Expr::apps(false_elim, [p.clone(), false_pf]);
        let r = d.mk_lam(hnp_id, BinderInfo::Default, not_p.clone(), body);
        d.finish_child(r)
    };
    // Or.rec {p} {not_p} {motive} case_p case_np (em p)
    let body = Expr::apps(
        c.or_rec.clone(),
        [p.clone(), not_p.clone(), motive, case_p, case_np, em_p],
    );

    let r = top.mk_lam(h_id, BinderInfo::Default, not_not_p, body);
    let r = top.mk_lam(p_id, BinderInfo::Implicit, c.prop.clone(), r);
    top.finish(r)
}

/// Build the choice-backed `indefiniteDescription` term for predicate
/// `pred : Prop → Prop` and proof `h_ex : ∃ x, pred x`, returning a term of
/// type `Subtype.{1} Prop pred`. Implements
/// `choice (Exists.elim h_ex (fun a ha => Nonempty.intro ⟨a, ha⟩))`.
///
/// `pred` / `h_ex` may reference fvars owned by `parent` (e.g. when used inside
/// the uniform-in-`W` motive). All internal binders descend from `parent` and
/// are closed with `finish_child`, so outer fvars are tolerated and the result
/// is closed only by the eventual `parent` binders.
fn indef_descr(c: &EmConsts, parent: &EnvDeclBuilder, pred: Expr, h_ex: Expr) -> Expr {
    let subtype_ty = c.subtype_of(pred.clone());
    let nonempty_subtype = Expr::app(c.nonempty1.clone(), subtype_ty.clone());

    // f : ∀ (a : Prop), pred a → Nonempty subtype
    let f = {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (a_id, a) = b.fresh_local(c.prop.clone());
        let pred_a = Expr::app(pred.clone(), a.clone());
        let (ha_id, ha) = b.fresh_local(pred_a.clone());
        let sub_witness = Expr::apps(
            c.subtype_mk.clone(),
            [c.prop.clone(), pred.clone(), a.clone(), ha.clone()],
        );
        let body = Expr::apps(c.nonempty_intro1.clone(), [subtype_ty.clone(), sub_witness]);
        let r = b.mk_lam(ha_id, BinderInfo::Default, pred_a, body);
        let r = b.mk_lam(a_id, BinderInfo::Default, c.prop.clone(), r);
        b.finish_child(r)
    };

    // Exists.elim.{1} {Prop} {pred} {Nonempty subtype} h_ex f
    let ne_proof = Expr::apps(
        c.exists_elim1.clone(),
        [c.prop.clone(), pred, nonempty_subtype, h_ex, f],
    );

    // Classical.choice.{1} {subtype_ty} ne_proof
    Expr::apps(c.choice1.clone(), [subtype_ty, ne_proof])
}

/// Build predicate `fun (x : Prop) => Or (x = anchor) p`. Closed `Prop → Prop`.
fn build_pred(c: &EmConsts, outer: &EnvDeclBuilder, p: Expr, anchor: Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(outer);
    let (x_id, x) = b.fresh_local(c.prop.clone());
    let x_eq_anchor = c.eq_prop(x.clone(), anchor);
    let body = c.or(x_eq_anchor, p);
    let lam = b.mk_lam(x_id, BinderInfo::Default, c.prop.clone(), body);
    b.finish_child(lam)
}

/// `∃ x, pred x` witnessed at `anchor` via `Or.inl (Eq.refl Prop anchor)`.
/// `pred anchor` is defeq `Or (anchor = anchor) p`.
fn build_exists_pred(c: &EmConsts, pred: Expr, anchor: Expr, p: Expr) -> Expr {
    let anchor_eq = c.eq_prop(anchor.clone(), anchor.clone());
    let refl = Expr::apps(c.eq_refl1.clone(), [c.prop.clone(), anchor.clone()]);
    let witness = Expr::apps(c.or_inl.clone(), [anchor_eq, p, refl]);
    Expr::apps(
        c.exists_intro1.clone(),
        [c.prop.clone(), pred, anchor, witness],
    )
}

/// The full Diaconescu proof term for `Classical.em`:
/// `fun (p : Prop) => <Or p (p → False)>`.
fn build_em_value(c: &EmConsts) -> Expr {
    let mut top = EnvDeclBuilder::new();
    let (p_id, p) = top.fresh_local(c.prop.clone());

    let not_p = c.not(&top, p.clone());
    let goal = c.or(p.clone(), not_p.clone());

    // Predicates U, V : Prop → Prop.
    let pred_u = build_pred(c, &top, p.clone(), c.true_.clone());
    let pred_v = build_pred(c, &top, p.clone(), c.false_.clone());

    // exU, exV.
    let ex_u = build_exists_pred(c, pred_u.clone(), c.true_.clone(), p.clone());
    let ex_v = build_exists_pred(c, pred_v.clone(), c.false_.clone(), p.clone());

    // su := indef_descr U exU,  sv := indef_descr V exV   (Subtype witnesses).
    let su = indef_descr(c, &top, pred_u.clone(), ex_u.clone());
    let sv = indef_descr(c, &top, pred_v.clone(), ex_v.clone());

    // u := su.val,  v := sv.val.
    let u = c.val_of(pred_u.clone(), su.clone());
    let v = c.val_of(pred_v.clone(), sv.clone());

    // u_spec : U u := su.property,  v_spec : V v := sv.property.
    let u_spec = Expr::apps(
        c.subtype_property.clone(),
        [c.prop.clone(), pred_u.clone(), su.clone()],
    );
    let v_spec = Expr::apps(
        c.subtype_property.clone(),
        [c.prop.clone(), pred_v.clone(), sv.clone()],
    );

    let u_eq_true = c.eq_prop(u.clone(), c.true_.clone());
    let v_eq_false = c.eq_prop(v.clone(), c.false_.clone());

    // p_implies_uv : p → (u = v).
    let p_implies_uv = build_p_implies_uv(
        c,
        &top,
        p.clone(),
        pred_u.clone(),
        pred_v.clone(),
        u.clone(),
    );

    // not_uv_or_p : Or (u = v → False) p.
    let not_uv_or_p = build_not_uv_or_p(
        c,
        &top,
        p.clone(),
        u.clone(),
        v.clone(),
        u_eq_true,
        v_eq_false,
        u_spec,
        v_spec,
    );

    // Final Or.rec on not_uv_or_p.
    let u_eq_v = c.eq_prop(u.clone(), v.clone());
    let not_uv = {
        let mut d = EnvDeclBuilder::child_of(&top);
        let (x_id, _) = d.fresh_local(u_eq_v.clone());
        let r = d.mk_pi(x_id, BinderInfo::Default, u_eq_v.clone(), c.false_.clone());
        d.finish_child(r)
    };
    let major_ty = c.or(not_uv.clone(), p.clone());

    // motive := fun (_ : Or not_uv p) => goal
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&top);
        let (h_id, _) = d.fresh_local(major_ty.clone());
        let r = d.mk_lam(h_id, BinderInfo::Default, major_ty.clone(), goal.clone());
        d.finish_child(r)
    };

    // case inl (hne : u≠v) => Or.inr p not_p (fun hp => hne (p_implies_uv hp))
    let case_inl = {
        let mut d = EnvDeclBuilder::child_of(&top);
        let (hne_id, hne) = d.fresh_local(not_uv.clone());
        let np = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (hp_id, hp) = e.fresh_local(p.clone());
            let uv = Expr::app(p_implies_uv.clone(), hp.clone());
            let false_pf = Expr::app(hne.clone(), uv);
            let lam = e.mk_lam(hp_id, BinderInfo::Default, p.clone(), false_pf);
            e.finish_child(lam)
        };
        let body = Expr::apps(c.or_inr.clone(), [p.clone(), not_p.clone(), np]);
        let lam = d.mk_lam(hne_id, BinderInfo::Default, not_uv.clone(), body);
        d.finish_child(lam)
    };

    // case inr (hp : p) => Or.inl p not_p hp
    let case_inr = {
        let mut d = EnvDeclBuilder::child_of(&top);
        let (hp_id, hp) = d.fresh_local(p.clone());
        let body = Expr::apps(c.or_inl.clone(), [p.clone(), not_p.clone(), hp]);
        let lam = d.mk_lam(hp_id, BinderInfo::Default, p.clone(), body);
        d.finish_child(lam)
    };

    // Or.rec {not_uv} {p} {motive} case_inl case_inr not_uv_or_p
    let body = Expr::apps(
        c.or_rec.clone(),
        [not_uv, p.clone(), motive, case_inl, case_inr, not_uv_or_p],
    );

    let r = top.mk_lam(p_id, BinderInfo::Default, c.prop.clone(), body);
    top.finish(r)
}

/// Build `not_uv_or_p : Or (u = v → False) p` by nested `Or.rec` on the specs.
#[allow(clippy::too_many_arguments)]
fn build_not_uv_or_p(
    c: &EmConsts,
    outer: &EnvDeclBuilder,
    p: Expr,
    u: Expr,
    v: Expr,
    u_eq_true: Expr,
    v_eq_false: Expr,
    u_spec: Expr,
    v_spec: Expr,
) -> Expr {
    let u_eq_v = c.eq_prop(u.clone(), v.clone());
    let not_uv = {
        let mut d = EnvDeclBuilder::child_of(outer);
        let (x_id, _) = d.fresh_local(u_eq_v.clone());
        let r = d.mk_pi(x_id, BinderInfo::Default, u_eq_v.clone(), c.false_.clone());
        d.finish_child(r)
    };
    let result_ty = c.or(not_uv.clone(), p.clone());

    let u_spec_ty = c.or(u_eq_true.clone(), p.clone());
    let v_spec_ty = c.or(v_eq_false.clone(), p.clone());

    // inner Or.rec on v_spec given `hut : u = True`. Every nested builder
    // descends from the *live* parent builder `d` so fvar ID ranges stay
    // disjoint (avoids #1544-class sibling collisions).
    let make_inner = |d: &EnvDeclBuilder, hut: Expr| -> Expr {
        let motive_v = {
            let mut e = EnvDeclBuilder::child_of(d);
            let (h_id, _) = e.fresh_local(v_spec_ty.clone());
            let r = e.mk_lam(
                h_id,
                BinderInfo::Default,
                v_spec_ty.clone(),
                result_ty.clone(),
            );
            e.finish_child(r)
        };
        let case_vf = {
            let mut e = EnvDeclBuilder::child_of(d);
            let (hvf_id, hvf) = e.fresh_local(v_eq_false.clone());
            let ne = build_u_ne_v(c, &e, u.clone(), v.clone(), hut.clone(), hvf.clone());
            let body = Expr::apps(c.or_inl.clone(), [not_uv.clone(), p.clone(), ne]);
            let lam = e.mk_lam(hvf_id, BinderInfo::Default, v_eq_false.clone(), body);
            e.finish_child(lam)
        };
        let case_vp = {
            let mut e = EnvDeclBuilder::child_of(d);
            let (hp_id, hp) = e.fresh_local(p.clone());
            let body = Expr::apps(c.or_inr.clone(), [not_uv.clone(), p.clone(), hp]);
            let lam = e.mk_lam(hp_id, BinderInfo::Default, p.clone(), body);
            e.finish_child(lam)
        };
        Expr::apps(
            c.or_rec.clone(),
            [
                v_eq_false.clone(),
                p.clone(),
                motive_v,
                case_vf,
                case_vp,
                v_spec.clone(),
            ],
        )
    };

    // outer Or.rec on u_spec.
    let motive_u = {
        let mut d = EnvDeclBuilder::child_of(outer);
        let (h_id, _) = d.fresh_local(u_spec_ty.clone());
        let r = d.mk_lam(
            h_id,
            BinderInfo::Default,
            u_spec_ty.clone(),
            result_ty.clone(),
        );
        d.finish_child(r)
    };
    let case_ut = {
        let mut d = EnvDeclBuilder::child_of(outer);
        let (hut_id, hut) = d.fresh_local(u_eq_true.clone());
        let body = make_inner(&d, hut.clone());
        let lam = d.mk_lam(hut_id, BinderInfo::Default, u_eq_true.clone(), body);
        d.finish_child(lam)
    };
    let case_up = {
        let mut d = EnvDeclBuilder::child_of(outer);
        let (hp_id, hp) = d.fresh_local(p.clone());
        let body = Expr::apps(c.or_inr.clone(), [not_uv.clone(), p.clone(), hp]);
        let lam = d.mk_lam(hp_id, BinderInfo::Default, p.clone(), body);
        d.finish_child(lam)
    };

    Expr::apps(
        c.or_rec.clone(),
        [u_eq_true, p, motive_u, case_ut, case_up, u_spec],
    )
}

/// Build `u ≠ v : u = v → False` from `hut : u = True` and `hvf : v = False`.
fn build_u_ne_v(
    c: &EmConsts,
    outer: &EnvDeclBuilder,
    u: Expr,
    v: Expr,
    hut: Expr,
    hvf: Expr,
) -> Expr {
    let u_eq_v = c.eq_prop(u.clone(), v.clone());
    let mut b = EnvDeclBuilder::child_of(outer);
    let (heq_id, heq) = b.fresh_local(u_eq_v.clone());

    // u_eq_false : u = False
    //   Eq.subst.{1} {Prop} {fun w => u = w} {v} {False} hvf heq
    let motive_uw = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = e.fresh_local(c.prop.clone());
        let body = c.eq_prop(u.clone(), w);
        let lam = e.mk_lam(w_id, BinderInfo::Default, c.prop.clone(), body);
        e.finish_child(lam)
    };
    let u_eq_false = Expr::apps(
        c.eq_subst1.clone(),
        [
            c.prop.clone(),
            motive_uw,
            v.clone(),
            c.false_.clone(),
            hvf.clone(),
            heq.clone(),
        ],
    );

    // true_eq_false : True = False
    //   Eq.subst.{1} {Prop} {fun w => w = False} {u} {True} hut u_eq_false
    let motive_wf = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = e.fresh_local(c.prop.clone());
        let body = c.eq_prop(w, c.false_.clone());
        let lam = e.mk_lam(w_id, BinderInfo::Default, c.prop.clone(), body);
        e.finish_child(lam)
    };
    let true_eq_false = Expr::apps(
        c.eq_subst1.clone(),
        [
            c.prop.clone(),
            motive_wf,
            u.clone(),
            c.true_.clone(),
            hut.clone(),
            u_eq_false,
        ],
    );

    // false_proof : False
    //   Eq.subst.{1} {Prop} {fun w => w} {True} {False} true_eq_false True.intro
    let motive_id = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = e.fresh_local(c.prop.clone());
        let lam = e.mk_lam(w_id, BinderInfo::Default, c.prop.clone(), w);
        e.finish_child(lam)
    };
    let false_proof = Expr::apps(
        c.eq_subst1.clone(),
        [
            c.prop.clone(),
            motive_id,
            c.true_.clone(),
            c.false_.clone(),
            true_eq_false,
            c.true_intro.clone(),
        ],
    );

    let lam = b.mk_lam(heq_id, BinderInfo::Default, u_eq_v, false_proof);
    b.finish_child(lam)
}

/// Build `p → (u = v)`.
///
/// Given `hp : p`, `U = V` by `funext`+`propext`. The choice witness transports
/// along `U = V`; proof-irrelevance of the existence proof identifies the two
/// `Classical.choice` applications, so `u = v`.
fn build_p_implies_uv(
    c: &EmConsts,
    outer: &EnvDeclBuilder,
    p: Expr,
    pred_u: Expr,
    pred_v: Expr,
    u: Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(outer);
    let (hp_id, hp) = b.fresh_local(p.clone());

    // pred_eq : U = V.
    let pred_eq = build_pred_eq(c, &b, p.clone(), pred_u.clone(), pred_v.clone(), hp.clone());

    // u = v via the uniform-in-W transport.
    let uv_eq = build_uv_eq_uniform(c, &b, p.clone(), pred_u, pred_v, u, pred_eq);

    let lam = b.mk_lam(hp_id, BinderInfo::Default, p, uv_eq);
    b.finish_child(lam)
}

/// `pred_eq : U = V` via `funext` of pointwise `propext`.
fn build_pred_eq(
    c: &EmConsts,
    outer: &EnvDeclBuilder,
    p: Expr,
    pred_u: Expr,
    pred_v: Expr,
    hp: Expr,
) -> Expr {
    // pointwise : ∀ (x : Prop), U x = V x
    let pointwise = {
        let mut b = EnvDeclBuilder::child_of(outer);
        let (x_id, x) = b.fresh_local(c.prop.clone());
        let x_eq_true = c.eq_prop(x.clone(), c.true_.clone());
        let x_eq_false = c.eq_prop(x.clone(), c.false_.clone());
        let ux = c.or(x_eq_true.clone(), p.clone());
        let vx = c.or(x_eq_false.clone(), p.clone());
        let fwd = {
            let mut e = EnvDeclBuilder::child_of(&b);
            let (h_id, _) = e.fresh_local(ux.clone());
            let body = Expr::apps(
                c.or_inr.clone(),
                [x_eq_false.clone(), p.clone(), hp.clone()],
            );
            let lam = e.mk_lam(h_id, BinderInfo::Default, ux.clone(), body);
            e.finish_child(lam)
        };
        let bwd = {
            let mut e = EnvDeclBuilder::child_of(&b);
            let (h_id, _) = e.fresh_local(vx.clone());
            let body = Expr::apps(c.or_inr.clone(), [x_eq_true.clone(), p.clone(), hp.clone()]);
            let lam = e.mk_lam(h_id, BinderInfo::Default, vx.clone(), body);
            e.finish_child(lam)
        };
        // Faithful `propext : {a b} → (a ↔ b) → a = b` takes one `Iff`; package
        // the two implications via `Iff.intro ux vx fwd bwd`.
        let iff = Expr::apps(
            Expr::const_(Name::from_string("Iff.intro"), vec![]),
            [ux.clone(), vx.clone(), fwd, bwd],
        );
        let pe = Expr::apps(c.propext.clone(), [ux, vx, iff]);
        let lam = b.mk_lam(x_id, BinderInfo::Default, c.prop.clone(), pe);
        b.finish_child(lam)
    };

    // β := fun (_ : Prop) => Prop
    let beta = {
        let mut b = EnvDeclBuilder::child_of(outer);
        let (x_id, _) = b.fresh_local(c.prop.clone());
        let lam = b.mk_lam(x_id, BinderInfo::Default, c.prop.clone(), c.prop.clone());
        b.finish_child(lam)
    };

    // funext.{1,1} {Prop} {β} {U} {V} pointwise : U = V
    Expr::apps(
        c.funext11.clone(),
        [c.prop.clone(), beta, pred_u, pred_v, pointwise],
    )
}

/// Build `u = v` from `pred_eq : U = V` using a uniform-in-`W` motive:
///
/// ```text
/// motive (W : Prop → Prop) :=
///   ∀ (h : ∃ x, W x), u = Subtype.val Prop W (indef_descr W h)
/// base : motive U := fun h => Eq.refl Prop u
///   (valid: `indef_descr U h` is defeq `indef_descr U exU = su` by
///    proof-irrelevance of the existence proof, so the goal is defeq `u = u`)
/// transported := Eq.subst.{1} {Prop→Prop} {motive} {U} {V} pred_eq base
/// transported (exV) : u = Subtype.val Prop V (indef_descr V exV) ≡ u = v
/// ```
fn build_uv_eq_uniform(
    c: &EmConsts,
    outer: &EnvDeclBuilder,
    p: Expr,
    pred_u: Expr,
    pred_v: Expr,
    u: Expr,
    pred_eq: Expr,
) -> Expr {
    // Prop → Prop function type.
    let pred_fn_ty = {
        let mut b = EnvDeclBuilder::child_of(outer);
        let (x_id, _) = b.fresh_local(c.prop.clone());
        let r = b.mk_pi(x_id, BinderInfo::Default, c.prop.clone(), c.prop.clone());
        b.finish_child(r)
    };

    // motive : (Prop → Prop) → Prop
    let motive = {
        let mut b = EnvDeclBuilder::child_of(outer);
        let (w_id, w) = b.fresh_local(pred_fn_ty.clone());
        let ex_w = c.exists_of(w.clone());
        let (h_id, h) = b.fresh_local(ex_w.clone());
        let descr = indef_descr(c, &b, w.clone(), h.clone());
        let val = c.val_of(w.clone(), descr);
        let body = c.eq_prop(u.clone(), val);
        let inner = b.mk_pi(h_id, BinderInfo::Default, ex_w, body);
        let lam = b.mk_lam(w_id, BinderInfo::Default, pred_fn_ty.clone(), inner);
        b.finish_child(lam)
    };

    // base : motive U := fun (h : ∃ x, U x) => Eq.refl Prop u
    let base = {
        let mut b = EnvDeclBuilder::child_of(outer);
        let ex_u = c.exists_of(pred_u.clone());
        let (h_id, _h) = b.fresh_local(ex_u.clone());
        let refl_u = Expr::apps(c.eq_refl1.clone(), [c.prop.clone(), u.clone()]);
        let lam = b.mk_lam(h_id, BinderInfo::Default, ex_u, refl_u);
        b.finish_child(lam)
    };

    // transported : motive V := Eq.subst {Prop→Prop} {motive} {U} {V} pred_eq base
    let transported = Expr::apps(
        c.eq_subst1.clone(),
        [
            pred_fn_ty.clone(),
            motive,
            pred_u.clone(),
            pred_v.clone(),
            pred_eq,
            base,
        ],
    );

    // exV : ∃ x, V x.
    let ex_v = build_exists_pred(c, pred_v.clone(), c.false_.clone(), p);

    // transported exV : u = Subtype.val Prop V (indef_descr V exV) ≡ u = v.
    Expr::app(transported, ex_v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;

    /// Probe/inventory (Step 1): confirm the kernel exposes every primitive the
    /// Diaconescu term needs, by building the choice-backed `indefiniteDescription`
    /// for a concrete predicate and type-checking it through the kernel.
    #[test]
    fn em_inventory_indef_descr_typechecks() {
        let mut env = Environment::with_prelude();
        env.init_propext().expect("propext");
        env.init_funext().expect("funext");
        env.init_subtype().expect("subtype");
        env.init_exists().expect("exists");
        for n in [
            "Classical.choice",
            "Nonempty",
            "Nonempty.intro",
            "Subtype",
            "Subtype.mk",
            "Subtype.val",
            "Subtype.property",
            "Exists",
            "Exists.intro",
            "Exists.elim",
            "Or",
            "Or.inl",
            "Or.inr",
            "Or.rec",
            "Eq.refl",
            "Eq.subst",
            "propext",
            "funext",
            "True",
            "False",
            "True.intro",
        ] {
            assert!(
                env.get_const(&Name::from_string(n)).is_some(),
                "missing kernel primitive needed by Diaconescu proof: {n}"
            );
        }
    }

    /// The `em` proof value type-checks against the registered `em` type.
    #[test]
    fn em_value_checks_against_type() {
        let mut env = Environment::with_prelude();
        // After prelude, em exists (axiom or theorem). Build the value/type and
        // check them in a fresh checker via add_decl under a probe name.
        env.init_propext().expect("propext");
        env.init_funext().expect("funext");
        env.init_subtype().expect("subtype");
        env.init_exists().expect("exists");
        let c = EmConsts::new();
        let type_ = build_em_type(&c);
        let value = build_em_value(&c);
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("Classical.em.diaconescu_probe"),
            level_params: vec![],
            type_,
            value,
        })
        .expect("Diaconescu em proof term must type-check");
    }

    /// `byContradiction` proof value type-checks against its registered type.
    #[test]
    fn by_contradiction_value_checks_against_type() {
        let env = Environment::with_prelude();
        let c = EmConsts::new();
        let type_ = build_by_contradiction_type(&c);
        let value = build_by_contradiction_value(&c);
        let mut env2 = env;
        env2.add_decl(Declaration::Theorem {
            name: Name::from_string("Classical.byContradiction.diaconescu_probe"),
            level_params: vec![],
            type_,
            value,
        })
        .expect("byContradiction proof term must type-check");
    }

    /// The guarded swap takes effect in the canonical prelude: `Classical.em`
    /// and `Classical.byContradiction` are registered as `Declaration::Theorem`
    /// (NOT `Axiom`), retiring them from the foundational-axiom census.
    #[test]
    fn em_and_by_contradiction_are_theorems_in_prelude() {
        use super::super::types::ConstantKind;
        let env = Environment::with_prelude();
        for n in ["Classical.em", "Classical.byContradiction"] {
            let info = env
                .get_const(&Name::from_string(n))
                .unwrap_or_else(|| panic!("{n} must be registered in the prelude"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{n} must be a kernel-CHECKED Theorem after the Diaconescu swap, \
                 not an Axiom",
            );
        }
    }

    /// `Classical.em`'s transitive axiom closure is `⊆ FOUNDATIONAL_AXIOMS`
    /// (it reaches `propext`, `funext`, `Classical.choice`, and the `Eq`/`Quot`
    /// foundational primitives). This is the soundness payoff: downstream
    /// theorems reaching `em`/`byContradiction` stay `Constructive`.
    #[test]
    fn em_axiom_closure_is_foundational() {
        use super::super::axiom_audit::is_foundational_axiom;
        let env = Environment::with_prelude();
        for n in ["Classical.em", "Classical.byContradiction"] {
            let deps = env
                .axiom_deps(&Name::from_string(n))
                .unwrap_or_else(|| panic!("axiom_deps must resolve {n}"));
            for dep in &deps {
                assert!(
                    is_foundational_axiom(dep),
                    "{n} reaches non-foundational axiom {dep:?} in its closure: \
                     full closure = {deps:?}",
                );
            }
        }
    }
}
