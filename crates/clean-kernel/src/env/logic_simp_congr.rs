// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `Eq`-concluding members of G39's prelude set (ledger (109)),
//! registered by `logic_simp_iff.rs`'s `register_simp_logic_iff_lemmas`:
//!
//! ```text
//! not_false_eq_true : (¬False) = True
//! not_true_eq_false : (¬True) = False
//! forall_congr.{u}  : {α : Sort u} → {p q : α → Prop} →
//!                     (∀ a, p a = q a) → (∀ a, p a) = (∀ a, q a)
//! implies_true.{u}  : (α : Sort u) → (α → True) = True
//! false_implies    : (p : Prop) → (False → p) = True
//! ne_eq.{u_1}       : {α : Sort u_1} → (a b : α) → (a ≠ b) = ¬(a = b)
//! ```
//!
//! Real kernel-checked theorems; each axiom closure is `{propext}`
//! (FOUNDATIONAL), except `ne_eq`'s, which is empty (`rfl`, as in Lean).

use super::decl_builder::EnvDeclBuilder;
use super::logic_simp_iff::{arrow, iff_intro, konst, not};
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Lean's `implies_true` / `false_implies` (G12). Both equations follow
    /// from an inhabitant of the LHS via `propext`: `fun _ => True.intro`
    /// or `False.elim`. The domain of `implies_true` ranges over `Sort u`,
    /// not just propositions; `false_implies` has a proposition codomain.
    pub(super) fn register_implication_true(&mut self, false_domain: bool) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let prop = Expr::sort(Level::zero());
        let binder_ty = if false_domain {
            prop.clone()
        } else {
            Expr::sort(Level::param(u.clone()))
        };
        let mut b = EnvDeclBuilder::new();
        let (arg_id, arg) = b.fresh_local(binder_ty.clone());
        let (domain, codomain, name) = if false_domain {
            (konst("False"), arg, "false_implies")
        } else {
            (arg, konst("True"), "implies_true")
        };
        let lhs = arrow(domain.clone(), codomain.clone());
        let rhs = konst("True");
        let eq = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [prop, lhs.clone(), rhs.clone()],
        );
        let type_ = b.finish(b.mk_pi(arg_id, BinderInfo::Default, binder_ty.clone(), eq));

        let (x_id, x) = b.fresh_local(domain.clone());
        let inhabitant = if false_domain {
            Expr::apps(
                Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                [codomain, x],
            )
        } else {
            konst("True.intro")
        };
        let inhabitant = b.mk_lam(x_id, BinderInfo::Default, domain, inhabitant);
        let (h_id, _) = b.fresh_local(lhs.clone());
        let mp = b.mk_lam(h_id, BinderInfo::Default, lhs.clone(), konst("True.intro"));
        let (r_id, _) = b.fresh_local(rhs.clone());
        let mpr = b.mk_lam(r_id, BinderInfo::Default, rhs.clone(), inhabitant);
        let iff_proof = iff_intro(lhs.clone(), rhs.clone(), mp, mpr);
        let proof = Expr::apps(konst("propext"), [lhs, rhs, iff_proof]);
        let value = b.finish(b.mk_lam(arg_id, BinderInfo::Default, binder_ty, proof));
        // SOUNDNESS: checked `add_decl`; closure `{propext}` is foundational.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: if false_domain { vec![] } else { vec![u] },
            type_,
            value,
        })
    }

    /// `not_true_eq_false : (¬True) = False` (`value`) and
    /// `not_false_eq_true : (¬False) = True` (`!value`), by `propext`:
    /// `¬True → False` is `fun h => h True.intro`, `¬False` is `fun f => f`.
    pub(super) fn register_not_const_eq(&mut self, value: bool) -> Result<(), EnvError> {
        let (arg, result, name) = if value {
            (konst("True"), konst("False"), "not_true_eq_false")
        } else {
            (konst("False"), konst("True"), "not_false_eq_true")
        };
        let lhs = not(arg.clone());
        let eq_prop = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let type_ = Expr::apps(
            eq_prop,
            [Expr::sort(Level::zero()), lhs.clone(), result.clone()],
        );
        let value_expr = {
            let mut b = EnvDeclBuilder::new();
            let (h_id, h) = b.fresh_local(lhs.clone());
            let (r_id, r) = b.fresh_local(result.clone());
            let (mp, mpr) = if value {
                // mp : ¬True → False := fun h => h True.intro
                // mpr : False → ¬True := fun f => False.elim f
                let mp = b.mk_lam(
                    h_id,
                    BinderInfo::Default,
                    lhs.clone(),
                    Expr::app(h, konst("True.intro")),
                );
                let elim = Expr::apps(
                    Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                    [lhs.clone(), r],
                );
                (
                    mp,
                    b.mk_lam(r_id, BinderInfo::Default, result.clone(), elim),
                )
            } else {
                // mp : ¬False → True := fun _ => True.intro
                // mpr : True → ¬False := fun _ (f : False) => f
                let mp = b.mk_lam(h_id, BinderInfo::Default, lhs.clone(), konst("True.intro"));
                let (f_id, f) = b.fresh_local(konst("False"));
                let inner = b.mk_lam(f_id, BinderInfo::Default, konst("False"), f);
                (
                    mp,
                    b.mk_lam(r_id, BinderInfo::Default, result.clone(), inner),
                )
            };
            let iff_proof = iff_intro(lhs.clone(), result.clone(), mp, mpr);
            b.finish(Expr::apps(konst("propext"), [lhs, result, iff_proof]))
        };
        // SOUNDNESS: checked `add_decl`; axiom closure `{propext}`.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value: value_expr,
        })
    }

    /// `ne_eq.{u_1} : ∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬(a = b)`, Lean
    /// core's `@[simp]` theorem (`Init/SimpLemmas.lean`, both pinned
    /// toolchains; `#print axioms ne_eq`: none). `Ne a b` is reducible to
    /// `¬(a = b)`, so the proof is `Eq.refl (a ≠ b)`, as Lean's `rfl`.
    pub(super) fn register_ne_eq(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u_1");
        let lu = Level::param(u.clone());
        let sort_u = Expr::sort(lu.clone());
        let prop = Expr::sort(Level::zero());
        let mut b = EnvDeclBuilder::new();
        let (al_id, alpha) = b.fresh_local(sort_u.clone());
        let (a_id, a) = b.fresh_local(alpha.clone());
        let (b_id, bv) = b.fresh_local(alpha.clone());
        let ne = Expr::apps(
            Expr::const_(Name::from_string("Ne"), vec![lu.clone()]),
            [alpha.clone(), a.clone(), bv.clone()],
        );
        let eq = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![lu]),
            [alpha.clone(), a, bv],
        );
        let prop_level = vec![Level::succ(Level::zero())];
        let stmt = Expr::apps(
            Expr::const_(Name::from_string("Eq"), prop_level.clone()),
            [prop.clone(), ne.clone(), not(eq)],
        );
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), prop_level),
            [prop, ne],
        );
        let type_ = b.mk_pi(b_id, BinderInfo::Default, alpha.clone(), stmt);
        let type_ = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), type_);
        let type_ = b.finish(b.mk_pi(al_id, BinderInfo::Implicit, sort_u.clone(), type_));
        let value = b.mk_lam(b_id, BinderInfo::Default, alpha.clone(), refl);
        let value = b.mk_lam(a_id, BinderInfo::Default, alpha, value);
        let value = b.finish(b.mk_lam(al_id, BinderInfo::Implicit, sort_u, value));
        // SOUNDNESS: checked `add_decl` (the kernel unfolds the reducible
        // `Ne`); axiom closure empty.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("ne_eq"),
            level_params: vec![u],
            type_,
            value,
        })
    }

    /// `forall_congr.{u} : {α : Sort u} → {p q : α → Prop} →
    ///   (h : ∀ a, p a = q a) → (∀ a, p a) = (∀ a, q a)`, by `propext` over
    /// `Iff.intro (fun hp a => Eq.mp (h a) (hp a)) (fun hq a => Eq.mpr (h a) (hq a))`.
    pub(super) fn register_forall_congr(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let lu = Level::param(u.clone());
        let sort_u = Expr::sort(lu);
        let prop = Expr::sort(Level::zero());
        let eq_prop = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [prop.clone(), l, r],
            )
        };
        // ∀ (x : α), f x  — built through the builder so `x` is abstracted.
        let forall_app = |b: &mut EnvDeclBuilder, alpha: &Expr, f: &Expr| {
            let (x_id, x) = b.fresh_local(alpha.clone());
            b.mk_pi(
                x_id,
                BinderInfo::Default,
                alpha.clone(),
                Expr::app(f.clone(), x),
            )
        };
        let h_ty = |b: &mut EnvDeclBuilder, alpha: &Expr, p: &Expr, q: &Expr| {
            let (x_id, x) = b.fresh_local(alpha.clone());
            let body = eq_prop(Expr::app(p.clone(), x.clone()), Expr::app(q.clone(), x));
            b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), body)
        };
        let pred_ty = |alpha: &Expr| arrow(alpha.clone(), prop.clone());

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (al_id, alpha) = b.fresh_local(sort_u.clone());
            let (p_id, p) = b.fresh_local(pred_ty(&alpha));
            let (q_id, q) = b.fresh_local(pred_ty(&alpha));
            let hty = h_ty(&mut b, &alpha, &p, &q);
            let (h_id, _h) = b.fresh_local(hty.clone());
            let all_p = forall_app(&mut b, &alpha, &p);
            let all_q = forall_app(&mut b, &alpha, &q);
            let concl = eq_prop(all_p, all_q);
            let r = b.mk_pi(h_id, BinderInfo::Default, hty, concl);
            let r = b.mk_pi(q_id, BinderInfo::Implicit, pred_ty(&alpha), r);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, pred_ty(&alpha), r);
            b.finish(b.mk_pi(al_id, BinderInfo::Implicit, sort_u.clone(), r))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (al_id, alpha) = b.fresh_local(sort_u.clone());
            let (p_id, p) = b.fresh_local(pred_ty(&alpha));
            let (q_id, q) = b.fresh_local(pred_ty(&alpha));
            let hty = h_ty(&mut b, &alpha, &p, &q);
            let (h_id, h) = b.fresh_local(hty.clone());
            let all_p = forall_app(&mut b, &alpha, &p);
            let all_q = forall_app(&mut b, &alpha, &q);
            let eq_mp = Expr::const_(Name::from_string("Eq.mp"), vec![Level::zero()]);
            let eq_mpr = Expr::const_(Name::from_string("Eq.mpr"), vec![Level::zero()]);
            // fun (hp : ∀ x, p x) (x : α) => @Eq.mp (p x) (q x) (h x) (hp x)
            let transport = |b: &mut EnvDeclBuilder, from_all: &Expr, op: &Expr| {
                let (hf_id, hf) = b.fresh_local(from_all.clone());
                let (x_id, x) = b.fresh_local(alpha.clone());
                let body = Expr::apps(
                    op.clone(),
                    [
                        Expr::app(p.clone(), x.clone()),
                        Expr::app(q.clone(), x.clone()),
                        Expr::app(h.clone(), x.clone()),
                        Expr::app(hf, x),
                    ],
                );
                let r = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), body);
                b.mk_lam(hf_id, BinderInfo::Default, from_all.clone(), r)
            };
            let mp = transport(&mut b, &all_p, &eq_mp);
            let mpr = transport(&mut b, &all_q, &eq_mpr);
            let iff_proof = iff_intro(all_p.clone(), all_q.clone(), mp, mpr);
            let body = Expr::apps(konst("propext"), [all_p, all_q, iff_proof]);
            let r = b.mk_lam(h_id, BinderInfo::Default, hty, body);
            let r = b.mk_lam(q_id, BinderInfo::Implicit, pred_ty(&alpha), r);
            let r = b.mk_lam(p_id, BinderInfo::Implicit, pred_ty(&alpha), r);
            b.finish(b.mk_lam(al_id, BinderInfo::Implicit, sort_u, r))
        };
        // SOUNDNESS: checked `add_decl`; axiom closure `{propext}`
        // (FOUNDATIONAL); domain-specific axiom count unchanged.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("forall_congr"),
            level_params: vec![u],
            type_,
            value,
        })
    }
}
