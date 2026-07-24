// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! List permutation (`List.Perm`) initialization.
//!
//! `List.Perm` is the canonical Lean 4 inductive relation witnessing that two
//! lists are permutations of one another:
//!
//! ```text
//! inductive List.Perm : List α → List α → Prop
//!   | nil   : Perm [] []
//!   | cons  (x : α) : Perm l₁ l₂ → Perm (x :: l₁) (x :: l₂)
//!   | swap  (x y : α) (l : List α) : Perm (y :: x :: l) (x :: y :: l)
//!   | trans : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃
//! ```
//!
//! `List.Perm` has `num_params = 1` (the element type `α`) and TWO indices,
//! both of type `List α`, that reference the parameter. This is the smallest
//! prelude inductive exercising the multi-index recursor scheme: the generated
//! `List.Perm.rec` motive abstracts both `List α` index domains. Registering
//! it here pins that the recursor type is well-formed.
//!
//! `List.Perm.refl` and `List.Perm.symm` are derived constructively (via
//! `List.rec` and `List.Perm.rec` respectively); their transitive axiom
//! closure is empty.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize `List.Perm` (the permutation relation) and the constructive
    /// lemmas `List.Perm.refl` and `List.Perm.symm`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.list_perm_init == true`
    /// ENSURES: On success, `List`, `List.Perm`, its four constructors,
    ///          `List.Perm.rec`, `List.Perm.refl`, and `List.Perm.symm` are
    ///          registered
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without
    ///          duplication
    pub fn init_list_perm(&mut self) -> Result<(), EnvError> {
        if self.list_perm_init {
            return Ok(());
        }

        // `List` provides the inductive, its constructors, and `List.rec`.
        self.init_list()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u_level.clone()]);
        let list_cons = Expr::const_(Name::from_string("List.cons"), vec![u_level.clone()]);
        let perm_const = Expr::const_(Name::from_string("List.Perm"), vec![u_level.clone()]);

        // `List α`
        let list_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
        // `@List.nil α`, `@List.cons α x l`
        let nil_of = |a: &Expr| Expr::app(list_nil.clone(), a.clone());
        let cons_of = |a: &Expr, x: Expr, l: Expr| Expr::apps(list_cons.clone(), [a.clone(), x, l]);
        // `@List.Perm α l₁ l₂`
        let perm =
            |a: &Expr, l1: Expr, l2: Expr| Expr::apps(perm_const.clone(), [a.clone(), l1, l2]);

        // ── List.Perm : {α : Type u} → List α → List α → Prop ────────────────
        // num_params = 1 (α); the two trailing `List α` arguments are indices.
        let perm_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (l1_id, _l1) = b.fresh_local(list_of(&alpha));
            let (l2_id, _l2) = b.fresh_local(list_of(&alpha));
            let e = prop.clone();
            let e = b.mk_pi(l2_id, BinderInfo::Default, list_of(&alpha), e);
            let e = b.mk_pi(l1_id, BinderInfo::Default, list_of(&alpha), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // ── List.Perm.nil : {α} → Perm α [] [] ───────────────────────────────
        let nil_ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let concl = perm(&alpha, nil_of(&alpha), nil_of(&alpha));
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), concl);
            b.finish(e)
        };

        // ── List.Perm.cons :
        //      {α} → (x : α) → {l₁ l₂ : List α} → Perm α l₁ l₂
        //          → Perm α (x :: l₁) (x :: l₂) ───────────────────────────────
        // FIDELITY (residual-to-zero campaign, 2026-07-02): the element `x`
        // comes FIRST, matching Batteries/Lean 4.8's genuine constructor
        // (`#print List.Perm`: `cons (x : α) {l₁ l₂ : List α}`). The previous
        // stub put the lists first (`{l₁}{l₂}(x)`), so the shadowed import made
        // every real Mathlib positional application
        // `@List.Perm.cons α (l.get i) …` bind the WRONG binders and fail with
        // `expected List α, got α` (the List.erase_get type_mismatch).
        let cons_ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (l1_id, l1) = b.fresh_local(list_of(&alpha));
            let (l2_id, l2) = b.fresh_local(list_of(&alpha));
            let (h_id, _h) = b.fresh_local(perm(&alpha, l1.clone(), l2.clone()));
            let concl = perm(
                &alpha,
                cons_of(&alpha, x.clone(), l1.clone()),
                cons_of(&alpha, x.clone(), l2.clone()),
            );
            let e = b.mk_pi(
                h_id,
                BinderInfo::Default,
                perm(&alpha, l1.clone(), l2.clone()),
                concl,
            );
            let e = b.mk_pi(l2_id, BinderInfo::Implicit, list_of(&alpha), e);
            let e = b.mk_pi(l1_id, BinderInfo::Implicit, list_of(&alpha), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // ── List.Perm.swap :
        //      {α} → (x y : α) → (l : List α)
        //          → Perm α (y :: x :: l) (x :: y :: l) ──────────────────────
        let swap_ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (y_id, y) = b.fresh_local(alpha.clone());
            let (l_id, l) = b.fresh_local(list_of(&alpha));
            let yxl = cons_of(&alpha, y.clone(), cons_of(&alpha, x.clone(), l.clone()));
            let xyl = cons_of(&alpha, x.clone(), cons_of(&alpha, y.clone(), l.clone()));
            let concl = perm(&alpha, yxl, xyl);
            let e = b.mk_pi(l_id, BinderInfo::Default, list_of(&alpha), concl);
            let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // ── List.Perm.trans :
        //      {α} → {l₁ l₂ l₃ : List α} → Perm α l₁ l₂ → Perm α l₂ l₃
        //          → Perm α l₁ l₃ ────────────────────────────────────────────
        let trans_ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (l1_id, l1) = b.fresh_local(list_of(&alpha));
            let (l2_id, l2) = b.fresh_local(list_of(&alpha));
            let (l3_id, l3) = b.fresh_local(list_of(&alpha));
            let (h1_id, _h1) = b.fresh_local(perm(&alpha, l1.clone(), l2.clone()));
            let (h2_id, _h2) = b.fresh_local(perm(&alpha, l2.clone(), l3.clone()));
            let concl = perm(&alpha, l1.clone(), l3.clone());
            let e = b.mk_pi(
                h2_id,
                BinderInfo::Default,
                perm(&alpha, l2.clone(), l3.clone()),
                concl,
            );
            let e = b.mk_pi(
                h1_id,
                BinderInfo::Default,
                perm(&alpha, l1.clone(), l2.clone()),
                e,
            );
            let e = b.mk_pi(l3_id, BinderInfo::Implicit, list_of(&alpha), e);
            let e = b.mk_pi(l2_id, BinderInfo::Implicit, list_of(&alpha), e);
            let e = b.mk_pi(l1_id, BinderInfo::Implicit, list_of(&alpha), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let perm_decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("List.Perm"),
                type_: perm_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("List.Perm.nil"),
                        type_: nil_ctor_type,
                    },
                    Constructor {
                        name: Name::from_string("List.Perm.cons"),
                        type_: cons_ctor_type,
                    },
                    Constructor {
                        name: Name::from_string("List.Perm.swap"),
                        type_: swap_ctor_type,
                    },
                    Constructor {
                        name: Name::from_string("List.Perm.trans"),
                        type_: trans_ctor_type,
                    },
                ],
            }],
        };

        self.add_inductive(perm_decl)?;

        let perm_nil = Expr::const_(Name::from_string("List.Perm.nil"), vec![u_level.clone()]);
        let perm_cons = Expr::const_(Name::from_string("List.Perm.cons"), vec![u_level.clone()]);
        let perm_trans = Expr::const_(Name::from_string("List.Perm.trans"), vec![u_level.clone()]);
        // `List.Perm` is a Prop with multiple constructors → Prop-only
        // elimination: `List.Perm.rec` has a single level param `u` and its
        // motive targets `Prop`.
        let perm_rec = Expr::const_(Name::from_string("List.Perm.rec"), vec![u_level.clone()]);

        // ── List.Perm.refl : {α} → (l : List α) → Perm α l l ─────────────────
        // Proof by structural recursion on `l` via `List.rec`:
        //   motive  := λ (l : List α) => Perm α l l
        //   nil      ↦ @List.Perm.nil α
        //   cons x xs ih ↦ @List.Perm.cons α x xs xs ih
        let perm_refl_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (l_id, l) = b.fresh_local(list_of(&alpha));
            let concl = perm(&alpha, l.clone(), l.clone());
            let e = b.mk_pi(l_id, BinderInfo::Default, list_of(&alpha), concl);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let perm_refl_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());

            // motive : λ (l : List α) => Perm α l l  (returns Prop)
            let (m_id, m_l) = b.fresh_local(list_of(&alpha));
            let motive = b.mk_lam(
                m_id,
                BinderInfo::Default,
                list_of(&alpha),
                perm(&alpha, m_l.clone(), m_l.clone()),
            );

            // nil case : @List.Perm.nil α
            let nil_case = Expr::app(perm_nil.clone(), alpha.clone());

            // cons case : λ (x : α) (xs : List α) (ih : Perm α xs xs)
            //               => @List.Perm.cons α x xs xs ih
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (xs_id, xs) = b.fresh_local(list_of(&alpha));
            let (ih_id, ih) = b.fresh_local(perm(&alpha, xs.clone(), xs.clone()));
            let cons_body = Expr::apps(
                perm_cons.clone(),
                [alpha.clone(), x.clone(), xs.clone(), xs.clone(), ih.clone()],
            );
            let cons_case = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                perm(&alpha, xs.clone(), xs.clone()),
                cons_body,
            );
            let cons_case = b.mk_lam(xs_id, BinderInfo::Default, list_of(&alpha), cons_case);
            let cons_case = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), cons_case);

            // List.rec.{0, u} α motive nil_case cons_case
            // (motive lands in Prop = Sort 0, list lives in Sort u).
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), u_level.clone()],
            );
            let (l_id, l) = b.fresh_local(list_of(&alpha));
            let body = Expr::apps(
                list_rec,
                [alpha.clone(), motive, nil_case, cons_case, l.clone()],
            );
            let e = b.mk_lam(l_id, BinderInfo::Default, list_of(&alpha), body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("List.Perm.refl"),
            level_params: vec![u.clone()],
            type_: perm_refl_type,
            value: perm_refl_value,
        })?;

        // ── List.Perm.symm :
        //      {α} → {l₁ l₂ : List α} → Perm α l₁ l₂ → Perm α l₂ l₁ ──────────
        // Proof by recursion on the permutation derivation via `List.Perm.rec`:
        //   motive   := λ (a b : List α) (_ : Perm α a b) => Perm α b a
        //   nil       ↦ @List.Perm.nil α
        //   cons x ih ↦ @List.Perm.cons α x l₂ l₁ ih           (ih : Perm α l₂ l₁)
        //   swap x y l ↦ @List.Perm.swap α y x l               (symmetric image)
        //   trans ih₁ ih₂ ↦ @List.Perm.trans α l₃ l₂ l₁ ih₂ ih₁
        let perm_symm_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (l1_id, l1) = b.fresh_local(list_of(&alpha));
            let (l2_id, l2) = b.fresh_local(list_of(&alpha));
            let (h_id, _h) = b.fresh_local(perm(&alpha, l1.clone(), l2.clone()));
            let concl = perm(&alpha, l2.clone(), l1.clone());
            let e = b.mk_pi(
                h_id,
                BinderInfo::Default,
                perm(&alpha, l1.clone(), l2.clone()),
                concl,
            );
            let e = b.mk_pi(l2_id, BinderInfo::Implicit, list_of(&alpha), e);
            let e = b.mk_pi(l1_id, BinderInfo::Implicit, list_of(&alpha), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let perm_symm_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());

            // motive : λ (a b : List α) (_ : Perm α a b) => Perm α b a
            let (ma_id, ma) = b.fresh_local(list_of(&alpha));
            let (mb_id, mb) = b.fresh_local(list_of(&alpha));
            let (mp_id, _mp) = b.fresh_local(perm(&alpha, ma.clone(), mb.clone()));
            let motive_body = perm(&alpha, mb.clone(), ma.clone());
            let motive = b.mk_lam(
                mp_id,
                BinderInfo::Default,
                perm(&alpha, ma.clone(), mb.clone()),
                motive_body,
            );
            let motive = b.mk_lam(mb_id, BinderInfo::Default, list_of(&alpha), motive);
            let motive = b.mk_lam(ma_id, BinderInfo::Default, list_of(&alpha), motive);

            // nil minor : @List.Perm.nil α : Perm α [] []  (= motive [] [] nil)
            let m_nil = Expr::app(perm_nil.clone(), alpha.clone());

            // cons minor. A recursor minor premise binds the constructor's
            // fields (in declaration order, all explicit) followed by one IH
            // per recursive field, then concludes with the motive applied to
            // the constructor's result. For the Lean-faithful
            // `cons (x : α) {l₁ l₂ : List α} (h : Perm α l₁ l₂)` the premise is:
            //   λ (x : α) (l₁ l₂ : List α) (h : Perm α l₁ l₂)
            //     (ih : Perm α l₂ l₁ /- = motive l₁ l₂ h -/)
            //       => Perm α (x::l₂) (x::l₁)
            // realised by `@List.Perm.cons α x l₂ l₁ ih`.
            let m_cons = {
                let (x_id, x) = b.fresh_local(alpha.clone());
                let (cl1_id, cl1) = b.fresh_local(list_of(&alpha));
                let (cl2_id, cl2) = b.fresh_local(list_of(&alpha));
                let (chh_id, _chh) = b.fresh_local(perm(&alpha, cl1.clone(), cl2.clone()));
                let (cih_id, cih) = b.fresh_local(perm(&alpha, cl2.clone(), cl1.clone()));
                let body = Expr::apps(
                    perm_cons.clone(),
                    [
                        alpha.clone(),
                        x.clone(),
                        cl2.clone(),
                        cl1.clone(),
                        cih.clone(),
                    ],
                );
                let e = b.mk_lam(
                    cih_id,
                    BinderInfo::Default,
                    perm(&alpha, cl2.clone(), cl1.clone()),
                    body,
                );
                let e = b.mk_lam(
                    chh_id,
                    BinderInfo::Default,
                    perm(&alpha, cl1.clone(), cl2.clone()),
                    e,
                );
                let e = b.mk_lam(cl2_id, BinderInfo::Default, list_of(&alpha), e);
                let e = b.mk_lam(cl1_id, BinderInfo::Default, list_of(&alpha), e);
                b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), e)
            };

            // swap minor (no recursive fields → no IH):
            //   λ (x y : α) (l : List α) => @List.Perm.swap α y x l
            // The constructor concludes `Perm (y::x::l) (x::y::l)`, so the
            // premise must yield `motive (y::x::l) (x::y::l) (swap …)` =
            //   `Perm α (x::y::l) (y::x::l)`, which is exactly `swap α y x l`.
            let m_swap = {
                let (x_id, x) = b.fresh_local(alpha.clone());
                let (y_id, y) = b.fresh_local(alpha.clone());
                let (sl_id, sl) = b.fresh_local(list_of(&alpha));
                let perm_swap =
                    Expr::const_(Name::from_string("List.Perm.swap"), vec![u_level.clone()]);
                let body = Expr::apps(perm_swap, [alpha.clone(), y.clone(), x.clone(), sl.clone()]);
                let e = b.mk_lam(sl_id, BinderInfo::Default, list_of(&alpha), body);
                let e = b.mk_lam(y_id, BinderInfo::Default, alpha.clone(), e);
                b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), e)
            };

            // trans minor (two recursive fields → two IHs, all explicit in
            // constructor order: fields l₁ l₂ l₃ h₁ h₂, then ih₁ ih₂):
            //   λ (l₁ l₂ l₃ : List α) (h₁ : Perm α l₁ l₂) (h₂ : Perm α l₂ l₃)
            //     (ih₁ : Perm α l₂ l₁ /- motive l₁ l₂ h₁ -/)
            //     (ih₂ : Perm α l₃ l₂ /- motive l₂ l₃ h₂ -/)
            //       => @List.Perm.trans α l₃ l₂ l₁ ih₂ ih₁ : Perm α l₃ l₁
            let m_trans = {
                let (t1_id, t1) = b.fresh_local(list_of(&alpha));
                let (t2_id, t2) = b.fresh_local(list_of(&alpha));
                let (t3_id, t3) = b.fresh_local(list_of(&alpha));
                let (th1_id, _th1) = b.fresh_local(perm(&alpha, t1.clone(), t2.clone()));
                let (th2_id, _th2) = b.fresh_local(perm(&alpha, t2.clone(), t3.clone()));
                let (tih1_id, tih1) = b.fresh_local(perm(&alpha, t2.clone(), t1.clone()));
                let (tih2_id, tih2) = b.fresh_local(perm(&alpha, t3.clone(), t2.clone()));
                let body = Expr::apps(
                    perm_trans.clone(),
                    [
                        alpha.clone(),
                        t3.clone(),
                        t2.clone(),
                        t1.clone(),
                        tih2.clone(),
                        tih1.clone(),
                    ],
                );
                let e = b.mk_lam(
                    tih2_id,
                    BinderInfo::Default,
                    perm(&alpha, t3.clone(), t2.clone()),
                    body,
                );
                let e = b.mk_lam(
                    tih1_id,
                    BinderInfo::Default,
                    perm(&alpha, t2.clone(), t1.clone()),
                    e,
                );
                let e = b.mk_lam(
                    th2_id,
                    BinderInfo::Default,
                    perm(&alpha, t2.clone(), t3.clone()),
                    e,
                );
                let e = b.mk_lam(
                    th1_id,
                    BinderInfo::Default,
                    perm(&alpha, t1.clone(), t2.clone()),
                    e,
                );
                let e = b.mk_lam(t3_id, BinderInfo::Default, list_of(&alpha), e);
                let e = b.mk_lam(t2_id, BinderInfo::Default, list_of(&alpha), e);
                b.mk_lam(t1_id, BinderInfo::Default, list_of(&alpha), e)
            };

            // @List.Perm.rec α motive m_nil m_cons m_swap m_trans l₁ l₂ h
            let (l1_id, l1) = b.fresh_local(list_of(&alpha));
            let (l2_id, l2) = b.fresh_local(list_of(&alpha));
            let (h_id, h) = b.fresh_local(perm(&alpha, l1.clone(), l2.clone()));
            let body = Expr::apps(
                perm_rec.clone(),
                [
                    alpha.clone(),
                    motive,
                    m_nil,
                    m_cons,
                    m_swap,
                    m_trans,
                    l1.clone(),
                    l2.clone(),
                    h.clone(),
                ],
            );
            let e = b.mk_lam(
                h_id,
                BinderInfo::Default,
                perm(&alpha, l1.clone(), l2.clone()),
                body,
            );
            let e = b.mk_lam(l2_id, BinderInfo::Implicit, list_of(&alpha), e);
            let e = b.mk_lam(l1_id, BinderInfo::Implicit, list_of(&alpha), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("List.Perm.symm"),
            level_params: vec![u.clone()],
            type_: perm_symm_type,
            value: perm_symm_value,
        })?;

        self.list_perm_init = true;
        Ok(())
    }

    /// Check if `List.Perm` has been initialized.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_list_perm` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_list_perm(&self) -> bool {
        self.list_perm_init
    }
}

#[cfg(test)]
mod list_perm_tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    fn env_with_perm() -> Environment {
        let mut env = Environment::new();
        env.init_list_perm().expect("List.Perm should initialize");
        env
    }

    #[test]
    fn test_list_perm_init_idempotent() {
        let mut env = env_with_perm();
        env.init_list_perm()
            .expect("idempotent re-initialization should succeed");
        assert!(env.has_list_perm());
    }

    #[test]
    fn test_list_perm_inductive_and_constructors_registered() {
        let env = env_with_perm();
        for name in [
            "List.Perm",
            "List.Perm.nil",
            "List.Perm.cons",
            "List.Perm.swap",
            "List.Perm.trans",
            "List.Perm.rec",
        ] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered"
            );
        }
        // `List.Perm` is a genuine inductive with one param and TWO indices.
        let ind = env
            .inductives
            .get(&Name::from_string("List.Perm"))
            .expect("List.Perm should be an inductive");
        assert_eq!(ind.num_params, 1, "α is the sole parameter");
        assert_eq!(ind.num_indices, 2, "both `List α` arguments are indices");
    }

    /// FIDELITY + ADVERSARIAL pins for the `List.Perm.cons` binder-order
    /// correction (residual-to-zero campaign, 2026-07-02).
    ///
    /// Batteries/Lean 4.8 ground truth (`#print List.Perm`):
    /// `cons (x : α) {l₁ l₂ : List α} : Perm l₁ l₂ → Perm (x::l₁) (x::l₂)` —
    /// the ELEMENT comes first. The previous stub put the lists first
    /// (`{l₁}{l₂}(x)`), so Mathlib's positional applications
    /// (`@List.Perm.cons α (l.get i) …` in `List.erase_get`) bound the wrong
    /// binders and were rejected. Pins BOTH directions: Lean-order checks,
    /// old-transposed-order is rejected (fidelity fix, not a relaxation).
    #[test]
    fn test_perm_cons_lean_binder_order() {
        let mut env = Environment::new();
        env.init_nat().expect("nat");
        env.init_list_perm().expect("perm");
        let tc = TypeChecker::new(&env);

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            zero.clone(),
        );
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            nat.clone(),
        );
        // h : Perm [] []
        let h = Expr::app(
            Expr::const_(Name::from_string("List.Perm.nil"), vec![Level::zero()]),
            nat.clone(),
        );
        let cons = Expr::const_(Name::from_string("List.Perm.cons"), vec![Level::zero()]);

        // Lean order: @Perm.cons Nat (x := 1) (l₁ := []) (l₂ := []) h — checks.
        let good = Expr::apps(
            cons.clone(),
            [
                nat.clone(),
                one.clone(),
                nil.clone(),
                nil.clone(),
                h.clone(),
            ],
        );
        let good_ty = tc
            .infer_type_full(&good)
            .expect("Lean-binder-order Perm.cons application must type-check");
        // Conclusion is Perm (1::[]) (1::[]).
        let one_nil = Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [nat.clone(), one.clone(), nil.clone()],
        );
        let want = Expr::apps(
            Expr::const_(Name::from_string("List.Perm"), vec![Level::zero()]),
            [nat.clone(), one_nil.clone(), one_nil.clone()],
        );
        assert!(
            tc.is_def_eq(&good_ty, &want),
            "Perm.cons conclusion must be Perm (x::l₁) (x::l₂)"
        );

        // Old transposed order: @Perm.cons Nat (l₁ := ...) — positionally puts
        // a LIST where the corrected signature expects the ELEMENT. Must be
        // rejected.
        let tc2 = TypeChecker::new(&env);
        let old_order = Expr::apps(
            cons,
            [
                nat.clone(),
                nil.clone(),
                nil.clone(),
                one.clone(),
                h.clone(),
            ],
        );
        assert!(
            tc2.infer_type_full(&old_order).is_err(),
            "old transposed-order Perm.cons application must be rejected"
        );
    }

    #[test]
    fn test_list_perm_rec_type_infers_a_sort() {
        // The whole point of the multi-index recursor fix: `List.Perm.rec`'s
        // motive abstracts two `List α` index domains that reference the
        // parameter. Before the fix this raised `UnboundVariable(0)`.
        let env = env_with_perm();
        let rec = env
            .get_const(&Name::from_string("List.Perm.rec"))
            .expect("List.Perm.rec should be registered");
        let tc = TypeChecker::new(&env);
        let _sort = tc
            .infer_type(&rec.type_)
            .expect("List.Perm.rec type should infer a sort (no UnboundVariable)");
    }

    #[test]
    fn test_perm_refl_is_constructive_theorem() {
        let env = env_with_perm();
        let info = env
            .get_const(&Name::from_string("List.Perm.refl"))
            .expect("List.Perm.refl should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "theorem must retain its proof value");

        let quality = env
            .proof_quality(&Name::from_string("List.Perm.refl"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "List.Perm.refl must be Constructive (empty axiom closure), got {quality:?}"
        );
        let deps = env
            .axiom_deps(&Name::from_string("List.Perm.refl"))
            .expect("axiom_deps should be reported");
        assert!(
            deps.is_empty(),
            "List.Perm.refl must have an empty domain-axiom closure, got {deps:?}"
        );
    }

    #[test]
    fn test_perm_symm_is_constructive_theorem() {
        // The symm proof was blocked on the multi-index recursor bug: it is
        // built directly from `List.Perm.rec`, so a mis-typed recursor would
        // make this term fail to kernel-check.
        let env = env_with_perm();
        let info = env
            .get_const(&Name::from_string("List.Perm.symm"))
            .expect("List.Perm.symm should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "theorem must retain its proof value");

        let quality = env
            .proof_quality(&Name::from_string("List.Perm.symm"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "List.Perm.symm must be Constructive (empty axiom closure), got {quality:?}"
        );
        let deps = env
            .axiom_deps(&Name::from_string("List.Perm.symm"))
            .expect("axiom_deps should be reported");
        assert!(
            deps.is_empty(),
            "List.Perm.symm must have an empty domain-axiom closure, got {deps:?}"
        );
    }

    #[test]
    fn test_perm_symm_value_type_checks_to_symm_type() {
        // Independently confirm the stored proof term checks at the declared
        // `List.Perm.symm` type via the kernel type-checker.
        let env = env_with_perm();
        let info = env
            .get_const(&Name::from_string("List.Perm.symm"))
            .expect("List.Perm.symm should be registered");
        let value = info
            .value
            .clone()
            .expect("List.Perm.symm must retain its proof value");
        let tc = TypeChecker::new(&env);
        let inferred = tc
            .infer_type(&value)
            .expect("List.Perm.symm proof term should type-check");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "inferred symm type must match the declared type"
        );
    }

    #[test]
    fn test_perm_recursors_all_infer_a_sort() {
        // `add_inductive` generates `.rec`, `.casesOn`, and `.recOn`; all three
        // run through the (fixed) motive construction, so confirm each
        // multi-index `List.Perm` eliminator is well-typed.
        let env = env_with_perm();
        let tc = TypeChecker::new(&env);
        for name in ["List.Perm.rec", "List.Perm.casesOn", "List.Perm.recOn"] {
            let c = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            let _sort = tc
                .infer_type(&c.type_)
                .unwrap_or_else(|e| panic!("{name} type should infer a sort, got {e:?}"));
        }
    }

    #[test]
    fn test_existing_recursors_unchanged_still_infer() {
        // Regression guard: the de-Bruijn fix must not perturb the recursor
        // types of single-index or non-param-referencing inductives. Spot-check
        // a representative spread — `Nat` (no indices), `List` (one param, no
        // index), `Eq` (one index referencing a param), `List.Mem` (one index),
        // and `Or`/`And` (logical connectives) — by inferring each recursor's
        // stored type.
        let mut env = Environment::new();
        env.init_eq().expect("init_eq");
        env.init_and().expect("init_and");
        env.init_or().expect("init_or");
        env.init_nat().expect("init_nat");
        env.init_list_mem().expect("init_list_mem");
        let tc = TypeChecker::new(&env);
        for name in [
            "Nat.rec",
            "List.rec",
            "Eq.rec",
            "List.Mem.rec",
            "Or.rec",
            "And.rec",
        ] {
            let c = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            let _sort = tc
                .infer_type(&c.type_)
                .unwrap_or_else(|e| panic!("{name} type should infer a sort, got {e:?}"));
        }
    }
}
