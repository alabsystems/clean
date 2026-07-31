// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parametric `BEq (List α)` instance.
//!
//! Registers:
//! - `List.beq : {α : Type u} → [BEq α] → List α → List α → Bool`
//!   — a genuine recursive boolean equality built on `List.rec` (no axioms,
//!   no `sorry`).
//! - `instBEqList : {α : Type u} → [BEq α] → BEq (List α)`
//!   — a parametric instance so that structure/enum `deriving BEq` over a
//!   `List T` field resolves `BEq (List T)` instead of leaving a fresh meta
//!   (the "contains free variables" registration failure).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `List.beq` and the parametric `instBEqList` instance.
    ///
    /// Runs at the tail of `init_beq`, by which point `List`, `Bool`, `Bool.and`
    /// and `BEq`/`BEq.beq`/`BEq.mk` are all available.
    pub(crate) fn init_beq_list(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 census
        // 2026-07-06): Clean's `List.beq` is a direct double-`List.rec`
        // elimination — Lean v4.30 stores a brecOn tower, so the seeded twin
        // fails the value-defeq dedup and the `List.beq`/`instBEqList`
        // eq_def/lemma web cascades (Init.Data.List.Basic). `instBEqList`
        // wraps the gated `List.beq`, so it rides the same gate.
        // Import-suppressed (WS17 pattern): the genuine olean pair imports
        // through the checked add_decl path; the default lane is unchanged.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let bool_and = Expr::const_(Name::from_string("Bool.and"), vec![]);

        let list_const = |lvl: Level| Expr::const_(Name::from_string("List"), vec![lvl]);
        let list_alpha_of = |alpha: &Expr| Expr::app(list_const(u_level.clone()), alpha.clone());

        // List.rec.{v, u}
        let list_rec =
            |v: Level| Expr::const_(Name::from_string("List.rec"), vec![v, u_level.clone()]);
        // Motive-sort levels: Bool : Sort 1; (List α → Bool) : Type u = Sort (u+1).
        let lvl_bool = Level::succ(Level::zero()); // 1
        let lvl_fn = Level::succ(u_level.clone()); // u + 1

        let beq_const = Expr::const_(Name::from_string("BEq"), vec![u_level.clone()]);
        let beq_beq = Expr::const_(Name::from_string("BEq.beq"), vec![u_level.clone()]);
        let beq_mk = Expr::const_(Name::from_string("BEq.mk"), vec![u_level.clone()]);

        // ----------------------------------------------------------------
        // List.beq value:
        //   λ {α} [inst : BEq α] (l1 l2 : List α) =>
        //     List.rec.{u+1,u} α (motive := λ _ : List α => List α → Bool)
        //       nilCase consCase l1 l2
        // where
        //   nilCase  := λ (m2 : List α) => isNil m2
        //   consCase := λ (h1 : α) (t1 : List α) (ih : List α → Bool) =>
        //                 λ (m2 : List α) => innerMatch h1 ih m2
        // ----------------------------------------------------------------
        let list_beq_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = list_alpha_of(&alpha);
            let (inst_id, inst) = b.fresh_local(Expr::app(beq_const.clone(), alpha.clone()));
            let (l1_id, l1) = b.fresh_local(list_alpha.clone());
            let (l2_id, l2) = b.fresh_local(list_alpha.clone());

            // Outer motive: λ (_ : List α) => (List α → Bool)
            let outer_motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = c.fresh_local(list_alpha.clone());
                let fn_ty = Expr::pi(BinderInfo::Default, list_alpha.clone(), bool_const.clone());
                c.mk_lam(m_id, BinderInfo::Default, list_alpha.clone(), fn_ty)
            };

            // isNil : List α → Bool  =  List.rec.{1,u} α (λ _ => Bool) true (λ _ _ _ => false) ·
            // We build it inline as a function applied to m2 inside nilCase.
            // nilCase := λ (m2 : List α) =>
            //   List.rec.{1,u} α (λ _ : List α => Bool) Bool.true (λ _ _ _ => Bool.false) m2
            let nil_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m2_id, m2) = c.fresh_local(list_alpha.clone());

                let inner_motive = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (w_id, _w) = d.fresh_local(list_alpha.clone());
                    d.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_alpha.clone(),
                        bool_const.clone(),
                    )
                };
                // cons case for isNil: λ (h2 : α)(t2 : List α)(ih2 : Bool) => Bool.false
                let inner_cons = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (h2_id, _h2) = d.fresh_local(alpha.clone());
                    let (t2_id, _t2) = d.fresh_local(list_alpha.clone());
                    let (ih2_id, _ih2) = d.fresh_local(bool_const.clone());
                    let body = bool_false.clone();
                    let body = d.mk_lam(ih2_id, BinderInfo::Default, bool_const.clone(), body);
                    let body = d.mk_lam(t2_id, BinderInfo::Default, list_alpha.clone(), body);
                    d.finish_child(d.mk_lam(h2_id, BinderInfo::Default, alpha.clone(), body))
                };
                let rec_app = Expr::apps(
                    list_rec(lvl_bool.clone()),
                    [
                        alpha.clone(),
                        inner_motive,
                        bool_true.clone(),
                        inner_cons,
                        m2,
                    ],
                );
                c.finish_child(c.mk_lam(m2_id, BinderInfo::Default, list_alpha.clone(), rec_app))
            };

            // consCase := λ (h1 : α)(t1 : List α)(ih : List α → Bool) =>
            //   λ (m2 : List α) =>
            //     List.rec.{1,u} α (λ _ : List α => Bool)
            //       Bool.false
            //       (λ (h2 : α)(t2 : List α)(_ih2 : Bool) =>
            //          Bool.and (BEq.beq α inst h1 h2) (ih t2))
            //       m2
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h1_id, h1) = c.fresh_local(alpha.clone());
                let (t1_id, _t1) = c.fresh_local(list_alpha.clone());
                let ih_ty = Expr::pi(BinderInfo::Default, list_alpha.clone(), bool_const.clone());
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let (m2_id, m2) = c.fresh_local(list_alpha.clone());

                let inner_motive = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (w_id, _w) = d.fresh_local(list_alpha.clone());
                    d.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_alpha.clone(),
                        bool_const.clone(),
                    )
                };
                // inner cons: λ (h2 : α)(t2 : List α)(_ih2 : Bool) =>
                //   Bool.and (BEq.beq α inst h1 h2) (ih t2)
                let inner_cons = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (h2_id, h2) = d.fresh_local(alpha.clone());
                    let (t2_id, t2) = d.fresh_local(list_alpha.clone());
                    let (ih2_id, _ih2) = d.fresh_local(bool_const.clone());

                    // BEq.beq α inst h1 h2
                    let head_eq = Expr::apps(
                        beq_beq.clone(),
                        [alpha.clone(), inst.clone(), h1.clone(), h2],
                    );
                    // ih t2
                    let tail_eq = Expr::app(ih.clone(), t2);
                    // Bool.and head_eq tail_eq
                    let conj = Expr::apps(bool_and.clone(), [head_eq, tail_eq]);

                    let body = d.mk_lam(ih2_id, BinderInfo::Default, bool_const.clone(), conj);
                    let body = d.mk_lam(t2_id, BinderInfo::Default, list_alpha.clone(), body);
                    d.finish_child(d.mk_lam(h2_id, BinderInfo::Default, alpha.clone(), body))
                };

                let rec_app = Expr::apps(
                    list_rec(lvl_bool.clone()),
                    [
                        alpha.clone(),
                        inner_motive,
                        bool_false.clone(),
                        inner_cons,
                        m2,
                    ],
                );
                let body = c.mk_lam(m2_id, BinderInfo::Default, list_alpha.clone(), rec_app);
                let body = c.mk_lam(ih_id, BinderInfo::Default, ih_ty.clone(), body);
                let body = c.mk_lam(t1_id, BinderInfo::Default, list_alpha.clone(), body);
                c.finish_child(c.mk_lam(h1_id, BinderInfo::Default, alpha.clone(), body))
            };

            // List.rec.{u+1,u} α outer_motive nil_case cons_case l1   : List α → Bool
            // then applied to l2.
            let outer_rec = Expr::apps(
                list_rec(lvl_fn.clone()),
                [alpha.clone(), outer_motive, nil_case, cons_case, l1],
            );
            let body = Expr::app(outer_rec, l2);

            let body = b.mk_lam(l2_id, BinderInfo::Default, list_alpha.clone(), body);
            let body = b.mk_lam(l1_id, BinderInfo::Default, list_alpha.clone(), body);
            let body = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(beq_const.clone(), alpha.clone()),
                body,
            );
            let body = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(body)
        };

        // List.beq type:
        //   {α : Type u} → [BEq α] → List α → List α → Bool
        let list_beq_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = list_alpha_of(&alpha);
            let (inst_id, _inst) = b.fresh_local(Expr::app(beq_const.clone(), alpha.clone()));
            let (l1_id, _l1) = b.fresh_local(list_alpha.clone());
            let (l2_id, _l2) = b.fresh_local(list_alpha.clone());
            let r = bool_const.clone();
            let r = b.mk_pi(l2_id, BinderInfo::Default, list_alpha.clone(), r);
            let r = b.mk_pi(l1_id, BinderInfo::Default, list_alpha.clone(), r);
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
            name: Name::from_string("List.beq"),
            level_params: vec![u.clone()],
            type_: list_beq_type,
            value: list_beq_value,
            is_reducible: true,
        })?;

        // instBEqList : {α : Type u} → [BEq α] → BEq (List α)
        //   := λ {α} [inst] => BEq.mk (List α) (List.beq α inst)
        let inst_list_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = list_alpha_of(&alpha);
            let (inst_id, _inst) = b.fresh_local(Expr::app(beq_const.clone(), alpha.clone()));
            let r = Expr::app(beq_const.clone(), list_alpha);
            let r = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(beq_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let inst_list_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = list_alpha_of(&alpha);
            let (inst_id, inst) = b.fresh_local(Expr::app(beq_const.clone(), alpha.clone()));

            // List.beq α inst  : List α → List α → Bool
            let list_beq_applied = Expr::apps(
                Expr::const_(Name::from_string("List.beq"), vec![u_level.clone()]),
                [alpha.clone(), inst.clone()],
            );
            // BEq.mk (List α) (List.beq α inst)
            let body = Expr::apps(beq_mk.clone(), [list_alpha, list_beq_applied]);

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
            name: Name::from_string("instBEqList"),
            level_params: vec![u.clone()],
            type_: inst_list_type,
            value: inst_list_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instBEqList"),
            class_name: Name::from_string("BEq"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // ── List.contains {α : Type u} [BEq α] (as : List α) (a : α) : Bool ─
        // R170: Lean `Init/Data/List/Basic.lean` — `List.contains as a := as.elem a`,
        // where `List.elem a | [] => false | b::bs => a == b || elem a bs`. Folded
        // over `as` as
        //   @List.rec α (λ _ => Bool) Bool.false
        //             (λ hd _ ih => Bool.or (@BEq.beq α inst a hd) ih) as
        // — the same `List.rec.{1,u}`-into-`Bool` shape as `List.any`, but the
        // cons test is `a == hd` (the fixed query element vs the head, via the
        // `[BEq α]` instance). Registered HERE (not with `List.any`/`List.all` in
        // `init_list_combinators`) because its type references `BEq`, which is
        // registered only after that earlier combinator pass. Reducible,
        // axiom-free; withheld in import mode with the rest of this init.
        if self
            .get_const(&Name::from_string("List.contains"))
            .is_none()
        {
            let bool_or = Expr::const_(Name::from_string("Bool.or"), vec![]);
            let contains_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let beq_alpha = Expr::app(beq_const.clone(), alpha.clone());
                let list_alpha = list_alpha_of(&alpha);
                let (inst_id, _inst) = b.fresh_local(beq_alpha.clone());
                let (as_id, _as) = b.fresh_local(list_alpha.clone());
                let (a_id, _a) = b.fresh_local(alpha.clone());
                let e = bool_const.clone();
                let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_pi(as_id, BinderInfo::Default, list_alpha.clone(), e);
                let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, beq_alpha.clone(), e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let contains_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let beq_alpha = Expr::app(beq_const.clone(), alpha.clone());
                let list_alpha = list_alpha_of(&alpha);
                let (inst_id, inst) = b.fresh_local(beq_alpha.clone());
                let (as_id, as_) = b.fresh_local(list_alpha.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());

                // motive: λ (_ : List α) => Bool
                let (m_id, _m) = b.fresh_local(list_alpha.clone());
                let motive = b.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    list_alpha.clone(),
                    bool_const.clone(),
                );

                // cons case: λ (hd : α) (_ : List α) (ih : Bool) =>
                //              Bool.or (@BEq.beq α inst a hd) ih
                let (hd_id, hd) = b.fresh_local(alpha.clone());
                let (tl_id, _tl) = b.fresh_local(list_alpha.clone());
                let (ih_id, ih) = b.fresh_local(bool_const.clone());
                let beq_a_hd = Expr::apps(
                    beq_beq.clone(),
                    [alpha.clone(), inst.clone(), a.clone(), hd.clone()],
                );
                let cons_body = Expr::apps(bool_or.clone(), [beq_a_hd, ih.clone()]);
                let cons_case = b.mk_lam(ih_id, BinderInfo::Default, bool_const.clone(), cons_body);
                let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), cons_case);
                let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);

                let body = Expr::apps(
                    list_rec(lvl_bool.clone()),
                    [
                        alpha.clone(),
                        motive,
                        bool_false.clone(),
                        cons_case,
                        as_.clone(),
                    ],
                );
                let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
                let e = b.mk_lam(as_id, BinderInfo::Default, list_alpha.clone(), e);
                let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, beq_alpha.clone(), e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.contains"),
                level_params: vec![u.clone()],
                type_: contains_type,
                value: contains_value,
                is_reducible: true,
            })?;
        }

        // ── List.count {α : Type u} [BEq α] (a : α) (l : List α) : Nat ──────
        // R171: Lean `Init/Data/List/Count.lean` — `List.count a l := countP (· == a) l`,
        // the number of elements of `l` that BEq-equal `a`. Folded over `l` as
        //   @List.rec α (λ _ => Nat) Nat.zero
        //     (λ hd _ ih => @Bool.rec (λ _ => Nat) ih (Nat.succ ih) (@BEq.beq α inst hd a)) l
        // — a `List.rec.{1,u}`-into-`Nat` fold whose cons case is `if hd == a
        // then ih+1 else ih`, spelled with `Bool.rec` (minor order [false, true])
        // over the instance's `hd == a`. `Bool.rec`/`Nat.succ` are fundamental and
        // available here; deliberately NOT `Bool.toNat` (R163), which is registered
        // in a LATER init pass than `init_beq_list` (same ordering trap as placing
        // List.contains before BEq). Arg order `(a, l)` matches Lean, so `l.count a`
        // resolves `l` to the `List α` parameter. Withheld in import mode.
        if self.get_const(&Name::from_string("List.count")).is_none() {
            let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
            let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![lvl_bool.clone()]);

            let count_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let beq_alpha = Expr::app(beq_const.clone(), alpha.clone());
                let list_alpha = list_alpha_of(&alpha);
                let (inst_id, _inst) = b.fresh_local(beq_alpha.clone());
                let (a_id, _a) = b.fresh_local(alpha.clone());
                let (l_id, _l) = b.fresh_local(list_alpha.clone());
                let e = nat_const.clone();
                let e = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, beq_alpha.clone(), e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let count_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let beq_alpha = Expr::app(beq_const.clone(), alpha.clone());
                let list_alpha = list_alpha_of(&alpha);
                let (inst_id, inst) = b.fresh_local(beq_alpha.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (l_id, l) = b.fresh_local(list_alpha.clone());

                // motive: λ (_ : List α) => Nat
                let (m_id, _m) = b.fresh_local(list_alpha.clone());
                let motive = b.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    list_alpha.clone(),
                    nat_const.clone(),
                );

                // cons case: λ (hd : α) (_ : List α) (ih : Nat) =>
                //              Nat.add (Bool.toNat (@BEq.beq α inst hd a)) ih
                let (hd_id, hd) = b.fresh_local(alpha.clone());
                let (tl_id, _tl) = b.fresh_local(list_alpha.clone());
                let (ih_id, ih) = b.fresh_local(nat_const.clone());
                let beq_hd_a = Expr::apps(
                    beq_beq.clone(),
                    [alpha.clone(), inst.clone(), hd.clone(), a.clone()],
                );
                // inner Bool.rec motive: λ (_ : Bool) => Nat
                let (bm_id, _bm) = b.fresh_local(bool_const.clone());
                let bool_motive = b.mk_lam(
                    bm_id,
                    BinderInfo::Default,
                    bool_const.clone(),
                    nat_const.clone(),
                );
                let succ_ih = Expr::app(nat_succ.clone(), ih.clone());
                // @Bool.rec (λ _ => Nat) ih (Nat.succ ih) (hd == a)
                //   = if hd == a then ih + 1 else ih   (minor order [false, true])
                let cons_body = Expr::apps(
                    bool_rec.clone(),
                    [bool_motive, ih.clone(), succ_ih, beq_hd_a],
                );
                let cons_case = b.mk_lam(ih_id, BinderInfo::Default, nat_const.clone(), cons_body);
                let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), cons_case);
                let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);

                let body = Expr::apps(
                    list_rec(lvl_bool.clone()),
                    [
                        alpha.clone(),
                        motive,
                        nat_zero.clone(),
                        cons_case,
                        l.clone(),
                    ],
                );
                let e = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), body);
                let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, beq_alpha.clone(), e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.count"),
                level_params: vec![u.clone()],
                type_: count_type,
                value: count_value,
                is_reducible: true,
            })?;
        }

        // ── List.elem {α : Type u} [BEq α] (a : α) (l : List α) : Bool ──────
        // R172: Lean `Init/Data/List/Basic.lean` — the primitive `List.contains`
        // delegates to: `List.elem a | [] => false | b::bs => a == b || elem a bs`.
        // Folded over `l` as
        //   @List.rec α (λ _ => Bool) Bool.false
        //             (λ hd _ ih => Bool.or (@BEq.beq α inst a hd) ih) l
        // — identical `List.rec.{1,u}`→`Bool` shape to `List.contains` (R170), but
        // the query element `a` is the FIRST explicit argument (so `l.elem a`
        // resolves `l` to the `List α` parameter, matching Lean). Uses only
        // fundamental primitives (Bool.or/Bool.false/BEq.beq/List.rec — NOT the
        // later-registered Bool.toNat). Withheld in import mode.
        if self.get_const(&Name::from_string("List.elem")).is_none() {
            let bool_or = Expr::const_(Name::from_string("Bool.or"), vec![]);

            let elem_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let beq_alpha = Expr::app(beq_const.clone(), alpha.clone());
                let list_alpha = list_alpha_of(&alpha);
                let (inst_id, _inst) = b.fresh_local(beq_alpha.clone());
                let (a_id, _a) = b.fresh_local(alpha.clone());
                let (l_id, _l) = b.fresh_local(list_alpha.clone());
                let e = bool_const.clone();
                let e = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, beq_alpha.clone(), e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let elem_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let beq_alpha = Expr::app(beq_const.clone(), alpha.clone());
                let list_alpha = list_alpha_of(&alpha);
                let (inst_id, inst) = b.fresh_local(beq_alpha.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (l_id, l) = b.fresh_local(list_alpha.clone());

                // motive: λ (_ : List α) => Bool
                let (m_id, _m) = b.fresh_local(list_alpha.clone());
                let motive = b.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    list_alpha.clone(),
                    bool_const.clone(),
                );

                // cons case: λ (hd : α) (_ : List α) (ih : Bool) =>
                //              Bool.or (@BEq.beq α inst a hd) ih
                let (hd_id, hd) = b.fresh_local(alpha.clone());
                let (tl_id, _tl) = b.fresh_local(list_alpha.clone());
                let (ih_id, ih) = b.fresh_local(bool_const.clone());
                let beq_a_hd = Expr::apps(
                    beq_beq.clone(),
                    [alpha.clone(), inst.clone(), a.clone(), hd.clone()],
                );
                let cons_body = Expr::apps(bool_or.clone(), [beq_a_hd, ih.clone()]);
                let cons_case = b.mk_lam(ih_id, BinderInfo::Default, bool_const.clone(), cons_body);
                let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), cons_case);
                let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);

                let body = Expr::apps(
                    list_rec(lvl_bool.clone()),
                    [
                        alpha.clone(),
                        motive,
                        bool_false.clone(),
                        cons_case,
                        l.clone(),
                    ],
                );
                let e = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), body);
                let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, beq_alpha.clone(), e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.elem"),
                level_params: vec![u.clone()],
                type_: elem_type,
                value: elem_value,
                is_reducible: true,
            })?;
        }

        // ── List.indexOf {α : Type u} [BEq α] (a : α) (l : List α) : Nat ────
        // R173: Lean `Init/Data/List/Basic.lean` — `List.indexOf a := findIdx (· == a)`,
        // the 0-based position of the first element BEq-equal to `a`, or `l.length`
        // if none. As a direct (accumulator-free) fold:
        //   indexOf a (hd :: tl) = if hd == a then 0 else Nat.succ (indexOf a tl)
        //   indexOf a []         = 0
        // i.e. @List.rec α (λ _ => Nat) Nat.zero
        //        (λ hd _ ih => @Bool.rec (λ _ => Nat) (Nat.succ ih) Nat.zero (@BEq.beq α inst hd a)) l
        // Bool.rec minor order [false, true]: no-match ↦ `Nat.succ ih` (1 + the
        // index within the tail), match ↦ `Nat.zero` (found here). Same type/shape
        // as `List.count` but the cons branches are swapped. All-fundamental
        // primitives (Bool.rec/Nat.succ/Nat.zero/BEq.beq/List.rec); withheld in
        // import mode.
        if self.get_const(&Name::from_string("List.indexOf")).is_none() {
            let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
            let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![lvl_bool.clone()]);

            let index_of_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let beq_alpha = Expr::app(beq_const.clone(), alpha.clone());
                let list_alpha = list_alpha_of(&alpha);
                let (inst_id, _inst) = b.fresh_local(beq_alpha.clone());
                let (a_id, _a) = b.fresh_local(alpha.clone());
                let (l_id, _l) = b.fresh_local(list_alpha.clone());
                let e = nat_const.clone();
                let e = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, beq_alpha.clone(), e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let index_of_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let beq_alpha = Expr::app(beq_const.clone(), alpha.clone());
                let list_alpha = list_alpha_of(&alpha);
                let (inst_id, inst) = b.fresh_local(beq_alpha.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (l_id, l) = b.fresh_local(list_alpha.clone());

                // motive: λ (_ : List α) => Nat
                let (m_id, _m) = b.fresh_local(list_alpha.clone());
                let motive = b.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    list_alpha.clone(),
                    nat_const.clone(),
                );

                // cons case: λ (hd : α) (_ : List α) (ih : Nat) =>
                //   @Bool.rec (λ _ => Nat) (Nat.succ ih) Nat.zero (@BEq.beq α inst hd a)
                let (hd_id, hd) = b.fresh_local(alpha.clone());
                let (tl_id, _tl) = b.fresh_local(list_alpha.clone());
                let (ih_id, ih) = b.fresh_local(nat_const.clone());
                let beq_hd_a = Expr::apps(
                    beq_beq.clone(),
                    [alpha.clone(), inst.clone(), hd.clone(), a.clone()],
                );
                let (bm_id, _bm) = b.fresh_local(bool_const.clone());
                let bool_motive = b.mk_lam(
                    bm_id,
                    BinderInfo::Default,
                    bool_const.clone(),
                    nat_const.clone(),
                );
                let succ_ih = Expr::app(nat_succ.clone(), ih.clone());
                let cons_body = Expr::apps(
                    bool_rec.clone(),
                    [bool_motive, succ_ih, nat_zero.clone(), beq_hd_a],
                );
                let cons_case = b.mk_lam(ih_id, BinderInfo::Default, nat_const.clone(), cons_body);
                let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), cons_case);
                let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);

                let body = Expr::apps(
                    list_rec(lvl_bool.clone()),
                    [
                        alpha.clone(),
                        motive,
                        nat_zero.clone(),
                        cons_case,
                        l.clone(),
                    ],
                );
                let e = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), body);
                let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, beq_alpha.clone(), e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.indexOf"),
                level_params: vec![u.clone()],
                type_: index_of_type,
                value: index_of_value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    /// Both `List.beq` and the parametric `instBEqList` are registered as
    /// `Definition`s (not axioms) by `with_prelude`, and their declared types
    /// type-check via `infer_type` — proving the closed terms are well-formed.
    #[test]
    fn test_list_beq_and_inst_type_check() {
        let env = Environment::with_prelude();

        for name in ["List.beq", "instBEqList"] {
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
    }

    /// The axiom closure of `instBEqList` and `List.beq` is EMPTY — no `sorryAx`,
    /// no fake/trusted axiom anywhere in the term. This is the no-fake guard.
    #[test]
    fn test_list_beq_axiom_closure_empty() {
        let env = Environment::with_prelude();
        for name in ["List.beq", "instBEqList"] {
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
