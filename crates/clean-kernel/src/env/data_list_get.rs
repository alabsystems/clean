// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `List.get` — the Fin-indexed accessor behind the `List` `GetElem`
//! instance (Brick 4; companion to `data_getelem_list.rs`).
//!
//! ```text
//! def List.get {α : Type u} : (as : List α) → Fin as.length → α
//!   | cons a _,  ⟨0, _⟩ => a
//!   | cons _ as, ⟨Nat.succ i, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩
//! ```
//!
//! Lean source (toolchain `v4.30.0-rc2`): `Init/Prelude.lean:3059`, with
//! Lean's exact `Fin as.length` signature (the prelude carries
//! `Fin`/`Fin.mk`/`Fin.val`/`Fin.isLt`). Compiled to a `List.rec`
//! elimination — total by construction over the `Fin` evidence, exactly the
//! recursion of Lean's equation-compiled definition; fully kernel-checked,
//! no axioms, no sorry.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constant table for the `List.get` / `GetElem`-instance builders,
/// all at the single universe parameter `u`.
pub(super) struct ListGetElemConsts {
    pub(super) u: Level,
    pub(super) type_u: Expr,
    pub(super) nat: Expr,
    pub(super) nat_succ: Expr,
    pub(super) nat_zero: Expr,
    pub(super) nat_lt: Expr,
    pub(super) list: Expr,
    pub(super) list_length: Expr,
    pub(super) fin: Expr,
    pub(super) fin_mk: Expr,
    pub(super) fin_val: Expr,
    pub(super) fin_islt: Expr,
    pub(super) lt_lt: Expr,
    pub(super) inst_lt_nat: Expr,
}

impl ListGetElemConsts {
    pub(super) fn new(u: &Level) -> Self {
        Self {
            u: u.clone(),
            type_u: Expr::sort(Level::succ(u.clone())),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            list: Expr::const_(Name::from_string("List"), vec![u.clone()]),
            list_length: Expr::const_(Name::from_string("List.length"), vec![u.clone()]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_mk: Expr::const_(Name::from_string("Fin.mk"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_islt: Expr::const_(Name::from_string("Fin.isLt"), vec![]),
            lt_lt: Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
            inst_lt_nat: Expr::const_(Name::from_string("instLTNat"), vec![]),
        }
    }

    /// `@List.length α as`
    pub(super) fn len(&self, alpha: &Expr, as_: &Expr) -> Expr {
        Expr::apps(self.list_length.clone(), [alpha.clone(), as_.clone()])
    }

    /// `Nat.lt a b` (the raw prelude spelling `Fin.mk`/`Fin.isLt` use).
    pub(super) fn nat_lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a, b])
    }

    /// `fun (as : List α) (i : Nat) => @LT.lt Nat instLTNat i (List.length as)`
    /// — Lean's `fun as i => i < as.length` valid predicate
    /// (`Init/GetElem.lean:293/339`).
    pub(super) fn valid_pred(&self, parent: &EnvDeclBuilder, alpha: &Expr) -> Expr {
        let list_alpha = Expr::app(self.list.clone(), alpha.clone());
        let mut c = EnvDeclBuilder::child_of(parent);
        let (as_id, as_) = c.fresh_local(list_alpha.clone());
        let (i_id, i) = c.fresh_local(self.nat.clone());
        let body = Expr::apps(
            self.lt_lt.clone(),
            [
                self.nat.clone(),
                self.inst_lt_nat.clone(),
                i,
                self.len(alpha, &as_),
            ],
        );
        let r = c.mk_lam(i_id, BinderInfo::Default, self.nat.clone(), body);
        let r = c.mk_lam(as_id, BinderInfo::Default, list_alpha, r);
        c.finish_child(r)
    }
}

impl Environment {
    /// `List.get {α : Type u} : (as : List α) → Fin as.length → α`
    /// (`Init/Prelude.lean:3059`), as a `List.rec` elimination with motive
    /// `fun as => Fin as.length → α`:
    /// - nil minor: `Fin (length nil)` is uninhabited — refute with
    ///   `False.elim (Nat.not_succ_le_zero i.val i.isLt)` (`length nil ≡ 0`).
    /// - cons minor: `Nat.rec` on `i.val` with the bound threaded through the
    ///   motive `fun v => Nat.lt v (length (cons a tl)) → α`; the zero case
    ///   returns the head, the succ case recurses with
    ///   `⟨j, Nat.le_of_succ_le_succ h⟩` — exactly Lean's two equations.
    pub(super) fn register_list_get(
        &mut self,
        u: &Name,
        k: &ListGetElemConsts,
    ) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("List.get")).is_some() {
            return Ok(());
        }

        // Motive codomain `Fin (length l) → α : Type u` (imax 1 (u+1) = u+1),
        // so List.rec/Nat.rec eliminate at [succ u] (List.rec: [succ u, u]).
        let list_rec = Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::succ(k.u.clone()), k.u.clone()],
        );
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(k.u.clone())]);
        let false_elim = Expr::const_(
            Name::from_string("False.elim"),
            vec![Level::succ(k.u.clone())],
        );
        let not_succ_le_zero = Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]);
        let le_of_succ_le_succ = Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]);
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![k.u.clone()]);
        let list_cons = Expr::const_(Name::from_string("List.cons"), vec![k.u.clone()]);

        // {α : Type u} → (as : List α) → Fin (List.length as) → α
        let get_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(k.type_u.clone());
            let list_alpha = Expr::app(k.list.clone(), alpha.clone());
            let (as_id, as_) = b.fresh_local(list_alpha.clone());
            let fin_len = Expr::app(k.fin.clone(), k.len(&alpha, &as_));
            let (i_id, _i) = b.fresh_local(fin_len.clone());
            let r = alpha.clone();
            let r = b.mk_pi(i_id, BinderInfo::Default, fin_len, r);
            let r = b.mk_pi(as_id, BinderInfo::Default, list_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, k.type_u.clone(), r);
            b.finish(r)
        };

        let get_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(k.type_u.clone());
            let list_alpha = Expr::app(k.list.clone(), alpha.clone());
            let (as_id, as_) = b.fresh_local(list_alpha.clone());

            // motive: fun (l : List α) => Fin (List.length l) → α
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (l_id, l) = c.fresh_local(list_alpha.clone());
                let fin_len = Expr::app(k.fin.clone(), k.len(&alpha, &l));
                let r = Expr::pi(BinderInfo::Default, fin_len, alpha.clone());
                let r = c.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), r);
                c.finish_child(r)
            };

            // nil minor: fun (i : Fin (length nil)) =>
            //   False.elim α (Nat.not_succ_le_zero i.val i.isLt)
            // Well-typed: i.isLt : Nat.lt i.val (length nil), and
            // `Nat.lt a b ≡ Nat.le (succ a) b` (δ) with `length nil ≡ 0` (δι).
            let nil_minor = {
                let nil_alpha = Expr::app(list_nil.clone(), alpha.clone());
                let len_nil = k.len(&alpha, &nil_alpha);
                let fin_len_nil = Expr::app(k.fin.clone(), len_nil.clone());
                let mut c = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = c.fresh_local(fin_len_nil.clone());
                let val_i = Expr::apps(k.fin_val.clone(), [len_nil.clone(), i.clone()]);
                let islt_i = Expr::apps(k.fin_islt.clone(), [len_nil.clone(), i.clone()]);
                let absurd = Expr::apps(not_succ_le_zero.clone(), [val_i, islt_i]);
                let body = Expr::apps(false_elim.clone(), [alpha.clone(), absurd]);
                let r = c.mk_lam(i_id, BinderInfo::Default, fin_len_nil, body);
                c.finish_child(r)
            };

            // cons minor: fun (a : α) (tl : List α) (ih : Fin (length tl) → α)
            //               (i : Fin (length (cons a tl))) =>
            //   Nat.rec (motive := fun v => Nat.lt v (length (cons a tl)) → α)
            //     (fun _ => a)
            //     (fun j _prev h => ih ⟨j, Nat.le_of_succ_le_succ (succ j) (length tl) h⟩)
            //     i.val i.isLt
            let cons_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(alpha.clone());
                let (tl_id, tl) = c.fresh_local(list_alpha.clone());
                let len_tl = k.len(&alpha, &tl);
                let fin_len_tl = Expr::app(k.fin.clone(), len_tl.clone());
                let ih_ty = Expr::pi(BinderInfo::Default, fin_len_tl, alpha.clone());
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let cons_a_tl =
                    Expr::apps(list_cons.clone(), [alpha.clone(), a.clone(), tl.clone()]);
                let len_cons = k.len(&alpha, &cons_a_tl);
                let fin_len_cons = Expr::app(k.fin.clone(), len_cons.clone());
                let (i_id, i) = c.fresh_local(fin_len_cons.clone());

                // inner motive: fun (v : Nat) => Nat.lt v (length (cons a tl)) → α
                let nat_motive = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (v_id, v) = d.fresh_local(k.nat.clone());
                    let r = Expr::pi(
                        BinderInfo::Default,
                        k.nat_lt(v, len_cons.clone()),
                        alpha.clone(),
                    );
                    let r = d.mk_lam(v_id, BinderInfo::Default, k.nat.clone(), r);
                    d.finish_child(r)
                };
                // zero minor: fun (_ : Nat.lt 0 (length (cons a tl))) => a
                let zero_minor = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let h_ty = k.nat_lt(k.nat_zero.clone(), len_cons.clone());
                    let (h_id, _h) = d.fresh_local(h_ty.clone());
                    let r = d.mk_lam(h_id, BinderInfo::Default, h_ty, a.clone());
                    d.finish_child(r)
                };
                // succ minor: fun (j : Nat) (_prev : Nat.lt j (length (cons a tl)) → α)
                //               (h : Nat.lt (succ j) (length (cons a tl))) =>
                //   ih (Fin.mk (length tl) j (Nat.le_of_succ_le_succ (succ j) (length tl) h))
                // Well-typed: `Nat.lt (succ j) (length (cons a tl))`
                //   ≡ Nat.le (succ (succ j)) (succ (length tl)) (δι).
                let succ_minor = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (j_id, j) = d.fresh_local(k.nat.clone());
                    let prev_ty = Expr::pi(
                        BinderInfo::Default,
                        k.nat_lt(j.clone(), len_cons.clone()),
                        alpha.clone(),
                    );
                    let (prev_id, _prev) = d.fresh_local(prev_ty.clone());
                    let succ_j = Expr::app(k.nat_succ.clone(), j.clone());
                    let h_ty = k.nat_lt(succ_j.clone(), len_cons.clone());
                    let (h_id, h) = d.fresh_local(h_ty.clone());
                    let bound = Expr::apps(le_of_succ_le_succ.clone(), [succ_j, len_tl.clone(), h]);
                    let fin_j = Expr::apps(k.fin_mk.clone(), [len_tl.clone(), j.clone(), bound]);
                    let body = Expr::app(ih.clone(), fin_j);
                    let r = d.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                    let r = d.mk_lam(prev_id, BinderInfo::Default, prev_ty, r);
                    let r = d.mk_lam(j_id, BinderInfo::Default, k.nat.clone(), r);
                    d.finish_child(r)
                };

                let val_i = Expr::apps(k.fin_val.clone(), [len_cons.clone(), i.clone()]);
                let islt_i = Expr::apps(k.fin_islt.clone(), [len_cons.clone(), i.clone()]);
                let body = Expr::apps(
                    nat_rec.clone(),
                    [nat_motive, zero_minor, succ_minor, val_i, islt_i],
                );
                let r = c.mk_lam(i_id, BinderInfo::Default, fin_len_cons, body);
                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
                let r = c.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };

            let body = Expr::apps(
                list_rec,
                [alpha.clone(), motive, nil_minor, cons_minor, as_.clone()],
            );
            let r = b.mk_lam(as_id, BinderInfo::Default, list_alpha, body);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, k.type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.get"),
            level_params: vec![u.clone()],
            type_: get_type,
            value: get_value,
            is_reducible: true,
        })
    }
}
