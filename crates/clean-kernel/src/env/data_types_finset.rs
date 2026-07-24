// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Finset` — the faithful "no-duplicates multiset", built on the genuine
//! `Multiset` quotient (so `Finset` equality is up to permutation, exactly as
//! in Lean 4 / Mathlib).
//!
//! This module is the next link in the substrate chain toward `Fintype`:
//!
//! - `Multiset.Nodup : Multiset α → Prop` — lifts `List.Nodup` through the
//!   `Quot (@List.Perm α)` quotient. The lift is well-defined because `Nodup`
//!   respects `Perm`, witnessed by the constructive congruence
//!   `List.Perm.nodup_iff : Perm l₁ l₂ → (List.Nodup l₁ ↔ List.Nodup l₂)`
//!   (proved by `List.Perm.rec`); `propext` turns the `Iff` into the `Eq` that
//!   `Quot.lift` needs.
//! - `Finset α := { s : Multiset α // Multiset.Nodup s }` — a `Subtype` of the
//!   `Multiset` quotient.
//! - `Finset.empty`, `Finset.Mem`, and the `Membership (Finset α)` instance.
//!
//! Every declaration here is constructive and its transitive axiom closure is
//! `⊆ {Quot.sound, propext}` — both FOUNDATIONAL. No domain-specific axiom,
//! `sorry`, or unchecked declaration is introduced (the lone exception is the
//! `Membership` *instance*, registered as an opaque `Axiom` exactly as
//! `Multiset.instMembership` is — a typeclass-instance shim, not a proof).
//!
//! Universe handling: `List.{u} : Type u → Type u`, so `List α : Type u =
//! Sort (u+1)`; `Multiset α : Type u` likewise. The quotient lift therefore
//! lives at level `u+1`, mirroring `data_types_multiset.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize `Multiset.Nodup`, the `Finset` subtype, and its core
    /// operations (`empty`, `Mem`) plus the `Membership` instance.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance.
    /// ENSURES: On success, `self.finset_init == true`.
    /// ENSURES: On success the following are registered: the And/Not/Iff
    ///          congruence helpers, `List.nodup_cons_iff`,
    ///          `List.Perm.nodup_iff`, `Multiset.Nodup`, `Finset`,
    ///          `Finset.mk`/`val`/`property`/`rec` (via `Subtype`),
    ///          `Finset.empty`, `Finset.Mem`, and `Finset.instMembership`.
    /// ENSURES: Idempotent — calling multiple times returns `Ok(())` without
    ///          duplication.
    pub fn init_finset(&mut self) -> Result<(), EnvError> {
        if self.finset_init {
            return Ok(());
        }

        // Dependencies: the full Multiset substrate (List, List.Mem, List.Perm,
        // List.Nodup, Multiset + ops + Mem), And/Not/Iff/Eq, Quot machinery, and
        // Subtype for the Finset carrier.
        self.init_multiset()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_subtype()?;

        self.init_finset_logic_helpers()?;
        self.init_list_nodup_cons_iff()?;
        self.init_perm_nodup_iff()?;
        self.init_multiset_nodup()?;
        self.init_finset_core()?;
        self.init_finset_mem_cons()?;
        self.init_fintype()?;

        self.finset_init = true;
        Ok(())
    }

    /// Register the real `Fintype` *structure* (Type-valued, carrying data):
    ///
    /// ```text
    /// structure Fintype (α : Type u) : Type u where
    ///   elems    : Finset α
    ///   complete : ∀ (a : α), Finset.Mem a elems
    /// ```
    ///
    /// This replaces the earlier opaque `Fintype : (α : Type u) → Prop` axiom
    /// (wrong sort — in Lean 4 `Fintype α` is *data*). It is registered as a
    /// one-constructor inductive `Fintype.mk` with structure projections
    /// `Fintype.elems` and `Fintype.complete` (via `Expr::proj`), exactly like
    /// the other kernel structures (`Subtype`, `Prod`, …). No axiom, `sorry`, or
    /// unchecked declaration is introduced; the completeness field uses the
    /// genuine `Finset.Mem` predicate built earlier in this module.
    ///
    /// The `α` binder of the *type* is explicit (`Default`) to match Lean 4's
    /// `class Fintype (α : Type*)`; in the constructor and projections it is
    /// implicit, consumed positionally by the kernel.
    pub(crate) fn init_fintype(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Fintype")).is_some()
            && self.get_const(&Name::from_string("Fintype.mk")).is_some()
        {
            return Ok(());
        }
        // Dependencies: `Finset` + `Finset.Mem`. When invoked from inside
        // `init_finset` (after `init_finset_core`), the carrier already exists,
        // so we must NOT re-enter `init_finset` (its `finset_init` flag is not
        // yet set, which would double-register the logic helpers). When invoked
        // standalone (e.g. from `init_domain_types`), the carrier is absent and
        // we build the full Finset chain first; that chain ends by calling
        // `init_fintype` again, which the idempotency guard above short-circuits.
        if self.get_const(&Name::from_string("Finset")).is_none() {
            self.init_finset()?;
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

        let finset_const = Expr::const_(Name::from_string("Finset"), vec![u_level.clone()]);
        let finset_mem = Expr::const_(Name::from_string("Finset.Mem"), vec![u_level.clone()]);
        let fintype_const = Expr::const_(Name::from_string("Fintype"), vec![u_level.clone()]);

        let fin_of = |a: &Expr| Expr::app(finset_const.clone(), a.clone());
        let fmem = |a: &Expr, x: Expr, f: Expr| Expr::apps(finset_mem.clone(), [a.clone(), x, f]);

        // Fintype : Type u → Type u
        let fintype_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());

        // complete-field type as a function of (α, elems):
        //   ∀ (a : α), Finset.Mem a elems
        let complete_ty = |b: &mut EnvDeclBuilder, alpha: &Expr, elems: &Expr| -> Expr {
            let (a_id, a) = b.fresh_local(alpha.clone());
            let body = fmem(alpha, a.clone(), elems.clone());
            b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body)
        };

        // Fintype.mk : {α : Type u} → (elems : Finset α)
        //                → (∀ (a : α), Finset.Mem a elems) → Fintype α
        let fintype_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (elems_id, elems) = b.fresh_local(fin_of(&alpha));
            let comp_ty = complete_ty(&mut b, &alpha, &elems);
            let (comp_id, _comp) = b.fresh_local(comp_ty.clone());
            let result = Expr::app(fintype_const.clone(), alpha.clone());
            let e = b.mk_pi(comp_id, BinderInfo::Default, comp_ty, result);
            let e = b.mk_pi(elems_id, BinderInfo::Default, fin_of(&alpha), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Fintype"),
                type_: fintype_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Fintype.mk"),
                    type_: fintype_mk_type,
                }],
            }],
        })?;

        // Fintype.elems : {α : Type u} → Fintype α → Finset α
        let elems_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ft = Expr::app(fintype_const.clone(), alpha.clone());
            let (s_id, _s) = b.fresh_local(ft.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, ft, fin_of(&alpha));
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let elems_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ft = Expr::app(fintype_const.clone(), alpha.clone());
            let (s_id, s) = b.fresh_local(ft.clone());
            let body = Expr::proj(Name::from_string("Fintype"), 0, s);
            let e = b.mk_lam(s_id, BinderInfo::Default, ft, body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fintype.elems"),
            level_params: vec![u.clone()],
            type_: elems_type,
            value: elems_value,
            is_reducible: true,
        })?;

        // Fintype.complete : {α : Type u} → (s : Fintype α)
        //                      → ∀ (a : α), Finset.Mem a (Fintype.elems s)
        let elems_const = Expr::const_(Name::from_string("Fintype.elems"), vec![u_level.clone()]);
        let complete_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ft = Expr::app(fintype_const.clone(), alpha.clone());
            let (s_id, s) = b.fresh_local(ft.clone());
            let elems_s = Expr::apps(elems_const.clone(), [alpha.clone(), s.clone()]);
            let comp_ty = complete_ty(&mut b, &alpha, &elems_s);
            let e = b.mk_pi(s_id, BinderInfo::Default, ft, comp_ty);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let complete_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ft = Expr::app(fintype_const.clone(), alpha.clone());
            let (s_id, s) = b.fresh_local(ft.clone());
            let body = Expr::proj(Name::from_string("Fintype"), 1, s);
            let e = b.mk_lam(s_id, BinderInfo::Default, ft, body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fintype.complete"),
            level_params: vec![u.clone()],
            type_: complete_type,
            value: complete_value,
            is_reducible: true,
        })?;

        self.register_structure_fields(
            Name::from_string("Fintype"),
            vec![Name::from_string("elems"), Name::from_string("complete")],
        )?;

        Ok(())
    }

    /// Register the small, fully-constructive propositional helpers used by the
    /// `Perm.nodup_iff` recursion:
    ///
    /// - `Iff.not_congr {p q : Prop} : (p ↔ q) → (¬p ↔ ¬q)`
    /// - `Iff.and_congr {p q r s : Prop} : (p ↔ r) → (q ↔ s) → (p ∧ q ↔ r ∧ s)`
    ///
    /// Both are proved from `Iff.intro` + `And.intro`/`And.left`/`And.right`
    /// with `Not p ≡ p → False` unfolding definitionally.
    fn init_finset_logic_helpers(&mut self) -> Result<(), EnvError> {
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        let not_const = Expr::const_(Name::from_string("Not"), vec![]);
        let and_const = Expr::const_(Name::from_string("And"), vec![]);
        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
        let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
        let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
        let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
        let iff_intro = Expr::const_(Name::from_string("Iff.intro"), vec![]);
        let iff_mp = Expr::const_(Name::from_string("Iff.mp"), vec![]);
        let iff_mpr = Expr::const_(Name::from_string("Iff.mpr"), vec![]);

        let not = |p: Expr| Expr::app(not_const.clone(), p);
        let and_ = |p: Expr, q: Expr| Expr::apps(and_const.clone(), [p, q]);
        let iff = |p: Expr, q: Expr| Expr::apps(iff_const.clone(), [p, q]);

        // ── Iff.not_congr {p q : Prop} : (p ↔ q) → (¬p ↔ ¬q) ────────────────
        // fwd : (p → False) → (q → False) := fun (hnp : ¬p) (hq : q) => hnp (h.mpr hq)
        // bwd : (q → False) → (p → False) := fun (hnq : ¬q) (hp : p) => hnq (h.mp hp)
        {
            let not_congr_type = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(prop.clone());
                let (q_id, q) = b.fresh_local(prop.clone());
                let (h_id, _h) = b.fresh_local(iff(p.clone(), q.clone()));
                let concl = iff(not(p.clone()), not(q.clone()));
                let e = b.mk_pi(h_id, BinderInfo::Default, iff(p.clone(), q.clone()), concl);
                let e = b.mk_pi(q_id, BinderInfo::Implicit, prop.clone(), e);
                let e = b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), e);
                b.finish(e)
            };
            let not_congr_value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(prop.clone());
                let (q_id, q) = b.fresh_local(prop.clone());
                let (h_id, h) = b.fresh_local(iff(p.clone(), q.clone()));
                // fwd : ¬p → ¬q  =  fun (hnp : ¬p) (hq : q) => hnp (Iff.mpr p q h hq)
                let fwd = {
                    let (hnp_id, hnp) = b.fresh_local(not(p.clone()));
                    let (hq_id, hq) = b.fresh_local(q.clone());
                    let hp = Expr::apps(iff_mpr.clone(), [p.clone(), q.clone(), h.clone(), hq]);
                    let body = Expr::app(hnp, hp);
                    let e = b.mk_lam(hq_id, BinderInfo::Default, q.clone(), body);
                    b.mk_lam(hnp_id, BinderInfo::Default, not(p.clone()), e)
                };
                // bwd : ¬q → ¬p  =  fun (hnq : ¬q) (hp : p) => hnq (Iff.mp p q h hp)
                let bwd = {
                    let (hnq_id, hnq) = b.fresh_local(not(q.clone()));
                    let (hp_id, hp) = b.fresh_local(p.clone());
                    let hq = Expr::apps(iff_mp.clone(), [p.clone(), q.clone(), h.clone(), hp]);
                    let body = Expr::app(hnq, hq);
                    let e = b.mk_lam(hp_id, BinderInfo::Default, p.clone(), body);
                    b.mk_lam(hnq_id, BinderInfo::Default, not(q.clone()), e)
                };
                let body = Expr::apps(
                    iff_intro.clone(),
                    [not(p.clone()), not(q.clone()), fwd, bwd],
                );
                let e = b.mk_lam(h_id, BinderInfo::Default, iff(p.clone(), q.clone()), body);
                let e = b.mk_lam(q_id, BinderInfo::Implicit, prop.clone(), e);
                let e = b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Iff.not_congr"),
                level_params: vec![],
                type_: not_congr_type,
                value: not_congr_value,
            })?;
        }

        // ── Iff.and_congr {p q r s : Prop} :
        //      (p ↔ r) → (q ↔ s) → (And p q ↔ And r s) ───────────────────────
        {
            let and_congr_type = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(prop.clone());
                let (q_id, q) = b.fresh_local(prop.clone());
                let (r_id, r) = b.fresh_local(prop.clone());
                let (s_id, s) = b.fresh_local(prop.clone());
                let (h1_id, _h1) = b.fresh_local(iff(p.clone(), r.clone()));
                let (h2_id, _h2) = b.fresh_local(iff(q.clone(), s.clone()));
                let concl = iff(and_(p.clone(), q.clone()), and_(r.clone(), s.clone()));
                let e = b.mk_pi(h2_id, BinderInfo::Default, iff(q.clone(), s.clone()), concl);
                let e = b.mk_pi(h1_id, BinderInfo::Default, iff(p.clone(), r.clone()), e);
                let e = b.mk_pi(s_id, BinderInfo::Implicit, prop.clone(), e);
                let e = b.mk_pi(r_id, BinderInfo::Implicit, prop.clone(), e);
                let e = b.mk_pi(q_id, BinderInfo::Implicit, prop.clone(), e);
                let e = b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), e);
                b.finish(e)
            };
            let and_congr_value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(prop.clone());
                let (q_id, q) = b.fresh_local(prop.clone());
                let (r_id, r) = b.fresh_local(prop.clone());
                let (s_id, s) = b.fresh_local(prop.clone());
                let (h1_id, h1) = b.fresh_local(iff(p.clone(), r.clone()));
                let (h2_id, h2) = b.fresh_local(iff(q.clone(), s.clone()));
                let apq = and_(p.clone(), q.clone());
                let ars = and_(r.clone(), s.clone());
                // fwd : And p q → And r s
                //   = fun (hpq : And p q) =>
                //       And.intro r s (Iff.mp p r h1 (And.left p q hpq))
                //                     (Iff.mp q s h2 (And.right p q hpq))
                let fwd = {
                    let (hpq_id, hpq) = b.fresh_local(apq.clone());
                    let lp = Expr::apps(and_left.clone(), [p.clone(), q.clone(), hpq.clone()]);
                    let rq = Expr::apps(and_right.clone(), [p.clone(), q.clone(), hpq.clone()]);
                    let mr = Expr::apps(iff_mp.clone(), [p.clone(), r.clone(), h1.clone(), lp]);
                    let ms = Expr::apps(iff_mp.clone(), [q.clone(), s.clone(), h2.clone(), rq]);
                    let body = Expr::apps(and_intro.clone(), [r.clone(), s.clone(), mr, ms]);
                    b.mk_lam(hpq_id, BinderInfo::Default, apq.clone(), body)
                };
                // bwd : And r s → And p q
                let bwd = {
                    let (hrs_id, hrs) = b.fresh_local(ars.clone());
                    let lr = Expr::apps(and_left.clone(), [r.clone(), s.clone(), hrs.clone()]);
                    let rs_ = Expr::apps(and_right.clone(), [r.clone(), s.clone(), hrs.clone()]);
                    let mp = Expr::apps(iff_mpr.clone(), [p.clone(), r.clone(), h1.clone(), lr]);
                    let mq = Expr::apps(iff_mpr.clone(), [q.clone(), s.clone(), h2.clone(), rs_]);
                    let body = Expr::apps(and_intro.clone(), [p.clone(), q.clone(), mp, mq]);
                    b.mk_lam(hrs_id, BinderInfo::Default, ars.clone(), body)
                };
                let body = Expr::apps(iff_intro.clone(), [apq.clone(), ars.clone(), fwd, bwd]);
                let e = b.mk_lam(h2_id, BinderInfo::Default, iff(q.clone(), s.clone()), body);
                let e = b.mk_lam(h1_id, BinderInfo::Default, iff(p.clone(), r.clone()), e);
                let e = b.mk_lam(s_id, BinderInfo::Implicit, prop.clone(), e);
                let e = b.mk_lam(r_id, BinderInfo::Implicit, prop.clone(), e);
                let e = b.mk_lam(q_id, BinderInfo::Implicit, prop.clone(), e);
                let e = b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Iff.and_congr"),
                level_params: vec![],
                type_: and_congr_type,
                value: and_congr_value,
            })?;
        }

        Ok(())
    }

    /// Register `List.nodup_cons_iff {α} (a : α) (l : List α) :
    /// Iff (List.Nodup (a :: l)) (And (¬ List.Mem a l) (List.Nodup l))`.
    ///
    /// The forward direction destructs the `List.Nodup (a::l)` proof with
    /// `List.Nodup.casesOn`, using an index-generalized motive built from
    /// `List.casesOn` (mirroring the `List.mem_cons_iff` technique): the motive
    /// maps `[]` to `True` (the unreachable nil branch) and `hd :: tl` to
    /// `And (¬ Mem hd tl) (Nodup tl)`, so the cons case is inhabited by
    /// `And.intro hm hn`. The backward direction is `List.Nodup.cons`.
    fn init_list_nodup_cons_iff(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let list_cons = Expr::const_(Name::from_string("List.cons"), vec![u_level.clone()]);
        let mem_const = Expr::const_(Name::from_string("List.Mem"), vec![u_level.clone()]);
        let nodup_const = Expr::const_(Name::from_string("List.Nodup"), vec![u_level.clone()]);
        let nodup_cons = Expr::const_(Name::from_string("List.Nodup.cons"), vec![u_level.clone()]);
        // `List.Nodup` is a `Prop` with two constructors → small elimination
        // into `Prop`; `List.Nodup.casesOn` carries only the inductive level `u`.
        let nodup_cases = Expr::const_(
            Name::from_string("List.Nodup.casesOn"),
            vec![u_level.clone()],
        );
        // `List.casesOn.{1,u}` — computing a `Prop` (Sort 0 ⇒ w = 1), exactly as
        // in `List.mem_cons_iff`.
        let list_cases = Expr::const_(
            Name::from_string("List.casesOn"),
            vec![Level::succ(Level::zero()), u_level.clone()],
        );

        let not_const = Expr::const_(Name::from_string("Not"), vec![]);
        let and_const = Expr::const_(Name::from_string("And"), vec![]);
        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
        let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
        let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
        let iff_intro = Expr::const_(Name::from_string("Iff.intro"), vec![]);
        let true_const = Expr::const_(Name::from_string("True"), vec![]);
        let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);

        let list_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
        let cons_of = |a: &Expr, x: Expr, l: Expr| Expr::apps(list_cons.clone(), [a.clone(), x, l]);
        let mem = |a: &Expr, x: Expr, l: Expr| Expr::apps(mem_const.clone(), [a.clone(), x, l]);
        let nodup = |a: &Expr, l: Expr| Expr::apps(nodup_const.clone(), [a.clone(), l]);
        let not = |p: Expr| Expr::app(not_const.clone(), p);
        let and_ = |p: Expr, q: Expr| Expr::apps(and_const.clone(), [p, q]);
        let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
        let iff = |p: Expr, q: Expr| Expr::apps(iff_const.clone(), [p, q]);

        let nodup_cons_iff_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (l_id, l) = b.fresh_local(list_of(&alpha));
            let lhs = nodup(&alpha, cons_of(&alpha, a.clone(), l.clone()));
            let rhs = and_(
                not(mem(&alpha, a.clone(), l.clone())),
                nodup(&alpha, l.clone()),
            );
            let concl = iff(lhs, rhs);
            let e = b.mk_pi(l_id, BinderInfo::Default, list_of(&alpha), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let nodup_cons_iff_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (l_id, l) = b.fresh_local(list_of(&alpha));

            let lhs = nodup(&alpha, cons_of(&alpha, a.clone(), l.clone()));
            let rhs = and_(
                not(mem(&alpha, a.clone(), l.clone())),
                nodup(&alpha, l.clone()),
            );

            // P : List α → Prop :=
            //   fun lst => List.casesOn.{1,u} α (fun _ => Prop) True
            //                (fun hd tl => And (¬ Mem hd tl) (Nodup tl)) lst
            let p_fun = {
                let (lst_id, lst) = b.fresh_local(list_of(&alpha));
                let cm = {
                    let (z_id, _z) = b.fresh_local(list_of(&alpha));
                    b.mk_lam(z_id, BinderInfo::Default, list_of(&alpha), prop.clone())
                };
                let cons_branch = {
                    let (hd_id, hd) = b.fresh_local(alpha.clone());
                    let (tl_id, tl) = b.fresh_local(list_of(&alpha));
                    let body = and_(
                        not(mem(&alpha, hd.clone(), tl.clone())),
                        nodup(&alpha, tl.clone()),
                    );
                    let e = b.mk_lam(tl_id, BinderInfo::Default, list_of(&alpha), body);
                    b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), e)
                };
                // Lean-faithful casesOn order: motive, major, then minors.
                let body = Expr::apps(
                    list_cases.clone(),
                    [
                        alpha.clone(),
                        cm,
                        lst.clone(),
                        true_const.clone(), // nil branch (unreachable for a::l)
                        cons_branch,
                    ],
                );
                b.mk_lam(lst_id, BinderInfo::Default, list_of(&alpha), body)
            };

            // forward : Nodup (a::l) → And (¬ Mem a l) (Nodup l)
            //   = fun hnd => List.Nodup.casesOn α
            //        (motive := fun lst _ => P lst)
            //        (a::l) hnd
            //        (nil  := True.intro)
            //        (cons := fun {hd} {tl} (hm : ¬ Mem hd tl) (hn : Nodup tl) =>
            //                    And.intro (¬ Mem hd tl) (Nodup tl) hm hn)
            let forward = {
                let (hnd_id, hnd) = b.fresh_local(lhs.clone());
                // motive: fun (lst : List α) (_ : Nodup lst) => P lst
                let motive = {
                    let (m_lst_id, m_lst) = b.fresh_local(list_of(&alpha));
                    let (m_h_id, _m_h) = b.fresh_local(nodup(&alpha, m_lst.clone()));
                    let body = Expr::app(p_fun.clone(), m_lst.clone());
                    let e = b.mk_lam(
                        m_h_id,
                        BinderInfo::Default,
                        nodup(&alpha, m_lst.clone()),
                        body,
                    );
                    b.mk_lam(m_lst_id, BinderInfo::Default, list_of(&alpha), e)
                };
                // nil minor : P [] = True, inhabited by True.intro
                let nil_minor = true_intro.clone();
                // cons minor : fun {hd}{tl} (hm)(hn) => And.intro _ _ hm hn
                // `List.Nodup.cons` has implicit {a}{l}; casesOn presents them as
                // the leading (implicit) minor binders.
                let cons_minor = {
                    let (hd_id, hd) = b.fresh_local(alpha.clone());
                    let (tl_id, tl) = b.fresh_local(list_of(&alpha));
                    let not_mem = not(mem(&alpha, hd.clone(), tl.clone()));
                    let nodup_tl = nodup(&alpha, tl.clone());
                    let (hm_id, hm) = b.fresh_local(not_mem.clone());
                    let (hn_id, hn) = b.fresh_local(nodup_tl.clone());
                    let body = Expr::apps(
                        and_intro.clone(),
                        [not_mem.clone(), nodup_tl.clone(), hm, hn],
                    );
                    let e = b.mk_lam(hn_id, BinderInfo::Default, nodup_tl, body);
                    let e = b.mk_lam(hm_id, BinderInfo::Default, not_mem, e);
                    let e = b.mk_lam(tl_id, BinderInfo::Implicit, list_of(&alpha), e);
                    b.mk_lam(hd_id, BinderInfo::Implicit, alpha.clone(), e)
                };
                // Lean-faithful casesOn order: motive, indices, major, minors.
                let body = Expr::apps(
                    nodup_cases.clone(),
                    [
                        alpha.clone(),
                        motive,
                        cons_of(&alpha, a.clone(), l.clone()), // index (a::l)
                        hnd.clone(),
                        nil_minor,
                        cons_minor,
                    ],
                );
                b.mk_lam(hnd_id, BinderInfo::Default, lhs.clone(), body)
            };

            // backward : And (¬ Mem a l) (Nodup l) → Nodup (a::l)
            //   = fun hand => @List.Nodup.cons α a l (And.left _ _ hand) (And.right _ _ hand)
            let backward = {
                let (hand_id, hand) = b.fresh_local(rhs.clone());
                let not_mem = not(mem(&alpha, a.clone(), l.clone()));
                let nodup_l = nodup(&alpha, l.clone());
                let hm = Expr::apps(
                    and_left.clone(),
                    [not_mem.clone(), nodup_l.clone(), hand.clone()],
                );
                let hn = Expr::apps(
                    and_right.clone(),
                    [not_mem.clone(), nodup_l.clone(), hand.clone()],
                );
                let body = Expr::apps(
                    nodup_cons.clone(),
                    [alpha.clone(), a.clone(), l.clone(), hm, hn],
                );
                b.mk_lam(hand_id, BinderInfo::Default, rhs.clone(), body)
            };

            let body = Expr::apps(
                iff_intro.clone(),
                [lhs.clone(), rhs.clone(), forward, backward],
            );
            let e = b.mk_lam(l_id, BinderInfo::Default, list_of(&alpha), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("List.nodup_cons_iff"),
            level_params: vec![u.clone()],
            type_: nodup_cons_iff_type,
            value: nodup_cons_iff_value,
        })?;

        Ok(())
    }

    /// Register `Or.not_or_iff_and_not {p q : Prop} :
    /// ¬(p ∨ q) ↔ (¬p ∧ ¬q)` (constructive De Morgan), and
    /// `List.not_mem_cons_iff {α} (a x : α) (l) :
    /// ¬ List.Mem a (x :: l) ↔ (¬(a = x) ∧ ¬ List.Mem a l)`.
    fn init_not_mem_cons_iff(&mut self) -> Result<(), EnvError> {
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        let or_const = Expr::const_(Name::from_string("Or"), vec![]);
        let or_inl = Expr::const_(Name::from_string("Or.inl"), vec![]);
        let or_inr = Expr::const_(Name::from_string("Or.inr"), vec![]);
        let or_cases = Expr::const_(Name::from_string("Or.casesOn"), vec![]);
        let and_const = Expr::const_(Name::from_string("And"), vec![]);
        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
        let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
        let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
        let not_const = Expr::const_(Name::from_string("Not"), vec![]);
        let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
        let iff_intro = Expr::const_(Name::from_string("Iff.intro"), vec![]);

        let not = |p: Expr| Expr::app(not_const.clone(), p);
        let or_ = |p: Expr, q: Expr| Expr::apps(or_const.clone(), [p, q]);
        let and_ = |p: Expr, q: Expr| Expr::apps(and_const.clone(), [p, q]);
        let iff = |p: Expr, q: Expr| Expr::apps(iff_const.clone(), [p, q]);

        // ── Or.not_or_iff_and_not {p q : Prop} : ¬(p ∨ q) ↔ (¬p ∧ ¬q) ────────
        {
            let nm_type = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(prop.clone());
                let (q_id, q) = b.fresh_local(prop.clone());
                let concl = iff(
                    not(or_(p.clone(), q.clone())),
                    and_(not(p.clone()), not(q.clone())),
                );
                let e = b.mk_pi(q_id, BinderInfo::Implicit, prop.clone(), concl);
                let e = b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), e);
                b.finish(e)
            };
            let nm_value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(prop.clone());
                let (q_id, q) = b.fresh_local(prop.clone());
                let opq = or_(p.clone(), q.clone());
                let lhs = not(opq.clone());
                let rhs = and_(not(p.clone()), not(q.clone()));
                // fwd : ¬(p∨q) → ¬p ∧ ¬q
                //   = fun h => And.intro (¬p)(¬q)
                //        (fun hp => h (Or.inl p q hp)) (fun hq => h (Or.inr p q hq))
                let fwd = {
                    let (h_id, h) = b.fresh_local(lhs.clone());
                    let np = {
                        let (hp_id, hp) = b.fresh_local(p.clone());
                        let inj = Expr::apps(or_inl.clone(), [p.clone(), q.clone(), hp]);
                        let body = Expr::app(h.clone(), inj);
                        b.mk_lam(hp_id, BinderInfo::Default, p.clone(), body)
                    };
                    let nq = {
                        let (hq_id, hq) = b.fresh_local(q.clone());
                        let inj = Expr::apps(or_inr.clone(), [p.clone(), q.clone(), hq]);
                        let body = Expr::app(h.clone(), inj);
                        b.mk_lam(hq_id, BinderInfo::Default, q.clone(), body)
                    };
                    let body =
                        Expr::apps(and_intro.clone(), [not(p.clone()), not(q.clone()), np, nq]);
                    b.mk_lam(h_id, BinderInfo::Default, lhs.clone(), body)
                };
                // bwd : (¬p ∧ ¬q) → ¬(p∨q)
                //   = fun h => fun hpq => Or.casesOn p q (fun _ => False)
                //        (fun hp => And.left _ _ h hp) (fun hq => And.right _ _ h hq) hpq
                let bwd = {
                    let (h_id, h) = b.fresh_local(rhs.clone());
                    let (hpq_id, hpq) = b.fresh_local(opq.clone());
                    let or_motive = {
                        let (z_id, _z) = b.fresh_local(opq.clone());
                        b.mk_lam(z_id, BinderInfo::Default, opq.clone(), false_const.clone())
                    };
                    let inl = {
                        let (hp_id, hp) = b.fresh_local(p.clone());
                        let np = Expr::apps(
                            and_left.clone(),
                            [not(p.clone()), not(q.clone()), h.clone()],
                        );
                        let body = Expr::app(np, hp);
                        b.mk_lam(hp_id, BinderInfo::Default, p.clone(), body)
                    };
                    let inr = {
                        let (hq_id, hq) = b.fresh_local(q.clone());
                        let nq = Expr::apps(
                            and_right.clone(),
                            [not(p.clone()), not(q.clone()), h.clone()],
                        );
                        let body = Expr::app(nq, hq);
                        b.mk_lam(hq_id, BinderInfo::Default, q.clone(), body)
                    };
                    // Lean-faithful casesOn order: motive, major, then minors.
                    let cased = Expr::apps(
                        or_cases.clone(),
                        [p.clone(), q.clone(), or_motive, hpq.clone(), inl, inr],
                    );
                    let inner = b.mk_lam(hpq_id, BinderInfo::Default, opq.clone(), cased);
                    b.mk_lam(h_id, BinderInfo::Default, rhs.clone(), inner)
                };
                let body = Expr::apps(iff_intro.clone(), [lhs.clone(), rhs.clone(), fwd, bwd]);
                let e = b.mk_lam(q_id, BinderInfo::Implicit, prop.clone(), body);
                let e = b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Or.not_or_iff_and_not"),
                level_params: vec![],
                type_: nm_type,
                value: nm_value,
            })?;
        }

        // ── List.not_mem_cons_iff {α} (a x : α) (l) :
        //      ¬ Mem a (x::l) ↔ (¬(a=x) ∧ ¬Mem a l) ──────────────────────────
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let list_cons = Expr::const_(Name::from_string("List.cons"), vec![u_level.clone()]);
        let mem_const = Expr::const_(Name::from_string("List.Mem"), vec![u_level.clone()]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let iff_trans = Expr::const_(Name::from_string("Iff.trans"), vec![]);
        let not_congr = Expr::const_(Name::from_string("Iff.not_congr"), vec![]);
        let not_or_iff = Expr::const_(Name::from_string("Or.not_or_iff_and_not"), vec![]);
        let mem_cons_iff_c = Expr::const_(
            Name::from_string("List.mem_cons_iff"),
            vec![u_level.clone()],
        );

        let list_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
        let cons_of = |a: &Expr, x: Expr, l: Expr| Expr::apps(list_cons.clone(), [a.clone(), x, l]);
        let mem = |a: &Expr, x: Expr, l: Expr| Expr::apps(mem_const.clone(), [a.clone(), x, l]);
        let eq_ = |a: &Expr, x: Expr, y: Expr| Expr::apps(eq_const.clone(), [a.clone(), x, y]);

        let nmci_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (l_id, l) = b.fresh_local(list_of(&alpha));
            let lhs = not(mem(
                &alpha,
                a.clone(),
                cons_of(&alpha, x.clone(), l.clone()),
            ));
            let rhs = and_(
                not(eq_(&alpha, a.clone(), x.clone())),
                not(mem(&alpha, a.clone(), l.clone())),
            );
            let concl = iff(lhs, rhs);
            let e = b.mk_pi(l_id, BinderInfo::Default, list_of(&alpha), concl);
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let nmci_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (l_id, l) = b.fresh_local(list_of(&alpha));

            let mem_xl = mem(&alpha, a.clone(), cons_of(&alpha, x.clone(), l.clone()));
            let eqax = eq_(&alpha, a.clone(), x.clone());
            let mem_al = mem(&alpha, a.clone(), l.clone());
            let or_disj = or_(eqax.clone(), mem_al.clone());
            let lhs = not(mem_xl.clone());
            let mid = not(or_disj.clone());
            let rhs = and_(not(eqax.clone()), not(mem_al.clone()));

            // mci : Mem a (x::l) ↔ (a=x) ∨ Mem a l
            let mci = Expr::apps(
                mem_cons_iff_c.clone(),
                [alpha.clone(), a.clone(), x.clone(), l.clone()],
            );
            // step1 : ¬Mem a (x::l) ↔ ¬((a=x) ∨ Mem a l)
            let step1 = Expr::apps(not_congr.clone(), [mem_xl.clone(), or_disj.clone(), mci]);
            // step2 : ¬((a=x)∨Mem a l) ↔ (¬(a=x) ∧ ¬Mem a l)
            let step2 = Expr::apps(not_or_iff.clone(), [eqax.clone(), mem_al.clone()]);
            // body = Iff.trans step1 step2
            let body = Expr::apps(
                iff_trans.clone(),
                [lhs.clone(), mid.clone(), rhs.clone(), step1, step2],
            );
            let e = b.mk_lam(l_id, BinderInfo::Default, list_of(&alpha), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("List.not_mem_cons_iff"),
            level_params: vec![u.clone()],
            type_: nmci_type,
            value: nmci_value,
        })?;

        Ok(())
    }

    /// Register `List.nodup_swap_inner {α} (x y : α) (l : List α) :`
    /// `((¬(y=x) ∧ ¬Mem y l) ∧ (¬Mem x l ∧ Nodup l)) ↔`
    /// `((¬(x=y) ∧ ¬Mem x l) ∧ (¬Mem y l ∧ Nodup l))`.
    ///
    /// Pure propositional shuffle: the only non-projection step is
    /// `¬(y=x) → ¬(x=y)` (resp. its converse), discharged by composing with
    /// `Eq.symm`. Everything else is `And.intro`/`And.left`/`And.right`.
    fn init_nodup_swap_inner(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let mem_const = Expr::const_(Name::from_string("List.Mem"), vec![u_level.clone()]);
        let nodup_const = Expr::const_(Name::from_string("List.Nodup"), vec![u_level.clone()]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let eq_symm = Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(u_level.clone())],
        );
        let not_const = Expr::const_(Name::from_string("Not"), vec![]);
        let and_const = Expr::const_(Name::from_string("And"), vec![]);
        let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
        let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
        let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
        let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
        let iff_intro = Expr::const_(Name::from_string("Iff.intro"), vec![]);

        let list_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
        let mem = |a: &Expr, x: Expr, l: Expr| Expr::apps(mem_const.clone(), [a.clone(), x, l]);
        let nodup = |a: &Expr, l: Expr| Expr::apps(nodup_const.clone(), [a.clone(), l]);
        let eq_ = |a: &Expr, x: Expr, y: Expr| Expr::apps(eq_const.clone(), [a.clone(), x, y]);
        let not = |p: Expr| Expr::app(not_const.clone(), p);
        let and_ = |p: Expr, q: Expr| Expr::apps(and_const.clone(), [p, q]);
        let iff = |p: Expr, q: Expr| Expr::apps(iff_const.clone(), [p, q]);

        let swap_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (y_id, y) = b.fresh_local(alpha.clone());
            let (l_id, l) = b.fresh_local(list_of(&alpha));
            let nyx = not(eq_(&alpha, y.clone(), x.clone()));
            let nxy = not(eq_(&alpha, x.clone(), y.clone()));
            let nm_y_l = not(mem(&alpha, y.clone(), l.clone()));
            let nm_x_l = not(mem(&alpha, x.clone(), l.clone()));
            let nd_l = nodup(&alpha, l.clone());
            let lhs = and_(
                and_(nyx.clone(), nm_y_l.clone()),
                and_(nm_x_l.clone(), nd_l.clone()),
            );
            let rhs = and_(
                and_(nxy.clone(), nm_x_l.clone()),
                and_(nm_y_l.clone(), nd_l.clone()),
            );
            let concl = iff(lhs, rhs);
            let e = b.mk_pi(l_id, BinderInfo::Default, list_of(&alpha), concl);
            let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let swap_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (y_id, y) = b.fresh_local(alpha.clone());
            let (l_id, l) = b.fresh_local(list_of(&alpha));

            let nyx = not(eq_(&alpha, y.clone(), x.clone()));
            let nxy = not(eq_(&alpha, x.clone(), y.clone()));
            let nm_y_l = not(mem(&alpha, y.clone(), l.clone()));
            let nm_x_l = not(mem(&alpha, x.clone(), l.clone()));
            let nd_l = nodup(&alpha, l.clone());
            let lhs = and_(
                and_(nyx.clone(), nm_y_l.clone()),
                and_(nm_x_l.clone(), nd_l.clone()),
            );
            let rhs = and_(
                and_(nxy.clone(), nm_x_l.clone()),
                and_(nm_y_l.clone(), nd_l.clone()),
            );

            // negsym {p q : α} : ¬(p=q) → ¬(q=p)
            //   = fun (nh : ¬(p=q)) (e : q=p) => nh (Eq.symm α q p e)
            let neg_sym = |b: &mut EnvDeclBuilder, p: &Expr, q: &Expr, nh: Expr| -> Expr {
                let (e_id, e_) = b.fresh_local(eq_(&alpha, q.clone(), p.clone()));
                // Eq.symm α q p e : p = q
                let sym = Expr::apps(eq_symm.clone(), [alpha.clone(), q.clone(), p.clone(), e_]);
                let body = Expr::app(nh, sym);
                b.mk_lam(
                    e_id,
                    BinderInfo::Default,
                    eq_(&alpha, q.clone(), p.clone()),
                    body,
                )
            };

            // fwd : lhs → rhs
            //   given h : (nyx ∧ nm_y_l) ∧ (nm_x_l ∧ nd_l)
            //   produce  (nxy ∧ nm_x_l) ∧ (nm_y_l ∧ nd_l)
            let fwd = {
                let (h_id, h) = b.fresh_local(lhs.clone());
                let a1 = and_(nyx.clone(), nm_y_l.clone());
                let a2 = and_(nm_x_l.clone(), nd_l.clone());
                let left = Expr::apps(and_left.clone(), [a1.clone(), a2.clone(), h.clone()]); // nyx ∧ nm_y_l
                let right = Expr::apps(and_right.clone(), [a1.clone(), a2.clone(), h.clone()]); // nm_x_l ∧ nd_l
                let h_nyx = Expr::apps(
                    and_left.clone(),
                    [nyx.clone(), nm_y_l.clone(), left.clone()],
                );
                let h_nm_y = Expr::apps(
                    and_right.clone(),
                    [nyx.clone(), nm_y_l.clone(), left.clone()],
                );
                let h_nm_x = Expr::apps(
                    and_left.clone(),
                    [nm_x_l.clone(), nd_l.clone(), right.clone()],
                );
                let h_nd = Expr::apps(
                    and_right.clone(),
                    [nm_x_l.clone(), nd_l.clone(), right.clone()],
                );
                let h_nxy = neg_sym(&mut b, &y, &x, h_nyx); // ¬(y=x) → ¬(x=y)
                                                            // out1 = And.intro nxy nm_x_l h_nxy h_nm_x
                let out1 = Expr::apps(
                    and_intro.clone(),
                    [nxy.clone(), nm_x_l.clone(), h_nxy, h_nm_x],
                );
                // out2 = And.intro nm_y_l nd_l h_nm_y h_nd
                let out2 = Expr::apps(
                    and_intro.clone(),
                    [nm_y_l.clone(), nd_l.clone(), h_nm_y, h_nd],
                );
                let b1 = and_(nxy.clone(), nm_x_l.clone());
                let b2 = and_(nm_y_l.clone(), nd_l.clone());
                let body = Expr::apps(and_intro.clone(), [b1, b2, out1, out2]);
                b.mk_lam(h_id, BinderInfo::Default, lhs.clone(), body)
            };

            // bwd : rhs → lhs (mirror image)
            let bwd = {
                let (h_id, h) = b.fresh_local(rhs.clone());
                let b1 = and_(nxy.clone(), nm_x_l.clone());
                let b2 = and_(nm_y_l.clone(), nd_l.clone());
                let left = Expr::apps(and_left.clone(), [b1.clone(), b2.clone(), h.clone()]); // nxy ∧ nm_x_l
                let right = Expr::apps(and_right.clone(), [b1.clone(), b2.clone(), h.clone()]); // nm_y_l ∧ nd_l
                let h_nxy = Expr::apps(
                    and_left.clone(),
                    [nxy.clone(), nm_x_l.clone(), left.clone()],
                );
                let h_nm_x = Expr::apps(
                    and_right.clone(),
                    [nxy.clone(), nm_x_l.clone(), left.clone()],
                );
                let h_nm_y = Expr::apps(
                    and_left.clone(),
                    [nm_y_l.clone(), nd_l.clone(), right.clone()],
                );
                let h_nd = Expr::apps(
                    and_right.clone(),
                    [nm_y_l.clone(), nd_l.clone(), right.clone()],
                );
                let h_nyx = neg_sym(&mut b, &x, &y, h_nxy); // ¬(x=y) → ¬(y=x)
                let out1 = Expr::apps(
                    and_intro.clone(),
                    [nyx.clone(), nm_y_l.clone(), h_nyx, h_nm_y],
                );
                let out2 = Expr::apps(
                    and_intro.clone(),
                    [nm_x_l.clone(), nd_l.clone(), h_nm_x, h_nd],
                );
                let a1 = and_(nyx.clone(), nm_y_l.clone());
                let a2 = and_(nm_x_l.clone(), nd_l.clone());
                let body = Expr::apps(and_intro.clone(), [a1, a2, out1, out2]);
                b.mk_lam(h_id, BinderInfo::Default, rhs.clone(), body)
            };

            let body = Expr::apps(iff_intro.clone(), [lhs.clone(), rhs.clone(), fwd, bwd]);
            let e = b.mk_lam(l_id, BinderInfo::Default, list_of(&alpha), body);
            let e = b.mk_lam(y_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("List.nodup_swap_inner"),
            level_params: vec![u.clone()],
            type_: swap_type,
            value: swap_value,
        })?;

        Ok(())
    }

    /// Register `List.Perm.nodup_iff {α} {l₁ l₂ : List α} :
    /// Perm l₁ l₂ → Iff (List.Nodup l₁) (List.Nodup l₂)`, proved by
    /// `List.Perm.rec` with motive `λ m₁ m₂ _ => Iff (Nodup m₁) (Nodup m₂)`.
    ///
    /// Case structure (mirrors `List.Perm.mem_iff`):
    /// - `nil`: `Iff.rfl`.
    /// - `cons x hp ih`: unfold both sides with `List.nodup_cons_iff`, then
    ///   transport the conjunction with `Iff.and_congr` over
    ///   `Iff.not_congr (List.Perm.mem_iff x hp)` (the `¬Mem` premise) and `ih`
    ///   (the `Nodup` tail).
    /// - `swap x y l`: unfold both `Nodup (y::x::l)` and `Nodup (x::y::l)` two
    ///   layers deep with `nodup_cons_iff` and the membership De-Morgan helper
    ///   `List.not_mem_cons_iff`, then reconcile the two nested conjunctions
    ///   with the pure And/Eq-symmetry shuffle `List.nodup_swap_inner`.
    /// - `trans h₁ h₂ ih₁ ih₂`: `Iff.trans ih₁ ih₂`.
    fn init_perm_nodup_iff(&mut self) -> Result<(), EnvError> {
        // First register the two swap-specific helper lemmas.
        self.init_not_mem_cons_iff()?;
        self.init_nodup_swap_inner()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let list_cons = Expr::const_(Name::from_string("List.cons"), vec![u_level.clone()]);
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u_level.clone()]);
        let mem_const = Expr::const_(Name::from_string("List.Mem"), vec![u_level.clone()]);
        let nodup_const = Expr::const_(Name::from_string("List.Nodup"), vec![u_level.clone()]);
        let perm_const = Expr::const_(Name::from_string("List.Perm"), vec![u_level.clone()]);
        let perm_rec = Expr::const_(Name::from_string("List.Perm.rec"), vec![u_level.clone()]);

        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
        let not_const = Expr::const_(Name::from_string("Not"), vec![]);
        let and_const = Expr::const_(Name::from_string("And"), vec![]);
        let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
        let iff_rfl = Expr::const_(Name::from_string("Iff.rfl"), vec![]);
        let iff_symm = Expr::const_(Name::from_string("Iff.symm"), vec![]);
        let iff_trans = Expr::const_(Name::from_string("Iff.trans"), vec![]);
        let and_congr = Expr::const_(Name::from_string("Iff.and_congr"), vec![]);
        let not_congr = Expr::const_(Name::from_string("Iff.not_congr"), vec![]);
        let nodup_cons_iff_c = Expr::const_(
            Name::from_string("List.nodup_cons_iff"),
            vec![u_level.clone()],
        );
        let perm_mem_iff_c = Expr::const_(
            Name::from_string("List.Perm.mem_iff"),
            vec![u_level.clone()],
        );
        let not_mem_cons_iff_c = Expr::const_(
            Name::from_string("List.not_mem_cons_iff"),
            vec![u_level.clone()],
        );
        let nodup_swap_inner_c = Expr::const_(
            Name::from_string("List.nodup_swap_inner"),
            vec![u_level.clone()],
        );

        let list_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
        let nil_of = |a: &Expr| Expr::app(list_nil.clone(), a.clone());
        let cons_of = |a: &Expr, x: Expr, l: Expr| Expr::apps(list_cons.clone(), [a.clone(), x, l]);
        let mem = |a: &Expr, x: Expr, l: Expr| Expr::apps(mem_const.clone(), [a.clone(), x, l]);
        let nodup = |a: &Expr, l: Expr| Expr::apps(nodup_const.clone(), [a.clone(), l]);
        let perm_rel = |a: &Expr| Expr::app(perm_const.clone(), a.clone());
        let perm =
            |a: &Expr, l1: Expr, l2: Expr| Expr::apps(perm_const.clone(), [a.clone(), l1, l2]);
        let eq_ = |a: &Expr, x: Expr, y: Expr| Expr::apps(eq_const.clone(), [a.clone(), x, y]);
        let not = |p: Expr| Expr::app(not_const.clone(), p);
        let and_ = |p: Expr, q: Expr| Expr::apps(and_const.clone(), [p, q]);
        let iff = |p: Expr, q: Expr| Expr::apps(iff_const.clone(), [p, q]);

        let nodup_iff_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (l1_id, l1) = b.fresh_local(list_of(&alpha));
            let (l2_id, l2) = b.fresh_local(list_of(&alpha));
            let (hp_id, _hp) = b.fresh_local(perm(&alpha, l1.clone(), l2.clone()));
            let concl = iff(nodup(&alpha, l1.clone()), nodup(&alpha, l2.clone()));
            let e = b.mk_pi(
                hp_id,
                BinderInfo::Default,
                perm(&alpha, l1.clone(), l2.clone()),
                concl,
            );
            let e = b.mk_pi(l2_id, BinderInfo::Implicit, list_of(&alpha), e);
            let e = b.mk_pi(l1_id, BinderInfo::Implicit, list_of(&alpha), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let nodup_iff_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());

            // motive : λ (m1 m2 : List α) (_ : Perm m1 m2) => Iff (Nodup m1)(Nodup m2)
            let motive = {
                let (m1_id, m1) = b.fresh_local(list_of(&alpha));
                let (m2_id, m2) = b.fresh_local(list_of(&alpha));
                let (mp_id, _mp) = b.fresh_local(perm(&alpha, m1.clone(), m2.clone()));
                let body = iff(nodup(&alpha, m1.clone()), nodup(&alpha, m2.clone()));
                let e = b.mk_lam(
                    mp_id,
                    BinderInfo::Default,
                    perm(&alpha, m1.clone(), m2.clone()),
                    body,
                );
                let e = b.mk_lam(m2_id, BinderInfo::Default, list_of(&alpha), e);
                b.mk_lam(m1_id, BinderInfo::Default, list_of(&alpha), e)
            };

            // nil minor : Iff (Nodup []) (Nodup []) = @Iff.rfl (Nodup [])
            let m_nil = Expr::app(iff_rfl.clone(), nodup(&alpha, nil_of(&alpha)));

            // cons minor (binder order follows the Lean-faithful ctor:
            // element x first, then {l₁}{l₂}, h, ih)
            let m_cons = {
                let (cx_id, cx) = b.fresh_local(alpha.clone());
                let (cl1_id, cl1) = b.fresh_local(list_of(&alpha));
                let (cl2_id, cl2) = b.fresh_local(list_of(&alpha));
                let (chp_id, chp) = b.fresh_local(perm(&alpha, cl1.clone(), cl2.clone()));
                let ih_ty = iff(nodup(&alpha, cl1.clone()), nodup(&alpha, cl2.clone()));
                let (ih_id, ih) = b.fresh_local(ih_ty.clone());

                let nd_xc1 = nodup(&alpha, cons_of(&alpha, cx.clone(), cl1.clone()));
                let nd_xc2 = nodup(&alpha, cons_of(&alpha, cx.clone(), cl2.clone()));
                let nm1 = not(mem(&alpha, cx.clone(), cl1.clone()));
                let nm2 = not(mem(&alpha, cx.clone(), cl2.clone()));
                let nd1 = nodup(&alpha, cl1.clone());
                let nd2 = nodup(&alpha, cl2.clone());
                let conj1 = and_(nm1.clone(), nd1.clone());
                let conj2 = and_(nm2.clone(), nd2.clone());

                // step1 : Nodup (x::l1) ↔ (¬Mem x l1 ∧ Nodup l1)
                let step1 = Expr::apps(
                    nodup_cons_iff_c.clone(),
                    [alpha.clone(), cx.clone(), cl1.clone()],
                );
                // mem_eq : Mem x l1 ↔ Mem x l2
                let mem_eq = Expr::apps(
                    perm_mem_iff_c.clone(),
                    [
                        alpha.clone(),
                        cx.clone(),
                        cl1.clone(),
                        cl2.clone(),
                        chp.clone(),
                    ],
                );
                // not_eq : ¬Mem x l1 ↔ ¬Mem x l2
                let not_eq = Expr::apps(
                    not_congr.clone(),
                    [
                        mem(&alpha, cx.clone(), cl1.clone()),
                        mem(&alpha, cx.clone(), cl2.clone()),
                        mem_eq,
                    ],
                );
                // mid : conj1 ↔ conj2
                let mid = Expr::apps(
                    and_congr.clone(),
                    [
                        nm1.clone(),
                        nd1.clone(),
                        nm2.clone(),
                        nd2.clone(),
                        not_eq,
                        ih.clone(),
                    ],
                );
                // step3 : conj2 ↔ Nodup (x::l2)  =  Iff.symm (nodup_cons_iff x l2)
                let ncl2 = Expr::apps(
                    nodup_cons_iff_c.clone(),
                    [alpha.clone(), cx.clone(), cl2.clone()],
                );
                let step3 = Expr::apps(iff_symm.clone(), [nd_xc2.clone(), conj2.clone(), ncl2]);
                // inner = trans mid step3 : conj1 ↔ Nodup (x::l2)
                let inner = Expr::apps(
                    iff_trans.clone(),
                    [conj1.clone(), conj2.clone(), nd_xc2.clone(), mid, step3],
                );
                // body = trans step1 inner : Nodup (x::l1) ↔ Nodup (x::l2)
                let body = Expr::apps(
                    iff_trans.clone(),
                    [nd_xc1.clone(), conj1.clone(), nd_xc2.clone(), step1, inner],
                );
                let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let e = b.mk_lam(
                    chp_id,
                    BinderInfo::Default,
                    perm(&alpha, cl1.clone(), cl2.clone()),
                    e,
                );
                let e = b.mk_lam(cl2_id, BinderInfo::Default, list_of(&alpha), e);
                let e = b.mk_lam(cl1_id, BinderInfo::Default, list_of(&alpha), e);
                b.mk_lam(cx_id, BinderInfo::Default, alpha.clone(), e)
            };

            // swap minor : λ (x y : α) (l : List α) =>
            //   Iff (Nodup (y::x::l)) (Nodup (x::y::l))
            let m_swap = {
                let (sx_id, sx) = b.fresh_local(alpha.clone());
                let (sy_id, sy) = b.fresh_local(alpha.clone());
                let (sl_id, sl) = b.fresh_local(list_of(&alpha));

                let xl = cons_of(&alpha, sx.clone(), sl.clone());
                let yl = cons_of(&alpha, sy.clone(), sl.clone());
                let yxl = cons_of(&alpha, sy.clone(), xl.clone());
                let xyl = cons_of(&alpha, sx.clone(), yl.clone());

                let nd_yxl = nodup(&alpha, yxl.clone());
                let nd_xyl = nodup(&alpha, xyl.clone());
                let nd_xl = nodup(&alpha, xl.clone());
                let nd_yl = nodup(&alpha, yl.clone());
                let nd_l = nodup(&alpha, sl.clone());

                // Per-side shapes:
                //   ¬Mem y (x::l), ¬Mem x (y::l)
                let nm_y_xl = not(mem(&alpha, sy.clone(), xl.clone()));
                let nm_x_yl = not(mem(&alpha, sx.clone(), yl.clone()));
                // De-Morgan unfolded shapes:
                //   ¬(y=x) ∧ ¬Mem y l   and   ¬(x=y) ∧ ¬Mem x l
                let nyx = not(eq_(&alpha, sy.clone(), sx.clone()));
                let nxy = not(eq_(&alpha, sx.clone(), sy.clone()));
                let nm_y_l = not(mem(&alpha, sy.clone(), sl.clone()));
                let nm_x_l = not(mem(&alpha, sx.clone(), sl.clone()));
                let dm_y = and_(nyx.clone(), nm_y_l.clone());
                let dm_x = and_(nxy.clone(), nm_x_l.clone());

                // Left side full unfold:
                // Nodup (y::x::l)
                //  ↔ ¬Mem y (x::l) ∧ Nodup (x::l)           [nodup_cons_iff y (x::l)]
                //  ↔ (¬(y=x) ∧ ¬Mem y l) ∧ Nodup (x::l)     [and_congr not_mem_cons_iff rfl]
                //  ↔ (¬(y=x) ∧ ¬Mem y l) ∧ (¬Mem x l ∧ Nodup l) [and_congr rfl nodup_cons_iff x l]
                let conj_y_xl = and_(nm_y_xl.clone(), nd_xl.clone());
                let conj_dm_y_xl = and_(dm_y.clone(), nd_xl.clone());
                let conj_xl_inner = and_(nm_x_l.clone(), nd_l.clone());
                let left_full = and_(dm_y.clone(), conj_xl_inner.clone());

                // sA : Nodup (y::x::l) ↔ ¬Mem y (x::l) ∧ Nodup (x::l)
                let s_a = Expr::apps(
                    nodup_cons_iff_c.clone(),
                    [alpha.clone(), sy.clone(), xl.clone()],
                );
                // dmY_iff : ¬Mem y (x::l) ↔ (¬(y=x) ∧ ¬Mem y l)
                let dm_y_iff = Expr::apps(
                    not_mem_cons_iff_c.clone(),
                    [alpha.clone(), sy.clone(), sx.clone(), sl.clone()],
                );
                // sB : (¬Mem y (x::l) ∧ Nodup (x::l)) ↔ (dm_y ∧ Nodup (x::l))
                let s_b = Expr::apps(
                    and_congr.clone(),
                    [
                        nm_y_xl.clone(),
                        nd_xl.clone(),
                        dm_y.clone(),
                        nd_xl.clone(),
                        dm_y_iff,
                        Expr::app(iff_rfl.clone(), nd_xl.clone()),
                    ],
                );
                // xl_iff : Nodup (x::l) ↔ (¬Mem x l ∧ Nodup l)
                let xl_iff = Expr::apps(
                    nodup_cons_iff_c.clone(),
                    [alpha.clone(), sx.clone(), sl.clone()],
                );
                // sC : (dm_y ∧ Nodup (x::l)) ↔ (dm_y ∧ (¬Mem x l ∧ Nodup l))
                let s_c = Expr::apps(
                    and_congr.clone(),
                    [
                        dm_y.clone(),
                        nd_xl.clone(),
                        dm_y.clone(),
                        conj_xl_inner.clone(),
                        Expr::app(iff_rfl.clone(), dm_y.clone()),
                        xl_iff,
                    ],
                );
                // left = trans sA (trans sB sC) : Nodup(y::x::l) ↔ left_full
                let left_bc = Expr::apps(
                    iff_trans.clone(),
                    [
                        conj_y_xl.clone(),
                        conj_dm_y_xl.clone(),
                        left_full.clone(),
                        s_b,
                        s_c,
                    ],
                );
                let left = Expr::apps(
                    iff_trans.clone(),
                    [
                        nd_yxl.clone(),
                        conj_y_xl.clone(),
                        left_full.clone(),
                        s_a,
                        left_bc,
                    ],
                );

                // Right side full unfold (symmetric, x↔y):
                // Nodup (x::y::l) ↔ (¬(x=y) ∧ ¬Mem x l) ∧ (¬Mem y l ∧ Nodup l)
                let conj_x_yl = and_(nm_x_yl.clone(), nd_yl.clone());
                let conj_dm_x_yl = and_(dm_x.clone(), nd_yl.clone());
                let conj_yl_inner = and_(nm_y_l.clone(), nd_l.clone());
                let right_full = and_(dm_x.clone(), conj_yl_inner.clone());

                let r_a = Expr::apps(
                    nodup_cons_iff_c.clone(),
                    [alpha.clone(), sx.clone(), yl.clone()],
                );
                let dm_x_iff = Expr::apps(
                    not_mem_cons_iff_c.clone(),
                    [alpha.clone(), sx.clone(), sy.clone(), sl.clone()],
                );
                let r_b = Expr::apps(
                    and_congr.clone(),
                    [
                        nm_x_yl.clone(),
                        nd_yl.clone(),
                        dm_x.clone(),
                        nd_yl.clone(),
                        dm_x_iff,
                        Expr::app(iff_rfl.clone(), nd_yl.clone()),
                    ],
                );
                let yl_iff = Expr::apps(
                    nodup_cons_iff_c.clone(),
                    [alpha.clone(), sy.clone(), sl.clone()],
                );
                let r_c = Expr::apps(
                    and_congr.clone(),
                    [
                        dm_x.clone(),
                        nd_yl.clone(),
                        dm_x.clone(),
                        conj_yl_inner.clone(),
                        Expr::app(iff_rfl.clone(), dm_x.clone()),
                        yl_iff,
                    ],
                );
                let right_bc = Expr::apps(
                    iff_trans.clone(),
                    [
                        conj_x_yl.clone(),
                        conj_dm_x_yl.clone(),
                        right_full.clone(),
                        r_b,
                        r_c,
                    ],
                );
                // right : Nodup(x::y::l) ↔ right_full
                let right = Expr::apps(
                    iff_trans.clone(),
                    [
                        nd_xyl.clone(),
                        conj_x_yl.clone(),
                        right_full.clone(),
                        r_a,
                        right_bc,
                    ],
                );
                // right_symm : right_full ↔ Nodup(x::y::l)
                let right_symm = Expr::apps(
                    iff_symm.clone(),
                    [nd_xyl.clone(), right_full.clone(), right],
                );

                // shuffle : left_full ↔ right_full
                //   = List.nodup_swap_inner α x y l
                // (left_full = dm_y ∧ (¬Mem x l ∧ Nodup l),
                //  right_full = dm_x ∧ (¬Mem y l ∧ Nodup l))
                let shuffle = Expr::apps(
                    nodup_swap_inner_c.clone(),
                    [alpha.clone(), sx.clone(), sy.clone(), sl.clone()],
                );

                // body = trans left (trans shuffle right_symm)
                let tail = Expr::apps(
                    iff_trans.clone(),
                    [
                        left_full.clone(),
                        right_full.clone(),
                        nd_xyl.clone(),
                        shuffle,
                        right_symm,
                    ],
                );
                let body = Expr::apps(
                    iff_trans.clone(),
                    [
                        nd_yxl.clone(),
                        left_full.clone(),
                        nd_xyl.clone(),
                        left,
                        tail,
                    ],
                );

                let e = b.mk_lam(sl_id, BinderInfo::Default, list_of(&alpha), body);
                let e = b.mk_lam(sy_id, BinderInfo::Default, alpha.clone(), e);
                b.mk_lam(sx_id, BinderInfo::Default, alpha.clone(), e)
            };

            // trans minor : λ (l1 l2 l3) (h1)(h2)(ih1)(ih2) => Iff.trans ih1 ih2
            let m_trans = {
                let (t1_id, t1) = b.fresh_local(list_of(&alpha));
                let (t2_id, t2) = b.fresh_local(list_of(&alpha));
                let (t3_id, t3) = b.fresh_local(list_of(&alpha));
                let (th1_id, _th1) = b.fresh_local(perm(&alpha, t1.clone(), t2.clone()));
                let (th2_id, _th2) = b.fresh_local(perm(&alpha, t2.clone(), t3.clone()));
                let ih1_ty = iff(nodup(&alpha, t1.clone()), nodup(&alpha, t2.clone()));
                let ih2_ty = iff(nodup(&alpha, t2.clone()), nodup(&alpha, t3.clone()));
                let (ih1_id, ih1) = b.fresh_local(ih1_ty.clone());
                let (ih2_id, ih2) = b.fresh_local(ih2_ty.clone());
                let body = Expr::apps(
                    iff_trans.clone(),
                    [
                        nodup(&alpha, t1.clone()),
                        nodup(&alpha, t2.clone()),
                        nodup(&alpha, t3.clone()),
                        ih1.clone(),
                        ih2.clone(),
                    ],
                );
                let e = b.mk_lam(ih2_id, BinderInfo::Default, ih2_ty, body);
                let e = b.mk_lam(ih1_id, BinderInfo::Default, ih1_ty, e);
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

            // @List.Perm.rec α motive m_nil m_cons m_swap m_trans l1 l2 hp
            let (l1_id, l1) = b.fresh_local(list_of(&alpha));
            let (l2_id, l2) = b.fresh_local(list_of(&alpha));
            let (hp_id, hp) = b.fresh_local(perm(&alpha, l1.clone(), l2.clone()));
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
                    hp.clone(),
                ],
            );
            let e = b.mk_lam(
                hp_id,
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
            name: Name::from_string("List.Perm.nodup_iff"),
            level_params: vec![u.clone()],
            type_: nodup_iff_type,
            value: nodup_iff_value,
        })?;

        Ok(())
    }

    /// Register `Multiset.Nodup : {α} → Multiset α → Prop`, the lift of
    /// `List.Nodup` through `Quot (@List.Perm α)`.
    ///
    /// ```text
    /// Multiset.Nodup α s :=
    ///   @Quot.lift (List α) (Perm α) Prop
    ///     (fun l => List.Nodup l)
    ///     (fun l₁ l₂ hp => @propext (Nodup l₁) (Nodup l₂)
    ///         (Iff.mp  _ _ (List.Perm.nodup_iff α hp))
    ///         (Iff.mpr _ _ (List.Perm.nodup_iff α hp)))
    ///     s
    /// ```
    ///
    /// The "respects-`Perm`" obligation is discharged by `List.Perm.nodup_iff`
    /// (constructive) turned into the required `Eq` by `propext`.
    fn init_multiset_nodup(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let lvl_su = Level::succ(u_level.clone());

        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let perm_const = Expr::const_(Name::from_string("List.Perm"), vec![u_level.clone()]);
        let nodup_const = Expr::const_(Name::from_string("List.Nodup"), vec![u_level.clone()]);
        let multiset_const = Expr::const_(Name::from_string("Multiset"), vec![u_level.clone()]);
        let perm_nodup_iff_c = Expr::const_(
            Name::from_string("List.Perm.nodup_iff"),
            vec![u_level.clone()],
        );

        let propext = Expr::const_(Name::from_string("propext"), vec![]);
        // `Quot.lift.{u+1, 1}` — carrier `List α : Sort (u+1)`, target `Prop = Sort 1`.
        let quot_lift = Expr::const_(
            Name::from_string("Quot.lift"),
            vec![lvl_su.clone(), Level::succ(Level::zero())],
        );

        let list_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
        let perm_rel = |a: &Expr| Expr::app(perm_const.clone(), a.clone());
        let perm =
            |a: &Expr, l1: Expr, l2: Expr| Expr::apps(perm_const.clone(), [a.clone(), l1, l2]);
        let nodup = |a: &Expr, l: Expr| Expr::apps(nodup_const.clone(), [a.clone(), l]);
        let mset_of = |a: &Expr| Expr::app(multiset_const.clone(), a.clone());

        let nodup_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (s_id, _s) = b.fresh_local(mset_of(&alpha));
            let e = prop.clone();
            let e = b.mk_pi(s_id, BinderInfo::Default, mset_of(&alpha), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let nodup_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (s_id, s) = b.fresh_local(mset_of(&alpha));

            // f := fun (l : List α) => List.Nodup l
            let f = {
                let (l_id, l) = b.fresh_local(list_of(&alpha));
                let body = nodup(&alpha, l.clone());
                b.mk_lam(l_id, BinderInfo::Default, list_of(&alpha), body)
            };
            // h := fun (l1 l2 : List α) (hp : Perm l1 l2) =>
            //        propext (Nodup l1) (Nodup l2) (mp ...) (mpr ...)
            let h = {
                let (l1_id, l1) = b.fresh_local(list_of(&alpha));
                let (l2_id, l2) = b.fresh_local(list_of(&alpha));
                let (hp_id, hp) = b.fresh_local(perm(&alpha, l1.clone(), l2.clone()));
                let nd1 = nodup(&alpha, l1.clone());
                let nd2 = nodup(&alpha, l2.clone());
                let iff_term = Expr::apps(
                    perm_nodup_iff_c.clone(),
                    [alpha.clone(), l1.clone(), l2.clone(), hp.clone()],
                );
                // Faithful `propext` takes the `Iff` directly; `iff_term`
                // (`perm_nodup_iff … : Nodup l1 ↔ Nodup l2`) is already in hand.
                let body = Expr::apps(propext.clone(), [nd1, nd2, iff_term]);
                let e = b.mk_lam(
                    hp_id,
                    BinderInfo::Default,
                    perm(&alpha, l1.clone(), l2.clone()),
                    body,
                );
                let e = b.mk_lam(l2_id, BinderInfo::Default, list_of(&alpha), e);
                b.mk_lam(l1_id, BinderInfo::Default, list_of(&alpha), e)
            };
            let body = Expr::apps(
                quot_lift.clone(),
                [
                    list_of(&alpha),
                    perm_rel(&alpha),
                    prop.clone(),
                    f,
                    h,
                    s.clone(),
                ],
            );
            let e = b.mk_lam(s_id, BinderInfo::Default, mset_of(&alpha), body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Multiset.Nodup"),
            level_params: vec![u.clone()],
            type_: nodup_type,
            value: nodup_value,
            is_reducible: true,
        })?;

        Ok(())
    }
    /// Register the `Finset` carrier and its core operations.
    ///
    /// ```text
    /// Finset α            := { s : Multiset α // Multiset.Nodup s }
    ///                      := @Subtype (Multiset α) (fun s => Multiset.Nodup s)
    /// Finset.empty : Finset α
    ///                      := @Subtype.mk (Multiset α) (Nodup) Multiset.nil (List.Nodup.nil)
    /// Finset.Mem a F       := Multiset.Mem a (Subtype.val F)
    /// Finset.instMembership : Membership α (Finset α)   (opaque instance shim)
    /// ```
    fn init_finset_core(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let lvl_su = Level::succ(u_level.clone());

        let multiset_const = Expr::const_(Name::from_string("Multiset"), vec![u_level.clone()]);
        let multiset_nil = Expr::const_(Name::from_string("Multiset.nil"), vec![u_level.clone()]);
        let multiset_mem = Expr::const_(Name::from_string("Multiset.Mem"), vec![u_level.clone()]);
        let multiset_nodup =
            Expr::const_(Name::from_string("Multiset.Nodup"), vec![u_level.clone()]);
        let nodup_nil = Expr::const_(Name::from_string("List.Nodup.nil"), vec![u_level.clone()]);
        let finset_const = Expr::const_(Name::from_string("Finset"), vec![u_level.clone()]);
        // `Subtype.{u+1}` — carrier `Multiset α : Sort (u+1)`.
        let subtype = Expr::const_(Name::from_string("Subtype"), vec![lvl_su.clone()]);
        let subtype_mk = Expr::const_(Name::from_string("Subtype.mk"), vec![lvl_su.clone()]);
        let subtype_val = Expr::const_(Name::from_string("Subtype.val"), vec![lvl_su.clone()]);

        let mset_of = |a: &Expr| Expr::app(multiset_const.clone(), a.clone());
        let mnil_of = |a: &Expr| Expr::app(multiset_nil.clone(), a.clone());
        let mnodup = |a: &Expr, s: Expr| Expr::apps(multiset_nodup.clone(), [a.clone(), s]);
        let mmem = |a: &Expr, x: Expr, s: Expr| Expr::apps(multiset_mem.clone(), [a.clone(), x, s]);
        let fin_of = |a: &Expr| Expr::app(finset_const.clone(), a.clone());

        // Predicate `fun (s : Multiset α) => Multiset.Nodup s` (reused).
        let nodup_pred = |b: &mut EnvDeclBuilder, alpha: &Expr| -> Expr {
            let (s_id, s) = b.fresh_local(mset_of(alpha));
            let body = mnodup(alpha, s.clone());
            b.mk_lam(s_id, BinderInfo::Default, mset_of(alpha), body)
        };

        // ── Finset : Type u → Type u := fun α => @Subtype (Multiset α) (Nodup) ─
        let finset_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
        let finset_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let pred = nodup_pred(&mut b, &alpha);
            let body = Expr::apps(subtype.clone(), [mset_of(&alpha), pred]);
            let e = b.mk_lam(alpha_id, BinderInfo::Default, type_u.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Finset"),
            level_params: vec![u.clone()],
            type_: finset_type,
            value: finset_value,
            is_reducible: true,
        })?;

        // ── Finset.empty : {α} → Finset α
        //   := @Subtype.mk (Multiset α) (Nodup) Multiset.nil (List.Nodup.nil α)
        // (List.Nodup.nil α : List.Nodup [] def-eq Multiset.Nodup Multiset.nil
        //  through the Quot.lift reduction on the canonical representative.)
        let finset_empty_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let e = fin_of(&alpha);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let finset_empty_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let pred = nodup_pred(&mut b, &alpha);
            let nil_proof = Expr::app(nodup_nil.clone(), alpha.clone());
            let body = Expr::apps(
                subtype_mk.clone(),
                [mset_of(&alpha), pred, mnil_of(&alpha), nil_proof],
            );
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Finset.empty"),
            level_params: vec![u.clone()],
            type_: finset_empty_type,
            value: finset_empty_value,
            is_reducible: true,
        })?;

        // ── Finset.Mem : {α} → α → Finset α → Prop
        //   := fun α a F => Multiset.Mem a (@Subtype.val (Multiset α) (Nodup) F)
        let finset_mem_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (f_id, _f) = b.fresh_local(fin_of(&alpha));
            let e = prop.clone();
            let e = b.mk_pi(f_id, BinderInfo::Default, fin_of(&alpha), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let finset_mem_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (f_id, f) = b.fresh_local(fin_of(&alpha));
            let pred = nodup_pred(&mut b, &alpha);
            // @Subtype.val (Multiset α) (Nodup) F  : Multiset α
            let val = Expr::apps(subtype_val.clone(), [mset_of(&alpha), pred, f.clone()]);
            let body = mmem(&alpha, a.clone(), val);
            let e = b.mk_lam(f_id, BinderInfo::Default, fin_of(&alpha), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Finset.Mem"),
            level_params: vec![u.clone()],
            type_: finset_mem_type,
            value: finset_mem_value,
            is_reducible: true,
        })?;

        // ── Finset.instMembership : {α : Type u} → Membership α (Finset α)
        //     := Membership.mk α (Finset α)
        //          (fun (s : Finset α) (a : α) => Finset.Mem α a s)
        // Genuine `Membership.mk`-based definition (NOT an axiom) so
        // `Membership.mem α (Finset α) inst s a` proj-reduces to
        // `Finset.Mem a s`. The `Membership` field is COLLECTION-first since
        // Lean v4.9 (`mem : γ → α → Prop`, Init/Prelude.lean:1746), while
        // Clean's hand-rolled `Finset.Mem` carrier stays element-first, so the
        // instance wraps it in the flip lambda — the same pattern Lean v4.30
        // itself uses for `List` (`⟨fun l a => Mem a l⟩`). Shape correction to
        // MATCH Lean; the kernel re-checks the body.
        let inst_membership_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let membership_uu = Expr::const_(
                Name::from_string("Membership"),
                vec![u_level.clone(), u_level.clone()],
            );
            let e = Expr::apps(membership_uu, [alpha.clone(), fin_of(&alpha)]);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let inst_membership_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let membership_mk = Expr::const_(
                Name::from_string("Membership.mk"),
                vec![u_level.clone(), u_level.clone()],
            );
            let finset_mem = Expr::const_(Name::from_string("Finset.Mem"), vec![u_level.clone()]);
            // Collection-first flip lambda over the element-first carrier:
            //   fun (s : Finset α) (a : α) => Finset.Mem α a s
            let flip_mem = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (s_id, s) = c.fresh_local(fin_of(&alpha));
                let (a_id, a) = c.fresh_local(alpha.clone());
                let body = Expr::apps(finset_mem, [alpha.clone(), a.clone(), s.clone()]);
                let r = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
                let r = c.mk_lam(s_id, BinderInfo::Default, fin_of(&alpha), r);
                c.finish_child(r)
            };
            let body = Expr::apps(membership_mk, [alpha.clone(), fin_of(&alpha), flip_mem]);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Finset.instMembership"),
            level_params: vec![u.clone()],
            type_: inst_membership_type,
            value: inst_membership_value,
            is_reducible: true,
        })?;
        // Register it as a `Membership` instance so `a ∈ s` (Finset) resolves.
        self.register_instance(crate::env::KernelInstanceInfo {
            name: Name::from_string("Finset.instMembership"),
            class_name: Name::from_string("Membership"),
            priority: crate::env::DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.init_finset_mem_empty()?;
        self.init_finset_cons()?;

        Ok(())
    }

    /// Register `Multiset.nodup_cons {α} (a : α) (s : Multiset α) :`
    /// `¬ Multiset.Mem a s → Multiset.Nodup s → Multiset.Nodup (Multiset.cons a s)`
    /// (by `Quot.ind` on `s`), and the dependent constructor
    /// `Finset.cons {α} (a : α) (F : Finset α) (h : ¬ Finset.Mem a F) : Finset α`
    /// that inserts a fresh element preserving the no-duplicates witness.
    fn init_finset_cons(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let lvl_su = Level::succ(u_level.clone());

        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let perm_const = Expr::const_(Name::from_string("List.Perm"), vec![u_level.clone()]);
        let nodup_cons_ctor =
            Expr::const_(Name::from_string("List.Nodup.cons"), vec![u_level.clone()]);
        let multiset_const = Expr::const_(Name::from_string("Multiset"), vec![u_level.clone()]);
        let multiset_cons = Expr::const_(Name::from_string("Multiset.cons"), vec![u_level.clone()]);
        let multiset_mem = Expr::const_(Name::from_string("Multiset.Mem"), vec![u_level.clone()]);
        let multiset_nodup =
            Expr::const_(Name::from_string("Multiset.Nodup"), vec![u_level.clone()]);
        let not_mem_const = Expr::const_(Name::from_string("Not"), vec![]);
        // `Quot.ind.{u+1}` — carrier `List α : Sort (u+1)`.
        let quot_ind = Expr::const_(Name::from_string("Quot.ind"), vec![lvl_su.clone()]);

        let subtype_mk = Expr::const_(Name::from_string("Subtype.mk"), vec![lvl_su.clone()]);
        let subtype_val = Expr::const_(Name::from_string("Subtype.val"), vec![lvl_su.clone()]);
        let finset_const = Expr::const_(Name::from_string("Finset"), vec![u_level.clone()]);
        let finset_mem = Expr::const_(Name::from_string("Finset.Mem"), vec![u_level.clone()]);
        let nodup_cons_c = Expr::const_(
            Name::from_string("Multiset.nodup_cons"),
            vec![u_level.clone()],
        );

        let list_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
        let perm_rel = |a: &Expr| Expr::app(perm_const.clone(), a.clone());
        let mset_of = |a: &Expr| Expr::app(multiset_const.clone(), a.clone());
        let mcons =
            |a: &Expr, x: Expr, s: Expr| Expr::apps(multiset_cons.clone(), [a.clone(), x, s]);
        let mmem = |a: &Expr, x: Expr, s: Expr| Expr::apps(multiset_mem.clone(), [a.clone(), x, s]);
        let mnodup = |a: &Expr, s: Expr| Expr::apps(multiset_nodup.clone(), [a.clone(), s]);
        let not = |p: Expr| Expr::app(not_mem_const.clone(), p);
        let fin_of = |a: &Expr| Expr::app(finset_const.clone(), a.clone());
        let fmem = |a: &Expr, x: Expr, f: Expr| Expr::apps(finset_mem.clone(), [a.clone(), x, f]);

        let nodup_pred = |b: &mut EnvDeclBuilder, alpha: &Expr| -> Expr {
            let (s_id, s) = b.fresh_local(mset_of(alpha));
            let body = mnodup(alpha, s.clone());
            b.mk_lam(s_id, BinderInfo::Default, mset_of(alpha), body)
        };

        // ── Multiset.nodup_cons {α} (a) (s) :
        //      ¬ Mem a s → Nodup s → Nodup (cons a s) ────────────────────────
        let mnc_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (s_id, s) = b.fresh_local(mset_of(&alpha));
            let not_mem = not(mmem(&alpha, a.clone(), s.clone()));
            let nodup_s = mnodup(&alpha, s.clone());
            let concl = mnodup(&alpha, mcons(&alpha, a.clone(), s.clone()));
            let (hn_id, _hn) = b.fresh_local(nodup_s.clone());
            let (hm_id, _hm) = b.fresh_local(not_mem.clone());
            let e = b.mk_pi(hn_id, BinderInfo::Default, nodup_s.clone(), concl);
            let e = b.mk_pi(hm_id, BinderInfo::Default, not_mem.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, mset_of(&alpha), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let mnc_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (s_id, s) = b.fresh_local(mset_of(&alpha));

            // motive β : fun (s : Multiset α) =>
            //   ¬ Mem a s → Nodup s → Nodup (cons a s)
            let motive = {
                let (ms_id, ms) = b.fresh_local(mset_of(&alpha));
                let not_mem = not(mmem(&alpha, a.clone(), ms.clone()));
                let nodup_s = mnodup(&alpha, ms.clone());
                let concl = mnodup(&alpha, mcons(&alpha, a.clone(), ms.clone()));
                let (hn_id, _hn) = b.fresh_local(nodup_s.clone());
                let (hm_id, _hm) = b.fresh_local(not_mem.clone());
                let e = b.mk_pi(hn_id, BinderInfo::Default, nodup_s.clone(), concl);
                let e = b.mk_pi(hm_id, BinderInfo::Default, not_mem.clone(), e);
                b.mk_lam(ms_id, BinderInfo::Default, mset_of(&alpha), e)
            };

            // hyp : ∀ (l : List α), β (Quot.mk l)
            //   = fun (l : List α) (hm : ¬ Mem a (Quot.mk l)) (hn : Nodup (Quot.mk l)) =>
            //       @List.Nodup.cons α a l hm hn
            // (declared arg/result types quot-reduce to ¬List.Mem a l, List.Nodup l,
            //  and List.Nodup (a::l) respectively.)
            let hyp = {
                let (l_id, l) = b.fresh_local(list_of(&alpha));
                // Type the lambda binders at the *Multiset* shapes so the lambda's
                // inferred type matches β (Quot.mk l) up to def-eq.
                let mk = {
                    let quot_mk = Expr::const_(Name::from_string("Quot.mk"), vec![lvl_su.clone()]);
                    Expr::apps(quot_mk, [list_of(&alpha), perm_rel(&alpha), l.clone()])
                };
                let not_mem = not(mmem(&alpha, a.clone(), mk.clone()));
                let nodup_s = mnodup(&alpha, mk.clone());
                let (hm_id, hm) = b.fresh_local(not_mem.clone());
                let (hn_id, hn) = b.fresh_local(nodup_s.clone());
                let body = Expr::apps(
                    nodup_cons_ctor.clone(),
                    [alpha.clone(), a.clone(), l.clone(), hm, hn],
                );
                let e = b.mk_lam(hn_id, BinderInfo::Default, nodup_s, body);
                let e = b.mk_lam(hm_id, BinderInfo::Default, not_mem, e);
                b.mk_lam(l_id, BinderInfo::Default, list_of(&alpha), e)
            };

            // @Quot.ind (List α) (Perm α) β hyp s
            let body = Expr::apps(
                quot_ind.clone(),
                [list_of(&alpha), perm_rel(&alpha), motive, hyp, s.clone()],
            );
            let e = b.mk_lam(s_id, BinderInfo::Default, mset_of(&alpha), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Multiset.nodup_cons"),
            level_params: vec![u.clone()],
            type_: mnc_type,
            value: mnc_value,
        })?;

        // ── Finset.cons {α} (a) (F : Finset α) (h : ¬ Finset.Mem a F) : Finset α
        //   := @Subtype.mk (Multiset α) (Nodup)
        //        (Multiset.cons a F.val)
        //        (Multiset.nodup_cons a F.val h F.property)
        // where F.val = @Subtype.val (Multiset α)(Nodup) F and
        //       F.property : Multiset.Nodup F.val.
        // `h : ¬ Finset.Mem a F` quot-reduces to `¬ Multiset.Mem a F.val`.
        let subtype_property =
            Expr::const_(Name::from_string("Subtype.property"), vec![lvl_su.clone()]);

        let fcons_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (f_id, f) = b.fresh_local(fin_of(&alpha));
            let h_ty = not(fmem(&alpha, a.clone(), f.clone()));
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let concl = fin_of(&alpha);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(f_id, BinderInfo::Default, fin_of(&alpha), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let fcons_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (f_id, f) = b.fresh_local(fin_of(&alpha));
            let h_ty = not(fmem(&alpha, a.clone(), f.clone()));
            let (h_id, h) = b.fresh_local(h_ty.clone());
            let pred = nodup_pred(&mut b, &alpha);
            // val := @Subtype.val (Multiset α) (Nodup) F : Multiset α
            let val = Expr::apps(
                subtype_val.clone(),
                [mset_of(&alpha), pred.clone(), f.clone()],
            );
            // prop := @Subtype.property (Multiset α) (Nodup) F : Multiset.Nodup val
            let prop_proof = Expr::apps(
                subtype_property.clone(),
                [mset_of(&alpha), pred.clone(), f.clone()],
            );
            // new_val := Multiset.cons a val
            let new_val = mcons(&alpha, a.clone(), val.clone());
            // nodup proof : Multiset.Nodup (Multiset.cons a val)
            //   = Multiset.nodup_cons a val h prop
            // (h : ¬ Finset.Mem a F def-eq ¬ Multiset.Mem a val.)
            let nodup_proof = Expr::apps(
                nodup_cons_c.clone(),
                [alpha.clone(), a.clone(), val.clone(), h.clone(), prop_proof],
            );
            let body = Expr::apps(
                subtype_mk.clone(),
                [mset_of(&alpha), pred, new_val, nodup_proof],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, fin_of(&alpha), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Finset.cons"),
            level_params: vec![u.clone()],
            type_: fcons_type,
            value: fcons_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Register `List.not_mem_nil {α} (a : α) : ¬ List.Mem a []` (constructive,
    /// via `List.Mem.casesOn` on the empty index) and the `Finset`-level
    /// `Finset.mem_empty {α} (a : α) : ¬ Finset.Mem a Finset.empty`, which holds
    /// because `Finset.Mem a Finset.empty` quot-reduces to `List.Mem a []`.
    fn init_finset_mem_empty(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u_level.clone()]);
        let mem_const = Expr::const_(Name::from_string("List.Mem"), vec![u_level.clone()]);
        // `List.Mem.casesOn.{u}` — `List.Mem` is a `Prop`, small elimination.
        let mem_cases = Expr::const_(Name::from_string("List.Mem.casesOn"), vec![u_level.clone()]);
        // `List.casesOn.{1,u}` — computing a `Prop` motive.
        let list_cases = Expr::const_(
            Name::from_string("List.casesOn"),
            vec![Level::succ(Level::zero()), u_level.clone()],
        );
        let not_const = Expr::const_(Name::from_string("Not"), vec![]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let true_const = Expr::const_(Name::from_string("True"), vec![]);
        let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
        let finset_const = Expr::const_(Name::from_string("Finset"), vec![u_level.clone()]);
        let finset_empty = Expr::const_(Name::from_string("Finset.empty"), vec![u_level.clone()]);
        let finset_mem = Expr::const_(Name::from_string("Finset.Mem"), vec![u_level.clone()]);
        let not_mem_nil_c =
            Expr::const_(Name::from_string("List.not_mem_nil"), vec![u_level.clone()]);

        let list_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
        let nil_of = |a: &Expr| Expr::app(list_nil.clone(), a.clone());
        let mem = |a: &Expr, x: Expr, l: Expr| Expr::apps(mem_const.clone(), [a.clone(), x, l]);
        let not = |p: Expr| Expr::app(not_const.clone(), p);
        let fin_of = |a: &Expr| Expr::app(finset_const.clone(), a.clone());
        let fempty_of = |a: &Expr| Expr::app(finset_empty.clone(), a.clone());
        let fmem = |a: &Expr, x: Expr, f: Expr| Expr::apps(finset_mem.clone(), [a.clone(), x, f]);

        // ── List.not_mem_nil {α} (a : α) : ¬ List.Mem a [] ──────────────────
        let nmn_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let concl = not(mem(&alpha, a.clone(), nil_of(&alpha)));
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), concl);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let nmn_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (h_id, h) = b.fresh_local(mem(&alpha, a.clone(), nil_of(&alpha)));

            // P : List α → Prop :=
            //   fun lst => List.casesOn α (fun _ => Prop) False (fun _ _ => True) lst
            // so P [] = False, P (_ :: _) = True.
            let p_fun = {
                let (lst_id, lst) = b.fresh_local(list_of(&alpha));
                let cm = {
                    let (z_id, _z) = b.fresh_local(list_of(&alpha));
                    b.mk_lam(z_id, BinderInfo::Default, list_of(&alpha), prop.clone())
                };
                let cons_branch = {
                    let (hd_id, _hd) = b.fresh_local(alpha.clone());
                    let (tl_id, _tl) = b.fresh_local(list_of(&alpha));
                    let e = b.mk_lam(
                        tl_id,
                        BinderInfo::Default,
                        list_of(&alpha),
                        true_const.clone(),
                    );
                    b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), e)
                };
                // Lean-faithful casesOn order: motive, major, then minors.
                let body = Expr::apps(
                    list_cases.clone(),
                    [
                        alpha.clone(),
                        cm,
                        lst.clone(),
                        false_const.clone(), // nil branch ⇒ False
                        cons_branch,         // cons branch ⇒ True
                    ],
                );
                b.mk_lam(lst_id, BinderInfo::Default, list_of(&alpha), body)
            };

            // motive : fun (lst : List α) (_ : Mem a lst) => P lst
            let motive = {
                let (m_lst_id, m_lst) = b.fresh_local(list_of(&alpha));
                let (m_h_id, _m_h) = b.fresh_local(mem(&alpha, a.clone(), m_lst.clone()));
                let body = Expr::app(p_fun.clone(), m_lst.clone());
                let e = b.mk_lam(
                    m_h_id,
                    BinderInfo::Default,
                    mem(&alpha, a.clone(), m_lst.clone()),
                    body,
                );
                b.mk_lam(m_lst_id, BinderInfo::Default, list_of(&alpha), e)
            };
            // head minor : fun (as : List α) => True.intro   (motive (a::as) _ = P(a::as) = True)
            let head_minor = {
                let (as_id, _as) = b.fresh_local(list_of(&alpha));
                b.mk_lam(
                    as_id,
                    BinderInfo::Default,
                    list_of(&alpha),
                    true_intro.clone(),
                )
            };
            // tail minor : fun (b' : α)(as : List α)(_ : Mem a as) => True.intro
            let tail_minor = {
                let (b2_id, _b2) = b.fresh_local(alpha.clone());
                let (as_id, as_) = b.fresh_local(list_of(&alpha));
                let (h2_id, _h2) = b.fresh_local(mem(&alpha, a.clone(), as_.clone()));
                let e = b.mk_lam(
                    h2_id,
                    BinderInfo::Default,
                    mem(&alpha, a.clone(), as_.clone()),
                    true_intro.clone(),
                );
                let e = b.mk_lam(as_id, BinderInfo::Default, list_of(&alpha), e);
                b.mk_lam(b2_id, BinderInfo::Default, alpha.clone(), e)
            };
            // List.Mem.casesOn α a motive [] h head tail : P [] = False
            // (Lean-faithful casesOn order: motive, indices, major, minors.)
            let cased = Expr::apps(
                mem_cases.clone(),
                [
                    alpha.clone(),
                    a.clone(),
                    motive,
                    nil_of(&alpha), // index []
                    h.clone(),
                    head_minor,
                    tail_minor,
                ],
            );
            let body = b.mk_lam(
                h_id,
                BinderInfo::Default,
                mem(&alpha, a.clone(), nil_of(&alpha)),
                cased,
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("List.not_mem_nil"),
            level_params: vec![u.clone()],
            type_: nmn_type,
            value: nmn_value,
        })?;

        // ── Finset.mem_empty {α} (a : α) : ¬ Finset.Mem a Finset.empty ──────
        // `Finset.Mem a Finset.empty` reduces (Subtype.val + Quot.lift) to
        // `List.Mem a []`, so `List.not_mem_nil a` inhabits the negation.
        let me_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let concl = not(fmem(&alpha, a.clone(), fempty_of(&alpha)));
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), concl);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let me_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let body = Expr::apps(not_mem_nil_c.clone(), [alpha.clone(), a.clone()]);
            let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Finset.mem_empty"),
            level_params: vec![u.clone()],
            type_: me_type,
            value: me_value,
        })?;

        Ok(())
    }

    /// Register the `Finset`-level membership-introduction lemmas used to build
    /// completeness proofs over an explicit `Finset.cons` chain:
    ///
    /// - `Multiset.mem_cons_of_mem {α} (a b : α) (s) :`
    ///   `Multiset.Mem a s → Multiset.Mem a (Multiset.cons b s)`
    ///   (by `Quot.ind` on `s`; on a representative `l` it quot-reduces to
    ///   `List.Mem a l → List.Mem a (b :: l)`, discharged by `List.Mem.tail`).
    /// - `Finset.mem_cons_self {α} (a : α) (F : Finset α) (h : ¬ Finset.Mem a F) :`
    ///   `Finset.Mem a (Finset.cons a F h)` — the goal def-eq-reduces to
    ///   `Multiset.Mem a (Multiset.cons a F.val)` (through `Subtype.val` on the
    ///   reducible `Finset.cons`), inhabited by `Multiset.mem_cons_self`.
    /// - `Finset.mem_cons_of_mem {α} (a b : α) (F) (h) :`
    ///   `Finset.Mem a F → Finset.Mem a (Finset.cons b F h)` — similarly, from
    ///   `Multiset.mem_cons_of_mem a b F.val`.
    ///
    /// Every term is constructive; transitive axiom closure `⊆ {Quot.sound,
    /// propext}` (both FOUNDATIONAL).
    fn init_finset_mem_cons(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let lvl_su = Level::succ(u_level.clone());

        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let perm_const = Expr::const_(Name::from_string("List.Perm"), vec![u_level.clone()]);
        let list_mem_const = Expr::const_(Name::from_string("List.Mem"), vec![u_level.clone()]);
        let list_mem_tail = Expr::const_(Name::from_string("List.Mem.tail"), vec![u_level.clone()]);
        let multiset_const = Expr::const_(Name::from_string("Multiset"), vec![u_level.clone()]);
        let multiset_cons = Expr::const_(Name::from_string("Multiset.cons"), vec![u_level.clone()]);
        let multiset_mem = Expr::const_(Name::from_string("Multiset.Mem"), vec![u_level.clone()]);
        let mset_mem_self = Expr::const_(
            Name::from_string("Multiset.mem_cons_self"),
            vec![u_level.clone()],
        );
        let mset_mem_of_mem = Expr::const_(
            Name::from_string("Multiset.mem_cons_of_mem"),
            vec![u_level.clone()],
        );
        // `Quot.ind.{u+1}` — carrier `List α : Sort (u+1)`.
        let quot_ind = Expr::const_(Name::from_string("Quot.ind"), vec![lvl_su.clone()]);

        let subtype_val = Expr::const_(Name::from_string("Subtype.val"), vec![lvl_su.clone()]);
        let multiset_nodup =
            Expr::const_(Name::from_string("Multiset.Nodup"), vec![u_level.clone()]);
        let finset_const = Expr::const_(Name::from_string("Finset"), vec![u_level.clone()]);
        let finset_cons = Expr::const_(Name::from_string("Finset.cons"), vec![u_level.clone()]);
        let finset_mem = Expr::const_(Name::from_string("Finset.Mem"), vec![u_level.clone()]);
        let not_const = Expr::const_(Name::from_string("Not"), vec![]);

        let list_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
        let perm_rel = |a: &Expr| Expr::app(perm_const.clone(), a.clone());
        let mset_of = |a: &Expr| Expr::app(multiset_const.clone(), a.clone());
        let mcons =
            |a: &Expr, x: Expr, s: Expr| Expr::apps(multiset_cons.clone(), [a.clone(), x, s]);
        let mmem = |a: &Expr, x: Expr, s: Expr| Expr::apps(multiset_mem.clone(), [a.clone(), x, s]);
        let lmem =
            |a: &Expr, x: Expr, l: Expr| Expr::apps(list_mem_const.clone(), [a.clone(), x, l]);
        let mnodup = |a: &Expr, s: Expr| Expr::apps(multiset_nodup.clone(), [a.clone(), s]);
        let fin_of = |a: &Expr| Expr::app(finset_const.clone(), a.clone());
        let fmem = |a: &Expr, x: Expr, f: Expr| Expr::apps(finset_mem.clone(), [a.clone(), x, f]);
        let not = |p: Expr| Expr::app(not_const.clone(), p);
        let nodup_pred = |b: &mut EnvDeclBuilder, alpha: &Expr| -> Expr {
            let (s_id, s) = b.fresh_local(mset_of(alpha));
            let body = mnodup(alpha, s.clone());
            b.mk_lam(s_id, BinderInfo::Default, mset_of(alpha), body)
        };

        // ── Multiset.mem_cons_of_mem {α} (a b) (s) :
        //      Multiset.Mem a s → Multiset.Mem a (Multiset.cons b s) ───────────
        {
            let mcom_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (bv_id, bv) = b.fresh_local(alpha.clone());
                let (s_id, s) = b.fresh_local(mset_of(&alpha));
                let hyp = mmem(&alpha, a.clone(), s.clone());
                let concl = mmem(&alpha, a.clone(), mcons(&alpha, bv.clone(), s.clone()));
                let arrow = Expr::pi(BinderInfo::Default, hyp.clone(), concl);
                let e = b.mk_pi(s_id, BinderInfo::Default, mset_of(&alpha), arrow);
                let e = b.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let mcom_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (bv_id, bv) = b.fresh_local(alpha.clone());
                let (s_id, s) = b.fresh_local(mset_of(&alpha));

                // motive : fun (s : Multiset α) =>
                //            Multiset.Mem a s → Multiset.Mem a (Multiset.cons b s)
                let motive = {
                    let (ms_id, ms) = b.fresh_local(mset_of(&alpha));
                    let hyp = mmem(&alpha, a.clone(), ms.clone());
                    let concl = mmem(&alpha, a.clone(), mcons(&alpha, bv.clone(), ms.clone()));
                    let arrow = Expr::pi(BinderInfo::Default, hyp, concl);
                    b.mk_lam(ms_id, BinderInfo::Default, mset_of(&alpha), arrow)
                };
                // hyp : ∀ (l : List α), motive (Quot.mk l)
                //   = fun (l) (hm : List.Mem a l) => @List.Mem.tail α a b l hm
                // (motive (Quot.mk l) quot-reduces to List.Mem a l → List.Mem a (b::l).)
                let hyp = {
                    let (l_id, l) = b.fresh_local(list_of(&alpha));
                    // At the representative, the hypothesis is `List.Mem a l`
                    // (the def-eq reduction of `Multiset.Mem a (Quot.mk l)`).
                    let mem_a_l = lmem(&alpha, a.clone(), l.clone());
                    let (hm_id, hm) = b.fresh_local(mem_a_l.clone());
                    let body = Expr::apps(
                        list_mem_tail.clone(),
                        [alpha.clone(), a.clone(), bv.clone(), l.clone(), hm],
                    );
                    let e = b.mk_lam(hm_id, BinderInfo::Default, mem_a_l, body);
                    b.mk_lam(l_id, BinderInfo::Default, list_of(&alpha), e)
                };
                let body = Expr::apps(
                    quot_ind.clone(),
                    [list_of(&alpha), perm_rel(&alpha), motive, hyp, s.clone()],
                );
                let e = b.mk_lam(s_id, BinderInfo::Default, mset_of(&alpha), body);
                let e = b.mk_lam(bv_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Multiset.mem_cons_of_mem"),
                level_params: vec![u.clone()],
                type_: mcom_type,
                value: mcom_value,
            })?;
        }

        // ── Finset.mem_cons_self {α} (a) (F) (h : ¬ Finset.Mem a F) :
        //      Finset.Mem a (Finset.cons a F h) ───────────────────────────────
        {
            let fms_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (f_id, f) = b.fresh_local(fin_of(&alpha));
                let h_ty = not(fmem(&alpha, a.clone(), f.clone()));
                let (h_id, h) = b.fresh_local(h_ty.clone());
                let fcons = Expr::apps(
                    finset_cons.clone(),
                    [alpha.clone(), a.clone(), f.clone(), h.clone()],
                );
                let concl = fmem(&alpha, a.clone(), fcons);
                let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
                let e = b.mk_pi(f_id, BinderInfo::Default, fin_of(&alpha), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let fms_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (f_id, f) = b.fresh_local(fin_of(&alpha));
                let h_ty = not(fmem(&alpha, a.clone(), f.clone()));
                let (h_id, _h) = b.fresh_local(h_ty.clone());
                let pred = nodup_pred(&mut b, &alpha);
                // val := @Subtype.val (Multiset α) (Nodup) F : Multiset α
                let val = Expr::apps(subtype_val.clone(), [mset_of(&alpha), pred, f.clone()]);
                // @Multiset.mem_cons_self α a F.val : Multiset.Mem a (cons a F.val)
                // which is def-eq to the goal Finset.Mem a (Finset.cons a F h).
                let body = Expr::apps(mset_mem_self.clone(), [alpha.clone(), a.clone(), val]);
                let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                let e = b.mk_lam(f_id, BinderInfo::Default, fin_of(&alpha), e);
                let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Finset.mem_cons_self"),
                level_params: vec![u.clone()],
                type_: fms_type,
                value: fms_value,
            })?;
        }

        // ── Finset.mem_cons_of_mem {α} (a b) (F) (h) :
        //      Finset.Mem a F → Finset.Mem a (Finset.cons b F h) ──────────────
        {
            let fcom_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (bv_id, bv) = b.fresh_local(alpha.clone());
                let (f_id, f) = b.fresh_local(fin_of(&alpha));
                let h_ty = not(fmem(&alpha, bv.clone(), f.clone()));
                let (h_id, h) = b.fresh_local(h_ty.clone());
                let mem_a_f = fmem(&alpha, a.clone(), f.clone());
                let fcons = Expr::apps(
                    finset_cons.clone(),
                    [alpha.clone(), bv.clone(), f.clone(), h.clone()],
                );
                let concl = fmem(&alpha, a.clone(), fcons);
                let arrow = Expr::pi(BinderInfo::Default, mem_a_f, concl);
                let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, arrow);
                let e = b.mk_pi(f_id, BinderInfo::Default, fin_of(&alpha), e);
                let e = b.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let fcom_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());
                let (bv_id, bv) = b.fresh_local(alpha.clone());
                let (f_id, f) = b.fresh_local(fin_of(&alpha));
                let h_ty = not(fmem(&alpha, bv.clone(), f.clone()));
                let (h_id, _h) = b.fresh_local(h_ty.clone());
                let mem_a_f = fmem(&alpha, a.clone(), f.clone());
                let (hm_id, hm) = b.fresh_local(mem_a_f.clone());
                let pred = nodup_pred(&mut b, &alpha);
                let val = Expr::apps(subtype_val.clone(), [mset_of(&alpha), pred, f.clone()]);
                // @Multiset.mem_cons_of_mem α a b F.val hm
                //   : Multiset.Mem a (cons b F.val), def-eq the Finset goal.
                // (hm : Finset.Mem a F def-eq Multiset.Mem a F.val.)
                let body = Expr::apps(
                    mset_mem_of_mem.clone(),
                    [alpha.clone(), a.clone(), bv.clone(), val, hm],
                );
                let e = b.mk_lam(hm_id, BinderInfo::Default, mem_a_f, body);
                let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, e);
                let e = b.mk_lam(f_id, BinderInfo::Default, fin_of(&alpha), e);
                let e = b.mk_lam(bv_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Finset.mem_cons_of_mem"),
                level_params: vec![u.clone()],
                type_: fcom_type,
                value: fcom_value,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod finset_tests {
    use super::*;
    use crate::tc::TypeChecker;

    fn env_with_finset() -> Environment {
        let mut env = Environment::new();
        env.init_finset().expect("Finset should initialize");
        env
    }

    fn assert_value_checks_and_clean(env: &Environment, name: &str) {
        let tc = TypeChecker::new(env);
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        if let Some(value) = info.value.clone() {
            let inferred = tc
                .infer_type(&value)
                .unwrap_or_else(|e| panic!("{name} value should type-check, got {e:?}"));
            assert!(
                tc.is_def_eq(&inferred, &info.type_),
                "{name}: inferred type must match declared type"
            );
        }
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("axiom_deps for {name}"));
        assert!(
            deps.is_empty(),
            "{name} must have an empty domain-axiom closure (⊆ FOUNDATIONAL), got {deps:?}"
        );
    }

    #[test]
    fn test_finset_logic_helpers_constructive() {
        let env = env_with_finset();
        for name in [
            "Iff.not_congr",
            "Iff.and_congr",
            "List.nodup_cons_iff",
            "Or.not_or_iff_and_not",
            "List.not_mem_cons_iff",
            "List.nodup_swap_inner",
        ] {
            assert_value_checks_and_clean(&env, name);
        }
    }

    /// The decisive deliverable: `List.Perm.nodup_iff` is registered, its proof
    /// term kernel-checks at the declared type, and its transitive axiom closure
    /// is `⊆ FOUNDATIONAL` (empty after foundational filtering). The proof rides
    /// `List.Perm.rec`, so all four cases (nil/cons/swap/trans) discharge.
    #[test]
    fn test_perm_nodup_iff_constructive() {
        let env = env_with_finset();
        assert_value_checks_and_clean(&env, "List.Perm.nodup_iff");
    }

    #[test]
    fn test_finset_init_idempotent() {
        let mut env = env_with_finset();
        env.init_finset()
            .expect("idempotent re-initialization should succeed");
        assert!(env.finset_init);
    }

    /// `Multiset.Nodup`, `Finset`, `Finset.empty`, and `Finset.Mem` are all
    /// registered, their stored values kernel-type-check at the declared type,
    /// and their transitive axiom closure is `⊆ FOUNDATIONAL` ({Quot.sound,
    /// propext}). `Finset.instMembership` is an instance shim (an `Axiom`), so
    /// its presence is checked but not its (nonexistent) value.
    #[test]
    fn test_finset_core_registered_and_clean() {
        let env = env_with_finset();
        for name in [
            "Multiset.Nodup",
            "Finset",
            "Finset.empty",
            "Finset.Mem",
            "Finset.instMembership",
            "List.Perm.nodup_iff",
        ] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered"
            );
        }
        for name in ["Multiset.Nodup", "Finset", "Finset.empty", "Finset.Mem"] {
            assert_value_checks_and_clean(&env, name);
        }
    }

    /// `Multiset.nodup_cons` and `Finset.cons` are registered, kernel-check,
    /// and are domain-axiom-free (closure ⊆ {Quot.sound, propext}). `Finset.cons`
    /// is the fresh-insertion constructor preserving the no-duplicates witness.
    #[test]
    fn test_finset_cons_constructive() {
        let env = env_with_finset();
        for name in ["Multiset.nodup_cons", "Finset.cons"] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered"
            );
            assert_value_checks_and_clean(&env, name);
        }
    }

    /// `List.not_mem_nil` and `Finset.mem_empty` are constructive proofs:
    /// nothing is a member of the empty list / empty finset. Both type-check and
    /// are domain-axiom-free.
    #[test]
    fn test_finset_mem_empty_constructive() {
        let env = env_with_finset();
        for name in ["List.not_mem_nil", "Finset.mem_empty"] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered"
            );
            assert_value_checks_and_clean(&env, name);
        }
    }

    /// `Finset.empty` and `Finset.Mem` type-check concretely over `Finset Nat`:
    /// `Finset.Mem 0 Finset.empty` is a well-formed `Prop`. This exercises the
    /// `Subtype.val`/`Quot.lift` reductions on the canonical representative.
    #[test]
    fn test_finset_empty_mem_concrete_typechecks() {
        let env = env_with_finset();
        let tc = TypeChecker::new(&env);
        let lvl0 = Level::zero();
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        let empty = Expr::app(
            Expr::const_(Name::from_string("Finset.empty"), vec![lvl0.clone()]),
            nat.clone(),
        );
        // Finset.Mem 0 Finset.empty : Prop
        let mem_goal = Expr::apps(
            Expr::const_(Name::from_string("Finset.Mem"), vec![lvl0.clone()]),
            [nat.clone(), zero.clone(), empty.clone()],
        );
        let inferred = tc
            .infer_type(&mem_goal)
            .expect("Finset.Mem 0 Finset.empty should type-check");
        assert!(
            tc.is_def_eq(&inferred, &prop),
            "membership of an element in a Finset is a Prop"
        );
    }

    /// Faithfulness: a `Finset` is a `Subtype` of the genuine `Multiset`
    /// quotient, so two `Finset`s whose underlying lists are permutations are
    /// *equal*. We build `Finset Nat` values backed by `{0,1}` and `{1,0}` (via
    /// `Multiset.cons`, which respects `List.Perm`) and prove their underlying
    /// multisets are equal with `Quot.sound`, then transport equality to the
    /// `Subtype` values — confirming `Finset` equality is up to permutation.
    ///
    /// Concretely we kernel-check that `Quot.sound (List.Perm.swap ...)` proves
    /// `Multiset.cons 0 (Multiset.cons 1 nil) = Multiset.cons 1 (Multiset.cons 0 nil)`,
    /// the underlying `val`-equality that makes the two single-`Nodup`-witness
    /// Finsets equal.
    #[test]
    fn test_finset_underlying_multiset_order_insensitive() {
        let env = env_with_finset();
        let tc = TypeChecker::new(&env);

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            zero.clone(),
        );
        let lvl0 = Level::zero();
        let lvl1 = Level::succ(Level::zero());

        let list_nat = Expr::app(
            Expr::const_(Name::from_string("List"), vec![lvl0.clone()]),
            nat.clone(),
        );
        let nil_nat = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![lvl0.clone()]),
            nat.clone(),
        );
        let cons_nat = |h: Expr, t: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![lvl0.clone()]),
                [nat.clone(), h, t],
            )
        };
        let perm_rel_nat = Expr::app(
            Expr::const_(Name::from_string("List.Perm"), vec![lvl0.clone()]),
            nat.clone(),
        );
        let mset_nat = Expr::app(
            Expr::const_(Name::from_string("Multiset"), vec![lvl0.clone()]),
            nat.clone(),
        );
        let mcons = |h: Expr, s: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Multiset.cons"), vec![lvl0.clone()]),
                [nat.clone(), h, s],
            )
        };
        let mnil = Expr::app(
            Expr::const_(Name::from_string("Multiset.nil"), vec![lvl0.clone()]),
            nat.clone(),
        );

        // val_lhs = cons 0 (cons 1 nil); val_rhs = cons 1 (cons 0 nil)
        let val_lhs = mcons(zero.clone(), mcons(one.clone(), mnil.clone()));
        let val_rhs = mcons(one.clone(), mcons(zero.clone(), mnil.clone()));
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            [mset_nat.clone(), val_lhs.clone(), val_rhs.clone()],
        );
        // proof: Quot.sound (List.Perm.swap 1 0 []) : Quot.mk [0,1] = Quot.mk [1,0]
        let l01 = cons_nat(zero.clone(), cons_nat(one.clone(), nil_nat.clone()));
        let l10 = cons_nat(one.clone(), cons_nat(zero.clone(), nil_nat.clone()));
        let perm_swap = Expr::apps(
            Expr::const_(Name::from_string("List.Perm.swap"), vec![lvl0.clone()]),
            [nat.clone(), one.clone(), zero.clone(), nil_nat.clone()],
        );
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Quot.sound"), vec![lvl1.clone()]),
            [list_nat.clone(), perm_rel_nat.clone(), l01, l10, perm_swap],
        );
        let inferred = tc
            .infer_type(&proof)
            .expect("underlying-multiset order-insensitivity proof should type-check");
        assert!(
            tc.is_def_eq(&inferred, &goal),
            "the Multiset underlying a Finset is order-insensitive (up to Perm)"
        );
    }

    /// `Multiset.mem_cons_of_mem`, `Finset.mem_cons_self`, and
    /// `Finset.mem_cons_of_mem` are registered, kernel-check at their declared
    /// types, and are domain-axiom-free (closure ⊆ {Quot.sound, propext}). These
    /// are the membership-introduction lemmas a genuine `Fintype` completeness
    /// proof rides over an explicit `Finset.cons` chain.
    #[test]
    fn test_finset_mem_cons_lemmas_constructive() {
        let env = env_with_finset();
        for name in [
            "Multiset.mem_cons_of_mem",
            "Finset.mem_cons_self",
            "Finset.mem_cons_of_mem",
        ] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered"
            );
            assert_value_checks_and_clean(&env, name);
        }
    }

    /// The real `Fintype` structure replaces the old opaque
    /// `Fintype : (α : Type u) → Prop` axiom. It is a Type-valued one-constructor
    /// inductive (`Fintype.mk`) with structure projections `Fintype.elems` and
    /// `Fintype.complete`. All four declarations are registered and kernel-check;
    /// the projections are domain-axiom-free. The type is `Type u → Type u`
    /// (data, not Prop), with an explicit first binder.
    #[test]
    fn test_fintype_structure_registered_and_typed() {
        let env = env_with_finset();
        for name in ["Fintype", "Fintype.mk", "Fintype.elems", "Fintype.complete"] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered"
            );
        }
        // Projections are real definitions; check value + axiom cleanliness.
        for name in ["Fintype.elems", "Fintype.complete"] {
            assert_value_checks_and_clean(&env, name);
        }

        // `Fintype : Type u → Type u` — a data type former, NOT a Prop predicate.
        let info = env
            .get_const(&Name::from_string("Fintype"))
            .expect("Fintype const");
        match info.type_.kind() {
            ExprKind::Pi(bd, dom, body) => {
                assert_eq!(
                    bd.info,
                    BinderInfo::Default,
                    "Fintype's α binder should be explicit (Default), like `Fintype (α : Type*)`"
                );
                // domain Type u = Sort (u+1); codomain Type u = Sort (u+1) (NOT Prop).
                assert!(
                    matches!(dom.kind(), ExprKind::Sort(l) if !l.is_zero()),
                    "Fintype's domain should be a Type universe, got {dom:?}"
                );
                assert!(
                    matches!(body.kind(), ExprKind::Sort(l) if !l.is_zero()),
                    "Fintype α must be Type-valued (data), NOT Prop; got {body:?}"
                );
            }
            other => panic!("Fintype type should be a Pi, got {other:?}"),
        }
    }

    /// End-to-end faithfulness witness: a genuine `Fintype Bool` value built from
    /// the real structure machinery kernel-checks. The carrier is
    /// `Finset.cons true (Finset.cons false Finset.empty h_f) h_t` and the
    /// completeness proof dispatches on `Bool.rec` using `Finset.mem_cons_self` /
    /// `Finset.mem_cons_of_mem`. The `¬mem` witnesses are discharged by
    /// `Bool.noConfusion` (distinct constructors) and `Finset.mem_empty`. The
    /// whole `Fintype.mk` application type-checks at `Fintype Bool`.
    #[test]
    fn test_fintype_bool_instance_kernel_checks() {
        let mut env = env_with_finset();
        // Bring Bool + its noConfusion into scope.
        env.init_bool().expect("Bool should init");
        env.init_true_false().expect("True/False should init");
        if env
            .get_const(&Name::from_string("Bool.noConfusion"))
            .is_none()
        {
            env.regenerate_missing_no_confusion();
        }
        let tc = TypeChecker::new(&env);

        let lvl0 = Level::zero();
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![Level::succ(lvl0.clone())]);
        let not_c = Expr::const_(Name::from_string("Not"), vec![]);
        let no_conf = Expr::const_(Name::from_string("Bool.noConfusion"), vec![lvl0.clone()]);

        let finset_const = Expr::const_(Name::from_string("Finset"), vec![lvl0.clone()]);
        let finset_empty = Expr::app(
            Expr::const_(Name::from_string("Finset.empty"), vec![lvl0.clone()]),
            bool_c.clone(),
        );
        let finset_cons = Expr::const_(Name::from_string("Finset.cons"), vec![lvl0.clone()]);
        let finset_mem = Expr::const_(Name::from_string("Finset.Mem"), vec![lvl0.clone()]);
        let mem_empty = Expr::const_(Name::from_string("Finset.mem_empty"), vec![lvl0.clone()]);
        let mem_self = Expr::const_(
            Name::from_string("Finset.mem_cons_self"),
            vec![lvl0.clone()],
        );
        let mem_of_mem = Expr::const_(
            Name::from_string("Finset.mem_cons_of_mem"),
            vec![lvl0.clone()],
        );

        let fmem = |x: Expr, f: Expr| Expr::apps(finset_mem.clone(), [bool_c.clone(), x, f]);
        let fcons =
            |a: Expr, f: Expr, h: Expr| Expr::apps(finset_cons.clone(), [bool_c.clone(), a, f, h]);
        let not = |p: Expr| Expr::app(not_c.clone(), p);
        let eq_b = |l: Expr, r: Expr| Expr::apps(eq_c.clone(), [bool_c.clone(), l, r]);
        // ¬(l = r) := fun (h : l = r) => @Bool.noConfusion.{0} False l r h
        let ne = |l: Expr, r: Expr| {
            let body = Expr::apps(
                no_conf.clone(),
                [false_c.clone(), l.clone(), r.clone(), Expr::bvar(0)],
            );
            Expr::lam(BinderInfo::Default, eq_b(l, r), body)
        };

        // h_f : ¬ Finset.Mem false Finset.empty := Finset.mem_empty false
        let h_f = Expr::apps(mem_empty.clone(), [bool_c.clone(), bfalse.clone()]);
        // s1 := Finset.cons false Finset.empty h_f
        let s1 = fcons(bfalse.clone(), finset_empty.clone(), h_f.clone());
        // h_t : ¬ Finset.Mem true s1
        //   goal reduces to ¬ List.Mem true [false]; via not_mem_cons_iff.mpr ⟨ne, not_mem_nil⟩.
        // Build it directly: List.not_mem_cons_iff true false [] .mpr (And.intro (ne true false)
        //   (List.not_mem_nil true))  — but the Finset goal is def-eq to ¬List.Mem true [false].
        let h_t = {
            let nmci = Expr::const_(
                Name::from_string("List.not_mem_cons_iff"),
                vec![lvl0.clone()],
            );
            let iff_mpr = Expr::const_(Name::from_string("Iff.mpr"), vec![]);
            let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
            let not_mem_nil =
                Expr::const_(Name::from_string("List.not_mem_nil"), vec![lvl0.clone()]);
            let list_nil = Expr::app(
                Expr::const_(Name::from_string("List.nil"), vec![lvl0.clone()]),
                bool_c.clone(),
            );
            let list_mem = Expr::const_(Name::from_string("List.Mem"), vec![lvl0.clone()]);
            let lmem = |x: Expr, l: Expr| Expr::apps(list_mem.clone(), [bool_c.clone(), x, l]);
            // ¬(true=false)
            let ne_tf = ne(btrue.clone(), bfalse.clone());
            let ne_tf_ty = not(eq_b(btrue.clone(), bfalse.clone()));
            // ¬ List.Mem true []
            let nmem_nil = Expr::apps(not_mem_nil.clone(), [bool_c.clone(), btrue.clone()]);
            let nmem_nil_ty = not(lmem(btrue.clone(), list_nil.clone()));
            // And.intro (¬(true=false)) (¬Mem true []) ne_tf nmem_nil
            let conj = Expr::apps(
                and_intro.clone(),
                [ne_tf_ty.clone(), nmem_nil_ty.clone(), ne_tf, nmem_nil],
            );
            // List.not_mem_cons_iff true false [] : ¬Mem true (false::[]) ↔ (¬(true=false) ∧ ¬Mem true [])
            let iff_t = Expr::apps(
                nmci.clone(),
                [
                    bool_c.clone(),
                    btrue.clone(),
                    bfalse.clone(),
                    list_nil.clone(),
                ],
            );
            let lhs = not(lmem(
                btrue.clone(),
                Expr::apps(
                    Expr::const_(Name::from_string("List.cons"), vec![lvl0.clone()]),
                    [bool_c.clone(), bfalse.clone(), list_nil.clone()],
                ),
            ));
            let rhs = {
                let and_c = Expr::const_(Name::from_string("And"), vec![]);
                Expr::apps(and_c, [ne_tf_ty, nmem_nil_ty])
            };
            // Iff.mpr lhs rhs iff_t conj : ¬Mem true (false::[])  (def-eq the Finset goal)
            Expr::apps(iff_mpr.clone(), [lhs, rhs, iff_t, conj])
        };
        // elems := Finset.cons true s1 h_t
        let elems = fcons(btrue.clone(), s1.clone(), h_t.clone());

        // complete : ∀ (a : Bool), Finset.Mem a elems
        //   := fun a => @Bool.rec (fun a => Finset.Mem a elems) <false-case> <true-case> a
        let complete = {
            let motive = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_c.clone());
                let body = fmem(a.clone(), elems.clone());
                let e = b.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), body);
                b.finish(e)
            };
            // Bool.rec.{0} eliminating into Prop (Sort 0).
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![lvl0.clone()]);
            // false-case : Finset.Mem false elems
            //   = mem_cons_of_mem false true s1 h_t (mem_cons_self false empty h_f)
            let mem_false_s1 = Expr::apps(
                mem_self.clone(),
                [
                    bool_c.clone(),
                    bfalse.clone(),
                    finset_empty.clone(),
                    h_f.clone(),
                ],
            );
            let false_case = Expr::apps(
                mem_of_mem.clone(),
                [
                    bool_c.clone(),
                    bfalse.clone(),
                    btrue.clone(),
                    s1.clone(),
                    h_t.clone(),
                    mem_false_s1,
                ],
            );
            // true-case : Finset.Mem true elems = mem_cons_self true s1 h_t
            let true_case = Expr::apps(
                mem_self.clone(),
                [bool_c.clone(), btrue.clone(), s1.clone(), h_t.clone()],
            );
            // Bool.rec minors in ctor order: false, then true.
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bool_c.clone());
            let rec_app = Expr::apps(bool_rec.clone(), [motive, false_case, true_case, a.clone()]);
            let e = b.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), rec_app);
            b.finish(e)
        };

        // @Fintype.mk Bool elems complete : Fintype Bool
        let fintype_mk = Expr::const_(Name::from_string("Fintype.mk"), vec![lvl0.clone()]);
        let inst = Expr::apps(fintype_mk, [bool_c.clone(), elems.clone(), complete]);
        let fintype_bool = Expr::app(finset_const_to_fintype(&lvl0), bool_c.clone());

        let inferred = tc
            .infer_type(&inst)
            .expect("Fintype Bool instance should type-check");
        assert!(
            tc.is_def_eq(&inferred, &fintype_bool),
            "the constructed instance must inhabit `Fintype Bool`, got {inferred:?}"
        );
        assert!(
            !inst.has_sorry(),
            "the constructed Fintype Bool instance must be sorry-free"
        );
    }

    fn finset_const_to_fintype(lvl0: &Level) -> Expr {
        Expr::const_(Name::from_string("Fintype"), vec![lvl0.clone()])
    }
}
