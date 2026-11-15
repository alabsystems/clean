// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parametric `List.decEq : {α : Type u} → [DecidableEq α] → (xs ys : List α) →
//! Decidable (Eq xs ys)` and the instance `instDecidableEqList : {α : Type u} →
//! [DecidableEq α] → DecidableEq (List α)` — real kernel terms (NO `sorry`, NO
//! axiom).
//!
//! # Why this exists
//!
//! `algebra_list_char_dec_eq_proof.rs` already carries the MONOMORPHIC
//! `ListChar.decEq`, which backs the constructive `String.decEq`. Nothing
//! carried `DecidableEq (List α)` for any other element type, so
//! `Decidable ([1] = [1] : List Nat)` had no candidate at all and `deriving
//! DecidableEq` over a `terms : List T` field fail-closed with `Unsupported`.
//! This file is the universe-polymorphic, element-generic form of the same
//! proof; `ListChar.decEq` is left alone because `String.decEq` and its
//! `.olean` dedup lane are written against that exact constant.
//!
//! # Proof sketch
//!
//! Identical in shape to the `List Char` proof — double structural recursion via
//! `List.rec`, the OUTER motive returning a function (the
//! `data_typeclasses_beq_list` trick), with `Char.decEq` replaced by the element
//! instance threaded through `decEq`:
//!
//! ```text
//! C xs := (ys : List α) → Decidable (Eq (List α) xs ys)
//!
//! List.decEq.{u} : {α : Type u} → [inst : DecidableEq α] →
//!                  (xs ys : List α) → Decidable (Eq xs ys) :=
//!   fun {α} [inst] xs ys => (@List.rec.{u+1,u} α C nilCase consCase xs) ys
//!
//!   nilCase : C nil = fun ys => @List.rec.{1,u} α (fun _ => Decidable (Eq nil _))
//!       (isTrue (Eq.refl nil))                          -- nil = nil
//!       (fun hd' tl' _ih =>                             -- nil ≠ cons
//!          isFalse (fun h => noConf nil (cons hd' tl') h))
//!       ys
//!
//!   consCase : fun hd tl (ih : C tl) ys =>
//!       @List.rec.{1,u} α (fun _ => Decidable (Eq (cons hd tl) _))
//!         (isFalse (fun h => noConf (cons hd tl) nil h))   -- cons ≠ nil
//!         (fun hd' tl' _ih2 =>                             -- cons/cons
//!            @Decidable.rec.{1} (Eq α hd hd') hdMotive hdFalse hdTrue
//!              (@decEq.{u+1} α inst hd hd'))
//!         ys
//! ```
//!
//! where `noConf lhs rhs h` is the v4.30 heterogeneous application
//! (designs/2026-07-03-noconfusion-ctoridx-convention.md §3/§5-N2):
//!
//! ```text
//! noConf lhs rhs h :=
//!   @List.noConfusion.{0,u} False α lhs α rhs
//!     (@Eq.refl.{u+2} (Type u) α)               -- α = α' premise (params equal)
//!     (@heq_of_eq.{u+1} (List α) lhs rhs h)     -- t ≍ t' major premise
//! ```
//!
//! The cons/cons leaf dispatches first on the element decision, then (in the
//! head-equal branch) on `ih tl'`:
//! - **both isTrue**: lift to `cons hd tl = cons hd' tl'` by two `congrArg`s +
//!   `Eq.trans`.
//! - **head isFalse**: cons-injectivity on the head via `noConf`, converting the
//!   `HEq` field hypothesis back with `eq_of_heq`.
//! - **tail isFalse**: the same, on the tail hypothesis.
//!
//! # Universe bookkeeping
//!
//! `α : Type u = Sort (u+1)` and `List.{u} α : Type u`, so `Eq`, `HEq`,
//! `heq_of_eq`, `eq_of_heq`, `congrArg`, `DecidableEq` and `decEq` are all
//! instantiated at `u+1`, and the `α = α` noConfusion premise at `u+2`. The
//! OUTER `List.rec` motive lands in `Sort (imax (u+1) 1) = Sort (u+1)` (the
//! `(ys : List α) → Decidable …` function type), the INNER one in `Sort 1`
//! (`Decidable …`); at `u = 0` the two coincide, which is why the `List Char`
//! proof gets away with a single `List.rec.{1,0}`.
//!
//! # Axiom closure
//!
//! The term mentions only `Eq`/`Eq.refl`/`Eq.trans`, `HEq`/`heq_of_eq`/
//! `eq_of_heq`, `List`/`List.nil`/`List.cons`/`List.rec`/`List.noConfusion`,
//! `DecidableEq`/`decEq`, `congrArg`, `Decidable`(`.rec`/`.isTrue`/`.isFalse`)
//! and `False` — all constructive. So `env.axiom_deps("List.decEq")` is empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment, KernelInstanceInfo};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `List.decEq` and the parametric `instDecidableEqList` instance.
    ///
    /// # Contract
    ///
    /// REQUIRES: `List`(+ctors/rec/noConfusion), `Eq`(+`Eq.refl`/`Eq.trans`),
    ///           `HEq`(+`heq_of_eq`/`eq_of_heq`), `congrArg`,
    ///           `Decidable`(+ctors/rec), `DecidableEq`, `decEq` and `False` are
    ///           registered. Runs from the tail of `init_decidable_eq`, by which
    ///           point `DecidableEq`/`decEq` exist; the `List`/`Eq`/`HEq`
    ///           prerequisites are auto-initialized here.
    /// ENSURES: On success, `List.decEq` is a `Definition` whose value
    ///          type-checks at `{α : Type u} → [DecidableEq α] → (xs ys : List α)
    ///          → Decidable (Eq xs ys)` with an empty axiom closure, and
    ///          `instDecidableEqList` is a registered `DecidableEq` instance.
    /// ENSURES: Idempotent; skipped cleanly on a sparser env missing a
    ///          prerequisite, and in IMPORT MODE (see below).
    pub(crate) fn register_list_dec_eq_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): withheld for the same
        // reason `init_beq_list` withholds `List.beq` — Lean v4.30 ships its own
        // `List.decEq`/`instDecidableEqList` (as a brecOn tower), so a seeded
        // Clean twin fails the value-defeq dedup and cascades through the
        // `Init.Data.List.Basic` lemma web. The genuine pair imports through the
        // checked `add_decl` path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("List.decEq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Dependencies. `init_true_false` before `init_decidable` so
        // `Decidable.isFalse` carries the real `(p → False)` negation type.
        self.init_eq()?;
        self.init_heq()?;
        self.init_list()?;
        self.init_true_false()?;
        self.init_decidable()?;
        if self
            .get_const(&Name::from_string("List.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }
        // `DecidableEq`/`decEq` come from `init_decidable_eq`, which is this
        // function's only caller — but a sparser env could reach here another
        // way, so skip cleanly rather than build an ill-typed term.
        let have_prereqs = self.get_const(&Name::from_string("DecidableEq")).is_some()
            && self.get_const(&Name::from_string("decEq")).is_some()
            && self.get_const(&Name::from_string("congrArg")).is_some()
            && self.get_const(&Name::from_string("List.rec")).is_some()
            && self
                .get_const(&Name::from_string("List.noConfusion"))
                .is_some()
            && self.get_const(&Name::from_string("heq_of_eq")).is_some()
            && self.get_const(&Name::from_string("eq_of_heq")).is_some();
        if !have_prereqs {
            return Ok(());
        }

        // ----- levels -----
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        // α : Type u = Sort (u+1); List α : Type u too.
        let succ_u = Level::succ(u_level.clone());
        // `Type u` itself lives in `Sort (u+2)` — the noConfusion param premise.
        let succ_succ_u = Level::succ(succ_u.clone());
        let lvl_one = Level::succ(Level::zero());
        let type_u = Expr::sort(succ_u.clone());

        // ----- shared constants -----
        let list_c = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let nil_c = Expr::const_(Name::from_string("List.nil"), vec![u_level.clone()]);
        let cons_c = Expr::const_(Name::from_string("List.cons"), vec![u_level.clone()]);
        // OUTER motive `(ys : List α) → Decidable …` : Sort (u+1).
        let list_rec_out = Expr::const_(
            Name::from_string("List.rec"),
            vec![succ_u.clone(), u_level.clone()],
        );
        // INNER motive `Decidable …` : Sort 1.
        let list_rec_in = Expr::const_(
            Name::from_string("List.rec"),
            vec![lvl_one.clone(), u_level.clone()],
        );
        // List.noConfusion.{w=0, u}: P = False : Sort 0, element univ u.
        let list_no_conf = Expr::const_(
            Name::from_string("List.noConfusion"),
            vec![Level::zero(), u_level.clone()],
        );

        let eq_cst = Expr::const_(Name::from_string("Eq"), vec![succ_u.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![succ_u.clone()]);
        let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![succ_u.clone()]);
        let eq_refl_param = Expr::const_(Name::from_string("Eq.refl"), vec![succ_succ_u]);
        let heq_cst = Expr::const_(Name::from_string("HEq"), vec![succ_u.clone()]);
        let heq_of_eq = Expr::const_(Name::from_string("heq_of_eq"), vec![succ_u.clone()]);
        let eq_of_heq = Expr::const_(Name::from_string("eq_of_heq"), vec![succ_u.clone()]);
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![succ_u.clone(), succ_u.clone()],
        );
        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![lvl_one.clone()]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let dec_eq_cls = Expr::const_(Name::from_string("DecidableEq"), vec![succ_u.clone()]);
        let dec_eq_fn = Expr::const_(Name::from_string("decEq"), vec![succ_u.clone()]);

        // ----- type: {α : Type u} → [inst : DecidableEq α] →
        //             (xs ys : List α) → Decidable (Eq (List α) xs ys)
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let dec_eq_alpha = Expr::app(dec_eq_cls.clone(), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(dec_eq_alpha.clone());
            let list_a = Expr::app(list_c.clone(), alpha.clone());

            let core = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (xs_id, xs) = c.fresh_local(list_a.clone());
                let (ys_id, ys) = c.fresh_local(list_a.clone());
                let concl = Expr::app(
                    dec.clone(),
                    Expr::apps(eq_cst.clone(), [list_a.clone(), xs, ys]),
                );
                let e = c.mk_pi(ys_id, BinderInfo::Default, list_a.clone(), concl);
                c.finish_child(c.mk_pi(xs_id, BinderInfo::Default, list_a.clone(), e))
            };
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, dec_eq_alpha, core);
            b.finish(b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e))
        };

        // ----- value -----
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let dec_eq_alpha = Expr::app(dec_eq_cls.clone(), alpha.clone());
            let (inst_id, inst) = b.fresh_local(dec_eq_alpha.clone());

            // α-dependent shorthands. Every closure below captures only `alpha`
            // / `inst` (the two root FVars) plus closed constants, so each child
            // builder may use them freely.
            let list_a = Expr::app(list_c.clone(), alpha.clone());
            let nil = Expr::app(nil_c.clone(), alpha.clone());
            let cons = |hd: Expr, tl: Expr| Expr::apps(cons_c.clone(), [alpha.clone(), hd, tl]);
            let eq_l = |l: Expr, r: Expr| Expr::apps(eq_cst.clone(), [list_a.clone(), l, r]);
            let eq_a = |l: Expr, r: Expr| Expr::apps(eq_cst.clone(), [alpha.clone(), l, r]);
            let heq_a = |l: Expr, r: Expr| {
                Expr::apps(heq_cst.clone(), [alpha.clone(), l, alpha.clone(), r])
            };
            let heq_l = |l: Expr, r: Expr| {
                Expr::apps(heq_cst.clone(), [list_a.clone(), l, list_a.clone(), r])
            };
            let eq_of_heq_a =
                |l: Expr, r: Expr, h: Expr| Expr::apps(eq_of_heq.clone(), [alpha.clone(), l, r, h]);
            let eq_of_heq_l = |l: Expr, r: Expr, h: Expr| {
                Expr::apps(eq_of_heq.clone(), [list_a.clone(), l, r, h])
            };
            let dec_eq_l = |l: Expr, r: Expr| Expr::app(dec.clone(), eq_l(l, r));
            let mk_true = |prop: Expr, pf: Expr| Expr::apps(is_true.clone(), [prop, pf]);
            let mk_false = |prop: Expr, neg: Expr| Expr::apps(is_false.clone(), [prop, neg]);
            // `@decEq.{u+1} α inst x y : Decidable (Eq α x y)` — the element
            // decision, taken from the instance premise rather than from a
            // hard-wired `Char.decEq`.
            let elem_dec = |x: Expr, y: Expr| {
                Expr::apps(dec_eq_fn.clone(), [alpha.clone(), inst.clone(), x, y])
            };
            // `@Eq.refl.{u+2} (Type u) α : @Eq.{u+2} (Type u) α α` — the v4.30
            // noConfusion params-equal premise.
            let param_refl = Expr::apps(eq_refl_param.clone(), [type_u.clone(), alpha.clone()]);
            // v4.30 application: for DISTINCT constructors this term IS `False`
            // (noConfusionType δι-reduces to `False`); for the cons/cons diagonal
            // it has type `(hd ≍ hd' → tl ≍ tl' → False) → False`.
            let noconf = |lhs: Expr, rhs: Expr, h: Expr| {
                let major = Expr::apps(
                    heq_of_eq.clone(),
                    [list_a.clone(), lhs.clone(), rhs.clone(), h],
                );
                Expr::apps(
                    list_no_conf.clone(),
                    [
                        false_c.clone(),
                        alpha.clone(),
                        lhs,
                        alpha.clone(),
                        rhs,
                        param_refl.clone(),
                        major,
                    ],
                )
            };

            // outer motive C: fun (xs : List α) => (ys : List α) → Decidable (Eq xs ys)
            let outer_c = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (xs_id, xs) = c.fresh_local(list_a.clone());
                let inner = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (ys_id, ys) = d.fresh_local(list_a.clone());
                    let body = dec_eq_l(xs.clone(), ys);
                    d.finish_child(d.mk_pi(ys_id, BinderInfo::Default, list_a.clone(), body))
                };
                c.finish_child(c.mk_lam(xs_id, BinderInfo::Default, list_a.clone(), inner))
            };

            // nilCase : fun (ys : List α) => @List.rec.{1,u} α nInnerC nNil nCons ys
            let nil_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ys_id, ys) = c.fresh_local(list_a.clone());

                // nInnerC : fun (_ys : List α) => Decidable (Eq nil _ys)
                let n_inner_c = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (yc_id, yc) = d.fresh_local(list_a.clone());
                    let body = dec_eq_l(nil.clone(), yc);
                    d.finish_child(d.mk_lam(yc_id, BinderInfo::Default, list_a.clone(), body))
                };
                // nNil : isTrue (Eq.refl nil)
                let n_nil = mk_true(
                    eq_l(nil.clone(), nil.clone()),
                    Expr::apps(eq_refl.clone(), [list_a.clone(), nil.clone()]),
                );
                // nCons : fun hd' tl' _ih => isFalse (fun h => noConf nil (cons hd' tl') h)
                let n_cons = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hdp_id, hdp) = d.fresh_local(alpha.clone());
                    let (tlp_id, tlp) = d.fresh_local(list_a.clone());
                    let (ih_id, _ih) = d.fresh_local(dec_eq_l(nil.clone(), tlp.clone()));
                    let cons_p = cons(hdp.clone(), tlp.clone());
                    let prop = eq_l(nil.clone(), cons_p.clone());
                    let neg = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (h_id, h) = e.fresh_local(prop.clone());
                        let body = noconf(nil.clone(), cons_p.clone(), h);
                        e.finish_child(e.mk_lam(h_id, BinderInfo::Default, prop.clone(), body))
                    };
                    let body = mk_false(prop, neg);
                    let e = d.mk_lam(
                        ih_id,
                        BinderInfo::Default,
                        dec_eq_l(nil.clone(), tlp.clone()),
                        body,
                    );
                    let e = d.mk_lam(tlp_id, BinderInfo::Default, list_a.clone(), e);
                    d.finish_child(d.mk_lam(hdp_id, BinderInfo::Default, alpha.clone(), e))
                };
                let rec_body = Expr::apps(
                    list_rec_in.clone(),
                    [alpha.clone(), n_inner_c, n_nil, n_cons, ys],
                );
                c.finish_child(c.mk_lam(ys_id, BinderInfo::Default, list_a.clone(), rec_body))
            };

            // consCase : fun (hd : α)(tl : List α)(ih : C tl)(ys : List α) =>
            //              @List.rec.{1,u} α cInnerC cNil cCons ys
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hd_id, hd) = c.fresh_local(alpha.clone());
                let (tl_id, tl) = c.fresh_local(list_a.clone());
                // ih : (ys : List α) → Decidable (Eq tl ys)
                let ih_ty = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (ys_id, ys) = d.fresh_local(list_a.clone());
                    let body = dec_eq_l(tl.clone(), ys);
                    d.finish_child(d.mk_pi(ys_id, BinderInfo::Default, list_a.clone(), body))
                };
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let (ys_id, ys) = c.fresh_local(list_a.clone());

                let cons_xs = cons(hd.clone(), tl.clone());

                // cInnerC : fun (_ys : List α) => Decidable (Eq (cons hd tl) _ys)
                let c_inner_c = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (yc_id, yc) = d.fresh_local(list_a.clone());
                    let body = dec_eq_l(cons_xs.clone(), yc);
                    d.finish_child(d.mk_lam(yc_id, BinderInfo::Default, list_a.clone(), body))
                };
                // cNil : isFalse (fun h => noConf (cons hd tl) nil h)
                let c_nil = {
                    let prop = eq_l(cons_xs.clone(), nil.clone());
                    let neg = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (h_id, h) = d.fresh_local(prop.clone());
                        let body = noconf(cons_xs.clone(), nil.clone(), h);
                        d.finish_child(d.mk_lam(h_id, BinderInfo::Default, prop.clone(), body))
                    };
                    mk_false(prop, neg)
                };
                // cCons : fun hd' tl' _ih2 =>
                //   @Decidable.rec.{1} (Eq α hd hd') hdMotive hdFalse hdTrue (decEq α inst hd hd')
                let c_cons = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hdp_id, hdp) = d.fresh_local(alpha.clone());
                    let (tlp_id, tlp) = d.fresh_local(list_a.clone());
                    let (ih2_id, _ih2) = d.fresh_local(dec_eq_l(cons_xs.clone(), tlp.clone()));

                    let cons_ys = cons(hdp.clone(), tlp.clone());
                    let goal = eq_l(cons_xs.clone(), cons_ys.clone());
                    let p_head = eq_a(hd.clone(), hdp.clone());

                    // hdMotive : fun (_ : Decidable p_head) => Decidable goal
                    let hd_motive = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (ds_id, _ds) = e.fresh_local(Expr::app(dec.clone(), p_head.clone()));
                        e.finish_child(e.mk_lam(
                            ds_id,
                            BinderInfo::Default,
                            Expr::app(dec.clone(), p_head.clone()),
                            Expr::app(dec.clone(), goal.clone()),
                        ))
                    };

                    // hdFalse : fun (hne_h : p_head → False) =>
                    //   isFalse (fun (h : goal) =>
                    //     noConf … h (fun he ht => hne_h (eq_of_heq he)))
                    let hd_false = {
                        let not_p = Expr::pi(BinderInfo::Default, p_head.clone(), false_c.clone());
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (hne_id, hne) = e.fresh_local(not_p.clone());
                        let neg = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (h_id, h) = g.fresh_local(goal.clone());
                            let cont = {
                                let mut k = EnvDeclBuilder::child_of(&g);
                                let he_ty = heq_a(hd.clone(), hdp.clone());
                                let (he_id, he) = k.fresh_local(he_ty.clone());
                                let ht_ty = heq_l(tl.clone(), tlp.clone());
                                let (ht_id, _ht) = k.fresh_local(ht_ty.clone());
                                let body = Expr::app(
                                    hne.clone(),
                                    eq_of_heq_a(hd.clone(), hdp.clone(), he),
                                );
                                let body = k.mk_lam(ht_id, BinderInfo::Default, ht_ty, body);
                                k.finish_child(k.mk_lam(he_id, BinderInfo::Default, he_ty, body))
                            };
                            let nc = noconf(cons_xs.clone(), cons_ys.clone(), h);
                            let body = Expr::app(nc, cont);
                            g.finish_child(g.mk_lam(h_id, BinderInfo::Default, goal.clone(), body))
                        };
                        let body = mk_false(goal.clone(), neg);
                        e.finish_child(e.mk_lam(hne_id, BinderInfo::Default, not_p, body))
                    };

                    // hdTrue : fun (heq_h : p_head) =>
                    //   @Decidable.rec.{1} (Eq tl tl') tlMotive tlFalse tlTrue (ih tl')
                    let hd_true = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (heqh_id, heqh) = e.fresh_local(p_head.clone());
                        let p_tail = eq_l(tl.clone(), tlp.clone());

                        let tl_motive = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (ds_id, _ds) =
                                g.fresh_local(Expr::app(dec.clone(), p_tail.clone()));
                            g.finish_child(g.mk_lam(
                                ds_id,
                                BinderInfo::Default,
                                Expr::app(dec.clone(), p_tail.clone()),
                                Expr::app(dec.clone(), goal.clone()),
                            ))
                        };

                        let tl_false = {
                            let not_p =
                                Expr::pi(BinderInfo::Default, p_tail.clone(), false_c.clone());
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (hnet_id, hnet) = g.fresh_local(not_p.clone());
                            let neg = {
                                let mut k = EnvDeclBuilder::child_of(&g);
                                let (h_id, h) = k.fresh_local(goal.clone());
                                let cont = {
                                    let mut m = EnvDeclBuilder::child_of(&k);
                                    let he_ty = heq_a(hd.clone(), hdp.clone());
                                    let (he_id, _he) = m.fresh_local(he_ty.clone());
                                    let ht_ty = heq_l(tl.clone(), tlp.clone());
                                    let (ht_id, ht) = m.fresh_local(ht_ty.clone());
                                    let body = Expr::app(
                                        hnet.clone(),
                                        eq_of_heq_l(tl.clone(), tlp.clone(), ht),
                                    );
                                    let body = m.mk_lam(ht_id, BinderInfo::Default, ht_ty, body);
                                    m.finish_child(m.mk_lam(
                                        he_id,
                                        BinderInfo::Default,
                                        he_ty,
                                        body,
                                    ))
                                };
                                let nc = noconf(cons_xs.clone(), cons_ys.clone(), h);
                                let body = Expr::app(nc, cont);
                                k.finish_child(k.mk_lam(
                                    h_id,
                                    BinderInfo::Default,
                                    goal.clone(),
                                    body,
                                ))
                            };
                            let body = mk_false(goal.clone(), neg);
                            g.finish_child(g.mk_lam(hnet_id, BinderInfo::Default, not_p, body))
                        };

                        // tlTrue : fun (heq_t : p_tail) => isTrue (consEqLift)
                        let tl_true = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (heqt_id, heqt) = g.fresh_local(p_tail.clone());

                            // step1 = @congrArg α (List α) hd hd' (fun c => cons c tl) heq_h
                            let f_head = {
                                let mut k = EnvDeclBuilder::child_of(&g);
                                let (cc_id, cc) = k.fresh_local(alpha.clone());
                                let body = cons(cc, tl.clone());
                                k.finish_child(k.mk_lam(
                                    cc_id,
                                    BinderInfo::Default,
                                    alpha.clone(),
                                    body,
                                ))
                            };
                            let step1 = Expr::apps(
                                congr_arg.clone(),
                                [
                                    alpha.clone(),
                                    list_a.clone(),
                                    hd.clone(),
                                    hdp.clone(),
                                    f_head,
                                    heqh.clone(),
                                ],
                            );
                            // step2 = @congrArg (List α)(List α) tl tl' (fun t => cons hd' t) heq_t
                            let f_tail = {
                                let mut k = EnvDeclBuilder::child_of(&g);
                                let (tt_id, tt) = k.fresh_local(list_a.clone());
                                let body = cons(hdp.clone(), tt);
                                k.finish_child(k.mk_lam(
                                    tt_id,
                                    BinderInfo::Default,
                                    list_a.clone(),
                                    body,
                                ))
                            };
                            let step2 = Expr::apps(
                                congr_arg.clone(),
                                [
                                    list_a.clone(),
                                    list_a.clone(),
                                    tl.clone(),
                                    tlp.clone(),
                                    f_tail,
                                    heqt,
                                ],
                            );
                            let cons_mid = cons(hdp.clone(), tl.clone());
                            let cons_eq_lift = Expr::apps(
                                eq_trans.clone(),
                                [
                                    list_a.clone(),
                                    cons_xs.clone(),
                                    cons_mid,
                                    cons_ys.clone(),
                                    step1,
                                    step2,
                                ],
                            );
                            let body = mk_true(goal.clone(), cons_eq_lift);
                            g.finish_child(g.mk_lam(
                                heqt_id,
                                BinderInfo::Default,
                                p_tail.clone(),
                                body,
                            ))
                        };

                        let discriminant = Expr::app(ih.clone(), tlp.clone());
                        let rec_app = Expr::apps(
                            dec_rec.clone(),
                            [p_tail.clone(), tl_motive, tl_false, tl_true, discriminant],
                        );
                        e.finish_child(e.mk_lam(
                            heqh_id,
                            BinderInfo::Default,
                            p_head.clone(),
                            rec_app,
                        ))
                    };

                    let discriminant = elem_dec(hd.clone(), hdp.clone());
                    let rec_app = Expr::apps(
                        dec_rec.clone(),
                        [p_head, hd_motive, hd_false, hd_true, discriminant],
                    );
                    let e = d.mk_lam(
                        ih2_id,
                        BinderInfo::Default,
                        dec_eq_l(cons_xs.clone(), tlp.clone()),
                        rec_app,
                    );
                    let e = d.mk_lam(tlp_id, BinderInfo::Default, list_a.clone(), e);
                    d.finish_child(d.mk_lam(hdp_id, BinderInfo::Default, alpha.clone(), e))
                };

                let rec_body = Expr::apps(
                    list_rec_in.clone(),
                    [alpha.clone(), c_inner_c, c_nil, c_cons, ys],
                );
                let e = c.mk_lam(ys_id, BinderInfo::Default, list_a.clone(), rec_body);
                let e = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, e);
                let e = c.mk_lam(tl_id, BinderInfo::Default, list_a.clone(), e);
                c.finish_child(c.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), e))
            };

            // core : fun (xs ys : List α) => (@List.rec.{u+1,u} α C nilCase consCase xs) ys
            let core = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (xs_id, xs) = c.fresh_local(list_a.clone());
                let (ys_id, ys) = c.fresh_local(list_a.clone());
                let rec_xs = Expr::apps(
                    list_rec_out.clone(),
                    [alpha.clone(), outer_c, nil_case, cons_case, xs],
                );
                let body = Expr::app(rec_xs, ys);
                let e = c.mk_lam(ys_id, BinderInfo::Default, list_a.clone(), body);
                c.finish_child(c.mk_lam(xs_id, BinderInfo::Default, list_a.clone(), e))
            };

            let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, dec_eq_alpha, core);
            b.finish(b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e))
        };

        self.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![u.clone()],
            type_,
            value,
            is_reducible: true,
        })?;

        // instDecidableEqList : {α : Type u} → [DecidableEq α] → DecidableEq (List α)
        //   := List.decEq
        //
        // `DecidableEq.{u+1} (List.{u} α)` reducibly unfolds to
        // `(xs ys : List α) → Decidable (Eq xs ys)`, which is exactly the tail of
        // `List.decEq`'s type, so the bare constant type-checks at this type. The
        // value is the bare constant (not an inlined copy) for the reason spelled
        // out at `instDecidableEqNat`: `value: None` makes the elaborator inline
        // the whole recursive body at every use site.
        let inst_name = Name::from_string("instDecidableEqList");
        if self.get_const(&inst_name).is_none() {
            let inst_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let dec_eq_alpha = Expr::app(dec_eq_cls.clone(), alpha.clone());
                let (inst_id, _inst) = b.fresh_local(dec_eq_alpha.clone());
                let concl = Expr::app(dec_eq_cls.clone(), Expr::app(list_c.clone(), alpha.clone()));
                let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, dec_eq_alpha, concl);
                b.finish(b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e))
            };
            self.add_decl(Declaration::Definition {
                name: inst_name.clone(),
                level_params: vec![u.clone()],
                type_: inst_type,
                value: Expr::const_(name.clone(), vec![u_level.clone()]),
                is_reducible: true,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: inst_name,
                class_name: Name::from_string("DecidableEq"),
                priority: crate::env::LEAN_DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    fn mentions(e: &Expr, target: &str) -> bool {
        fn go(e: &Expr, target: &str, hit: &mut bool) {
            if *hit {
                return;
            }
            match e.kind() {
                ExprKind::Const(n, _) if n.to_string() == target => *hit = true,
                ExprKind::App(f, a) => {
                    go(f, target, hit);
                    go(a, target, hit);
                }
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    go(t, target, hit);
                    go(b, target, hit);
                }
                ExprKind::Let(_, t, v, b, _) => {
                    go(t, target, hit);
                    go(v, target, hit);
                    go(b, target, hit);
                }
                _ => {}
            }
        }
        let mut hit = false;
        go(e, target, &mut hit);
        hit
    }

    /// The kernel accepts the parametric `List.decEq` term and registers it as a
    /// `Definition` (not an `Axiom`), idempotently. `with_prelude` already runs
    /// the registration, so this also pins that it is present by default.
    #[test]
    fn test_list_dec_eq_registered_and_type_checks() {
        let mut env = Environment::with_prelude();
        env.register_list_dec_eq_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("List.decEq"))
            .expect("List.decEq should be registered by with_prelude");
        assert_eq!(info.kind, ConstantKind::Definition);
        assert!(info.value.is_some(), "Definition must retain its value");
        assert_eq!(
            info.level_params.len(),
            1,
            "List.decEq is `.{{u}}`-polymorphic"
        );

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("List.decEq"),
                vec![Level::zero()],
            ))
            .expect("List.decEq should type-check at u := 0");
    }

    /// `instDecidableEqList` is a registered, kernel-checked `DecidableEq`
    /// instance — the thing the elaborator's candidate list was missing.
    #[test]
    fn test_inst_decidable_eq_list_is_registered_instance() {
        let env = Environment::with_prelude();
        let info = env
            .get_const(&Name::from_string("instDecidableEqList"))
            .expect("instDecidableEqList should be registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        assert!(
            env.is_instance(&Name::from_string("instDecidableEqList")),
            "instDecidableEqList must be a registered DecidableEq instance"
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("instDecidableEqList"),
                vec![Level::zero()],
            ))
            .expect("instDecidableEqList should type-check at u := 0");
    }

    /// Axiom closure is EMPTY for both — no `sorryAx`, no declared axiom.
    #[test]
    fn test_list_dec_eq_axiom_closure_empty() {
        let env = Environment::with_prelude();
        for name in ["List.decEq", "instDecidableEqList"] {
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

    /// The body genuinely dispatches — guards against a degenerate masquerade.
    #[test]
    fn test_list_dec_eq_uses_real_dispatch() {
        let env = Environment::with_prelude();
        let info = env.get_const(&Name::from_string("List.decEq")).unwrap();
        let value = info.value.as_ref().expect("Definition has value");

        assert!(
            mentions(value, "Decidable.rec"),
            "must dispatch via Decidable.rec"
        );
        assert!(mentions(value, "List.rec"), "must recurse via List.rec");
        assert!(
            mentions(value, "decEq"),
            "must dispatch elements through the DecidableEq premise"
        );
        assert!(
            mentions(value, "List.noConfusion"),
            "must use List.noConfusion"
        );
        assert!(mentions(value, "congrArg"), "must lift via congrArg");
        assert!(!mentions(value, "sorryAx"), "must not contain sorryAx");
    }

    /// The HEAD constant of an application spine, or `None` for a non-`Const`
    /// head. Used instead of `mentions` for the reduction test: both
    /// `Decidable.isTrue` and `Decidable.isFalse` occur syntactically in the
    /// unreduced body, so a `mentions` assertion would pass on a STUCK term.
    fn head_const(e: &Expr) -> Option<String> {
        let mut cur = e.clone();
        loop {
            match cur.kind() {
                ExprKind::App(f, _) => cur = (**f).clone(),
                ExprKind::Const(n, _) => return Some(n.to_string()),
                ExprKind::MData(_, inner) => cur = (**inner).clone(),
                _ => return None,
            }
        }
    }

    /// The instance COMPUTES: `@List.decEq Nat instDecidableEqNat [1] [1]`
    /// whnf-reduces to an `isTrue` HEAD (not a stuck recursor), and the
    /// unequal pair reduces to `isFalse`. A term that merely type-checks is not
    /// enough — `decide` needs the decision to reduce.
    #[test]
    fn test_list_dec_eq_computes_on_nat_literals() {
        let env = Environment::with_prelude();
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let list_nat_dec = Expr::apps(
            Expr::const_(Name::from_string("List.decEq"), vec![Level::zero()]),
            [
                nat.clone(),
                Expr::const_(Name::from_string("instDecidableEqNat"), vec![]),
            ],
        );
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            nat.clone(),
        );
        let cons = |n: u64, tl: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [nat.clone(), Expr::nat_lit(n), tl],
            )
        };

        let tc = TypeChecker::with_mode(&env, env.mode());
        let eq_case = Expr::apps(
            list_nat_dec.clone(),
            [cons(1, nil.clone()), cons(1, nil.clone())],
        );
        let reduced = tc.whnf(&eq_case);
        assert_eq!(
            head_const(&reduced).as_deref(),
            Some("Decidable.isTrue"),
            "[1] = [1] must decide isTrue, got {reduced:?}"
        );

        let ne_case = Expr::apps(list_nat_dec, [cons(1, nil.clone()), cons(2, nil.clone())]);
        let reduced = tc.whnf(&ne_case);
        assert_eq!(
            head_const(&reduced).as_deref(),
            Some("Decidable.isFalse"),
            "[1] = [2] must decide isFalse, got {reduced:?}"
        );
    }
}
