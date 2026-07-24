// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `ListChar.decEq : (xs ys : List Char) → Decidable (Eq xs ys)` —
//! the sound decision procedure for equality of `Char` lists, built as a real
//! kernel term (NO `sorry`, NO axiom). It is the L1 layer beneath the
//! constructive `String.decEq` (a `String` is a single-field wrapper around a
//! `List Char`).
//!
//! # Proof sketch
//!
//! Double structural recursion via `List.rec`, with the OUTER motive returning a
//! function (the data_typeclasses_beq_list trick):
//!
//! ```text
//! C xs := (ys : List Char) → Decidable (Eq (List Char) xs ys)
//!
//! ListChar.decEq : (xs ys : List Char) → Decidable (Eq xs ys) :=
//!   fun xs ys => (@List.rec.{1,0} Char C nilCase consCase xs) ys
//!
//!   nilCase : C nil = fun ys => @List.rec.{1,0} Char (fun _ => Decidable (Eq nil _))
//!       (isTrue (Eq.refl nil))                          -- nil = nil
//!       (fun hd' tl' _ih =>                             -- nil ≠ cons
//!          isFalse (fun h => noConf nil (cons hd' tl') h))
//!       ys
//!
//!   consCase : fun hd tl (ih : C tl) ys =>
//!       @List.rec.{1,0} Char (fun _ => Decidable (Eq (cons hd tl) _))
//!         (isFalse (fun h => noConf (cons hd tl) nil h))   -- cons ≠ nil
//!         (fun hd' tl' _ih2 =>                           -- cons/cons
//!            @Decidable.rec.{1} (Eq Char hd hd') hdMotive hdFalse hdTrue (Char.decEq hd hd'))
//!         ys
//! ```
//!
//! where `noConf lhs rhs h` is the v4.30 heterogeneous application
//! (designs/2026-07-03-noconfusion-ctoridx-convention.md §3/§5-N2):
//!
//! ```text
//! noConf lhs rhs h :=
//!   @List.noConfusion.{0,0} False Char lhs Char rhs
//!     (@Eq.refl.{2} (Type 0) Char)              -- α = α' premise (params equal)
//!     (@heq_of_eq.{1} (List Char) lhs rhs h)    -- t ≍ t' major premise
//! ```
//!
//! In the cons/cons leaf we dispatch first on `Char.decEq hd hd'`, then (in the
//! head-equal branch) on `ih tl'`:
//! - **both isTrue** (`heq_h : hd = hd'`, `heq_t : tl = tl'`): lift to
//!   `cons hd tl = cons hd' tl'` by two `congrArg`s + `Eq.trans` — `consEqLift`.
//! - **head isFalse** (`hne_h : hd = hd' → False`): from `h : cons hd tl =
//!   cons hd' tl'`, `noConf (cons hd tl) (cons hd' tl') h
//!   (fun (he : hd ≍ hd') (ht : tl ≍ tl') => hne_h (eq_of_heq he)) : False` —
//!   cons-injectivity on the head. Under the v4.30 convention both cons fields
//!   mention the param `α`, so the diagonal chain carries `HEq` hypotheses and
//!   the continuation converts with `eq_of_heq`.
//! - **tail isFalse** (`hne_t : tl = tl' → False`): same, applying
//!   `hne_t (eq_of_heq ht)`.
//!
//! Every `isFalse` branch carries a genuine `¬(a = b)` term: for distinct
//! constructors `@List.noConfusionType False Char nil Char (cons _)` δι-reduces
//! to `False` directly; for the cons/cons diagonal `@List.noConfusionType False
//! Char (cons hd tl) Char (cons hd' tl')` δι-reduces to
//! `(hd ≍ hd' → tl ≍ tl' → False) → False`, so the injectivity continuation
//! discharges it.
//!
//! # Axiom closure
//!
//! The term mentions only `Eq`/`Eq.refl`/`Eq.trans`, `HEq`/`heq_of_eq`/
//! `eq_of_heq`, `List`/`List.nil`/`List.cons`/`List.rec`/`List.noConfusion`,
//! `Char`/`Char.decEq`, `congrArg`, `Decidable`(`.rec`/`.isTrue`/`.isFalse`),
//! and `False` — all constructive (generated recursors / reducible definitions
//! / the axiom-free `Char.decEq` and Eq↔HEq bridge). So
//! `env.axiom_deps("ListChar.decEq")` is empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `ListChar.decEq` as a kernel-checked `Declaration::Definition`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `List`, `List.nil`, `List.cons`, `List.rec`, `List.noConfusion`,
    ///           `Char`, `Char.decEq`, `Eq`(+`Eq.refl`/`Eq.trans`), `congrArg`,
    ///           `Decidable`(+ctors/rec), `False` are registered (auto-initialized
    ///           here; `Char.decEq` is the axiom-free wrapper proof).
    /// ENSURES: On success, `ListChar.decEq` is a `Definition` whose value
    ///          type-checks at `(xs ys : List Char) → Decidable (Eq xs ys)` and
    ///          whose axiom closure is empty.
    /// ENSURES: Idempotent.
    pub(crate) fn register_list_char_dec_eq_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("ListChar.decEq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Dependencies. `init_true_false` before `init_decidable` so
        // `Decidable.isFalse` carries the real `(p → False)` negation type.
        self.init_eq()?;
        // HEq + the heq_of_eq/eq_of_heq bridge: the v4.30 noConfusion
        // convention takes an `α = α'` premise plus a `t ≍ t'` major, and the
        // cons/cons diagonal chain carries HEq field hypotheses.
        self.init_heq()?;
        self.init_list()?;
        self.init_char()?;
        self.init_true_false()?;
        self.init_decidable()?;
        // `Char.decEq` — the axiom-free `Nat`-wrapper decision procedure.
        if self.get_const(&Name::from_string("Char.decEq")).is_none() {
            self.register_wrapper_dec_eq_proof("Char")?;
        }
        // `List.noConfusion` for the distinct-constructor / cons-injectivity arms.
        if self
            .get_const(&Name::from_string("List.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        // ----- shared constants -----
        let type0 = Level::zero();
        let type1 = Level::succ(Level::zero());

        let char_c = Expr::const_(Name::from_string("Char"), vec![]);
        // Char : Type 0 ⟹ List.{0} Char : Type 0
        let list_c = Expr::const_(Name::from_string("List"), vec![type0.clone()]);
        let list_char = Expr::app(list_c.clone(), char_c.clone());
        // `List.nil {α}` is implicit in α — apply `Char` explicitly: `@List.nil.{0} Char`.
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![type0.clone()]),
            char_c.clone(),
        );
        let cons_c = Expr::const_(Name::from_string("List.cons"), vec![type0.clone()]);
        // List.rec.{v, u}: outer/inner motives land in Sort 1 (the function type
        // `(ys) → Decidable …` and `Decidable …` both live in Type 0 = Sort 1).
        let list_rec = Expr::const_(
            Name::from_string("List.rec"),
            vec![type1.clone(), type0.clone()],
        );
        // List.noConfusion.{w=0, u=0}: P = False : Sort 0, element univ Char : 0.
        let list_no_conf = Expr::const_(
            Name::from_string("List.noConfusion"),
            vec![type0.clone(), type0.clone()],
        );
        // v4.30 heterogeneous premises (design §3): the param premise is
        // `@Eq.{2} (Type 0) Char Char`, discharged by refl; the major premise
        // is `Char lists ≍`, obtained from the Eq hypothesis via heq_of_eq.
        let type2 = Level::succ(type1.clone());
        // `Type 0` = `Sort 1` — the instantiated `List.{0}` param domain.
        let sort1 = Expr::from_kind(crate::expr::ExprKind::Sort(type1.clone()));
        // @Eq.refl.{2} (Type 0) Char : @Eq.{2} (Type 0) Char Char
        let char_param_refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![type2]),
            [sort1, char_c.clone()],
        );
        let heq_of_eq_lc = Expr::const_(Name::from_string("heq_of_eq"), vec![type1.clone()]);
        let eq_of_heq_ch = Expr::const_(Name::from_string("eq_of_heq"), vec![type1.clone()]);
        let eq_of_heq_lc = Expr::const_(Name::from_string("eq_of_heq"), vec![type1.clone()]);
        let heq_ch = Expr::const_(Name::from_string("HEq"), vec![type1.clone()]);
        let heq_lc = Expr::const_(Name::from_string("HEq"), vec![type1.clone()]);

        let char_dec_eq = Expr::const_(Name::from_string("Char.decEq"), vec![]);

        // Eq.{1} on List Char and on Char (both : Type 0 = Sort 1).
        let eq_lc = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_ch = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_refl_lc = Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]);
        let eq_trans_lc = Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]);

        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![type1.clone()]);
        // congrArg.{1,1}: Char → List Char and List Char → List Char.
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![type1.clone(), type1.clone()],
        );
        let false_c = Expr::const_(Name::from_string("False"), vec![]);

        // ----- helper closures -----
        let cons = |hd: Expr, tl: Expr| Expr::apps(cons_c.clone(), [char_c.clone(), hd, tl]);
        let eq_l = |l: Expr, r: Expr| Expr::apps(eq_lc.clone(), [list_char.clone(), l, r]);
        let eq_c = |l: Expr, r: Expr| Expr::apps(eq_ch.clone(), [char_c.clone(), l, r]);
        // Heterogeneous (v4.30 diagonal-chain) hypotheses: `hd ≍ hd'` /
        // `tl ≍ tl'` — homogeneous instances of HEq, converted back to Eq
        // with eq_of_heq where the branch needs the Eq form.
        let heq_c =
            |l: Expr, r: Expr| Expr::apps(heq_ch.clone(), [char_c.clone(), l, char_c.clone(), r]);
        let heq_l = |l: Expr, r: Expr| {
            Expr::apps(heq_lc.clone(), [list_char.clone(), l, list_char.clone(), r])
        };
        let eq_of_heq_c =
            |l: Expr, r: Expr, h: Expr| Expr::apps(eq_of_heq_ch.clone(), [char_c.clone(), l, r, h]);
        let eq_of_heq_l = |l: Expr, r: Expr, h: Expr| {
            Expr::apps(eq_of_heq_lc.clone(), [list_char.clone(), l, r, h])
        };
        let dec_eq_l = |l: Expr, r: Expr| Expr::app(dec.clone(), eq_l(l, r));
        let mk_true = |prop: Expr, pf: Expr| Expr::apps(is_true.clone(), [prop, pf]);
        let mk_false = |prop: Expr, neg: Expr| Expr::apps(is_false.clone(), [prop, neg]);

        // v4.30 application: `@List.noConfusion.{0,0} False Char lhs Char rhs
        // (Eq.refl (Type 0) Char) (heq_of_eq h)` — for DISTINCT constructors
        // this term IS `False` (noConfusionType δι-reduces to `False`); for
        // the cons/cons diagonal it has type `(hd ≍ hd' → tl ≍ tl' → False) →
        // False`. Design §5/N2.
        let noconf_distinct = |lhs: Expr, rhs: Expr, h: Expr| {
            let major = Expr::apps(
                heq_of_eq_lc.clone(),
                [list_char.clone(), lhs.clone(), rhs.clone(), h],
            );
            Expr::apps(
                list_no_conf.clone(),
                [
                    false_c.clone(),
                    char_c.clone(),
                    lhs,
                    char_c.clone(),
                    rhs,
                    char_param_refl.clone(),
                    major,
                ],
            )
        };

        // ----- Type: (xs ys : List Char) → Decidable (Eq xs ys) -----
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_char.clone());
            let (ys_id, ys) = b.fresh_local(list_char.clone());
            let concl = dec_eq_l(xs.clone(), ys.clone());
            let e = b.mk_pi(ys_id, BinderInfo::Default, list_char.clone(), concl);
            let e = b.mk_pi(xs_id, BinderInfo::Default, list_char.clone(), e);
            b.finish(e)
        };

        // ----- outer motive C: fun (_xs : List Char) =>
        //         (ys : List Char) → Decidable (Eq _xs ys)
        let outer_c = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_char.clone());
            let inner = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ys_id, ys) = c.fresh_local(list_char.clone());
                let body = dec_eq_l(xs.clone(), ys);
                c.finish_child(c.mk_pi(ys_id, BinderInfo::Default, list_char.clone(), body))
            };
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_char.clone(), inner))
        };

        // ----- nilCase : C nil = fun (ys : List Char) =>
        //         @List.rec.{1,0} Char nInnerC nNil nCons ys
        let nil_case = {
            let mut b = EnvDeclBuilder::new();
            let (ys_id, ys) = b.fresh_local(list_char.clone());

            // nInnerC : fun (_ys : List Char) => Decidable (Eq nil _ys)
            let n_inner_c = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (yc_id, yc) = c.fresh_local(list_char.clone());
                let body = dec_eq_l(nil.clone(), yc);
                c.finish_child(c.mk_lam(yc_id, BinderInfo::Default, list_char.clone(), body))
            };
            // nNil : Decidable (Eq nil nil) = isTrue (Eq.refl nil)
            let n_nil = mk_true(
                eq_l(nil.clone(), nil.clone()),
                Expr::apps(eq_refl_lc.clone(), [list_char.clone(), nil.clone()]),
            );
            // nCons : fun (hd' : Char)(tl' : List Char)(_ih : Decidable (Eq nil tl')) =>
            //   isFalse (fun (h : Eq nil (cons hd' tl')) => List.noConfusion h)
            let n_cons = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hdp_id, hdp) = c.fresh_local(char_c.clone());
                let (tlp_id, tlp) = c.fresh_local(list_char.clone());
                let (ih_id, _ih) = c.fresh_local(dec_eq_l(nil.clone(), tlp.clone()));
                let cons_p = cons(hdp.clone(), tlp.clone());
                let prop = eq_l(nil.clone(), cons_p.clone());
                let neg = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (h_id, h) = d.fresh_local(prop.clone());
                    let body = noconf_distinct(nil.clone(), cons_p.clone(), h);
                    d.finish_child(d.mk_lam(h_id, BinderInfo::Default, prop.clone(), body))
                };
                let body = mk_false(prop, neg);
                let e = c.mk_lam(
                    ih_id,
                    BinderInfo::Default,
                    dec_eq_l(nil.clone(), tlp.clone()),
                    body,
                );
                let e = c.mk_lam(tlp_id, BinderInfo::Default, list_char.clone(), e);
                c.finish_child(c.mk_lam(hdp_id, BinderInfo::Default, char_c.clone(), e))
            };
            let rec_body = Expr::apps(
                list_rec.clone(),
                [char_c.clone(), n_inner_c, n_nil, n_cons, ys],
            );
            b.finish(b.mk_lam(ys_id, BinderInfo::Default, list_char.clone(), rec_body))
        };

        // ----- consCase : fun (hd : Char)(tl : List Char)(ih : C tl)(ys : List Char) =>
        //         @List.rec.{1,0} Char cInnerC cNil cCons ys
        let cons_case = {
            let mut b = EnvDeclBuilder::new();
            let (hd_id, hd) = b.fresh_local(char_c.clone());
            let (tl_id, tl) = b.fresh_local(list_char.clone());
            // ih : (ys : List Char) → Decidable (Eq tl ys)
            let ih_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ys_id, ys) = c.fresh_local(list_char.clone());
                let body = dec_eq_l(tl.clone(), ys);
                c.finish_child(c.mk_pi(ys_id, BinderInfo::Default, list_char.clone(), body))
            };
            let (ih_id, ih) = b.fresh_local(ih_ty.clone());
            let (ys_id, ys) = b.fresh_local(list_char.clone());

            let cons_xs = cons(hd.clone(), tl.clone());

            // cInnerC : fun (_ys : List Char) => Decidable (Eq (cons hd tl) _ys)
            let c_inner_c = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (yc_id, yc) = c.fresh_local(list_char.clone());
                let body = dec_eq_l(cons_xs.clone(), yc);
                c.finish_child(c.mk_lam(yc_id, BinderInfo::Default, list_char.clone(), body))
            };
            // cNil : Decidable (Eq (cons hd tl) nil) = isFalse (fun h => List.noConfusion h)
            let c_nil = {
                let prop = eq_l(cons_xs.clone(), nil.clone());
                let neg = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(prop.clone());
                    let body = noconf_distinct(cons_xs.clone(), nil.clone(), h);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, prop.clone(), body))
                };
                mk_false(prop, neg)
            };
            // cCons : fun (hd' : Char)(tl' : List Char)(_ih2 : Decidable (Eq (cons hd tl) tl')) =>
            //   @Decidable.rec.{1} (Eq Char hd hd') hdMotive hdFalse hdTrue (Char.decEq hd hd')
            let c_cons = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hdp_id, hdp) = c.fresh_local(char_c.clone());
                let (tlp_id, tlp) = c.fresh_local(list_char.clone());
                let (ih2_id, _ih2) = c.fresh_local(dec_eq_l(cons_xs.clone(), tlp.clone()));

                let cons_ys = cons(hdp.clone(), tlp.clone());
                let goal = eq_l(cons_xs.clone(), cons_ys.clone()); // Eq (cons hd tl)(cons hd' tl')
                let p_head = eq_c(hd.clone(), hdp.clone()); // Eq Char hd hd'

                // hdMotive : fun (_ : Decidable (Eq Char hd hd')) =>
                //   Decidable (Eq (cons hd tl)(cons hd' tl'))
                let hd_motive = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (ds_id, _ds) = d.fresh_local(Expr::app(dec.clone(), p_head.clone()));
                    d.finish_child(d.mk_lam(
                        ds_id,
                        BinderInfo::Default,
                        Expr::app(dec.clone(), p_head.clone()),
                        Expr::app(dec.clone(), goal.clone()),
                    ))
                };

                // hdFalse : fun (hne_h : Eq Char hd hd' → False) =>
                //   isFalse (fun (h : goal) =>
                //     noConf (cons hd tl)(cons hd' tl') h
                //       (fun (he : hd ≍ hd')(ht : tl ≍ tl') => hne_h (eq_of_heq he)))
                let hd_false = {
                    let not_p = Expr::pi(BinderInfo::Default, p_head.clone(), false_c.clone());
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hne_id, hne) = d.fresh_local(not_p.clone());
                    let neg = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (h_id, h) = e.fresh_local(goal.clone());
                        // continuation:
                        //   fun (he : hd ≍ hd')(ht : tl ≍ tl') => hne_h (eq_of_heq he)
                        let cont = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let he_ty = heq_c(hd.clone(), hdp.clone());
                            let (he_id, he) = g.fresh_local(he_ty.clone());
                            let ht_ty = heq_l(tl.clone(), tlp.clone());
                            let (ht_id, _ht) = g.fresh_local(ht_ty.clone());
                            let body =
                                Expr::app(hne.clone(), eq_of_heq_c(hd.clone(), hdp.clone(), he));
                            let body = g.mk_lam(ht_id, BinderInfo::Default, ht_ty, body);
                            g.finish_child(g.mk_lam(he_id, BinderInfo::Default, he_ty, body))
                        };
                        // noConf … h : (hd ≍ hd' → tl ≍ tl' → False) → False
                        let nc = noconf_distinct(cons_xs.clone(), cons_ys.clone(), h);
                        let body = Expr::app(nc, cont);
                        e.finish_child(e.mk_lam(h_id, BinderInfo::Default, goal.clone(), body))
                    };
                    let body = mk_false(goal.clone(), neg);
                    d.finish_child(d.mk_lam(hne_id, BinderInfo::Default, not_p, body))
                };

                // hdTrue : fun (heq_h : Eq Char hd hd') =>
                //   @Decidable.rec.{1} (Eq tl tl') tlMotive tlFalse tlTrue (ih tl')
                let hd_true = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (heqh_id, heqh) = d.fresh_local(p_head.clone());

                    let p_tail = eq_l(tl.clone(), tlp.clone()); // Eq (List Char) tl tl'

                    // tlMotive : fun (_ : Decidable (Eq tl tl')) => Decidable goal
                    let tl_motive = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (ds_id, _ds) = e.fresh_local(Expr::app(dec.clone(), p_tail.clone()));
                        e.finish_child(e.mk_lam(
                            ds_id,
                            BinderInfo::Default,
                            Expr::app(dec.clone(), p_tail.clone()),
                            Expr::app(dec.clone(), goal.clone()),
                        ))
                    };

                    // tlFalse : fun (hne_t : Eq tl tl' → False) =>
                    //   isFalse (fun (h : goal) =>
                    //     noConf … h (fun he ht => hne_t (eq_of_heq ht)))
                    let tl_false = {
                        let not_p = Expr::pi(BinderInfo::Default, p_tail.clone(), false_c.clone());
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (hnet_id, hnet) = e.fresh_local(not_p.clone());
                        let neg = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (h_id, h) = g.fresh_local(goal.clone());
                            let cont = {
                                let mut k = EnvDeclBuilder::child_of(&g);
                                let he_ty = heq_c(hd.clone(), hdp.clone());
                                let (he_id, _he) = k.fresh_local(he_ty.clone());
                                let ht_ty = heq_l(tl.clone(), tlp.clone());
                                let (ht_id, ht) = k.fresh_local(ht_ty.clone());
                                let body = Expr::app(
                                    hnet.clone(),
                                    eq_of_heq_l(tl.clone(), tlp.clone(), ht),
                                );
                                let body = k.mk_lam(ht_id, BinderInfo::Default, ht_ty, body);
                                k.finish_child(k.mk_lam(he_id, BinderInfo::Default, he_ty, body))
                            };
                            let nc = noconf_distinct(cons_xs.clone(), cons_ys.clone(), h);
                            let body = Expr::app(nc, cont);
                            g.finish_child(g.mk_lam(h_id, BinderInfo::Default, goal.clone(), body))
                        };
                        let body = mk_false(goal.clone(), neg);
                        e.finish_child(e.mk_lam(hnet_id, BinderInfo::Default, not_p, body))
                    };

                    // tlTrue : fun (heq_t : Eq tl tl') => isTrue (consEqLift)
                    // consEqLift : Eq (cons hd tl)(cons hd' tl') via two congrArg + trans.
                    let tl_true = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (heqt_id, heqt) = e.fresh_local(p_tail.clone());

                        // step1 = @congrArg Char (List Char) hd hd' (fun c => cons c tl) heq_h
                        //   : Eq (cons hd tl) (cons hd' tl)
                        let f_head = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (cc_id, cc) = g.fresh_local(char_c.clone());
                            let body = cons(cc, tl.clone());
                            g.finish_child(g.mk_lam(
                                cc_id,
                                BinderInfo::Default,
                                char_c.clone(),
                                body,
                            ))
                        };
                        let step1 = Expr::apps(
                            congr_arg.clone(),
                            [
                                char_c.clone(),
                                list_char.clone(),
                                hd.clone(),
                                hdp.clone(),
                                f_head,
                                heqh.clone(),
                            ],
                        );
                        // step2 = @congrArg (List Char)(List Char) tl tl' (fun t => cons hd' t) heq_t
                        //   : Eq (cons hd' tl)(cons hd' tl')
                        let f_tail = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (tt_id, tt) = g.fresh_local(list_char.clone());
                            let body = cons(hdp.clone(), tt);
                            g.finish_child(g.mk_lam(
                                tt_id,
                                BinderInfo::Default,
                                list_char.clone(),
                                body,
                            ))
                        };
                        let step2 = Expr::apps(
                            congr_arg.clone(),
                            [
                                list_char.clone(),
                                list_char.clone(),
                                tl.clone(),
                                tlp.clone(),
                                f_tail,
                                heqt,
                            ],
                        );
                        // consEqLift = @Eq.trans (List Char)
                        //   (cons hd tl)(cons hd' tl)(cons hd' tl') step1 step2
                        let cons_mid = cons(hdp.clone(), tl.clone());
                        let cons_eq_lift = Expr::apps(
                            eq_trans_lc.clone(),
                            [
                                list_char.clone(),
                                cons_xs.clone(),
                                cons_mid,
                                cons_ys.clone(),
                                step1,
                                step2,
                            ],
                        );
                        let body = mk_true(goal.clone(), cons_eq_lift);
                        e.finish_child(e.mk_lam(heqt_id, BinderInfo::Default, p_tail.clone(), body))
                    };

                    let discriminant = Expr::app(ih.clone(), tlp.clone());
                    let rec_app = Expr::apps(
                        dec_rec.clone(),
                        [p_tail.clone(), tl_motive, tl_false, tl_true, discriminant],
                    );
                    d.finish_child(d.mk_lam(heqh_id, BinderInfo::Default, p_head.clone(), rec_app))
                };

                let discriminant = Expr::apps(char_dec_eq.clone(), [hd.clone(), hdp.clone()]);
                let rec_app = Expr::apps(
                    dec_rec.clone(),
                    [p_head, hd_motive, hd_false, hd_true, discriminant],
                );
                let e = c.mk_lam(
                    ih2_id,
                    BinderInfo::Default,
                    dec_eq_l(cons_xs.clone(), tlp.clone()),
                    rec_app,
                );
                let e = c.mk_lam(tlp_id, BinderInfo::Default, list_char.clone(), e);
                c.finish_child(c.mk_lam(hdp_id, BinderInfo::Default, char_c.clone(), e))
            };

            let rec_body = Expr::apps(
                list_rec.clone(),
                [char_c.clone(), c_inner_c, c_nil, c_cons, ys],
            );
            let e = b.mk_lam(ys_id, BinderInfo::Default, list_char.clone(), rec_body);
            let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, e);
            let e = b.mk_lam(tl_id, BinderInfo::Default, list_char.clone(), e);
            b.finish(b.mk_lam(hd_id, BinderInfo::Default, char_c.clone(), e))
        };

        // ----- value: fun (xs ys : List Char) =>
        //         (@List.rec.{1,0} Char outer_c nilCase consCase xs) ys -----
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_char.clone());
            let (ys_id, ys) = b.fresh_local(list_char.clone());
            let rec_xs = Expr::apps(
                list_rec.clone(),
                [
                    char_c.clone(),
                    outer_c.clone(),
                    nil_case.clone(),
                    cons_case.clone(),
                    xs,
                ],
            );
            let body = Expr::app(rec_xs, ys);
            let e = b.mk_lam(ys_id, BinderInfo::Default, list_char.clone(), body);
            let e = b.mk_lam(xs_id, BinderInfo::Default, list_char.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    /// The kernel accepts the `ListChar.decEq` decision-procedure term and
    /// registers it as a `Definition` (not an `Axiom`), idempotently.
    #[test]
    fn test_list_char_dec_eq_registered_and_type_checks() {
        let mut env = Environment::with_prelude();
        env.register_list_char_dec_eq_proof()
            .expect("first registration");
        env.register_list_char_dec_eq_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("ListChar.decEq"))
            .expect("ListChar.decEq should be registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        assert!(info.value.is_some(), "Definition must retain its value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("ListChar.decEq"), vec![]))
            .expect("ListChar.decEq should type-check");
    }

    /// Axiom closure is empty — every branch is a real constructive term
    /// (`List.rec`, `List.noConfusion`, `Char.decEq`, `congrArg`, `Eq.trans`);
    /// NO `sorry`, NO declared axiom.
    #[test]
    fn test_list_char_dec_eq_axiom_closure_empty() {
        let mut env = Environment::with_prelude();
        env.register_list_char_dec_eq_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("ListChar.decEq"))
            .expect("ListChar.decEq is registered");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            names.is_empty(),
            "ListChar.decEq must have empty axiom closure, got {names:?}"
        );
    }

    /// The body genuinely dispatches via `Decidable.rec`, `List.rec`,
    /// `Char.decEq`, `List.noConfusion`, and lifts via `congrArg` — guards
    /// against a degenerate / `sorry`-laden masquerade.
    #[test]
    fn test_list_char_dec_eq_uses_real_dispatch() {
        let mut env = Environment::with_prelude();
        env.register_list_char_dec_eq_proof().unwrap();
        let info = env.get_const(&Name::from_string("ListChar.decEq")).unwrap();
        let value = info.value.as_ref().expect("Definition has value");

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

        assert!(
            mentions(value, "Decidable.rec"),
            "must dispatch via Decidable.rec"
        );
        assert!(mentions(value, "List.rec"), "must recurse via List.rec");
        assert!(
            mentions(value, "Char.decEq"),
            "must dispatch via Char.decEq"
        );
        assert!(
            mentions(value, "List.noConfusion"),
            "must use List.noConfusion"
        );
        assert!(mentions(value, "congrArg"), "must lift via congrArg");
        assert!(!mentions(value, "sorryAx"), "must not contain sorryAx");
    }
}
