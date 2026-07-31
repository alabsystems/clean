// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive lemmas bridging `Nat.ble` (boolean `≤`) to `Nat.le` (the
//! inductive `≤` Prop) — real kernel terms, NO `sorry`, NO axiom. These let the
//! `Decidable (Nat.le a b)` / `Nat.lt` native reducers emit sound `isTrue` /
//! `isFalse` witnesses instead of `sorryAx`.
//!
//! Semantics used (`Nat.ble`, order_nat_cmp.rs): `ble 0 _ ≡ true`,
//! `ble (succ m) 0 ≡ false`, `ble (succ m) (succ n) ≡ ble m n`.
//!
//! - `Nat.ble_refl a : ble a a = true` — `Nat.rec` on `a`.
//! - `Nat.ble_succ_right_eq_true a m : ble a m = true → ble a (succ m) = true` —
//!   nested `Nat.rec` (on `a`, then `m`), `Bool.noConfusion` for the impossible
//!   `ble (succ a) 0 = true`.
//! - `Nat.ble_eq_true_of_le a b : Nat.le a b → ble a b = true` — `Nat.le.rec`
//!   (refl ↦ `ble_refl`, step ↦ `ble_succ_right_eq_true`).
//! - `Nat.not_le_of_ble_eq_false a b : ble a b = false → Nat.le a b → False` —
//!   `ble_eq_true_of_le` + `Bool.noConfusion` (no recursion).
//! - `Nat.le_of_ble_eq_true a b : ble a b = true → Nat.le a b` — nested
//!   `Nat.rec` (on `b`, then `a`), `Nat.zero_le` / `Nat.succ_le_succ` /
//!   `Nat.le.refl`, `Bool.noConfusion` for impossible cases.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register the `Nat.ble`↔`Nat.le` bridge lemmas (idempotent, axiom-free).
    pub(crate) fn register_nat_ble_le_lemmas(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate — the whole
        // bridge family is stated over the import-gated `Nat.ble` seed (see
        // order_nat_cmp.rs::init_nat_cmp); the genuine olean lemmas import
        // through the checked path instead. Default lane byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_true_false()?;
        self.init_nat_cmp()?; // Nat.ble
        self.init_le()?; // Nat.le + Nat.le.rec + Nat.le.refl/step
        self.init_lt()?; // Nat.lt
        self.init_nat_top_level_ordering().ok(); // Nat.succ_le_succ etc. (lemma 5)
        if self
            .get_const(&Name::from_string("Bool.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        let zero_lvl = Level::zero();
        let one = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let succ_c = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let ble_c = Expr::const_(Name::from_string("Nat.ble"), vec![]);
        let le_c = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let eq_b = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl_b = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![zero_lvl.clone()]);
        let no_conf = Expr::const_(
            Name::from_string("Bool.noConfusion"),
            vec![zero_lvl.clone()],
        );

        let succ = |x: Expr| Expr::app(succ_c.clone(), x);
        let ble = |x: Expr, y: Expr| Expr::apps(ble_c.clone(), [x, y]);
        let le = |x: Expr, y: Expr| Expr::apps(le_c.clone(), [x, y]);
        let eqbt = |x: Expr| Expr::apps(eq_b.clone(), [bool_c.clone(), x, btrue.clone()]);
        // `@Bool.noConfusion.{0} P false true h : P`  (h : false = true, ex falso)
        let exfalso =
            |p: Expr, h: Expr| Expr::apps(no_conf.clone(), [p, bfalse.clone(), btrue.clone(), h]);

        // ───────────── 1. Nat.ble_refl : ∀ a, ble a a = true ─────────────
        if self.get_const(&Name::from_string("Nat.ble_refl")).is_none() {
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat.clone());
                b.finish(b.mk_pi(
                    a_id,
                    BinderInfo::Default,
                    nat.clone(),
                    eqbt(ble(a.clone(), a)),
                ))
            };
            let motive = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat.clone());
                b.finish(b.mk_lam(
                    a_id,
                    BinderInfo::Default,
                    nat.clone(),
                    eqbt(ble(a.clone(), a)),
                ))
            };
            let zcase = Expr::apps(eq_refl_b.clone(), [bool_c.clone(), btrue.clone()]);
            let scase = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat.clone());
                let ih_ty = eqbt(ble(a.clone(), a.clone()));
                let (ih_id, ih) = b.fresh_local(ih_ty.clone());
                let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, ih);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e))
            };
            let value = Expr::apps(nat_rec0.clone(), [motive, zcase, scase]);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.ble_refl"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── 2. Nat.ble_succ_right_eq_true : ∀ a m, ble a m = true → ble a (succ m) = true ──
        if self
            .get_const(&Name::from_string("Nat.ble_succ_right_eq_true"))
            .is_none()
        {
            // C a := ∀ m, ble a m = true → ble a (succ m) = true
            let c_motive_pi = |a: &Expr, bld: &EnvDeclBuilder| {
                let mut c = EnvDeclBuilder::child_of(bld);
                let (m_id, m) = c.fresh_local(nat.clone());
                let hyp = eqbt(ble(a.clone(), m.clone()));
                let concl = eqbt(ble(a.clone(), succ(m.clone())));
                let (h_id, _h) = c.fresh_local(hyp.clone());
                let inner = c.mk_pi(h_id, BinderInfo::Default, hyp, concl);
                c.finish_child(c.mk_pi(m_id, BinderInfo::Default, nat.clone(), inner))
            };
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat.clone());
                let body = c_motive_pi(&a, &b);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, nat.clone(), body))
            };
            let motive = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat.clone());
                let body = c_motive_pi(&a, &b);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, nat.clone(), body))
            };
            // base : C 0 = ∀ m, ble 0 m = true → ble 0 (succ m) = true := fun m _h => Eq.refl true
            let base = {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(nat.clone());
                let hyp = eqbt(ble(zero.clone(), m.clone()));
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let body = Expr::apps(eq_refl_b.clone(), [bool_c.clone(), btrue.clone()]);
                let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
                b.finish(b.mk_lam(m_id, BinderInfo::Default, nat.clone(), e))
            };
            // step : fun a' (ih : C a') => fun m => Nat.rec D mbase mstep m
            let step = {
                let mut b = EnvDeclBuilder::new();
                let (ap_id, ap) = b.fresh_local(nat.clone());
                let c_ap = c_motive_pi(&ap, &b);
                let (ih_id, ih) = b.fresh_local(c_ap.clone());
                // D : fun m => ble (succ a') m = true → ble (succ a') (succ m) = true
                let d_motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (m_id, m) = c.fresh_local(nat.clone());
                    let hyp = eqbt(ble(succ(ap.clone()), m.clone()));
                    let concl = eqbt(ble(succ(ap.clone()), succ(m.clone())));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    let inner = c.mk_pi(h_id, BinderInfo::Default, hyp, concl);
                    c.finish_child(c.mk_lam(m_id, BinderInfo::Default, nat.clone(), inner))
                };
                // mbase : D 0 = ble (succ a') 0 = true → ble (succ a')(succ 0) = true
                //   := fun (h : ...) => exfalso goal h
                let mbase = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hyp = eqbt(ble(succ(ap.clone()), zero.clone()));
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let goal = eqbt(ble(succ(ap.clone()), succ(zero.clone())));
                    let body = exfalso(goal, h);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, body))
                };
                // mstep : fun m' (_ihm : D m') => ih m'
                let mstep = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (mp_id, mp) = c.fresh_local(nat.clone());
                    // D m' (for the unused inner IH binder)
                    let d_mp = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let hyp = eqbt(ble(succ(ap.clone()), mp.clone()));
                        let concl = eqbt(ble(succ(ap.clone()), succ(mp.clone())));
                        let (h_id, _h) = d.fresh_local(hyp.clone());
                        d.finish_child(d.mk_pi(h_id, BinderInfo::Default, hyp, concl))
                    };
                    let (ihm_id, _ihm) = c.fresh_local(d_mp.clone());
                    let body = Expr::app(ih.clone(), mp.clone());
                    let e = c.mk_lam(ihm_id, BinderInfo::Default, d_mp, body);
                    c.finish_child(c.mk_lam(mp_id, BinderInfo::Default, nat.clone(), e))
                };
                let inner_rec = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (m_id, m) = c.fresh_local(nat.clone());
                    let body = Expr::apps(nat_rec0.clone(), [d_motive, mbase, mstep, m]);
                    c.finish_child(c.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
                };
                let e = b.mk_lam(ih_id, BinderInfo::Default, c_ap, inner_rec);
                b.finish(b.mk_lam(ap_id, BinderInfo::Default, nat.clone(), e))
            };
            let value = Expr::apps(nat_rec0.clone(), [motive, base, step]);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.ble_succ_right_eq_true"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── 3. Nat.ble_eq_true_of_le : ∀ a b, Nat.le a b → ble a b = true ──
        if self
            .get_const(&Name::from_string("Nat.ble_eq_true_of_le"))
            .is_none()
        {
            let le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);
            let ble_refl = Expr::const_(Name::from_string("Nat.ble_refl"), vec![]);
            let ble_sr = Expr::const_(Name::from_string("Nat.ble_succ_right_eq_true"), vec![]);

            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bv_id, bv) = b.fresh_local(nat.clone());
            let h_ty = le(a.clone(), bv.clone());
            let (h_id, h) = b.fresh_local(h_ty.clone());

            // motive : fun (t : Nat) (_ : Nat.le a t) => ble a t = true
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = c.fresh_local(nat.clone());
                let le_at = le(a.clone(), t.clone());
                let (ht_id, _ht) = c.fresh_local(le_at.clone());
                let body = eqbt(ble(a.clone(), t.clone()));
                let lam_h = c.mk_lam(ht_id, BinderInfo::Default, le_at, body);
                c.finish_child(c.mk_lam(t_id, BinderInfo::Default, nat.clone(), lam_h))
            };
            // refl minor : ble a a = true := Nat.ble_refl a
            let minor_refl = Expr::app(ble_refl, a.clone());
            // step minor : fun {t} (_ht : Nat.le a t) (ih : ble a t = true) => ble_succ_right a t ih
            let minor_step = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = c.fresh_local(nat.clone());
                let le_at = le(a.clone(), t.clone());
                let (ht_id, _ht) = c.fresh_local(le_at.clone());
                let ih_ty = eqbt(ble(a.clone(), t.clone()));
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let body = Expr::apps(ble_sr.clone(), [a.clone(), t.clone(), ih]);
                let l = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let l = c.mk_lam(ht_id, BinderInfo::Default, le_at, l);
                c.finish_child(c.mk_lam(t_id, BinderInfo::Implicit, nat.clone(), l))
            };
            let rec_app = Expr::apps(
                le_rec,
                [
                    a.clone(),
                    motive,
                    minor_refl,
                    minor_step,
                    bv.clone(),
                    h.clone(),
                ],
            );
            let value = {
                let e = b.mk_lam(h_id, BinderInfo::Default, h_ty.clone(), rec_app);
                let e = b.mk_lam(bv_id, BinderInfo::Default, nat.clone(), e);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e))
            };
            let type_ = {
                let e = b.mk_pi(
                    h_id,
                    BinderInfo::Default,
                    h_ty,
                    eqbt(ble(a.clone(), bv.clone())),
                );
                let e = b.mk_pi(bv_id, BinderInfo::Default, nat.clone(), e);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.ble_eq_true_of_le"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── 4. Nat.not_le_of_ble_eq_false : ∀ a b, ble a b = false → Nat.le a b → False ──
        if self
            .get_const(&Name::from_string("Nat.not_le_of_ble_eq_false"))
            .is_none()
        {
            let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]);
            let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![one.clone()]);
            let ble_eq_true_of_le =
                Expr::const_(Name::from_string("Nat.ble_eq_true_of_le"), vec![]);
            let eqbf = |x: Expr| Expr::apps(eq_b.clone(), [bool_c.clone(), x, bfalse.clone()]);

            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let (bv_id, bv) = b.fresh_local(nat.clone());
            let hf_ty = eqbf(ble(a.clone(), bv.clone()));
            let (hf_id, hf) = b.fresh_local(hf_ty.clone());
            let hle_ty = le(a.clone(), bv.clone());
            let (hle_id, hle) = b.fresh_local(hle_ty.clone());

            // symm hf : false = ble a b
            let symm = Expr::apps(
                eq_symm,
                [
                    bool_c.clone(),
                    ble(a.clone(), bv.clone()),
                    bfalse.clone(),
                    hf.clone(),
                ],
            );
            // ble_eq_true_of_le a b hle : ble a b = true
            let bet = Expr::apps(ble_eq_true_of_le, [a.clone(), bv.clone(), hle.clone()]);
            // trans : false = true
            let trans = Expr::apps(
                eq_trans,
                [
                    bool_c.clone(),
                    bfalse.clone(),
                    ble(a.clone(), bv.clone()),
                    btrue.clone(),
                    symm,
                    bet,
                ],
            );
            let body = exfalso(false_c.clone(), trans);
            let value = {
                let e = b.mk_lam(hle_id, BinderInfo::Default, hle_ty.clone(), body);
                let e = b.mk_lam(hf_id, BinderInfo::Default, hf_ty.clone(), e);
                let e = b.mk_lam(bv_id, BinderInfo::Default, nat.clone(), e);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e))
            };
            let type_ = {
                let e = b.mk_pi(hle_id, BinderInfo::Default, hle_ty, false_c.clone());
                let e = b.mk_pi(hf_id, BinderInfo::Default, hf_ty, e);
                let e = b.mk_pi(bv_id, BinderInfo::Default, nat.clone(), e);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.not_le_of_ble_eq_false"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── Nat.zero_le : ∀ n, Nat.le 0 n (build if the prelude lacks it) ──
        if self.get_const(&Name::from_string("Nat.zero_le")).is_none() {
            let le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
            let le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat.clone());
                b.finish(b.mk_pi(n_id, BinderInfo::Default, nat.clone(), le(zero.clone(), n)))
            };
            let motive = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat.clone());
                b.finish(b.mk_lam(n_id, BinderInfo::Default, nat.clone(), le(zero.clone(), n)))
            };
            let zcase = Expr::app(le_refl.clone(), zero.clone());
            let scase = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat.clone());
                let ih_ty = le(zero.clone(), n.clone());
                let (ih_id, ih) = b.fresh_local(ih_ty.clone());
                let body = Expr::apps(le_step.clone(), [zero.clone(), n.clone(), ih]);
                let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                b.finish(b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e))
            };
            let value = Expr::apps(nat_rec0.clone(), [motive, zcase, scase]);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.zero_le"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── 5. Nat.le_of_ble_eq_true : ∀ a b, ble a b = true → Nat.le a b ──
        if self
            .get_const(&Name::from_string("Nat.le_of_ble_eq_true"))
            .is_none()
        {
            let le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
            let zero_le = Expr::const_(Name::from_string("Nat.zero_le"), vec![]);
            let succ_le_succ = Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]);

            // C b := ∀ a, ble a b = true → Nat.le a b
            let c_pi = |bexpr: &Expr, bld: &EnvDeclBuilder| {
                let mut c = EnvDeclBuilder::child_of(bld);
                let (a_id, a) = c.fresh_local(nat.clone());
                let hyp = eqbt(ble(a.clone(), bexpr.clone()));
                let (h_id, _h) = c.fresh_local(hyp.clone());
                let inner = c.mk_pi(h_id, BinderInfo::Default, hyp, le(a.clone(), bexpr.clone()));
                c.finish_child(c.mk_pi(a_id, BinderInfo::Default, nat.clone(), inner))
            };
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat.clone());
                let (bv_id, bv) = b.fresh_local(nat.clone());
                let hyp = eqbt(ble(a.clone(), bv.clone()));
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hyp, le(a.clone(), bv.clone()));
                let e = b.mk_pi(bv_id, BinderInfo::Default, nat.clone(), e);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e))
            };
            let motive = {
                let mut b = EnvDeclBuilder::new();
                let (bv_id, bv) = b.fresh_local(nat.clone());
                let body = c_pi(&bv, &b);
                b.finish(b.mk_lam(bv_id, BinderInfo::Default, nat.clone(), body))
            };
            // base : C 0 = ∀ a, ble a 0 = true → Nat.le a 0  (Nat.rec on a)
            let base = {
                let b = EnvDeclBuilder::new();
                // E a := ble a 0 = true → Nat.le a 0
                let e_pi = |aexpr: &Expr, bld: &EnvDeclBuilder| {
                    let mut c = EnvDeclBuilder::child_of(bld);
                    let hyp = eqbt(ble(aexpr.clone(), zero.clone()));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    c.finish_child(c.mk_pi(
                        h_id,
                        BinderInfo::Default,
                        hyp,
                        le(aexpr.clone(), zero.clone()),
                    ))
                };
                let e_motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, a) = c.fresh_local(nat.clone());
                    let body = e_pi(&a, &c);
                    c.finish_child(c.mk_lam(a_id, BinderInfo::Default, nat.clone(), body))
                };
                // ebase : E 0 = ble 0 0 = true → Nat.le 0 0 := fun _h => Nat.le.refl 0
                let ebase = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hyp = eqbt(ble(zero.clone(), zero.clone()));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    let body = Expr::app(le_refl.clone(), zero.clone());
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, body))
                };
                // estep : fun a' _iha => fun (h : ble (succ a') 0 = true) => exfalso (le (succ a') 0) h
                let estep = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ap_id, ap) = c.fresh_local(nat.clone());
                    let e_ap = e_pi(&ap, &c);
                    let (iha_id, _iha) = c.fresh_local(e_ap.clone());
                    let hyp = eqbt(ble(succ(ap.clone()), zero.clone()));
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let body = exfalso(le(succ(ap.clone()), zero.clone()), h);
                    let l = c.mk_lam(h_id, BinderInfo::Default, hyp, body);
                    let l = c.mk_lam(iha_id, BinderInfo::Default, e_ap, l);
                    c.finish_child(c.mk_lam(ap_id, BinderInfo::Default, nat.clone(), l))
                };
                let body = Expr::apps(nat_rec0.clone(), [e_motive, ebase, estep]);
                b.finish(body)
            };
            // step : fun b' (ih_b : C b') => Nat.rec F fbase fstep   (∀ a, ble a (succ b') = true → le a (succ b'))
            let step = {
                let mut b = EnvDeclBuilder::new();
                let (bp_id, bp) = b.fresh_local(nat.clone());
                let c_bp = c_pi(&bp, &b);
                let (ihb_id, ihb) = b.fresh_local(c_bp.clone());
                // F a := ble a (succ b') = true → Nat.le a (succ b')
                let f_pi = |aexpr: &Expr, bld: &EnvDeclBuilder, bp: &Expr| {
                    let mut c = EnvDeclBuilder::child_of(bld);
                    let hyp = eqbt(ble(aexpr.clone(), succ(bp.clone())));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    c.finish_child(c.mk_pi(
                        h_id,
                        BinderInfo::Default,
                        hyp,
                        le(aexpr.clone(), succ(bp.clone())),
                    ))
                };
                let f_motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, a) = c.fresh_local(nat.clone());
                    let body = f_pi(&a, &c, &bp);
                    c.finish_child(c.mk_lam(a_id, BinderInfo::Default, nat.clone(), body))
                };
                // fbase : F 0 = ble 0 (succ b') = true → Nat.le 0 (succ b') := fun _h => Nat.zero_le (succ b')
                let fbase = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hyp = eqbt(ble(zero.clone(), succ(bp.clone())));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    let body = Expr::app(zero_le.clone(), succ(bp.clone()));
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, body))
                };
                // fstep : fun a' _ifa => fun (h : ble (succ a')(succ b') = true) =>
                //           Nat.succ_le_succ a' b' (ih_b a' h)
                let fstep = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ap_id, ap) = c.fresh_local(nat.clone());
                    let f_ap = f_pi(&ap, &c, &bp);
                    let (ifa_id, _ifa) = c.fresh_local(f_ap.clone());
                    let hyp = eqbt(ble(succ(ap.clone()), succ(bp.clone())));
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let inner = Expr::app(Expr::app(ihb.clone(), ap.clone()), h);
                    let body = Expr::apps(succ_le_succ.clone(), [ap.clone(), bp.clone(), inner]);
                    let l = c.mk_lam(h_id, BinderInfo::Default, hyp, body);
                    let l = c.mk_lam(ifa_id, BinderInfo::Default, f_ap, l);
                    c.finish_child(c.mk_lam(ap_id, BinderInfo::Default, nat.clone(), l))
                };
                let rec_body = Expr::apps(nat_rec0.clone(), [f_motive, fbase, fstep]);
                let e = b.mk_lam(ihb_id, BinderInfo::Default, c_bp, rec_body);
                b.finish(b.mk_lam(bp_id, BinderInfo::Default, nat.clone(), e))
            };
            // value : λ (a b : Nat) (h : ble a b = true) => (Nat.rec C base step b) a h
            // (recurse on `b`, then apply to `a` and `h` — matches the `∀ a b, …` type).
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(nat.clone());
                let (bv_id, bv) = b.fresh_local(nat.clone());
                let hyp = eqbt(ble(a.clone(), bv.clone()));
                let (h_id, h) = b.fresh_local(hyp.clone());
                let rec_b = Expr::apps(nat_rec0.clone(), [motive, base, step, bv.clone()]);
                let body = Expr::app(Expr::app(rec_b, a.clone()), h);
                let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
                let e = b.mk_lam(bv_id, BinderInfo::Default, nat.clone(), e);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.le_of_ble_eq_true"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::TypeChecker;

    #[test]
    fn test_nat_ble_le_lemmas_type_check_and_axiom_free() {
        let mut env = Environment::new();
        env.register_nat_ble_le_lemmas().expect("register");
        env.register_nat_ble_le_lemmas().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in [
            "Nat.ble_refl",
            "Nat.ble_succ_right_eq_true",
            "Nat.ble_eq_true_of_le",
            "Nat.not_le_of_ble_eq_false",
            "Nat.le_of_ble_eq_true",
        ] {
            let n = Name::from_string(name);
            let _ = tc
                .infer_type(&Expr::const_(n.clone(), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
            let deps = env.axiom_deps(&n).expect("registered");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
        }
    }
}
