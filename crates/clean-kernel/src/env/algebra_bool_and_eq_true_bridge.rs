// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness bridges from the boolean connectives `Bool.and` / `Bool.or` to
//! their `= true` semantics — real kernel terms (NO `sorry`, NO axiom):
//!
//! - `Bool.and_eq_true_left  : ∀ a b, Bool.and a b = true → a = true`
//! - `Bool.and_eq_true_right : ∀ a b, Bool.and a b = true → b = true`
//! - `Bool.or_eq_true_elim   : ∀ a b (C : Prop),
//!        Bool.or a b = true → (a = true → C) → (b = true → C) → C`
//!
//! `Bool.and` reduces as `Bool.and false b ≡ false`, `Bool.and true b ≡ b`;
//! `Bool.or` reduces as `Bool.or false b ≡ b`, `Bool.or true b ≡ true`
//! (`data_types_nat.rs`). Each is a single `Bool.rec` on `a` (no recursion):
//!   * and-left / a=false:  hyp `false = true` IS the goal `false = true` (`λ h. h`).
//!   * and-left / a=true:   goal `true = true` (`Eq.refl true`, hyp unused).
//!   * and-right / a=false: hyp `false = true`; `Bool.noConfusion` inhabits `b = true`.
//!   * and-right / a=true:  `Bool.and true b ≡ b`, so hyp `b = true` IS the goal.
//!   * or-elim / a=false:   `Bool.or false b ≡ b`, so hyp `b = true`; apply the
//!                          right case function (`fb h`).
//!   * or-elim / a=true:    hyp `true = true`; apply the left case (`fa h`).
//!
//! These back the Trust spec-elab CONNECTIVE certified monitors (two-language
//! design §1.1): a `P && Q` monitor `Bool.and mon_P mon_Q` cites the and-bridges
//! to project the shared `= true` hypothesis onto each conjunct before
//! `And.intro`; a `P || Q` monitor `Bool.or mon_P mon_Q` cites `or_eq_true_elim`
//! to case-split the shared hypothesis and emit `Or.inl` / `Or.inr` of the
//! sub-monitors' certificates.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Bool.and_eq_true_left` / `Bool.and_eq_true_right` as
    /// kernel-checked `Declaration::Theorem` terms. Idempotent; axiom-free.
    pub(crate) fn register_bool_and_eq_true_bridges(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_bool()?;
        self.init_true_false()?; // False (De Morgan companions)
        self.init_and()?; // And + And.left/And.right (¬(P∧Q) plumbing)
        self.init_or()?; // Or + Or.rec (not_or_intro)
        if self
            .get_const(&Name::from_string("Bool.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        let one = Level::succ(Level::zero());
        let zero_lvl = Level::zero();
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let and_c = Expr::const_(Name::from_string("Bool.and"), vec![]);
        let or_c = Expr::const_(Name::from_string("Bool.or"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        // The motive is an `Eq`-implication in `Prop = Sort 0`.
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![zero_lvl.clone()]);
        let no_conf = Expr::const_(Name::from_string("Bool.noConfusion"), vec![zero_lvl]);

        let not_c = Expr::const_(Name::from_string("Bool.not"), vec![]);
        let band = |x: Expr, y: Expr| Expr::apps(and_c.clone(), [x, y]);
        let bor = |x: Expr, y: Expr| Expr::apps(or_c.clone(), [x, y]);
        let bnot = |x: Expr| Expr::app(not_c.clone(), x);
        let eqbt = |x: Expr| Expr::apps(eq_c.clone(), [bool_c.clone(), x, btrue.clone()]);
        let eqbf = |x: Expr| Expr::apps(eq_c.clone(), [bool_c.clone(), x, bfalse.clone()]);
        let refl_true = || Expr::apps(eq_refl.clone(), [bool_c.clone(), btrue.clone()]);
        let refl_false = || Expr::apps(eq_refl.clone(), [bool_c.clone(), bfalse.clone()]);
        // `@Bool.noConfusion.{0} P false true h : P`  (h : false = true, ex falso)
        let exfalso =
            |p: Expr, h: Expr| Expr::apps(no_conf.clone(), [p, bfalse.clone(), btrue.clone(), h]);
        // `@Bool.noConfusion.{0} P true false h : P`  (h : true = false, ex falso)
        let exfalso_tf =
            |p: Expr, h: Expr| Expr::apps(no_conf.clone(), [p, btrue.clone(), bfalse.clone(), h]);

        // ── Bool.and_eq_true_left : ∀ a b, Bool.and a b = true → a = true ──
        if self
            .get_const(&Name::from_string("Bool.and_eq_true_left"))
            .is_none()
        {
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_c.clone());
                let (bv_id, bv) = b.fresh_local(bool_c.clone());
                let hyp = eqbt(band(a.clone(), bv.clone()));
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hyp, eqbt(a.clone()));
                let e = b.mk_pi(bv_id, BinderInfo::Default, bool_c.clone(), e);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_c.clone());
                let (bv_id, bv) = b.fresh_local(bool_c.clone());
                // motive : fun a' => (Bool.and a' b = true) → (a' = true)
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ap_id, ap) = c.fresh_local(bool_c.clone());
                    let hyp = eqbt(band(ap.clone(), bv.clone()));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    let inner = c.mk_pi(h_id, BinderInfo::Default, hyp, eqbt(ap.clone()));
                    c.finish_child(c.mk_lam(ap_id, BinderInfo::Default, bool_c.clone(), inner))
                };
                // a=false: λ (h : Bool.and false b = true). h   (h : false = true ≡ goal)
                let false_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hyp = eqbt(band(bfalse.clone(), bv.clone()));
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, h))
                };
                // a=true: λ (h : Bool.and true b = true). Eq.refl true
                let true_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hyp = eqbt(band(btrue.clone(), bv.clone()));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, refl_true()))
                };
                let rec_a =
                    Expr::apps(bool_rec.clone(), [motive, false_case, true_case, a.clone()]);
                let e = b.mk_lam(bv_id, BinderInfo::Default, bool_c.clone(), rec_a);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Bool.and_eq_true_left"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── Bool.and_eq_true_right : ∀ a b, Bool.and a b = true → b = true ──
        if self
            .get_const(&Name::from_string("Bool.and_eq_true_right"))
            .is_none()
        {
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_c.clone());
                let (bv_id, bv) = b.fresh_local(bool_c.clone());
                let hyp = eqbt(band(a.clone(), bv.clone()));
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hyp, eqbt(bv.clone()));
                let e = b.mk_pi(bv_id, BinderInfo::Default, bool_c.clone(), e);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_c.clone());
                let (bv_id, bv) = b.fresh_local(bool_c.clone());
                // motive : fun a' => (Bool.and a' b = true) → (b = true)
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ap_id, ap) = c.fresh_local(bool_c.clone());
                    let hyp = eqbt(band(ap.clone(), bv.clone()));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    let inner = c.mk_pi(h_id, BinderInfo::Default, hyp, eqbt(bv.clone()));
                    c.finish_child(c.mk_lam(ap_id, BinderInfo::Default, bool_c.clone(), inner))
                };
                // a=false: λ (h : Bool.and false b = true). exfalso (b=true) h
                //   (h : false = true; Bool.noConfusion inhabits the goal b = true)
                let false_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hyp = eqbt(band(bfalse.clone(), bv.clone()));
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let body = exfalso(eqbt(bv.clone()), h);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, body))
                };
                // a=true: λ (h : Bool.and true b = true). h   (h : b = true ≡ goal)
                let true_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hyp = eqbt(band(btrue.clone(), bv.clone()));
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, h))
                };
                let rec_a =
                    Expr::apps(bool_rec.clone(), [motive, false_case, true_case, a.clone()]);
                let e = b.mk_lam(bv_id, BinderInfo::Default, bool_c.clone(), rec_a);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Bool.and_eq_true_right"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── Bool.or_eq_true_elim :
        //      ∀ a b (C : Prop), Bool.or a b = true → (a=true→C) → (b=true→C) → C ──
        // A self-contained eliminator: a single `Bool.rec` on `a` that, given the
        // shared `Bool.or a b = true` hypothesis and the two case functions,
        // dispatches to the right one. `Bool.or false b ≡ b` (so the hyp is
        // `b = true`, apply `fb`); `Bool.or true b ≡ true` (apply `fa`).
        if self
            .get_const(&Name::from_string("Bool.or_eq_true_elim"))
            .is_none()
        {
            let prop = Expr::prop();
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_c.clone());
                let (bv_id, bv) = b.fresh_local(bool_c.clone());
                let (c_id, cc) = b.fresh_local(prop.clone());
                let hyp = eqbt(bor(a.clone(), bv.clone()));
                let fa_arrow = Expr::arrow(eqbt(a.clone()), cc.clone());
                let fb_arrow = Expr::arrow(eqbt(bv.clone()), cc.clone());
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let (fa_id, _fa) = b.fresh_local(fa_arrow.clone());
                let (fb_id, _fb) = b.fresh_local(fb_arrow.clone());
                let e = b.mk_pi(fb_id, BinderInfo::Default, fb_arrow, cc.clone());
                let e = b.mk_pi(fa_id, BinderInfo::Default, fa_arrow, e);
                let e = b.mk_pi(h_id, BinderInfo::Default, hyp, e);
                let e = b.mk_pi(c_id, BinderInfo::Default, prop.clone(), e);
                let e = b.mk_pi(bv_id, BinderInfo::Default, bool_c.clone(), e);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_c.clone());
                let (bv_id, bv) = b.fresh_local(bool_c.clone());
                let (c_id, cc) = b.fresh_local(prop.clone());
                // motive : fun a' => (Bool.or a' b = true)→(a'=true→C)→(b=true→C)→C
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ap_id, ap) = c.fresh_local(bool_c.clone());
                    let hyp = eqbt(bor(ap.clone(), bv.clone()));
                    let fa_arrow = Expr::arrow(eqbt(ap.clone()), cc.clone());
                    let fb_arrow = Expr::arrow(eqbt(bv.clone()), cc.clone());
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    let (fa_id, _fa) = c.fresh_local(fa_arrow.clone());
                    let (fb_id, _fb) = c.fresh_local(fb_arrow.clone());
                    let e = c.mk_pi(fb_id, BinderInfo::Default, fb_arrow, cc.clone());
                    let e = c.mk_pi(fa_id, BinderInfo::Default, fa_arrow, e);
                    let e = c.mk_pi(h_id, BinderInfo::Default, hyp, e);
                    c.finish_child(c.mk_lam(ap_id, BinderInfo::Default, bool_c.clone(), e))
                };
                // case-function arrow types at the ground `a'` (false / true):
                let case_arrows = |lhs: Expr| -> (Expr, Expr, Expr) {
                    (
                        eqbt(bor(lhs.clone(), bv.clone())),
                        Expr::arrow(eqbt(lhs), cc.clone()),
                        Expr::arrow(eqbt(bv.clone()), cc.clone()),
                    )
                };
                // a=false: λ (h : Bool.or false b = true)(fa)(fb). fb h
                //   (Bool.or false b ≡ b, so h : b = true; fb h : C)
                let false_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hyp, fa_arrow, fb_arrow) = case_arrows(bfalse.clone());
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let (fa_id, _fa) = c.fresh_local(fa_arrow.clone());
                    let (fb_id, fb) = c.fresh_local(fb_arrow.clone());
                    let body = Expr::app(fb, h);
                    let e = c.mk_lam(fb_id, BinderInfo::Default, fb_arrow, body);
                    let e = c.mk_lam(fa_id, BinderInfo::Default, fa_arrow, e);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, e))
                };
                // a=true: λ (h : Bool.or true b = true)(fa)(fb). fa h
                //   (Bool.or true b ≡ true, so h : true = true; fa h : C)
                let true_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hyp, fa_arrow, fb_arrow) = case_arrows(btrue.clone());
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let (fa_id, fa) = c.fresh_local(fa_arrow.clone());
                    let (fb_id, _fb) = c.fresh_local(fb_arrow.clone());
                    let body = Expr::app(fa, h);
                    let e = c.mk_lam(fb_id, BinderInfo::Default, fb_arrow, body);
                    let e = c.mk_lam(fa_id, BinderInfo::Default, fa_arrow, e);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, e))
                };
                let rec_a =
                    Expr::apps(bool_rec.clone(), [motive, false_case, true_case, a.clone()]);
                let e = b.mk_lam(c_id, BinderInfo::Default, prop.clone(), rec_a);
                let e = b.mk_lam(bv_id, BinderInfo::Default, bool_c.clone(), e);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Bool.or_eq_true_elim"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── Clean.Bool.eq_false_of_not_eq_true : ∀ b, Bool.not b = true → b = false ──
        // Single `Bool.rec` on `b`. `Bool.not false ≡ true` (so the b=false case's
        // goal `false = false` is `Eq.refl false`); `Bool.not true ≡ false` (so the
        // b=true hyp is `false = true` — `Bool.noConfusion` inhabits `true = false`).
        // Backs the Trust spec-elab NEGATION certified monitor (§1.1): a `!C`
        // clause monitor `Bool.not mon_C` cites this to turn `Bool.not mon_C = true`
        // into `mon_C = false`, then applies the inner clause's COMPLETENESS lemma
        // (Nat.not_le_of_ble_eq_false / Nat.ne_of_beq_false) to get ¬C.
        //
        // FIDELITY / KV-LIFT (2026-07-12): this seed MUST NOT be named
        // `Bool.not_eq_true`. Lean 4's real
        // `Bool.not_eq_true : (¬(b = true)) = (b = false)` is an
        // `@Eq Prop (Not (b = true)) (b = false)`, which is NOT definitionally equal
        // to this implication `(Bool.not b = true) → (b = false)`: different head
        // (Eq-of-Props vs Pi), and verified non-defeq in Lean's own kernel
        // (`fun (h : (!b) = true) => (h : ¬(b = true))` is rejected there). Seeding
        // under the real Lean name at env-init SHADOWED the authoritative olean
        // constant (the dedup correctly flags the type divergence and keeps the
        // seed), so every real Init/Std declaration whose proof cites Lean's
        // `Bool.not_eq_true` — e.g. via `forall_congr (fun a => Bool.not_eq_true …)`
        // — was re-checked against this WRONG type and rejected (KernelCheckFailed).
        // That was the dominant measured real-Lean KV residual (Init/PropLemmas
        // `Bool.dite_*` family + the 70 `Std/…/Associative` Bool `not`/`beq`/`decide`
        // lemmas). Renaming to the `Clean.` namespace frees the Lean name so the
        // genuine olean constant imports and re-verifies. Do NOT instead add a kernel
        // reduction making `Bool.not b = true` defeq to `Not (b = true)` — that would
        // OVER-ACCEPT relative to Lean and is unsound.
        if self
            .get_const(&Name::from_string("Clean.Bool.eq_false_of_not_eq_true"))
            .is_none()
        {
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (b_id, bv) = b.fresh_local(bool_c.clone());
                let hyp = eqbt(bnot(bv.clone()));
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hyp, eqbf(bv.clone()));
                b.finish(b.mk_pi(b_id, BinderInfo::Default, bool_c.clone(), e))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (b_id, bv) = b.fresh_local(bool_c.clone());
                // motive : fun b' => (Bool.not b' = true) → (b' = false)
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (bp_id, bp) = c.fresh_local(bool_c.clone());
                    let hyp = eqbt(bnot(bp.clone()));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    let inner = c.mk_pi(h_id, BinderInfo::Default, hyp, eqbf(bp.clone()));
                    c.finish_child(c.mk_lam(bp_id, BinderInfo::Default, bool_c.clone(), inner))
                };
                // b=false: λ (h : Bool.not false = true). Eq.refl false
                let false_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hyp = eqbt(bnot(bfalse.clone()));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, refl_false()))
                };
                // b=true: λ (h : Bool.not true = true). exfalso (true=false) h
                //   (Bool.not true ≡ false, so h : false = true)
                let true_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hyp = eqbt(bnot(btrue.clone()));
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let body = exfalso(eqbf(btrue.clone()), h);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, body))
                };
                let rec_b = Expr::apps(
                    bool_rec.clone(),
                    [motive, false_case, true_case, bv.clone()],
                );
                b.finish(b.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), rec_b))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Clean.Bool.eq_false_of_not_eq_true"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // The `= false` (COMPLETENESS-side) companions of the bridges above —
        // they back the DUAL certificate the negation-of-compound monitor needs
        // (`mon = false → ¬P`), so `!(P && Q)` / `!(P || Q)` can be certified via
        // De Morgan. `False` + `Or.rec` (a Prop-recursor: no universe param, like
        // `Nat.le.rec`) are used below.
        let false_c2 = Expr::const_(Name::from_string("False"), vec![]);
        let prop0 = Expr::prop();

        // ── Clean.Bool.eq_true_of_not_eq_false : ∀ b, Bool.not b = false → b = true ──
        // FIDELITY / KV-LIFT (2026-07-12): same rename as
        // `Clean.Bool.eq_false_of_not_eq_true` above. Lean 4's real
        // `Bool.not_eq_false : (¬(b = false)) = (b = true)` is
        // `@Eq Prop (Not (b = false)) (b = true)`, NOT defeq to this implication
        // `(Bool.not b = false) → (b = true)`. Seeding the Lean name shadowed the
        // olean constant and was the other half of the measured Bool KV residual.
        if self
            .get_const(&Name::from_string("Clean.Bool.eq_true_of_not_eq_false"))
            .is_none()
        {
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (b_id, bv) = b.fresh_local(bool_c.clone());
                let hyp = eqbf(bnot(bv.clone()));
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hyp, eqbt(bv.clone()));
                b.finish(b.mk_pi(b_id, BinderInfo::Default, bool_c.clone(), e))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (b_id, bv) = b.fresh_local(bool_c.clone());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (bp_id, bp) = c.fresh_local(bool_c.clone());
                    let hyp = eqbf(bnot(bp.clone()));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    let inner = c.mk_pi(h_id, BinderInfo::Default, hyp, eqbt(bp.clone()));
                    c.finish_child(c.mk_lam(bp_id, BinderInfo::Default, bool_c.clone(), inner))
                };
                // b=false: Bool.not false ≡ true, so h : true = false → exfalso
                let false_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hyp = eqbf(bnot(bfalse.clone()));
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let body = exfalso_tf(eqbt(bfalse.clone()), h);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, body))
                };
                // b=true: Bool.not true ≡ false, so h : false = false; goal true=true
                let true_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let hyp = eqbf(bnot(btrue.clone()));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, refl_true()))
                };
                let rec_b = Expr::apps(
                    bool_rec.clone(),
                    [motive, false_case, true_case, bv.clone()],
                );
                b.finish(b.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), rec_b))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Clean.Bool.eq_true_of_not_eq_false"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── Bool.and_eq_false_elim :
        //      ∀ a b (C:Prop), Bool.and a b=false → (a=false→C)→(b=false→C)→C ──
        // Bool.and false b ≡ false (apply fa); Bool.and true b ≡ b (hyp b=false, fb).
        if self
            .get_const(&Name::from_string("Bool.and_eq_false_elim"))
            .is_none()
        {
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_c.clone());
                let (bv_id, bv) = b.fresh_local(bool_c.clone());
                let (c_id, cc) = b.fresh_local(prop0.clone());
                let hyp = eqbf(band(a.clone(), bv.clone()));
                let fa_arrow = Expr::arrow(eqbf(a.clone()), cc.clone());
                let fb_arrow = Expr::arrow(eqbf(bv.clone()), cc.clone());
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let (fa_id, _fa) = b.fresh_local(fa_arrow.clone());
                let (fb_id, _fb) = b.fresh_local(fb_arrow.clone());
                let e = b.mk_pi(fb_id, BinderInfo::Default, fb_arrow, cc.clone());
                let e = b.mk_pi(fa_id, BinderInfo::Default, fa_arrow, e);
                let e = b.mk_pi(h_id, BinderInfo::Default, hyp, e);
                let e = b.mk_pi(c_id, BinderInfo::Default, prop0.clone(), e);
                let e = b.mk_pi(bv_id, BinderInfo::Default, bool_c.clone(), e);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_c.clone());
                let (bv_id, bv) = b.fresh_local(bool_c.clone());
                let (c_id, cc) = b.fresh_local(prop0.clone());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ap_id, ap) = c.fresh_local(bool_c.clone());
                    let hyp = eqbf(band(ap.clone(), bv.clone()));
                    let fa_arrow = Expr::arrow(eqbf(ap.clone()), cc.clone());
                    let fb_arrow = Expr::arrow(eqbf(bv.clone()), cc.clone());
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    let (fa_id, _fa) = c.fresh_local(fa_arrow.clone());
                    let (fb_id, _fb) = c.fresh_local(fb_arrow.clone());
                    let e = c.mk_pi(fb_id, BinderInfo::Default, fb_arrow, cc.clone());
                    let e = c.mk_pi(fa_id, BinderInfo::Default, fa_arrow, e);
                    let e = c.mk_pi(h_id, BinderInfo::Default, hyp, e);
                    c.finish_child(c.mk_lam(ap_id, BinderInfo::Default, bool_c.clone(), e))
                };
                let case_arrows = |lhs: Expr| -> (Expr, Expr, Expr) {
                    (
                        eqbf(band(lhs.clone(), bv.clone())),
                        Expr::arrow(eqbf(lhs), cc.clone()),
                        Expr::arrow(eqbf(bv.clone()), cc.clone()),
                    )
                };
                // a=false: λ h fa fb. fa h   (Bool.and false b ≡ false; h : false=false)
                let false_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hyp, fa_arrow, fb_arrow) = case_arrows(bfalse.clone());
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let (fa_id, fa) = c.fresh_local(fa_arrow.clone());
                    let (fb_id, _fb) = c.fresh_local(fb_arrow.clone());
                    let body = Expr::app(fa, h);
                    let e = c.mk_lam(fb_id, BinderInfo::Default, fb_arrow, body);
                    let e = c.mk_lam(fa_id, BinderInfo::Default, fa_arrow, e);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, e))
                };
                // a=true: λ h fa fb. fb h   (Bool.and true b ≡ b; h : b=false)
                let true_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hyp, fa_arrow, fb_arrow) = case_arrows(btrue.clone());
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let (fa_id, _fa) = c.fresh_local(fa_arrow.clone());
                    let (fb_id, fb) = c.fresh_local(fb_arrow.clone());
                    let body = Expr::app(fb, h);
                    let e = c.mk_lam(fb_id, BinderInfo::Default, fb_arrow, body);
                    let e = c.mk_lam(fa_id, BinderInfo::Default, fa_arrow, e);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, e))
                };
                let rec_a =
                    Expr::apps(bool_rec.clone(), [motive, false_case, true_case, a.clone()]);
                let e = b.mk_lam(c_id, BinderInfo::Default, prop0.clone(), rec_a);
                let e = b.mk_lam(bv_id, BinderInfo::Default, bool_c.clone(), e);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Bool.and_eq_false_elim"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── Bool.or_eq_false_elim :
        //      ∀ a b (C:Prop), Bool.or a b=false → (a=false→b=false→C)→C ──
        // Bool.or a b = false means BOTH are false, so the single case function
        // receives both proofs. Bool.or false b ≡ b (h : b=false, a=false is refl);
        // Bool.or true b ≡ true (h : true=false, impossible).
        if self
            .get_const(&Name::from_string("Bool.or_eq_false_elim"))
            .is_none()
        {
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_c.clone());
                let (bv_id, bv) = b.fresh_local(bool_c.clone());
                let (c_id, cc) = b.fresh_local(prop0.clone());
                let hyp = eqbf(bor(a.clone(), bv.clone()));
                let k_arrow =
                    Expr::arrow(eqbf(a.clone()), Expr::arrow(eqbf(bv.clone()), cc.clone()));
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let (k_id, _k) = b.fresh_local(k_arrow.clone());
                let e = b.mk_pi(k_id, BinderInfo::Default, k_arrow, cc.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hyp, e);
                let e = b.mk_pi(c_id, BinderInfo::Default, prop0.clone(), e);
                let e = b.mk_pi(bv_id, BinderInfo::Default, bool_c.clone(), e);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), e))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bool_c.clone());
                let (bv_id, bv) = b.fresh_local(bool_c.clone());
                let (c_id, cc) = b.fresh_local(prop0.clone());
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ap_id, ap) = c.fresh_local(bool_c.clone());
                    let hyp = eqbf(bor(ap.clone(), bv.clone()));
                    let k_arrow =
                        Expr::arrow(eqbf(ap.clone()), Expr::arrow(eqbf(bv.clone()), cc.clone()));
                    let (h_id, _h) = c.fresh_local(hyp.clone());
                    let (k_id, _k) = c.fresh_local(k_arrow.clone());
                    let e = c.mk_pi(k_id, BinderInfo::Default, k_arrow, cc.clone());
                    let e = c.mk_pi(h_id, BinderInfo::Default, hyp, e);
                    c.finish_child(c.mk_lam(ap_id, BinderInfo::Default, bool_c.clone(), e))
                };
                let case_parts = |lhs: Expr| -> (Expr, Expr) {
                    (
                        eqbf(bor(lhs.clone(), bv.clone())),
                        Expr::arrow(eqbf(lhs), Expr::arrow(eqbf(bv.clone()), cc.clone())),
                    )
                };
                // a=false: λ (h : b=false) (k). k (Eq.refl false) h
                let false_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hyp, k_arrow) = case_parts(bfalse.clone());
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let (k_id, k) = c.fresh_local(k_arrow.clone());
                    let body = Expr::apps(k, [refl_false(), h]);
                    let e = c.mk_lam(k_id, BinderInfo::Default, k_arrow, body);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, e))
                };
                // a=true: λ (h : true=false) (k). exfalso_tf C h
                let true_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hyp, k_arrow) = case_parts(btrue.clone());
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let (k_id, _k) = c.fresh_local(k_arrow.clone());
                    let body = exfalso_tf(cc.clone(), h);
                    let e = c.mk_lam(k_id, BinderInfo::Default, k_arrow, body);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, hyp, e))
                };
                let rec_a =
                    Expr::apps(bool_rec.clone(), [motive, false_case, true_case, a.clone()]);
                let e = b.mk_lam(c_id, BinderInfo::Default, prop0.clone(), rec_a);
                let e = b.mk_lam(bv_id, BinderInfo::Default, bool_c.clone(), e);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Bool.or_eq_false_elim"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── not_or_intro : ∀ (p q : Prop), (p → False) → (q → False) → (p ∨ q → False) ──
        // Standard De Morgan half, via `Or.rec` (Prop-recursor, no universe param)
        // with the constant motive `fun _ => False`.
        if self.get_const(&Name::from_string("not_or_intro")).is_none() {
            let or_c2 = Expr::const_(Name::from_string("Or"), vec![]);
            let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
            let or_pq = |p: Expr, q: Expr| Expr::apps(or_c2.clone(), [p, q]);
            let neg = |p: Expr| Expr::arrow(p, false_c2.clone());
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(prop0.clone());
                let (q_id, q) = b.fresh_local(prop0.clone());
                let (np_id, _np) = b.fresh_local(neg(p.clone()));
                let (nq_id, _nq) = b.fresh_local(neg(q.clone()));
                let concl = neg(or_pq(p.clone(), q.clone()));
                let e = b.mk_pi(nq_id, BinderInfo::Default, neg(q.clone()), concl);
                let e = b.mk_pi(np_id, BinderInfo::Default, neg(p.clone()), e);
                let e = b.mk_pi(q_id, BinderInfo::Default, prop0.clone(), e);
                b.finish(b.mk_pi(p_id, BinderInfo::Default, prop0.clone(), e))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(prop0.clone());
                let (q_id, q) = b.fresh_local(prop0.clone());
                let (np_id, np) = b.fresh_local(neg(p.clone()));
                let (nq_id, nq) = b.fresh_local(neg(q.clone()));
                // λ (hor : Or p q). @Or.rec p q (fun _ => False) np nq hor
                let hor_body = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hor_id, hor) = c.fresh_local(or_pq(p.clone(), q.clone()));
                    let motive = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (t_id, _t) = d.fresh_local(or_pq(p.clone(), q.clone()));
                        d.finish_child(d.mk_lam(
                            t_id,
                            BinderInfo::Default,
                            or_pq(p.clone(), q.clone()),
                            false_c2.clone(),
                        ))
                    };
                    let rec_app = Expr::apps(
                        or_rec.clone(),
                        [p.clone(), q.clone(), motive, np.clone(), nq.clone(), hor],
                    );
                    c.finish_child(c.mk_lam(
                        hor_id,
                        BinderInfo::Default,
                        or_pq(p.clone(), q.clone()),
                        rec_app,
                    ))
                };
                let e = b.mk_lam(nq_id, BinderInfo::Default, neg(q.clone()), hor_body);
                let e = b.mk_lam(np_id, BinderInfo::Default, neg(p.clone()), e);
                let e = b.mk_lam(q_id, BinderInfo::Default, prop0.clone(), e);
                b.finish(b.mk_lam(p_id, BinderInfo::Default, prop0.clone(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("not_or_intro"),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        // ── not_and_of_not_left  : ∀ (p q : Prop), (p → False) → (p ∧ q → False) ──
        // ── not_and_of_not_right : ∀ (p q : Prop), (q → False) → (p ∧ q → False) ──
        // The other De Morgan half: one false conjunct refutes the conjunction.
        // `λ p q n hpq. n (And.left/right p q hpq)`.
        {
            let and_c2 = Expr::const_(Name::from_string("And"), vec![]);
            let and_pq = |p: Expr, q: Expr| Expr::apps(and_c2.clone(), [p, q]);
            let neg = |p: Expr| Expr::arrow(p, false_c2.clone());
            for (thm, proj_name, proj_of) in [
                ("not_and_of_not_left", "And.left", true),
                ("not_and_of_not_right", "And.right", false),
            ] {
                if self.get_const(&Name::from_string(thm)).is_some() {
                    continue;
                }
                let proj = Expr::const_(Name::from_string(proj_name), vec![]);
                // The hypothesis is a negation of p (left) or q (right).
                let type_ = {
                    let mut b = EnvDeclBuilder::new();
                    let (p_id, p) = b.fresh_local(prop0.clone());
                    let (q_id, q) = b.fresh_local(prop0.clone());
                    let hyp_neg = if proj_of {
                        neg(p.clone())
                    } else {
                        neg(q.clone())
                    };
                    let (n_id, _n) = b.fresh_local(hyp_neg.clone());
                    let concl = neg(and_pq(p.clone(), q.clone()));
                    let e = b.mk_pi(n_id, BinderInfo::Default, hyp_neg, concl);
                    let e = b.mk_pi(q_id, BinderInfo::Default, prop0.clone(), e);
                    b.finish(b.mk_pi(p_id, BinderInfo::Default, prop0.clone(), e))
                };
                let value = {
                    let mut b = EnvDeclBuilder::new();
                    let (p_id, p) = b.fresh_local(prop0.clone());
                    let (q_id, q) = b.fresh_local(prop0.clone());
                    let hyp_neg = if proj_of {
                        neg(p.clone())
                    } else {
                        neg(q.clone())
                    };
                    let (n_id, n) = b.fresh_local(hyp_neg.clone());
                    // λ (hpq : And p q). n (proj p q hpq)
                    let body = {
                        let mut c = EnvDeclBuilder::child_of(&b);
                        let (hpq_id, hpq) = c.fresh_local(and_pq(p.clone(), q.clone()));
                        let projected = Expr::apps(proj.clone(), [p.clone(), q.clone(), hpq]);
                        let applied = Expr::app(n.clone(), projected);
                        c.finish_child(c.mk_lam(
                            hpq_id,
                            BinderInfo::Default,
                            and_pq(p.clone(), q.clone()),
                            applied,
                        ))
                    };
                    let e = b.mk_lam(n_id, BinderInfo::Default, hyp_neg, body);
                    let e = b.mk_lam(q_id, BinderInfo::Default, prop0.clone(), e);
                    b.finish(b.mk_lam(p_id, BinderInfo::Default, prop0.clone(), e))
                };
                self.add_decl(Declaration::Theorem {
                    name: Name::from_string(thm),
                    level_params: vec![],
                    type_,
                    value,
                })?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::TypeChecker;

    fn check_axiom_free(env: &Environment, thm: &str) {
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(thm), vec![]))
            .unwrap_or_else(|e| panic!("{thm} should type-check: {e:?}"));
        let deps = env
            .axiom_deps(&Name::from_string(thm))
            .unwrap_or_else(|| panic!("{thm} should be registered"));
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "{thm} must be axiom-free, got {names:?}");
    }

    #[test]
    fn test_bool_and_eq_true_bridges_type_check_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_bool_and_eq_true_bridges().expect("register");
        env.register_bool_and_eq_true_bridges().expect("idempotent");
        check_axiom_free(&env, "Bool.and_eq_true_left");
        check_axiom_free(&env, "Bool.and_eq_true_right");
        check_axiom_free(&env, "Bool.or_eq_true_elim");
        check_axiom_free(&env, "Clean.Bool.eq_false_of_not_eq_true");
        check_axiom_free(&env, "Clean.Bool.eq_true_of_not_eq_false");
        check_axiom_free(&env, "Bool.and_eq_false_elim");
        check_axiom_free(&env, "Bool.or_eq_false_elim");
        check_axiom_free(&env, "not_or_intro");
        check_axiom_free(&env, "not_and_of_not_left");
        check_axiom_free(&env, "not_and_of_not_right");
    }

    /// FIDELITY / KV-LIFT regression (2026-07-12). The Bool `not`/`not_eq`
    /// implication bridges must NOT squat the real Lean 4 stdlib names
    /// `Bool.not_eq_true` / `Bool.not_eq_false`. Lean's real constants are
    /// Eq-of-Props — `Bool.not_eq_true : (¬(b = true)) = (b = false)` — which are
    /// NOT definitionally equal to Clean's implication bridges
    /// `(Bool.not b = true) → (b = false)` (Eq-of-Props head vs Pi head; the
    /// olean dedup correctly flags the divergence). Seeding under the Lean name
    /// shadowed the authoritative olean constant and made Clean reject every real
    /// Init/Std proof that cites Lean's `Bool.not_eq_true` (measured: the
    /// Init/PropLemmas `Bool.dite_*` family + 70 `Std/…/Associative` Bool
    /// `not`/`beq`/`decide` lemmas). This pins that (a) the Lean names stay FREE
    /// for the importer, (b) the renamed internal bridges exist, and (c) the
    /// kernel does NOT — unsoundly — treat the two Bool forms as defeq.
    #[test]
    fn test_bool_not_eq_bridges_do_not_shadow_lean_stdlib_names() {
        use crate::expr::FVarId;

        let mut env = Environment::with_prelude();
        env.register_bool_and_eq_true_bridges().expect("register");

        // (a) The real Lean names are FREE — the olean importer supplies the
        //     authoritative `@Eq Prop (Not (b = …)) (b = …)` constants.
        assert!(
            env.get_const(&Name::from_string("Bool.not_eq_true"))
                .is_none(),
            "seed must not squat Lean's `Bool.not_eq_true`"
        );
        assert!(
            env.get_const(&Name::from_string("Bool.not_eq_false"))
                .is_none(),
            "seed must not squat Lean's `Bool.not_eq_false`"
        );

        // (b) The renamed internal implication bridges are present.
        assert!(
            env.get_const(&Name::from_string("Clean.Bool.eq_false_of_not_eq_true"))
                .is_some(),
            "renamed internal bridge must be registered"
        );
        assert!(
            env.get_const(&Name::from_string("Clean.Bool.eq_true_of_not_eq_false"))
                .is_some(),
            "renamed internal bridge must be registered"
        );

        // (c) LOUD NEGATIVE: `Bool.not b = true` is NOT defeq to `Not (b = true)`,
        //     exactly as Lean's own kernel rejects
        //     `fun (h : (!b) = true) => (h : ¬(b = true))`. Treating them equal
        //     would over-accept relative to Lean and be unsound — this is the
        //     boundary the fix deliberately does NOT cross.
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let not_op = Expr::const_(Name::from_string("Bool.not"), vec![]);
        let not_prop = Expr::const_(Name::from_string("Not"), vec![]);
        let b = Expr::fvar(FVarId::new(7));
        // (Bool.not b) = true
        let bnot_eq_true = Expr::apps(
            eq_c.clone(),
            [bool_c.clone(), Expr::app(not_op, b.clone()), btrue.clone()],
        );
        // Not (b = true)
        let b_eq_true = Expr::apps(eq_c, [bool_c, b, btrue]);
        let not_b_eq_true = Expr::app(not_prop, b_eq_true);
        let tc = TypeChecker::new(&env);
        assert!(
            !tc.is_def_eq(&bnot_eq_true, &not_b_eq_true),
            "kernel must NOT treat `Bool.not b = true` as defeq to `Not (b = true)` \
             — Lean's kernel rejects it; equating them would over-accept (unsound)"
        );
    }
}
