// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Substitutivity of the step relation** — item (1) of
//! `designs/2026-09-18-is-candmodel-uninhabited.md`'s work list, and the first
//! object on the path to asking whether `CandModel` is inhabited.
//!
//! ```text
//! beta_reduces e e' -> forall s, beta_reduces (psubst s e) (psubst s e')
//! ```
//!
//! Nothing of this shape exists in the tree — searched by STATEMENT, not by
//! name: the only constants relating two steps with a substitution between them
//! are `the_red_env` and `wRecSpine1_step_inv`, and neither is it.
//! `betaReduces_psubst`, the one name that looks right, is the β rule restated
//! over `psubst` rather than a congruence.
//!
//! # Why `psubst` and not `instantiate`
//!
//! Stated over `instantiate` the three under-binder arms (`lam_body`, `pi_cod`,
//! `let_body`) need the substitution at a lifted depth and the proof becomes de
//! Bruijn arithmetic. Stated over `psubst` they are ordinary congruences, for
//! two reasons that together are the whole design:
//!
//! * `psubst` carries its own shifting through `up`, so the under-binder arms
//!   simply apply the induction hypothesis **at `up s`**;
//! * `psubst` is a `KExpr.rec` with a function-valued motive, so
//!   `psubst s (KExpr.app f a)` ι-reduces to `KExpr.app (psubst s f)
//!   (psubst s a)` DEFINITIONALLY. Every congruence arm is therefore one
//!   constructor application and an induction hypothesis, with no rewrite at
//!   all.
//!
//! Only `beta` and `zeta` need anything at all, and only because their
//! right-hand sides are `instantiate`: there the arm must show
//! `psubst s (instantiate b a) = instantiate (psubst (up s) b) (psubst s a)`.
//!
//! **That equation already exists, as `psubst_instantiate`, stated in exactly
//! that form.** The first version of this module derived it from
//! `instantiate_eq_psubst` + `psubst_comp` + `psubst_scons_instantiate` through
//! two helper lemmas of its own, because I looked for the ingredients before
//! looking for the result. Both helpers refused, and the elaborator named the
//! lemma in the same breath — *"Unknown identifier: …; nearest theorem names:
//! psubst_instantiate"*. The arms now use it directly and this module registers
//! ONE constant.
//!
//! # The ι residual is CARRIED, not proved
//!
//! The `iota` arm needs `iota_reduces` substitutivity, which is a separate
//! problem about the recursor rules rather than about substitution. It is taken
//! as a hypothesis, exactly as this crate already does with `hiota` / `hiotap` /
//! `hiotad`, so that this lands as ONE object instead of two coupled ones.
//!
//! # Arities, measured rather than grepped
//!
//! `KExpr.rec` takes a motive plus NINE minors — sort, bvar, app, lam, pi,
//! const, let_, proj, lit — and `beta_reduces` has FIFTEEN constructors. Both
//! were established by paren-matching `psubst`'s own recursor application;
//! grep gave the wrong answer twice while this file was being written.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The statement and its proof term, built arm by arm.
    pub(super) fn beta_subst_congr_src() -> String {
        let goal = |x: &str, y: &str| {
            format!("forall (s : Nat -> KExpr), beta_reduces (psubst s {x}) (psubst s {y})")
        };
        let motive = format!(
            "(fun (x : KExpr) (y : KExpr) (_h : beta_reduces x y) => {})",
            goal("x", "y")
        );
        format!(
            "def beta_reduces_psubst_congr \
             (hiota : forall (x : KExpr) (y : KExpr) (t : Nat -> KExpr), \
             iota_reduces x y -> beta_reduces (psubst t x) (psubst t y)) \
             (e : KExpr) (e2 : KExpr) (h : beta_reduces e e2) : {goal_e} := \
             beta_reduces.rec {motive} \
             {a_beta} {a_app_left} {a_app_right} {a_lam_ty} {a_lam_body} \
             {a_pi_dom} {a_pi_cod} {a_fa_dom} {a_fa_cod} {a_zeta} \
             {a_let_ty} {a_let_val} {a_let_body} {a_iota} {a_proj} \
             e e2 h",
            goal_e = goal("e", "e2"),
            // beta: the right-hand side is an `instantiate`, so the arm rebuilds
            // the redex under psubst and then transports along the substrate's
            // composition chain.
            a_beta = "(fun (A : KExpr) (body : KExpr) (arg : KExpr) (s : Nat -> KExpr) => \
                      Eq.substType KExpr \
                      (fun (z : KExpr) => beta_reduces \
                      (KExpr.app (KExpr.lam (psubst s A) (psubst (up s) body)) (psubst s arg)) z) \
                      (instantiate (psubst (up s) body) (psubst s arg)) \
                      (psubst s (instantiate body arg)) \
                      (Eq.symm KExpr (psubst s (instantiate body arg)) \
                      (instantiate (psubst (up s) body) (psubst s arg)) \
                      (psubst_instantiate body arg s)) \
                      (beta_reduces.beta (psubst s A) (psubst (up s) body) (psubst s arg)))",
            a_app_left = "(fun (f : KExpr) (f2 : KExpr) (a : KExpr) \
                          (_hs : beta_reduces f f2) \
                          (ih : forall (s : Nat -> KExpr), \
                          beta_reduces (psubst s f) (psubst s f2)) (s : Nat -> KExpr) => \
                          beta_reduces.app_left (psubst s f) (psubst s f2) (psubst s a) (ih s))",
            a_app_right = "(fun (f : KExpr) (a : KExpr) (a2 : KExpr) \
                           (_hs : beta_reduces a a2) \
                           (ih : forall (s : Nat -> KExpr), \
                           beta_reduces (psubst s a) (psubst s a2)) (s : Nat -> KExpr) => \
                           beta_reduces.app_right (psubst s f) (psubst s a) (psubst s a2) (ih s))",
            a_lam_ty = "(fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) \
                        (_hs : beta_reduces ty ty2) \
                        (ih : forall (s : Nat -> KExpr), \
                        beta_reduces (psubst s ty) (psubst s ty2)) (s : Nat -> KExpr) => \
                        beta_reduces.lam_ty (psubst s ty) (psubst s ty2) \
                        (psubst (up s) body) (ih s))",
            // UNDER A BINDER: the induction hypothesis is taken at `up s`.
            a_lam_body = "(fun (ty : KExpr) (body : KExpr) (body2 : KExpr) \
                          (_hs : beta_reduces body body2) \
                          (ih : forall (s : Nat -> KExpr), \
                          beta_reduces (psubst s body) (psubst s body2)) (s : Nat -> KExpr) => \
                          beta_reduces.lam_body (psubst s ty) (psubst (up s) body) \
                          (psubst (up s) body2) (ih (up s)))",
            a_pi_dom = "(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) \
                        (_hs : beta_reduces dom dom2) \
                        (ih : forall (s : Nat -> KExpr), \
                        beta_reduces (psubst s dom) (psubst s dom2)) (s : Nat -> KExpr) => \
                        beta_reduces.pi_dom (psubst s dom) (psubst s dom2) \
                        (psubst (up s) body) (ih s))",
            a_pi_cod = "(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) \
                        (_hs : beta_reduces body body2) \
                        (ih : forall (s : Nat -> KExpr), \
                        beta_reduces (psubst s body) (psubst s body2)) (s : Nat -> KExpr) => \
                        beta_reduces.pi_cod (psubst s dom) (psubst (up s) body) \
                        (psubst (up s) body2) (ih (up s)))",
            // The forall_ arms are written exactly as the pi arms. If
            // `KExpr.forall_` is a `pi` alias these elaborate unchanged; if it
            // is a tenth constructor they fail and say so, which is the
            // identification this module also settles.
            a_fa_dom = "(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) \
                        (_hs : beta_reduces dom dom2) \
                        (ih : forall (s : Nat -> KExpr), \
                        beta_reduces (psubst s dom) (psubst s dom2)) (s : Nat -> KExpr) => \
                        beta_reduces.forall_congr_dom (psubst s dom) (psubst s dom2) \
                        (psubst (up s) body) (ih s))",
            a_fa_cod = "(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) \
                        (_hs : beta_reduces body body2) \
                        (ih : forall (s : Nat -> KExpr), \
                        beta_reduces (psubst s body) (psubst s body2)) (s : Nat -> KExpr) => \
                        beta_reduces.forall_congr_cod (psubst s dom) (psubst (up s) body) \
                        (psubst (up s) body2) (ih (up s)))",
            // zeta: the same instantiate transport as beta, one constructor over.
            a_zeta = "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (s : Nat -> KExpr) => \
                      Eq.substType KExpr \
                      (fun (z : KExpr) => beta_reduces \
                      (KExpr.let_ (psubst s ty) (psubst s val) (psubst (up s) body)) z) \
                      (instantiate (psubst (up s) body) (psubst s val)) \
                      (psubst s (instantiate body val)) \
                      (Eq.symm KExpr (psubst s (instantiate body val)) \
                      (instantiate (psubst (up s) body) (psubst s val)) \
                      (psubst_instantiate body val s)) \
                      (beta_reduces.zeta (psubst s ty) (psubst s val) (psubst (up s) body)))",
            a_let_ty = "(fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) \
                        (_hs : beta_reduces ty ty2) \
                        (ih : forall (s : Nat -> KExpr), \
                        beta_reduces (psubst s ty) (psubst s ty2)) (s : Nat -> KExpr) => \
                        beta_reduces.let_ty (psubst s ty) (psubst s ty2) (psubst s val) \
                        (psubst (up s) body) (ih s))",
            a_let_val = "(fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) \
                         (_hs : beta_reduces val val2) \
                         (ih : forall (s : Nat -> KExpr), \
                         beta_reduces (psubst s val) (psubst s val2)) (s : Nat -> KExpr) => \
                         beta_reduces.let_val (psubst s ty) (psubst s val) (psubst s val2) \
                         (psubst (up s) body) (ih s))",
            a_let_body = "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) \
                          (_hs : beta_reduces body body2) \
                          (ih : forall (s : Nat -> KExpr), \
                          beta_reduces (psubst s body) (psubst s body2)) (s : Nat -> KExpr) => \
                          beta_reduces.let_body (psubst s ty) (psubst s val) \
                          (psubst (up s) body) (psubst (up s) body2) (ih (up s)))",
            // The CARRIED residual.
            a_iota = "(fun (x : KExpr) (y : KExpr) (hir : iota_reduces x y) \
                      (s : Nat -> KExpr) => hiota x y s hir)",
            a_proj = "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub2 : KExpr) \
                      (_hs : beta_reduces sub sub2) \
                      (ih : forall (s : Nat -> KExpr), \
                      beta_reduces (psubst s sub) (psubst s sub2)) (s : Nat -> KExpr) => \
                      beta_reduces.proj ps pidx (psubst s sub) (psubst s sub2) (ih s))",
        )
    }

    /// Substitutivity lifted from `beta_reduces` to `whnf_step`.
    ///
    /// `whnf_step` has exactly two arms, `beta` and `delta`, so this is one
    /// application of [`Self::beta_subst_congr_src`] and one carried residual.
    /// The δ residual is carried for the same reason the ι one is: a δ step
    /// unfolds a constant, and whether that commutes with substitution is a
    /// question about `delta_reduces`'s own congruence structure, not about
    /// substitution.
    pub(super) fn whnf_step_subst_congr_src() -> String {
        // whnf_step.rec takes its INDICES FIRST and a motive over the proof
        // alone -- `whnf_step.rec a b (fun (_ : whnf_step a b) => C) beta delta h`
        // -- so each minor binds only its own reduction proof. Read off an
        // existing call site rather than assumed; the first version bound the
        // indices in the arms and was refused with "expected (x : beta_reduces
        // …) -> …". Note this differs from `whnf_acc.rec`, whose motive DOES
        // take the index; the two conventions sit side by side in this file.
        "def whnf_step_psubst_congr \
         (hiota : forall (x : KExpr) (y : KExpr) (t : Nat -> KExpr), \
         iota_reduces x y -> beta_reduces (psubst t x) (psubst t y)) \
         (hdelta : forall (x : KExpr) (y : KExpr) (t : Nat -> KExpr), \
         delta_reduces x y -> whnf_step (psubst t x) (psubst t y)) \
         (e : KExpr) (e2 : KExpr) (h : whnf_step e e2) : \
         forall (s : Nat -> KExpr), whnf_step (psubst s e) (psubst s e2) := \
         whnf_step.rec e e2 \
         (fun (_h : whnf_step e e2) => \
         forall (s : Nat -> KExpr), whnf_step (psubst s e) (psubst s e2)) \
         (fun (hb : beta_reduces e e2) (s : Nat -> KExpr) => \
         whnf_step.beta (psubst s e) (psubst s e2) \
         (beta_reduces_psubst_congr hiota e e2 hb s)) \
         (fun (hd : delta_reduces e e2) (s : Nat -> KExpr) => hdelta e e2 s hd) \
         h"
        .to_string()
    }

    /// **ITEM (2)** — anti-substitution for accessibility:
    /// `whnf_acc (psubst s e) -> whnf_acc e`.
    ///
    /// This is the lemma `redLet` needs at its `let_body` case, and the reason
    /// the type-blind `CandModel` probe stops where it does: `redLet` is handed
    /// accessibility of `instantiate b a` and never of `b`, while `let_body`
    /// lets reduction happen inside `b`.
    ///
    /// By accessibility induction on the SUBSTITUTED term, with the motive
    /// carrying an EQUATION rather than the term itself — `whnf_acc.rec` binds
    /// the scrutinee, so without the equation the induction hypothesis could
    /// not be re-aimed at `psubst s e2` for the `e2` the goal is about. The
    /// step is [`Self::whnf_step_subst_congr_src`]: a reduction of `e` induces
    /// one of `psubst s e`, which is what lets the hypothesis be inverted at
    /// the substituted term.
    pub(super) fn whnf_acc_psubst_inv_src() -> String {
        let motive = "(fun (y : KExpr) (_hy : whnf_acc y) => \
                      forall (e : KExpr) (s : Nat -> KExpr), \
                      Eq KExpr y (psubst s e) -> whnf_acc e)";
        format!(
            "def whnf_acc_psubst_inv \
             (hiota : forall (x : KExpr) (y : KExpr) (t : Nat -> KExpr), \
             iota_reduces x y -> beta_reduces (psubst t x) (psubst t y)) \
             (hdelta : forall (x : KExpr) (y : KExpr) (t : Nat -> KExpr), \
             delta_reduces x y -> whnf_step (psubst t x) (psubst t y)) \
             (x : KExpr) (hx : whnf_acc x) : \
             forall (e : KExpr) (s : Nat -> KExpr), Eq KExpr x (psubst s e) -> whnf_acc e := \
             whnf_acc.rec {motive} \
             (fun (y : KExpr) \
             (f : forall (y2 : KExpr), whnf_step y y2 -> whnf_acc y2) \
             (ih : forall (y2 : KExpr) (_st : whnf_step y y2), \
             forall (e : KExpr) (s : Nat -> KExpr), Eq KExpr y2 (psubst s e) -> whnf_acc e) \
             (e : KExpr) (s : Nat -> KExpr) (heq : Eq KExpr y (psubst s e)) => \
             whnf_acc.intro e (fun (e2 : KExpr) (st : whnf_step e e2) => \
             ih (psubst s e2) \
             (Eq.substType KExpr (fun (z : KExpr) => whnf_step z (psubst s e2)) \
             (psubst s e) y (Eq.symm KExpr y (psubst s e) heq) \
             (whnf_step_psubst_congr hiota hdelta e e2 st s)) \
             e2 s (Eq.refl KExpr (psubst s e2)))) \
             x hx"
        )
    }

    /// **What a step out of a `let_` can be** — the inversion item (3) needs.
    ///
    /// `redLet` at the type-blind candidate must show `whnf_acc (let_ A a b)`,
    /// so by `whnf_acc.intro` it owes a case for EVERY step out of that term.
    /// Nothing in the tree inverts one: the only step-inversion lemmas are
    /// `wRecSpine1_step_inv` and `wRecSpine2_step_inv`, both about W-recursor
    /// spines.
    ///
    /// Four cases are real — ζ and the three congruences — and ten of
    /// `beta_reduces`'s fifteen arms are refuted outright because their
    /// left index is a different constructor (`let_ne_app`, `let_ne_lam`,
    /// `let_ne_pi`, `let_ne_proj`; the two `forall_congr_*` arms go through
    /// `let_ne_pi` because `KExpr.forall_` is a `pi` alias, which
    /// `beta_reduces_psubst_congr` established).
    ///
    /// **Two arms are CARRIED rather than refuted**, and honestly so: `iota`
    /// and `delta` have a VARIABLE left index, so no discrimination lemma
    /// touches them. Whether a `let_` can δ- or ι-step is a question about
    /// those relations, not about `let_`, and the caller supplies the answer.
    ///
    /// **The four real arms must TRANSPORT through `let_` injectivity.** An
    /// arm binds its own `ty`/`val`/`body`; the continuations are stated at the
    /// outer `A`/`a`/`b`. The equation `hx` is what relates them, via
    /// `let_inj_fst` / `_snd` / `_thd`, and each arm spends two of those on its
    /// result equation plus one on its reduction. Omitting them is refused with
    /// "fvar mismatch", which points at the binder and not at the missing
    /// rewrite.
    ///
    /// **Each arm's induction hypothesis is the motive at that arm's OWN
    /// SUBTERMS**, not at its conclusion's indices — `app_left`'s is about `f`
    /// and `f'`, never about `app f a` and `app f' a`. Writing it the other way
    /// is refused with "cannot unify an application with a free variable",
    /// which names the symptom and not the cause. None of the twelve congruence
    /// arms USES its hypothesis — each is refuted by a discrimination lemma or
    /// rebuilt from the two equations — but dead weight still has to be typed
    /// correctly.
    ///
    /// **`C` is a `Type`, not a `Prop`, and that is forced.** The generated
    /// discrimination lemmas are `forall <binders> (R : Type), Eq KExpr lhs rhs
    /// -> R`, and this kernel is non-cumulative, so a `Prop` conclusion cannot
    /// be passed where `R : Type` is expected. Their binders also come BEFORE
    /// `R`, not after — read off the generator in
    /// `expr_model_discrimination_let.rs` rather than guessed, after the first
    /// version got both wrong.
    pub(super) fn whnf_step_let_inv_src() -> String {
        let lt = "(KExpr.let_ A a b)";
        // The convoy carries BOTH equations: the recursor is applied at fixed
        // indices, so inside an arm `x` and `y` are that ARM's indices and the
        // equations are what tie them back to the ones being inverted.
        let motive = format!(
            "(fun (x : KExpr) (y : KExpr) (_h : beta_reduces x y) => \
             Eq KExpr x {lt} -> Eq KExpr y e2 -> C)"
        );
        format!(
            "def whnf_step_let_inv (A : KExpr) (a : KExpr) (b : KExpr) (e2 : KExpr) (C : Type) \
             (h : whnf_step {lt} e2) \
             (kz : Eq KExpr e2 (instantiate b a) -> C) \
             (kty : forall (A2 : KExpr), beta_reduces A A2 -> \
             Eq KExpr e2 (KExpr.let_ A2 a b) -> C) \
             (kval : forall (a2 : KExpr), beta_reduces a a2 -> \
             Eq KExpr e2 (KExpr.let_ A a2 b) -> C) \
             (kbody : forall (b2 : KExpr), beta_reduces b b2 -> \
             Eq KExpr e2 (KExpr.let_ A a b2) -> C) \
             (kiota : iota_reduces {lt} e2 -> C) \
             (kdelta : delta_reduces {lt} e2 -> C) : C := \
             whnf_step.rec {lt} e2 (fun (_hs : whnf_step {lt} e2) => C) \
             (fun (hb : beta_reduces {lt} e2) => \
             beta_reduces.rec {motive} \
             {a_beta} {a_app_left} {a_app_right} {a_lam_ty} {a_lam_body} \
             {a_pi_dom} {a_pi_cod} {a_fa_dom} {a_fa_cod} {a_zeta} \
             {a_let_ty} {a_let_val} {a_let_body} {a_iota} {a_proj} \
             {lt} e2 hb (Eq.refl KExpr {lt}) (Eq.refl KExpr e2)) \
             (fun (hd : delta_reduces {lt} e2) => kdelta hd) \
             h",
            // --- the ten refuted arms: left index is not a `let_` ---
            a_beta = format_args!(
                "(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) \
                 (hx : Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) {lt}) \
                 (_hy : Eq KExpr (instantiate body arg) e2) => \
                 let_ne_app A a b (KExpr.lam A0 body) arg C \
                 (Eq.symm KExpr (KExpr.app (KExpr.lam A0 body) arg) {lt} hx))"
            ),
            a_app_left = format_args!(
                "(fun (f : KExpr) (f2 : KExpr) (aa : KExpr) (_hs : beta_reduces f f2) \
                 (_ih : Eq KExpr f {lt} -> Eq KExpr f2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.app f aa) {lt}) \
                 (_hy : Eq KExpr (KExpr.app f2 aa) e2) => \
                 let_ne_app A a b f aa C (Eq.symm KExpr (KExpr.app f aa) {lt} hx))"
            ),
            a_app_right = format_args!(
                "(fun (f : KExpr) (aa : KExpr) (a2 : KExpr) (_hs : beta_reduces aa a2) \
                 (_ih : Eq KExpr aa {lt} -> Eq KExpr a2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.app f aa) {lt}) \
                 (_hy : Eq KExpr (KExpr.app f a2) e2) => \
                 let_ne_app A a b f aa C (Eq.symm KExpr (KExpr.app f aa) {lt} hx))"
            ),
            a_lam_ty = format_args!(
                "(fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hs : beta_reduces ty ty2) \
                 (_ih : Eq KExpr ty {lt} -> Eq KExpr ty2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.lam ty body) {lt}) \
                 (_hy : Eq KExpr (KExpr.lam ty2 body) e2) => \
                 let_ne_lam A a b ty body C (Eq.symm KExpr (KExpr.lam ty body) {lt} hx))"
            ),
            a_lam_body = format_args!(
                "(fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) \
                 (_ih : Eq KExpr body {lt} -> Eq KExpr body2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.lam ty body) {lt}) \
                 (_hy : Eq KExpr (KExpr.lam ty body2) e2) => \
                 let_ne_lam A a b ty body C (Eq.symm KExpr (KExpr.lam ty body) {lt} hx))"
            ),
            a_pi_dom = format_args!(
                "(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hs : beta_reduces dom dom2) \
                 (_ih : Eq KExpr dom {lt} -> Eq KExpr dom2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.pi dom body) {lt}) \
                 (_hy : Eq KExpr (KExpr.pi dom2 body) e2) => \
                 let_ne_pi A a b dom body C (Eq.symm KExpr (KExpr.pi dom body) {lt} hx))"
            ),
            a_pi_cod = format_args!(
                "(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) \
                 (_ih : Eq KExpr body {lt} -> Eq KExpr body2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.pi dom body) {lt}) \
                 (_hy : Eq KExpr (KExpr.pi dom body2) e2) => \
                 let_ne_pi A a b dom body C (Eq.symm KExpr (KExpr.pi dom body) {lt} hx))"
            ),
            a_fa_dom = format_args!(
                "(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hs : beta_reduces dom dom2) \
                 (_ih : Eq KExpr dom {lt} -> Eq KExpr dom2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.forall_ dom body) {lt}) \
                 (_hy : Eq KExpr (KExpr.forall_ dom2 body) e2) => \
                 let_ne_pi A a b dom body C \
                 (Eq.symm KExpr (KExpr.forall_ dom body) {lt} hx))"
            ),
            a_fa_cod = format_args!(
                "(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) \
                 (_ih : Eq KExpr body {lt} -> Eq KExpr body2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.forall_ dom body) {lt}) \
                 (_hy : Eq KExpr (KExpr.forall_ dom body2) e2) => \
                 let_ne_pi A a b dom body C \
                 (Eq.symm KExpr (KExpr.forall_ dom body) {lt} hx))"
            ),
            a_proj = format_args!(
                "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub2 : KExpr) \
                 (_hs : beta_reduces sub sub2) \
                 (_ih : Eq KExpr sub {lt} -> Eq KExpr sub2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.proj ps pidx sub) {lt}) \
                 (_hy : Eq KExpr (KExpr.proj ps pidx sub2) e2) => \
                 let_ne_proj A a b ps pidx sub C \
                 (Eq.symm KExpr (KExpr.proj ps pidx sub) {lt} hx))"
            ),
            // --- the four real arms: rebuild through let_ injectivity ---
            a_zeta = format_args!(
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) \
                 (hx : Eq KExpr (KExpr.let_ ty val body) {lt}) \
                 (hy : Eq KExpr (instantiate body val) e2) => \
                 kz (Eq.substType KExpr \
                 (fun (z : KExpr) => Eq KExpr e2 (instantiate z a)) body b \
                 (let_inj_thd ty val body A a b hx) \
                 (Eq.substType KExpr \
                 (fun (w : KExpr) => Eq KExpr e2 (instantiate body w)) val a \
                 (let_inj_snd ty val body A a b hx) \
                 (Eq.symm KExpr (instantiate body val) e2 hy))))"
            ),
            a_let_ty = format_args!(
                "(fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) \
                 (hs : beta_reduces ty ty2) \
                 (_ih : Eq KExpr ty {lt} -> Eq KExpr ty2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.let_ ty val body) {lt}) \
                 (hy : Eq KExpr (KExpr.let_ ty2 val body) e2) => \
                 kty ty2 (Eq.substType KExpr (fun (z : KExpr) => beta_reduces z ty2) \
                 ty A (let_inj_fst ty val body A a b hx) hs) \
                 (Eq.substType KExpr \
                 (fun (z : KExpr) => Eq KExpr e2 (KExpr.let_ ty2 a z)) body b \
                 (let_inj_thd ty val body A a b hx) \
                 (Eq.substType KExpr \
                 (fun (w : KExpr) => Eq KExpr e2 (KExpr.let_ ty2 w body)) val a \
                 (let_inj_snd ty val body A a b hx) \
                 (Eq.symm KExpr (KExpr.let_ ty2 val body) e2 hy))))"
            ),
            a_let_val = format_args!(
                "(fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) \
                 (hs : beta_reduces val val2) \
                 (_ih : Eq KExpr val {lt} -> Eq KExpr val2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.let_ ty val body) {lt}) \
                 (hy : Eq KExpr (KExpr.let_ ty val2 body) e2) => \
                 kval val2 (Eq.substType KExpr (fun (z : KExpr) => beta_reduces z val2) \
                 val a (let_inj_snd ty val body A a b hx) hs) \
                 (Eq.substType KExpr \
                 (fun (z : KExpr) => Eq KExpr e2 (KExpr.let_ A val2 z)) body b \
                 (let_inj_thd ty val body A a b hx) \
                 (Eq.substType KExpr \
                 (fun (w : KExpr) => Eq KExpr e2 (KExpr.let_ w val2 body)) ty A \
                 (let_inj_fst ty val body A a b hx) \
                 (Eq.symm KExpr (KExpr.let_ ty val2 body) e2 hy))))"
            ),
            a_let_body = format_args!(
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) \
                 (hs : beta_reduces body body2) \
                 (_ih : Eq KExpr body {lt} -> Eq KExpr body2 e2 -> C) \
                 (hx : Eq KExpr (KExpr.let_ ty val body) {lt}) \
                 (hy : Eq KExpr (KExpr.let_ ty val body2) e2) => \
                 kbody body2 (Eq.substType KExpr (fun (z : KExpr) => beta_reduces z body2) \
                 body b (let_inj_thd ty val body A a b hx) hs) \
                 (Eq.substType KExpr \
                 (fun (z : KExpr) => Eq KExpr e2 (KExpr.let_ A z body2)) val a \
                 (let_inj_snd ty val body A a b hx) \
                 (Eq.substType KExpr \
                 (fun (w : KExpr) => Eq KExpr e2 (KExpr.let_ w val body2)) ty A \
                 (let_inj_fst ty val body A a b hx) \
                 (Eq.symm KExpr (KExpr.let_ ty val body2) e2 hy))))"
            ),
            // --- the two carried arms: variable left index ---
            a_iota = format_args!(
                "(fun (x : KExpr) (y : KExpr) (hir : iota_reduces x y) \
                 (hx : Eq KExpr x {lt}) (hy : Eq KExpr y e2) => \
                 kiota (Eq.substType KExpr (fun (z : KExpr) => iota_reduces {lt} z) \
                 y e2 hy (Eq.substType KExpr (fun (z : KExpr) => iota_reduces z y) \
                 x {lt} hx hir)))"
            ),
        )
    }

    /// Accessibility is closed under stepping — `whnf_acc`'s own inversion.
    ///
    /// The constructor stores exactly the function being asked for, so this is
    /// one `whnf_acc.rec` with the motive returning that function. It is `cr2`
    /// of the `CandModel` telescope at a type-blind candidate, which the probe
    /// beside this module already showed holds; registered here as a real
    /// lemma because the `redLet` induction needs it outside a `cfg(test)`
    /// probe.
    pub(super) fn whnf_acc_step_src() -> String {
        "def whnf_acc_step (e : KExpr) (e2 : KExpr) (h : whnf_acc e) \
         (s : whnf_step e e2) : whnf_acc e2 := \
         whnf_acc.rec \
         (fun (x : KExpr) (_hx : whnf_acc x) => \
         forall (y : KExpr), whnf_step x y -> whnf_acc y) \
         (fun (x : KExpr) \
         (f : forall (y : KExpr), whnf_step x y -> whnf_acc y) \
         (_ih : forall (y : KExpr) (_s : whnf_step x y), \
         forall (z : KExpr), whnf_step y z -> whnf_acc z) => f) \
         e h e2 s"
            .to_string()
    }

    /// A reduction of `b` induces one of `instantiate b x` — item (1)
    /// specialised from `psubst` to `instantiate`.
    ///
    /// `instantiate b x` IS `psubst (scons x idsubst) b` by
    /// `instantiate_eq_psubst`, so this is `beta_reduces_psubst_congr` at
    /// `s := scons x idsubst` with that equation transported across both sides.
    /// The `redLet` induction needs exactly this: when `b` steps to `b2` the
    /// hypothesis `forall x, whnf_acc x -> whnf_acc (instantiate b x)` has to be
    /// re-established at `b2`, and this is what moves it.
    pub(super) fn beta_reduces_instantiate_congr_src() -> String {
        "def beta_reduces_instantiate_congr \
         (hiota : forall (p : KExpr) (q : KExpr) (t : Nat -> KExpr), \
         iota_reduces p q -> beta_reduces (psubst t p) (psubst t q)) \
         (b : KExpr) (b2 : KExpr) (hs : beta_reduces b b2) (x : KExpr) : \
         beta_reduces (instantiate b x) (instantiate b2 x) := \
         Eq.substType KExpr \
         (fun (z : KExpr) => beta_reduces (instantiate b x) z) \
         (psubst (scons x idsubst) b2) (instantiate b2 x) \
         (Eq.symm KExpr (instantiate b2 x) (psubst (scons x idsubst) b2) \
         (instantiate_eq_psubst b2 x)) \
         (Eq.substType KExpr \
         (fun (z : KExpr) => beta_reduces z (psubst (scons x idsubst) b2)) \
         (psubst (scons x idsubst) b) (instantiate b x) \
         (Eq.symm KExpr (instantiate b x) (psubst (scons x idsubst) b) \
         (instantiate_eq_psubst b x)) \
         (beta_reduces_psubst_congr hiota b b2 hs (scons x idsubst)))"
            .to_string()
    }

    /// The `redLet` hypothesis, moved from `b` to a reduct `b2`.
    ///
    /// Move a pointwise `instantiate` hypothesis along a step of its BODY.
    ///
    /// ```text
    /// beta_reduces b b2 -> (forall x, whnf_acc x -> whnf_acc (instantiate b x))
    ///   -> forall x, whnf_acc x -> whnf_acc (instantiate b2 x)
    /// ```
    ///
    /// Both weak-head expansion laws are handed `forall x, Red A x -> Red (inst
    /// B x) (inst b x)` and both have an induction that steps `b` to `b2` and
    /// owes the same at `b2` — ζ through `let_body`, β through `lam_body`. This
    /// moves it: `instantiate b x` steps to `instantiate b2 x`, and
    /// accessibility is closed under stepping.
    ///
    /// It was called `redlet_hyp_step` and lived in the `cfg(test)` probe set,
    /// which was wrong on both counts: there is no candidate in its statement,
    /// and the ζ law is not the only caller.
    pub(super) fn instantiate_hyp_step_src() -> String {
        "def instantiate_hyp_step \
         (hiota : forall (p : KExpr) (q : KExpr) (t : Nat -> KExpr), \
         iota_reduces p q -> beta_reduces (psubst t p) (psubst t q)) \
         (b : KExpr) (b2 : KExpr) (hs : beta_reduces b b2) \
         (hyp : forall (x : KExpr), whnf_acc x -> whnf_acc (instantiate b x)) : \
         forall (x : KExpr), whnf_acc x -> whnf_acc (instantiate b2 x) := \
         fun (x : KExpr) (hx : whnf_acc x) => \
         whnf_acc_step (instantiate b x) (instantiate b2 x) (hyp x hx) \
         (whnf_step.beta (instantiate b x) (instantiate b2 x) \
         (beta_reduces_instantiate_congr hiota b b2 hs x))"
            .to_string()
    }

    /// **ITEM (3)** — `redLet` holds at the type-blind candidate.
    ///
    /// ```text
    /// whnf_acc A -> whnf_acc a -> whnf_acc b
    ///   -> (forall x, whnf_acc x -> whnf_acc (instantiate b x))
    ///   -> whnf_acc (let_ A a b)
    /// ```
    ///
    /// This is `CandModel`'s `redLet` field with `Red T e := whnf_acc e`, the
    /// candidate that discards the type index. Certificate §2a records `redLet`
    /// as "proved not dischargeable as stated", by an argument about an
    /// ARBITRARY candidate family (R1's `zeta_expansion_not_generic` exhibits an
    /// `IsCandSet` containing a let-contractum while excluding its redex). If
    /// this holds, that result is about a ROUTE and not about the field being
    /// unsatisfiable — which is the distinction the whole inhabitation question
    /// turns on.
    ///
    /// **A TRIPLE accessibility induction**, and it must be triple because
    /// `whnf_step` reduces UNDER BINDERS: `let_ty`, `let_val` and `let_body`
    /// are all steps, so each of `A`, `a` and `b` can move and each needs its
    /// own well-founded recursion. Under weak-head reduction only ζ would fire
    /// and this would be one line — the under-binder congruence IS the
    /// difficulty, exactly as the design note says.
    ///
    /// The `let_body` case is why item (2) exists: stepping `b` to `b2` obliges
    /// the hypothesis at `b2`, which `instantiate_hyp_step` supplies.
    #[cfg(test)]
    pub(super) fn redlet_blind_src() -> String {
        // The motive at each level, innermost first.
        let hyp =
            |bb: &str| format!("forall (x : KExpr), whnf_acc x -> whnf_acc (instantiate {bb} x)");
        let m_b = format!(
            "(fun (bb : KExpr) (_h : whnf_acc bb) => ({}) -> whnf_acc (KExpr.let_ AA aa bb))",
            hyp("bb")
        );
        let m_a = format!(
            "(fun (aa : KExpr) (_h : whnf_acc aa) => \
             forall (bb : KExpr), whnf_acc bb -> ({}) -> whnf_acc (KExpr.let_ AA aa bb))",
            hyp("bb")
        );
        let m_ty = format!(
            "(fun (AA : KExpr) (_h : whnf_acc AA) => \
             forall (aa : KExpr), whnf_acc aa -> forall (bb : KExpr), whnf_acc bb -> \
             ({}) -> whnf_acc (KExpr.let_ AA aa bb))",
            hyp("bb")
        );
        format!(
            "def redlet_blind \
             (hiota : forall (p : KExpr) (q : KExpr) (t : Nat -> KExpr), \
             iota_reduces p q -> beta_reduces (psubst t p) (psubst t q)) \
             (kio : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
             iota_reduces (KExpr.let_ p q r) z -> whnf_acc z) \
             (kde : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
             delta_reduces (KExpr.let_ p q r) z -> whnf_acc z) \
             (A : KExpr) (hA : whnf_acc A) : \
             forall (aa : KExpr), whnf_acc aa -> forall (bb : KExpr), whnf_acc bb -> \
             ({hyp_bb}) -> whnf_acc (KExpr.let_ A aa bb) := \
             whnf_acc.rec {m_ty} \
             (fun (AA : KExpr) \
             (fA : forall (A2 : KExpr), whnf_step AA A2 -> whnf_acc A2) \
             (ihA : forall (A2 : KExpr) (_s : whnf_step AA A2), \
             forall (aa : KExpr), whnf_acc aa -> forall (bb : KExpr), whnf_acc bb -> \
             ({hyp_bb}) -> whnf_acc (KExpr.let_ A2 aa bb)) \
             (a0 : KExpr) (ha0 : whnf_acc a0) => \
             whnf_acc.rec {m_a} \
             (fun (aa : KExpr) \
             (fa : forall (a2 : KExpr), whnf_step aa a2 -> whnf_acc a2) \
             (iha : forall (a2 : KExpr) (_s : whnf_step aa a2), \
             forall (bb : KExpr), whnf_acc bb -> ({hyp_bb}) -> \
             whnf_acc (KExpr.let_ AA a2 bb)) \
             (b0 : KExpr) (hb0 : whnf_acc b0) => \
             whnf_acc.rec {m_b} \
             (fun (bb : KExpr) \
             (fb : forall (b2 : KExpr), whnf_step bb b2 -> whnf_acc b2) \
             (ihb : forall (b2 : KExpr) (_s : whnf_step bb b2), \
             ({hyp_b2}) -> whnf_acc (KExpr.let_ AA aa b2)) \
             (hyp : {hyp_bb}) => \
             whnf_acc.intro (KExpr.let_ AA aa bb) \
             (fun (e2 : KExpr) (st : whnf_step (KExpr.let_ AA aa bb) e2) => \
             whnf_step_let_inv AA aa bb e2 (whnf_acc e2) st \
             (fun (hz : Eq KExpr e2 (instantiate bb aa)) => \
             Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) \
             (instantiate bb aa) e2 \
             (Eq.symm KExpr e2 (instantiate bb aa) hz) \
             (hyp aa (whnf_acc.intro aa fa))) \
             (fun (A2 : KExpr) (hs : beta_reduces AA A2) \
             (he : Eq KExpr e2 (KExpr.let_ A2 aa bb)) => \
             Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) \
             (KExpr.let_ A2 aa bb) e2 (Eq.symm KExpr e2 (KExpr.let_ A2 aa bb) he) \
             (ihA A2 (whnf_step.beta AA A2 hs) aa (whnf_acc.intro aa fa) \
             bb (whnf_acc.intro bb fb) hyp)) \
             (fun (a2 : KExpr) (hs : beta_reduces aa a2) \
             (he : Eq KExpr e2 (KExpr.let_ AA a2 bb)) => \
             Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) \
             (KExpr.let_ AA a2 bb) e2 (Eq.symm KExpr e2 (KExpr.let_ AA a2 bb) he) \
             (iha a2 (whnf_step.beta aa a2 hs) bb (whnf_acc.intro bb fb) hyp)) \
             (fun (b2 : KExpr) (hs : beta_reduces bb b2) \
             (he : Eq KExpr e2 (KExpr.let_ AA aa b2)) => \
             Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) \
             (KExpr.let_ AA aa b2) e2 (Eq.symm KExpr e2 (KExpr.let_ AA aa b2) he) \
             (ihb b2 (whnf_step.beta bb b2 hs) \
             (instantiate_hyp_step hiota bb b2 hs hyp))) \
             (fun (hir : iota_reduces (KExpr.let_ AA aa bb) e2) => kio AA aa bb e2 hir) \
             (fun (hdr : delta_reduces (KExpr.let_ AA aa bb) e2) => kde AA aa bb e2 hdr))) \
             b0 hb0) \
             a0 ha0) \
             A hA",
            hyp_bb = hyp("bb"),
            hyp_b2 = hyp("b2"),
        )
    }

    /// `whnf_step` congruence in an application's function position.
    ///
    /// `beta_reduces` has `app_left`; `delta_reduces` is carried, as everywhere
    /// in this chain, because whether unfolding a constant commutes with an
    /// application spine is a question about δ and not about `app`.
    pub(super) fn whnf_step_app_left_src() -> String {
        "def whnf_step_app_left \
         (hdapp : forall (p : KExpr) (q : KExpr) (r : KExpr), \
         delta_reduces p q -> whnf_step (KExpr.app p r) (KExpr.app q r)) \
         (f : KExpr) (f2 : KExpr) (aa : KExpr) (s : whnf_step f f2) : \
         whnf_step (KExpr.app f aa) (KExpr.app f2 aa) := \
         whnf_step.rec f f2 \
         (fun (_h : whnf_step f f2) => \
         whnf_step (KExpr.app f aa) (KExpr.app f2 aa)) \
         (fun (hb : beta_reduces f f2) => \
         whnf_step.beta (KExpr.app f aa) (KExpr.app f2 aa) \
         (beta_reduces.app_left f f2 aa hb)) \
         (fun (hd : delta_reduces f f2) => hdapp f f2 aa hd) \
         s"
        .to_string()
    }

    /// An application's function is accessible if the application is.
    ///
    /// The anti-congruence counterpart of [`Self::whnf_acc_psubst_inv`], and the
    /// same shape: accessibility induction on the APPLICATION with the motive
    /// carrying an equation, since `whnf_acc.rec` binds its scrutinee.
    ///
    /// This is the ingredient `pi_intro` wants at a type-blind candidate, where
    /// it reads `(forall a, whnf_acc a -> whnf_acc (app f a)) -> whnf_acc f`:
    /// apply the hypothesis at any accessible argument and strip the spine.
    pub(super) fn whnf_acc_app_fn_src() -> String {
        "def whnf_acc_app_fn \
         (hdapp : forall (p : KExpr) (q : KExpr) (r : KExpr), \
         delta_reduces p q -> whnf_step (KExpr.app p r) (KExpr.app q r)) \
         (y : KExpr) (hy : whnf_acc y) : \
         forall (ff : KExpr) (aa : KExpr), Eq KExpr y (KExpr.app ff aa) -> whnf_acc ff := \
         whnf_acc.rec \
         (fun (z : KExpr) (_hz : whnf_acc z) => \
         forall (ff : KExpr) (aa : KExpr), Eq KExpr z (KExpr.app ff aa) -> whnf_acc ff) \
         (fun (z : KExpr) \
         (fz : forall (z2 : KExpr), whnf_step z z2 -> whnf_acc z2) \
         (ih : forall (z2 : KExpr) (_s : whnf_step z z2), \
         forall (ff : KExpr) (aa : KExpr), Eq KExpr z2 (KExpr.app ff aa) -> whnf_acc ff) \
         (ff : KExpr) (aa : KExpr) (heq : Eq KExpr z (KExpr.app ff aa)) => \
         whnf_acc.intro ff (fun (f2 : KExpr) (st : whnf_step ff f2) => \
         ih (KExpr.app f2 aa) \
         (Eq.substType KExpr \
         (fun (w : KExpr) => whnf_step w (KExpr.app f2 aa)) \
         (KExpr.app ff aa) z (Eq.symm KExpr z (KExpr.app ff aa) heq) \
         (whnf_step_app_left hdapp ff f2 aa st)) \
         f2 aa (Eq.refl KExpr (KExpr.app f2 aa)))) \
         y hy"
            .to_string()
    }

    /// `whnf_acc (bvar i)` — a bound variable is strongly normalizing.
    ///
    /// One line over `no_whnf_step_bvar`, and it exists for a reason worth
    /// naming: several type-blind probes need SOME accessible term to
    /// instantiate a universally quantified hypothesis at, and taking one as a
    /// PARAMETER would weaken the result from a law to a conditional. A `bvar`
    /// is the cheapest inhabitant of `whnf_acc` there is — it admits no step at
    /// all, so its accessibility is the vacuous `intro`.
    pub(super) fn whnf_acc_bvar_src() -> String {
        "def whnf_acc_bvar (i : Nat) : whnf_acc (KExpr.bvar i) := \
         whnf_acc.intro (KExpr.bvar i) \
         (fun (e2 : KExpr) (st : whnf_step (KExpr.bvar i) e2) => \
         no_whnf_step_bvar i e2 (whnf_acc e2) st)"
            .to_string()
    }

    /// `whnf_acc (instantiate b a) -> whnf_acc b`.
    ///
    /// `whnf_acc_psubst_inv` at the singleton substitution, transported through
    /// `instantiate_eq_psubst`. Stated separately because `instantiate` is the
    /// spelling every binder rule uses and rewriting at the call site each time
    /// is how the `scons a idsubst` form leaks into statements that are not
    /// about substitutions.
    pub(super) fn whnf_acc_instantiate_inv_src() -> String {
        "def whnf_acc_instantiate_inv \
         (hiota : forall (x : KExpr) (y : KExpr) (t : Nat -> KExpr), \
         iota_reduces x y -> beta_reduces (psubst t x) (psubst t y)) \
         (hdelta : forall (x : KExpr) (y : KExpr) (t : Nat -> KExpr), \
         delta_reduces x y -> whnf_step (psubst t x) (psubst t y)) \
         (bb : KExpr) (aa : KExpr) (h : whnf_acc (instantiate bb aa)) : whnf_acc bb := \
         whnf_acc_psubst_inv hiota hdelta (instantiate bb aa) h bb (scons aa idsubst) \
         (instantiate_eq_psubst bb aa)"
            .to_string()
    }

    /// PROBE. `CandModel.pi_intro` at the type-blind candidate, EXACTLY as the
    /// field reads:
    ///
    /// ```text
    /// (forall a, whnf_acc a -> whnf_acc (app f a)) -> whnf_acc f
    /// ```
    ///
    /// It holds, and it is one line — instantiate the hypothesis at `bvar 0`
    /// and strip the spine with `whnf_acc_app_fn`. The `A` and `B` of the real
    /// field are absent because the candidate discards the type index, which is
    /// the whole point: `pi_intro` carries NO type content at all.
    ///
    /// Read beside `pi_elim`, which is FALSE at this same candidate, this is
    /// the sharp statement of where the Pi pair's difficulty lives. The
    /// introduction rule is free; the elimination rule is the entire
    /// obstruction. That asymmetry is exactly what a logical relation exists to
    /// pay for, and it says the type-awareness `CandModel` needs is needed at
    /// ONE field.
    #[cfg(test)]
    pub(super) fn pi_intro_blind_src() -> String {
        "def pi_intro_blind \
         (hdapp : forall (p : KExpr) (q : KExpr) (r : KExpr), \
         delta_reduces p q -> whnf_step (KExpr.app p r) (KExpr.app q r)) \
         (ff : KExpr) \
         (hpt : forall (aa : KExpr), whnf_acc aa -> whnf_acc (KExpr.app ff aa)) : \
         whnf_acc ff := \
         whnf_acc_app_fn hdapp (KExpr.app ff (KExpr.bvar Nat.zero)) \
         (hpt (KExpr.bvar Nat.zero) (whnf_acc_bvar Nat.zero)) \
         ff (KExpr.bvar Nat.zero) \
         (Eq.refl KExpr (KExpr.app ff (KExpr.bvar Nat.zero)))"
            .to_string()
    }

    /// PROBE. `CandModel.redLet` at the type-blind candidate, EXACTLY as the
    /// field reads — no extra hypothesis:
    ///
    /// ```text
    /// whnf_acc A
    ///   -> (forall a, whnf_acc a -> whnf_acc (instantiate b a))
    ///   -> forall a, whnf_acc a -> whnf_acc (let_ A a b)
    /// ```
    ///
    /// `redlet_blind` takes `whnf_acc b` as a THIRD hypothesis, which the real
    /// field does not supply, so on its own it was a near miss and this closes
    /// the gap: `whnf_acc b` is DERIVABLE from the pointwise hypothesis, by
    /// instantiating it at `bvar 0` and inverting the substitution. Until that
    /// was checked it was not obvious the field held at all — the pointwise
    /// hypothesis says nothing about `b` directly, only about its instances.
    #[cfg(test)]
    pub(super) fn redlet_blind_exact_src() -> String {
        "def redlet_blind_exact \
         (hiota : forall (p : KExpr) (q : KExpr) (t : Nat -> KExpr), \
         iota_reduces p q -> beta_reduces (psubst t p) (psubst t q)) \
         (hdelta : forall (p : KExpr) (q : KExpr) (t : Nat -> KExpr), \
         delta_reduces p q -> whnf_step (psubst t p) (psubst t q)) \
         (kio : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
         iota_reduces (KExpr.let_ p q r) z -> whnf_acc z) \
         (kde : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
         delta_reduces (KExpr.let_ p q r) z -> whnf_acc z) \
         (A : KExpr) (bb : KExpr) (hA : whnf_acc A) \
         (hpt : forall (x : KExpr), whnf_acc x -> whnf_acc (instantiate bb x)) \
         (aa : KExpr) (haa : whnf_acc aa) : whnf_acc (KExpr.let_ A aa bb) := \
         redlet_blind hiota kio kde A hA aa haa bb \
         (whnf_acc_instantiate_inv hiota hdelta bb (KExpr.bvar Nat.zero) \
         (hpt (KExpr.bvar Nat.zero) (whnf_acc_bvar Nat.zero))) \
         hpt"
        .to_string()
    }

    /// The GENERAL lemmas, in dependency order — facts about substitution and
    /// accessibility, tied to no candidate. These are wired.
    pub(super) fn beta_subst_congr_sources() -> Vec<(String, String)> {
        vec![
            (
                "beta_reduces_psubst_congr".to_string(),
                Self::beta_subst_congr_src(),
            ),
            (
                "whnf_step_psubst_congr".to_string(),
                Self::whnf_step_subst_congr_src(),
            ),
            (
                "whnf_acc_psubst_inv".to_string(),
                Self::whnf_acc_psubst_inv_src(),
            ),
            (
                "whnf_step_let_inv".to_string(),
                Self::whnf_step_let_inv_src(),
            ),
            ("whnf_acc_step".to_string(), Self::whnf_acc_step_src()),
            (
                "beta_reduces_instantiate_congr".to_string(),
                Self::beta_reduces_instantiate_congr_src(),
            ),
            (
                "whnf_step_app_left".to_string(),
                Self::whnf_step_app_left_src(),
            ),
            ("whnf_acc_app_fn".to_string(), Self::whnf_acc_app_fn_src()),
            ("whnf_acc_bvar".to_string(), Self::whnf_acc_bvar_src()),
            (
                "whnf_acc_instantiate_inv".to_string(),
                Self::whnf_acc_instantiate_inv_src(),
            ),
            (
                "instantiate_hyp_step".to_string(),
                Self::instantiate_hyp_step_src(),
            ),
        ]
    }

    /// The type-blind CANDIDATE probes. NOT wired and not to be: `Red T e :=
    /// whnf_acc e` is not a candidate model, and registering `redlet_blind` as
    /// a fact about `CandModel` would be a false claim. Scratch-only.
    #[cfg(test)]
    pub(super) fn redlet_blind_probe_sources() -> Vec<(String, String)> {
        vec![
            ("redlet_blind".to_string(), Self::redlet_blind_src()),
            (
                "redlet_blind_exact".to_string(),
                Self::redlet_blind_exact_src(),
            ),
            ("pi_intro_blind".to_string(), Self::pi_intro_blind_src()),
        ]
    }

    /// Registered from `bundles.rs` after `add_dependent_sn_richmodel`, which
    /// is what mints the `psubst` tower these consume — `psubst_instantiate`,
    /// `instantiate_eq_psubst`, `up`, `scons`, `idsubst`. The other
    /// dependencies are earlier still: `beta_reduces` / `whnf_step` /
    /// `whnf_acc` from `add_whnf_reduction`, and `let_ne_*` / `let_inj_*` from
    /// `add_expr_model_let_discrimination`.
    ///
    /// Scratch-elaborated before being wired, per the recipe, and wired because
    /// scratch proves the TERMS while only this proves the ORDER.
    pub(super) fn add_beta_subst_congr(&mut self) -> Result<(), SpecError> {
        for (_n, src) in Self::beta_subst_congr_sources() {
            self.add_recursive_def(&src, "step substitutivity")?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "beta_subst_congr_tests.rs"]
mod tests;
