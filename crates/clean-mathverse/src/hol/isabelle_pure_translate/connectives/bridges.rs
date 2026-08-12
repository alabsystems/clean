// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Connective bridge proofs and `Eq`/`True` helpers for the Isabelle Pure
//! translator (`eq_prop`, `true_enc_and_proof`, `all_def_bridge_proof`,
//! `true_or_false_proof`). Moved verbatim from the original single-file
//! `connectives` module; behaviour is byte-identical.

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

use super::super::*;

/// `@Eq.{1} Prop a b`, the embedded HOL equation over `bool`/`Prop`.
pub(crate) fn eq_prop(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [Expr::prop(), a, b],
    )
}

/// `True_enc = ((λx:Prop. x) = (λx:Prop. x))` and its `Eq.refl` proof. The
/// connective encoding of `HOL.True`; its inhabitant is `Eq.refl.{1} (Prop→Prop)
/// (λx.x)`. Returned as `(encoding, refl_proof)`.
pub(crate) fn true_enc_and_proof() -> (Expr, Expr) {
    let id_lam = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let prop_prop = Expr::arrow(Expr::prop(), Expr::prop());
    let enc = Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [prop_prop.clone(), id_lam.clone(), id_lam.clone()],
    );
    let refl = Expr::apps(
        Expr::const_str_levels("Eq.refl", vec![obj_level()]),
        [prop_prop, id_lam],
    );
    (enc, refl)
}

/// Build the closed clean proof of HOL's `All_def` core equation
///
/// ```text
/// @Eq Prop (∀x:α. p x) (@Eq (α→Prop) p (λx:α. True_enc))
/// ```
///
/// — i.e. `(∀x. p x) ↔ (p = (λx. True))` lifted across `propext`. `alpha` is the
/// (object-`Type`) domain and `p : α → Prop` is the predicate; both are arbitrary
/// closed clean terms (typically the theorem's quantified `∀(T:Type)`/`∀(P:α→Prop)`
/// parameters). Built entirely from `propext`/`funext`/`congrFun`/`Eq.{refl,mpr}`,
/// whose transitive closure is `⊆ {propext, Quot.sound}` (foundational). The kernel
/// re-checks the result against the embedded statement, so soundness rests only on
/// those foundational axioms.
///
/// Proof skeleton (`propext_iff a b mp mpr` builds `propext a b (Iff.intro …)`):
///   - `a = ∀x:α. p x`,   `b = @Eq (α→Prop) p (λx. True_enc)`;
///   - `mp : a → b`  via `funext` + pointwise `propext (p x ↔ True_enc)`
///     (forward: `p x` from `h x`; backward: `True_enc` by `Eq.refl`);
///   - `mpr : b → a` via, for each `x`, `congrFun heq x : p x = (λx.True_enc) x`
///     (defeq `p x = True_enc`), then `Eq.mpr (p x) True_enc … True_enc`.
pub(crate) fn all_def_bridge_proof(alpha: &Expr, p: &Expr) -> Expr {
    // Fresh fvar id space for this proof's binders (abstracted away below).
    const FH: u64 = 0xA11D_0001; // h : ∀x. p x
    const FX: u64 = 0xA11D_0002; // x : α
    const FHEQ: u64 = 0xA11D_0003; // heq : p = (λx. True_enc)

    let (true_enc, refl_true) = true_enc_and_proof();
    // β = (fun _:α => Prop) — the constant codomain family for funext/congrFun.
    let beta = Expr::lam(BinderInfo::Default, alpha.clone(), Expr::prop());
    // λx:α. True_enc  (True_enc is closed, so no lift over the new binder).
    let lam_true = Expr::lam(BinderInfo::Default, alpha.clone(), true_enc.clone());
    // a = ∀x:α. p x  (p closed → lift over the fresh binder, apply to bvar 0).
    let forall_px = Expr::pi(
        BinderInfo::Default,
        alpha.clone(),
        Expr::app(p.clone().lift(1), Expr::bvar(0)),
    );
    // b = @Eq (α→Prop) p (λx. True_enc).
    let p_eq_lam_true = Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [
            Expr::arrow(alpha.clone(), Expr::prop()),
            p.clone(),
            lam_true.clone(),
        ],
    );

    // --- mp : (∀x. p x) → (p = λx. True_enc) ---
    let mp = {
        let h = Expr::fvar(FVarId::new(FH));
        // pointwise : fun (x:α) => propext (p x) True_enc (λ_:(p x). refl_true) (λ_:True_enc. h x)
        let pointwise = {
            let x = Expr::fvar(FVarId::new(FX));
            let px = Expr::app(p.clone(), x.clone());
            // p x → True_enc: `fun (_ : p x) => refl_true`
            let fwd = Expr::lam(BinderInfo::Default, px.clone(), refl_true.clone());
            // True_enc → p x: `fun (_ : True_enc) => h x`  (h is the outer binder).
            let bwd = Expr::lam(
                BinderInfo::Default,
                true_enc.clone(),
                Expr::app(h.clone(), x.clone()),
            );
            let peq = propext_iff(px, true_enc.clone(), fwd, bwd);
            Expr::lam(
                BinderInfo::Default,
                alpha.clone(),
                peq.abstract_fvar(FVarId::new(FX)),
            )
        };
        // @funext.{1,1} α (fun _:α => Prop) p (λx. True_enc) pointwise.
        // β = (λ_:α. Prop) : α → Sort 1, so the codomain universe v = 1: the
        // family returns `Prop`, whose own type is `Sort 1`.
        let fe = Expr::apps(
            Expr::const_str_levels("funext", vec![obj_level(), obj_level()]),
            [
                alpha.clone(),
                beta.clone(),
                p.clone(),
                lam_true.clone(),
                pointwise,
            ],
        );
        Expr::lam(
            BinderInfo::Default,
            forall_px.clone(),
            fe.abstract_fvar(FVarId::new(FH)),
        )
    };

    // --- mpr : (p = λx. True_enc) → (∀x. p x) ---
    let mpr = {
        let heq = Expr::fvar(FVarId::new(FHEQ));
        // body under (heq, x): @Eq.mpr.{0} (p x) True_enc (congrFun heq x) refl_true.
        let x = Expr::fvar(FVarId::new(FX));
        let px = Expr::app(p.clone(), x.clone());
        // @congrFun.{1,1} α (fun _:α => Prop) p (λx. True_enc) heq x
        //   : @Eq Prop (p x) ((λx. True_enc) x)   [(λx.True_enc) x ≡ True_enc by β]
        // β's codomain universe v = 1 (same reasoning as funext above).
        let cf = Expr::apps(
            Expr::const_str_levels("congrFun", vec![obj_level(), obj_level()]),
            [
                alpha.clone(),
                beta.clone(),
                p.clone(),
                lam_true.clone(),
                heq.clone(),
                x.clone(),
            ],
        );
        // @Eq.mpr.{0} (p x) True_enc cf refl_true : p x.
        let mpr_body = Expr::apps(
            Expr::const_str_levels("Eq.mpr", vec![Level::zero()]),
            [px, true_enc.clone(), cf, refl_true.clone()],
        );
        // fun (x:α) => mpr_body
        let x_lam = Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            mpr_body.abstract_fvar(FVarId::new(FX)),
        );
        // fun (heq : p = λx. True_enc) => x_lam
        Expr::lam(
            BinderInfo::Default,
            p_eq_lam_true.clone(),
            x_lam.abstract_fvar(FVarId::new(FHEQ)),
        )
    };

    propext_iff(forall_px, p_eq_lam_true, mp, mpr)
}

/// Build the clean proof of `HOL.True_or_False` instantiated at `p : Prop`:
/// the disj-encoded `∀C. ((P = True_enc) → C) → ((P = False_enc) → C) → C`,
/// discharged by `Classical.em P` (excluded middle) + `propext`. `true_enc`
/// and `false_enc` are the HOL connective encodings of `True`/`False`.
///
/// Built entirely with fresh `FVarId`s and `abstract_fvar` (no manual de
/// Bruijn). The kernel re-checks the result against the embedded statement, so
/// soundness rests on `propext` + `Classical.em` (whose closure is foundational).
pub(crate) fn true_or_false_proof(p: &Expr, true_enc: &Expr, false_enc: &Expr) -> Expr {
    // Fresh fvar id space for this proof's binders (abstracted away below).
    const FC: u64 = 0x70F0_0001; // C : Prop
    const FF: u64 = 0x70F0_0002; // f : (P = True_enc) → C
    const FG: u64 = 0x70F0_0003; // g : (P = False_enc) → C
    const FHP: u64 = 0x70F0_0004; // hp : P
    const FHNP: u64 = 0x70F0_0005; // hnp : P → False
    const FHF: u64 = 0x70F0_0006; // hf : False_enc
    let c = Expr::fvar(FVarId::new(FC));
    let f = Expr::fvar(FVarId::new(FF));
    let g = Expr::fvar(FVarId::new(FG));

    let p_eq_true = eq_prop(p.clone(), true_enc.clone());
    let p_eq_false = eq_prop(p.clone(), false_enc.clone());
    let not_p = Expr::arrow(p.clone(), Expr::const_str("False"));

    // Positive branch: `fun (hp : P) => f (propext P True_enc (fun _:P => Eq.refl..(λx.x)) (fun _:True_enc => hp))`.
    let id_lam = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let prop_prop = Expr::arrow(Expr::prop(), Expr::prop());
    let refl_true = Expr::apps(
        Expr::const_str_levels("Eq.refl", vec![obj_level()]),
        [prop_prop, id_lam],
    );
    let pos_branch = {
        let hp = Expr::fvar(FVarId::new(FHP));
        // p → True_enc: `fun (_ : P) => refl_true`
        let hpt = Expr::lam(BinderInfo::Default, p.clone(), refl_true);
        // True_enc → p: `fun (_ : True_enc) => hp`, where `hp` is the OUTER
        // branch binder (kept free here; abstracted once at the branch level so
        // it does not capture the `_ : True_enc` argument).
        let htp = Expr::lam(BinderInfo::Default, true_enc.clone(), hp.clone());
        let peq = propext_iff(p.clone(), true_enc.clone(), hpt, htp);
        let body = Expr::app(f.clone(), peq);
        Expr::lam(
            BinderInfo::Default,
            p.clone(),
            body.abstract_fvar(FVarId::new(FHP)),
        )
    };

    // Negative branch: `fun (hnp : P → False) => g (propext P False_enc (fun hp:P => False.elim (hnp hp)) (fun hf:False_enc => hf P))`.
    let neg_branch = {
        let hnp = Expr::fvar(FVarId::new(FHNP));
        let hf = Expr::fvar(FVarId::new(FHF));
        // p → False_enc: `fun (hp : P) => @False.elim.{0} False_enc (hnp hp)`
        let hpf = {
            let hp = Expr::fvar(FVarId::new(FHP));
            let absurd = Expr::app(hnp.clone(), hp);
            let fe = Expr::apps(
                Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                [false_enc.clone(), absurd],
            );
            Expr::lam(
                BinderInfo::Default,
                p.clone(),
                fe.abstract_fvar(FVarId::new(FHP)),
            )
        };
        // False_enc → p: `fun (hf : ∀Q:Prop. Q) => hf P`
        let hfp = {
            let body = Expr::app(hf.clone(), p.clone());
            Expr::lam(
                BinderInfo::Default,
                false_enc.clone(),
                body.abstract_fvar(FVarId::new(FHF)),
            )
        };
        let peq = propext_iff(p.clone(), false_enc.clone(), hpf, hfp);
        let body = Expr::app(g.clone(), peq);
        Expr::lam(
            BinderInfo::Default,
            not_p.clone(),
            body.abstract_fvar(FVarId::new(FHNP)),
        )
    };

    // Case-split: `@Or.rec P (P→False) (fun _ => C) pos_branch neg_branch (Classical.em P)`.
    let em = Expr::app(Expr::const_str("Classical.em"), p.clone());
    let motive = {
        let or_ty = Expr::apps(Expr::const_str("Or"), [p.clone(), not_p.clone()]);
        // `fun (_ : Or P (P→False)) => C` (C closed at this depth).
        Expr::lam(BinderInfo::Default, or_ty, c.clone())
    };
    let case = Expr::apps(
        Expr::const_str("Or.rec"),
        [p.clone(), not_p.clone(), motive, pos_branch, neg_branch, em],
    );

    // Wrap in `fun (C:Prop) (f:(P=True_enc)→C) (g:(P=False_enc)→C) => case`.
    let case = case.abstract_fvar(FVarId::new(FG));
    let g_ty = Expr::arrow(p_eq_false, c.clone());
    let g_lam = Expr::lam(BinderInfo::Default, g_ty, case);
    let g_lam = g_lam.abstract_fvar(FVarId::new(FF));
    let f_ty = Expr::arrow(p_eq_true, c.clone());
    let f_lam = Expr::lam(BinderInfo::Default, f_ty, g_lam);
    let f_lam = f_lam.abstract_fvar(FVarId::new(FC));
    Expr::lam(BinderInfo::Default, Expr::prop(), f_lam)
}
