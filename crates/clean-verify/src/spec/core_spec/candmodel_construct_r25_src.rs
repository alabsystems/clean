// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R25 sources — **THE ARROW CANDIDATE**: the non-dependent function type over
//! R17's system, and both the introduction and the elimination rule a Tait
//! fundamental theorem needs at it.
//!
//! See the module doc of [`super::candmodel_construct_r25`] for the argument.

// **This module deliberately imports nothing** — the R12-R24 convention.

/// The lift amount.
const ONE: &str = "(Nat.succ Nat.zero)";
/// The lifted codomain: `B` pushed under one binder.
const LIFTB: &str = "(lift_at B Nat.zero (Nat.succ Nat.zero))";
/// The junk-extended valuation the `pi` clause of `xval` reads its codomain at.
const JR: &str = "(vconsD Sk.ty D (junkD Sk.ty) r)";
/// The codomain's derivation inside that binder.
const HLIFT: &str = "(wkc_lift0 D B Sk.ty hB Sk.ty)";

/// The codomain's interpretation as the `pi` clause actually reads it — lifted,
/// at the junk extension. `r20_xval_lift0` is what identifies it with `B`'s own.
fn xval_lifted() -> String {
    format!("(xval (skcons Sk.ty D) {LIFTB} Sk.ty {HLIFT} {JR})")
}

// ================================================================
// Group A — the type former.
// ================================================================

/// **`r25_arrow`** — the NON-DEPENDENT function type, `A -> B`, spelled in de
/// Bruijn as a `pi` whose codomain is lifted past the binder.
pub(super) fn src_arrow() -> String {
    format!(
        "def r25_arrow (A : KExpr) (B : KExpr) : KExpr := KExpr.pi A (lift_at B Nat.zero {ONE})"
    )
}

/// **`r25_arrowWkc`** — its shape derivation, and the place the shape
/// arithmetic has to work out.
///
/// `WKC.pi` concludes at `piShape sA sB`, and `piShape Sk.ty t` computes to
/// `Sk.ty` — so a `pi` of two TYPES is itself a type. Its codomain premise sits
/// in `skcons (domSk sA) D`, and `domSk Sk.ty` computes to `Sk.ty` — so
/// `wkc_lift0` at `Sk.ty` produces exactly the derivation the constructor
/// wants. Neither of those is arranged here; both are R12's `piShape`/`domSk`
/// computing, and this definition is the first place in the ladder that depends
/// on them lining up.
pub(super) fn src_arrow_wkc() -> String {
    format!("def r25_arrowWkc (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) : WKC D (r25_arrow A B) Sk.ty := WKC.pi D A {LIFTB} Sk.ty Sk.ty hA {HLIFT}")
}

// ================================================================
// Group B — the two rules.
// ================================================================

/// **`r25_red_app` — THE ELIMINATION RULE**, and the `app` case of a Tait
/// fundamental theorem over this lineage.
///
/// A term reducible at `A -> B`, applied to a term reducible at `A`, is
/// reducible at `B`. The proof is short and the reason is worth stating:
/// `xval` at a `pi` of two types denotes `PiSet (xval A) (fun _ => xval B')`
/// where `B'` is the codomain read LIFTED at the junk extension —
/// `mkTyD Sk.ty Sk.ty C` computes to `C` and `vcarD Sk.ty V` computes to `V`,
/// so the membership IS the function-space clause, definitionally. The only
/// work is identifying `B'` with `B`, which is exactly `r20_xval_lift0`.
pub(super) fn ty_red_app() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D) (f : KExpr) (a : KExpr), r24_RedAt D (r25_arrow A B) (r25_arrowWkc D A B hA hB) r f -> r24_RedAt D A hA r a -> r24_RedAt D B hB r (KExpr.app f a)".to_string()
}

pub(super) fn val_red_app() -> String {
    let xl = xval_lifted();
    format!("fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D) (f : KExpr) (a : KExpr) (hf : r24_RedAt D (r25_arrow A B) (r25_arrowWkc D A B hA hB) r f) (ha : r24_RedAt D A hA r a) => Eq.substType (VD Sk.ty) (fun (qv : VD Sk.ty) => qv (KExpr.app f a)) {xl} (xval D B Sk.ty hB r) (r20_xval_lift0 D B Sk.ty hB Sk.ty (junkD Sk.ty) r) (hf a ha)")
}

/// **`r25_red_lam` — THE INTRODUCTION RULE**, and the `lam` case.
///
/// A lambda whose body's contractum is reducible at `B` for every reducible
/// argument — and every `betaStar`-development of the body, which is R1's
/// honest family interface rather than a weakening chosen here — is reducible
/// at `A -> B`.
///
/// This is `r24_red_beta_expand` under the same `r20_xval_lift0` transport as
/// the elimination rule, run the other way. It is the case that needed an
/// ENGINE, and the engine is R1's, available because a β redex is neutral.
pub(super) fn ty_red_lam() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D), GoodEnvD D r -> forall (ann : KExpr), whnf_acc ann -> forall (b : KExpr), whnf_acc b -> (forall (b2 : KExpr), betaStar b b2 -> forall (a2 : KExpr), r24_RedAt D A hA r a2 -> r24_RedAt D B hB r (instantiate b2 a2)) -> r24_RedAt D (r25_arrow A B) (r25_arrowWkc D A B hA hB) r (KExpr.lam ann b)".to_string()
}

pub(super) fn val_red_lam() -> String {
    let xl = xval_lifted();
    let redex = "(KExpr.app (KExpr.lam ann b) a)";
    format!("fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) (ann : KExpr) (hann : whnf_acc ann) (b : KExpr) (hb : whnf_acc b) (hfam : forall (b2 : KExpr), betaStar b b2 -> forall (a2 : KExpr), r24_RedAt D A hA r a2 -> r24_RedAt D B hB r (instantiate b2 a2)) (a : KExpr) (ha : r24_RedAt D A hA r a) => Eq.substType (VD Sk.ty) (fun (qv : VD Sk.ty) => qv {redex}) (xval D B Sk.ty hB r) {xl} (Eq.symm (VD Sk.ty) {xl} (xval D B Sk.ty hB r) (r20_xval_lift0 D B Sk.ty hB Sk.ty (junkD Sk.ty) r)) (r24_red_beta_expand D A B hA hB r hr ann hann b hb hfam a ha)")
}

/// **`r25_red_arrow_is_the_function_space`** — the membership at an arrow type
/// IS the function-space clause, stated so nobody has to re-derive it from
/// `mkTyD`/`vcarD`/`PiSet` computing.
///
/// Both directions are the identity: `r25_red_app` supplies one and the lambda
/// case consumes the other, and this constant records that the unfolding is
/// definitional rather than a lemma. The codomain still reads LIFTED — that is
/// what `r20_xval_lift0` is for and why this statement is about `B'` and not
/// `B`.
pub(super) fn ty_red_arrow_unfolds() -> String {
    let xl = xval_lifted();
    format!("forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D) (t : KExpr), Eq Type (r24_RedAt D (r25_arrow A B) (r25_arrowWkc D A B hA hB) r t) (forall (qa : KExpr), r24_RedAt D A hA r qa -> {xl} (KExpr.app t qa))")
}

pub(super) fn val_red_arrow_unfolds() -> String {
    let xl = xval_lifted();
    format!("fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D) (t : KExpr) => Eq.refl Type (forall (qa : KExpr), r24_RedAt D A hA r qa -> {xl} (KExpr.app t qa))")
}

/// **`r25_red_arrow_members_sn`** — a term reducible at a function type
/// normalizes. R24's `members_sn` at the arrow type, which is an ordinary
/// `ty`-shaped type here and so NOT one of the degenerate arrow-SHAPED
/// instances R23 measured.
pub(super) fn ty_red_arrow_sn() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D), GoodEnvD D r -> forall (t : KExpr), r24_RedAt D (r25_arrow A B) (r25_arrowWkc D A B hA hB) r t -> whnf_acc t".to_string()
}

pub(super) fn val_red_arrow_sn() -> String {
    "fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) => r24_red_members_sn D (r25_arrow A B) (r25_arrowWkc D A B hA hB) r hr".to_string()
}

// ================================================================
// Group C — negative controls. NOT registered.
// ================================================================

/// The elimination rule with the `r20_xval_lift0` transport DROPPED — the
/// application handed back directly. It must be refused: the `pi` clause reads
/// its codomain LIFTED at the junk extension, so `hf a ha` inhabits the lifted
/// reading and not `B`'s own, and the two are identified by a lemma rather than
/// by computation. If this ever passes, `r20_xval_lift0` is not load-bearing
/// here and the arrow candidate is reading its codomain somewhere unexpected.
#[cfg(test)]
pub(super) fn probe_app_without_transport() -> String {
    format!("def r25_app_no_transport_probe : {} := fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D) (f : KExpr) (a : KExpr) (hf : r24_RedAt D (r25_arrow A B) (r25_arrowWkc D A B hA hB) r f) (ha : r24_RedAt D A hA r a) => hf a ha", ty_red_app())
}

/// The introduction rule with its `whnf_acc` premises dropped. R1's engine
/// takes both — the redex's SN is not free — so the kernel must refuse.
#[cfg(test)]
pub(super) fn probe_lam_without_acc() -> String {
    let xl = xval_lifted();
    let redex = "(KExpr.app (KExpr.lam ann b) a)";
    format!("def r25_lam_no_acc_probe : forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D), GoodEnvD D r -> forall (ann : KExpr) (b : KExpr), (forall (b2 : KExpr), betaStar b b2 -> forall (a2 : KExpr), r24_RedAt D A hA r a2 -> r24_RedAt D B hB r (instantiate b2 a2)) -> r24_RedAt D (r25_arrow A B) (r25_arrowWkc D A B hA hB) r (KExpr.lam ann b) := fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) (ann : KExpr) (b : KExpr) (hfam : forall (b2 : KExpr), betaStar b b2 -> forall (a2 : KExpr), r24_RedAt D A hA r a2 -> r24_RedAt D B hB r (instantiate b2 a2)) (a : KExpr) (ha : r24_RedAt D A hA r a) => Eq.substType (VD Sk.ty) (fun (qv : VD Sk.ty) => qv {redex}) (xval D B Sk.ty hB r) {xl} (Eq.symm (VD Sk.ty) {xl} (xval D B Sk.ty hB r) (r20_xval_lift0 D B Sk.ty hB Sk.ty (junkD Sk.ty) r)) (r24_red_beta_expand D A B hA hB r hr ann hann b hb hfam a ha)")
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R25Item {
    Def {
        name: String,
        src: String,
    },
    Thm {
        name: String,
        ty: String,
        val: String,
    },
}

#[cfg(test)]
impl R25Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R25Item::Def { name, .. } | R25Item::Thm { name, .. } => name,
        }
    }

    pub(super) fn decl_source(&self) -> String {
        match self {
            R25Item::Def { src, .. } => src.clone(),
            R25Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn d(name: &str, src: String) -> R25Item {
    R25Item::Def {
        name: name.to_string(),
        src,
    }
}

fn t(name: &str, ty: String, val: String) -> R25Item {
    R25Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R25 constant, in registration order.
pub(super) fn r25_items() -> Vec<R25Item> {
    vec![
        d("r25_arrow", src_arrow()),
        d("r25_arrowWkc", src_arrow_wkc()),
        t(
            "r25_red_arrow_is_the_function_space",
            ty_red_arrow_unfolds(),
            val_red_arrow_unfolds(),
        ),
        t("r25_red_app", ty_red_app(), val_red_app()),
        t("r25_red_lam", ty_red_lam(), val_red_lam()),
        t(
            "r25_red_arrow_members_sn",
            ty_red_arrow_sn(),
            val_red_arrow_sn(),
        ),
    ]
}

#[cfg(test)]
pub(super) fn r25_all_sources() -> Vec<(String, String)> {
    r25_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
