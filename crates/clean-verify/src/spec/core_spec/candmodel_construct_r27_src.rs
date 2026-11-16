// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R27 sources — **VARIABLES ARE REDUCIBLE**, and reducibility does not see
//! which derivation typed the type. The two facts a Tait fundamental theorem
//! needs that are about `r24_RedAt` itself rather than about a rule.
//!
//! See the module doc of [`super::candmodel_construct_r27`] for the argument.

// **This module deliberately imports nothing** — the R12-R26 convention.

/// The `HeadFree` witness at any head that is not a constant application.
/// `kapp_fn (bvar i)` is `bvar i`, whose `kexpr_const_name` is `none`.
const HF_REFL: &str = "(@Eq.refl (OptionType Name) (@OptionType.none Name))";

// ================================================================
// Group A — reducibility is derivation-irrelevant.
// ================================================================

/// **`r27_red_irrel`** — `r24_RedAt` does not depend on WHICH `WKC` derivation
/// typed the type.
///
/// `r17_xval_irrel` (R17's subsingleton, through `r17_wkc_deriv_unique`) says
/// two `WKC` derivations of one judgment have equal interpretations;
/// `vcarD Sk.ty V` computes to `V`, so the membership transports along that
/// equality with one `Eq.substType`.
///
/// **This is what lets a term judgment quantify over the derivation in its
/// conclusion.** A fundamental theorem's arms each have a derivation in hand —
/// `tvar` has the context's, `tapp` and `tlam` have their nodes' — and they are
/// not the same one the statement was given. Without this the theorem could not
/// be stated uniformly.
pub(super) const TY_RED_IRREL: &str = "forall (D : Nat -> Sk) (A : KExpr) (h1 : WKC D A Sk.ty) (h2 : WKC D A Sk.ty) (r : VEnvD D) (t : KExpr), r24_RedAt D A h1 r t -> r24_RedAt D A h2 r t";

pub(super) const VAL_RED_IRREL: &str = "fun (D : Nat -> Sk) (A : KExpr) (h1 : WKC D A Sk.ty) (h2 : WKC D A Sk.ty) (r : VEnvD D) (t : KExpr) (hm : r24_RedAt D A h1 r t) => @Eq.substType (VD Sk.ty) (fun (qv : VD Sk.ty) => qv t) (xval D A Sk.ty h1 r) (xval D A Sk.ty h2 r) (r17_xval_irrel D A Sk.ty h1 h2 r) hm";

// ================================================================
// Group B — VARIABLES ARE REDUCIBLE.
// ================================================================

/// **`r27_red_var` — every de Bruijn variable is reducible at EVERY type.**
///
/// The classical pivot of a Tait argument, and here it is three ingredients
/// this ladder already has:
///
/// * `bvar i` is **Neutral** — the spec's `Neutral` sends a `bvar` to
///   `ConstFreeUnit`, so `ConstFreeUnit.triv` discharges it;
/// * `bvar i` is **`HeadFree`** — `kapp_fn (bvar i)` is `bvar i` and its
///   `kexpr_const_name` is `none`, so `Eq.refl` discharges it;
/// * a `bvar` **cannot step** — `r15_whnf_stepT_inv` at a `bvar` head has NO
///   continuations, so it produces the goal type directly from the step.
///
/// cr3 then applies: a neutral, head-free term all of whose reducts are in the
/// candidate is in the candidate, and it has no reducts.
///
/// **Why a fundamental theorem cannot do without it.** Its `lam` case must
/// supply `whnf_acc` of the substituted body to R1's engine, and the body is
/// only reducible after an argument is substituted. The classical escape is to
/// substitute a VARIABLE — sound exactly because variables are reducible, which
/// is this lemma.
pub(super) fn ty_red_var() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D), GoodEnvD D r -> forall (i : Nat), r24_RedAt D A hA r (KExpr.bvar i)".to_string()
}

pub(super) fn val_red_var() -> String {
    format!("fun (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) (i : Nat) => isCandHF_cr3 (r24_RedAt D A hA r) (r24_red_isCandHF D A hA r hr) (KExpr.bvar i) {HF_REFL} ConstFreeUnit.triv (fun (qe2 : KExpr) (qst : whnf_step (KExpr.bvar i) qe2) => r15_whnf_stepT_inv (r24_RedAt D A hA r qe2) (KExpr.bvar i) qe2 {HF_REFL} qst)")
}

/// **`r27_red_var_is_sn`** — the immediate corollary, and the shape the `lam`
/// case consumes: a variable normalizes. Trivial on its own; registered because
/// it is the composition `r24_red_members_sn ∘ r27_red_var` that a later rung
/// will spend, and because it is the smallest object at which the whole chain
/// from R23's adequacy down to a concrete term is visible.
pub(super) fn ty_red_var_is_sn() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D), GoodEnvD D r -> forall (i : Nat), whnf_acc (KExpr.bvar i)".to_string()
}

pub(super) fn val_red_var_is_sn() -> String {
    "fun (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) (i : Nat) => r24_red_members_sn D A hA r hr (KExpr.bvar i) (r27_red_var D A hA r hr i)".to_string()
}

// ================================================================
// Group C — negative controls. NOT registered.
// ================================================================

/// The same cr3 route at a LAMBDA instead of a variable. It must be refused:
/// the spec's `Neutral` sends a `lam` to `Empty`, so `ConstFreeUnit.triv`
/// cannot discharge the neutrality premise. This is the control that
/// `r27_red_var` rests on `bvar`'s NEUTRALITY and not on something that would
/// make every term reducible — if it passed, `r24_RedAt` would be total and
/// every membership result in R18-R26 would be worthless.
#[cfg(test)]
pub(super) fn probe_lam_is_reducible() -> String {
    format!("def r27_lam_reducible_probe : forall (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D), GoodEnvD D r -> forall (ann : KExpr) (b : KExpr), r24_RedAt D A hA r (KExpr.lam ann b) := fun (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) (ann : KExpr) (b : KExpr) => isCandHF_cr3 (r24_RedAt D A hA r) (r24_red_isCandHF D A hA r hr) (KExpr.lam ann b) {HF_REFL} ConstFreeUnit.triv (fun (qe2 : KExpr) (qst : whnf_step (KExpr.lam ann b) qe2) => r15_whnf_stepT_inv (r24_RedAt D A hA r qe2) (KExpr.lam ann b) qe2 {HF_REFL} qst)")
}

/// `r27_red_var` with the `GoodEnvD` premise dropped. Refused: candidacy of
/// `r24_RedAt` is what cr3 is applied to, and that is R23's adequacy, which is
/// conditional on a good valuation.
#[cfg(test)]
pub(super) fn probe_var_without_env() -> String {
    format!("def r27_var_no_env_probe : forall (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D) (i : Nat), r24_RedAt D A hA r (KExpr.bvar i) := fun (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D) (i : Nat) => isCandHF_cr3 (r24_RedAt D A hA r) (r24_red_isCandHF D A hA r) (KExpr.bvar i) {HF_REFL} ConstFreeUnit.triv (fun (qe2 : KExpr) (qst : whnf_step (KExpr.bvar i) qe2) => r15_whnf_stepT_inv (r24_RedAt D A hA r qe2) (KExpr.bvar i) qe2 {HF_REFL} qst)")
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R27Item {
    Thm {
        name: String,
        ty: String,
        val: String,
    },
}

#[cfg(test)]
impl R27Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R27Item::Thm { name, .. } => name,
        }
    }

    pub(super) fn decl_source(&self) -> String {
        match self {
            R27Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn t(name: &str, ty: String, val: String) -> R27Item {
    R27Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R27 constant, in registration order.
pub(super) fn r27_items() -> Vec<R27Item> {
    vec![
        t(
            "r27_red_irrel",
            TY_RED_IRREL.to_string(),
            VAL_RED_IRREL.to_string(),
        ),
        t("r27_red_var", ty_red_var(), val_red_var()),
        t("r27_red_var_is_sn", ty_red_var_is_sn(), val_red_var_is_sn()),
    ]
}

#[cfg(test)]
pub(super) fn r27_all_sources() -> Vec<(String, String)> {
    r27_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
