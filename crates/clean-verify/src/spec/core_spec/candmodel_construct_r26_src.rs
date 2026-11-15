// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R26 sources — **THE SINGLE-CONTRACTUM ENGINE**, ported to the HeadFree
//! candidate class, and the `lam` rule in the form a fundamental theorem
//! actually supplies.
//!
//! See the module doc of [`super::candmodel_construct_r26`] for the argument.

// **This module deliberately imports nothing** — the R12-R25 convention.

/// The codomain read as `xval`'s `pi` clause reads it — lifted, at the junk
/// extension. R25's spelling, repeated here because this file imports nothing.
const XLIFT: &str = "(xval (skcons Sk.ty D) (lift_at B Nat.zero (Nat.succ Nat.zero)) Sk.ty (wkc_lift0 D B Sk.ty hB Sk.ty) (vconsD Sk.ty D (junkD Sk.ty) r))";

// ================================================================
// Group A — the cr2-face port.
// ================================================================

/// **`r26_candHF_betaStar_closed`** — R2's `candSet_betaStar_closed` at the
/// HeadFree class.
///
/// R2's proof iterates the **cr2 face** and nothing else — its own description
/// says so — and cr2 is UNRESTRICTED in both `IsCandSet` and `IsCandHF`; only
/// cr3 differs, by taking a `HeadFree` witness. So the port is R2's term with
/// `IsCandSet` replaced by `IsCandHF` and `isCandSet_cr2` by `isCandHF_cr2`,
/// which is the same mechanical weakening R5 applied to `candExp_beta` to get
/// `candExpHF_beta`.
pub(super) const TY_CANDHF_BETASTAR_CLOSED: &str = "forall (S : KExpr -> Type), IsCandHF S -> forall (x : KExpr) (y : KExpr), betaStar x y -> S x -> S y";

pub(super) const VAL_CANDHF_BETASTAR_CLOSED: &str = "fun (S : KExpr -> Type) (hS : IsCandHF S) (x : KExpr) (y : KExpr) (hstar : betaStar x y) => betaStar.rec (fun (x0 : KExpr) (y0 : KExpr) (_ : betaStar x0 y0) => S x0 -> S y0) (fun (xe : KExpr) (hx : S xe) => hx) (fun (xe : KExpr) (xe2 : KExpr) (xe3 : KExpr) (hstep : beta_reduces xe xe2) (_hrest : betaStar xe2 xe3) (ih : S xe2 -> S xe3) (hx : S xe) => ih (isCandHF_cr2 S hS xe xe2 hx (whnf_step.beta xe xe2 hstep))) x y hstar";

/// **`r26_candExpHF_beta_subst`** — R2's single-contractum engine at the
/// HeadFree class.
///
/// R2 builds `candExp_beta_subst` as `candExp_beta` fed a family premise
/// manufactured from the SINGLE contractum by walking `betaStar` with
/// `candSet_betaStar_closed` and `betaStar_inst_transport`. Every piece of that
/// has a HeadFree counterpart — `candExpHF_beta` is R5's, the star walker is
/// the port above, and the transport is about `betaStar` and `instantiate`
/// only — so this is R2's proof with two names changed.
///
/// **This is the constant the ladder was missing.** R24's `r24_red_beta_expand`
/// takes R1's FAMILY premise, which is the honest engine interface but not what
/// a fundamental theorem's `lam` case produces; that case produces the single
/// contractum, through `psubst_scons_instantiate`.
pub(super) const TY_CANDEXPHF_BETA_SUBST: &str = "forall (S : KExpr -> Type) (SA : KExpr -> Type), IsCandHF S -> IsCandHF SA -> RecEnvClosed (red_rec the_red_env) -> forall (ty : KExpr), whnf_acc ty -> forall (b : KExpr), whnf_acc b -> (forall (a2 : KExpr), SA a2 -> S (instantiate b a2)) -> forall (a : KExpr), SA a -> S (KExpr.app (KExpr.lam ty b) a)";

pub(super) const VAL_CANDEXPHF_BETA_SUBST: &str = "fun (S : KExpr -> Type) (SA : KExpr -> Type) (hS : IsCandHF S) (hSA : IsCandHF SA) (hcl : RecEnvClosed (red_rec the_red_env)) (ty : KExpr) (hty : whnf_acc ty) (b : KExpr) (hb : whnf_acc b) (hone : forall (a2 : KExpr), SA a2 -> S (instantiate b a2)) (a : KExpr) (ha : SA a) => candExpHF_beta S SA hS hSA ty hty b hb (fun (b2 : KExpr) (hstar : betaStar b b2) (a2 : KExpr) (ha2 : SA a2) => r26_candHF_betaStar_closed S hS (instantiate b a2) (instantiate b2 a2) (betaStar_inst_transport b b2 hstar hcl a2) (hone a2 ha2)) a ha";

// ================================================================
// Group B — the rule a fundamental theorem supplies.
// ================================================================

/// **`r26_red_beta_expand_one`** — β head-expansion at `r24_RedAt`, from the
/// SINGLE contractum.
pub(super) fn ty_red_beta_expand_one() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D), GoodEnvD D r -> RecEnvClosed (red_rec the_red_env) -> forall (lamTy : KExpr), whnf_acc lamTy -> forall (b : KExpr), whnf_acc b -> (forall (a2 : KExpr), r24_RedAt D A hA r a2 -> r24_RedAt D B hB r (instantiate b a2)) -> forall (a : KExpr), r24_RedAt D A hA r a -> r24_RedAt D B hB r (KExpr.app (KExpr.lam lamTy b) a)".to_string()
}

pub(super) const VAL_RED_BETA_EXPAND_ONE: &str = "fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) (hcl : RecEnvClosed (red_rec the_red_env)) (lamTy : KExpr) (hlamTy : whnf_acc lamTy) (b : KExpr) (hb : whnf_acc b) (hone : forall (a2 : KExpr), r24_RedAt D A hA r a2 -> r24_RedAt D B hB r (instantiate b a2)) (a : KExpr) (ha : r24_RedAt D A hA r a) => r26_candExpHF_beta_subst (r24_RedAt D B hB r) (r24_RedAt D A hA r) (r24_red_isCandHF D B hB r hr) (r24_red_isCandHF D A hA r hr) hcl lamTy hlamTy b hb hone a ha";

/// **`r26_red_lam_one` — THE `lam` RULE IN THE FORM A FUNDAMENTAL THEOREM
/// SUPPLIES IT.**
///
/// R25's `r25_red_lam` takes R1's family premise. This takes the SINGLE
/// contractum, which is what a fundamental theorem's `lam` case has in hand: at
/// body `b` and substitution `σ`, its induction hypothesis gives reducibility
/// of `psubst (scons a σ) b`, and `psubst_scons_instantiate` turns that into
/// reducibility of `instantiate (psubst (up σ) b) a` — exactly this premise.
pub(super) fn ty_red_lam_one() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D), GoodEnvD D r -> RecEnvClosed (red_rec the_red_env) -> forall (ann : KExpr), whnf_acc ann -> forall (b : KExpr), whnf_acc b -> (forall (a2 : KExpr), r24_RedAt D A hA r a2 -> r24_RedAt D B hB r (instantiate b a2)) -> r24_RedAt D (r25_arrow A B) (r25_arrowWkc D A B hA hB) r (KExpr.lam ann b)".to_string()
}

pub(super) fn val_red_lam_one() -> String {
    let redex = "(KExpr.app (KExpr.lam ann b) a)";
    format!("fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) (hcl : RecEnvClosed (red_rec the_red_env)) (ann : KExpr) (hann : whnf_acc ann) (b : KExpr) (hb : whnf_acc b) (hone : forall (a2 : KExpr), r24_RedAt D A hA r a2 -> r24_RedAt D B hB r (instantiate b a2)) (a : KExpr) (ha : r24_RedAt D A hA r a) => Eq.substType (VD Sk.ty) (fun (qv : VD Sk.ty) => qv {redex}) (xval D B Sk.ty hB r) {XLIFT} (Eq.symm (VD Sk.ty) {XLIFT} (xval D B Sk.ty hB r) (r20_xval_lift0 D B Sk.ty hB Sk.ty (junkD Sk.ty) r)) (r26_red_beta_expand_one D A B hA hB r hr hcl ann hann b hb hone a ha)")
}

/// **`r26_lam_premise_is_the_induction_hypothesis`** — the bridge, stated.
///
/// `psubst_scons_instantiate` is `psubst (scons a s) b = instantiate (psubst
/// (up s) b) a`. Read right to left at a reducibility predicate, it says: the
/// premise `r26_red_lam_one` wants about `instantiate (psubst (up s) b) a` IS
/// reducibility of `psubst (scons a s) b`, which is what an induction on a term
/// judgment hands back at its `lam` case. Registered so the connection is a
/// kernel-checked constant rather than a remark in a commit message.
pub(super) const TY_LAM_PREMISE_IS_IH: &str = "forall (D : Nat -> Sk) (B : KExpr) (hB : WKC D B Sk.ty) (r : VEnvD D) (b : KExpr) (s : Nat -> KExpr) (a : KExpr), r24_RedAt D B hB r (psubst (scons a s) b) -> r24_RedAt D B hB r (instantiate (psubst (up s) b) a)";

pub(super) const VAL_LAM_PREMISE_IS_IH: &str = "fun (D : Nat -> Sk) (B : KExpr) (hB : WKC D B Sk.ty) (r : VEnvD D) (b : KExpr) (s : Nat -> KExpr) (a : KExpr) (h : r24_RedAt D B hB r (psubst (scons a s) b)) => Eq.substType KExpr (fun (qw : KExpr) => r24_RedAt D B hB r qw) (psubst (scons a s) b) (instantiate (psubst (up s) b) a) (psubst_scons_instantiate b a s) h";

// ================================================================
// Group C — negative controls. NOT registered.
// ================================================================

/// The star walker with cr2 swapped for cr1. It must be refused: cr1 says
/// members are `whnf_acc`, which does not move membership along a step, and the
/// walk is the only thing that turns a single contractum into R1's family.
#[cfg(test)]
pub(super) fn probe_star_walker_with_cr1() -> String {
    VAL_CANDHF_BETASTAR_CLOSED
        .replace("isCandHF_cr2", "isCandHF_cr1")
        .replace(
            "fun (S : KExpr -> Type) (hS : IsCandHF S)",
            "def r26_star_cr1_probe : forall (S : KExpr -> Type), IsCandHF S -> forall (x : KExpr) (y : KExpr), betaStar x y -> S x -> S y := fun (S : KExpr -> Type) (hS : IsCandHF S)",
        )
}

/// The single-contractum rule with the `RecEnvClosed` hypothesis dropped. It
/// must be refused: `betaStar_inst_transport` takes it, and the spec passes it
/// as a premise rather than discharging it at `the_red_env`.
#[cfg(test)]
pub(super) fn probe_one_without_recenvclosed() -> String {
    format!("def r26_one_no_recenv_probe : forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D), GoodEnvD D r -> forall (lamTy : KExpr), whnf_acc lamTy -> forall (b : KExpr), whnf_acc b -> (forall (a2 : KExpr), r24_RedAt D A hA r a2 -> r24_RedAt D B hB r (instantiate b a2)) -> forall (a : KExpr), r24_RedAt D A hA r a -> r24_RedAt D B hB r (KExpr.app (KExpr.lam lamTy b) a) := {VAL_RED_BETA_EXPAND_ONE}")
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R26Item {
    Thm {
        name: String,
        ty: String,
        val: String,
    },
}

#[cfg(test)]
impl R26Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R26Item::Thm { name, .. } => name,
        }
    }

    pub(super) fn decl_source(&self) -> String {
        match self {
            R26Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn t(name: &str, ty: String, val: String) -> R26Item {
    R26Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R26 constant, in registration order.
pub(super) fn r26_items() -> Vec<R26Item> {
    vec![
        t(
            "r26_candHF_betaStar_closed",
            TY_CANDHF_BETASTAR_CLOSED.to_string(),
            VAL_CANDHF_BETASTAR_CLOSED.to_string(),
        ),
        t(
            "r26_candExpHF_beta_subst",
            TY_CANDEXPHF_BETA_SUBST.to_string(),
            VAL_CANDEXPHF_BETA_SUBST.to_string(),
        ),
        t(
            "r26_red_beta_expand_one",
            ty_red_beta_expand_one(),
            VAL_RED_BETA_EXPAND_ONE.to_string(),
        ),
        t("r26_red_lam_one", ty_red_lam_one(), val_red_lam_one()),
        t(
            "r26_lam_premise_is_the_induction_hypothesis",
            TY_LAM_PREMISE_IS_IH.to_string(),
            VAL_LAM_PREMISE_IS_IH.to_string(),
        ),
    ]
}

#[cfg(test)]
pub(super) fn r26_all_sources() -> Vec<(String, String)> {
    r26_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
