// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R24 sources — **THE REDUCIBILITY INTERFACE**: reducibility at a `ty`-shaped
//! type over R17's seven-constructor interpretation, with R1's β
//! head-expansion engine landed on it and R1's ζ refutation paired beside it.
//!
//! See the module doc of [`super::candmodel_construct_r24`] for the argument.

// **This module deliberately imports nothing** — the R12-R23 convention.

/// R1's head-expansion ENGINE shape, at a chosen redex. R1 spells this once and
/// instantiates it twice: at `app (lam ty b) a`, where it is a THEOREM
/// (`candExp_beta`), and at `let_ ty a b`, where it is REFUTED
/// (`zeta_expansion_not_generic`). Re-spelled here, over `IsCandHF`, so the two
/// can be paired in one constant.
///
/// `s` and `sa` are spelled UNPARENTHESISED and applied flat. Measured
/// 2026-09-17: this parser rejects a parenthesised application in HEAD
/// position — `(r24_RedAt D A hA r) qa2` elaborates to "function type
/// fvar#… is not a function type, but 4 argument(s) remain", where the flat
/// `r24_RedAt D A hA r qa2` is accepted. The sibling value of this very
/// theorem was written flat and passed while the type was written
/// parenthesised and failed, which is how the restriction surfaced.
fn engine_ty_hf(s: &str, sa: &str, redex: &str) -> String {
    format!("forall (qlamTy : KExpr), whnf_acc qlamTy -> forall (qb : KExpr), whnf_acc qb -> (forall (qb2 : KExpr), betaStar qb qb2 -> forall (qa2 : KExpr), {sa} qa2 -> {s} (instantiate qb2 qa2)) -> forall (qa : KExpr), {sa} qa -> {s} {redex}")
}

/// R1's ζ engine hypothesis, verbatim in shape: `IsCandSet` and the `let_`
/// redex. This is the statement `zeta_expansion_not_generic` sends to `Empty`.
#[cfg_attr(not(test), allow(dead_code))]
fn zeta_engine_hypothesis() -> String {
    "forall (S : KExpr -> Type) (SA : KExpr -> Type), IsCandSet S -> IsCandSet SA -> forall (ty : KExpr), whnf_acc ty -> forall (b : KExpr), whnf_acc b -> (forall (b2 : KExpr), betaStar b b2 -> forall (a2 : KExpr), SA a2 -> S (instantiate b2 a2)) -> forall (a : KExpr), SA a -> S (KExpr.let_ ty a b)".to_string()
}

// ================================================================
// Group A — the interface.
// ================================================================

/// **`r24_RedAt`** — REDUCIBILITY at a type.
///
/// A term `t` is reducible at the type `A` when it belongs to the candidate `A`
/// denotes. `A` is required to be `WKC`-typed at shape `Sk.ty`, which is
/// exactly where `vcarD` is faithful (`r23_vcar_ty_is_the_set`) — so unlike the
/// arrow-shaped instances R23 measured, this predicate carries the
/// interpretation's full content.
pub(super) const SRC_RED_AT: &str = "def r24_RedAt (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D) : KExpr -> Type := vcarD Sk.ty (xval D A Sk.ty hA r)";

/// **`r24_red_isCandHF`** — reducibility at a type is a HEAD-FREE candidate.
///
/// R23 gives `IsCandHI`; `isCandHI_weaken` is the one step to the class R1's
/// engines are stated over.
pub(super) const TY_RED_ISCANDHF: &str = "forall (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D), GoodEnvD D r -> IsCandHF (r24_RedAt D A hA r)";

pub(super) const VAL_RED_ISCANDHF: &str = "fun (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) => isCandHI_weaken (vcarD Sk.ty (xval D A Sk.ty hA r)) (r23_isCandHI_xval D A Sk.ty hA r hr)";

// ================================================================
// Group B — THE BETA ENGINE, ON THE INTERPRETATION'S OWN CANDIDATES.
// ================================================================

/// **`r24_red_beta_expand` — β HEAD-EXPANSION at `r24_RedAt`.**
///
/// If the contractum is reducible at the result type for every reducible
/// argument and every `betaStar`-development of the body, then the REDEX is
/// reducible at the result type. This is R1's `candExpHF_beta` instantiated at
/// the candidates R23 supplies, and it is the lemma a Tait fundamental theorem
/// spends at its `lam` case.
///
/// **It exists because a β redex is NEUTRAL**, which is R1's own pivot: the
/// spec's `Neutral` sends every `app` head to `ConstFreeUnit`, so
/// `app (lam ty b) a` is neutral and cr3 applies. It is also `HeadFree` — its
/// `kapp_fn` is a `lam`, whose `kexpr_const_name` is `none` — which is why the
/// HeadFree-restricted class suffices and no stronger candidate interface is
/// needed.
pub(super) fn ty_red_beta_expand() -> String {
    let s = "r24_RedAt D B hB r";
    let sa = "r24_RedAt D A hA r";
    format!("forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D), GoodEnvD D r -> {}", engine_ty_hf(s, sa, "(KExpr.app (KExpr.lam qlamTy qb) qa)"))
}

pub(super) const VAL_RED_BETA_EXPAND: &str = "fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) (qlamTy : KExpr) (hlamTy : whnf_acc qlamTy) (qb : KExpr) (hb : whnf_acc qb) (hfam : forall (qb2 : KExpr), betaStar qb qb2 -> forall (qa2 : KExpr), r24_RedAt D A hA r qa2 -> r24_RedAt D B hB r (instantiate qb2 qa2)) (qa : KExpr) (ha : r24_RedAt D A hA r qa) => candExpHF_beta (r24_RedAt D B hB r) (r24_RedAt D A hA r) (r24_red_isCandHF D B hB r hr) (r24_red_isCandHF D A hA r hr) qlamTy hlamTy qb hb hfam qa ha";

/// **THE CONTRAST — and why it is NOT one constant.**
///
/// The intent was an `AndType` pairing the β engine above with R1's
/// `zeta_expansion_not_generic`. It does not typecheck, and the reason is
/// measured rather than guessed: `GoodEnvD` lives in `Type 1` (it is a
/// `forall` over `GoodD`, which R12 put there deliberately because this kernel
/// is NON-CUMULATIVE and `IsCandHI S : Type 0` could not be the base), so the
/// β-engine statement is a `Type 1`, while `AndType` is `Type 0`-valued. The
/// kernel reports `universe level conflict: 1 vs 0`, and no `Type 1`
/// conjunction exists in the spec.
///
/// So the contrast is carried MECHANICALLY instead, by three things that do
/// hold: `r24_red_beta_expand` is registered; `zeta_expansion_not_generic` is
/// R1's and registered; and `r24_zeta_engine_probe` — the same engine at
/// `r24_RedAt` with the redex swapped — is REFUSED by the kernel. This helper
/// survives as the drift guard that the two engine shapes still differ in
/// exactly the redex and nothing else.
#[cfg(test)]
pub(super) fn ty_beta_holds_zeta_refuted() -> String {
    format!(
        "AndType ({}) (({}) -> Empty)",
        ty_red_beta_expand(),
        zeta_engine_hypothesis()
    )
}

#[cfg(test)]
pub(super) fn zeta_engine_hypothesis_for_test() -> String {
    zeta_engine_hypothesis()
}

// ================================================================
// Group C — what the interface inherits from R22 and R23.
// ================================================================

/// **`r24_red_members_sn`** — every reducible term is `whnf_acc`. R23's
/// normalization theorem at `Sk.ty`, which is its non-degenerate shape.
pub(super) const TY_RED_MEMBERS_SN: &str = "forall (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D), GoodEnvD D r -> forall (x : KExpr), r24_RedAt D A hA r x -> whnf_acc x";

pub(super) const VAL_RED_MEMBERS_SN: &str = "fun (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) => r23_xval_members_sn D A Sk.ty hA r hr";

/// **`r24_red_excludes_omega`** — the looping term is reducible at no type.
pub(super) const TY_RED_EXCLUDES_OMEGA: &str = "forall (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D), GoodEnvD D r -> r24_RedAt D A hA r r5_omegaV -> Empty";

pub(super) const VAL_RED_EXCLUDES_OMEGA: &str = "fun (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D) (hr : GoodEnvD D r) => r23_xval_excludes_omega D A Sk.ty hA r hr";

/// **`r24_red_conv_stable`** — reducibility is stable under CONVERSION of the
/// type.
///
/// R22's `val_conv` at `Sk.ty`. Worth registering separately because R23
/// measured that `r22_xval_conv` degenerates to the identity at ARROW shapes;
/// this is the instance where it does not, and it is the one a fundamental
/// theorem's conversion rule would consume.
pub(super) const TY_RED_CONV_STABLE: &str = "forall (D : Nat -> Sk) (A1 : KExpr) (A2 : KExpr) (w : KExpr) (hA1 : WKC D A1 Sk.ty) (hA2 : WKC D A2 Sk.ty) (r : VEnvD D) (t : KExpr), whnfStar A1 w -> whnfStar A2 w -> r24_RedAt D A1 hA1 r t -> r24_RedAt D A2 hA2 r t";

pub(super) const VAL_RED_CONV_STABLE: &str = "fun (D : Nat -> Sk) (A1 : KExpr) (A2 : KExpr) (w : KExpr) (hA1 : WKC D A1 Sk.ty) (hA2 : WKC D A2 Sk.ty) (r : VEnvD D) (t : KExpr) => r22_xval_conv D A1 A2 w Sk.ty hA1 hA2 r t";

// ================================================================
// Group D — negative controls. NOT registered.
// ================================================================

/// The ζ engine at `r24_RedAt`, proved the way the β one is. It must be
/// refused: `candExpHF_beta`'s conclusion is the `app (lam …) …` redex and
/// there is no engine that yields the `let_` one — R1 proved there cannot be.
#[cfg(test)]
pub(super) fn probe_zeta_engine_at_red() -> String {
    let s = "r24_RedAt D B hB r";
    let sa = "r24_RedAt D A hA r";
    format!("def r24_zeta_engine_probe : forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (hA : WKC D A Sk.ty) (hB : WKC D B Sk.ty) (r : VEnvD D), GoodEnvD D r -> {} := {}", engine_ty_hf(s, sa, "(KExpr.let_ qlamTy qa qb)"), VAL_RED_BETA_EXPAND)
}

/// Candidacy of `r24_RedAt` with the `GoodEnvD` premise dropped. Refused —
/// R23's adequacy is what makes the interpretation a candidate at all, and it
/// is conditional on a good valuation.
#[cfg(test)]
pub(super) fn probe_candhf_without_env() -> String {
    "def r24_candhf_no_env_probe : forall (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D), IsCandHF (r24_RedAt D A hA r) := fun (D : Nat -> Sk) (A : KExpr) (hA : WKC D A Sk.ty) (r : VEnvD D) => isCandHI_weaken (vcarD Sk.ty (xval D A Sk.ty hA r)) isCandHI_whnfAcc".to_string()
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R24Item {
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
impl R24Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R24Item::Def { name, .. } | R24Item::Thm { name, .. } => name,
        }
    }

    pub(super) fn decl_source(&self) -> String {
        match self {
            R24Item::Def { src, .. } => src.clone(),
            R24Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn d(name: &str, src: String) -> R24Item {
    R24Item::Def {
        name: name.to_string(),
        src,
    }
}

fn t(name: &str, ty: String, val: String) -> R24Item {
    R24Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R24 constant, in registration order.
pub(super) fn r24_items() -> Vec<R24Item> {
    vec![
        d("r24_RedAt", SRC_RED_AT.to_string()),
        t(
            "r24_red_isCandHF",
            TY_RED_ISCANDHF.to_string(),
            VAL_RED_ISCANDHF.to_string(),
        ),
        t(
            "r24_red_beta_expand",
            ty_red_beta_expand(),
            VAL_RED_BETA_EXPAND.to_string(),
        ),
        t(
            "r24_red_members_sn",
            TY_RED_MEMBERS_SN.to_string(),
            VAL_RED_MEMBERS_SN.to_string(),
        ),
        t(
            "r24_red_excludes_omega",
            TY_RED_EXCLUDES_OMEGA.to_string(),
            VAL_RED_EXCLUDES_OMEGA.to_string(),
        ),
        t(
            "r24_red_conv_stable",
            TY_RED_CONV_STABLE.to_string(),
            VAL_RED_CONV_STABLE.to_string(),
        ),
    ]
}

#[cfg(test)]
pub(super) fn r24_all_sources() -> Vec<(String, String)> {
    r24_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
