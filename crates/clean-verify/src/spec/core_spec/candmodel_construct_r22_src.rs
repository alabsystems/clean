// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R22 sources — **THE NATIVE CONVERSION LEMMA**, and the `whnfStar` form that
//! carries the step law to it.
//!
//! See the module doc of [`super::candmodel_construct_r22`] for the argument.

// **This module deliberately imports nothing** — the R12-R21 convention.

/// R12's `KDTY`.
const KDTY: &str = "(Sk.kd Sk.ty)";
/// `bvar 0`.
const V0: &str = "(KExpr.bvar Nat.zero)";
/// `Sort 0`.
const S0: &str = "(KExpr.sort Level.zero)";
/// R16's `INST0` — the ζ/β contractum both witnesses land on.
const INST0: &str = "(instantiate (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))";

/// R15's CPS continuation shape, at `xval`.
fn sem_k(d: &str, e2: &str, s: &str, src: &str, c: &str) -> String {
    format!("forall (zh2 : WKC {d} {e2} {s}), (forall (zr : VEnvD {d}), Eq (VD {s}) (xval {d} {e2} {s} zh2 zr) ({src} zr)) -> {c}")
}

// ================================================================
// Group A — the reduction SEQUENCE.
// ================================================================

/// **`r22_xval_star_sem`** — R15's `val_star_sem` over `WKC`/`xval`.
///
/// An induction on `whnfStar`, not on the derivation, so it has exactly two
/// arms and neither of them knows how many constructors the shape system has.
/// That is why this rung is short where R19-R21 were long: the seven-constructor
/// work is all inside `r21_xval_step_sem`, which this consumes once.
pub(super) fn ty_xval_star_sem() -> String {
    format!(
        "forall (D : Nat -> Sk) (e : KExpr) (w : KExpr), whnfStar e w -> forall (s : Sk) (h : WKC D e s) (C : Type), ({}) -> C",
        sem_k("D", "w", "s", "(xval D e s h)", "C")
    )
}

pub(super) fn val_xval_star_sem() -> String {
    let mot = format!(
        "(fun (qe : KExpr) (qw : KExpr) (qh : whnfStar qe qw) => forall (qs : Sk) (qd : WKC D qe qs) (qC : Type), ({}) -> qC)",
        sem_k("D", "qw", "qs", "(xval D qe qs qd)", "qC")
    );
    let m_refl = format!(
        "(fun (qe : KExpr) (qs : Sk) (qd : WKC D qe qs) (qC : Type) (qk : {}) => qk qd (fun (zr : VEnvD D) => Eq.refl (VD qs) (xval D qe qs qd zr)))",
        sem_k("D", "qe", "qs", "(xval D qe qs qd)", "qC")
    );
    let ih = format!(
        "(qih : forall (qs : Sk) (qd : WKC D qe2 qs) (qC : Type), ({}) -> qC)",
        sem_k("D", "qe3", "qs", "(xval D qe2 qs qd)", "qC")
    );
    let m_step = format!(
        "(fun (qe : KExpr) (qe2 : KExpr) (qe3 : KExpr) (qst : whnf_step qe qe2) (qrest : whnfStar qe2 qe3) {ih} (qs : Sk) (qd : WKC D qe qs) (qC : Type) (qk : {}) => r21_xval_step_sem D qe qs qd qe2 qst qC (fun (zh2 : WKC D qe2 qs) (zhv : forall (zr : VEnvD D), Eq (VD qs) (xval D qe2 qs zh2 zr) (xval D qe qs qd zr)) => qih qs zh2 qC (fun (zhw : WKC D qe3 qs) (zhv2 : forall (zr : VEnvD D), Eq (VD qs) (xval D qe3 qs zhw zr) (xval D qe2 qs zh2 zr)) => qk zhw (fun (zr : VEnvD D) => Eq.trans (VD qs) (xval D qe3 qs zhw zr) (xval D qe2 qs zh2 zr) (xval D qe qs qd zr) (zhv2 zr) (zhv zr)))))",
        sem_k("D", "qe3", "qs", "(xval D qe qs qd)", "qC")
    );
    format!("fun (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) => whnfStar.rec {mot} {m_refl} {m_step} e w hstar")
}

/// **`r22_xval_step_star`** — the ∀-form along a whole sequence. R16's
/// `val_step_star` with `PropBox` reused and `r17_xval_irrel` in place of
/// `r16_sval_irrel`.
pub(super) const TY_XVAL_STEP_STAR: &str = "forall (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) (s : Sk) (h : WKC D e s) (hw : WKC D w s) (r : VEnvD D), Eq (VD s) (xval D w s hw r) (xval D e s h r)";

pub(super) const VAL_XVAL_STEP_STAR: &str = "fun (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) (s : Sk) (h : WKC D e s) (hw : WKC D w s) (r : VEnvD D) => r16_unbox (Eq (VD s) (xval D w s hw r) (xval D e s h r)) (r22_xval_star_sem D e w hstar s h (PropBox (Eq (VD s) (xval D w s hw r) (xval D e s h r))) (fun (zhw : WKC D w s) (zhv : forall (zr : VEnvD D), Eq (VD s) (xval D w s zhw zr) (xval D e s h zr)) => r16_propBox_intro (Eq (VD s) (xval D w s hw r) (xval D e s h r)) (Eq.trans (VD s) (xval D w s hw r) (xval D w s zhw r) (xval D e s h r) (r17_xval_irrel D w s hw zhw r) (zhv r))))";

// ================================================================
// Group B — THE NATIVE CONVERSION LEMMA.
// ================================================================

/// **`r22_xval_conv`** — R16's unconditional `val_conv` at seven constructors.
///
/// **No `PropBox` here, and that is the structural point.** R16 needed the box
/// for `val_step` and `val_step_star` because their conclusions are `Eq`s,
/// which live in Prop, while the CPS continuation quantifies over `C : Type`.
/// `val_conv`'s conclusion is a MEMBERSHIP — `vcarD s v t` is a `Type` — so it
/// can be handed to `r22_xval_star_sem` as its own `C` directly, and the whole
/// lemma is one application of the star form, one `Eq.trans`, and one
/// `Eq.substType`.
///
/// It also needs no irrelevance hypothesis. R15 stated `val_conv` conditionally
/// on one (`r15_val_conv_from_irrel`) and R16 discharged it with
/// `r16_sval_irrel`; here the witness `zhw` the star form hands back is used at
/// BOTH reduction sequences, so the two interpretations are related without ever
/// comparing two derivations of one judgment.
pub(super) const TY_XVAL_CONV: &str = "forall (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WKC D e1 s) (h2 : WKC D e2 s) (r : VEnvD D) (t : KExpr), whnfStar e1 w -> whnfStar e2 w -> vcarD s (xval D e1 s h1 r) t -> vcarD s (xval D e2 s h2 r) t";

pub(super) const VAL_XVAL_CONV: &str = "fun (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WKC D e1 s) (h2 : WKC D e2 s) (r : VEnvD D) (t : KExpr) (st1 : whnfStar e1 w) (st2 : whnfStar e2 w) (hm : vcarD s (xval D e1 s h1 r) t) => r22_xval_star_sem D e1 w st1 s h1 (vcarD s (xval D e2 s h2 r) t) (fun (zhw : WKC D w s) (zhv : forall (zr : VEnvD D), Eq (VD s) (xval D w s zhw zr) (xval D e1 s h1 zr)) => Eq.substType (VD s) (fun (qv : VD s) => vcarD s qv t) (xval D e1 s h1 r) (xval D e2 s h2 r) (Eq.trans (VD s) (xval D e1 s h1 r) (xval D w s zhw r) (xval D e2 s h2 r) (Eq.symm (VD s) (xval D w s zhw r) (xval D e1 s h1 r) (zhv r)) (r22_xval_step_star D e2 w st2 s h2 zhw r)) hm)";

// ================================================================
// Group C — the drift checks and the reach witnesses.
// ================================================================

/// **`r22_conv_extends_transported`** — R18's `r18_xval_conv` TYPE proved with
/// R22's native VALUE.
pub(super) const TY_CONV_EXTENDS: &str = "forall (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WK D e1 s) (h2 : WK D e2 s) (r : VEnvD D) (t : KExpr), whnfStar e1 w -> whnfStar e2 w -> vcarD s (xval D e1 s (r17_wk_wkc D e1 s h1) r) t -> vcarD s (xval D e2 s (r17_wk_wkc D e2 s h2) r) t";

pub(super) const VAL_CONV_EXTENDS: &str = "fun (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WK D e1 s) (h2 : WK D e2 s) (r : VEnvD D) (t : KExpr) (st1 : whnfStar e1 w) (st2 : whnfStar e2 w) (hm : vcarD s (xval D e1 s (r17_wk_wkc D e1 s h1) r) t) => r22_xval_conv D e1 e2 w s (r17_wk_wkc D e1 s h1) (r17_wk_wkc D e2 s h2) r t st1 st2 hm";

/// **`r22_step_star_extends_transported`** — the same for R18's
/// `r18_xval_step_star`.
pub(super) const TY_STAR_EXTENDS: &str = "forall (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) (s : Sk) (h : WK D e s) (hw : WK D w s) (r : VEnvD D), Eq (VD s) (xval D w s (r17_wk_wkc D w s hw) r) (xval D e s (r17_wk_wkc D e s h) r)";

pub(super) const VAL_STAR_EXTENDS: &str = "fun (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) (s : Sk) (h : WK D e s) (hw : WK D w s) (r : VEnvD D) => r22_xval_step_star D e w hstar s (r17_wk_wkc D e s h) (r17_wk_wkc D w s hw) r";

/// R17's `let_` witness reduces to its ζ contractum in ONE step, hence in one
/// `whnfStar` link. The object every witness below is stated at.
pub(super) fn src_let_star() -> String {
    format!("def r22_letStar : whnfStar r17_letTerm {INST0} := whnfStar.step r17_letTerm {INST0} {INST0} (whnf_step.beta r17_letTerm {INST0} (beta_reduces.zeta {S0} {S0} {V0})) (whnfStar.refl {INST0})")
}

/// **`r22_step_star_reaches_let`** — the ∀-form star law at that ζ sequence.
pub(super) fn ty_star_reaches_let() -> String {
    format!("forall (r : VEnvD r12_betaEnv), Eq (VD {KDTY}) (xval r12_betaEnv {INST0} {KDTY} r17_wkc_step_let_witness r) (xval r12_betaEnv r17_letTerm {KDTY} r17_let_witness r)")
}

pub(super) fn val_star_reaches_let() -> String {
    format!("fun (r : VEnvD r12_betaEnv) => r22_xval_step_star r12_betaEnv r17_letTerm {INST0} r22_letStar {KDTY} r17_let_witness r17_wkc_step_let_witness r")
}

/// **`r22_conv_reaches_let`** — CONVERSION across that ζ step, at a real
/// membership.
///
/// The `let_` term and its contractum share the reduct `INST0` — the term by
/// one ζ step, the contractum reflexively — so `r22_xval_conv` carries any
/// membership from one to the other. Stated as a function of the membership
/// rather than at a fixed inhabitant, because what the rung claims is the
/// TRANSPORT and not the existence of a particular element.
pub(super) fn ty_conv_reaches_let() -> String {
    format!("forall (r : VEnvD r12_betaEnv) (t : KExpr), vcarD {KDTY} (xval r12_betaEnv r17_letTerm {KDTY} r17_let_witness r) t -> vcarD {KDTY} (xval r12_betaEnv {INST0} {KDTY} r17_wkc_step_let_witness r) t")
}

pub(super) fn val_conv_reaches_let() -> String {
    format!("fun (r : VEnvD r12_betaEnv) (t : KExpr) (hm : vcarD {KDTY} (xval r12_betaEnv r17_letTerm {KDTY} r17_let_witness r) t) => r22_xval_conv r12_betaEnv r17_letTerm {INST0} {INST0} {KDTY} r17_let_witness r17_wkc_step_let_witness r t r22_letStar (whnfStar.refl {INST0}) hm")
}

// ================================================================
// Group D — negative controls. NOT registered.
// ================================================================

/// The conversion lemma with the SECOND reduction premise dropped, proved by
/// simply returning the membership. It must be refused: without `whnfStar e2 w`
/// the two terms need share no reduct at all, and the statement would say the
/// interpretations of arbitrary same-shaped terms have the same inhabitants.
#[cfg(test)]
pub(super) fn probe_conv_without_second_star() -> String {
    "def r22_conv_one_star_probe : forall (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WKC D e1 s) (h2 : WKC D e2 s) (r : VEnvD D) (t : KExpr), whnfStar e1 w -> vcarD s (xval D e1 s h1 r) t -> vcarD s (xval D e2 s h2 r) t := fun (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WKC D e1 s) (h2 : WKC D e2 s) (r : VEnvD D) (t : KExpr) (st1 : whnfStar e1 w) (hm : vcarD s (xval D e1 s h1 r) t) => hm".to_string()
}

/// The star law with `Eq.refl` for a proof. Both sides are `WKC.rec` stuck on
/// different variable derivations, so the kernel must refuse.
#[cfg(test)]
pub(super) fn probe_star_refl() -> String {
    format!("def r22_star_refl_probe : {TY_XVAL_STEP_STAR} := fun (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) (s : Sk) (h : WKC D e s) (hw : WKC D w s) (r : VEnvD D) => Eq.refl (VD s) (xval D w s hw r)")
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R22Item {
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
impl R22Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R22Item::Def { name, .. } | R22Item::Thm { name, .. } => name,
        }
    }

    pub(super) fn decl_source(&self) -> String {
        match self {
            R22Item::Def { src, .. } => src.clone(),
            R22Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn d(name: &str, src: String) -> R22Item {
    R22Item::Def {
        name: name.to_string(),
        src,
    }
}

fn t(name: &str, ty: String, val: String) -> R22Item {
    R22Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R22 constant, in registration order.
pub(super) fn r22_items() -> Vec<R22Item> {
    vec![
        t("r22_xval_star_sem", ty_xval_star_sem(), val_xval_star_sem()),
        t(
            "r22_xval_step_star",
            TY_XVAL_STEP_STAR.to_string(),
            VAL_XVAL_STEP_STAR.to_string(),
        ),
        t(
            "r22_xval_conv",
            TY_XVAL_CONV.to_string(),
            VAL_XVAL_CONV.to_string(),
        ),
        t(
            "r22_step_star_extends_transported",
            TY_STAR_EXTENDS.to_string(),
            VAL_STAR_EXTENDS.to_string(),
        ),
        t(
            "r22_conv_extends_transported",
            TY_CONV_EXTENDS.to_string(),
            VAL_CONV_EXTENDS.to_string(),
        ),
        d("r22_letStar", src_let_star()),
        t(
            "r22_step_star_reaches_let",
            ty_star_reaches_let(),
            val_star_reaches_let(),
        ),
        t(
            "r22_conv_reaches_let",
            ty_conv_reaches_let(),
            val_conv_reaches_let(),
        ),
    ]
}

#[cfg(test)]
pub(super) fn r22_all_sources() -> Vec<(String, String)> {
    r22_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
