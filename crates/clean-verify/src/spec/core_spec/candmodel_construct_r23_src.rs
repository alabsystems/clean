// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R23 sources — **ADEQUACY AND NORMALIZATION at seven constructors**: every
//! `WKC`-typed term's interpretation is a GOOD value, hence a candidate, hence
//! every member of it is `whnf_acc`.
//!
//! See the module doc of [`super::candmodel_construct_r23`] for the argument.

// **This module deliberately imports nothing** — the R12-R22 convention.

/// R12's `TOPSET`.
#[cfg(test)]
const TOPSET: &str = "(fun (qe : KExpr) => whnf_acc qe)";
/// R12's `KDTY`.
const KDTY: &str = "(Sk.kd Sk.ty)";
/// R17's `DEADCONST`.
const DEADCONST: &str = "(KExpr.const fixture_def_env_name (@ListType.nil Level))";

/// R10/R17's first inertness premise, at the constant `n`.
fn defval_none(n: &str) -> String {
    format!(
        "@Eq (OptionType KExpr) (defval_for (red_def the_red_env) {n}) (@OptionType.none KExpr)"
    )
}

/// R10/R17's second inertness premise, at the constant `n`.
fn recmeta_none(n: &str) -> String {
    format!(
        "@Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) {n}) (@OptionType.none RecMeta)"
    )
}

// ================================================================
// Group A — ADEQUACY.
// ================================================================

/// **`r23_xval_good` — R12's `sval_good` at SEVEN constructors.**
///
/// Every `WKC` derivation's interpretation, at a GOOD valuation, is a GOOD
/// value. `GoodD` is the logical relation: at `ty` and `kd` it is candidacy of
/// the denoted SET, and at an arrow it is the real function-space clause
/// (`forall x, GoodD d x -> GoodD c (f x)`).
pub(super) const TY_XVAL_GOOD: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (r : VEnvD D), GoodEnvD D r -> GoodD s (xval D e s h r)";

/// The proof: `WKC.rec` at seven arms, R12's five plus `konst` and `let_`.
#[allow(clippy::too_many_lines)]
pub(super) fn val_xval_good() -> String {
    let motive = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => forall (qr : VEnvD qD), GoodEnvD qD qr -> GoodD qs (xval qD qe qs qh qr))";
    let m_var =
        "(fun (qD : Nat -> Sk) (qi : Nat) (qr : VEnvD qD) (qhr : GoodEnvD qD qr) => qhr qi)";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) (qr : VEnvD qD) (qhr : GoodEnvD qD qr) => goodSet_whnfAcc)";

    // --- pi ---
    let dsa = "(skcons (domSk qsA) qD)";
    let ca = "(vcarD qsA (xval qD qA qsA qhA qr))";
    let jenv = "(vconsD (domSk qsA) qD (junkD (domSk qsA)) qr)";
    let cbc = format!("(vcarD qsB (xval {dsa} qB qsB qhB {jenv}))");
    let cb = format!("(fun (qa : KExpr) => {cbc})");
    let set = format!("(PiSet {ca} {cb})");
    let hca = "(isCandHI_vcarD qsA (xval qD qA qsA qhA qr) (qihgA qr qhr))";
    let hgood_jenv =
        "(goodEnvD_vconsD (domSk qsA) qD (junkD (domSk qsA)) qr (goodD_junkD (domSk qsA)) qhr)";
    let hcb = format!("(fun (qa2 : KExpr) (qm : {ca} qa2) => isCandHI_vcarD qsB (xval {dsa} qB qsB qhB {jenv}) (qihgB {jenv} {hgood_jenv}))");
    let hinv = format!("(fun (qa1 : KExpr) (qa2 : KExpr) (qw : KExpr) (qm1 : {ca} qa1) (qst : whnf_step qa1 qa2) (qm : {cbc} qw) => qm)");
    let ih_a =
        "(qihgA : forall (qr2 : VEnvD qD), GoodEnvD qD qr2 -> GoodD qsA (xval qD qA qsA qhA qr2))";
    let ih_b = format!("(qihgB : forall (qr2 : VEnvD {dsa}), GoodEnvD {dsa} qr2 -> GoodD qsB (xval {dsa} qB qsB qhB qr2))");
    let m_pi = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC {dsa} qB qsB) {ih_a} {ih_b} (qr : VEnvD qD) (qhr : GoodEnvD qD qr) => goodD_mkTyD qsA qsB {set} (isCandHI_piSet {ca} {cb} {hca} {hcb} {hinv}))");

    // --- lam ---
    let ih_lb = format!("(qihgb : forall (qr2 : VEnvD {dsa}), GoodEnvD {dsa} qr2 -> GoodD qc (xval {dsa} qb qc qhb qr2))");
    let m_lam = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC {dsa} qb qc) {ih_a} {ih_lb} (qr : VEnvD qD) (qhr : GoodEnvD qD qr) (qx : VD (domSk qsA)) (qhx : GoodD (domSk qsA) qx) => qihgb (vconsD (domSk qsA) qD qx qr) (goodEnvD_vconsD (domSk qsA) qD qx qr qhx qhr))");

    // --- app ---
    let ih_af = "(qihgf : forall (qr2 : VEnvD qD), GoodEnvD qD qr2 -> GoodD (Sk.arr qd qcc) (xval qD qf (Sk.arr qd qcc) qhf qr2))";
    let ih_aa =
        "(qihga : forall (qr2 : VEnvD qD), GoodEnvD qD qr2 -> GoodD qd (xval qD qa qd qha qr2))";
    let m_app = format!("(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) {ih_af} {ih_aa} (qr : VEnvD qD) (qhr : GoodEnvD qD qr) => qihgf qr qhr (xval qD qa qd qha qr) (qihga qr qhr))");

    // --- konst: the TOP candidate is good, and that is the whole arm ---
    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhrm : {}) (qr : VEnvD qD) (qhr : GoodEnvD qD qr) => goodSet_whnfAcc)",
        defval_none("qn"),
        recmeta_none("qn")
    );

    // --- let_: the body at the valuation extended by the VALUE's interpretation ---
    let ldd = "(skcons qsv qD)";
    let ih_t =
        "(qihgt : forall (qr2 : VEnvD qD), GoodEnvD qD qr2 -> GoodD qst (xval qD qtt qst qht qr2))";
    let ih_v =
        "(qihgv : forall (qr2 : VEnvD qD), GoodEnvD qD qr2 -> GoodD qsv (xval qD qv qsv qhv qr2))";
    let ih_bl = format!("(qihgb : forall (qr2 : VEnvD {ldd}), GoodEnvD {ldd} qr2 -> GoodD qc (xval {ldd} qb qc qhb qr2))");
    let xv = "(xval qD qv qsv qhv qr)";
    let m_let = format!("(fun (qD : Nat -> Sk) (qtt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qtt qst) (qhv : WKC qD qv qsv) (qhb : WKC {ldd} qb qc) {ih_t} {ih_v} {ih_bl} (qr : VEnvD qD) (qhr : GoodEnvD qD qr) => qihgb (vconsD qsv qD {xv} qr) (goodEnvD_vconsD qsv qD {xv} qr (qihgv qr qhr) qhr))");

    format!("fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) => @WKC.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h")
}

// ================================================================
// Group B — CANDIDACY and NORMALIZATION.
// ================================================================

/// **`r23_isCandHI_xval`** — the SET a `WKC`-typed term denotes is a candidate.
pub(super) const TY_ISCANDHI_XVAL: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (r : VEnvD D), GoodEnvD D r -> IsCandHI (vcarD s (xval D e s h r))";

pub(super) const VAL_ISCANDHI_XVAL: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (r : VEnvD D) (hr : GoodEnvD D r) => isCandHI_vcarD s (xval D e s h r) (r23_xval_good D e s h r hr)";

/// **`r23_xval_members_sn` — NORMALIZATION.** Every member of the candidate a
/// `WKC`-typed term denotes is `whnf_acc`: accessible under `whnf_step`, i.e.
/// it has no infinite reduction sequence.
///
/// Off `isCandHI_cr1`, the first candidate condition. It is unconditional —
/// there is no `CandModel` hypothesis anywhere in its closure — but read the
/// module doc before quoting it, because what it quantifies over is narrower
/// than "the kernel's terms".
pub(super) const TY_XVAL_MEMBERS_SN: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (r : VEnvD D), GoodEnvD D r -> forall (x : KExpr), vcarD s (xval D e s h r) x -> whnf_acc x";

pub(super) const VAL_XVAL_MEMBERS_SN: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (r : VEnvD D) (hr : GoodEnvD D r) => isCandHI_cr1 (vcarD s (xval D e s h r)) (r23_isCandHI_xval D e s h r hr)";

/// **`r23_xval_excludes_omega`** — the looping term is in NO such candidate.
///
/// R12's `sval_excludes_omega` at seven constructors. This is the half that
/// makes the normalization theorem say something: a candidate that contained Ω
/// would make `members_sn` false, and an EMPTY candidate would make it vacuous.
pub(super) const TY_XVAL_EXCLUDES_OMEGA: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (r : VEnvD D), GoodEnvD D r -> vcarD s (xval D e s h r) r5_omegaV -> Empty";

pub(super) const VAL_XVAL_EXCLUDES_OMEGA: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (r : VEnvD D) (hr : GoodEnvD D r) (hm : vcarD s (xval D e s h r) r5_omegaV) => r5_omegaV_not_whnfAcc (r23_xval_members_sn D e s h r hr r5_omegaV hm)";

// ================================================================
// Group C — the drift check and the object-level witnesses.
// ================================================================

/// **`r23_good_reproves_sval_good`** — R12's `sval_good` STATEMENT, re-proved
/// from R23's native theorem through R18's transfer.
///
/// Two genuinely different proofs of one statement: R12's induction on `WK`,
/// and this rung's induction on `WKC` pushed across `r18_xval_sval`. A rung
/// that widened the system while drifting the adequacy statement would be
/// invisible without it.
pub(super) const TY_GOOD_REPROVES: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D), GoodEnvD D r -> GoodD s (sval D e s h r)";

pub(super) const VAL_GOOD_REPROVES: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D) (hr : GoodEnvD D r) => @Eq.substType (VD s) (fun (qv : VD s) => GoodD s qv) (xval D e s (r17_wk_wkc D e s h) r) (sval D e s h r) (r18_xval_sval D e s h r) (r23_xval_good D e s (r17_wk_wkc D e s h) r hr)";

/// **`r23_sn_fires_at_konst`** — the normalization theorem CONCLUDING, at a
/// real object.
///
/// R17 registered `r17_konst_mem_witness`, an inhabitant of the candidate its
/// `konst` witness denotes. Feeding it to `r23_xval_members_sn` yields
/// `whnf_acc` of that constant — so the candidate is INHABITED and the theorem
/// fires on it, which is what separates a normalization result from a vacuous
/// one.
pub(super) fn ty_sn_fires_at_konst() -> String {
    format!("whnf_acc {DEADCONST}")
}

pub(super) fn val_sn_fires_at_konst() -> String {
    format!("r23_xval_members_sn r12_piEnv {DEADCONST} Sk.ty r17_konst_witness (r12_junkEnv r12_piEnv) (goodEnvD_junk r12_piEnv) {DEADCONST} r17_konst_mem_witness")
}

/// **`r23_omega_excluded_at_let`** — Ω is not in the candidate R17's `let_`
/// witness denotes. The `let_` half of the exclusion, at an object.
pub(super) fn ty_omega_excluded_at_let() -> String {
    format!("vcarD {KDTY} (xval r12_betaEnv r17_letTerm {KDTY} r17_let_witness (r12_junkEnv r12_betaEnv)) r5_omegaV -> Empty")
}

pub(super) fn val_omega_excluded_at_let() -> String {
    format!("r23_xval_excludes_omega r12_betaEnv r17_letTerm {KDTY} r17_let_witness (r12_junkEnv r12_betaEnv) (goodEnvD_junk r12_betaEnv)")
}

/// **`r23_omega_excluded_at_konst`** — the same at the `konst` witness.
pub(super) fn ty_omega_excluded_at_konst() -> String {
    format!("vcarD Sk.ty (xval r12_piEnv {DEADCONST} Sk.ty r17_konst_witness (r12_junkEnv r12_piEnv)) r5_omegaV -> Empty")
}

pub(super) fn val_omega_excluded_at_konst() -> String {
    format!("r23_xval_excludes_omega r12_piEnv {DEADCONST} Sk.ty r17_konst_witness (r12_junkEnv r12_piEnv) (goodEnvD_junk r12_piEnv)")
}

/// **`r23_vcar_arr_is_top` — THE SCOPE OF ALL OF IT, computed.**
///
/// `vcarD` at an ARROW shape DISCARDS its value and returns the top candidate:
/// `vcarD (Sk.arr d c) f e` is `whnf_acc e` for every `f`. `Eq.refl` proves it,
/// which is the point — it is a computation, not a theorem.
///
/// Consequences that must travel with every membership statement in R18-R23:
/// at an arrow shape `vcarD s (xval …) x` carries NO information about the
/// interpretation, so `r23_xval_members_sn` there degenerates to `whnf_acc x →
/// whnf_acc x` and `r22_xval_conv` degenerates to the identity. The content of
/// the membership-shaped results lives at `ty` and `kd` shapes, where `vcarD`
/// IS the denoted set.
pub(super) const TY_VCAR_ARR_IS_TOP: &str = "forall (d : Sk) (c : Sk) (f : VD (Sk.arr d c)) (e : KExpr), @Eq Type (vcarD (Sk.arr d c) f e) (whnf_acc e)";

pub(super) const VAL_VCAR_ARR_IS_TOP: &str =
    "fun (d : Sk) (c : Sk) (f : VD (Sk.arr d c)) (e : KExpr) => @Eq.refl Type (whnf_acc e)";

/// **`r23_vcar_ty_is_the_set`** — the other half, also `Eq.refl`: at `ty` the
/// candidate IS the denoted set, so nothing is discarded there. Registered
/// beside its sibling so the two states are named apart rather than left for a
/// reader to infer from one of them.
pub(super) const TY_VCAR_TY_IS_SET: &str =
    "forall (C : VD Sk.ty) (e : KExpr), @Eq Type (vcarD Sk.ty C e) (C e)";

pub(super) const VAL_VCAR_TY_IS_SET: &str = "fun (C : VD Sk.ty) (e : KExpr) => @Eq.refl Type (C e)";

// ================================================================
// Group D — negative controls. NOT registered.
// ================================================================

/// The `GoodEnvD` premise, dropped. Its `var` arm needs exactly that premise —
/// the valuation's entries need not be good otherwise — so the kernel must
/// refuse this, which is the measurement that adequacy is not free.
#[cfg(test)]
pub(super) fn probe_good_without_env() -> String {
    "def r23_good_no_env_probe : forall (D : Nat -> Sk) (i : Nat) (r : VEnvD D), GoodD (D i) (r i) := fun (D : Nat -> Sk) (i : Nat) (r : VEnvD D) => goodSet_whnfAcc".to_string()
}

/// `vcarD` claimed to collapse at `ty` the way it does at an arrow. It must be
/// refused for a general `C`: if it were accepted, every membership statement
/// in R18-R23 would be the top candidate in disguise and the whole
/// normalization result would say nothing.
#[cfg(test)]
pub(super) fn probe_vcar_ty_collapses() -> String {
    format!("def r23_vcar_ty_collapse_probe : forall (C : VD Sk.ty) (e : KExpr), @Eq Type (vcarD Sk.ty C e) (whnf_acc e) := fun (C : VD Sk.ty) (e : KExpr) => @Eq.refl Type {TOPSET}")
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R23Item {
    Thm {
        name: String,
        ty: String,
        val: String,
    },
}

#[cfg(test)]
impl R23Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R23Item::Thm { name, .. } => name,
        }
    }

    pub(super) fn decl_source(&self) -> String {
        match self {
            R23Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn t(name: &str, ty: String, val: String) -> R23Item {
    R23Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R23 constant, in registration order.
pub(super) fn r23_items() -> Vec<R23Item> {
    vec![
        t("r23_xval_good", TY_XVAL_GOOD.to_string(), val_xval_good()),
        t(
            "r23_isCandHI_xval",
            TY_ISCANDHI_XVAL.to_string(),
            VAL_ISCANDHI_XVAL.to_string(),
        ),
        t(
            "r23_xval_members_sn",
            TY_XVAL_MEMBERS_SN.to_string(),
            VAL_XVAL_MEMBERS_SN.to_string(),
        ),
        t(
            "r23_xval_excludes_omega",
            TY_XVAL_EXCLUDES_OMEGA.to_string(),
            VAL_XVAL_EXCLUDES_OMEGA.to_string(),
        ),
        t(
            "r23_good_reproves_sval_good",
            TY_GOOD_REPROVES.to_string(),
            VAL_GOOD_REPROVES.to_string(),
        ),
        t(
            "r23_sn_fires_at_konst",
            ty_sn_fires_at_konst(),
            val_sn_fires_at_konst(),
        ),
        t(
            "r23_omega_excluded_at_konst",
            ty_omega_excluded_at_konst(),
            val_omega_excluded_at_konst(),
        ),
        t(
            "r23_omega_excluded_at_let",
            ty_omega_excluded_at_let(),
            val_omega_excluded_at_let(),
        ),
        t(
            "r23_vcar_arr_is_top",
            TY_VCAR_ARR_IS_TOP.to_string(),
            VAL_VCAR_ARR_IS_TOP.to_string(),
        ),
        t(
            "r23_vcar_ty_is_the_set",
            TY_VCAR_TY_IS_SET.to_string(),
            VAL_VCAR_TY_IS_SET.to_string(),
        ),
    ]
}

#[cfg(test)]
pub(super) fn r23_all_sources() -> Vec<(String, String)> {
    r23_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
