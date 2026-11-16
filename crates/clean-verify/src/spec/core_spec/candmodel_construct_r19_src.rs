// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R19 sources — **THE FIRST NATIVE SEMANTIC LEMMA**: `val_lift` proved by
//! induction on `WKC`, so it holds at `konst` and `let_` derivations, which
//! R18's transported `r18_xval_lift` cannot reach.
//!
//! See the module doc of [`super::candmodel_construct_r19`] for the argument.

// **This module deliberately imports nothing** — the R12-R18 convention, so the
// whole file can be `#[path]`-included into a scratch crate that depends only on
// `clean-parser` and parse-checked in a second.

/// The lift amount `wkc_lift` is stated at.
const ONE: &str = "(Nat.succ Nat.zero)";
/// R12's `KDTY`.
const KDTY: &str = "(Sk.kd Sk.ty)";
/// R17's `DEADCONST` — the real inert reflected constant its `konst` witness
/// is built at. Re-declared, not imported, per this file's no-imports rule.
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
// Group A — the `var` arm, bought with R18's transfer.
// ================================================================

/// **`r19_xval_wkc_lift_var`** — the interpretation of `r17_wkc_lift_var`.
///
/// R14 needed a four-step proof here, through two `sval`-side cast lemmas
/// (`r14_sval_cast_term`, `r14_sval_cast_shape`), because the lifted variable
/// derivation is a term cast wrapped around a shape cast wrapped around
/// `WK.var`. **This rung needs none of them**, and that is R18's transfer doing
/// visible work rather than sitting in a ledger: `r17_wkc_lift_var` and the
/// EMBEDDING of `r14_wk_lift_var` derive the same judgment, so R17's
/// subsingleton equates their interpretations, the transfer moves one of them to
/// `sval`, and `r14_sval_wk_lift_var` finishes. Three steps, no new cast lemma,
/// and no `xval`-side transport machinery at all.
pub(super) fn ty_xval_wkc_lift_var() -> String {
    format!("forall (c : Nat) (i : Nat) (t : Sk) (D : Nat -> Sk) (r : VEnvD (skins c t D)), @Eq (VD (D i)) (xval (skins c t D) (lift_at (KExpr.bvar i) c {ONE}) (D i) (r17_wkc_lift_var c i t D) r) (venvLiftD c t D r i)")
}

pub(super) fn val_xval_wkc_lift_var() -> String {
    let ek = "(skins c t D)";
    let le = format!("(lift_at (KExpr.bvar i) c {ONE})");
    let wk_var = "(r14_wk_lift_var c i t D)";
    let a = format!("(xval {ek} {le} (D i) (r17_wkc_lift_var c i t D) r)");
    let b = format!("(xval {ek} {le} (D i) (r17_wk_wkc {ek} {le} (D i) {wk_var}) r)");
    let c = format!("(sval {ek} {le} (D i) {wk_var} r)");
    format!("fun (c : Nat) (i : Nat) (t : Sk) (D : Nat -> Sk) (r : VEnvD {ek}) => @Eq.trans (VD (D i)) {a} {b} (venvLiftD c t D r i) (r17_xval_irrel {ek} {le} (D i) (r17_wkc_lift_var c i t D) (r17_wk_wkc {ek} {le} (D i) {wk_var}) r) (@Eq.trans (VD (D i)) {b} {c} (venvLiftD c t D r i) (r18_xval_sval {ek} {le} (D i) {wk_var} r) (r14_sval_wk_lift_var c i t D r))")
}

// ================================================================
// Group B — THE NATIVE LEMMA.
// ================================================================

/// **`r19_xval_lift` — R14's `val_lift` at SEVEN constructors.**
///
/// Same statement as `r18_xval_lift` with one binder changed, and that binder
/// is the whole rung: `h : WKC D e s` where R18 has `h : WK D e s`. The
/// left-hand side reads `wkc_lift` at the derivation itself, not at an
/// embedding, so there is nothing left scoping the theorem to the image of
/// `r17_wk_wkc`.
pub(super) fn ty_xval_lift_native() -> String {
    format!("forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (k : Nat) (ins : Sk) (r : VEnvD (skins k ins D)), @Eq (VD s) (xval (skins k ins D) (lift_at e k {ONE}) s (wkc_lift D e s h k ins) r) (xval D e s h (venvLiftD k ins D r))")
}

/// The native proof: `WKC.rec` at seven arms.
///
/// The five old arms are R14's `val_lift` arms with `sval` replaced by `xval`
/// and `wk_lift` by `wkc_lift` — the congruence helpers (`r14_sval_pi_congr`,
/// `r14_vapply_congr`, `r13_vd_arr_funext`) and the valuation lemma
/// (`r14_venvLift_vcons`) are reused VERBATIM, because every one of them is a
/// statement about VALUES and valuations and none mentions a derivation.
///
/// The two new arms:
///
/// * **`konst` — `Eq.refl`, and for a reason worth stating.** `lift_at` leaves a
///   constant alone, `wkc_lift`'s `konst` arm rebuilds `WKC.konst` at the
///   extended shape environment with the same two inertness proofs, and `xval`'s
///   `konst` clause discards its valuation entirely (an inert constant denotes
///   the TOP candidate). So both sides are literally `fun e => whnf_acc e` and
///   the weakening lemma has nothing to say — which is the correct content, not
///   a gap.
/// * **`let_` — three steps, one more than `lam`.** `xval`'s `let_` clause reads
///   the valuation extended by the VALUE'S interpretation, so after the body's
///   induction hypothesis and `r14_venvLift_vcons` there is a third congruence,
///   in the extension value, discharged by the VALUE's induction hypothesis. The
///   annotation's hypothesis is unused: `xval` does not read the annotation.
#[allow(clippy::too_many_lines)]
pub(super) fn val_xval_lift_native() -> String {
    let ek = "(skins qk qins qD)";
    let rl = "(venvLiftD qk qins qD qr)";

    let motive = format!("(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => forall (qk : Nat) (qins : Sk) (qr : VEnvD {ek}), @Eq (VD qs) (xval {ek} (lift_at qe qk {ONE}) qs (wkc_lift qD qe qs qh qk qins) qr) (xval qD qe qs qh {rl}))");

    let m_var = format!("(fun (qD : Nat -> Sk) (qi : Nat) (qk : Nat) (qins : Sk) (qr : VEnvD {ek}) => r19_xval_wkc_lift_var qk qi qins qD qr)");
    let m_sort = format!("(fun (qD : Nat -> Sk) (qn : Level) (qk : Nat) (qins : Sk) (qr : VEnvD {ek}) => @Eq.refl (VD {KDTY}) (fun (qe2 : KExpr) => whnf_acc qe2))");

    // The annotation hypothesis, shared by `pi` and `lam`.
    let db = "(skcons (domSk qsA) qD)";
    let ih_a = format!("(qihA : forall (qk : Nat) (qins : Sk) (qr : VEnvD {ek}), @Eq (VD qsA) (xval {ek} (lift_at qA qk {ONE}) qsA (wkc_lift qD qA qsA qhA qk qins) qr) (xval qD qA qsA qhA {rl}))");
    let p_va = format!("(xval {ek} (lift_at qA qk {ONE}) qsA (wkc_lift qD qA qsA qhA qk qins) qr)");
    let p_va2 = format!("(xval qD qA qsA qhA {rl})");

    // --- pi ---
    let ekb = format!("(skins (Nat.succ qk) qins {db})");
    let ih_pb = format!("(qihB : forall (qk : Nat) (qins : Sk) (qr : VEnvD (skins qk qins {db})), @Eq (VD qsB) (xval (skins qk qins {db}) (lift_at qB qk {ONE}) qsB (wkc_lift {db} qB qsB qhB qk qins) qr) (xval {db} qB qsB qhB (venvLiftD qk qins {db} qr)))");
    let jb = "(junkD (domSk qsA))";
    let yb = format!("(vconsD (domSk qsA) {ek} {jb} qr)");
    let p_vb = format!("(xval {ekb} (lift_at qB (Nat.succ qk) {ONE}) qsB (wkc_lift {db} qB qsB qhB (Nat.succ qk) qins) {yb})");
    let p_mid = format!("(xval {db} qB qsB qhB (venvLiftD (Nat.succ qk) qins {db} {yb}))");
    let p_vb2 = format!("(xval {db} qB qsB qhB (vconsD (domSk qsA) qD {jb} {rl}))");
    let p_cong = format!("(@Eq.cong (VEnvD {db}) (VD qsB) (fun (qrr : VEnvD {db}) => xval {db} qB qsB qhB qrr) (venvLiftD (Nat.succ qk) qins {db} {yb}) (vconsD (domSk qsA) qD {jb} {rl}) (r14_venvLift_vcons qk qins (domSk qsA) qD {jb} qr))");
    let p_hb = format!(
        "(@Eq.trans (VD qsB) {p_vb} {p_mid} {p_vb2} (qihB (Nat.succ qk) qins {yb}) {p_cong})"
    );
    let m_pi = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC {db} qB qsB) {ih_a} {ih_pb} (qk : Nat) (qins : Sk) (qr : VEnvD {ek}) => r14_sval_pi_congr qsA qsB {p_va} {p_va2} {p_vb} {p_vb2} (qihA qk qins qr) {p_hb})");

    // --- lam ---
    let ih_lb = format!("(qihb : forall (qk : Nat) (qins : Sk) (qr : VEnvD (skins qk qins {db})), @Eq (VD qc) (xval (skins qk qins {db}) (lift_at qb qk {ONE}) qc (wkc_lift {db} qb qc qhb qk qins) qr) (xval {db} qb qc qhb (venvLiftD qk qins {db} qr)))");
    let lam_t = "(KExpr.lam qA qb)";
    let lam_s = "(Sk.arr (domSk qsA) qc)";
    let lam_d = "(WKC.lam qD qA qb qsA qc qhA qhb)";
    let l_f = format!("(xval {ek} (lift_at {lam_t} qk {ONE}) {lam_s} (wkc_lift qD {lam_t} {lam_s} {lam_d} qk qins) qr)");
    let l_g = format!("(xval qD {lam_t} {lam_s} {lam_d} {rl})");
    let yx = format!("(vconsD (domSk qsA) {ek} qx qr)");
    let l_x1 = format!("(xval {ekb} (lift_at qb (Nat.succ qk) {ONE}) qc (wkc_lift {db} qb qc qhb (Nat.succ qk) qins) {yx})");
    let l_x2 = format!("(xval {db} qb qc qhb (venvLiftD (Nat.succ qk) qins {db} {yx}))");
    let l_x3 = format!("(xval {db} qb qc qhb (vconsD (domSk qsA) qD qx {rl}))");
    let l_cong = format!("(@Eq.cong (VEnvD {db}) (VD qc) (fun (qrr : VEnvD {db}) => xval {db} qb qc qhb qrr) (venvLiftD (Nat.succ qk) qins {db} {yx}) (vconsD (domSk qsA) qD qx {rl}) (r14_venvLift_vcons qk qins (domSk qsA) qD qx qr))");
    let l_point = format!("(fun (qx : VD (domSk qsA)) => @Eq.trans (VD qc) {l_x1} {l_x2} {l_x3} (qihb (Nat.succ qk) qins {yx}) {l_cong})");
    let m_lam = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC {db} qb qc) {ih_a} {ih_lb} (qk : Nat) (qins : Sk) (qr : VEnvD {ek}) => r13_vd_arr_funext (domSk qsA) qc {l_f} {l_g} {l_point})");

    // --- app ---
    let arr = "(Sk.arr qd qcc)";
    let ih_f = format!("(qihf : forall (qk : Nat) (qins : Sk) (qr : VEnvD {ek}), @Eq (VD {arr}) (xval {ek} (lift_at qf qk {ONE}) {arr} (wkc_lift qD qf {arr} qhf qk qins) qr) (xval qD qf {arr} qhf {rl}))");
    let ih_ar = format!("(qiha : forall (qk : Nat) (qins : Sk) (qr : VEnvD {ek}), @Eq (VD qd) (xval {ek} (lift_at qa qk {ONE}) qd (wkc_lift qD qa qd qha qk qins) qr) (xval qD qa qd qha {rl}))");
    let a_f =
        format!("(xval {ek} (lift_at qf qk {ONE}) {arr} (wkc_lift qD qf {arr} qhf qk qins) qr)");
    let a_f2 = format!("(xval qD qf {arr} qhf {rl})");
    let a_x = format!("(xval {ek} (lift_at qa qk {ONE}) qd (wkc_lift qD qa qd qha qk qins) qr)");
    let a_x2 = format!("(xval qD qa qd qha {rl})");
    let m_app = format!("(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf {arr}) (qha : WKC qD qa qd) {ih_f} {ih_ar} (qk : Nat) (qins : Sk) (qr : VEnvD {ek}) => r14_vapply_congr qd qcc {a_f} {a_f2} {a_x} {a_x2} (qihf qk qins qr) (qiha qk qins qr))");

    // --- konst ---
    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) (qk : Nat) (qins : Sk) (qr : VEnvD {ek}) => @Eq.refl (VD Sk.ty) (fun (qe2 : KExpr) => whnf_acc qe2))",
        defval_none("qn"),
        recmeta_none("qn")
    );

    // --- let_ ---
    let dbl = "(skcons qsv qD)";
    let ekbl = format!("(skins (Nat.succ qk) qins {dbl})");
    let ih_t = format!("(qiht : forall (qk : Nat) (qins : Sk) (qr : VEnvD {ek}), @Eq (VD qst) (xval {ek} (lift_at qtt qk {ONE}) qst (wkc_lift qD qtt qst qht qk qins) qr) (xval qD qtt qst qht {rl}))");
    let ih_v = format!("(qihv : forall (qk : Nat) (qins : Sk) (qr : VEnvD {ek}), @Eq (VD qsv) (xval {ek} (lift_at qv qk {ONE}) qsv (wkc_lift qD qv qsv qhv qk qins) qr) (xval qD qv qsv qhv {rl}))");
    let ih_bl = format!("(qihb : forall (qk : Nat) (qins : Sk) (qr : VEnvD (skins qk qins {dbl})), @Eq (VD qc) (xval (skins qk qins {dbl}) (lift_at qb qk {ONE}) qc (wkc_lift {dbl} qb qc qhb qk qins) qr) (xval {dbl} qb qc qhb (venvLiftD qk qins {dbl} qr)))");
    let xv_l = format!("(xval {ek} (lift_at qv qk {ONE}) qsv (wkc_lift qD qv qsv qhv qk qins) qr)");
    let xv_r = format!("(xval qD qv qsv qhv {rl})");
    let yv = format!("(vconsD qsv {ek} {xv_l} qr)");
    let t1 = format!("(xval {ekbl} (lift_at qb (Nat.succ qk) {ONE}) qc (wkc_lift {dbl} qb qc qhb (Nat.succ qk) qins) {yv})");
    let t2 = format!("(xval {dbl} qb qc qhb (venvLiftD (Nat.succ qk) qins {dbl} {yv}))");
    let t3 = format!("(xval {dbl} qb qc qhb (vconsD qsv qD {xv_l} {rl}))");
    let t4 = format!("(xval {dbl} qb qc qhb (vconsD qsv qD {xv_r} {rl}))");
    let s23 = format!("(@Eq.cong (VEnvD {dbl}) (VD qc) (fun (qrr : VEnvD {dbl}) => xval {dbl} qb qc qhb qrr) (venvLiftD (Nat.succ qk) qins {dbl} {yv}) (vconsD qsv qD {xv_l} {rl}) (r14_venvLift_vcons qk qins qsv qD {xv_l} qr))");
    let s34 = format!("(@Eq.cong (VD qsv) (VD qc) (fun (qw : VD qsv) => xval {dbl} qb qc qhb (vconsD qsv qD qw {rl})) {xv_l} {xv_r} (qihv qk qins qr))");
    let m_let = format!("(fun (qD : Nat -> Sk) (qtt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qtt qst) (qhv : WKC qD qv qsv) (qhb : WKC {dbl} qb qc) {ih_t} {ih_v} {ih_bl} (qk : Nat) (qins : Sk) (qr : VEnvD {ek}) => @Eq.trans (VD qc) {t1} {t3} {t4} (@Eq.trans (VD qc) {t1} {t2} {t3} (qihb (Nat.succ qk) qins {yv}) {s23}) {s34})");

    format!("fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) => @WKC.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h")
}

// ================================================================
// Group C — the corollary that measures the rung against R18.
// ================================================================

/// **`r19_native_extends_transported`** — at an embedded derivation the native
/// lemma says exactly what R18's transported one says.
///
/// Not decoration. R18's `r18_xval_lift` and this rung's `r19_xval_lift` are
/// two DIFFERENT proofs of overlapping statements — one routed through `sval`
/// and `r14_val_lift`, one an induction on `WKC` — and a rung that quietly
/// changed the statement while widening it would be invisible without this. The
/// proof is `Eq.refl` at the type level: instantiating the native theorem at
/// `r17_wk_wkc D e s h` produces R18's statement on the nose, so the check is
/// that the kernel accepts the transported theorem's TYPE with the native
/// theorem's VALUE.
pub(super) const TY_NATIVE_EXTENDS: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (k : Nat) (ins : Sk) (r : VEnvD (skins k ins D)), @Eq (VD s) (xval (skins k ins D) (lift_at e k (Nat.succ Nat.zero)) s (wkc_lift D e s (r17_wk_wkc D e s h) k ins) r) (xval D e s (r17_wk_wkc D e s h) (venvLiftD k ins D r))";

pub(super) const VAL_NATIVE_EXTENDS: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (k : Nat) (ins : Sk) (r : VEnvD (skins k ins D)) => r19_xval_lift D e s (r17_wk_wkc D e s h) k ins r";

/// **`r19_lift_reaches_konst`** — the native lemma INSTANTIATED at a real
/// `konst` derivation, the case R18 provably could not state.
///
/// R17's `r17_konst_witness` is a `WKC` derivation of a real inert reflected
/// constant; `r17_wkc_lift_konst_witness` already lifts it. This is the
/// SEMANTIC half at the same objects, and it is the one constant in this rung
/// that `r18_xval_lift` has no instance of at all.
pub(super) fn ty_lift_reaches_konst() -> String {
    let ek = format!("(skins Nat.zero {KDTY} r12_piEnv)");
    format!("@Eq (VD Sk.ty) (xval {ek} (lift_at {DEADCONST} Nat.zero {ONE}) Sk.ty (wkc_lift r12_piEnv {DEADCONST} Sk.ty r17_konst_witness Nat.zero {KDTY}) (r12_junkEnv {ek})) (xval r12_piEnv {DEADCONST} Sk.ty r17_konst_witness (venvLiftD Nat.zero {KDTY} r12_piEnv (r12_junkEnv {ek})))")
}

pub(super) fn val_lift_reaches_konst() -> String {
    format!("r19_xval_lift r12_piEnv {DEADCONST} Sk.ty r17_konst_witness Nat.zero {KDTY} (r12_junkEnv (skins Nat.zero {KDTY} r12_piEnv))")
}

/// **`r19_lift_reaches_let`** — the same at R17's `let_` witness.
pub(super) fn ty_lift_reaches_let() -> String {
    let ek = format!("(skins Nat.zero {KDTY} r12_betaEnv)");
    format!("@Eq (VD {KDTY}) (xval {ek} (lift_at r17_letTerm Nat.zero {ONE}) {KDTY} (wkc_lift r12_betaEnv r17_letTerm {KDTY} r17_let_witness Nat.zero {KDTY}) (r12_junkEnv {ek})) (xval r12_betaEnv r17_letTerm {KDTY} r17_let_witness (venvLiftD Nat.zero {KDTY} r12_betaEnv (r12_junkEnv {ek})))")
}

pub(super) fn val_lift_reaches_let() -> String {
    format!("r19_xval_lift r12_betaEnv r17_letTerm {KDTY} r17_let_witness Nat.zero {KDTY} (r12_junkEnv (skins Nat.zero {KDTY} r12_betaEnv))")
}

// ================================================================
// Group D — negative controls. NOT registered.
// ================================================================

/// The native lemma with `Eq.refl` for a proof. Both sides are `WKC.rec` stuck
/// on a VARIABLE derivation, so the kernel must refuse — the measurement that
/// the induction does real work.
#[cfg(test)]
pub(super) fn probe_native_refl() -> String {
    format!(
        "def r19_native_refl_probe : {} := fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (k : Nat) (ins : Sk) (r : VEnvD (skins k ins D)) => @Eq.refl (VD s) (xval (skins k ins D) (lift_at e k {ONE}) s (wkc_lift D e s h k ins) r)",
        ty_xval_lift_native()
    )
}

/// The `konst` arm's `Eq.refl` claimed at the ARROW shape instead of `Sk.ty`.
/// `WKC.konst` concludes at `Sk.ty` and nowhere else (R17's
/// `r17_headFree_wkc_arr` rests on exactly that), so the kernel must refuse —
/// the control that the arm's `Eq.refl` is reading the real clause and not
/// succeeding by universe or shape accident.
#[cfg(test)]
pub(super) fn probe_konst_arm_wrong_shape() -> String {
    "def r19_konst_arm_shape_probe : forall (D : Nat -> Sk) (n : Name) (us : ListType Level), @Eq (VD (Sk.arr Sk.ty Sk.ty)) (fun (qe2 : KExpr) => whnf_acc qe2) (fun (qe2 : KExpr) => whnf_acc qe2) := fun (D : Nat -> Sk) (n : Name) (us : ListType Level) => @Eq.refl (VD (Sk.arr Sk.ty Sk.ty)) (fun (qe2 : KExpr) => whnf_acc qe2)".to_string()
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R19Item {
    /// `add_definition` — a theorem whose proof term the kernel type-checks.
    Thm {
        name: String,
        ty: String,
        val: String,
    },
}

#[cfg(test)]
impl R19Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R19Item::Thm { name, .. } => name,
        }
    }

    pub(super) fn decl_source(&self) -> String {
        match self {
            R19Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn t(name: &str, ty: String, val: String) -> R19Item {
    R19Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R19 constant, in registration order.
pub(super) fn r19_items() -> Vec<R19Item> {
    vec![
        t(
            "r19_xval_wkc_lift_var",
            ty_xval_wkc_lift_var(),
            val_xval_wkc_lift_var(),
        ),
        t(
            "r19_xval_lift",
            ty_xval_lift_native(),
            val_xval_lift_native(),
        ),
        t(
            "r19_native_extends_transported",
            TY_NATIVE_EXTENDS.to_string(),
            VAL_NATIVE_EXTENDS.to_string(),
        ),
        t(
            "r19_lift_reaches_konst",
            ty_lift_reaches_konst(),
            val_lift_reaches_konst(),
        ),
        t(
            "r19_lift_reaches_let",
            ty_lift_reaches_let(),
            val_lift_reaches_let(),
        ),
    ]
}

#[cfg(test)]
pub(super) fn r19_all_sources() -> Vec<(String, String)> {
    r19_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
