// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R20 sources — **THE NATIVE SUBSTITUTION LEMMA**, and the `WKC`-indexed
//! valuation construction R18 and R19 both declined to invent.
//!
//! See the module doc of [`super::candmodel_construct_r20`] for the argument.

// **This module deliberately imports nothing** — the R12-R19 convention.

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
// Group A — the definition R18 and R19 both declined to invent.
// ================================================================

/// **`r20_xvenvSubD`** — the induced valuation of a `WKC`-typed substitution.
///
/// `venvSubD` (R14) is the same construction over `WK` and `sval`, and it is
/// what forced `r18_xval_psub`'s right-hand side to stay `WK`-indexed: R18's
/// doc recorded that a `WKC`-indexed one "is a DEFINITION, not a corollary of
/// this rung", and declined to invent it inside a theorem that was otherwise
/// pure transport. R19 repeated the point. This is that definition, made
/// deliberately and in its own rung, exactly as `venvSubD` was made in R14.
pub(super) const SRC_XVENV_SUB_D: &str = "def r20_xvenvSubD (sg : Nat -> KExpr) (D : Nat -> Sk) (Dp : Nat -> Sk) (hsg : forall (qi : Nat), WKC D (sg qi) (Dp qi)) (r : VEnvD D) (i : Nat) : VD (Dp i) := xval D (sg i) (Dp i) (hsg i) r";

/// **`r20_xvenvSubD_agrees`** — on the embedded fragment the new valuation
/// construction IS `venvSubD`.
///
/// One line: pointwise it is exactly R18's transfer, and `r13_venvD_funext`
/// makes that an equality of valuations. It matters because it is what lets the
/// native substitution lemma be compared with the transported one at all — the
/// two statements read different valuations, so without this they could drift
/// silently past each other.
pub(super) const TY_XVENV_SUB_AGREES: &str = "forall (sg : Nat -> KExpr) (D : Nat -> Sk) (Dp : Nat -> Sk) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) (r : VEnvD D), @Eq (VEnvD Dp) (r20_xvenvSubD sg D Dp (fun (qi : Nat) => r17_wk_wkc D (sg qi) (Dp qi) (hsg qi)) r) (venvSubD sg D Dp hsg r)";

pub(super) const VAL_XVENV_SUB_AGREES: &str = "fun (sg : Nat -> KExpr) (D : Nat -> Sk) (Dp : Nat -> Sk) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) (r : VEnvD D) => r13_venvD_funext Dp (r20_xvenvSubD sg D Dp (fun (qi : Nat) => r17_wk_wkc D (sg qi) (Dp qi) (hsg qi)) r) (venvSubD sg D Dp hsg r) (fun (i : Nat) => r18_xval_sval D (sg i) (Dp i) (hsg i) r)";

// ================================================================
// Group B — the two ingredients the induction needs.
// ================================================================

/// **`r20_xval_lift0`** — R19's native weakening at the context HEAD.
///
/// Definitional on both sides at cutoff zero: `skins Nat.zero t D` is
/// `skcons t D`, `wkc_lift … Nat.zero t` is `wkc_lift0 … t`, and
/// `venvLiftD Nat.zero t D (vconsD t D v r)` is `r` (one `Nat.rec` iota, then
/// function eta). R14's `val_lift0` with `sval`/`wk_lift0` replaced.
pub(super) const TY_XVAL_LIFT0: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (t : Sk) (v : VD t) (r : VEnvD D), @Eq (VD s) (xval (skcons t D) (lift_at e Nat.zero (Nat.succ Nat.zero)) s (wkc_lift0 D e s h t) (vconsD t D v r)) (xval D e s h r)";

pub(super) const VAL_XVAL_LIFT0: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (t : Sk) (v : VD t) (r : VEnvD D) => r19_xval_lift D e s h Nat.zero t (vconsD t D v r)";

/// **`r20_xval_cast_term`** — the interpretation does not see a term transport.
///
/// R14's `r14_sval_cast_term` with `r17_wkcCastT` in place of `r14_wkCastT`. A
/// based `Eq.rec` whose base case is `Eq.refl`, which is why both casts were
/// defined over a BARE `Eq.rec` rather than `Eq.substType` — R14 measured that
/// a transport spelled with `Eq.substType` does not delta-unfold and its
/// reflexivity base never reduces.
pub(super) const TY_XVAL_CAST_TERM: &str = "forall (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (s : Sk) (heq : @Eq KExpr e1 e2) (h : WKC D e1 s) (r : VEnvD D), @Eq (VD s) (xval D e2 s (r17_wkcCastT D e1 e2 s heq h) r) (xval D e1 s h r)";

pub(super) const VAL_XVAL_CAST_TERM: &str = "fun (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (s : Sk) (heq : @Eq KExpr e1 e2) (h : WKC D e1 s) (r : VEnvD D) => @Eq.rec KExpr e1 (fun (qz : KExpr) (qp : @Eq KExpr e1 qz) => @Eq (VD s) (xval D qz s (r17_wkcCastT D e1 qz s qp h) r) (xval D e1 s h r)) (@Eq.refl (VD s) (xval D e1 s h r)) e2 heq";

/// **`r20_xvenvSub_up`** — substitution commutes with valuation extension.
///
/// R14's `venvSub_up` over the new construction. The zero branch is `Eq.refl`;
/// the successor branch is `r20_xval_lift0`, which is the only place the whole
/// substitution lemma consumes R19.
pub(super) const TY_XVENV_SUB_UP: &str = "forall (D : Nat -> Sk) (Dp : Nat -> Sk) (sg : Nat -> KExpr) (hsg : forall (qi : Nat), WKC D (sg qi) (Dp qi)) (d : Sk) (v : VD d) (r : VEnvD D), @Eq (VEnvD (skcons d Dp)) (r20_xvenvSubD (up sg) (skcons d D) (skcons d Dp) (wkc_up D Dp sg d hsg) (vconsD d D v r)) (vconsD d Dp v (r20_xvenvSubD sg D Dp hsg r))";

pub(super) const VAL_XVENV_SUB_UP: &str = "fun (D : Nat -> Sk) (Dp : Nat -> Sk) (sg : Nat -> KExpr) (hsg : forall (qi : Nat), WKC D (sg qi) (Dp qi)) (d : Sk) (v : VD d) (r : VEnvD D) => r13_venvD_funext (skcons d Dp) (r20_xvenvSubD (up sg) (skcons d D) (skcons d Dp) (wkc_up D Dp sg d hsg) (vconsD d D v r)) (vconsD d Dp v (r20_xvenvSubD sg D Dp hsg r)) (fun (i : Nat) => @Nat.rec (fun (qi : Nat) => @Eq (VD (skcons d Dp qi)) (r20_xvenvSubD (up sg) (skcons d D) (skcons d Dp) (wkc_up D Dp sg d hsg) (vconsD d D v r) qi) (vconsD d Dp v (r20_xvenvSubD sg D Dp hsg r) qi)) (@Eq.refl (VD d) v) (fun (qn : Nat) (qih : @Eq (VD (skcons d Dp qn)) (r20_xvenvSubD (up sg) (skcons d D) (skcons d Dp) (wkc_up D Dp sg d hsg) (vconsD d D v r) qn) (vconsD d Dp v (r20_xvenvSubD sg D Dp hsg r) qn)) => r20_xval_lift0 D (sg qn) (Dp qn) (hsg qn) d v r) i)";

/// **`r20_xvenvSub_scons`** — the single-term substitution's induced valuation
/// is the extension by that term's own interpretation. R14's
/// `venvSub_scons` over `r17_scons_typed`.
pub(super) const TY_XVENV_SUB_SCONS: &str = "forall (D : Nat -> Sk) (a : KExpr) (d : Sk) (ha : WKC D a d) (r : VEnvD D), @Eq (VEnvD (skcons d D)) (r20_xvenvSubD (scons a idsubst) D (skcons d D) (r17_scons_typed D a d ha) r) (vconsD d D (xval D a d ha r) r)";

pub(super) const VAL_XVENV_SUB_SCONS: &str = "fun (D : Nat -> Sk) (a : KExpr) (d : Sk) (ha : WKC D a d) (r : VEnvD D) => r13_venvD_funext (skcons d D) (r20_xvenvSubD (scons a idsubst) D (skcons d D) (r17_scons_typed D a d ha) r) (vconsD d D (xval D a d ha r) r) (fun (i : Nat) => @Nat.rec (fun (qi : Nat) => @Eq (VD (skcons d D qi)) (r20_xvenvSubD (scons a idsubst) D (skcons d D) (r17_scons_typed D a d ha) r qi) (vconsD d D (xval D a d ha r) r qi)) (@Eq.refl (VD d) (xval D a d ha r)) (fun (qn : Nat) (qih : @Eq (VD (skcons d D qn)) (r20_xvenvSubD (scons a idsubst) D (skcons d D) (r17_scons_typed D a d ha) r qn) (vconsD d D (xval D a d ha r) r qn)) => @Eq.refl (VD (D qn)) (r qn)) i)";

// ================================================================
// Group C — THE NATIVE SUBSTITUTION LEMMA.
// ================================================================

/// **`r20_xval_psub` — R14's `val_psub` at SEVEN constructors.**
pub(super) const TY_XVAL_PSUB: &str = "forall (Dp : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC Dp e s) (sg : Nat -> KExpr) (D : Nat -> Sk) (hsg : forall (qi : Nat), WKC D (sg qi) (Dp qi)) (r : VEnvD D), @Eq (VD s) (xval D (psubst sg e) s (wkc_psub Dp e s h sg D hsg) r) (xval Dp e s h (r20_xvenvSubD sg D Dp hsg r))";

/// The native proof: `WKC.rec` at seven arms, R14's five plus `konst` and
/// `let_`.
///
/// The `var` arm is `Eq.refl`, and R14 recorded why: stating the operation with
/// a substitution HYPOTHESIS rather than a cutoff makes the derivation it
/// produces at a variable BE the hypothesis, so the interpretation is the
/// induced valuation on the nose. `konst` is `Eq.refl` for R19's reason —
/// `psubst` leaves a constant alone and `xval`'s `konst` clause never reads the
/// valuation. `let_` costs one congruence more than `lam`, in the extension
/// value, exactly as it did in R19.
#[allow(clippy::too_many_lines)]
pub(super) fn val_xval_psub() -> String {
    let hyp = "(forall (qi : Nat), WKC qD (qsg qi) (qDp qi))";
    let subd = "(skcons (domSk qsA) qD)";
    let subdp = "(skcons (domSk qsA) qDp)";
    let wu = "(wkc_up qD qDp qsg (domSk qsA) qhsg)";
    let rs = "(r20_xvenvSubD qsg qD qDp qhsg qr)";
    let jb = "(junkD (domSk qsA))";

    let motive = "(fun (qDp : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qDp qe qs) => forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) (qr : VEnvD qD), @Eq (VD qs) (xval qD (psubst qsg qe) qs (wkc_psub qDp qe qs qh qsg qD qhsg) qr) (xval qDp qe qs qh (r20_xvenvSubD qsg qD qDp qhsg qr)))";
    let m_var = format!("(fun (qDp : Nat -> Sk) (qi : Nat) (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => @Eq.refl (VD (qDp qi)) (xval qD (qsg qi) (qDp qi) (qhsg qi) qr))");
    let m_sort = format!("(fun (qDp : Nat -> Sk) (qn : Level) (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => @Eq.refl (VD {KDTY}) (fun (qe2 : KExpr) => whnf_acc qe2))");

    let ih_a = format!("(qihA : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD), @Eq (VD qsA) (xval qD (psubst qsg qA) qsA (wkc_psub qDp qA qsA qhA qsg qD qhsg) qr) (xval qDp qA qsA qhA (r20_xvenvSubD qsg qD qDp qhsg qr)))");
    let hypb = "(forall (qi : Nat), WKC qD (qsg qi) (skcons (domSk qsA) qDp qi))";

    // --- pi ---
    let ih_pb = format!("(qihB : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hypb}) (qr : VEnvD qD), @Eq (VD qsB) (xval qD (psubst qsg qB) qsB (wkc_psub {subdp} qB qsB qhB qsg qD qhsg) qr) (xval {subdp} qB qsB qhB (r20_xvenvSubD qsg qD {subdp} qhsg qr)))");
    let yb = format!("(vconsD (domSk qsA) qD {jb} qr)");
    let p_va = "(xval qD (psubst qsg qA) qsA (wkc_psub qDp qA qsA qhA qsg qD qhsg) qr)";
    let p_va2 = format!("(xval qDp qA qsA qhA {rs})");
    let p_vb = format!("(xval {subd} (psubst (up qsg) qB) qsB (wkc_psub {subdp} qB qsB qhB (up qsg) {subd} {wu}) {yb})");
    let p_mid =
        format!("(xval {subdp} qB qsB qhB (r20_xvenvSubD (up qsg) {subd} {subdp} {wu} {yb}))");
    let p_vb2 = format!("(xval {subdp} qB qsB qhB (vconsD (domSk qsA) qDp {jb} {rs}))");
    let p_cong = format!("(@Eq.cong (VEnvD {subdp}) (VD qsB) (fun (qrr : VEnvD {subdp}) => xval {subdp} qB qsB qhB qrr) (r20_xvenvSubD (up qsg) {subd} {subdp} {wu} {yb}) (vconsD (domSk qsA) qDp {jb} {rs}) (r20_xvenvSub_up qD qDp qsg qhsg (domSk qsA) {jb} qr))");
    let p_hb = format!(
        "(@Eq.trans (VD qsB) {p_vb} {p_mid} {p_vb2} (qihB (up qsg) {subd} {wu} {yb}) {p_cong})"
    );
    let m_pi = format!("(fun (qDp : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qDp qA qsA) (qhB : WKC {subdp} qB qsB) {ih_a} {ih_pb} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => r14_sval_pi_congr qsA qsB {p_va} {p_va2} {p_vb} {p_vb2} (qihA qsg qD qhsg qr) {p_hb})");

    // --- lam ---
    let ih_lb = format!("(qihb : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hypb}) (qr : VEnvD qD), @Eq (VD qc) (xval qD (psubst qsg qb) qc (wkc_psub {subdp} qb qc qhb qsg qD qhsg) qr) (xval {subdp} qb qc qhb (r20_xvenvSubD qsg qD {subdp} qhsg qr)))");
    let yx = "(vconsD (domSk qsA) qD qx qr)";
    let l_f = "(xval qD (psubst qsg (KExpr.lam qA qb)) (Sk.arr (domSk qsA) qc) (wkc_psub qDp (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc) (WKC.lam qDp qA qb qsA qc qhA qhb) qsg qD qhsg) qr)";
    let l_g = format!("(xval qDp (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc) (WKC.lam qDp qA qb qsA qc qhA qhb) {rs})");
    let l_x1 = format!("(xval {subd} (psubst (up qsg) qb) qc (wkc_psub {subdp} qb qc qhb (up qsg) {subd} {wu}) {yx})");
    let l_x2 =
        format!("(xval {subdp} qb qc qhb (r20_xvenvSubD (up qsg) {subd} {subdp} {wu} {yx}))");
    let l_x3 = format!("(xval {subdp} qb qc qhb (vconsD (domSk qsA) qDp qx {rs}))");
    let l_cong = format!("(@Eq.cong (VEnvD {subdp}) (VD qc) (fun (qrr : VEnvD {subdp}) => xval {subdp} qb qc qhb qrr) (r20_xvenvSubD (up qsg) {subd} {subdp} {wu} {yx}) (vconsD (domSk qsA) qDp qx {rs}) (r20_xvenvSub_up qD qDp qsg qhsg (domSk qsA) qx qr))");
    let l_point = format!("(fun (qx : VD (domSk qsA)) => @Eq.trans (VD qc) {l_x1} {l_x2} {l_x3} (qihb (up qsg) {subd} {wu} {yx}) {l_cong})");
    let m_lam = format!("(fun (qDp : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qDp qA qsA) (qhb : WKC {subdp} qb qc) {ih_a} {ih_lb} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => r13_vd_arr_funext (domSk qsA) qc {l_f} {l_g} {l_point})");

    // --- app ---
    let arr = "(Sk.arr qd qcc)";
    let ih_f = format!("(qihf : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD), @Eq (VD {arr}) (xval qD (psubst qsg qf) {arr} (wkc_psub qDp qf {arr} qhf qsg qD qhsg) qr) (xval qDp qf {arr} qhf (r20_xvenvSubD qsg qD qDp qhsg qr)))");
    let ih_ar = format!("(qiha : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD), @Eq (VD qd) (xval qD (psubst qsg qa) qd (wkc_psub qDp qa qd qha qsg qD qhsg) qr) (xval qDp qa qd qha (r20_xvenvSubD qsg qD qDp qhsg qr)))");
    let a_f = format!("(xval qD (psubst qsg qf) {arr} (wkc_psub qDp qf {arr} qhf qsg qD qhsg) qr)");
    let a_f2 = format!("(xval qDp qf {arr} qhf {rs})");
    let a_x = "(xval qD (psubst qsg qa) qd (wkc_psub qDp qa qd qha qsg qD qhsg) qr)";
    let a_x2 = format!("(xval qDp qa qd qha {rs})");
    let m_app = format!("(fun (qDp : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qDp qf {arr}) (qha : WKC qDp qa qd) {ih_f} {ih_ar} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => r14_vapply_congr qd qcc {a_f} {a_f2} {a_x} {a_x2} (qihf qsg qD qhsg qr) (qiha qsg qD qhsg qr))");

    // --- konst ---
    let m_konst = format!(
        "(fun (qDp : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => @Eq.refl (VD Sk.ty) (fun (qe2 : KExpr) => whnf_acc qe2))",
        defval_none("qn"),
        recmeta_none("qn")
    );

    // --- let_ ---
    let ldp = "(skcons qsv qDp)";
    let ldd = "(skcons qsv qD)";
    let wul = "(wkc_up qD qDp qsg qsv qhsg)";
    let hypl = "(forall (qi : Nat), WKC qD (qsg qi) (skcons qsv qDp qi))";
    let ih_t = format!("(qiht : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD), @Eq (VD qst) (xval qD (psubst qsg qtt) qst (wkc_psub qDp qtt qst qht qsg qD qhsg) qr) (xval qDp qtt qst qht (r20_xvenvSubD qsg qD qDp qhsg qr)))");
    let ih_v = format!("(qihv : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD), @Eq (VD qsv) (xval qD (psubst qsg qv) qsv (wkc_psub qDp qv qsv qhv qsg qD qhsg) qr) (xval qDp qv qsv qhv (r20_xvenvSubD qsg qD qDp qhsg qr)))");
    let ih_bl = format!("(qihb : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hypl}) (qr : VEnvD qD), @Eq (VD qc) (xval qD (psubst qsg qb) qc (wkc_psub {ldp} qb qc qhb qsg qD qhsg) qr) (xval {ldp} qb qc qhb (r20_xvenvSubD qsg qD {ldp} qhsg qr)))");
    let xv_l = "(xval qD (psubst qsg qv) qsv (wkc_psub qDp qv qsv qhv qsg qD qhsg) qr)";
    let xv_r = format!("(xval qDp qv qsv qhv {rs})");
    let yv = format!("(vconsD qsv qD {xv_l} qr)");
    let t1 = format!(
        "(xval {ldd} (psubst (up qsg) qb) qc (wkc_psub {ldp} qb qc qhb (up qsg) {ldd} {wul}) {yv})"
    );
    let t2 = format!("(xval {ldp} qb qc qhb (r20_xvenvSubD (up qsg) {ldd} {ldp} {wul} {yv}))");
    let t3 = format!("(xval {ldp} qb qc qhb (vconsD qsv qDp {xv_l} {rs}))");
    let t4 = format!("(xval {ldp} qb qc qhb (vconsD qsv qDp {xv_r} {rs}))");
    let s23 = format!("(@Eq.cong (VEnvD {ldp}) (VD qc) (fun (qrr : VEnvD {ldp}) => xval {ldp} qb qc qhb qrr) (r20_xvenvSubD (up qsg) {ldd} {ldp} {wul} {yv}) (vconsD qsv qDp {xv_l} {rs}) (r20_xvenvSub_up qD qDp qsg qhsg qsv {xv_l} qr))");
    let s34 = format!("(@Eq.cong (VD qsv) (VD qc) (fun (qw : VD qsv) => xval {ldp} qb qc qhb (vconsD qsv qDp qw {rs})) {xv_l} {xv_r} (qihv qsg qD qhsg qr))");
    let m_let = format!("(fun (qDp : Nat -> Sk) (qtt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qDp qtt qst) (qhv : WKC qDp qv qsv) (qhb : WKC {ldp} qb qc) {ih_t} {ih_v} {ih_bl} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => @Eq.trans (VD qc) {t1} {t3} {t4} (@Eq.trans (VD qc) {t1} {t2} {t3} (qihb (up qsg) {ldd} {wul} {yv}) {s23}) {s34})");

    format!("fun (Dp : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC Dp e s) => @WKC.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} Dp e s h")
}

/// **`r20_xval_inst` — native instantiation.** R14's `val_inst` over `wkc_inst`:
/// the term transport off `instantiate_eq_psubst`, the native substitution
/// lemma, then `r20_xvenvSub_scons` to read the induced valuation as the
/// extension by the argument's own interpretation.
///
/// This is the one the β law wants, and it is the reason `val_psub` is worth
/// having natively at all: `wkc_inst` is what R17's `wkc_step` calls at its
/// head-β arm.
pub(super) const TY_XVAL_INST: &str = "forall (D : Nat -> Sk) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hb : WKC (skcons d D) b c) (ha : WKC D a d) (r : VEnvD D), @Eq (VD c) (xval D (instantiate b a) c (wkc_inst D b a d c hb ha) r) (xval (skcons d D) b c hb (vconsD d D (xval D a d ha r) r))";

pub(super) fn val_xval_inst() -> String {
    let hsub = "(r17_scons_typed D a d ha)";
    let sym = "(@Eq.symm KExpr (instantiate b a) (psubst (scons a idsubst) b) (instantiate_eq_psubst b a))";
    let wps = format!("(wkc_psub (skcons d D) b c hb (scons a idsubst) D {hsub})");
    let x1 = "(xval D (instantiate b a) c (wkc_inst D b a d c hb ha) r)";
    let x2 = format!("(xval D (psubst (scons a idsubst) b) c {wps} r)");
    let x3 = format!(
        "(xval (skcons d D) b c hb (r20_xvenvSubD (scons a idsubst) D (skcons d D) {hsub} r))"
    );
    let x4 = "(xval (skcons d D) b c hb (vconsD d D (xval D a d ha r) r))";
    let s1 = format!(
        "(r20_xval_cast_term D (psubst (scons a idsubst) b) (instantiate b a) c {sym} {wps} r)"
    );
    let s2 = format!("(r20_xval_psub (skcons d D) b c hb (scons a idsubst) D {hsub} r)");
    let s3 = format!("(@Eq.cong (VEnvD (skcons d D)) (VD c) (fun (qrr : VEnvD (skcons d D)) => xval (skcons d D) b c hb qrr) (r20_xvenvSubD (scons a idsubst) D (skcons d D) {hsub} r) (vconsD d D (xval D a d ha r) r) (r20_xvenvSub_scons D a d ha r))");
    format!("fun (D : Nat -> Sk) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hb : WKC (skcons d D) b c) (ha : WKC D a d) (r : VEnvD D) => @Eq.trans (VD c) {x1} {x3} {x4} (@Eq.trans (VD c) {x1} {x2} {x3} {s1} {s2}) {s3}")
}

// ================================================================
// Group D — the drift check and the two reach witnesses.
// ================================================================

/// **`r20_psub_extends_transported`** — R18's `r18_xval_psub` TYPE, proved from
/// R20's native lemma plus `r20_xvenvSubD_agrees`.
///
/// Two steps rather than R19's one, and the extra step is exactly the caveat
/// R18 recorded: the two statements read DIFFERENT valuation constructions, so
/// the native lemma has to be pushed across the agreement lemma before it can
/// be compared with the transported one at all.
pub(super) const TY_PSUB_EXTENDS: &str = "forall (Dp : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK Dp e s) (sg : Nat -> KExpr) (D : Nat -> Sk) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) (r : VEnvD D), @Eq (VD s) (xval D (psubst sg e) s (wkc_psub Dp e s (r17_wk_wkc Dp e s h) sg D (fun (qi : Nat) => r17_wk_wkc D (sg qi) (Dp qi) (hsg qi))) r) (xval Dp e s (r17_wk_wkc Dp e s h) (venvSubD sg D Dp hsg r))";

pub(super) fn val_psub_extends() -> String {
    let hc = "(fun (qi : Nat) => r17_wk_wkc D (sg qi) (Dp qi) (hsg qi))";
    let hw = "(r17_wk_wkc Dp e s h)";
    let mid = format!("(xval Dp e s {hw} (r20_xvenvSubD sg D Dp {hc} r))");
    let lhs = format!("(xval D (psubst sg e) s (wkc_psub Dp e s {hw} sg D {hc}) r)");
    let rhs = "(xval Dp e s (r17_wk_wkc Dp e s h) (venvSubD sg D Dp hsg r))";
    let cong = format!("(@Eq.cong (VEnvD Dp) (VD s) (fun (qrr : VEnvD Dp) => xval Dp e s {hw} qrr) (r20_xvenvSubD sg D Dp {hc} r) (venvSubD sg D Dp hsg r) (r20_xvenvSubD_agrees sg D Dp hsg r))");
    format!("fun (Dp : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK Dp e s) (sg : Nat -> KExpr) (D : Nat -> Sk) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) (r : VEnvD D) => @Eq.trans (VD s) {lhs} {mid} {rhs} (r20_xval_psub Dp e s {hw} sg D {hc} r) {cong}")
}

/// The native substitution lemma at R17's real `konst` witness — substituting
/// under the identity substitution at a constant no embedding reaches.
pub(super) fn ty_psub_reaches_konst() -> String {
    format!("forall (r : VEnvD r12_piEnv), @Eq (VD Sk.ty) (xval r12_piEnv (psubst idsubst {DEADCONST}) Sk.ty (wkc_psub r12_piEnv {DEADCONST} Sk.ty r17_konst_witness idsubst r12_piEnv (r20_idsubst_typed r12_piEnv)) r) (xval r12_piEnv {DEADCONST} Sk.ty r17_konst_witness (r20_xvenvSubD idsubst r12_piEnv r12_piEnv (r20_idsubst_typed r12_piEnv) r))")
}

pub(super) fn val_psub_reaches_konst() -> String {
    format!("fun (r : VEnvD r12_piEnv) => r20_xval_psub r12_piEnv {DEADCONST} Sk.ty r17_konst_witness idsubst r12_piEnv (r20_idsubst_typed r12_piEnv) r")
}

/// The identity substitution is `WKC`-typed at every index — the supply the two
/// reach witnesses need. `idsubst i` is `bvar i`, so every index is `WKC.var`.
pub(super) const SRC_IDSUBST_TYPED: &str =
    "def r20_idsubst_typed (D : Nat -> Sk) (i : Nat) : WKC D (idsubst i) (D i) := WKC.var D i";

/// The same at R17's `let_` witness.
pub(super) const TY_PSUB_REACHES_LET: &str = "forall (r : VEnvD r12_betaEnv), @Eq (VD (Sk.kd Sk.ty)) (xval r12_betaEnv (psubst idsubst r17_letTerm) (Sk.kd Sk.ty) (wkc_psub r12_betaEnv r17_letTerm (Sk.kd Sk.ty) r17_let_witness idsubst r12_betaEnv (r20_idsubst_typed r12_betaEnv)) r) (xval r12_betaEnv r17_letTerm (Sk.kd Sk.ty) r17_let_witness (r20_xvenvSubD idsubst r12_betaEnv r12_betaEnv (r20_idsubst_typed r12_betaEnv) r))";

pub(super) const VAL_PSUB_REACHES_LET: &str = "fun (r : VEnvD r12_betaEnv) => r20_xval_psub r12_betaEnv r17_letTerm (Sk.kd Sk.ty) r17_let_witness idsubst r12_betaEnv (r20_idsubst_typed r12_betaEnv) r";

/// **`r20_xval_beta`** — the semantic β law, NATIVE.
///
/// R14's `val_beta` shape at `wkc_inst`: the interpretation of a β redex's
/// contractum is the body's interpretation at the valuation extended by the
/// argument's. This is `r20_xval_inst` read at the objects `wkc_step`'s head-β
/// arm produces, and it is the concrete reason the substitution lemma was worth
/// proving natively rather than transporting.
pub(super) fn ty_xval_beta() -> String {
    "forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hA : WKC D A d) (hb : WKC (skcons (domSk d) D) b c) (ha : WKC D a (domSk d)) (r : VEnvD D), @Eq (VD c) (xval D (instantiate b a) c (wkc_inst D b a (domSk d) c hb ha) r) (xval D (KExpr.app (KExpr.lam A b) a) c (WKC.app D (KExpr.lam A b) a (domSk d) c (WKC.lam D A b d c hA hb) ha) r)".to_string()
}

pub(super) fn val_xval_beta() -> String {
    "fun (D : Nat -> Sk) (A : KExpr) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hA : WKC D A d) (hb : WKC (skcons (domSk d) D) b c) (ha : WKC D a (domSk d)) (r : VEnvD D) => r20_xval_inst D b a (domSk d) c hb ha r".to_string()
}

// ================================================================
// Group E — negative controls. NOT registered.
// ================================================================

/// The native substitution lemma with `Eq.refl` for a proof. Both sides are
/// recursors stuck on a VARIABLE derivation, so the kernel must refuse.
#[cfg(test)]
pub(super) fn probe_psub_refl() -> String {
    format!("def r20_psub_refl_probe : {TY_XVAL_PSUB} := fun (Dp : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC Dp e s) (sg : Nat -> KExpr) (D : Nat -> Sk) (hsg : forall (qi : Nat), WKC D (sg qi) (Dp qi)) (r : VEnvD D) => @Eq.refl (VD s) (xval D (psubst sg e) s (wkc_psub Dp e s h sg D hsg) r)")
}

/// `r20_xvenvSubD` claimed to agree with `venvSubD` at an ARBITRARY `WKC`
/// substitution hypothesis rather than at an embedded one, with the same proof.
/// It must be refused: `venvSubD` takes a `WK`-typed hypothesis and there is
/// none to hand at a `konst`- or `let_`-headed substitution. This is the
/// SCOPE of the agreement lemma made machine-visible — the new construction is
/// strictly wider than the old one, and the bridge between them is not.
#[cfg(test)]
pub(super) fn probe_agrees_at_wkc() -> String {
    format!("def r20_agrees_at_wkc_probe : forall (sg : Nat -> KExpr) (D : Nat -> Sk) (Dp : Nat -> Sk) (hsg : forall (qi : Nat), WKC D (sg qi) (Dp qi)) (r : VEnvD D), @Eq (VEnvD Dp) (r20_xvenvSubD sg D Dp hsg r) (venvSubD sg D Dp hsg r) := {VAL_XVENV_SUB_AGREES}")
}

/// The β law with its argument at the WRONG shape: `ha` typed at `d` instead of
/// `domSk d`. `WKC.app`'s function premise is at `Sk.arr (domSk d) c`, so the
/// argument must inhabit `domSk d`; the kernel must refuse. The control that
/// `r20_xval_beta` is reading the real application rule and not succeeding
/// because `domSk` collapses.
#[cfg(test)]
pub(super) fn probe_beta_wrong_arg_shape() -> String {
    "def r20_beta_arg_shape_probe : forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hA : WKC D A d) (hb : WKC (skcons (domSk d) D) b c) (ha : WKC D a d) (r : VEnvD D), @Eq (VD c) (xval D (instantiate b a) c (wkc_inst D b a (domSk d) c hb ha) r) (xval D (KExpr.app (KExpr.lam A b) a) c (WKC.app D (KExpr.lam A b) a (domSk d) c (WKC.lam D A b d c hA hb) ha) r) := fun (D : Nat -> Sk) (A : KExpr) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hA : WKC D A d) (hb : WKC (skcons (domSk d) D) b c) (ha : WKC D a d) (r : VEnvD D) => r20_xval_inst D b a (domSk d) c hb ha r".to_string()
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R20Item {
    /// `add_recursive_def` — a constant later proofs must REDUCE THROUGH.
    Def { name: String, src: String },
    /// `add_definition` — a theorem whose proof term the kernel type-checks.
    Thm {
        name: String,
        ty: String,
        val: String,
    },
}

#[cfg(test)]
impl R20Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R20Item::Def { name, .. } | R20Item::Thm { name, .. } => name,
        }
    }

    pub(super) fn decl_source(&self) -> String {
        match self {
            R20Item::Def { src, .. } => src.clone(),
            R20Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn d(name: &str, src: String) -> R20Item {
    R20Item::Def {
        name: name.to_string(),
        src,
    }
}

fn t(name: &str, ty: String, val: String) -> R20Item {
    R20Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R20 constant, in registration order.
pub(super) fn r20_items() -> Vec<R20Item> {
    vec![
        d("r20_xvenvSubD", SRC_XVENV_SUB_D.to_string()),
        d("r20_idsubst_typed", SRC_IDSUBST_TYPED.to_string()),
        t(
            "r20_xvenvSubD_agrees",
            TY_XVENV_SUB_AGREES.to_string(),
            VAL_XVENV_SUB_AGREES.to_string(),
        ),
        t(
            "r20_xval_lift0",
            TY_XVAL_LIFT0.to_string(),
            VAL_XVAL_LIFT0.to_string(),
        ),
        t(
            "r20_xval_cast_term",
            TY_XVAL_CAST_TERM.to_string(),
            VAL_XVAL_CAST_TERM.to_string(),
        ),
        t(
            "r20_xvenvSub_up",
            TY_XVENV_SUB_UP.to_string(),
            VAL_XVENV_SUB_UP.to_string(),
        ),
        t(
            "r20_xvenvSub_scons",
            TY_XVENV_SUB_SCONS.to_string(),
            VAL_XVENV_SUB_SCONS.to_string(),
        ),
        t("r20_xval_psub", TY_XVAL_PSUB.to_string(), val_xval_psub()),
        t("r20_xval_inst", TY_XVAL_INST.to_string(), val_xval_inst()),
        t("r20_xval_beta", ty_xval_beta(), val_xval_beta()),
        t(
            "r20_psub_extends_transported",
            TY_PSUB_EXTENDS.to_string(),
            val_psub_extends(),
        ),
        t(
            "r20_psub_reaches_konst",
            ty_psub_reaches_konst(),
            val_psub_reaches_konst(),
        ),
        t(
            "r20_psub_reaches_let",
            TY_PSUB_REACHES_LET.to_string(),
            VAL_PSUB_REACHES_LET.to_string(),
        ),
    ]
}

#[cfg(test)]
pub(super) fn r20_all_sources() -> Vec<(String, String)> {
    r20_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
