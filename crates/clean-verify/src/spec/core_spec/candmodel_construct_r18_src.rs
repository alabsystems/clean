// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R18 sources — **THE SEMANTIC TRANSFER**, and the R14/R16 semantic stack
//! carried across it onto `xval`.
//!
//! R17 landed the embedding `r17_wk_wkc` and the shape-level agreement
//! `r17_shapeOf_agrees_on_wk`, and named what it did NOT land:
//!
//! > *"the semantic transfer (`xval (wk_wkc h) r = sval h r`) is the named next
//! > item."*
//!
//! This is that item, plus every consequence it unlocks. See the module doc of
//! [`super::candmodel_construct_r18`] for the argument.

// **This module deliberately imports nothing** — the R12/R14/R15/R16/R17
// convention, so the whole file can be `#[path]`-included into a scratch crate
// that depends only on `clean-parser` and parse-checked in a second. The four
// shared spellings below are re-declared here for that reason, exactly as R15,
// R16 and R17 re-declare them.

/// `bvar 0`.
const V0: &str = "(KExpr.bvar Nat.zero)";
/// `Sort 0`.
const S0: &str = "(KExpr.sort Level.zero)";
/// The kind of types — R12's `KDTY`.
const KDTY: &str = "(Sk.kd Sk.ty)";
/// The lift amount `wk_lift` / `wkc_lift` are stated at.
const ONE: &str = "(Nat.succ Nat.zero)";
/// R12's β contractum, R16's `INST0`.
const INST0: &str = "(instantiate (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))";

// ================================================================
// Group A — THE TRANSFER.
//
// `sval` recurses on a `WK` derivation; `xval` recurses on a `WKC` one. The
// embedding turns the first into the second CONSTRUCTOR BY CONSTRUCTOR, and
// both interpretations read the SAME five clauses at those five constructors,
// so the transfer is an induction on the `WK` derivation whose every arm is
// either `Eq.refl` or one of the congruence helpers R14 already built for
// exactly this shape of obligation.
// ================================================================

/// The shape environment under a binder: R12/R14's `skcons (domSk qsA) qD`.
const DB: &str = "(skcons (domSk qsA) qD)";

/// **`r18_xval_sval` — THE SEMANTIC TRANSFER.**
///
/// On every term the OLD system types, the NEW interpretation and the old one
/// agree, at every valuation. This is the semantic counterpart of R17's
/// `r17_shapeOf_agrees_on_wk`, which said the same thing one level down about
/// SHAPES; it is what makes R12-R16's semantic lineage a statement about
/// `xval`, not merely about the system `xval` extends.
pub(super) const TY_XVAL_SVAL: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D), Eq (VD s) (xval D e s (r17_wk_wkc D e s h) r) (sval D e s h r)";

/// The transfer's proof term: `WK.rec` at five arms.
///
/// * `var` / `sort` — `Eq.refl`. Both interpretations read the valuation, resp.
///   the top candidate, with no derivation content at all.
/// * `pi` — `r14_sval_pi_congr`, R14's two-place congruence in the domain and
///   codomain VALUES, at the two induction hypotheses. The codomain hypothesis
///   is used at the ONE valuation the clause reads — the junk extension — which
///   is why no valuation quantifier has to be carried under the binder.
/// * `lam` — `r13_vd_arr_funext`. The two sides are SEMANTIC FUNCTIONS agreeing
///   pointwise, which is exactly the obstruction R12 recorded and R13 removed;
///   the pointwise proof is the body's hypothesis at the extended valuation.
/// * `app` — `r14_vapply_congr`, the two-place congruence in the function and
///   the argument.
///
/// Every arm is R14's `val_lift` arm with the lifting stripped out, which is
/// the measurement worth keeping: the transfer needed NO new semantic
/// machinery, only the machinery R13/R14 built for the corpus's `val_lift`.
#[allow(clippy::too_many_lines)]
pub(super) fn val_xval_sval() -> String {
    let motive = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => forall (qr : VEnvD qD), Eq (VD qs) (xval qD qe qs (r17_wk_wkc qD qe qs qh) qr) (sval qD qe qs qh qr))";

    let m_var = "(fun (qD : Nat -> Sk) (qi : Nat) (qr : VEnvD qD) => Eq.refl (VD (qD qi)) (qr qi))";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) (qr : VEnvD qD) => Eq.refl (VD (Sk.kd Sk.ty)) (fun (qe2 : KExpr) => whnf_acc qe2))";

    // The annotation hypothesis, shared by `pi` and `lam`.
    let ih_a = "(qihA : forall (qr : VEnvD qD), Eq (VD qsA) (xval qD qA qsA (r17_wk_wkc qD qA qsA qhA) qr) (sval qD qA qsA qhA qr))";
    let xa = "(xval qD qA qsA (r17_wk_wkc qD qA qsA qhA) qr)";
    let sa = "(sval qD qA qsA qhA qr)";

    // --- pi ---
    let ih_pb = format!("(qihB : forall (qr : VEnvD {DB}), Eq (VD qsB) (xval {DB} qB qsB (r17_wk_wkc {DB} qB qsB qhB) qr) (sval {DB} qB qsB qhB qr))");
    let jr = "(vconsD (domSk qsA) qD (junkD (domSk qsA)) qr)";
    let xb = format!("(xval {DB} qB qsB (r17_wk_wkc {DB} qB qsB qhB) {jr})");
    let sb = format!("(sval {DB} qB qsB qhB {jr})");
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK {DB} qB qsB) {ih_a} {ih_pb} (qr : VEnvD qD) => r14_sval_pi_congr qsA qsB {xa} {sa} {xb} {sb} (qihA qr) (qihB {jr}))"
    );

    // --- lam ---
    let ih_lb = format!("(qihb : forall (qr : VEnvD {DB}), Eq (VD qc) (xval {DB} qb qc (r17_wk_wkc {DB} qb qc qhb) qr) (sval {DB} qb qc qhb qr))");
    let lam_t = "(KExpr.lam qA qb)";
    let lam_s = "(Sk.arr (domSk qsA) qc)";
    let lam_d = "(WK.lam qD qA qb qsA qc qhA qhb)";
    let lf = format!("(xval qD {lam_t} {lam_s} (r17_wk_wkc qD {lam_t} {lam_s} {lam_d}) qr)");
    let lg = format!("(sval qD {lam_t} {lam_s} {lam_d} qr)");
    let l_point = "(fun (qx : VD (domSk qsA)) => qihb (vconsD (domSk qsA) qD qx qr))";
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK {DB} qb qc) {ih_a} {ih_lb} (qr : VEnvD qD) => r13_vd_arr_funext (domSk qsA) qc {lf} {lg} {l_point})"
    );

    // --- app ---
    let arr = "(Sk.arr qd qcc)";
    let ih_f = format!("(qihf : forall (qr : VEnvD qD), Eq (VD {arr}) (xval qD qf {arr} (r17_wk_wkc qD qf {arr} qhf) qr) (sval qD qf {arr} qhf qr))");
    let ih_ar = "(qiha : forall (qr : VEnvD qD), Eq (VD qd) (xval qD qa qd (r17_wk_wkc qD qa qd qha) qr) (sval qD qa qd qha qr))";
    let xf = format!("(xval qD qf {arr} (r17_wk_wkc qD qf {arr} qhf) qr)");
    let sf = format!("(sval qD qf {arr} qhf qr)");
    let xarg = "(xval qD qa qd (r17_wk_wkc qD qa qd qha) qr)";
    let sarg = "(sval qD qa qd qha qr)";
    let m_app = format!(
        "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf {arr}) (qha : WK qD qa qd) {ih_f} {ih_ar} (qr : VEnvD qD) => r14_vapply_congr qd qcc {xf} {sf} {xarg} {sarg} (qihf qr) (qiha qr))"
    );

    format!("fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) => WK.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h")
}

// ================================================================
// Group B — what `xval` gets NATIVELY, at all SEVEN constructors.
//
// These are not transfers. They are R13's engine re-run on `xval` itself, so
// they hold at `konst` and `let_` derivations too — the two constructors the
// embedding cannot reach.
// ================================================================

/// **`r18_xval_env_congr`** — the interpretation respects pointwise-equal
/// valuations, at every shape environment, term, shape and `WKC` derivation.
///
/// R13's `r13_sval_env_congr` with `xval` in place of `sval`: one
/// `r13_venvD_funext` to turn pointwise agreement into an equality of
/// valuations, one `Eq.cong` to push it through. Nothing about the derivation
/// is inspected, which is precisely why the new constructors cost nothing here.
pub(super) const TY_XVAL_ENV_CONGR: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (hw : WKC D e s) (r : VEnvD D) (r2 : VEnvD D), (forall (i : Nat), Eq (VD (D i)) (r i) (r2 i)) -> Eq (VD s) (xval D e s hw r) (xval D e s hw r2)";

pub(super) const VAL_XVAL_ENV_CONGR: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (hw : WKC D e s) (r : VEnvD D) (r2 : VEnvD D) (h : forall (i : Nat), Eq (VD (D i)) (r i) (r2 i)) => Eq.cong (VEnvD D) (VD s) (fun (qr : VEnvD D) => xval D e s hw qr) r r2 (r13_venvD_funext D r r2 h)";

// ================================================================
// Group C — the SEMANTIC STACK, transferred.
//
// Each of these is the R14/R16 theorem with `sval` replaced by `xval` on both
// sides. The proof shape is always the same three-step sandwich: transfer
// forwards, apply the `sval` theorem, transfer back. Where the SUBJECT also
// changes — `wkc_lift` for `wk_lift` — R17's subsingleton supplies the fourth
// step for free, which is the first payoff `r17_wkc_deriv_unique` has had
// outside its own rung.
// ================================================================

/// **`r18_xval_step`** — R16's ∀-form `val_step`, on the `xval` side.
pub(super) const TY_XVAL_STEP: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (e2 : KExpr) (st : whnf_step e e2) (h2 : WK D e2 s) (r : VEnvD D), Eq (VD s) (xval D e2 s (r17_wk_wkc D e2 s h2) r) (xval D e s (r17_wk_wkc D e s h) r)";

pub(super) const VAL_XVAL_STEP: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (e2 : KExpr) (st : whnf_step e e2) (h2 : WK D e2 s) (r : VEnvD D) => Eq.trans (VD s) (xval D e2 s (r17_wk_wkc D e2 s h2) r) (sval D e2 s h2 r) (xval D e s (r17_wk_wkc D e s h) r) (r18_xval_sval D e2 s h2 r) (Eq.trans (VD s) (sval D e2 s h2 r) (sval D e s h r) (xval D e s (r17_wk_wkc D e s h) r) (r16_val_step D e s h e2 st h2 r) (Eq.symm (VD s) (xval D e s (r17_wk_wkc D e s h) r) (sval D e s h r) (r18_xval_sval D e s h r)))";

/// **`r18_xval_step_star`** — the same along a whole reduction SEQUENCE.
pub(super) const TY_XVAL_STEP_STAR: &str = "forall (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) (s : Sk) (h : WK D e s) (hw : WK D w s) (r : VEnvD D), Eq (VD s) (xval D w s (r17_wk_wkc D w s hw) r) (xval D e s (r17_wk_wkc D e s h) r)";

pub(super) const VAL_XVAL_STEP_STAR: &str = "fun (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) (s : Sk) (h : WK D e s) (hw : WK D w s) (r : VEnvD D) => Eq.trans (VD s) (xval D w s (r17_wk_wkc D w s hw) r) (sval D w s hw r) (xval D e s (r17_wk_wkc D e s h) r) (r18_xval_sval D w s hw r) (Eq.trans (VD s) (sval D w s hw r) (sval D e s h r) (xval D e s (r17_wk_wkc D e s h) r) (r16_val_step_star D e w hstar s h hw r) (Eq.symm (VD s) (xval D e s (r17_wk_wkc D e s h) r) (sval D e s h r) (r18_xval_sval D e s h r)))";

/// **`r18_xval_conv`** — R16's unconditional `val_conv`, on the `xval` side.
///
/// The only one of the four whose conclusion is a MEMBERSHIP rather than an
/// equality, so the transfer is spent through `Eq.substType` in both
/// directions instead of `Eq.trans`.
pub(super) const TY_XVAL_CONV: &str = "forall (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WK D e1 s) (h2 : WK D e2 s) (r : VEnvD D) (t : KExpr), whnfStar e1 w -> whnfStar e2 w -> vcarD s (xval D e1 s (r17_wk_wkc D e1 s h1) r) t -> vcarD s (xval D e2 s (r17_wk_wkc D e2 s h2) r) t";

pub(super) const VAL_XVAL_CONV: &str = "fun (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WK D e1 s) (h2 : WK D e2 s) (r : VEnvD D) (t : KExpr) (st1 : whnfStar e1 w) (st2 : whnfStar e2 w) (hm : vcarD s (xval D e1 s (r17_wk_wkc D e1 s h1) r) t) => Eq.substType (VD s) (fun (qv : VD s) => vcarD s qv t) (sval D e2 s h2 r) (xval D e2 s (r17_wk_wkc D e2 s h2) r) (Eq.symm (VD s) (xval D e2 s (r17_wk_wkc D e2 s h2) r) (sval D e2 s h2 r) (r18_xval_sval D e2 s h2 r)) (r16_val_conv D e1 e2 w s h1 h2 r t st1 st2 (Eq.substType (VD s) (fun (qv : VD s) => vcarD s qv t) (xval D e1 s (r17_wk_wkc D e1 s h1) r) (sval D e1 s h1 r) (r18_xval_sval D e1 s h1 r) hm))";

/// **`r18_xval_lift` — THE SEMANTIC WEAKENING LEMMA, ON R17'S OWN OPERATION.**
///
/// The other three transfers keep the subject fixed and only change the
/// interpretation. This one changes the SUBJECT too: its left-hand side reads
/// `wkc_lift`, the seven-constructor operation R17 built, where `r14_val_lift`
/// reads `wk_lift`. The two produce derivations of the SAME judgment, and
/// R17's `r17_wkc_deriv_unique` says any two such are equal — so
/// `r17_xval_irrel` closes the gap in one step and no commutation lemma
/// between the two operations has to be proved.
///
/// That is the first use `r17_wkc_deriv_unique` has had outside R17, and it is
/// the reason a subsingleton was worth keeping when the conversion rule would
/// have cost it (`r17_conv_verdict`).
pub(super) fn ty_xval_lift() -> String {
    format!("forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (k : Nat) (t : Sk) (r : VEnvD (skins k t D)), Eq (VD s) (xval (skins k t D) (lift_at e k {ONE}) s (wkc_lift D e s (r17_wk_wkc D e s h) k t) r) (xval D e s (r17_wk_wkc D e s h) (venvLiftD k t D r))")
}

pub(super) fn val_xval_lift() -> String {
    let ek = "(skins k t D)";
    let le = format!("(lift_at e k {ONE})");
    let wlift_w = "(wk_lift D e s h k t)";
    let a = format!("(xval {ek} {le} s (wkc_lift D e s (r17_wk_wkc D e s h) k t) r)");
    let b = format!("(xval {ek} {le} s (r17_wk_wkc {ek} {le} s {wlift_w}) r)");
    let c = format!("(sval {ek} {le} s {wlift_w} r)");
    let dd = "(sval D e s h (venvLiftD k t D r))";
    let ee = "(xval D e s (r17_wk_wkc D e s h) (venvLiftD k t D r))";
    format!("fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (k : Nat) (t : Sk) (r : VEnvD {ek}) => Eq.trans (VD s) {a} {c} {ee} (Eq.trans (VD s) {a} {b} {c} (r17_xval_irrel {ek} {le} s (wkc_lift D e s (r17_wk_wkc D e s h) k t) (r17_wk_wkc {ek} {le} s {wlift_w}) r) (r18_xval_sval {ek} {le} s {wlift_w} r)) (Eq.trans (VD s) {c} {dd} {ee} (r14_val_lift D e s h k t r) (Eq.symm (VD s) {ee} {dd} (r18_xval_sval D e s h (venvLiftD k t D r))))")
}

/// **`r18_xval_psub`** — R14's semantic substitution lemma, on `wkc_psub`.
///
/// The same four-step chain as `r18_xval_lift`, and the same reason it is only
/// four: `wkc_psub` at an embedded derivation with an embedded substitution
/// hypothesis, and the embedding of `wk_psub`, derive one judgment, so
/// `r17_wkc_deriv_unique` identifies them through `r17_xval_irrel`.
///
/// **The right-hand side still reads `venvSubD`, which is `WK`-indexed**
/// (`venvSubD sg D Dp hsg r i := sval D (sg i) (Dp i) (hsg i) r`), and that is
/// deliberate: a `WKC`-indexed valuation construction is a DEFINITION, not a
/// corollary of this rung, and inventing one here would put an unproved
/// `xval`-side object into a theorem that is otherwise pure transport.
pub(super) const TY_XVAL_PSUB: &str = "forall (Dp : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK Dp e s) (sg : Nat -> KExpr) (D : Nat -> Sk) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) (r : VEnvD D), Eq (VD s) (xval D (psubst sg e) s (wkc_psub Dp e s (r17_wk_wkc Dp e s h) sg D (fun (qi : Nat) => r17_wk_wkc D (sg qi) (Dp qi) (hsg qi))) r) (xval Dp e s (r17_wk_wkc Dp e s h) (venvSubD sg D Dp hsg r))";

pub(super) fn val_xval_psub() -> String {
    let pe = "(psubst sg e)";
    let hsgc = "(fun (qi : Nat) => r17_wk_wkc D (sg qi) (Dp qi) (hsg qi))";
    let wpc = format!("(wkc_psub Dp e s (r17_wk_wkc Dp e s h) sg D {hsgc})");
    let wpw_wk = "(wk_psub Dp e s h sg D hsg)";
    let wpw = format!("(r17_wk_wkc D {pe} s {wpw_wk})");
    let rs = "(venvSubD sg D Dp hsg r)";
    let a = format!("(xval D {pe} s {wpc} r)");
    let b = format!("(xval D {pe} s {wpw} r)");
    let c = format!("(sval D {pe} s {wpw_wk} r)");
    let dd = format!("(sval Dp e s h {rs})");
    let ee = format!("(xval Dp e s (r17_wk_wkc Dp e s h) {rs})");
    format!("fun (Dp : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK Dp e s) (sg : Nat -> KExpr) (D : Nat -> Sk) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) (r : VEnvD D) => Eq.trans (VD s) {a} {c} {ee} (Eq.trans (VD s) {a} {b} {c} (r17_xval_irrel D {pe} s {wpc} {wpw} r) (r18_xval_sval D {pe} s {wpw_wk} r)) (Eq.trans (VD s) {c} {dd} {ee} (r14_val_psub Dp e s h sg D hsg r) (Eq.symm (VD s) {ee} {dd} (r18_xval_sval Dp e s h {rs})))")
}

/// **`r18_xval_inst`** — R14's instantiation lemma, on `wkc_inst`.
///
/// FIVE steps rather than four, and the fifth is the interesting one. R14's
/// right-hand side extends the valuation by `sval D a d ha r`; the `xval`-side
/// statement must extend it by `xval D a d (wk_wkc ha) r`, so the transfer is
/// spent a THIRD time, under `vconsD`, through one `Eq.cong` in the extension
/// value. That is the only place in this rung where the transfer is used other
/// than at the theorem's own subject.
pub(super) const TY_XVAL_INST: &str = "forall (D : Nat -> Sk) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hb : WK (skcons d D) b c) (ha : WK D a d) (r : VEnvD D), Eq (VD c) (xval D (instantiate b a) c (wkc_inst D b a d c (r17_wk_wkc (skcons d D) b c hb) (r17_wk_wkc D a d ha)) r) (xval (skcons d D) b c (r17_wk_wkc (skcons d D) b c hb) (vconsD d D (xval D a d (r17_wk_wkc D a d ha) r) r))";

pub(super) fn val_xval_inst() -> String {
    let dd_ = "(skcons d D)";
    let ib = "(instantiate b a)";
    let hbc = format!("(r17_wk_wkc {dd_} b c hb)");
    let hac = "(r17_wk_wkc D a d ha)";
    let wic = format!("(wkc_inst D b a d c {hbc} {hac})");
    let wiw_wk = "(wk_inst D b a d c hb ha)";
    let wiw = format!("(r17_wk_wkc D {ib} c {wiw_wk})");
    let sa = "(sval D a d ha r)";
    let xa = format!("(xval D a d {hac} r)");
    let a = format!("(xval D {ib} c {wic} r)");
    let b = format!("(xval D {ib} c {wiw} r)");
    let cc = format!("(sval D {ib} c {wiw_wk} r)");
    let ee = format!("(sval {dd_} b c hb (vconsD d D {sa} r))");
    let ff = format!("(xval {dd_} b c {hbc} (vconsD d D {sa} r))");
    let gg = format!("(xval {dd_} b c {hbc} (vconsD d D {xa} r))");
    let step_cong = format!("(Eq.cong (VD d) (VD c) (fun (qv : VD d) => xval {dd_} b c {hbc} (vconsD d D qv r)) {sa} {xa} (Eq.symm (VD d) {xa} {sa} (r18_xval_sval D a d ha r)))");
    let step_ef =
        format!("(Eq.symm (VD c) {ff} {ee} (r18_xval_sval {dd_} b c hb (vconsD d D {sa} r)))");
    format!("fun (D : Nat -> Sk) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hb : WK {dd_} b c) (ha : WK D a d) (r : VEnvD D) => Eq.trans (VD c) {a} {cc} {gg} (Eq.trans (VD c) {a} {b} {cc} (r17_xval_irrel D {ib} c {wic} {wiw} r) (r18_xval_sval D {ib} c {wiw_wk} r)) (Eq.trans (VD c) {cc} {ee} {gg} (r14_val_inst D b a d c hb ha r) (Eq.trans (VD c) {ee} {ff} {gg} {step_ef} {step_cong}))")
}

// ================================================================
// Group D — the witnesses, at REAL objects.
// ================================================================

/// The transfer at R12's registered β redex and its derivation — a real
/// application of a real lambda, under the all-junk valuation.
pub(super) fn ty_transfer_witness() -> String {
    format!("Eq (VD {KDTY}) (xval r12_betaEnv r12_betaRedex {KDTY} (r17_wk_wkc r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv) r12_betaJunkEnv) (sval r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r12_betaJunkEnv)")
}

pub(super) fn val_transfer_witness() -> String {
    format!("r18_xval_sval r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r12_betaJunkEnv")
}

/// `r18_xval_step` COMPUTED at R12's redex and its contractum — R16's
/// `r16_val_step_witness` with both interpretations moved to `xval`.
pub(super) fn ty_xval_step_witness() -> String {
    format!("Eq (VD {KDTY}) (xval r12_betaEnv {INST0} {KDTY} (r17_wk_wkc r12_betaEnv {INST0} {KDTY} r15_instDeriv) r12_betaJunkEnv) (xval r12_betaEnv r12_betaRedex {KDTY} (r17_wk_wkc r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv) r12_betaJunkEnv)")
}

pub(super) fn val_xval_step_witness() -> String {
    format!("r18_xval_step r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv {INST0} (r14_beta_step {V0} {V0} {S0}) r15_instDeriv r12_betaJunkEnv")
}

// ================================================================
// Group E — negative controls. NOT registered; the refusal tests feed these
// to `add_definition` and require the kernel to REJECT them.
// ================================================================

/// The transfer with `Eq.refl` for a proof. The two sides are `WKC.rec` and
/// `WK.rec` stuck on a VARIABLE derivation, so neither reduces and the kernel
/// must refuse — the measurement that the transfer does real work rather than
/// restating a definitional identity.
#[cfg(test)]
pub(super) fn probe_transfer_refl() -> String {
    format!(
        "def r18_transfer_refl_probe : {TY_XVAL_SVAL} := fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D) => Eq.refl (VD s) (xval D e s (r17_wk_wkc D e s h) r)"
    )
}

/// `r18_xval_lift` GENERALISED to an arbitrary `WKC` derivation, with the same
/// proof. It must be refused: the proof's third step is `r14_val_lift`, whose
/// subject is a `WK` derivation, and a `konst`- or `let_`-headed `WKC`
/// derivation is not one. This is the SCOPE of Group C, made machine-visible.
#[cfg(test)]
pub(super) fn probe_lift_at_wkc() -> String {
    format!(
        "def r18_lift_at_wkc_probe : forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (hw : WKC D e s) (k : Nat) (t : Sk) (r : VEnvD (skins k t D)), Eq (VD s) (xval (skins k t D) (lift_at e k {ONE}) s (wkc_lift D e s hw k t) r) (xval D e s hw (venvLiftD k t D r)) := {}",
        val_xval_lift()
    )
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R18Item {
    /// `add_definition` — a theorem whose proof term the kernel type-checks.
    Thm {
        name: String,
        ty: String,
        val: String,
    },
}

#[cfg(test)]
impl R18Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R18Item::Thm { name, .. } => name,
        }
    }

    /// The item as ONE parse-checkable declaration, for the parse gate.
    pub(super) fn decl_source(&self) -> String {
        match self {
            R18Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn t(name: &str, ty: String, val: String) -> R18Item {
    R18Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R18 constant, in registration order.
pub(super) fn r18_items() -> Vec<R18Item> {
    vec![
        // --- Group A: the transfer.
        t("r18_xval_sval", TY_XVAL_SVAL.to_string(), val_xval_sval()),
        // --- Group B: native, at all seven constructors.
        t(
            "r18_xval_env_congr",
            TY_XVAL_ENV_CONGR.to_string(),
            VAL_XVAL_ENV_CONGR.to_string(),
        ),
        // --- Group C: the semantic stack, transferred.
        t(
            "r18_xval_step",
            TY_XVAL_STEP.to_string(),
            VAL_XVAL_STEP.to_string(),
        ),
        t(
            "r18_xval_step_star",
            TY_XVAL_STEP_STAR.to_string(),
            VAL_XVAL_STEP_STAR.to_string(),
        ),
        t(
            "r18_xval_conv",
            TY_XVAL_CONV.to_string(),
            VAL_XVAL_CONV.to_string(),
        ),
        t("r18_xval_lift", ty_xval_lift(), val_xval_lift()),
        t("r18_xval_psub", TY_XVAL_PSUB.to_string(), val_xval_psub()),
        t("r18_xval_inst", TY_XVAL_INST.to_string(), val_xval_inst()),
        // --- Group D: the witnesses.
        t(
            "r18_transfer_witness",
            ty_transfer_witness(),
            val_transfer_witness(),
        ),
        t(
            "r18_xval_step_witness",
            ty_xval_step_witness(),
            val_xval_step_witness(),
        ),
    ]
}

/// Every R18 source as a parse-checkable declaration, for the parse gate and
/// the scratch harness.
#[cfg(test)]
pub(super) fn r18_all_sources() -> Vec<(String, String)> {
    r18_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
