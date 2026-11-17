// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R21 sources — **THE NATIVE STEP LAW**: subject reduction carrying a semantic
//! equation, by induction on `WKC`, at all seven constructors.
//!
//! See the module doc of [`super::candmodel_construct_r21`] for the argument.

// **This module deliberately imports nothing** — the R12-R20 convention.

/// The `head_free` reflexivity witness R15's inversion takes at every head that
/// is not an application.
const HF_REFL: &str = "(@Eq.refl (OptionType Name) (@OptionType.none Name))";
/// R12's `KDTY`.
const KDTY: &str = "(Sk.kd Sk.ty)";

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

/// R15's CPS continuation shape: from a step out of `src`, hand back a
/// derivation of the reduct AND the semantic equation, at `xval`.
fn sem_k(d: &str, e2: &str, s: &str, src: &str, c: &str) -> String {
    format!("forall (zh2 : WKC {d} {e2} {s}), (forall (zr : VEnvD {d}), @Eq (VD {s}) (xval {d} {e2} {s} zh2 zr) ({src} zr)) -> {c}")
}

// ================================================================
// Group A — the SEMANTIC lambda inversion.
// ================================================================

/// **`r21_xvalLamT`** — R15's `r15_svalLamT` over `WKC`/`xval`.
///
/// The computed CPS result type at NINE `KExpr` heads: `ConstFreeUnit` at eight
/// of them and, at a `lam` whose shape is an ARROW, the real obligation — hand
/// back a body derivation together with the semantic equation saying the
/// lambda's denotation applied to a value IS the body's denotation at the
/// extended valuation. Computing the type rather than writing an inductive is
/// R15's discipline: the impossible heads die by COMPUTATION.
pub(super) const SRC_XVAL_LAM_T: &str = "def r21_xvalLamT (D : Nat -> Sk) (C : Type) (e : KExpr) (s : Sk) (F : VEnvD D -> VD s) : Type := @KExpr.rec (fun (qe : KExpr) => forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (fun (qn : Level) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qi : Nat) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qf : KExpr) (qa : KExpr) (qihf : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qiha : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qA : KExpr) (qb : KExpr) (qihA : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qihb : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) => @Sk.rec (fun (qz : Sk) => (VEnvD D -> VD qz) -> Type) (fun (qF : VEnvD D -> VD Sk.ty) => ConstFreeUnit) (fun (qs1 : Sk) (qih : (VEnvD D -> VD qs1) -> Type) (qF : VEnvD D -> VD (Sk.kd qs1)) => ConstFreeUnit) (fun (qd : Sk) (qc : Sk) (qihd : (VEnvD D -> VD qd) -> Type) (qihc : (VEnvD D -> VD qc) -> Type) (qF : VEnvD D -> VD (Sk.arr qd qc)) => (forall (zhb : WKC (skcons qd D) qb qc), (forall (zr : VEnvD D) (zx : VD qd), @Eq (VD qc) (qF zr zx) (xval (skcons qd D) qb qc zhb (vconsD qd D zx zr))) -> C) -> C)) (fun (qA : KExpr) (qB : KExpr) (qihA : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qihB : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qn : Name) (qus : ListType Level) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qt : KExpr) (qv : KExpr) (qb : KExpr) (qiht : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qihv : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qihb : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qsn : Name) (qpi : Nat) (qsub : KExpr) (qihs : forall (qs : Sk), (VEnvD D -> VD qs) -> Type) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) (fun (qv : Nat) (qs : Sk) (qF : VEnvD D -> VD qs) => ConstFreeUnit) e s F";

/// **`r21_xval_lam_inv`** — that inversion, proved by `WKC.rec`.
///
/// Six arms are `ConstFreeUnit.triv` by computation; the `lam` arm hands back
/// its OWN body premise with `Eq.refl`, because `xval`'s `lam` clause is
/// literally the extended-valuation reading. The two new constructors cost one
/// token each, for the same reason the five old non-`lam` ones do.
pub(super) fn src_xval_lam_inv() -> String {
    let dsa = "(skcons (domSk qsA) qD)";
    let motive = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => r21_xvalLamT qD C qe qs (xval qD qe qs qh))";
    let m_var = "(fun (qD : Nat -> Sk) (qi : Nat) => ConstFreeUnit.triv)";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) => ConstFreeUnit.triv)";
    let m_pi = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC {dsa} qB qsB) (qihA : r21_xvalLamT qD C qA qsA (xval qD qA qsA qhA)) (qihB : r21_xvalLamT {dsa} C qB qsB (xval {dsa} qB qsB qhB)) => ConstFreeUnit.triv)");
    let cont = format!("(zk : forall (zhb : WKC {dsa} qb qc), (forall (zr : VEnvD qD) (zx : VD (domSk qsA)), @Eq (VD qc) (xval qD (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc) (WKC.lam qD qA qb qsA qc qhA qhb) zr zx) (xval {dsa} qb qc zhb (vconsD (domSk qsA) qD zx zr))) -> C)");
    let m_lam = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC {dsa} qb qc) (qihA : r21_xvalLamT qD C qA qsA (xval qD qA qsA qhA)) (qihb : r21_xvalLamT {dsa} C qb qc (xval {dsa} qb qc qhb)) {cont} => zk qhb (fun (zr : VEnvD qD) (zx : VD (domSk qsA)) => @Eq.refl (VD qc) (xval {dsa} qb qc qhb (vconsD (domSk qsA) qD zx zr))))");
    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) (qihf : r21_xvalLamT qD C qf (Sk.arr qd qcc) (xval qD qf (Sk.arr qd qcc) qhf)) (qiha : r21_xvalLamT qD C qa qd (xval qD qa qd qha)) => ConstFreeUnit.triv)";
    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) => ConstFreeUnit.triv)",
        defval_none("qn"),
        recmeta_none("qn")
    );
    let ldp = "(skcons qsv qD)";
    let m_let = format!("(fun (qD : Nat -> Sk) (qtt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qtt qst) (qhv : WKC qD qv qsv) (qhb : WKC {ldp} qb qc) (qiht : r21_xvalLamT qD C qtt qst (xval qD qtt qst qht)) (qihv : r21_xvalLamT qD C qv qsv (xval qD qv qsv qhv)) (qihb : r21_xvalLamT {ldp} C qb qc (xval {ldp} qb qc qhb)) => ConstFreeUnit.triv)");
    format!("def r21_xval_lam_inv (D : Nat -> Sk) (C : Type) (e : KExpr) (s : Sk) (h : WKC D e s) : r21_xvalLamT D C e s (xval D e s h) := @WKC.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h")
}

// ================================================================
// Group B — THE NATIVE STEP LAW.
// ================================================================

/// **`r21_xval_step_sem`** — R15's `val_step_sem` at seven constructors.
pub(super) fn ty_xval_step_sem() -> String {
    format!(
        "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (e2 : KExpr) (st : whnf_step e e2) (C : Type), ({}) -> C",
        sem_k("D", "e2", "s", "(xval D e s h)", "C")
    )
}

/// The native proof: `WKC.rec` at seven arms, each dispatching through R15's
/// `r15_whnf_stepT_inv` (or, at `let_`, R1's `letRedex_whnf_inv`) and pairing
/// the derivation `wkc_step` would build with its semantic equation.
#[allow(clippy::too_many_lines)]
pub(super) fn val_xval_step_sem() -> String {
    let mot = format!(
        "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => forall (qe2 : KExpr) (qst : whnf_step qe qe2) (qC : Type), ({}) -> qC)",
        sem_k("qD", "qe2", "qs", "(xval qD qe qs qh)", "qC")
    );

    let m_var = format!(
        "(fun (qD : Nat -> Sk) (qi : Nat) (qe2 : KExpr) (qst : whnf_step (KExpr.bvar qi) qe2) (qC : Type) (qk : {}) => r15_whnf_stepT_inv qC (KExpr.bvar qi) qe2 {HF_REFL} qst)",
        sem_k("qD", "qe2", "(qD qi)", "(xval qD (KExpr.bvar qi) (qD qi) (WKC.var qD qi))", "qC")
    );
    let m_sort = format!(
        "(fun (qD : Nat -> Sk) (qn : Level) (qe2 : KExpr) (qst : whnf_step (KExpr.sort qn) qe2) (qC : Type) (qk : {}) => r15_whnf_stepT_inv qC (KExpr.sort qn) qe2 {HF_REFL} qst)",
        sem_k("qD", "qe2", KDTY, &format!("(xval qD (KExpr.sort qn) {KDTY} (WKC.sort qD qn))"), "qC")
    );

    // ---- pi ----
    let dsa = "(skcons (domSk qsA) qD)";
    let pshape = "(piShape qsA qsB)";
    let pderiv = "(WKC.pi qD qA qB qsA qsB qhA qhB)";
    let ih_a = format!(
        "(qihA : forall (qz : KExpr) (qzs : whnf_step qA qz) (qzC : Type), ({}) -> qzC)",
        sem_k("qD", "qz", "qsA", "(xval qD qA qsA qhA)", "qzC")
    );
    let ih_pb = format!(
        "(qihB : forall (qz : KExpr) (qzs : whnf_step qB qz) (qzC : Type), ({}) -> qzC)",
        sem_k(dsa, "qz", "qsB", &format!("(xval {dsa} qB qsB qhB)"), "qzC")
    );
    let kpi = sem_k(
        "qD",
        "qe2",
        pshape,
        &format!("(xval qD (KExpr.pi qA qB) {pshape} {pderiv})"),
        "qC",
    );
    let jenv = "(vconsD (domSk qsA) qD (junkD (domSk qsA)) zr)";
    let vb = format!("(xval {dsa} qB qsB qhB {jenv})");
    let nd1 = "(WKC.pi qD zy qB qsA qsB zh2 qhB)";
    let cast1 = format!("(r17_wkcCastT qD (KExpr.pi zy qB) qe2 {pshape} (@Eq.symm KExpr qe2 (KExpr.pi zy qB) zeq) {nd1})");
    let lhs1 = format!("(xval qD qe2 {pshape} {cast1} zr)");
    let mid1 = format!("(xval qD (KExpr.pi zy qB) {pshape} {nd1} zr)");
    let rhs1 = format!("(xval qD (KExpr.pi qA qB) {pshape} {pderiv} zr)");
    let step1 = format!("(r20_xval_cast_term qD (KExpr.pi zy qB) qe2 {pshape} (@Eq.symm KExpr qe2 (KExpr.pi zy qB) zeq) {nd1} zr)");
    let cong1 = format!("(r14_sval_pi_congr qsA qsB (xval qD zy qsA zh2 zr) (xval qD qA qsA qhA zr) {vb} {vb} (zhv zr) (@Eq.refl (VD qsB) {vb}))");
    let p1 = format!("(fun (zy : KExpr) (zst : beta_reduces qA zy) (zeq : @Eq KExpr qe2 (KExpr.pi zy qB)) => qihA zy (@whnf_step.beta qA zy zst) qC (fun (zh2 : WKC qD zy qsA) (zhv : forall (zr : VEnvD qD), @Eq (VD qsA) (xval qD zy qsA zh2 zr) (xval qD qA qsA qhA zr)) => qk {cast1} (fun (zr : VEnvD qD) => @Eq.trans (VD {pshape}) {lhs1} {mid1} {rhs1} {step1} {cong1})))");
    let nd2 = "(WKC.pi qD qA zy qsA qsB qhA zh2)";
    let cast2 = format!("(r17_wkcCastT qD (KExpr.pi qA zy) qe2 {pshape} (@Eq.symm KExpr qe2 (KExpr.pi qA zy) zeq) {nd2})");
    let lhs2 = format!("(xval qD qe2 {pshape} {cast2} zr)");
    let mid2 = format!("(xval qD (KExpr.pi qA zy) {pshape} {nd2} zr)");
    let step2 = format!("(r20_xval_cast_term qD (KExpr.pi qA zy) qe2 {pshape} (@Eq.symm KExpr qe2 (KExpr.pi qA zy) zeq) {nd2} zr)");
    let va = "(xval qD qA qsA qhA zr)";
    let vb2 = format!("(xval {dsa} zy qsB zh2 {jenv})");
    let cong2 = format!(
        "(r14_sval_pi_congr qsA qsB {va} {va} {vb2} {vb} (@Eq.refl (VD qsA) {va}) (zhv {jenv}))"
    );
    let p2 = format!("(fun (zy : KExpr) (zst : beta_reduces qB zy) (zeq : @Eq KExpr qe2 (KExpr.pi qA zy)) => qihB zy (@whnf_step.beta qB zy zst) qC (fun (zh2 : WKC {dsa} zy qsB) (zhv : forall (zr : VEnvD {dsa}), @Eq (VD qsB) (xval {dsa} zy qsB zh2 zr) (xval {dsa} qB qsB qhB zr)) => qk {cast2} (fun (zr : VEnvD qD) => @Eq.trans (VD {pshape}) {lhs2} {mid2} {rhs1} {step2} {cong2})))");
    let m_pi = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC {dsa} qB qsB) {ih_a} {ih_pb} (qe2 : KExpr) (qst : whnf_step (KExpr.pi qA qB) qe2) (qC : Type) (qk : {kpi}) => r15_whnf_stepT_inv qC (KExpr.pi qA qB) qe2 {HF_REFL} qst {p1} {p2})");

    // ---- lam ----
    let lshape = "(Sk.arr (domSk qsA) qc)";
    let lderiv = "(WKC.lam qD qA qb qsA qc qhA qhb)";
    let ih_la = format!(
        "(qihA : forall (qz : KExpr) (qzs : whnf_step qA qz) (qzC : Type), ({}) -> qzC)",
        sem_k("qD", "qz", "qsA", "(xval qD qA qsA qhA)", "qzC")
    );
    let ih_lb = format!(
        "(qihb : forall (qz : KExpr) (qzs : whnf_step qb qz) (qzC : Type), ({}) -> qzC)",
        sem_k(dsa, "qz", "qc", &format!("(xval {dsa} qb qc qhb)"), "qzC")
    );
    let klam = sem_k(
        "qD",
        "qe2",
        lshape,
        &format!("(xval qD (KExpr.lam qA qb) {lshape} {lderiv})"),
        "qC",
    );
    let lnd1 = "(WKC.lam qD zy qb qsA qc zh2 qhb)";
    let lcast1 = format!("(r17_wkcCastT qD (KExpr.lam zy qb) qe2 {lshape} (@Eq.symm KExpr qe2 (KExpr.lam zy qb) zeq) {lnd1})");
    let llhs1 = format!("(xval qD qe2 {lshape} {lcast1} zr)");
    let lmid1 = format!("(xval qD (KExpr.lam zy qb) {lshape} {lnd1} zr)");
    let lrhs = format!("(xval qD (KExpr.lam qA qb) {lshape} {lderiv} zr)");
    let lstep1 = format!("(r20_xval_cast_term qD (KExpr.lam zy qb) qe2 {lshape} (@Eq.symm KExpr qe2 (KExpr.lam zy qb) zeq) {lnd1} zr)");
    let l1 = format!("(fun (zy : KExpr) (zst : beta_reduces qA zy) (zeq : @Eq KExpr qe2 (KExpr.lam zy qb)) => qihA zy (@whnf_step.beta qA zy zst) qC (fun (zh2 : WKC qD zy qsA) (zhv : forall (zr : VEnvD qD), @Eq (VD qsA) (xval qD zy qsA zh2 zr) (xval qD qA qsA qhA zr)) => qk {lcast1} (fun (zr : VEnvD qD) => @Eq.trans (VD {lshape}) {llhs1} {lmid1} {lrhs} {lstep1} (@Eq.refl (VD {lshape}) {lrhs}))))");
    let lnd2 = "(WKC.lam qD qA zy qsA qc qhA zh2)";
    let lcast2 = format!("(r17_wkcCastT qD (KExpr.lam qA zy) qe2 {lshape} (@Eq.symm KExpr qe2 (KExpr.lam qA zy) zeq) {lnd2})");
    let llhs2 = format!("(xval qD qe2 {lshape} {lcast2} zr)");
    let lmid2 = format!("(xval qD (KExpr.lam qA zy) {lshape} {lnd2} zr)");
    let lstep2 = format!("(r20_xval_cast_term qD (KExpr.lam qA zy) qe2 {lshape} (@Eq.symm KExpr qe2 (KExpr.lam qA zy) zeq) {lnd2} zr)");
    let lfun = format!("(r13_vd_arr_funext (domSk qsA) qc {lmid2} {lrhs} (fun (zx : VD (domSk qsA)) => zhv (vconsD (domSk qsA) qD zx zr)))");
    let l2 = format!("(fun (zy : KExpr) (zst : beta_reduces qb zy) (zeq : @Eq KExpr qe2 (KExpr.lam qA zy)) => qihb zy (@whnf_step.beta qb zy zst) qC (fun (zh2 : WKC {dsa} zy qc) (zhv : forall (zr : VEnvD {dsa}), @Eq (VD qc) (xval {dsa} zy qc zh2 zr) (xval {dsa} qb qc qhb zr)) => qk {lcast2} (fun (zr : VEnvD qD) => @Eq.trans (VD {lshape}) {llhs2} {lmid2} {lrhs} {lstep2} {lfun})))");
    let m_lam = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC {dsa} qb qc) {ih_la} {ih_lb} (qe2 : KExpr) (qst : whnf_step (KExpr.lam qA qb) qe2) (qC : Type) (qk : {klam}) => r15_whnf_stepT_inv qC (KExpr.lam qA qb) qe2 {HF_REFL} qst {l1} {l2})");

    // ---- app ----
    let aderiv = "(WKC.app qD qf qa qd qcc qhf qha)";
    let ih_f = format!(
        "(qihf : forall (qz : KExpr) (qzs : whnf_step qf qz) (qzC : Type), ({}) -> qzC)",
        sem_k(
            "qD",
            "qz",
            "(Sk.arr qd qcc)",
            "(xval qD qf (Sk.arr qd qcc) qhf)",
            "qzC"
        )
    );
    let ih_ar = format!(
        "(qiha : forall (qz : KExpr) (qzs : whnf_step qa qz) (qzC : Type), ({}) -> qzC)",
        sem_k("qD", "qz", "qd", "(xval qD qa qd qha)", "qzC")
    );
    let kapp = sem_k(
        "qD",
        "qe2",
        "qcc",
        &format!("(xval qD (KExpr.app qf qa) qcc {aderiv})"),
        "qC",
    );
    let hf = "(headFree_app qf qa (r17_headFree_wkc_arr qD qf (Sk.arr qd qcc) qhf qd qcc (@Eq.refl Sk (Sk.arr qd qcc))))";
    let xv = "(xval qD qa qd qha zr)";
    let arhs = format!("(xval qD (KExpr.app qf qa) qcc {aderiv} zr)");
    let hfl = "(r17_wkcCastT qD qf (KExpr.lam zA zb) (Sk.arr qd qcc) zlam qhf)";
    let hinst = "(wkc_inst qD zb qa qd qcc zhb qha)";
    let h2b = format!("(r17_wkcCastT qD (instantiate zb qa) qe2 qcc (@Eq.symm KExpr qe2 (instantiate zb qa) zcon) {hinst})");
    let bx1 = format!("(xval qD qe2 qcc {h2b} zr)");
    let bx2 = format!("(xval qD (instantiate zb qa) qcc {hinst} zr)");
    let bx3 = format!("(xval (skcons qd qD) zb qcc zhb (vconsD qd qD {xv} zr))");
    let bx4 = format!("(xval qD (KExpr.lam zA zb) (Sk.arr qd qcc) {hfl} zr {xv})");
    let bs1 = format!("(r20_xval_cast_term qD (instantiate zb qa) qe2 qcc (@Eq.symm KExpr qe2 (instantiate zb qa) zcon) {hinst} zr)");
    let bs2 = "(r20_xval_inst qD zb qa qd qcc zhb qha zr)";
    let bs3 = format!("(@Eq.symm (VD qcc) {bx4} {bx3} (zsem zr {xv}))");
    let bs4 = format!("(@Eq.cong (VD (Sk.arr qd qcc)) (VD qcc) (fun (zF : VD (Sk.arr qd qcc)) => zF {xv}) (xval qD (KExpr.lam zA zb) (Sk.arr qd qcc) {hfl} zr) (xval qD qf (Sk.arr qd qcc) qhf zr) (r20_xval_cast_term qD qf (KExpr.lam zA zb) (Sk.arr qd qcc) zlam qhf zr))");
    let bchain = format!("(@Eq.trans (VD qcc) {bx1} {bx3} {arhs} (@Eq.trans (VD qcc) {bx1} {bx2} {bx3} {bs1} {bs2}) (@Eq.trans (VD qcc) {bx3} {bx4} {arhs} {bs3} {bs4}))");
    let semcont = format!("(zsem : forall (zr : VEnvD qD) (zx : VD qd), @Eq (VD qcc) (xval qD (KExpr.lam zA zb) (Sk.arr qd qcc) {hfl} zr zx) (xval (skcons qd qD) zb qcc zhb (vconsD qd qD zx zr)))");
    let a1 = format!("(fun (zA : KExpr) (zb : KExpr) (zlam : @Eq KExpr qf (KExpr.lam zA zb)) (zcon : @Eq KExpr qe2 (instantiate zb qa)) => r21_xval_lam_inv qD qC (KExpr.lam zA zb) (Sk.arr qd qcc) {hfl} (fun (zhb : WKC (skcons qd qD) zb qcc) {semcont} => qk {h2b} (fun (zr : VEnvD qD) => {bchain})))");
    let and2 = "(WKC.app qD zy qa qd qcc zh2 qha)";
    let acast2 = format!("(r17_wkcCastT qD (KExpr.app zy qa) qe2 qcc (@Eq.symm KExpr qe2 (KExpr.app zy qa) zeq) {and2})");
    let al1 = format!("(xval qD qe2 qcc {acast2} zr)");
    let al2 = format!("(xval qD (KExpr.app zy qa) qcc {and2} zr)");
    let as1 = format!("(r20_xval_cast_term qD (KExpr.app zy qa) qe2 qcc (@Eq.symm KExpr qe2 (KExpr.app zy qa) zeq) {and2} zr)");
    let ac1 = format!("(r14_vapply_congr qd qcc (xval qD zy (Sk.arr qd qcc) zh2 zr) (xval qD qf (Sk.arr qd qcc) qhf zr) {xv} {xv} (zhv zr) (@Eq.refl (VD qd) {xv}))");
    let a2 = format!("(fun (zy : KExpr) (zst : beta_reduces qf zy) (zeq : @Eq KExpr qe2 (KExpr.app zy qa)) => qihf zy (@whnf_step.beta qf zy zst) qC (fun (zh2 : WKC qD zy (Sk.arr qd qcc)) (zhv : forall (zr : VEnvD qD), @Eq (VD (Sk.arr qd qcc)) (xval qD zy (Sk.arr qd qcc) zh2 zr) (xval qD qf (Sk.arr qd qcc) qhf zr)) => qk {acast2} (fun (zr : VEnvD qD) => @Eq.trans (VD qcc) {al1} {al2} {arhs} {as1} {ac1})))");
    let and3 = "(WKC.app qD qf zy qd qcc qhf zh2)";
    let acast3 = format!("(r17_wkcCastT qD (KExpr.app qf zy) qe2 qcc (@Eq.symm KExpr qe2 (KExpr.app qf zy) zeq) {and3})");
    let ar1 = format!("(xval qD qe2 qcc {acast3} zr)");
    let ar2 = format!("(xval qD (KExpr.app qf zy) qcc {and3} zr)");
    let as2 = format!("(r20_xval_cast_term qD (KExpr.app qf zy) qe2 qcc (@Eq.symm KExpr qe2 (KExpr.app qf zy) zeq) {and3} zr)");
    let ffv = "(xval qD qf (Sk.arr qd qcc) qhf zr)";
    let ac2 = format!("(r14_vapply_congr qd qcc {ffv} {ffv} (xval qD zy qd zh2 zr) {xv} (@Eq.refl (VD (Sk.arr qd qcc)) {ffv}) (zhv zr))");
    let a3 = format!("(fun (zy : KExpr) (zst : beta_reduces qa zy) (zeq : @Eq KExpr qe2 (KExpr.app qf zy)) => qiha zy (@whnf_step.beta qa zy zst) qC (fun (zh2 : WKC qD zy qd) (zhv : forall (zr : VEnvD qD), @Eq (VD qd) (xval qD zy qd zh2 zr) (xval qD qa qd qha zr)) => qk {acast3} (fun (zr : VEnvD qD) => @Eq.trans (VD qcc) {ar1} {ar2} {arhs} {as2} {ac2})))");
    let m_app = format!("(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) {ih_f} {ih_ar} (qe2 : KExpr) (qst : whnf_step (KExpr.app qf qa) qe2) (qC : Type) (qk : {kapp}) => r15_whnf_stepT_inv qC (KExpr.app qf qa) qe2 {hf} qst {a1} {a2} {a3})");

    // ---- konst: REFUTED, an inert constant admits no step at all ----
    let kkonst = sem_k(
        "qD",
        "qe2",
        "Sk.ty",
        "(xval qD (KExpr.const qn qus) Sk.ty (WKC.konst qD qn qus qhd qhr))",
        "qC",
    );
    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) (qe2 : KExpr) (qst : whnf_step (KExpr.const qn qus) qe2) (qC : Type) (qk : {kkonst}) => r17_const_no_step qn qus qe2 qC qhd qst)",
        defval_none("qn"),
        recmeta_none("qn")
    );

    // ---- let_ ----
    let ldd = "(skcons qsv qD)";
    let lderiv2 = "(WKC.let_ qD qtt qv qb qst qsv qc qht qhv qhb)";
    let iht = format!(
        "(qiht : forall (qz : KExpr) (qzs : whnf_step qtt qz) (qzC : Type), ({}) -> qzC)",
        sem_k("qD", "qz", "qst", "(xval qD qtt qst qht)", "qzC")
    );
    let ihv = format!(
        "(qihv : forall (qz : KExpr) (qzs : whnf_step qv qz) (qzC : Type), ({}) -> qzC)",
        sem_k("qD", "qz", "qsv", "(xval qD qv qsv qhv)", "qzC")
    );
    let ihb = format!(
        "(qihb : forall (qz : KExpr) (qzs : whnf_step qb qz) (qzC : Type), ({}) -> qzC)",
        sem_k(ldd, "qz", "qc", &format!("(xval {ldd} qb qc qhb)"), "qzC")
    );
    let klet = sem_k(
        "qD",
        "qe2",
        "qc",
        &format!("(xval qD (KExpr.let_ qtt qv qb) qc {lderiv2})"),
        "qC",
    );
    let lrhs2 = format!("(xval qD (KExpr.let_ qtt qv qb) qc {lderiv2} zr)");
    // zeta: the contractum's interpretation IS the let clause's, definitionally.
    let zinst = "(wkc_inst qD qb qv qsv qc qhb qhv)";
    let zcast = format!("(r17_wkcCastT qD (instantiate qb qv) qe2 qc (@Eq.symm KExpr qe2 (instantiate qb qv) zeq) {zinst})");
    let zx1 = format!("(xval qD qe2 qc {zcast} zr)");
    let zx2 = format!("(xval qD (instantiate qb qv) qc {zinst} zr)");
    let zs1 = format!("(r20_xval_cast_term qD (instantiate qb qv) qe2 qc (@Eq.symm KExpr qe2 (instantiate qb qv) zeq) {zinst} zr)");
    let zs2 = "(r20_xval_inst qD qb qv qsv qc qhb qhv zr)";
    let z0 = format!("(fun (zeq : @Eq KExpr qe2 (instantiate qb qv)) => qk {zcast} (fun (zr : VEnvD qD) => @Eq.trans (VD qc) {zx1} {zx2} {lrhs2} {zs1} {zs2}))");
    // congruence in the ANNOTATION: xval never reads it, so the equation is Eq.refl.
    let tnd = "(WKC.let_ qD zy qv qb qst qsv qc zh2 qhv qhb)";
    let tcast = format!("(r17_wkcCastT qD (KExpr.let_ zy qv qb) qe2 qc (@Eq.symm KExpr qe2 (KExpr.let_ zy qv qb) zeq) {tnd})");
    let tx1 = format!("(xval qD qe2 qc {tcast} zr)");
    let tx2 = format!("(xval qD (KExpr.let_ zy qv qb) qc {tnd} zr)");
    let ts1 = format!("(r20_xval_cast_term qD (KExpr.let_ zy qv qb) qe2 qc (@Eq.symm KExpr qe2 (KExpr.let_ zy qv qb) zeq) {tnd} zr)");
    let z1 = format!("(fun (zy : KExpr) (zst2 : beta_reduces qtt zy) (zeq : @Eq KExpr qe2 (KExpr.let_ zy qv qb)) => qiht zy (@whnf_step.beta qtt zy zst2) qC (fun (zh2 : WKC qD zy qst) (zhv : forall (zr : VEnvD qD), @Eq (VD qst) (xval qD zy qst zh2 zr) (xval qD qtt qst qht zr)) => qk {tcast} (fun (zr : VEnvD qD) => @Eq.trans (VD qc) {tx1} {tx2} {lrhs2} {ts1} (@Eq.refl (VD qc) {lrhs2}))))");
    // congruence in the VALUE: one Eq.cong in the extension value.
    let vnd = "(WKC.let_ qD qtt zy qb qst qsv qc qht zh2 qhb)";
    let vcast = format!("(r17_wkcCastT qD (KExpr.let_ qtt zy qb) qe2 qc (@Eq.symm KExpr qe2 (KExpr.let_ qtt zy qb) zeq) {vnd})");
    let vx1 = format!("(xval qD qe2 qc {vcast} zr)");
    let vx2 = format!("(xval qD (KExpr.let_ qtt zy qb) qc {vnd} zr)");
    let vs1 = format!("(r20_xval_cast_term qD (KExpr.let_ qtt zy qb) qe2 qc (@Eq.symm KExpr qe2 (KExpr.let_ qtt zy qb) zeq) {vnd} zr)");
    let vcong = format!("(@Eq.cong (VD qsv) (VD qc) (fun (zw : VD qsv) => xval {ldd} qb qc qhb (vconsD qsv qD zw zr)) (xval qD zy qsv zh2 zr) (xval qD qv qsv qhv zr) (zhv zr))");
    let z2 = format!("(fun (zy : KExpr) (zst2 : beta_reduces qv zy) (zeq : @Eq KExpr qe2 (KExpr.let_ qtt zy qb)) => qihv zy (@whnf_step.beta qv zy zst2) qC (fun (zh2 : WKC qD zy qsv) (zhv : forall (zr : VEnvD qD), @Eq (VD qsv) (xval qD zy qsv zh2 zr) (xval qD qv qsv qhv zr)) => qk {vcast} (fun (zr : VEnvD qD) => @Eq.trans (VD qc) {vx1} {vx2} {lrhs2} {vs1} {vcong})))");
    // congruence in the BODY: the body hypothesis at the value-extended valuation.
    let bnd = "(WKC.let_ qD qtt qv zy qst qsv qc qht qhv zh2)";
    let bcast = format!("(r17_wkcCastT qD (KExpr.let_ qtt qv zy) qe2 qc (@Eq.symm KExpr qe2 (KExpr.let_ qtt qv zy) zeq) {bnd})");
    let bbx1 = format!("(xval qD qe2 qc {bcast} zr)");
    let bbx2 = format!("(xval qD (KExpr.let_ qtt qv zy) qc {bnd} zr)");
    let bbs1 = format!("(r20_xval_cast_term qD (KExpr.let_ qtt qv zy) qe2 qc (@Eq.symm KExpr qe2 (KExpr.let_ qtt qv zy) zeq) {bnd} zr)");
    let z3 = format!("(fun (zy : KExpr) (zst2 : beta_reduces qb zy) (zeq : @Eq KExpr qe2 (KExpr.let_ qtt qv zy)) => qihb zy (@whnf_step.beta qb zy zst2) qC (fun (zh2 : WKC {ldd} zy qc) (zhv : forall (zr : VEnvD {ldd}), @Eq (VD qc) (xval {ldd} zy qc zh2 zr) (xval {ldd} qb qc qhb zr)) => qk {bcast} (fun (zr : VEnvD qD) => @Eq.trans (VD qc) {bbx1} {bbx2} {lrhs2} {bbs1} (zhv (vconsD qsv qD (xval qD qv qsv qhv zr) zr)))))");
    let m_let = format!("(fun (qD : Nat -> Sk) (qtt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qtt qst) (qhv : WKC qD qv qsv) (qhb : WKC {ldd} qb qc) {iht} {ihv} {ihb} (qe2 : KExpr) (qstep : whnf_step (KExpr.let_ qtt qv qb) qe2) (qC : Type) (qk : {klet}) => letRedex_whnf_inv qtt qv qb qe2 qC qstep {z0} {z1} {z2} {z3})");

    format!("fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) => @WKC.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h")
}

/// **`r21_xval_step`** — the ∀-form, at any derivation of the reduct.
///
/// R16 needed `PropBox` here because `val_step_sem`'s continuation is
/// quantified over `C : Type` while the conclusion is an `Eq`, which is a Prop;
/// that box is R16's and is reused verbatim. What R16 needed `r16_sval_irrel`
/// for, this rung gets from `r17_xval_irrel` — the subsingleton again.
pub(super) const TY_XVAL_STEP_NATIVE: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (e2 : KExpr) (st : whnf_step e e2) (h2 : WKC D e2 s) (r : VEnvD D), @Eq (VD s) (xval D e2 s h2 r) (xval D e s h r)";

pub(super) const VAL_XVAL_STEP_NATIVE: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (e2 : KExpr) (st : whnf_step e e2) (h2 : WKC D e2 s) (r : VEnvD D) => r16_unbox (@Eq (VD s) (xval D e2 s h2 r) (xval D e s h r)) (r21_xval_step_sem D e s h e2 st (PropBox (@Eq (VD s) (xval D e2 s h2 r) (xval D e s h r))) (fun (zh2 : WKC D e2 s) (zhv : forall (zr : VEnvD D), @Eq (VD s) (xval D e2 s zh2 zr) (xval D e s h zr)) => r16_propBox_intro (@Eq (VD s) (xval D e2 s h2 r) (xval D e s h r)) (@Eq.trans (VD s) (xval D e2 s h2 r) (xval D e2 s zh2 r) (xval D e s h r) (r17_xval_irrel D e2 s h2 zh2 r) (zhv r))))";

// ================================================================
// Group C — the drift check and the reach witness.
// ================================================================

/// **`r21_step_extends_transported`** — R18's `r18_xval_step` TYPE proved with
/// R21's native VALUE. One step, because both statements read `xval` on both
/// sides and only the binder differs.
pub(super) const TY_STEP_EXTENDS: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (e2 : KExpr) (st : whnf_step e e2) (h2 : WK D e2 s) (r : VEnvD D), @Eq (VD s) (xval D e2 s (r17_wk_wkc D e2 s h2) r) (xval D e s (r17_wk_wkc D e s h) r)";

pub(super) const VAL_STEP_EXTENDS: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (e2 : KExpr) (st : whnf_step e e2) (h2 : WK D e2 s) (r : VEnvD D) => r21_xval_step D e s (r17_wk_wkc D e s h) e2 st (r17_wk_wkc D e2 s h2) r";

/// The native step law at R17's `let_` witness, whose ζ step is a REAL
/// reduction out of a REAL `let_` — the case no embedding reaches.
pub(super) fn ty_step_reaches_let() -> String {
    let inst = "(instantiate (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))";
    format!("forall (r : VEnvD r12_betaEnv), @Eq (VD {KDTY}) (xval r12_betaEnv {inst} {KDTY} r17_wkc_step_let_witness r) (xval r12_betaEnv r17_letTerm {KDTY} r17_let_witness r)")
}

pub(super) fn val_step_reaches_let() -> String {
    let inst = "(instantiate (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))";
    let s0 = "(KExpr.sort Level.zero)";
    let v0 = "(KExpr.bvar Nat.zero)";
    format!("fun (r : VEnvD r12_betaEnv) => r21_xval_step r12_betaEnv r17_letTerm {KDTY} r17_let_witness {inst} (@whnf_step.beta r17_letTerm {inst} (beta_reduces.zeta {s0} {s0} {v0})) r17_wkc_step_let_witness r")
}

// ================================================================
// Group D — negative controls. NOT registered.
// ================================================================

/// The ∀-form with `Eq.refl` for a proof. Both sides are `WKC.rec` stuck on
/// DIFFERENT variable derivations of different terms, so the kernel must refuse.
#[cfg(test)]
pub(super) fn probe_step_refl() -> String {
    format!("def r21_step_refl_probe : {TY_XVAL_STEP_NATIVE} := fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (e2 : KExpr) (st : whnf_step e e2) (h2 : WKC D e2 s) (r : VEnvD D) => @Eq.refl (VD s) (xval D e2 s h2 r)")
}

/// The step law with its `whnf_step` premise DROPPED. It must be refused: it
/// would equate the interpretations of two arbitrary terms of one shape, which
/// is false, and it is the control that `st` is load-bearing rather than
/// decorative in the statement.
#[cfg(test)]
pub(super) fn probe_step_without_the_step() -> String {
    "def r21_step_no_premise_probe : forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (e2 : KExpr) (h2 : WKC D e2 s) (r : VEnvD D), @Eq (VD s) (xval D e2 s h2 r) (xval D e s h r) := fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (e2 : KExpr) (h2 : WKC D e2 s) (r : VEnvD D) => r17_xval_irrel D e2 s h2 h r".to_string()
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R21Item {
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
impl R21Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R21Item::Def { name, .. } | R21Item::Thm { name, .. } => name,
        }
    }

    pub(super) fn decl_source(&self) -> String {
        match self {
            R21Item::Def { src, .. } => src.clone(),
            R21Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn d(name: &str, src: String) -> R21Item {
    R21Item::Def {
        name: name.to_string(),
        src,
    }
}

fn t(name: &str, ty: String, val: String) -> R21Item {
    R21Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R21 constant, in registration order.
pub(super) fn r21_items() -> Vec<R21Item> {
    vec![
        d("r21_xvalLamT", SRC_XVAL_LAM_T.to_string()),
        d("r21_xval_lam_inv", src_xval_lam_inv()),
        t("r21_xval_step_sem", ty_xval_step_sem(), val_xval_step_sem()),
        t(
            "r21_xval_step",
            TY_XVAL_STEP_NATIVE.to_string(),
            VAL_XVAL_STEP_NATIVE.to_string(),
        ),
        t(
            "r21_step_extends_transported",
            TY_STEP_EXTENDS.to_string(),
            VAL_STEP_EXTENDS.to_string(),
        ),
        t(
            "r21_step_reaches_let",
            ty_step_reaches_let(),
            val_step_reaches_let(),
        ),
    ]
}

#[cfg(test)]
pub(super) fn r21_all_sources() -> Vec<(String, String)> {
    r21_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
