// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R17 sources, part 2 — the OPERATIONS (`wkc_lift` / `wkc_psub` / `wkc_inst`),
//! SUBJECT REDUCTION (`wkc_step`) at seven constructors, the settled
//! CONVERSION-RULE question, and the witnesses.
//!
//! Read `candmodel_construct_r17.rs` first. Part 1
//! (`candmodel_construct_r17_src.rs`) carries the system itself and the
//! R16-class metatheory; this file is everything downstream of it plus the
//! single ordered registration table.

use super::candmodel_construct_r17_src::{
    defval_none, recmeta_none, DEADCONST, HF_REFL, KDTY, ONE, S0, V0,
};

// ================================================================
// Group F — the WEAKENING and SUBSTITUTION operations, at seven
// constructors. R14's, with the two new arms.
//
// Both new arms are CHEAP and for the same reason: `lift_at` and `psubst` leave
// a `const` alone outright, and treat a `let_` exactly as they treat a `lam`
// (annotation and value at the cutoff, body one binder in). R14's recursive
// `skins` therefore keeps the `let_` binder case transport-free too.
// ================================================================

pub(super) fn src_wkc_lift_var() -> String {
    let shape_cast = "r17_wkcCastS (skins c t D) (KExpr.bvar (r14_wkpos i c)) (skins c t D (r14_wkpos i c)) (D i) (r14_skins_idx c i t D) (WKC.var (skins c t D) (r14_wkpos i c))";
    format!(
        "def r17_wkc_lift_var (c : Nat) (i : Nat) (t : Sk) (D : Nat -> Sk) : WKC (skins c t D) (lift_at (KExpr.bvar i) c {ONE}) (D i) := r17_wkcCastT (skins c t D) (KExpr.bvar (r14_wkpos i c)) (lift_at (KExpr.bvar i) c {ONE}) (D i) (Eq.symm KExpr (lift_at (KExpr.bvar i) c {ONE}) (KExpr.bvar (r14_wkpos i c)) (r14_lift_at_bvar_wkpos i c)) ({shape_cast})"
    )
}

pub(super) fn src_wkc_lift() -> String {
    let motive = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => forall (qk : Nat) (qins : Sk), WKC (skins qk qins qD) (lift_at qe qk (Nat.succ Nat.zero)) qs)";
    let m_var =
        "(fun (qD : Nat -> Sk) (qi : Nat) (qk : Nat) (qins : Sk) => r17_wkc_lift_var qk qi qins qD)";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) (qk : Nat) (qins : Sk) => WKC.sort (skins qk qins qD) qn)";
    let ih_a = "(qihA : forall (qk : Nat) (qins : Sk), WKC (skins qk qins qD) (lift_at qA qk (Nat.succ Nat.zero)) qsA)";
    let ih_pb = "(qihB : forall (qk : Nat) (qins : Sk), WKC (skins qk qins (skcons (domSk qsA) qD)) (lift_at qB qk (Nat.succ Nat.zero)) qsB)";
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC (skcons (domSk qsA) qD) qB qsB) {ih_a} {ih_pb} (qk : Nat) (qins : Sk) => WKC.pi (skins qk qins qD) (lift_at qA qk {ONE}) (lift_at qB (Nat.succ qk) {ONE}) qsA qsB (qihA qk qins) (qihB (Nat.succ qk) qins))"
    );
    let ih_lb = "(qihb : forall (qk : Nat) (qins : Sk), WKC (skins qk qins (skcons (domSk qsA) qD)) (lift_at qb qk (Nat.succ Nat.zero)) qc)";
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC (skcons (domSk qsA) qD) qb qc) {ih_a} {ih_lb} (qk : Nat) (qins : Sk) => WKC.lam (skins qk qins qD) (lift_at qA qk {ONE}) (lift_at qb (Nat.succ qk) {ONE}) qsA qc (qihA qk qins) (qihb (Nat.succ qk) qins))"
    );
    let ih_f = "(qihf : forall (qk : Nat) (qins : Sk), WKC (skins qk qins qD) (lift_at qf qk (Nat.succ Nat.zero)) (Sk.arr qd qcc))";
    let ih_ar = "(qiha : forall (qk : Nat) (qins : Sk), WKC (skins qk qins qD) (lift_at qa qk (Nat.succ Nat.zero)) qd)";
    let m_app = format!(
        "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) {ih_f} {ih_ar} (qk : Nat) (qins : Sk) => WKC.app (skins qk qins qD) (lift_at qf qk {ONE}) (lift_at qa qk {ONE}) qd qcc (qihf qk qins) (qiha qk qins))"
    );
    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) (qk : Nat) (qins : Sk) => WKC.konst (skins qk qins qD) qn qus qhd qhr)",
        defval_none("qn"),
        recmeta_none("qn")
    );
    let ih_t = "(qiht : forall (qk : Nat) (qins : Sk), WKC (skins qk qins qD) (lift_at qt qk (Nat.succ Nat.zero)) qst)";
    let ih_v = "(qihv : forall (qk : Nat) (qins : Sk), WKC (skins qk qins qD) (lift_at qv qk (Nat.succ Nat.zero)) qsv)";
    let ih_b = "(qihb : forall (qk : Nat) (qins : Sk), WKC (skins qk qins (skcons qsv qD)) (lift_at qb qk (Nat.succ Nat.zero)) qc)";
    let m_let = format!(
        "(fun (qD : Nat -> Sk) (qt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qt qst) (qhv : WKC qD qv qsv) (qhb : WKC (skcons qsv qD) qb qc) {ih_t} {ih_v} {ih_b} (qk : Nat) (qins : Sk) => WKC.let_ (skins qk qins qD) (lift_at qt qk {ONE}) (lift_at qv qk {ONE}) (lift_at qb (Nat.succ qk) {ONE}) qst qsv qc (qiht qk qins) (qihv qk qins) (qihb (Nat.succ qk) qins))"
    );
    format!(
        "def wkc_lift (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (k : Nat) (t : Sk) : WKC (skins k t D) (lift_at e k {ONE}) s := WKC.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h k t"
    )
}

pub(super) fn src_wkc_lift0() -> String {
    format!(
        "def wkc_lift0 (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (t : Sk) : WKC (skcons t D) (lift_at e Nat.zero {ONE}) s := wkc_lift D e s h Nat.zero t"
    )
}

pub(super) const SRC_WKC_UP: &str = "def wkc_up (D : Nat -> Sk) (Dp : Nat -> Sk) (sg : Nat -> KExpr) (d : Sk) (hsg : forall (qi : Nat), WKC D (sg qi) (Dp qi)) (i : Nat) : WKC (skcons d D) (up sg i) (skcons d Dp i) := Nat.rec (fun (qi : Nat) => WKC (skcons d D) (up sg qi) (skcons d Dp qi)) (WKC.var (skcons d D) Nat.zero) (fun (qn : Nat) (qih : WKC (skcons d D) (up sg qn) (skcons d Dp qn)) => wkc_lift0 D (sg qn) (Dp qn) (hsg qn) d) i";

pub(super) fn src_wkc_psub() -> String {
    let motive = "(fun (qDp : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qDp qe qs) => forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) -> WKC qD (psubst qsg qe) qs)";
    let m_var = "(fun (qDp : Nat -> Sk) (qi : Nat) (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qj : Nat), WKC qD (qsg qj) (qDp qj)) => qhsg qi)";
    let m_sort = "(fun (qDp : Nat -> Sk) (qn : Level) (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qj : Nat), WKC qD (qsg qj) (qDp qj)) => WKC.sort qD qn)";
    let ih_a = "(qihA : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) -> WKC qD (psubst qsg qA) qsA)";
    let ih_pb = "(qihB : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WKC qD (qsg qi) (skcons (domSk qsA) qDp qi)) -> WKC qD (psubst qsg qB) qsB)";
    let m_pi = format!(
        "(fun (qDp : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qDp qA qsA) (qhB : WKC (skcons (domSk qsA) qDp) qB qsB) {ih_a} {ih_pb} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) => WKC.pi qD (psubst qsg qA) (psubst (up qsg) qB) qsA qsB (qihA qsg qD qhsg) (qihB (up qsg) (skcons (domSk qsA) qD) (wkc_up qD qDp qsg (domSk qsA) qhsg)))"
    );
    let ih_lb = "(qihb : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WKC qD (qsg qi) (skcons (domSk qsA) qDp qi)) -> WKC qD (psubst qsg qb) qc)";
    let m_lam = format!(
        "(fun (qDp : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qDp qA qsA) (qhb : WKC (skcons (domSk qsA) qDp) qb qc) {ih_a} {ih_lb} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) => WKC.lam qD (psubst qsg qA) (psubst (up qsg) qb) qsA qc (qihA qsg qD qhsg) (qihb (up qsg) (skcons (domSk qsA) qD) (wkc_up qD qDp qsg (domSk qsA) qhsg)))"
    );
    let ih_f = "(qihf : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) -> WKC qD (psubst qsg qf) (Sk.arr qd qcc))";
    let ih_ar = "(qiha : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) -> WKC qD (psubst qsg qa) qd)";
    let m_app = format!(
        "(fun (qDp : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qDp qf (Sk.arr qd qcc)) (qha : WKC qDp qa qd) {ih_f} {ih_ar} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) => WKC.app qD (psubst qsg qf) (psubst qsg qa) qd qcc (qihf qsg qD qhsg) (qiha qsg qD qhsg))"
    );
    let m_konst = format!(
        "(fun (qDp : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) => WKC.konst qD qn qus qhd qhr)",
        defval_none("qn"),
        recmeta_none("qn")
    );
    let ih_t = "(qiht : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) -> WKC qD (psubst qsg qt) qst)";
    let ih_v = "(qihv : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) -> WKC qD (psubst qsg qv) qsv)";
    let ih_b = "(qihb : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WKC qD (qsg qi) (skcons qsv qDp qi)) -> WKC qD (psubst qsg qb) qc)";
    let m_let = format!(
        "(fun (qDp : Nat -> Sk) (qt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qDp qt qst) (qhv : WKC qDp qv qsv) (qhb : WKC (skcons qsv qDp) qb qc) {ih_t} {ih_v} {ih_b} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qi : Nat), WKC qD (qsg qi) (qDp qi)) => WKC.let_ qD (psubst qsg qt) (psubst qsg qv) (psubst (up qsg) qb) qst qsv qc (qiht qsg qD qhsg) (qihv qsg qD qhsg) (qihb (up qsg) (skcons qsv qD) (wkc_up qD qDp qsg qsv qhsg)))"
    );
    format!(
        "def wkc_psub (Dp : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC Dp e s) (sg : Nat -> KExpr) (D : Nat -> Sk) (hsg : forall (qi : Nat), WKC D (sg qi) (Dp qi)) : WKC D (psubst sg e) s := WKC.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} Dp e s h sg D hsg"
    )
}

pub(super) const SRC_SCONS_TYPED: &str = "def r17_scons_typed (D : Nat -> Sk) (a : KExpr) (d : Sk) (ha : WKC D a d) (i : Nat) : WKC D (scons a idsubst i) (skcons d D i) := Nat.rec (fun (qi : Nat) => WKC D (scons a idsubst qi) (skcons d D qi)) ha (fun (qn : Nat) (qih : WKC D (scons a idsubst qn) (skcons d D qn)) => WKC.var D qn) i";

pub(super) const SRC_WKC_INST: &str = "def wkc_inst (D : Nat -> Sk) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hb : WKC (skcons d D) b c) (ha : WKC D a d) : WKC D (instantiate b a) c := r17_wkcCastT D (psubst (scons a idsubst) b) (instantiate b a) c (Eq.symm KExpr (instantiate b a) (psubst (scons a idsubst) b) (instantiate_eq_psubst b a)) (wkc_psub (skcons d D) b c hb (scons a idsubst) D (r17_scons_typed D a d ha))";

// ================================================================
// Group G — SUBJECT REDUCTION at seven constructors.
//
// THE KEY STRUCTURAL FACT, and why the extension does NOT cost a rebuild of
// R15's step inversion: `WKC.konst` concludes at `Sk.ty` and at no other shape,
// so a term shape-typed at an ARROW is still head-free. R15's
// `r15_headFree_wk` ("WK never types a const-headed spine") becomes
// `r17_headFree_wkc_arr` ("WKC never types a const-headed spine AT AN ARROW
// SHAPE"), and `WKC.app`'s function premise is exactly at an arrow shape. R15's
// `r15_whnf_stepT_inv` is therefore consumed VERBATIM in five of the seven
// arms; R10's `HeadInert` machinery is not needed here at all.
// ================================================================

/// **THE STRUCTURAL FACT.** FIVE arms are one token (`Eq.refl` through
/// `HeadFree`'s `def`), the `app` arm is `headFree_app` at its own IH, and the
/// `konst` arm dies by COMPUTATION: its shape is `Sk.ty`, the hypothesis says
/// that is an `Sk.arr`, and `r17_notArrT` reads that off.
pub(super) const TY_HEADFREE_WKC_ARR: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk), WKC D e s -> forall (d : Sk) (c : Sk), Eq Sk s (Sk.arr d c) -> HeadFree e";

pub(super) fn val_headfree_wkc_arr() -> String {
    let mot = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => forall (qd : Sk) (qc : Sk), Eq Sk qs (Sk.arr qd qc) -> HeadFree qe)";
    let m_var = format!("(fun (qD : Nat -> Sk) (qi : Nat) (qd : Sk) (qc : Sk) (qeq : Eq Sk (qD qi) (Sk.arr qd qc)) => {HF_REFL})");
    let m_sort = format!("(fun (qD : Nat -> Sk) (qn : Level) (qd : Sk) (qc : Sk) (qeq : Eq Sk (Sk.kd Sk.ty) (Sk.arr qd qc)) => {HF_REFL})");
    let ih = |sub: &str, sh: &str| {
        format!("(forall (qd : Sk) (qc : Sk), Eq Sk {sh} (Sk.arr qd qc) -> HeadFree {sub})")
    };
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC (skcons (domSk qsA) qD) qB qsB) (qihA : {}) (qihB : {}) (qd : Sk) (qc : Sk) (qeq : Eq Sk (piShape qsA qsB) (Sk.arr qd qc)) => {HF_REFL})",
        ih("qA", "qsA"),
        ih("qB", "qsB")
    );
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qcl : Sk) (qhA : WKC qD qA qsA) (qhb : WKC (skcons (domSk qsA) qD) qb qcl) (qihA : {}) (qihb : {}) (qd : Sk) (qc : Sk) (qeq : Eq Sk (Sk.arr (domSk qsA) qcl) (Sk.arr qd qc)) => {HF_REFL})",
        ih("qA", "qsA"),
        ih("qb", "qcl")
    );
    let m_app = format!(
        "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd0 : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd0 qcc)) (qha : WKC qD qa qd0) (qihf : {}) (qiha : {}) (qd : Sk) (qc : Sk) (qeq : Eq Sk qcc (Sk.arr qd qc)) => headFree_app qf qa (qihf qd0 qcc (Eq.refl Sk (Sk.arr qd0 qcc))))",
        ih("qf", "(Sk.arr qd0 qcc)"),
        ih("qa", "qd0")
    );
    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) (qd : Sk) (qc : Sk) (qeq : Eq Sk Sk.ty (Sk.arr qd qc)) => Empty.rec (fun (qz : Empty) => HeadFree (KExpr.const qn qus)) (Eq.substType Sk r17_notArrT Sk.ty (Sk.arr qd qc) qeq ConstFreeUnit.triv))",
        defval_none("qn"),
        recmeta_none("qn")
    );
    let m_let = format!(
        "(fun (qD : Nat -> Sk) (qt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qcl : Sk) (qht : WKC qD qt qst) (qhv : WKC qD qv qsv) (qhb : WKC (skcons qsv qD) qb qcl) (qiht : {}) (qihv : {}) (qihb : {}) (qd : Sk) (qc : Sk) (qeq : Eq Sk qcl (Sk.arr qd qc)) => {HF_REFL})",
        ih("qt", "qst"),
        ih("qv", "qsv"),
        ih("qb", "qcl")
    );
    format!(
        "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) => WKC.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h"
    )
}

/// R10's interface, supplied for the WHOLE extended system: every shape-typed
/// term is head-INERT. This is where the `konst` rule's second premise
/// (`recmeta_for = none`) is load-bearing — subject reduction below does not
/// need it, `inertConst_headInert` does.
pub(super) const TY_HEADINERT_WKC: &str =
    "forall (D : Nat -> Sk) (e : KExpr) (s : Sk), WKC D e s -> HeadInert e";

pub(super) fn val_headinert_wkc() -> String {
    let mot = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => HeadInert qe)";
    let m_var =
        format!("(fun (qD : Nat -> Sk) (qi : Nat) => HeadInert.free (KExpr.bvar qi) {HF_REFL})");
    let m_sort =
        format!("(fun (qD : Nat -> Sk) (qn : Level) => HeadInert.free (KExpr.sort qn) {HF_REFL})");
    let m_pi = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC (skcons (domSk qsA) qD) qB qsB) (qihA : HeadInert qA) (qihB : HeadInert qB) => HeadInert.free (KExpr.pi qA qB) {HF_REFL})");
    let m_lam = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC (skcons (domSk qsA) qD) qb qc) (qihA : HeadInert qA) (qihb : HeadInert qb) => HeadInert.free (KExpr.lam qA qb) {HF_REFL})");
    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) (qihf : HeadInert qf) (qiha : HeadInert qa) => headInert_app qf qa qihf)";
    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) => inertConst_headInert qn qus qhd qhr)",
        defval_none("qn"),
        recmeta_none("qn")
    );
    let m_let = format!("(fun (qD : Nat -> Sk) (qt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qt qst) (qhv : WKC qD qv qsv) (qhb : WKC (skcons qsv qD) qb qc) (qiht : HeadInert qt) (qihv : HeadInert qv) (qihb : HeadInert qb) => HeadInert.free (KExpr.let_ qt qv qb) {HF_REFL})");
    format!(
        "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) => WKC.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h"
    )
}

/// **AN INERT CONSTANT ADMITS NO `whnf_step` AT ALL.** The β leg is R2's
/// `r2_const_no_beta_reduces` (a bare const admits no `beta_reduces` for ANY
/// name — an empty spine has no major premise, so even the ι arm dies
/// unconditionally); the δ leg is R10's own δ arm, at the head-name equation
/// that a bare const satisfies by `Eq.refl`. Only `defval_for = none` is
/// consumed.
pub(super) fn src_const_no_step() -> String {
    let cn = "(KExpr.const n us)";
    let denv = "(red_def the_red_env)";
    let none_eq = format!("(Eq.symm (OptionType KExpr) (delta_reduct {denv} {cn}) (OptionType.none KExpr) (delta_reduct_eq_none_of_defval_none {denv} {cn} n (Eq.refl (OptionType Name) (OptionType.some Name n)) hd))");
    let clash = format!("(Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct {denv} {cn}) (OptionType.some KExpr g2) {none_eq} zds)");
    format!(
        "def r17_const_no_step (n : Name) (us : ListType Level) (g2 : KExpr) (C : Type) (hd : {}) (hs : whnf_step {cn} g2) : C := constRedex_whnf_inv n us g2 C hs (fun (zds : delta_step {denv} {cn} g2) => option_none_ne_some_type KExpr g2 C {clash})",
        defval_none("n")
    )
}

/// R15's `r15_wkLamT` at `WKC`: a `KExpr.rec` on the term nested with a
/// `Sk.rec` on the shape, every pair but (`lam`, `arr`) `ConstFreeUnit`. Two
/// more dead arms than R15's (nine heads, not five), all still one token.
pub(super) const SRC_WKC_LAM_T: &str = "def r17_wkcLamT (D : Nat -> Sk) (C : Type) (e : KExpr) (s : Sk) : Type := KExpr.rec (fun (qe : KExpr) => Sk -> Type) (fun (qn : Level) (qs : Sk) => ConstFreeUnit) (fun (qi : Nat) (qs : Sk) => ConstFreeUnit) (fun (qf : KExpr) (qa : KExpr) (qihf : Sk -> Type) (qiha : Sk -> Type) (qs : Sk) => ConstFreeUnit) (fun (qA : KExpr) (qb : KExpr) (qihA : Sk -> Type) (qihb : Sk -> Type) => Sk.rec (fun (qz : Sk) => Type) ConstFreeUnit (fun (qs1 : Sk) (qih : Type) => ConstFreeUnit) (fun (qd : Sk) (qc : Sk) (qihd : Type) (qihc : Type) => (WKC (skcons qd D) qb qc -> C) -> C)) (fun (qA : KExpr) (qB : KExpr) (qihA : Sk -> Type) (qihB : Sk -> Type) (qs : Sk) => ConstFreeUnit) (fun (qn : Name) (qus : ListType Level) (qs : Sk) => ConstFreeUnit) (fun (qt : KExpr) (qv : KExpr) (qb : KExpr) (qiht : Sk -> Type) (qihv : Sk -> Type) (qihb : Sk -> Type) (qs : Sk) => ConstFreeUnit) (fun (qsn : Name) (qpi : Nat) (qsub : KExpr) (qihs : Sk -> Type) (qs : Sk) => ConstFreeUnit) (fun (qv : Nat) (qs : Sk) => ConstFreeUnit) e s";

pub(super) fn src_wkc_lam_inv() -> String {
    let motive = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => r17_wkcLamT qD C qe qs)";
    let m_var = "(fun (qD : Nat -> Sk) (qi : Nat) => ConstFreeUnit.triv)";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) => ConstFreeUnit.triv)";
    let m_pi = "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC (skcons (domSk qsA) qD) qB qsB) (qihA : r17_wkcLamT qD C qA qsA) (qihB : r17_wkcLamT (skcons (domSk qsA) qD) C qB qsB) => ConstFreeUnit.triv)";
    let m_lam = "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC (skcons (domSk qsA) qD) qb qc) (qihA : r17_wkcLamT qD C qA qsA) (qihb : r17_wkcLamT (skcons (domSk qsA) qD) C qb qc) (zk : WKC (skcons (domSk qsA) qD) qb qc -> C) => zk qhb)";
    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) (qihf : r17_wkcLamT qD C qf (Sk.arr qd qcc)) (qiha : r17_wkcLamT qD C qa qd) => ConstFreeUnit.triv)";
    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) => ConstFreeUnit.triv)",
        defval_none("qn"),
        recmeta_none("qn")
    );
    let m_let = "(fun (qD : Nat -> Sk) (qt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qt qst) (qhv : WKC qD qv qsv) (qhb : WKC (skcons qsv qD) qb qc) (qiht : r17_wkcLamT qD C qt qst) (qihv : r17_wkcLamT qD C qv qsv) (qihb : r17_wkcLamT (skcons qsv qD) C qb qc) => ConstFreeUnit.triv)";
    format!(
        "def r17_wkc_lam_inv (D : Nat -> Sk) (C : Type) (e : KExpr) (s : Sk) (h : WKC D e s) : r17_wkcLamT D C e s := WKC.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h"
    )
}

/// **`wkc_step`** — subject reduction for shapes at seven constructors, total
/// and unconditional, a `def` so a later rung can reduce through it.
///
/// Five arms reuse R15's step inversion verbatim; the two new ones are the
/// point:
///
/// * `konst` — no step exists (`r17_const_no_step`), so the arm is a refutation.
/// * `let_` — R1's `letRedex_whnf_inv` gives all four cases. **ζ lands on
///   `wkc_inst` exactly as head-β does**, because the `let_` rule's binder slot
///   carries the shape of the VALUE; the three congruences re-type their
///   stepped component at the SAME shape through the induction hypothesis, and
///   the `let_val` one needs no re-indexing of the body for the same reason.
#[allow(clippy::too_many_lines)]
pub(super) fn src_wkc_step() -> String {
    let mot = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => forall (qe2 : KExpr), whnf_step qe qe2 -> WKC qD qe2 qs)";
    let m_var = format!(
        "(fun (qD : Nat -> Sk) (qi : Nat) (qe2 : KExpr) (qst : whnf_step (KExpr.bvar qi) qe2) => r15_whnf_stepT_inv (WKC qD qe2 (qD qi)) (KExpr.bvar qi) qe2 {HF_REFL} qst)"
    );
    let m_sort = format!(
        "(fun (qD : Nat -> Sk) (qn : Level) (qe2 : KExpr) (qst : whnf_step (KExpr.sort qn) qe2) => r15_whnf_stepT_inv (WKC qD qe2 (Sk.kd Sk.ty)) (KExpr.sort qn) qe2 {HF_REFL} qst)"
    );

    let ihp_a = "(qihA : forall (qz : KExpr), whnf_step qA qz -> WKC qD qz qsA)";
    let ihp_b =
        "(qihB : forall (qz : KExpr), whnf_step qB qz -> WKC (skcons (domSk qsA) qD) qz qsB)";
    let p1 = "(fun (zy : KExpr) (zst : beta_reduces qA zy) (zeq : Eq KExpr qe2 (KExpr.pi zy qB)) => r17_wkcCastT qD (KExpr.pi zy qB) qe2 (piShape qsA qsB) (Eq.symm KExpr qe2 (KExpr.pi zy qB) zeq) (WKC.pi qD zy qB qsA qsB (qihA zy (whnf_step.beta qA zy zst)) qhB))";
    let p2 = "(fun (zy : KExpr) (zst : beta_reduces qB zy) (zeq : Eq KExpr qe2 (KExpr.pi qA zy)) => r17_wkcCastT qD (KExpr.pi qA zy) qe2 (piShape qsA qsB) (Eq.symm KExpr qe2 (KExpr.pi qA zy) zeq) (WKC.pi qD qA zy qsA qsB qhA (qihB zy (whnf_step.beta qB zy zst))))";
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC (skcons (domSk qsA) qD) qB qsB) {ihp_a} {ihp_b} (qe2 : KExpr) (qst : whnf_step (KExpr.pi qA qB) qe2) => r15_whnf_stepT_inv (WKC qD qe2 (piShape qsA qsB)) (KExpr.pi qA qB) qe2 {HF_REFL} qst {p1} {p2})"
    );

    let ihl_a = "(qihA : forall (qz : KExpr), whnf_step qA qz -> WKC qD qz qsA)";
    let ihl_b =
        "(qihb : forall (qz : KExpr), whnf_step qb qz -> WKC (skcons (domSk qsA) qD) qz qc)";
    let l1 = "(fun (zy : KExpr) (zst : beta_reduces qA zy) (zeq : Eq KExpr qe2 (KExpr.lam zy qb)) => r17_wkcCastT qD (KExpr.lam zy qb) qe2 (Sk.arr (domSk qsA) qc) (Eq.symm KExpr qe2 (KExpr.lam zy qb) zeq) (WKC.lam qD zy qb qsA qc (qihA zy (whnf_step.beta qA zy zst)) qhb))";
    let l2 = "(fun (zy : KExpr) (zst : beta_reduces qb zy) (zeq : Eq KExpr qe2 (KExpr.lam qA zy)) => r17_wkcCastT qD (KExpr.lam qA zy) qe2 (Sk.arr (domSk qsA) qc) (Eq.symm KExpr qe2 (KExpr.lam qA zy) zeq) (WKC.lam qD qA zy qsA qc qhA (qihb zy (whnf_step.beta qb zy zst))))";
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC (skcons (domSk qsA) qD) qb qc) {ihl_a} {ihl_b} (qe2 : KExpr) (qst : whnf_step (KExpr.lam qA qb) qe2) => r15_whnf_stepT_inv (WKC qD qe2 (Sk.arr (domSk qsA) qc)) (KExpr.lam qA qb) qe2 {HF_REFL} qst {l1} {l2})"
    );

    let iha_f = "(qihf : forall (qz : KExpr), whnf_step qf qz -> WKC qD qz (Sk.arr qd qcc))";
    let iha_a = "(qiha : forall (qz : KExpr), whnf_step qa qz -> WKC qD qz qd)";
    let hf = "(headFree_app qf qa (r17_headFree_wkc_arr qD qf (Sk.arr qd qcc) qhf qd qcc (Eq.refl Sk (Sk.arr qd qcc))))";
    let a1 = "(fun (zA : KExpr) (zb : KExpr) (zlam : Eq KExpr qf (KExpr.lam zA zb)) (zcon : Eq KExpr qe2 (instantiate zb qa)) => r17_wkc_lam_inv qD (WKC qD qe2 qcc) (KExpr.lam zA zb) (Sk.arr qd qcc) (r17_wkcCastT qD qf (KExpr.lam zA zb) (Sk.arr qd qcc) zlam qhf) (fun (zhb : WKC (skcons qd qD) zb qcc) => r17_wkcCastT qD (instantiate zb qa) qe2 qcc (Eq.symm KExpr qe2 (instantiate zb qa) zcon) (wkc_inst qD zb qa qd qcc zhb qha)))";
    let a2 = "(fun (zy : KExpr) (zst : beta_reduces qf zy) (zeq : Eq KExpr qe2 (KExpr.app zy qa)) => r17_wkcCastT qD (KExpr.app zy qa) qe2 qcc (Eq.symm KExpr qe2 (KExpr.app zy qa) zeq) (WKC.app qD zy qa qd qcc (qihf zy (whnf_step.beta qf zy zst)) qha))";
    let a3 = "(fun (zy : KExpr) (zst : beta_reduces qa zy) (zeq : Eq KExpr qe2 (KExpr.app qf zy)) => r17_wkcCastT qD (KExpr.app qf zy) qe2 qcc (Eq.symm KExpr qe2 (KExpr.app qf zy) zeq) (WKC.app qD qf zy qd qcc qhf (qiha zy (whnf_step.beta qa zy zst))))";
    let m_app = format!(
        "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) {iha_f} {iha_a} (qe2 : KExpr) (qst : whnf_step (KExpr.app qf qa) qe2) => r15_whnf_stepT_inv (WKC qD qe2 qcc) (KExpr.app qf qa) qe2 {hf} qst {a1} {a2} {a3})"
    );

    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) (qe2 : KExpr) (qst : whnf_step (KExpr.const qn qus) qe2) => r17_const_no_step qn qus qe2 (WKC qD qe2 Sk.ty) qhd qst)",
        defval_none("qn"),
        recmeta_none("qn")
    );

    let iht = "(qiht : forall (qz : KExpr), whnf_step qt qz -> WKC qD qz qst)";
    let ihv = "(qihv : forall (qz : KExpr), whnf_step qv qz -> WKC qD qz qsv)";
    let ihb = "(qihb : forall (qz : KExpr), whnf_step qb qz -> WKC (skcons qsv qD) qz qc)";
    let z0 = "(fun (zeq : Eq KExpr qe2 (instantiate qb qv)) => r17_wkcCastT qD (instantiate qb qv) qe2 qc (Eq.symm KExpr qe2 (instantiate qb qv) zeq) (wkc_inst qD qb qv qsv qc qhb qhv))";
    let z1 = "(fun (zy : KExpr) (zst : beta_reduces qt zy) (zeq : Eq KExpr qe2 (KExpr.let_ zy qv qb)) => r17_wkcCastT qD (KExpr.let_ zy qv qb) qe2 qc (Eq.symm KExpr qe2 (KExpr.let_ zy qv qb) zeq) (WKC.let_ qD zy qv qb qst qsv qc (qiht zy (whnf_step.beta qt zy zst)) qhv qhb))";
    let z2 = "(fun (zy : KExpr) (zst : beta_reduces qv zy) (zeq : Eq KExpr qe2 (KExpr.let_ qt zy qb)) => r17_wkcCastT qD (KExpr.let_ qt zy qb) qe2 qc (Eq.symm KExpr qe2 (KExpr.let_ qt zy qb) zeq) (WKC.let_ qD qt zy qb qst qsv qc qht (qihv zy (whnf_step.beta qv zy zst)) qhb))";
    let z3 = "(fun (zy : KExpr) (zst : beta_reduces qb zy) (zeq : Eq KExpr qe2 (KExpr.let_ qt qv zy)) => r17_wkcCastT qD (KExpr.let_ qt qv zy) qe2 qc (Eq.symm KExpr qe2 (KExpr.let_ qt qv zy) zeq) (WKC.let_ qD qt qv zy qst qsv qc qht qhv (qihb zy (whnf_step.beta qb zy zst))))";
    let m_let = format!(
        "(fun (qD : Nat -> Sk) (qt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qt qst) (qhv : WKC qD qv qsv) (qhb : WKC (skcons qsv qD) qb qc) {iht} {ihv} {ihb} (qe2 : KExpr) (qst2 : whnf_step (KExpr.let_ qt qv qb) qe2) => letRedex_whnf_inv qt qv qb qe2 (WKC qD qe2 qc) qst2 {z0} {z1} {z2} {z3})"
    );

    format!(
        "def wkc_step (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (e2 : KExpr) (st : whnf_step e e2) : WKC D e2 s := WKC.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h e2 st"
    )
}

// ================================================================
// Group H — THE CONVERSION RULE, SETTLED.
//
// R16's subsingleton holds "precisely because WK has no conversion rule", and
// `TypingCtx` has one. This group answers the question with two kernel-checked
// constants instead of prose, on the SMALLEST system that exhibits the
// phenomenon: two leaf rules and a conversion rule at the finest possible
// shape relation, propositional EQUALITY of shapes.
//
// VERDICT: shape assignment SURVIVES; derivation uniqueness does NOT, and it
// fails at the finest relation, so no weakening of the relation rescues it.
// That is why this rung does not build a conversion rule into `WKC`.
// ================================================================

pub(super) const SRC_WKV: &str = "inductive WKV : (Nat -> Sk) -> KExpr -> Sk -> Type
| var : forall (D : Nat -> Sk) (i : Nat), WKV D (KExpr.bvar i) (D i)
| sort : forall (D : Nat -> Sk) (n : Level), WKV D (KExpr.sort n) (Sk.kd Sk.ty)
| conv : forall (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (s2 : Sk), WKV D e s1 -> Eq Sk s1 s2 -> WKV D e s2";

/// **`WKV.rec` IS PARAMETER-PROMOTED, and `WKC.rec` is not.** `WKV.conv`'s
/// recursive premise is at the SAME shape environment as its conclusion, so `D`
/// is fixed across every constructor and `fixedIndicesToParams` promotes it:
/// `WKV.rec` takes `D` FIRST, before the motive, and the motive has THREE
/// binders, not four. `WKC` escapes this only because `WKC.pi` / `WKC.lam` /
/// `WKC.let_` all recurse at `skcons ... D`. Measured on R17's first cycle
/// (`expected (n : Nat) -> motive (KExpr.bvar n) (D n) (WKV.var D n)`), and
/// pinned by `test_candmodel_r17_wkv_recursor_is_parameter_promoted`.
pub(super) const TY_WKV_SHAPE_CORRECT: &str =
    "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKV D e s), Eq Sk s (r17_shapeOf D e)";
pub(super) const VAL_WKV_SHAPE_CORRECT: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKV D e s) => WKV.rec D (fun (qe : KExpr) (qs : Sk) (qh : WKV D qe qs) => Eq Sk qs (r17_shapeOf D qe)) (fun (qi : Nat) => Eq.refl Sk (D qi)) (fun (qn : Level) => Eq.refl Sk (Sk.kd Sk.ty)) (fun (qe : KExpr) (qs1 : Sk) (qs2 : Sk) (qh : WKV D qe qs1) (qp : Eq Sk qs1 qs2) (qih : Eq Sk qs1 (r17_shapeOf D qe)) => Eq.trans Sk qs2 qs1 (r17_shapeOf D qe) (Eq.symm Sk qs1 qs2 qp) qih) e s h";

/// **SHAPE ASSIGNMENT SURVIVES A CONVERSION RULE.** The `conv` arm is one
/// `Eq.trans`: the rule can only move a shape to one it is already EQUAL to, so
/// the computed shape still pins it. The answer the task asked for, proved.
pub(super) const TY_CONV_SHAPE_UNIQUE: &str = "forall (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (h1 : WKV D e s1) (s2 : Sk) (h2 : WKV D e s2), Eq Sk s1 s2";
pub(super) const VAL_CONV_SHAPE_UNIQUE: &str = "fun (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (h1 : WKV D e s1) (s2 : Sk) (h2 : WKV D e s2) => Eq.trans Sk s1 (r17_shapeOf D e) s2 (r17_wkv_shape_correct D e s1 h1) (Eq.symm Sk s2 (r17_shapeOf D e) (r17_wkv_shape_correct D e s2 h2))";

/// The constructor tag of a `WKV` derivation — the only thing needed to tell
/// two derivations apart, and a REDUCIBLE `def` so the discrimination computes.
pub(super) const SRC_WKV_TAG: &str = "def r17_wkv_tag (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKV D e s) : Nat := WKV.rec D (fun (qe : KExpr) (qs : Sk) (qh : WKV D qe qs) => Nat) (fun (qi : Nat) => Nat.zero) (fun (qn : Level) => Nat.succ Nat.zero) (fun (qe : KExpr) (qs1 : Sk) (qs2 : Sk) (qh : WKV D qe qs1) (qp : Eq Sk qs1 qs2) (qih : Nat) => Nat.succ (Nat.succ Nat.zero)) e s h";

/// `ConstFreeUnit` at zero, `Empty` at every successor. The `Nat` discriminator,
/// computed — R16's discipline, one type down.
pub(super) const SRC_ZERO_T: &str = "def r17_zeroT (n : Nat) : Type := Nat.rec (fun (qn : Nat) => Type) ConstFreeUnit (fun (qn : Nat) (qih : Type) => Empty) n";

/// The SECOND derivation of a judgment that already has one: the identity
/// conversion applied to `WKV.var`. It proves nothing new and it is not equal to
/// what it was built from.
pub(super) const SRC_CONV_DERIV: &str = "def r17_convDeriv (D : Nat -> Sk) (i : Nat) : WKV D (KExpr.bvar i) (D i) := WKV.conv D (KExpr.bvar i) (D i) (D i) (WKV.var D i) (Eq.refl Sk (D i))";

/// **A CONVERSION RULE BREAKS THE SUBSINGLETON — PROVED, not conjectured.**
/// `WKV.var D i` and `r17_convDeriv D i` derive the SAME judgment and are
/// provably DISTINCT, so R16's `r16_wk_deriv_unique` has no counterpart in any
/// system with a conversion rule. Note where the refutation lands: the relation
/// here is `Eq Sk`, the FINEST possible, so this is not an artefact of a coarse
/// conversion — no weakening of the relation rescues uniqueness.
pub(super) const TY_CONV_BREAKS_SUBSINGLETON: &str = "forall (D : Nat -> Sk) (i : Nat), Eq (WKV D (KExpr.bvar i) (D i)) (WKV.var D i) (r17_convDeriv D i) -> Empty";
pub(super) const VAL_CONV_BREAKS_SUBSINGLETON: &str = "fun (D : Nat -> Sk) (i : Nat) (h : Eq (WKV D (KExpr.bvar i) (D i)) (WKV.var D i) (r17_convDeriv D i)) => Eq.substType Nat r17_zeroT (r17_wkv_tag D (KExpr.bvar i) (D i) (WKV.var D i)) (r17_wkv_tag D (KExpr.bvar i) (D i) (r17_convDeriv D i)) (Eq.cong (WKV D (KExpr.bvar i) (D i)) Nat (fun (zx : WKV D (KExpr.bvar i) (D i)) => r17_wkv_tag D (KExpr.bvar i) (D i) zx) (WKV.var D i) (r17_convDeriv D i) h) ConstFreeUnit.triv";

/// The two halves in ONE kernel-checked constant, the ladder's contrast idiom:
/// under a conversion rule the SHAPE is still unique and the DERIVATION is not.
/// `PropBox` is the non-cumulativity bridge — the first half is a `forall` into
/// `Eq`, hence a Prop, and `AndType` takes `Type`s.
pub(super) const TY_CONV_VERDICT: &str = "AndType (PropBox (forall (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (h1 : WKV D e s1) (s2 : Sk) (h2 : WKV D e s2), Eq Sk s1 s2)) (forall (D : Nat -> Sk) (i : Nat), Eq (WKV D (KExpr.bvar i) (D i)) (WKV.var D i) (r17_convDeriv D i) -> Empty)";
pub(super) const VAL_CONV_VERDICT: &str = "AndType.intro (PropBox (forall (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (h1 : WKV D e s1) (s2 : Sk) (h2 : WKV D e s2), Eq Sk s1 s2)) (forall (D : Nat -> Sk) (i : Nat), Eq (WKV D (KExpr.bvar i) (D i)) (WKV.var D i) (r17_convDeriv D i) -> Empty) (r16_propBox_intro (forall (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (h1 : WKV D e s1) (s2 : Sk) (h2 : WKV D e s2), Eq Sk s1 s2) r17_conv_shape_unique) r17_conv_breaks_subsingleton";

// ================================================================
// Group I — WITNESSES, at REAL reflected constants and REAL terms.
// ================================================================

/// The `konst` rule at R9/R10's REAL reflected dead constant: both inertness
/// premises hold by `Eq.refl` over the live `the_red_env`. R9's
/// `synTyC_konst_dead_witness` and R11's `r11_interp_const_pi_witness` are the
/// precedent; this is the same constant, now shape-typed.
pub(super) fn src_konst_witness() -> String {
    format!("def r17_konst_witness : WKC r12_piEnv {DEADCONST} Sk.ty := WKC.konst r12_piEnv fixture_def_env_name (ListType.nil Level) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType RecMeta) (OptionType.none RecMeta))")
}

/// That constant is `whnf_acc` — through `r17_const_no_step`, so the `konst`
/// clause's TOP-candidate interpretation actually CONTAINS its own subject.
pub(super) fn src_dead_const_acc() -> String {
    format!("def r17_deadConst_acc : whnf_acc {DEADCONST} := whnf_acc.intro {DEADCONST} (fun (qe2 : KExpr) (qhs : whnf_step {DEADCONST} qe2) => r17_const_no_step fixture_def_env_name (ListType.nil Level) qe2 (whnf_acc qe2) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) qhs)")
}

/// NON-DEGENERACY of the `konst` interpretation clause: the constant is a MEMBER
/// of the candidate its own derivation denotes.
pub(super) fn ty_konst_mem_witness() -> String {
    format!("vcarD Sk.ty (xval r12_piEnv {DEADCONST} Sk.ty r17_konst_witness (r12_junkEnv r12_piEnv)) {DEADCONST}")
}
pub(super) const VAL_KONST_MEM_WITNESS: &str = "r17_deadConst_acc";

/// R15's own `let` probe, made a THEOREM. `probe_wk_step_at_let` records that
/// `WK` cannot even STATE `wk_step` at `let_ (sort 0) (sort 0) (bvar 0)`; `WKC`
/// types it, at the shape `r17_shapeOf` computes.
pub(super) fn src_let_term() -> String {
    format!("def r17_letTerm : KExpr := KExpr.let_ {S0} {S0} {V0}")
}

pub(super) fn src_let_witness() -> String {
    format!("def r17_let_witness : WKC r12_betaEnv r17_letTerm {KDTY} := WKC.let_ r12_betaEnv {S0} {S0} {V0} {KDTY} {KDTY} {KDTY} (WKC.sort r12_betaEnv Level.zero) (WKC.sort r12_betaEnv Level.zero) (WKC.var (skcons {KDTY} r12_betaEnv) Nat.zero)")
}

/// **SEMANTIC ζ IS DEFINITIONAL.** The interpretation of a shape-typed `let_`
/// IS the interpretation of its body at the valuation extended by the value's,
/// at EVERY shape environment, term, shape, derivation and valuation — the
/// exact analogue of R12's `r12_sval_beta`, and the reason R1's refutation of
/// the generic per-set ζ engine does NOT transfer: R1 is about candidate SETS
/// closing under expansion, this is an INTERPRETATION reading a valuation.
pub(super) const TY_XVAL_ZETA: &str = "forall (D : Nat -> Sk) (t : KExpr) (v : KExpr) (b : KExpr) (st : Sk) (sv : Sk) (c : Sk) (ht : WKC D t st) (hv : WKC D v sv) (hb : WKC (skcons sv D) b c) (r : VEnvD D), Eq (VD c) (xval D (KExpr.let_ t v b) c (WKC.let_ D t v b st sv c ht hv hb) r) (xval (skcons sv D) b c hb (vconsD sv D (xval D v sv hv r) r))";
pub(super) const VAL_XVAL_ZETA: &str = "fun (D : Nat -> Sk) (t : KExpr) (v : KExpr) (b : KExpr) (st : Sk) (sv : Sk) (c : Sk) (ht : WKC D t st) (hv : WKC D v sv) (hb : WKC (skcons sv D) b c) (r : VEnvD D) => Eq.refl (VD c) (xval (skcons sv D) b c hb (vconsD sv D (xval D v sv hv r) r))";

/// The POSITIVE half of the `let_` clause's non-degeneracy, at a term whose
/// value is a VARIABLE: the interpretation of `let x : Sort 0 := bvar 0; x` IS
/// the valuation's own slot 0, at every valuation. Paired with
/// `probe_zeta_junk`, which shows the junk-extended reading is a DIFFERENT
/// value — so the `let_` clause genuinely reads what the value denotes.
pub(super) fn ty_zeta_reads_value() -> String {
    let kk = "(Sk.kd (Sk.kd Sk.ty))";
    let env2 = format!("(skcons {kk} r12_betaEnv)");
    let hb = format!("(WKC.var {env2} Nat.zero)");
    let hlet = format!("(WKC.let_ r12_betaEnv {S0} {V0} {V0} {KDTY} {kk} {kk} (WKC.sort r12_betaEnv Level.zero) (WKC.var r12_betaEnv Nat.zero) {hb})");
    format!("forall (r : VEnvD r12_betaEnv), Eq (VD {kk}) (xval r12_betaEnv (KExpr.let_ {S0} {V0} {V0}) {kk} {hlet} r) (r Nat.zero)")
}
pub(super) fn val_zeta_reads_value() -> String {
    let kk = "(Sk.kd (Sk.kd Sk.ty))";
    format!("fun (r : VEnvD r12_betaEnv) => Eq.refl (VD {kk}) (r Nat.zero)")
}

/// `wkc_step` run on the ζ redex, through the whole `letRedex_whnf_inv` and out
/// at `wkc_inst`. The `let_` arm's real exercise.
pub(super) fn src_wkc_step_let_witness() -> String {
    format!("def r17_wkc_step_let_witness : WKC r12_betaEnv (instantiate {V0} {S0}) {KDTY} := wkc_step r12_betaEnv r17_letTerm {KDTY} r17_let_witness (instantiate {V0} {S0}) (whnf_step.beta r17_letTerm (instantiate {V0} {S0}) (beta_reduces.zeta {S0} {S0} {V0}))")
}

/// Weakening at the `konst` arm: lifting does not move a constant, and the
/// derivation survives into the extended shape environment.
pub(super) fn src_wkc_lift_konst_witness() -> String {
    format!("def r17_wkc_lift_konst_witness : WKC (skcons {KDTY} r12_piEnv) (lift_at {DEADCONST} Nat.zero {ONE}) Sk.ty := wkc_lift0 r12_piEnv {DEADCONST} Sk.ty r17_konst_witness {KDTY}")
}

/// NON-VACUITY of the subsingleton at two derivation TERMS built by genuinely
/// different routes: R14's `wk_inst` pushed through the embedding, and this
/// rung's own `wkc_step` run on the ζ redex.
pub(super) fn ty_deriv_unique_witness() -> String {
    let g = format!("(WKC r12_betaEnv (instantiate {V0} {S0}) {KDTY})");
    format!("Eq {g} (r17_wk_wkc r12_betaEnv (instantiate {V0} {S0}) {KDTY} r15_instDeriv) r17_wkc_step_let_witness")
}
pub(super) fn val_deriv_unique_witness() -> String {
    format!("r17_wkc_deriv_unique r12_betaEnv (instantiate {V0} {S0}) {KDTY} (r17_wk_wkc r12_betaEnv (instantiate {V0} {S0}) {KDTY} r15_instDeriv) r17_wkc_step_let_witness")
}

/// Irrelevance at the same pair — and the paired refusal test measures that the
/// equation is not `Eq.refl` in disguise.
pub(super) fn ty_irrel_witness() -> String {
    format!("Eq (VD {KDTY}) (xval r12_betaEnv (instantiate {V0} {S0}) {KDTY} (r17_wk_wkc r12_betaEnv (instantiate {V0} {S0}) {KDTY} r15_instDeriv) r12_betaJunkEnv) (xval r12_betaEnv (instantiate {V0} {S0}) {KDTY} r17_wkc_step_let_witness r12_betaJunkEnv)")
}
pub(super) fn val_irrel_witness() -> String {
    format!("r17_xval_irrel r12_betaEnv (instantiate {V0} {S0}) {KDTY} (r17_wk_wkc r12_betaEnv (instantiate {V0} {S0}) {KDTY} r15_instDeriv) r17_wkc_step_let_witness r12_betaJunkEnv")
}

/// **THE PROVED OBSTRUCTION: an UNRESTRICTED `konst` rule loses subject
/// reduction.** One kernel-checked constant pairing a REAL δ step out of a REAL
/// reflected constant — `the_red_env_delta_nonvacuous`, whose target
/// `kcre_witness_delta_value` is a `lam`, which is R9's finding about every real
/// body in `the_red_env` — with the proof that NO `lam` can carry the shape
/// `Sk.ty` that a const rule assigns. So a rule `WKC D (const n us) Sk.ty` at a
/// δ-ACTIVE constant would need `WKC D (lam A b) Sk.ty` for the reduct, and that
/// is refuted. The inertness premise is forced, not chosen.
pub(super) fn ty_unrestricted_konst_refuted() -> String {
    let step = "(PropBox (delta_step (red_def the_red_env) (KExpr.const kcre_witness_delta_head (ListType.nil Level)) kcre_witness_delta_value))";
    format!("AndType {step} (WKC r12_piEnv kcre_witness_delta_value Sk.ty -> Empty)")
}
pub(super) fn val_unrestricted_konst_refuted() -> String {
    let stepty = "(delta_step (red_def the_red_env) (KExpr.const kcre_witness_delta_head (ListType.nil Level)) kcre_witness_delta_value)";
    let step = format!("(PropBox {stepty})");
    let neg = "(WKC r12_piEnv kcre_witness_delta_value Sk.ty -> Empty)";
    format!("AndType.intro {step} {neg} (r16_propBox_intro {stepty} the_red_env_delta_nonvacuous) (fun (zh : WKC r12_piEnv kcre_witness_delta_value Sk.ty) => Eq.substType Sk r17_notArrT Sk.ty (r17_shapeOf r12_piEnv kcre_witness_delta_value) (r17_shape_correct r12_piEnv kcre_witness_delta_value Sk.ty zh) ConstFreeUnit.triv)")
}

/// THE RUNG'S HEADLINE CONTRAST, in one constant: both new constructors,
/// inhabited at REAL objects — a real reflected kernel constant and R15's own
/// unreachable `let` term.
pub(super) fn ty_constructor_gap_closed() -> String {
    format!("AndType (WKC r12_piEnv {DEADCONST} Sk.ty) (WKC r12_betaEnv r17_letTerm {KDTY})")
}
pub(super) fn val_constructor_gap_closed() -> String {
    format!("AndType.intro (WKC r12_piEnv {DEADCONST} Sk.ty) (WKC r12_betaEnv r17_letTerm {KDTY}) r17_konst_witness r17_let_witness")
}

// ================================================================
// PROBES — negative controls, never registered.
// ================================================================

/// The irrelevance witness's DISCRIMINATING control: the same equation by
/// `Eq.refl`. The kernel must refuse, or the witness is definitional.
#[cfg(test)]
pub(super) fn probe_irrel_refl() -> String {
    format!("def r17_irrel_refl_probe : {} := Eq.refl (VD {KDTY}) (xval r12_betaEnv (instantiate {V0} {S0}) {KDTY} (r17_wk_wkc r12_betaEnv (instantiate {V0} {S0}) {KDTY} r15_instDeriv) r12_betaJunkEnv)", ty_irrel_witness())
}

/// NON-DEGENERACY of the `let_` interpretation clause: `xval` at a `let_` reads
/// the VALUE's interpretation into the binder slot, not a junk one.
///
/// **Two measured constraints on how this probe has to be spelled** (2026-08-27,
/// R17's third cycle, where the first spelling was ACCEPTED and therefore
/// witnessed nothing):
///
/// 1. **The value must not be a `sort`.** `xval` sends every `sort` to the TOP
///    candidate, and `junkD (Sk.kd Sk.ty)` IS the top candidate, so at
///    `r17_letTerm` the two readings agree definitionally and the refusal never
///    fires. The value here is `bvar 0`, whose interpretation is the
///    valuation's own slot.
/// 2. **The valuation must be a VARIABLE.** `r12_betaJunkEnv` is junk at every
///    index, so the two readings would agree there too whatever the value is.
///    Quantifying the probe over `r` is what makes them differ — and a `def`
///    may carry a valuation here because its type is an `Eq`, hence a **Prop**,
///    not the `Type` R15 measured the refusal for.
#[cfg(test)]
pub(super) fn probe_zeta_junk() -> String {
    let kk = "(Sk.kd (Sk.kd Sk.ty))";
    let env2 = format!("(skcons {kk} r12_betaEnv)");
    let hb = format!("(WKC.var {env2} Nat.zero)");
    let hlet = format!("(WKC.let_ r12_betaEnv {S0} {V0} {V0} {KDTY} {kk} {kk} (WKC.sort r12_betaEnv Level.zero) (WKC.var r12_betaEnv Nat.zero) {hb})");
    let lhs = format!("(xval r12_betaEnv (KExpr.let_ {S0} {V0} {V0}) {kk} {hlet} r)");
    let rhs = format!("(xval {env2} {V0} {kk} {hb} (vconsD {kk} r12_betaEnv (junkD {kk}) r))");
    format!("def r17_zeta_junk_probe : forall (r : VEnvD r12_betaEnv), Eq (VD {kk}) {lhs} {rhs} := fun (r : VEnvD r12_betaEnv) => Eq.refl (VD {kk}) {lhs}")
}

/// A `konst` derivation at a shape it does not have. The rule concludes at
/// `Sk.ty` and at no other shape; the kernel must refuse.
#[cfg(test)]
pub(super) fn probe_konst_wrong_shape() -> String {
    format!("def r17_konst_wrong_shape_probe : WKC r12_piEnv {DEADCONST} {KDTY} := WKC.konst r12_piEnv fixture_def_env_name (ListType.nil Level) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType RecMeta) (OptionType.none RecMeta))")
}

/// The `konst` rule at a constant that is NOT inert. `kcre_witness_delta_head`
/// HAS a definitional value, so the first premise cannot be `Eq.refl`; the
/// kernel must refuse, which is what makes the inertness premise real.
#[cfg(test)]
pub(super) fn probe_konst_delta_active() -> String {
    "def r17_konst_delta_active_probe : WKC r12_piEnv (KExpr.const kcre_witness_delta_head (ListType.nil Level)) Sk.ty := WKC.konst r12_piEnv kcre_witness_delta_head (ListType.nil Level) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType RecMeta) (OptionType.none RecMeta))".to_string()
}

// ================================================================
// The single ORDERED table.
// ================================================================

/// One registration item, in dependency order.
pub(super) enum R17Item {
    /// `add_inductive` — a new type former.
    Ind { name: String, src: String },
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
impl R17Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R17Item::Ind { name, .. } | R17Item::Def { name, .. } | R17Item::Thm { name, .. } => {
                name
            }
        }
    }

    /// The item as ONE parse-checkable declaration, for the parse gate.
    pub(super) fn decl_source(&self) -> String {
        match self {
            R17Item::Ind { src, .. } | R17Item::Def { src, .. } => src.clone(),
            R17Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn i(name: &str, src: String) -> R17Item {
    R17Item::Ind {
        name: name.to_string(),
        src,
    }
}

fn d(name: &str, src: String) -> R17Item {
    R17Item::Def {
        name: name.to_string(),
        src,
    }
}

fn t(name: &str, ty: String, val: String) -> R17Item {
    R17Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R17 constant, in registration order.
#[allow(clippy::too_many_lines)]
pub(super) fn r17_items() -> Vec<R17Item> {
    use super::candmodel_construct_r17_src as p1;
    vec![
        // --- Group A: the system.
        i("WKC", p1::src_wkc()),
        d("xval", p1::src_xval()),
        d("r17_wk_wkc", p1::SRC_WK_WKC.to_string()),
        // --- Group B/C: discriminator, shapes.
        d("r17_notArrT", p1::SRC_NOT_ARR_T.to_string()),
        d("r17_shapeOf", p1::SRC_SHAPE_OF.to_string()),
        t(
            "r17_shape_correct",
            p1::TY_SHAPE_CORRECT.to_string(),
            p1::val_shape_correct(),
        ),
        t(
            "r17_wkc_shape_unique",
            p1::TY_SHAPE_UNIQUE.to_string(),
            p1::VAL_SHAPE_UNIQUE.to_string(),
        ),
        t(
            "r17_shapeOf_agrees_on_wk",
            p1::TY_SHAPEOF_AGREES.to_string(),
            p1::VAL_SHAPEOF_AGREES.to_string(),
        ),
        t(
            "r17_lam_never_ty",
            p1::TY_LAM_NEVER_TY.to_string(),
            p1::VAL_LAM_NEVER_TY.to_string(),
        ),
        // --- Group D: transports, the K step, the inversion.
        d("r17_wkcCastS", p1::SRC_WKC_CAST_S.to_string()),
        d("r17_wkcCastT", p1::SRC_WKC_CAST_T.to_string()),
        t(
            "r17_wkcCastS_refl",
            p1::TY_WKC_CAST_S_REFL.to_string(),
            p1::VAL_WKC_CAST_S_REFL.to_string(),
        ),
        d("r17_wkcT", p1::src_wkc_t()),
        d("r17_wkc_inv", p1::src_wkc_inv()),
        // --- Group E: alignments, the seven arms, the subsingleton.
        t(
            "r17_uniq_var",
            p1::TY_UNIQ_VAR.to_string(),
            p1::VAL_UNIQ_VAR.to_string(),
        ),
        t(
            "r17_uniq_sort",
            p1::TY_UNIQ_SORT.to_string(),
            p1::VAL_UNIQ_SORT.to_string(),
        ),
        d("r17_konst_irrel", p1::src_konst_irrel()),
        t("r17_uniq_konst", p1::ty_uniq_konst(), p1::val_uniq_konst()),
        t("r17_pi_align", p1::ty_pi_align(), p1::val_pi_align()),
        t("r17_uniq_pi", p1::ty_uniq_pi(), p1::val_uniq_pi()),
        t("r17_lam_align", p1::ty_lam_align(), p1::val_lam_align()),
        t("r17_uniq_lam", p1::ty_uniq_lam(), p1::val_uniq_lam()),
        t(
            "r17_app_align",
            p1::TY_APP_ALIGN.to_string(),
            p1::val_app_align(),
        ),
        t(
            "r17_uniq_app",
            p1::TY_UNIQ_APP.to_string(),
            p1::val_uniq_app(),
        ),
        t("r17_let_align", p1::ty_let_align(), p1::val_let_align()),
        t("r17_uniq_let", p1::ty_uniq_let(), p1::val_uniq_let()),
        t(
            "r17_wkc_deriv_unique",
            p1::TY_DERIV_UNIQUE.to_string(),
            p1::val_deriv_unique(),
        ),
        t(
            "r17_xval_irrel",
            p1::TY_XVAL_IRREL.to_string(),
            p1::VAL_XVAL_IRREL.to_string(),
        ),
        // --- Group F: the operations.
        d("r17_wkc_lift_var", src_wkc_lift_var()),
        d("wkc_lift", src_wkc_lift()),
        d("wkc_lift0", src_wkc_lift0()),
        d("wkc_up", SRC_WKC_UP.to_string()),
        d("wkc_psub", src_wkc_psub()),
        d("r17_scons_typed", SRC_SCONS_TYPED.to_string()),
        d("wkc_inst", SRC_WKC_INST.to_string()),
        // --- Group G: subject reduction.
        t(
            "r17_headFree_wkc_arr",
            TY_HEADFREE_WKC_ARR.to_string(),
            val_headfree_wkc_arr(),
        ),
        t(
            "r17_headInert_wkc",
            TY_HEADINERT_WKC.to_string(),
            val_headinert_wkc(),
        ),
        d("r17_const_no_step", src_const_no_step()),
        d("r17_wkcLamT", SRC_WKC_LAM_T.to_string()),
        d("r17_wkc_lam_inv", src_wkc_lam_inv()),
        d("wkc_step", src_wkc_step()),
        // --- Group H: the conversion-rule settlement.
        i("WKV", SRC_WKV.to_string()),
        t(
            "r17_wkv_shape_correct",
            TY_WKV_SHAPE_CORRECT.to_string(),
            VAL_WKV_SHAPE_CORRECT.to_string(),
        ),
        t(
            "r17_conv_shape_unique",
            TY_CONV_SHAPE_UNIQUE.to_string(),
            VAL_CONV_SHAPE_UNIQUE.to_string(),
        ),
        d("r17_wkv_tag", SRC_WKV_TAG.to_string()),
        d("r17_zeroT", SRC_ZERO_T.to_string()),
        d("r17_convDeriv", SRC_CONV_DERIV.to_string()),
        t(
            "r17_conv_breaks_subsingleton",
            TY_CONV_BREAKS_SUBSINGLETON.to_string(),
            VAL_CONV_BREAKS_SUBSINGLETON.to_string(),
        ),
        t(
            "r17_conv_verdict",
            TY_CONV_VERDICT.to_string(),
            VAL_CONV_VERDICT.to_string(),
        ),
        // --- Group I: the witnesses.
        d("r17_konst_witness", src_konst_witness()),
        d("r17_deadConst_acc", src_dead_const_acc()),
        t(
            "r17_konst_mem_witness",
            ty_konst_mem_witness(),
            VAL_KONST_MEM_WITNESS.to_string(),
        ),
        d("r17_letTerm", src_let_term()),
        d("r17_let_witness", src_let_witness()),
        t(
            "r17_xval_zeta",
            TY_XVAL_ZETA.to_string(),
            VAL_XVAL_ZETA.to_string(),
        ),
        t(
            "r17_xval_zeta_reads_value",
            ty_zeta_reads_value(),
            val_zeta_reads_value(),
        ),
        d("r17_wkc_step_let_witness", src_wkc_step_let_witness()),
        d("r17_wkc_lift_konst_witness", src_wkc_lift_konst_witness()),
        t(
            "r17_deriv_unique_witness",
            ty_deriv_unique_witness(),
            val_deriv_unique_witness(),
        ),
        t("r17_irrel_witness", ty_irrel_witness(), val_irrel_witness()),
        t(
            "r17_unrestricted_konst_refuted",
            ty_unrestricted_konst_refuted(),
            val_unrestricted_konst_refuted(),
        ),
        t(
            "r17_constructor_gap_closed",
            ty_constructor_gap_closed(),
            val_constructor_gap_closed(),
        ),
    ]
}

/// Every R17 source as a parse-checkable declaration, for the parse gate, the
/// drift-proof premise test and the scratch harness.
#[cfg(test)]
pub(super) fn r17_all_sources() -> Vec<(String, String)> {
    r17_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
