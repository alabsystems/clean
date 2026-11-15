// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R17 sources, part 1 — **the CONSTRUCTOR GAP**: `WKC`, the shape system with
//! `const` and `let_`, its interpretation `xval`, and the R16-class metatheory
//! (computed shape, shape uniqueness, the derivation inversion, the
//! subsingleton theorem and `xval` derivation irrelevance) carried to seven
//! constructors.
//!
//! Read `candmodel_construct_r17.rs` first: it carries the rung's verdict, the
//! settled conversion-rule question and the proved obstruction.
//!
//! **This module deliberately imports nothing** — the R12/R14/R15/R16
//! convention, so the whole file can be `#[path]`-included into a scratch crate
//! that depends only on `clean-parser` and parse-checked in a second.

// ================================================================
// Shared spellings.
// ================================================================

/// `bvar 0`.
pub(super) const V0: &str = "(KExpr.bvar Nat.zero)";
/// `sort 0`.
pub(super) const S0: &str = "(KExpr.sort Level.zero)";
/// The shape of a semantic type-of-types.
pub(super) const KDTY: &str = "(Sk.kd Sk.ty)";
/// One, as R14 spells it.
pub(super) const ONE: &str = "(Nat.succ Nat.zero)";
/// The reflected definition environment.
pub(super) const DENV: &str = "(red_def the_red_env)";
/// The reflected recursor environment.
pub(super) const RENV: &str = "(red_rec the_red_env)";
/// The head-free proof of any non-`const`-headed spine, by computation.
pub(super) const HF_REFL: &str = "(Eq.refl (OptionType Name) (OptionType.none Name))";
/// R10's REAL reflected dead constant: `defval_for` and `recmeta_for` are both
/// `none` by `Eq.refl` over the live `the_red_env`.
pub(super) const DEADCONST: &str = "(KExpr.const fixture_def_env_name (ListType.nil Level))";

/// The `konst` rule's first inertness premise: the constant has NO definitional
/// value, so no δ step can fire at it. R10's `defval_none`.
pub(super) fn defval_none(n: &str) -> String {
    format!("Eq (OptionType KExpr) (defval_for {DENV} {n}) (OptionType.none KExpr)")
}

/// The `konst` rule's second inertness premise: the constant carries NO recursor
/// metadata. R10's `recmeta_none`.
pub(super) fn recmeta_none(n: &str) -> String {
    format!("Eq (OptionType RecMeta) (recmeta_for {RENV} {n}) (OptionType.none RecMeta)")
}

// ================================================================
// Group A — THE SYSTEM. `WK` plus `konst` and `let_`.
// ================================================================

/// **SHAPE TYPING WITH CONSTANTS AND `let`.** R12's `WK` verbatim in its five
/// landed constructors, plus the two this rung adds:
///
/// * **`konst`** — an INERT constant (no definitional value, no recursor
///   metadata: R10's two `HeadInert.inert` side conditions) is shape-typed at
///   `Sk.ty`. The restriction is not conservatism, it is forced:
///   `r17_unrestricted_konst_refuted` proves a rule at `Sk.ty` for a δ-ACTIVE
///   constant loses subject reduction, because R9 measured that every real body
///   in `the_red_env` is a `lam` and a `lam`'s shape is an `Sk.arr`.
/// * **`let_`** — the binder slot carries the shape of the VALUE, not of the
///   annotation. That is what makes ζ subject reduction land on `wkc_inst`
///   exactly as head-β does, and it is what makes the semantic ζ law
///   (`r17_xval_zeta`) `Eq.refl`.
///
/// Every constructor leads with `(D : Nat -> Sk)` and every recursive premise
/// changes it (`skcons ... D`), so `fixedIndicesToParams` cannot fire — the same
/// reason `WK.rec` takes `D` after its minors, and the shape `WKC.rec` is
/// consumed with everywhere below.
pub(super) fn src_wkc() -> String {
    format!(
        "inductive WKC : (Nat -> Sk) -> KExpr -> Sk -> Type\n\
         | var : forall (D : Nat -> Sk) (i : Nat), WKC D (KExpr.bvar i) (D i)\n\
         | sort : forall (D : Nat -> Sk) (n : Level), WKC D (KExpr.sort n) (Sk.kd Sk.ty)\n\
         | pi : forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk), WKC D A sA -> WKC (skcons (domSk sA) D) B sB -> WKC D (KExpr.pi A B) (piShape sA sB)\n\
         | lam : forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (sA : Sk) (c : Sk), WKC D A sA -> WKC (skcons (domSk sA) D) b c -> WKC D (KExpr.lam A b) (Sk.arr (domSk sA) c)\n\
         | app : forall (D : Nat -> Sk) (f : KExpr) (a : KExpr) (d : Sk) (c : Sk), WKC D f (Sk.arr d c) -> WKC D a d -> WKC D (KExpr.app f a) c\n\
         | konst : forall (D : Nat -> Sk) (n : Name) (us : ListType Level), {} -> {} -> WKC D (KExpr.const n us) Sk.ty\n\
         | let_ : forall (D : Nat -> Sk) (t : KExpr) (v : KExpr) (b : KExpr) (st : Sk) (sv : Sk) (c : Sk), WKC D t st -> WKC D v sv -> WKC (skcons sv D) b c -> WKC D (KExpr.let_ t v b) c",
        defval_none("n"),
        recmeta_none("n")
    )
}

/// **THE SEVEN-CONSTRUCTOR INTERPRETATION.** R12's `sval` in its five landed
/// clauses, plus:
///
/// * `konst` — the TOP candidate. An inert constant admits no `whnf_step` at
///   all (`r17_const_no_step`), so nothing ever has to agree with a body, and
///   the junk-probe choice is sound rather than merely convenient.
/// * `let_` — the body's interpretation at the valuation EXTENDED BY THE
///   VALUE'S. Structurally the `lam` clause applied to the `app` clause's
///   argument, which is why `r17_xval_zeta` is `Eq.refl`.
pub(super) fn src_xval() -> String {
    let motive =
        "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => VEnvD qD -> VD qs)";
    let m_var = "(fun (qD : Nat -> Sk) (qi : Nat) (qr : VEnvD qD) => qr qi)";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) (qr : VEnvD qD) (qe : KExpr) => whnf_acc qe)";
    let m_pi = "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC (skcons (domSk qsA) qD) qB qsB) (qihA : VEnvD qD -> VD qsA) (qihB : VEnvD (skcons (domSk qsA) qD) -> VD qsB) (qr : VEnvD qD) => mkTyD qsA qsB (PiSet (vcarD qsA (qihA qr)) (fun (qa : KExpr) => vcarD qsB (qihB (vconsD (domSk qsA) qD (junkD (domSk qsA)) qr)))))";
    let m_lam = "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC (skcons (domSk qsA) qD) qb qc) (qihA : VEnvD qD -> VD qsA) (qihb : VEnvD (skcons (domSk qsA) qD) -> VD qc) (qr : VEnvD qD) (qx : VD (domSk qsA)) => qihb (vconsD (domSk qsA) qD qx qr))";
    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) (qihf : VEnvD qD -> VD (Sk.arr qd qcc)) (qiha : VEnvD qD -> VD qd) (qr : VEnvD qD) => qihf qr (qiha qr))";
    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) (qr : VEnvD qD) (qe : KExpr) => whnf_acc qe)",
        defval_none("qn"),
        recmeta_none("qn")
    );
    let m_let = "(fun (qD : Nat -> Sk) (qt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qt qst) (qhv : WKC qD qv qsv) (qhb : WKC (skcons qsv qD) qb qc) (qiht : VEnvD qD -> VD qst) (qihv : VEnvD qD -> VD qsv) (qihb : VEnvD (skcons qsv qD) -> VD qc) (qr : VEnvD qD) => qihb (vconsD qsv qD (qihv qr) qr))";
    format!(
        "def xval (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) (r : VEnvD D) : VD s := WKC.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h r"
    )
}

/// **THE EMBEDDING.** Every `WK` derivation is a `WKC` derivation — the
/// extension adds constructors and removes none, so R12-R16's whole lineage
/// survives inside this one. A `def`, so later proofs reduce through it.
pub(super) const SRC_WK_WKC: &str = "def r17_wk_wkc (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) : WKC D e s := WK.rec (fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => WKC qD qe qs) (fun (qD : Nat -> Sk) (qi : Nat) => WKC.var qD qi) (fun (qD : Nat -> Sk) (qn : Level) => WKC.sort qD qn) (fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK (skcons (domSk qsA) qD) qB qsB) (qihA : WKC qD qA qsA) (qihB : WKC (skcons (domSk qsA) qD) qB qsB) => WKC.pi qD qA qB qsA qsB qihA qihB) (fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK (skcons (domSk qsA) qD) qb qc) (qihA : WKC qD qA qsA) (qihb : WKC (skcons (domSk qsA) qD) qb qc) => WKC.lam qD qA qb qsA qc qihA qihb) (fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf (Sk.arr qd qcc)) (qha : WK qD qa qd) (qihf : WKC qD qf (Sk.arr qd qcc)) (qiha : WKC qD qa qd) => WKC.app qD qf qa qd qcc qihf qiha) D e s h";

// ================================================================
// Group B — the two `Sk` DISCRIMINATORS, computed.
//
// R16's discipline: an impossible shape dies by COMPUTATION through a `Sk.rec`
// landing in `Empty`, never through a hand-written discrimination lemma.
// ================================================================

/// `ConstFreeUnit` off the arrows, `Empty` at one. Feeding a shape equation
/// `Eq Sk X (Sk.arr d c)` through this IS the discrimination.
pub(super) const SRC_NOT_ARR_T: &str = "def r17_notArrT (s : Sk) : Type := Sk.rec (fun (qs : Sk) => Type) ConstFreeUnit (fun (qs1 : Sk) (qih : Type) => ConstFreeUnit) (fun (qd : Sk) (qc : Sk) (qihd : Type) (qihc : Type) => Empty) s";

// ================================================================
// Group C — SHAPE UNIQUENESS at seven constructors.
// ================================================================

/// The shape a term MUST have, at NINE `KExpr` heads. R16's `r16_shapeOf` with
/// two junk arms replaced by real ones: `const` keeps `Sk.ty` (which is what
/// `WKC.konst` concludes, so R16's arm was accidentally already right), and
/// `let_` becomes the body's shape in the environment extended by the VALUE's —
/// the arm R16 had no rule for. `r16_arrCod` is reused verbatim.
pub(super) const SRC_SHAPE_OF: &str = "def r17_shapeOf (D : Nat -> Sk) (e : KExpr) : Sk := KExpr.rec (fun (qe : KExpr) => (Nat -> Sk) -> Sk) (fun (qn : Level) (qD : Nat -> Sk) => Sk.kd Sk.ty) (fun (qi : Nat) (qD : Nat -> Sk) => qD qi) (fun (qf : KExpr) (qa : KExpr) (qihf : (Nat -> Sk) -> Sk) (qiha : (Nat -> Sk) -> Sk) (qD : Nat -> Sk) => r16_arrCod (qihf qD)) (fun (qA : KExpr) (qb : KExpr) (qihA : (Nat -> Sk) -> Sk) (qihb : (Nat -> Sk) -> Sk) (qD : Nat -> Sk) => Sk.arr (domSk (qihA qD)) (qihb (skcons (domSk (qihA qD)) qD))) (fun (qA : KExpr) (qB : KExpr) (qihA : (Nat -> Sk) -> Sk) (qihB : (Nat -> Sk) -> Sk) (qD : Nat -> Sk) => piShape (qihA qD) (qihB (skcons (domSk (qihA qD)) qD))) (fun (qn : Name) (qus : ListType Level) (qD : Nat -> Sk) => Sk.ty) (fun (qt : KExpr) (qv : KExpr) (qb : KExpr) (qiht : (Nat -> Sk) -> Sk) (qihv : (Nat -> Sk) -> Sk) (qihb : (Nat -> Sk) -> Sk) (qD : Nat -> Sk) => qihb (skcons (qihv qD) qD)) (fun (qsn : Name) (qpi : Nat) (qsub : KExpr) (qihs : (Nat -> Sk) -> Sk) (qD : Nat -> Sk) => Sk.ty) (fun (qv : Nat) (qD : Nat -> Sk) => Sk.ty) e D";

pub(super) const TY_SHAPE_CORRECT: &str =
    "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s), Eq Sk s (r17_shapeOf D e)";

pub(super) fn val_shape_correct() -> String {
    let mot = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => Eq Sk qs (r17_shapeOf qD qe))";
    let m_var = "(fun (qD : Nat -> Sk) (qi : Nat) => Eq.refl Sk (qD qi))";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) => Eq.refl Sk (Sk.kd Sk.ty))";

    let sa = "(r17_shapeOf qD qA)";
    let sb_pi = "(r17_shapeOf (skcons (domSk (r17_shapeOf qD qA)) qD) qB)";
    let step_pi_b = format!("(Eq.substType Sk (fun (zx : Sk) => Eq Sk qsB (r17_shapeOf (skcons (domSk zx) qD) qB)) qsA {sa} qihA qihB)");
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC (skcons (domSk qsA) qD) qB qsB) (qihA : Eq Sk qsA (r17_shapeOf qD qA)) (qihB : Eq Sk qsB (r17_shapeOf (skcons (domSk qsA) qD) qB)) => Eq.trans Sk (piShape qsA qsB) (piShape {sa} qsB) (piShape {sa} {sb_pi}) (Eq.cong Sk Sk (fun (zx : Sk) => piShape zx qsB) qsA {sa} qihA) (Eq.cong Sk Sk (fun (zy : Sk) => piShape {sa} zy) qsB {sb_pi} {step_pi_b}))"
    );

    let sc_lam = "(r17_shapeOf (skcons (domSk (r17_shapeOf qD qA)) qD) qb)";
    let step_lam_b = format!("(Eq.substType Sk (fun (zx : Sk) => Eq Sk qc (r17_shapeOf (skcons (domSk zx) qD) qb)) qsA {sa} qihA qihb)");
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC (skcons (domSk qsA) qD) qb qc) (qihA : Eq Sk qsA (r17_shapeOf qD qA)) (qihb : Eq Sk qc (r17_shapeOf (skcons (domSk qsA) qD) qb)) => Eq.trans Sk (Sk.arr (domSk qsA) qc) (Sk.arr (domSk {sa}) qc) (Sk.arr (domSk {sa}) {sc_lam}) (Eq.cong Sk Sk (fun (zx : Sk) => Sk.arr (domSk zx) qc) qsA {sa} qihA) (Eq.cong Sk Sk (fun (zy : Sk) => Sk.arr (domSk {sa}) zy) qc {sc_lam} {step_lam_b}))"
    );

    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) (qihf : Eq Sk (Sk.arr qd qcc) (r17_shapeOf qD qf)) (qiha : Eq Sk qd (r17_shapeOf qD qa)) => Eq.cong Sk Sk r16_arrCod (Sk.arr qd qcc) (r17_shapeOf qD qf) qihf)";

    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) => Eq.refl Sk Sk.ty)",
        defval_none("qn"),
        recmeta_none("qn")
    );

    // let_: the conclusion shape `qc` is a bare index, so the whole content is
    // moving the body's IH across the VALUE's shape — one Eq.substType, no
    // Eq.trans at all.
    let m_let = "(fun (qD : Nat -> Sk) (qt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qt qst) (qhv : WKC qD qv qsv) (qhb : WKC (skcons qsv qD) qb qc) (qiht : Eq Sk qst (r17_shapeOf qD qt)) (qihv : Eq Sk qsv (r17_shapeOf qD qv)) (qihb : Eq Sk qc (r17_shapeOf (skcons qsv qD) qb)) => Eq.substType Sk (fun (zx : Sk) => Eq Sk qc (r17_shapeOf (skcons zx qD) qb)) qsv (r17_shapeOf qD qv) qihv qihb)";

    format!(
        "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WKC D e s) => WKC.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h"
    )
}

pub(super) const TY_SHAPE_UNIQUE: &str = "forall (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (h1 : WKC D e s1) (s2 : Sk) (h2 : WKC D e s2), Eq Sk s1 s2";
pub(super) const VAL_SHAPE_UNIQUE: &str = "fun (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (h1 : WKC D e s1) (s2 : Sk) (h2 : WKC D e s2) => Eq.trans Sk s1 (r17_shapeOf D e) s2 (r17_shape_correct D e s1 h1) (Eq.symm Sk s2 (r17_shapeOf D e) (r17_shape_correct D e s2 h2))";

/// CONSERVATIVITY, in one line: on every term the OLD system types, R16's shape
/// function and this rung's agree. Two shape-correctness theorems composed
/// through the embedding.
pub(super) const TY_SHAPEOF_AGREES: &str =
    "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s), Eq Sk (r16_shapeOf D e) (r17_shapeOf D e)";
pub(super) const VAL_SHAPEOF_AGREES: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) => Eq.trans Sk (r16_shapeOf D e) s (r17_shapeOf D e) (Eq.symm Sk s (r16_shapeOf D e) (r16_shape_correct D e s h)) (r17_shape_correct D e s (r17_wk_wkc D e s h))";

/// A `lam` is shape-typed at an `Sk.arr`, NEVER at `Sk.ty`. The whole content
/// of the unrestricted-`konst` refutation, and it uses no discrimination lemma:
/// `r17_shapeOf` COMPUTES an `Sk.arr` at a `lam`, and `r17_notArrT` reads it.
pub(super) const TY_LAM_NEVER_TY: &str =
    "forall (D : Nat -> Sk) (A : KExpr) (b : KExpr), WKC D (KExpr.lam A b) Sk.ty -> Empty";
pub(super) const VAL_LAM_NEVER_TY: &str = "fun (D : Nat -> Sk) (A : KExpr) (b : KExpr) (h : WKC D (KExpr.lam A b) Sk.ty) => Eq.substType Sk r17_notArrT Sk.ty (r17_shapeOf D (KExpr.lam A b)) (r17_shape_correct D (KExpr.lam A b) Sk.ty h) ConstFreeUnit.triv";

// ================================================================
// Group D — the transports, the K step, and THE DERIVATION INVERSION.
// ================================================================

pub(super) const SRC_WKC_CAST_S: &str = "def r17_wkcCastS (D : Nat -> Sk) (e : KExpr) (a : Sk) (b : Sk) (p : Eq Sk a b) (h : WKC D e a) : WKC D e b := Eq.rec Sk a (fun (qz : Sk) (qp : Eq Sk a qz) => WKC D e qz) h b p";

pub(super) const SRC_WKC_CAST_T: &str = "def r17_wkcCastT (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (s : Sk) (p : Eq KExpr e1 e2) (h : WKC D e1 s) : WKC D e2 s := Eq.rec KExpr e1 (fun (qz : KExpr) (qp : Eq KExpr e1 qz) => WKC D qz s) h e2 p";

/// R16's ONE K step, at `WKC`. Same quarantine rule: a standalone constant,
/// never an inlined recursor minor.
pub(super) const TY_WKC_CAST_S_REFL: &str = "forall (D : Nat -> Sk) (e : KExpr) (a : Sk) (p : Eq Sk a a) (h : WKC D e a), Eq (WKC D e a) (r17_wkcCastS D e a a p h) h";
pub(super) const VAL_WKC_CAST_S_REFL: &str =
    "fun (D : Nat -> Sk) (e : KExpr) (a : Sk) (p : Eq Sk a a) (h : WKC D e a) => Eq.refl (WKC D e a) h";

fn ih_ty(sub: &str) -> String {
    format!("forall (qs : Sk), WKC D {sub} qs -> Prop")
}

/// R16's computed motive at NINE heads, of which SEVEN are now live. Only
/// `proj` and `lit` still die by computation through `r16_propUnit` — the
/// constructor gap, made machine-visible: the dead-arm count drops 4 -> 2.
pub(super) fn src_wkc_t() -> String {
    let sort_c = "(forall (zeq : Eq Sk (Sk.kd Sk.ty) qs), Eq (WKC D (KExpr.sort qn) qs) qh (r17_wkcCastS D (KExpr.sort qn) (Sk.kd Sk.ty) qs zeq (WKC.sort D qn)) -> C) -> C";
    let bvar_c = "(forall (zeq : Eq Sk (D qi) qs), Eq (WKC D (KExpr.bvar qi) qs) qh (r17_wkcCastS D (KExpr.bvar qi) (D qi) qs zeq (WKC.var D qi)) -> C) -> C";
    let app_c = "(forall (zd : Sk) (zhf : WKC D qf (Sk.arr zd qs)) (zha : WKC D qa zd), Eq (WKC D (KExpr.app qf qa) qs) qh (WKC.app D qf qa zd qs zhf zha) -> C) -> C";
    let lam_c = "(forall (zsA : Sk) (zc : Sk) (zhA : WKC D qA zsA) (zhb : WKC (skcons (domSk zsA) D) qb zc) (zeq : Eq Sk (Sk.arr (domSk zsA) zc) qs), Eq (WKC D (KExpr.lam qA qb) qs) qh (r17_wkcCastS D (KExpr.lam qA qb) (Sk.arr (domSk zsA) zc) qs zeq (WKC.lam D qA qb zsA zc zhA zhb)) -> C) -> C";
    let pi_c = "(forall (zsA : Sk) (zsB : Sk) (zhA : WKC D qA zsA) (zhB : WKC (skcons (domSk zsA) D) qB zsB) (zeq : Eq Sk (piShape zsA zsB) qs), Eq (WKC D (KExpr.pi qA qB) qs) qh (r17_wkcCastS D (KExpr.pi qA qB) (piShape zsA zsB) qs zeq (WKC.pi D qA qB zsA zsB zhA zhB)) -> C) -> C";
    let konst_c = format!(
        "(forall (zeq : Eq Sk Sk.ty qs) (zhd : {}) (zhr : {}), Eq (WKC D (KExpr.const qn qus) qs) qh (r17_wkcCastS D (KExpr.const qn qus) Sk.ty qs zeq (WKC.konst D qn qus zhd zhr)) -> C) -> C",
        defval_none("qn"),
        recmeta_none("qn")
    );
    let let_c = "(forall (zst : Sk) (zsv : Sk) (zht : WKC D qt zst) (zhv : WKC D qv zsv) (zhb : WKC (skcons zsv D) qb qs), Eq (WKC D (KExpr.let_ qt qv qb) qs) qh (WKC.let_ D qt qv qb zst zsv qs zht zhv zhb) -> C) -> C";
    let (ihf, iha) = (ih_ty("qf"), ih_ty("qa"));
    let (ihla, ihlb) = (ih_ty("qA"), ih_ty("qb"));
    let (ihpa, ihpb) = (ih_ty("qA"), ih_ty("qB"));
    let (iht, ihv, ihb) = (ih_ty("qt"), ih_ty("qv"), ih_ty("qb"));
    let ihs = ih_ty("qsub");
    format!(
        "def r17_wkcT (D : Nat -> Sk) (C : Prop) (e : KExpr) (s : Sk) (h : WKC D e s) : Prop := KExpr.rec (fun (qe : KExpr) => forall (qs : Sk), WKC D qe qs -> Prop) \
         (fun (qn : Level) (qs : Sk) (qh : WKC D (KExpr.sort qn) qs) => {sort_c}) \
         (fun (qi : Nat) (qs : Sk) (qh : WKC D (KExpr.bvar qi) qs) => {bvar_c}) \
         (fun (qf : KExpr) (qa : KExpr) (qihf : {ihf}) (qiha : {iha}) (qs : Sk) (qh : WKC D (KExpr.app qf qa) qs) => {app_c}) \
         (fun (qA : KExpr) (qb : KExpr) (qihA : {ihla}) (qihb : {ihlb}) (qs : Sk) (qh : WKC D (KExpr.lam qA qb) qs) => {lam_c}) \
         (fun (qA : KExpr) (qB : KExpr) (qihA : {ihpa}) (qihB : {ihpb}) (qs : Sk) (qh : WKC D (KExpr.pi qA qB) qs) => {pi_c}) \
         (fun (qn : Name) (qus : ListType Level) (qs : Sk) (qh : WKC D (KExpr.const qn qus) qs) => {konst_c}) \
         (fun (qt : KExpr) (qv : KExpr) (qb : KExpr) (qiht : {iht}) (qihv : {ihv}) (qihb : {ihb}) (qs : Sk) (qh : WKC D (KExpr.let_ qt qv qb) qs) => {let_c}) \
         (fun (qsn : Name) (qpi : Nat) (qsub : KExpr) (qihs : {ihs}) (qs : Sk) (qh : WKC D (KExpr.proj qsn qpi qsub) qs) => r16_propUnit) \
         (fun (qv : Nat) (qs : Sk) (qh : WKC D (KExpr.lit qv) qs) => r16_propUnit) e s h"
    )
}

/// The inversion itself, by `WKC.rec`. Every live arm hands its OWN constructor
/// fields to the continuation with `Eq.refl` — the `konst` arm hands back its
/// two INERTNESS PROOFS the same way, so no proof-irrelevance step is needed
/// here (it is needed once, in `r17_uniq_konst`).
pub(super) fn src_wkc_inv() -> String {
    let mot =
        "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WKC qD qe qs) => r17_wkcT qD C qe qs qh)";

    let k_var = "(zk : forall (zeq : Eq Sk (qD qi) (qD qi)), Eq (WKC qD (KExpr.bvar qi) (qD qi)) (WKC.var qD qi) (r17_wkcCastS qD (KExpr.bvar qi) (qD qi) (qD qi) zeq (WKC.var qD qi)) -> C)";
    let m_var = format!(
        "(fun (qD : Nat -> Sk) (qi : Nat) {k_var} => zk (Eq.refl Sk (qD qi)) (Eq.refl (WKC qD (KExpr.bvar qi) (qD qi)) (WKC.var qD qi)))"
    );

    let k_sort = "(zk : forall (zeq : Eq Sk (Sk.kd Sk.ty) (Sk.kd Sk.ty)), Eq (WKC qD (KExpr.sort qn) (Sk.kd Sk.ty)) (WKC.sort qD qn) (r17_wkcCastS qD (KExpr.sort qn) (Sk.kd Sk.ty) (Sk.kd Sk.ty) zeq (WKC.sort qD qn)) -> C)";
    let m_sort = format!(
        "(fun (qD : Nat -> Sk) (qn : Level) {k_sort} => zk (Eq.refl Sk (Sk.kd Sk.ty)) (Eq.refl (WKC qD (KExpr.sort qn) (Sk.kd Sk.ty)) (WKC.sort qD qn)))"
    );

    let dsa = "(skcons (domSk qsA) qD)";
    let k_pi = "(zk : forall (zsA : Sk) (zsB : Sk) (zhA : WKC qD qA zsA) (zhB : WKC (skcons (domSk zsA) qD) qB zsB) (zeq : Eq Sk (piShape zsA zsB) (piShape qsA qsB)), Eq (WKC qD (KExpr.pi qA qB) (piShape qsA qsB)) (WKC.pi qD qA qB qsA qsB qhA qhB) (r17_wkcCastS qD (KExpr.pi qA qB) (piShape zsA zsB) (piShape qsA qsB) zeq (WKC.pi qD qA qB zsA zsB zhA zhB)) -> C)";
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC {dsa} qB qsB) (qihA : r17_wkcT qD C qA qsA qhA) (qihB : r17_wkcT {dsa} C qB qsB qhB) {k_pi} => zk qsA qsB qhA qhB (Eq.refl Sk (piShape qsA qsB)) (Eq.refl (WKC qD (KExpr.pi qA qB) (piShape qsA qsB)) (WKC.pi qD qA qB qsA qsB qhA qhB)))"
    );

    let k_lam = "(zk : forall (zsA : Sk) (zc : Sk) (zhA : WKC qD qA zsA) (zhb : WKC (skcons (domSk zsA) qD) qb zc) (zeq : Eq Sk (Sk.arr (domSk zsA) zc) (Sk.arr (domSk qsA) qc)), Eq (WKC qD (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc)) (WKC.lam qD qA qb qsA qc qhA qhb) (r17_wkcCastS qD (KExpr.lam qA qb) (Sk.arr (domSk zsA) zc) (Sk.arr (domSk qsA) qc) zeq (WKC.lam qD qA qb zsA zc zhA zhb)) -> C)";
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC {dsa} qb qc) (qihA : r17_wkcT qD C qA qsA qhA) (qihb : r17_wkcT {dsa} C qb qc qhb) {k_lam} => zk qsA qc qhA qhb (Eq.refl Sk (Sk.arr (domSk qsA) qc)) (Eq.refl (WKC qD (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc)) (WKC.lam qD qA qb qsA qc qhA qhb)))"
    );

    let k_app = "(zk : forall (zd : Sk) (zhf : WKC qD qf (Sk.arr zd qcc)) (zha : WKC qD qa zd), Eq (WKC qD (KExpr.app qf qa) qcc) (WKC.app qD qf qa qd qcc qhf qha) (WKC.app qD qf qa zd qcc zhf zha) -> C)";
    let m_app = format!(
        "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) (qihf : r17_wkcT qD C qf (Sk.arr qd qcc) qhf) (qiha : r17_wkcT qD C qa qd qha) {k_app} => zk qd qhf qha (Eq.refl (WKC qD (KExpr.app qf qa) qcc) (WKC.app qD qf qa qd qcc qhf qha)))"
    );

    let k_konst = format!(
        "(zk : forall (zeq : Eq Sk Sk.ty Sk.ty) (zhd : {}) (zhr : {}), Eq (WKC qD (KExpr.const qn qus) Sk.ty) (WKC.konst qD qn qus qhd qhr) (r17_wkcCastS qD (KExpr.const qn qus) Sk.ty Sk.ty zeq (WKC.konst qD qn qus zhd zhr)) -> C)",
        defval_none("qn"),
        recmeta_none("qn")
    );
    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) {k_konst} => zk (Eq.refl Sk Sk.ty) qhd qhr (Eq.refl (WKC qD (KExpr.const qn qus) Sk.ty) (WKC.konst qD qn qus qhd qhr)))",
        defval_none("qn"),
        recmeta_none("qn")
    );

    let k_let = "(zk : forall (zst : Sk) (zsv : Sk) (zht : WKC qD qt zst) (zhv : WKC qD qv zsv) (zhb : WKC (skcons zsv qD) qb qc), Eq (WKC qD (KExpr.let_ qt qv qb) qc) (WKC.let_ qD qt qv qb qst qsv qc qht qhv qhb) (WKC.let_ qD qt qv qb zst zsv qc zht zhv zhb) -> C)";
    let m_let = format!(
        "(fun (qD : Nat -> Sk) (qt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qt qst) (qhv : WKC qD qv qsv) (qhb : WKC (skcons qsv qD) qb qc) (qiht : r17_wkcT qD C qt qst qht) (qihv : r17_wkcT qD C qv qsv qhv) (qihb : r17_wkcT (skcons qsv qD) C qb qc qhb) {k_let} => zk qst qsv qht qhv qhb (Eq.refl (WKC qD (KExpr.let_ qt qv qb) qc) (WKC.let_ qD qt qv qb qst qsv qc qht qhv qhb)))"
    );

    format!(
        "def r17_wkc_inv (D : Nat -> Sk) (C : Prop) (e : KExpr) (s : Sk) (h : WKC D e s) : r17_wkcT D C e s h := WKC.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h"
    )
}

// ================================================================
// Group E — the ALIGNMENTS and the SEVEN uniqueness arms.
// ================================================================

pub(super) fn ty_pi_align() -> String {
    let dsa = "(skcons (domSk sA) D)";
    format!("forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WKC D A sA) (hB : WKC {dsa} B sB) (ihA : forall (zh : WKC D A sA), Eq (WKC D A sA) hA zh) (ihB : forall (zh : WKC {dsa} B sB), Eq (WKC {dsa} B sB) hB zh) (zsA : Sk) (zsB : Sk) (zhA : WKC D A zsA) (zhB : WKC (skcons (domSk zsA) D) B zsB) (zeq : Eq Sk (piShape zsA zsB) (piShape sA sB)), Eq (WKC D (KExpr.pi A B) (piShape sA sB)) (r17_wkcCastS D (KExpr.pi A B) (piShape zsA zsB) (piShape sA sB) zeq (WKC.pi D A B zsA zsB zhA zhB)) (WKC.pi D A B sA sB hA hB)")
}

pub(super) fn val_pi_align() -> String {
    let dsa = "(skcons (domSk sA) D)";
    let goal = "(WKC D (KExpr.pi A B) (piShape sA sB))";
    let tgt = "(WKC.pi D A B sA sB hA hB)";
    let inner_mot = format!("(fun (qz : Sk) (qp : Eq Sk sB qz) => forall (whB2 : WKC {dsa} B qz) (weq2 : Eq Sk (piShape sA qz) (piShape sA sB)), Eq {goal} (r17_wkcCastS D (KExpr.pi A B) (piShape sA qz) (piShape sA sB) weq2 (WKC.pi D A B sA qz whA whB2)) {tgt})");
    let congs = format!("(Eq.trans {goal} (WKC.pi D A B sA sB whA whB2) (WKC.pi D A B sA sB hA whB2) {tgt} (Eq.cong (WKC D A sA) {goal} (fun (zx : WKC D A sA) => WKC.pi D A B sA sB zx whB2) whA hA (Eq.symm (WKC D A sA) hA whA (ihA whA))) (Eq.cong (WKC {dsa} B sB) {goal} (fun (zy : WKC {dsa} B sB) => WKC.pi D A B sA sB hA zy) whB2 hB (Eq.symm (WKC {dsa} B sB) hB whB2 (ihB whB2))))");
    let inner_base = format!("(fun (whB2 : WKC {dsa} B sB) (weq2 : Eq Sk (piShape sA sB) (piShape sA sB)) => Eq.trans {goal} (r17_wkcCastS D (KExpr.pi A B) (piShape sA sB) (piShape sA sB) weq2 (WKC.pi D A B sA sB whA whB2)) (WKC.pi D A B sA sB whA whB2) {tgt} (r17_wkcCastS_refl D (KExpr.pi A B) (piShape sA sB) weq2 (WKC.pi D A B sA sB whA whB2)) {congs})");
    let outer_mot = format!("(fun (qz : Sk) (qp : Eq Sk sA qz) => forall (whA : WKC D A qz) (wsB : Sk) (whB : WKC (skcons (domSk qz) D) B wsB) (weq : Eq Sk (piShape qz wsB) (piShape sA sB)), Eq {goal} (r17_wkcCastS D (KExpr.pi A B) (piShape qz wsB) (piShape sA sB) weq (WKC.pi D A B qz wsB whA whB)) {tgt})");
    let outer_base = format!("(fun (whA : WKC D A sA) (wsB : Sk) (whB : WKC {dsa} B wsB) => Eq.rec Sk sB {inner_mot} {inner_base} wsB (r17_wkc_shape_unique {dsa} B sB hB wsB whB) whB)");
    format!("fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WKC D A sA) (hB : WKC {dsa} B sB) (ihA : forall (zh : WKC D A sA), Eq (WKC D A sA) hA zh) (ihB : forall (zh : WKC {dsa} B sB), Eq (WKC {dsa} B sB) hB zh) (zsA : Sk) (zsB : Sk) (zhA : WKC D A zsA) (zhB : WKC (skcons (domSk zsA) D) B zsB) (zeq : Eq Sk (piShape zsA zsB) (piShape sA sB)) => Eq.rec Sk sA {outer_mot} {outer_base} zsA (r17_wkc_shape_unique D A sA hA zsA zhA) zhA zsB zhB zeq")
}

pub(super) fn ty_lam_align() -> String {
    let dsa = "(skcons (domSk sA) D)";
    format!("forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (sA : Sk) (c : Sk) (hA : WKC D A sA) (hb : WKC {dsa} b c) (ihA : forall (zh : WKC D A sA), Eq (WKC D A sA) hA zh) (ihb : forall (zh : WKC {dsa} b c), Eq (WKC {dsa} b c) hb zh) (zsA : Sk) (zc : Sk) (zhA : WKC D A zsA) (zhb : WKC (skcons (domSk zsA) D) b zc) (zeq : Eq Sk (Sk.arr (domSk zsA) zc) (Sk.arr (domSk sA) c)), Eq (WKC D (KExpr.lam A b) (Sk.arr (domSk sA) c)) (r17_wkcCastS D (KExpr.lam A b) (Sk.arr (domSk zsA) zc) (Sk.arr (domSk sA) c) zeq (WKC.lam D A b zsA zc zhA zhb)) (WKC.lam D A b sA c hA hb)")
}

pub(super) fn val_lam_align() -> String {
    let dsa = "(skcons (domSk sA) D)";
    let goal = "(WKC D (KExpr.lam A b) (Sk.arr (domSk sA) c))";
    let tgt = "(WKC.lam D A b sA c hA hb)";
    let inner_mot = format!("(fun (qz : Sk) (qp : Eq Sk c qz) => forall (whb2 : WKC {dsa} b qz) (weq2 : Eq Sk (Sk.arr (domSk sA) qz) (Sk.arr (domSk sA) c)), Eq {goal} (r17_wkcCastS D (KExpr.lam A b) (Sk.arr (domSk sA) qz) (Sk.arr (domSk sA) c) weq2 (WKC.lam D A b sA qz whA whb2)) {tgt})");
    let congs = format!("(Eq.trans {goal} (WKC.lam D A b sA c whA whb2) (WKC.lam D A b sA c hA whb2) {tgt} (Eq.cong (WKC D A sA) {goal} (fun (zx : WKC D A sA) => WKC.lam D A b sA c zx whb2) whA hA (Eq.symm (WKC D A sA) hA whA (ihA whA))) (Eq.cong (WKC {dsa} b c) {goal} (fun (zy : WKC {dsa} b c) => WKC.lam D A b sA c hA zy) whb2 hb (Eq.symm (WKC {dsa} b c) hb whb2 (ihb whb2))))");
    let inner_base = format!("(fun (whb2 : WKC {dsa} b c) (weq2 : Eq Sk (Sk.arr (domSk sA) c) (Sk.arr (domSk sA) c)) => Eq.trans {goal} (r17_wkcCastS D (KExpr.lam A b) (Sk.arr (domSk sA) c) (Sk.arr (domSk sA) c) weq2 (WKC.lam D A b sA c whA whb2)) (WKC.lam D A b sA c whA whb2) {tgt} (r17_wkcCastS_refl D (KExpr.lam A b) (Sk.arr (domSk sA) c) weq2 (WKC.lam D A b sA c whA whb2)) {congs})");
    let outer_mot = format!("(fun (qz : Sk) (qp : Eq Sk sA qz) => forall (whA : WKC D A qz) (wc : Sk) (whb : WKC (skcons (domSk qz) D) b wc) (weq : Eq Sk (Sk.arr (domSk qz) wc) (Sk.arr (domSk sA) c)), Eq {goal} (r17_wkcCastS D (KExpr.lam A b) (Sk.arr (domSk qz) wc) (Sk.arr (domSk sA) c) weq (WKC.lam D A b qz wc whA whb)) {tgt})");
    let outer_base = format!("(fun (whA : WKC D A sA) (wc : Sk) (whb : WKC {dsa} b wc) => Eq.rec Sk c {inner_mot} {inner_base} wc (r17_wkc_shape_unique {dsa} b c hb wc whb) whb)");
    format!("fun (D : Nat -> Sk) (A : KExpr) (b : KExpr) (sA : Sk) (c : Sk) (hA : WKC D A sA) (hb : WKC {dsa} b c) (ihA : forall (zh : WKC D A sA), Eq (WKC D A sA) hA zh) (ihb : forall (zh : WKC {dsa} b c), Eq (WKC {dsa} b c) hb zh) (zsA : Sk) (zc : Sk) (zhA : WKC D A zsA) (zhb : WKC (skcons (domSk zsA) D) b zc) (zeq : Eq Sk (Sk.arr (domSk zsA) zc) (Sk.arr (domSk sA) c)) => Eq.rec Sk sA {outer_mot} {outer_base} zsA (r17_wkc_shape_unique D A sA hA zsA zhA) zhA zc zhb zeq")
}

pub(super) const TY_APP_ALIGN: &str = "forall (D : Nat -> Sk) (f : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hf : WKC D f (Sk.arr d c)) (ha : WKC D a d) (ihf : forall (zh : WKC D f (Sk.arr d c)), Eq (WKC D f (Sk.arr d c)) hf zh) (iha : forall (zh : WKC D a d), Eq (WKC D a d) ha zh) (zd : Sk) (zhf : WKC D f (Sk.arr zd c)) (zha : WKC D a zd), Eq (WKC D (KExpr.app f a) c) (WKC.app D f a zd c zhf zha) (WKC.app D f a d c hf ha)";

pub(super) fn val_app_align() -> String {
    let goal = "(WKC D (KExpr.app f a) c)";
    let tgt = "(WKC.app D f a d c hf ha)";
    let mot = format!("(fun (qz : Sk) (qp : Eq Sk d qz) => forall (whf : WKC D f (Sk.arr qz c)) (wha : WKC D a qz), Eq {goal} (WKC.app D f a qz c whf wha) {tgt})");
    let base = format!("(fun (whf : WKC D f (Sk.arr d c)) (wha : WKC D a d) => Eq.trans {goal} (WKC.app D f a d c whf wha) (WKC.app D f a d c hf wha) {tgt} (Eq.cong (WKC D f (Sk.arr d c)) {goal} (fun (zx : WKC D f (Sk.arr d c)) => WKC.app D f a d c zx wha) whf hf (Eq.symm (WKC D f (Sk.arr d c)) hf whf (ihf whf))) (Eq.cong (WKC D a d) {goal} (fun (zy : WKC D a d) => WKC.app D f a d c hf zy) wha ha (Eq.symm (WKC D a d) ha wha (iha wha))))");
    format!("fun (D : Nat -> Sk) (f : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hf : WKC D f (Sk.arr d c)) (ha : WKC D a d) (ihf : forall (zh : WKC D f (Sk.arr d c)), Eq (WKC D f (Sk.arr d c)) hf zh) (iha : forall (zh : WKC D a d), Eq (WKC D a d) ha zh) (zd : Sk) (zhf : WKC D f (Sk.arr zd c)) (zha : WKC D a zd) => Eq.rec Sk d {mot} {base} zd (r17_wkc_shape_unique D a d ha zd zha) zhf zha")
}

/// **THE NEW ALIGNMENT.** `WKC.let_` carries the conclusion shape `c` as a bare
/// index — like `WKC.app` and unlike `WKC.lam`/`WKC.pi` — so there is NO CAST at
/// all. What it does have is TWO existential shapes (`st` from the annotation
/// and `sv` from the value), so it needs two J's where `app` needs one, and
/// three `Eq.cong`s where `app` needs two.
pub(super) fn ty_let_align() -> String {
    let db = "(skcons sv D)";
    format!("forall (D : Nat -> Sk) (t : KExpr) (v : KExpr) (b : KExpr) (st : Sk) (sv : Sk) (c : Sk) (ht : WKC D t st) (hv : WKC D v sv) (hb : WKC {db} b c) (iht : forall (zh : WKC D t st), Eq (WKC D t st) ht zh) (ihv : forall (zh : WKC D v sv), Eq (WKC D v sv) hv zh) (ihb : forall (zh : WKC {db} b c), Eq (WKC {db} b c) hb zh) (zst : Sk) (zsv : Sk) (zht : WKC D t zst) (zhv : WKC D v zsv) (zhb : WKC (skcons zsv D) b c), Eq (WKC D (KExpr.let_ t v b) c) (WKC.let_ D t v b zst zsv c zht zhv zhb) (WKC.let_ D t v b st sv c ht hv hb)")
}

pub(super) fn val_let_align() -> String {
    let db = "(skcons sv D)";
    let goal = "(WKC D (KExpr.let_ t v b) c)";
    let tgt = "(WKC.let_ D t v b st sv c ht hv hb)";
    let congs = format!("(Eq.trans {goal} (WKC.let_ D t v b st sv c wht whv whb) (WKC.let_ D t v b st sv c ht whv whb) {tgt} (Eq.cong (WKC D t st) {goal} (fun (zx : WKC D t st) => WKC.let_ D t v b st sv c zx whv whb) wht ht (Eq.symm (WKC D t st) ht wht (iht wht))) (Eq.trans {goal} (WKC.let_ D t v b st sv c ht whv whb) (WKC.let_ D t v b st sv c ht hv whb) {tgt} (Eq.cong (WKC D v sv) {goal} (fun (zy : WKC D v sv) => WKC.let_ D t v b st sv c ht zy whb) whv hv (Eq.symm (WKC D v sv) hv whv (ihv whv))) (Eq.cong (WKC {db} b c) {goal} (fun (zw : WKC {db} b c) => WKC.let_ D t v b st sv c ht hv zw) whb hb (Eq.symm (WKC {db} b c) hb whb (ihb whb)))))");
    let inner_mot = format!("(fun (qy : Sk) (qq : Eq Sk sv qy) => forall (whv : WKC D v qy) (whb : WKC (skcons qy D) b c), Eq {goal} (WKC.let_ D t v b st qy c wht whv whb) {tgt})");
    let inner_base = format!("(fun (whv : WKC D v sv) (whb : WKC {db} b c) => {congs})");
    let outer_mot = format!("(fun (qz : Sk) (qp : Eq Sk st qz) => forall (wht : WKC D t qz), Eq {goal} (WKC.let_ D t v b qz zsv c wht zhv zhb) {tgt})");
    let outer_base = format!("(fun (wht : WKC D t st) => Eq.rec Sk sv {inner_mot} {inner_base} zsv (r17_wkc_shape_unique D v sv hv zsv zhv) zhv zhb)");
    format!("fun (D : Nat -> Sk) (t : KExpr) (v : KExpr) (b : KExpr) (st : Sk) (sv : Sk) (c : Sk) (ht : WKC D t st) (hv : WKC D v sv) (hb : WKC {db} b c) (iht : forall (zh : WKC D t st), Eq (WKC D t st) ht zh) (ihv : forall (zh : WKC D v sv), Eq (WKC D v sv) hv zh) (ihb : forall (zh : WKC {db} b c), Eq (WKC {db} b c) hb zh) (zst : Sk) (zsv : Sk) (zht : WKC D t zst) (zhv : WKC D v zsv) (zhb : WKC (skcons zsv D) b c) => Eq.rec Sk st {outer_mot} {outer_base} zst (r17_wkc_shape_unique D t st ht zst zht) zht")
}

// ---- the seven arms ----

pub(super) const TY_UNIQ_VAR: &str = "forall (D : Nat -> Sk) (i : Nat) (h2 : WKC D (KExpr.bvar i) (D i)), Eq (WKC D (KExpr.bvar i) (D i)) (WKC.var D i) h2";
pub(super) const VAL_UNIQ_VAR: &str = "fun (D : Nat -> Sk) (i : Nat) (h2 : WKC D (KExpr.bvar i) (D i)) => r17_wkc_inv D (Eq (WKC D (KExpr.bvar i) (D i)) (WKC.var D i) h2) (KExpr.bvar i) (D i) h2 (fun (zeq : Eq Sk (D i) (D i)) (zh : Eq (WKC D (KExpr.bvar i) (D i)) h2 (r17_wkcCastS D (KExpr.bvar i) (D i) (D i) zeq (WKC.var D i))) => Eq.symm (WKC D (KExpr.bvar i) (D i)) h2 (WKC.var D i) (Eq.trans (WKC D (KExpr.bvar i) (D i)) h2 (r17_wkcCastS D (KExpr.bvar i) (D i) (D i) zeq (WKC.var D i)) (WKC.var D i) zh (r17_wkcCastS_refl D (KExpr.bvar i) (D i) zeq (WKC.var D i))))";

pub(super) const TY_UNIQ_SORT: &str = "forall (D : Nat -> Sk) (n : Level) (h2 : WKC D (KExpr.sort n) (Sk.kd Sk.ty)), Eq (WKC D (KExpr.sort n) (Sk.kd Sk.ty)) (WKC.sort D n) h2";
pub(super) const VAL_UNIQ_SORT: &str = "fun (D : Nat -> Sk) (n : Level) (h2 : WKC D (KExpr.sort n) (Sk.kd Sk.ty)) => r17_wkc_inv D (Eq (WKC D (KExpr.sort n) (Sk.kd Sk.ty)) (WKC.sort D n) h2) (KExpr.sort n) (Sk.kd Sk.ty) h2 (fun (zeq : Eq Sk (Sk.kd Sk.ty) (Sk.kd Sk.ty)) (zh : Eq (WKC D (KExpr.sort n) (Sk.kd Sk.ty)) h2 (r17_wkcCastS D (KExpr.sort n) (Sk.kd Sk.ty) (Sk.kd Sk.ty) zeq (WKC.sort D n))) => Eq.symm (WKC D (KExpr.sort n) (Sk.kd Sk.ty)) h2 (WKC.sort D n) (Eq.trans (WKC D (KExpr.sort n) (Sk.kd Sk.ty)) h2 (r17_wkcCastS D (KExpr.sort n) (Sk.kd Sk.ty) (Sk.kd Sk.ty) zeq (WKC.sort D n)) (WKC.sort D n) zh (r17_wkcCastS_refl D (KExpr.sort n) (Sk.kd Sk.ty) zeq (WKC.sort D n))))";

pub(super) fn ty_uniq_pi() -> String {
    let dsa = "(skcons (domSk sA) D)";
    format!("forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WKC D A sA) (hB : WKC {dsa} B sB) (ihA : forall (zh : WKC D A sA), Eq (WKC D A sA) hA zh) (ihB : forall (zh : WKC {dsa} B sB), Eq (WKC {dsa} B sB) hB zh) (h2 : WKC D (KExpr.pi A B) (piShape sA sB)), Eq (WKC D (KExpr.pi A B) (piShape sA sB)) (WKC.pi D A B sA sB hA hB) h2")
}

pub(super) fn val_uniq_pi() -> String {
    let dsa = "(skcons (domSk sA) D)";
    let goal = "(WKC D (KExpr.pi A B) (piShape sA sB))";
    let cast = "(r17_wkcCastS D (KExpr.pi A B) (piShape zsA zsB) (piShape sA sB) zeq (WKC.pi D A B zsA zsB zhA zhB))";
    let k = format!("(fun (zsA : Sk) (zsB : Sk) (zhA : WKC D A zsA) (zhB : WKC (skcons (domSk zsA) D) B zsB) (zeq : Eq Sk (piShape zsA zsB) (piShape sA sB)) (zh : Eq {goal} h2 {cast}) => Eq.symm {goal} h2 (WKC.pi D A B sA sB hA hB) (Eq.trans {goal} h2 {cast} (WKC.pi D A B sA sB hA hB) zh (r17_pi_align D A B sA sB hA hB ihA ihB zsA zsB zhA zhB zeq)))");
    format!("fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WKC D A sA) (hB : WKC {dsa} B sB) (ihA : forall (zh : WKC D A sA), Eq (WKC D A sA) hA zh) (ihB : forall (zh : WKC {dsa} B sB), Eq (WKC {dsa} B sB) hB zh) (h2 : WKC D (KExpr.pi A B) (piShape sA sB)) => r17_wkc_inv D (Eq {goal} (WKC.pi D A B sA sB hA hB) h2) (KExpr.pi A B) (piShape sA sB) h2 {k}")
}

pub(super) fn ty_uniq_lam() -> String {
    let dsa = "(skcons (domSk sA) D)";
    format!("forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (sA : Sk) (c : Sk) (hA : WKC D A sA) (hb : WKC {dsa} b c) (ihA : forall (zh : WKC D A sA), Eq (WKC D A sA) hA zh) (ihb : forall (zh : WKC {dsa} b c), Eq (WKC {dsa} b c) hb zh) (h2 : WKC D (KExpr.lam A b) (Sk.arr (domSk sA) c)), Eq (WKC D (KExpr.lam A b) (Sk.arr (domSk sA) c)) (WKC.lam D A b sA c hA hb) h2")
}

pub(super) fn val_uniq_lam() -> String {
    let dsa = "(skcons (domSk sA) D)";
    let goal = "(WKC D (KExpr.lam A b) (Sk.arr (domSk sA) c))";
    let cast = "(r17_wkcCastS D (KExpr.lam A b) (Sk.arr (domSk zsA) zc) (Sk.arr (domSk sA) c) zeq (WKC.lam D A b zsA zc zhA zhb))";
    let k = format!("(fun (zsA : Sk) (zc : Sk) (zhA : WKC D A zsA) (zhb : WKC (skcons (domSk zsA) D) b zc) (zeq : Eq Sk (Sk.arr (domSk zsA) zc) (Sk.arr (domSk sA) c)) (zh : Eq {goal} h2 {cast}) => Eq.symm {goal} h2 (WKC.lam D A b sA c hA hb) (Eq.trans {goal} h2 {cast} (WKC.lam D A b sA c hA hb) zh (r17_lam_align D A b sA c hA hb ihA ihb zsA zc zhA zhb zeq)))");
    format!("fun (D : Nat -> Sk) (A : KExpr) (b : KExpr) (sA : Sk) (c : Sk) (hA : WKC D A sA) (hb : WKC {dsa} b c) (ihA : forall (zh : WKC D A sA), Eq (WKC D A sA) hA zh) (ihb : forall (zh : WKC {dsa} b c), Eq (WKC {dsa} b c) hb zh) (h2 : WKC D (KExpr.lam A b) (Sk.arr (domSk sA) c)) => r17_wkc_inv D (Eq {goal} (WKC.lam D A b sA c hA hb) h2) (KExpr.lam A b) (Sk.arr (domSk sA) c) h2 {k}")
}

pub(super) const TY_UNIQ_APP: &str = "forall (D : Nat -> Sk) (f : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hf : WKC D f (Sk.arr d c)) (ha : WKC D a d) (ihf : forall (zh : WKC D f (Sk.arr d c)), Eq (WKC D f (Sk.arr d c)) hf zh) (iha : forall (zh : WKC D a d), Eq (WKC D a d) ha zh) (h2 : WKC D (KExpr.app f a) c), Eq (WKC D (KExpr.app f a) c) (WKC.app D f a d c hf ha) h2";

pub(super) fn val_uniq_app() -> String {
    let goal = "(WKC D (KExpr.app f a) c)";
    let k = format!("(fun (zd : Sk) (zhf : WKC D f (Sk.arr zd c)) (zha : WKC D a zd) (zh : Eq {goal} h2 (WKC.app D f a zd c zhf zha)) => Eq.symm {goal} h2 (WKC.app D f a d c hf ha) (Eq.trans {goal} h2 (WKC.app D f a zd c zhf zha) (WKC.app D f a d c hf ha) zh (r17_app_align D f a d c hf ha ihf iha zd zhf zha)))");
    format!("fun (D : Nat -> Sk) (f : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hf : WKC D f (Sk.arr d c)) (ha : WKC D a d) (ihf : forall (zh : WKC D f (Sk.arr d c)), Eq (WKC D f (Sk.arr d c)) hf zh) (iha : forall (zh : WKC D a d), Eq (WKC D a d) ha zh) (h2 : WKC D (KExpr.app f a) c) => r17_wkc_inv D (Eq {goal} (WKC.app D f a d c hf ha) h2) (KExpr.app f a) c h2 {k}")
}

/// **THE PROOF-IRRELEVANCE STEP, AS A STANDALONE CONSTANT.** Two `konst`
/// derivations of one judgment differ only in their INERTNESS PROOFS, which are
/// `Eq`s and therefore Props, and the KERNEL holds any two proofs of a Prop
/// definitionally equal — so the statement is `Eq.refl`.
///
/// **It must be its own constant, and that is measured, not stylistic.** R14
/// recorded the position dependence (`r14_vdCast_irrel`, and
/// `candmodel_construct_r14.rs` §2): written INLINE, the ELABORATOR compares the
/// two proof binders as free variables and refuses with an `fvar` mismatch,
/// while the identical statement registers cleanly through
/// `add_recursive_def`. R17 hit exactly that on its first cycle
/// (`fvar mismatch: FVarId(7) vs FVarId(3)` inside `r17_uniq_konst`), so the
/// step is factored out here and APPLIED. Had the rule's premises been the
/// `Type`-valued `HeadInert` instead of R10's two `Eq` side conditions, no
/// factoring would have helped and the subsingleton would have been lost.
pub(super) fn src_konst_irrel() -> String {
    let g = "(WKC D (KExpr.const n us) Sk.ty)";
    format!(
        "def r17_konst_irrel (D : Nat -> Sk) (n : Name) (us : ListType Level) (hd1 : {}) (hr1 : {}) (hd2 : {}) (hr2 : {}) : Eq {g} (WKC.konst D n us hd1 hr1) (WKC.konst D n us hd2 hr2) := Eq.refl {g} (WKC.konst D n us hd1 hr1)",
        defval_none("n"),
        recmeta_none("n"),
        defval_none("n"),
        recmeta_none("n")
    )
}

/// The `konst` arm of derivation uniqueness: the inversion, the cast-kill, and
/// one application of the standalone irrelevance step.
pub(super) fn ty_uniq_konst() -> String {
    format!(
        "forall (D : Nat -> Sk) (n : Name) (us : ListType Level) (hd : {}) (hr : {}) (h2 : WKC D (KExpr.const n us) Sk.ty), Eq (WKC D (KExpr.const n us) Sk.ty) (WKC.konst D n us hd hr) h2",
        defval_none("n"),
        recmeta_none("n")
    )
}

pub(super) fn val_uniq_konst() -> String {
    let goal = "(WKC D (KExpr.const n us) Sk.ty)";
    let cast = "(r17_wkcCastS D (KExpr.const n us) Sk.ty Sk.ty zeq (WKC.konst D n us zhd zhr))";
    let kill = format!("(Eq.trans {goal} {cast} (WKC.konst D n us zhd zhr) (WKC.konst D n us hd hr) (r17_wkcCastS_refl D (KExpr.const n us) Sk.ty zeq (WKC.konst D n us zhd zhr)) (r17_konst_irrel D n us zhd zhr hd hr))");
    let k = format!(
        "(fun (zeq : Eq Sk Sk.ty Sk.ty) (zhd : {}) (zhr : {}) (zh : Eq {goal} h2 {cast}) => Eq.symm {goal} h2 (WKC.konst D n us hd hr) (Eq.trans {goal} h2 {cast} (WKC.konst D n us hd hr) zh {kill}))",
        defval_none("n"),
        recmeta_none("n")
    );
    format!(
        "fun (D : Nat -> Sk) (n : Name) (us : ListType Level) (hd : {}) (hr : {}) (h2 : {goal}) => r17_wkc_inv D (Eq {goal} (WKC.konst D n us hd hr) h2) (KExpr.const n us) Sk.ty h2 {k}",
        defval_none("n"),
        recmeta_none("n")
    )
}

pub(super) fn ty_uniq_let() -> String {
    let db = "(skcons sv D)";
    format!("forall (D : Nat -> Sk) (t : KExpr) (v : KExpr) (b : KExpr) (st : Sk) (sv : Sk) (c : Sk) (ht : WKC D t st) (hv : WKC D v sv) (hb : WKC {db} b c) (iht : forall (zh : WKC D t st), Eq (WKC D t st) ht zh) (ihv : forall (zh : WKC D v sv), Eq (WKC D v sv) hv zh) (ihb : forall (zh : WKC {db} b c), Eq (WKC {db} b c) hb zh) (h2 : WKC D (KExpr.let_ t v b) c), Eq (WKC D (KExpr.let_ t v b) c) (WKC.let_ D t v b st sv c ht hv hb) h2")
}

pub(super) fn val_uniq_let() -> String {
    let db = "(skcons sv D)";
    let goal = "(WKC D (KExpr.let_ t v b) c)";
    let k = format!("(fun (zst : Sk) (zsv : Sk) (zht : WKC D t zst) (zhv : WKC D v zsv) (zhb : WKC (skcons zsv D) b c) (zh : Eq {goal} h2 (WKC.let_ D t v b zst zsv c zht zhv zhb)) => Eq.symm {goal} h2 (WKC.let_ D t v b st sv c ht hv hb) (Eq.trans {goal} h2 (WKC.let_ D t v b zst zsv c zht zhv zhb) (WKC.let_ D t v b st sv c ht hv hb) zh (r17_let_align D t v b st sv c ht hv hb iht ihv ihb zst zsv zht zhv zhb)))");
    format!("fun (D : Nat -> Sk) (t : KExpr) (v : KExpr) (b : KExpr) (st : Sk) (sv : Sk) (c : Sk) (ht : WKC D t st) (hv : WKC D v sv) (hb : WKC {db} b c) (iht : forall (zh : WKC D t st), Eq (WKC D t st) ht zh) (ihv : forall (zh : WKC D v sv), Eq (WKC D v sv) hv zh) (ihb : forall (zh : WKC {db} b c), Eq (WKC {db} b c) hb zh) (h2 : {goal}) => r17_wkc_inv D (Eq {goal} (WKC.let_ D t v b st sv c ht hv hb) h2) (KExpr.let_ t v b) c h2 {k}")
}

/// **THE SUBSINGLETON, AT SEVEN CONSTRUCTORS.** R16's headline SURVIVES the
/// extension: shape assignment stays syntax-directed (each rule is keyed by the
/// subject's head constructor and no rule is optional), its shapes stay unique,
/// and the two new arms add no non-determinism — `konst`'s only freedom is in
/// Prop, and `let_`'s two existential shapes are pinned by uniqueness.
pub(super) const TY_DERIV_UNIQUE: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h1 : WKC D e s) (h2 : WKC D e s), Eq (WKC D e s) h1 h2";

pub(super) fn val_deriv_unique() -> String {
    let mot = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh1 : WKC qD qe qs) => forall (qh2 : WKC qD qe qs), Eq (WKC qD qe qs) qh1 qh2)";
    let dsa = "(skcons (domSk qsA) qD)";
    let m_var = "(fun (qD : Nat -> Sk) (qi : Nat) => r17_uniq_var qD qi)";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) => r17_uniq_sort qD qn)";
    let m_pi = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WKC qD qA qsA) (qhB : WKC {dsa} qB qsB) (qihA : forall (qz : WKC qD qA qsA), Eq (WKC qD qA qsA) qhA qz) (qihB : forall (qz : WKC {dsa} qB qsB), Eq (WKC {dsa} qB qsB) qhB qz) => r17_uniq_pi qD qA qB qsA qsB qhA qhB qihA qihB)");
    let m_lam = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WKC qD qA qsA) (qhb : WKC {dsa} qb qc) (qihA : forall (qz : WKC qD qA qsA), Eq (WKC qD qA qsA) qhA qz) (qihb : forall (qz : WKC {dsa} qb qc), Eq (WKC {dsa} qb qc) qhb qz) => r17_uniq_lam qD qA qb qsA qc qhA qhb qihA qihb)");
    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WKC qD qf (Sk.arr qd qcc)) (qha : WKC qD qa qd) (qihf : forall (qz : WKC qD qf (Sk.arr qd qcc)), Eq (WKC qD qf (Sk.arr qd qcc)) qhf qz) (qiha : forall (qz : WKC qD qa qd), Eq (WKC qD qa qd) qha qz) => r17_uniq_app qD qf qa qd qcc qhf qha qihf qiha)";
    let m_konst = format!(
        "(fun (qD : Nat -> Sk) (qn : Name) (qus : ListType Level) (qhd : {}) (qhr : {}) => r17_uniq_konst qD qn qus qhd qhr)",
        defval_none("qn"),
        recmeta_none("qn")
    );
    let dbv = "(skcons qsv qD)";
    let m_let = format!("(fun (qD : Nat -> Sk) (qt : KExpr) (qv : KExpr) (qb : KExpr) (qst : Sk) (qsv : Sk) (qc : Sk) (qht : WKC qD qt qst) (qhv : WKC qD qv qsv) (qhb : WKC {dbv} qb qc) (qiht : forall (qz : WKC qD qt qst), Eq (WKC qD qt qst) qht qz) (qihv : forall (qz : WKC qD qv qsv), Eq (WKC qD qv qsv) qhv qz) (qihb : forall (qz : WKC {dbv} qb qc), Eq (WKC {dbv} qb qc) qhb qz) => r17_uniq_let qD qt qv qb qst qsv qc qht qhv qhb qiht qihv qihb)");
    format!("fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h1 : WKC D e s) (h2 : WKC D e s) => WKC.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} {m_konst} {m_let} D e s h1 h2")
}

/// **`xval` DERIVATION IRRELEVANCE**, one `Eq.cong` off the subsingleton —
/// R16's payoff, carried to the extended system unchanged.
pub(super) const TY_XVAL_IRREL: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h1 : WKC D e s) (h2 : WKC D e s) (r : VEnvD D), Eq (VD s) (xval D e s h1 r) (xval D e s h2 r)";
pub(super) const VAL_XVAL_IRREL: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h1 : WKC D e s) (h2 : WKC D e s) (r : VEnvD D) => Eq.cong (WKC D e s) (VD s) (fun (qh : WKC D e s) => xval D e s qh r) h1 h2 (r17_wkc_deriv_unique D e s h1 h2)";
