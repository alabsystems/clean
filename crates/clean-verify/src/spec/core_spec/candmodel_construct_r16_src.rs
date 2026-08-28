// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R16 sources — **`sval` DERIVATION IRRELEVANCE**, the single ingredient R15
//! proved `val_conv` and the ∀-form of `val_step` are missing.
//!
//! Read `candmodel_construct_r16.rs` first: it carries the rung's verdict and
//! the scope of what landed.
//!
//! **This module deliberately imports nothing** — the R14/R15 convention, so the
//! whole file can be `#[path]`-included into a scratch crate that depends only
//! on `clean-parser` and parse-checked in a second.
//!
//! ## The route, and why it is SHORTER than R15's
//!
//! R15's handoff proposed `sval`-valued inversions at all five `WK` heads plus
//! `r15_wk_shape_unique`. Landing shape-uniqueness first makes a STRONGER and
//! CHEAPER statement available: `WK` is a **subsingleton** — any two derivations
//! of the same term at the same shape are EQUAL — and `sval` irrelevance is then
//! one `Eq.cong`. So the five semantic inversions collapse to ONE derivation
//! inversion, and R13's funext / R14's congruences are not needed at all.

// ================================================================
// Shared spellings.
// ================================================================

/// `bvar 0`.
pub(super) const V0: &str = "(KExpr.bvar Nat.zero)";
/// `bvar 1` — the SECOND annotation, which gives a second β redex with the same
/// contractum and the same shape.
pub(super) const V1: &str = "(KExpr.bvar (Nat.succ Nat.zero))";
/// `sort 0`.
pub(super) const S0: &str = "(KExpr.sort Level.zero)";
/// The shape of a semantic type-of-types.
pub(super) const KDTY: &str = "(Sk.kd Sk.ty)";
/// The shape of R12's contrast environment's slots.
pub(super) const KDKDTY: &str = "(Sk.kd (Sk.kd Sk.ty))";
/// The common reduct of both contrast redexes.
pub(super) const INST0: &str = "(instantiate (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))";

// ================================================================
// Group A — the Prop unit, the arrow projection, and the Prop box.
// ================================================================

/// The fragment has **no `Unit`/`True`** (`whnf_progress.rs:143`), and R15's
/// `ConstFreeUnit` is `Type`-sorted, so it cannot be a dead arm of a computed
/// motive whose live arms are Props — the kernel is NON-CUMULATIVE. A reflexive
/// `Eq` is the cheapest inhabited Prop the fragment already has.
pub(super) const SRC_PROP_UNIT: &str = "def r16_propUnit : Prop := Eq Nat Nat.zero Nat.zero";
pub(super) const SRC_PROP_TRIV: &str = "def r16_propTriv : r16_propUnit := Eq.refl Nat Nat.zero";

/// The codomain of an arrow shape; junk elsewhere. This is what turns
/// `WK.app`'s premise shape `Sk.arr d c` into `c` under one `Eq.cong`, which is
/// the whole of `Sk.arr`'s second-component injectivity — no discrimination
/// lemma, exactly R15's computed-motive discipline.
pub(super) const SRC_ARR_COD: &str = "def r16_arrCod (s : Sk) : Sk := Sk.rec (fun (qs : Sk) => Sk) Sk.ty (fun (qs1 : Sk) (qih : Sk) => Sk.ty) (fun (qd : Sk) (qc : Sk) (qihd : Sk) (qihc : Sk) => qc) s";

/// **The Prop-to-Type box.** R15's `r15_val_step_sem` and `r15_val_star_sem`
/// quantify their continuation over `C : Type`; the ∀-form of `val_step` is an
/// `Eq`, which is a **Prop**, and the kernel is non-cumulative, so the Prop
/// cannot be handed to those theorems directly. One one-field inductive closes
/// it, and nothing else in the rung needs it.
pub(super) const SRC_PROP_BOX: &str = "inductive PropBox (P : Prop) : Type
| mk : P -> PropBox P";

pub(super) const SRC_PROP_BOX_INTRO: &str =
    "def r16_propBox_intro (P : Prop) (p : P) : PropBox P := PropBox.mk P p";

pub(super) const SRC_UNBOX: &str = "def r16_unbox (P : Prop) (b : PropBox P) : P := PropBox.rec P (fun (qb : PropBox P) => P) (fun (qp : P) => qp) b";

// ================================================================
// Group B — SHAPE UNIQUENESS, through a computed shape function.
//
// R15 named `r15_wk_shape_unique` as a prerequisite. Proving it through a
// TERM-recursive shape function rather than through five CPS inversions is what
// makes it four lines an arm: `r16_shapeOf` computes the shape a term must
// have, every `WK` derivation agrees with it, and uniqueness is one `Eq.trans`.
// ================================================================

/// The shape a term MUST have in a given shape environment, by recursion on the
/// TERM. The motive is `KExpr -> (Nat -> Sk) -> Sk`, not `KExpr -> Sk`, because
/// the environment changes under a binder.
pub(super) const SRC_SHAPE_OF: &str = "def r16_shapeOf (D : Nat -> Sk) (e : KExpr) : Sk := KExpr.rec (fun (qe : KExpr) => (Nat -> Sk) -> Sk) (fun (qn : Level) (qD : Nat -> Sk) => Sk.kd Sk.ty) (fun (qi : Nat) (qD : Nat -> Sk) => qD qi) (fun (qf : KExpr) (qa : KExpr) (qihf : (Nat -> Sk) -> Sk) (qiha : (Nat -> Sk) -> Sk) (qD : Nat -> Sk) => r16_arrCod (qihf qD)) (fun (qA : KExpr) (qb : KExpr) (qihA : (Nat -> Sk) -> Sk) (qihb : (Nat -> Sk) -> Sk) (qD : Nat -> Sk) => Sk.arr (domSk (qihA qD)) (qihb (skcons (domSk (qihA qD)) qD))) (fun (qA : KExpr) (qB : KExpr) (qihA : (Nat -> Sk) -> Sk) (qihB : (Nat -> Sk) -> Sk) (qD : Nat -> Sk) => piShape (qihA qD) (qihB (skcons (domSk (qihA qD)) qD))) (fun (qn : Name) (qus : ListType Level) (qD : Nat -> Sk) => Sk.ty) (fun (qt : KExpr) (qv : KExpr) (qb : KExpr) (qiht : (Nat -> Sk) -> Sk) (qihv : (Nat -> Sk) -> Sk) (qihb : (Nat -> Sk) -> Sk) (qD : Nat -> Sk) => Sk.ty) (fun (qsn : Name) (qpi : Nat) (qsub : KExpr) (qihs : (Nat -> Sk) -> Sk) (qD : Nat -> Sk) => Sk.ty) (fun (qv : Nat) (qD : Nat -> Sk) => Sk.ty) e D";

pub(super) const TY_SHAPE_CORRECT: &str =
    "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s), Eq Sk s (r16_shapeOf D e)";

pub(super) fn val_shape_correct() -> String {
    let mot = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => Eq Sk qs (r16_shapeOf qD qe))";
    let m_var = "(fun (qD : Nat -> Sk) (qi : Nat) => Eq.refl Sk (qD qi))";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) => Eq.refl Sk (Sk.kd Sk.ty))";

    // pi: piShape qsA qsB = piShape SA qsB = piShape SA SB.
    let sa = "(r16_shapeOf qD qA)";
    let sb_pi = "(r16_shapeOf (skcons (domSk (r16_shapeOf qD qA)) qD) qB)";
    let step_pi_b = format!("(Eq.substType Sk (fun (zx : Sk) => Eq Sk qsB (r16_shapeOf (skcons (domSk zx) qD) qB)) qsA {sa} qihA qihB)");
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK (skcons (domSk qsA) qD) qB qsB) (qihA : Eq Sk qsA (r16_shapeOf qD qA)) (qihB : Eq Sk qsB (r16_shapeOf (skcons (domSk qsA) qD) qB)) => Eq.trans Sk (piShape qsA qsB) (piShape {sa} qsB) (piShape {sa} {sb_pi}) (Eq.cong Sk Sk (fun (zx : Sk) => piShape zx qsB) qsA {sa} qihA) (Eq.cong Sk Sk (fun (zy : Sk) => piShape {sa} zy) qsB {sb_pi} {step_pi_b}))"
    );

    // lam: arr (domSk qsA) qc = arr (domSk SA) qc = arr (domSk SA) C.
    let sc_lam = "(r16_shapeOf (skcons (domSk (r16_shapeOf qD qA)) qD) qb)";
    let step_lam_b = format!("(Eq.substType Sk (fun (zx : Sk) => Eq Sk qc (r16_shapeOf (skcons (domSk zx) qD) qb)) qsA {sa} qihA qihb)");
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK (skcons (domSk qsA) qD) qb qc) (qihA : Eq Sk qsA (r16_shapeOf qD qA)) (qihb : Eq Sk qc (r16_shapeOf (skcons (domSk qsA) qD) qb)) => Eq.trans Sk (Sk.arr (domSk qsA) qc) (Sk.arr (domSk {sa}) qc) (Sk.arr (domSk {sa}) {sc_lam}) (Eq.cong Sk Sk (fun (zx : Sk) => Sk.arr (domSk zx) qc) qsA {sa} qihA) (Eq.cong Sk Sk (fun (zy : Sk) => Sk.arr (domSk {sa}) zy) qc {sc_lam} {step_lam_b}))"
    );

    // app: one Eq.cong through r16_arrCod; both sides compute to the goal.
    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf (Sk.arr qd qcc)) (qha : WK qD qa qd) (qihf : Eq Sk (Sk.arr qd qcc) (r16_shapeOf qD qf)) (qiha : Eq Sk qd (r16_shapeOf qD qa)) => Eq.cong Sk Sk r16_arrCod (Sk.arr qd qcc) (r16_shapeOf qD qf) qihf)";

    format!(
        "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) => WK.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h"
    )
}

pub(super) const TY_SHAPE_UNIQUE: &str = "forall (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (h1 : WK D e s1) (s2 : Sk) (h2 : WK D e s2), Eq Sk s1 s2";
pub(super) const VAL_SHAPE_UNIQUE: &str = "fun (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (h1 : WK D e s1) (s2 : Sk) (h2 : WK D e s2) => Eq.trans Sk s1 (r16_shapeOf D e) s2 (r16_shape_correct D e s1 h1) (Eq.symm Sk s2 (r16_shapeOf D e) (r16_shape_correct D e s2 h2))";

// ================================================================
// Group C — the shape transport, and the ONE step that uses K.
// ================================================================

/// Transport a shape derivation along a shape equality. A `def` over a BARE
/// `Eq.rec` (R14's rule: `Eq.substType` does not delta-unfold, so a transport
/// spelled with it is opaque and the `Eq.refl` base case never reduces).
pub(super) const SRC_WK_CAST_S: &str = "def r16_wkCastS (D : Nat -> Sk) (e : KExpr) (a : Sk) (b : Sk) (p : Eq Sk a b) (h : WK D e a) : WK D e b := Eq.rec Sk a (fun (qz : Sk) (qp : Eq Sk a qz) => WK D e qz) h b p";

/// **THE ONE K STEP OF THE RUNG, ISOLATED AS A STANDALONE CONSTANT.** After the
/// two based-path inductions in each alignment lemma, the leftover shape
/// equation is REFLEXIVE but is a *variable* proof, so plain ι does not fire on
/// it. `Eq` is a K-like inductive in this kernel (`Eq.rec.is_k = true`,
/// `env/inductive_recursor.rs:1036`, exercised by
/// `tc/tests/recursor.rs::test_k_axiom_reduction`), so the kernel reduces the
/// major to `Eq.refl` and the cast computes away — and the proof is `Eq.refl`.
/// Kept standalone, never inlined as a recursor minor, per the ladder's
/// proof-irrelevance rule.
pub(super) const TY_WK_CAST_S_REFL: &str = "forall (D : Nat -> Sk) (e : KExpr) (a : Sk) (p : Eq Sk a a) (h : WK D e a), Eq (WK D e a) (r16_wkCastS D e a a p h) h";
pub(super) const VAL_WK_CAST_S_REFL: &str = "fun (D : Nat -> Sk) (e : KExpr) (a : Sk) (p : Eq Sk a a) (h : WK D e a) => Eq.refl (WK D e a) h";

// ================================================================
// Group D — THE ONE DERIVATION INVERSION, as a computed motive.
//
// R15's idiom exactly: a `KExpr.rec` on the SUBJECT that maps each head to the
// continuation-passing case analysis its `WK` rule deserves, and every head
// outside `WK`'s five-constructor reach to `r16_propUnit`, so those four arms
// die by COMPUTATION rather than by a discrimination lemma.
// ================================================================

fn ih_ty(sub: &str) -> String {
    format!("forall (qs : Sk), WK D {sub} qs -> Prop")
}

pub(super) fn src_wk_t() -> String {
    let sort_c = "(forall (zeq : Eq Sk (Sk.kd Sk.ty) qs), Eq (WK D (KExpr.sort qn) qs) qh (r16_wkCastS D (KExpr.sort qn) (Sk.kd Sk.ty) qs zeq (WK.sort D qn)) -> C) -> C";
    let bvar_c = "(forall (zeq : Eq Sk (D qi) qs), Eq (WK D (KExpr.bvar qi) qs) qh (r16_wkCastS D (KExpr.bvar qi) (D qi) qs zeq (WK.var D qi)) -> C) -> C";
    let app_c = "(forall (zd : Sk) (zhf : WK D qf (Sk.arr zd qs)) (zha : WK D qa zd), Eq (WK D (KExpr.app qf qa) qs) qh (WK.app D qf qa zd qs zhf zha) -> C) -> C";
    let lam_c = "(forall (zsA : Sk) (zc : Sk) (zhA : WK D qA zsA) (zhb : WK (skcons (domSk zsA) D) qb zc) (zeq : Eq Sk (Sk.arr (domSk zsA) zc) qs), Eq (WK D (KExpr.lam qA qb) qs) qh (r16_wkCastS D (KExpr.lam qA qb) (Sk.arr (domSk zsA) zc) qs zeq (WK.lam D qA qb zsA zc zhA zhb)) -> C) -> C";
    let pi_c = "(forall (zsA : Sk) (zsB : Sk) (zhA : WK D qA zsA) (zhB : WK (skcons (domSk zsA) D) qB zsB) (zeq : Eq Sk (piShape zsA zsB) qs), Eq (WK D (KExpr.pi qA qB) qs) qh (r16_wkCastS D (KExpr.pi qA qB) (piShape zsA zsB) qs zeq (WK.pi D qA qB zsA zsB zhA zhB)) -> C) -> C";
    let (ihf, iha) = (ih_ty("qf"), ih_ty("qa"));
    let (ihla, ihlb) = (ih_ty("qA"), ih_ty("qb"));
    let (ihpa, ihpb) = (ih_ty("qA"), ih_ty("qB"));
    let (iht, ihv, ihb) = (ih_ty("qt"), ih_ty("qv"), ih_ty("qb"));
    let ihs = ih_ty("qsub");
    format!(
        "def r16_wkT (D : Nat -> Sk) (C : Prop) (e : KExpr) (s : Sk) (h : WK D e s) : Prop := KExpr.rec (fun (qe : KExpr) => forall (qs : Sk), WK D qe qs -> Prop) \
         (fun (qn : Level) (qs : Sk) (qh : WK D (KExpr.sort qn) qs) => {sort_c}) \
         (fun (qi : Nat) (qs : Sk) (qh : WK D (KExpr.bvar qi) qs) => {bvar_c}) \
         (fun (qf : KExpr) (qa : KExpr) (qihf : {ihf}) (qiha : {iha}) (qs : Sk) (qh : WK D (KExpr.app qf qa) qs) => {app_c}) \
         (fun (qA : KExpr) (qb : KExpr) (qihA : {ihla}) (qihb : {ihlb}) (qs : Sk) (qh : WK D (KExpr.lam qA qb) qs) => {lam_c}) \
         (fun (qA : KExpr) (qB : KExpr) (qihA : {ihpa}) (qihB : {ihpb}) (qs : Sk) (qh : WK D (KExpr.pi qA qB) qs) => {pi_c}) \
         (fun (qn : Name) (qus : ListType Level) (qs : Sk) (qh : WK D (KExpr.const qn qus) qs) => r16_propUnit) \
         (fun (qt : KExpr) (qv : KExpr) (qb : KExpr) (qiht : {iht}) (qihv : {ihv}) (qihb : {ihb}) (qs : Sk) (qh : WK D (KExpr.let_ qt qv qb) qs) => r16_propUnit) \
         (fun (qsn : Name) (qpi : Nat) (qsub : KExpr) (qihs : {ihs}) (qs : Sk) (qh : WK D (KExpr.proj qsn qpi qsub) qs) => r16_propUnit) \
         (fun (qv : Nat) (qs : Sk) (qh : WK D (KExpr.lit qv) qs) => r16_propUnit) e s h"
    )
}

/// The inversion itself, by `WK.rec`. Every arm hands its OWN constructor fields
/// to the continuation with `Eq.refl` — no injectivity, no discrimination — and
/// the reflexive shape cast computes away by plain ι, so **K is not used here**.
pub(super) fn src_wk_inv() -> String {
    let mot =
        "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => r16_wkT qD C qe qs qh)";

    let k_var = "(zk : forall (zeq : Eq Sk (qD qi) (qD qi)), Eq (WK qD (KExpr.bvar qi) (qD qi)) (WK.var qD qi) (r16_wkCastS qD (KExpr.bvar qi) (qD qi) (qD qi) zeq (WK.var qD qi)) -> C)";
    let m_var = format!(
        "(fun (qD : Nat -> Sk) (qi : Nat) {k_var} => zk (Eq.refl Sk (qD qi)) (Eq.refl (WK qD (KExpr.bvar qi) (qD qi)) (WK.var qD qi)))"
    );

    let k_sort = "(zk : forall (zeq : Eq Sk (Sk.kd Sk.ty) (Sk.kd Sk.ty)), Eq (WK qD (KExpr.sort qn) (Sk.kd Sk.ty)) (WK.sort qD qn) (r16_wkCastS qD (KExpr.sort qn) (Sk.kd Sk.ty) (Sk.kd Sk.ty) zeq (WK.sort qD qn)) -> C)";
    let m_sort = format!(
        "(fun (qD : Nat -> Sk) (qn : Level) {k_sort} => zk (Eq.refl Sk (Sk.kd Sk.ty)) (Eq.refl (WK qD (KExpr.sort qn) (Sk.kd Sk.ty)) (WK.sort qD qn)))"
    );

    let dsa = "(skcons (domSk qsA) qD)";
    let k_pi = "(zk : forall (zsA : Sk) (zsB : Sk) (zhA : WK qD qA zsA) (zhB : WK (skcons (domSk zsA) qD) qB zsB) (zeq : Eq Sk (piShape zsA zsB) (piShape qsA qsB)), Eq (WK qD (KExpr.pi qA qB) (piShape qsA qsB)) (WK.pi qD qA qB qsA qsB qhA qhB) (r16_wkCastS qD (KExpr.pi qA qB) (piShape zsA zsB) (piShape qsA qsB) zeq (WK.pi qD qA qB zsA zsB zhA zhB)) -> C)";
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK {dsa} qB qsB) (qihA : r16_wkT qD C qA qsA qhA) (qihB : r16_wkT {dsa} C qB qsB qhB) {k_pi} => zk qsA qsB qhA qhB (Eq.refl Sk (piShape qsA qsB)) (Eq.refl (WK qD (KExpr.pi qA qB) (piShape qsA qsB)) (WK.pi qD qA qB qsA qsB qhA qhB)))"
    );

    let k_lam = "(zk : forall (zsA : Sk) (zc : Sk) (zhA : WK qD qA zsA) (zhb : WK (skcons (domSk zsA) qD) qb zc) (zeq : Eq Sk (Sk.arr (domSk zsA) zc) (Sk.arr (domSk qsA) qc)), Eq (WK qD (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc)) (WK.lam qD qA qb qsA qc qhA qhb) (r16_wkCastS qD (KExpr.lam qA qb) (Sk.arr (domSk zsA) zc) (Sk.arr (domSk qsA) qc) zeq (WK.lam qD qA qb zsA zc zhA zhb)) -> C)";
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK {dsa} qb qc) (qihA : r16_wkT qD C qA qsA qhA) (qihb : r16_wkT {dsa} C qb qc qhb) {k_lam} => zk qsA qc qhA qhb (Eq.refl Sk (Sk.arr (domSk qsA) qc)) (Eq.refl (WK qD (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc)) (WK.lam qD qA qb qsA qc qhA qhb)))"
    );

    let k_app = "(zk : forall (zd : Sk) (zhf : WK qD qf (Sk.arr zd qcc)) (zha : WK qD qa zd), Eq (WK qD (KExpr.app qf qa) qcc) (WK.app qD qf qa qd qcc qhf qha) (WK.app qD qf qa zd qcc zhf zha) -> C)";
    let m_app = format!(
        "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf (Sk.arr qd qcc)) (qha : WK qD qa qd) (qihf : r16_wkT qD C qf (Sk.arr qd qcc) qhf) (qiha : r16_wkT qD C qa qd qha) {k_app} => zk qd qhf qha (Eq.refl (WK qD (KExpr.app qf qa) qcc) (WK.app qD qf qa qd qcc qhf qha)))"
    );

    format!(
        "def r16_wk_inv (D : Nat -> Sk) (C : Prop) (e : KExpr) (s : Sk) (h : WK D e s) : r16_wkT D C e s h := WK.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h"
    )
}

// ================================================================
// Group E — the three ALIGNMENT lemmas and the five arms.
//
// The inversion hands back subderivations at THEIR OWN shapes; the induction
// hypothesis only applies at the shapes the subject's derivation uses. Shape
// uniqueness closes the gap, and a based path induction (`Eq.rec`, Martin-Löf J)
// on each shape equation moves the received shape ONTO the subject's, after
// which the leftover cast is reflexive and `r16_wkCastS_refl` kills it.
// ================================================================

/// The `WK.pi` alignment: two J's, one cast-kill, two `Eq.cong`s.
pub(super) fn ty_pi_align() -> String {
    let dsa = "(skcons (domSk sA) D)";
    format!("forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK {dsa} B sB) (ihA : forall (zh : WK D A sA), Eq (WK D A sA) hA zh) (ihB : forall (zh : WK {dsa} B sB), Eq (WK {dsa} B sB) hB zh) (zsA : Sk) (zsB : Sk) (zhA : WK D A zsA) (zhB : WK (skcons (domSk zsA) D) B zsB) (zeq : Eq Sk (piShape zsA zsB) (piShape sA sB)), Eq (WK D (KExpr.pi A B) (piShape sA sB)) (r16_wkCastS D (KExpr.pi A B) (piShape zsA zsB) (piShape sA sB) zeq (WK.pi D A B zsA zsB zhA zhB)) (WK.pi D A B sA sB hA hB)")
}

pub(super) fn val_pi_align() -> String {
    let dsa = "(skcons (domSk sA) D)";
    let goal = "(WK D (KExpr.pi A B) (piShape sA sB))";
    let tgt = "(WK.pi D A B sA sB hA hB)";
    let inner_mot = format!("(fun (qz : Sk) (qp : Eq Sk sB qz) => forall (whB2 : WK {dsa} B qz) (weq2 : Eq Sk (piShape sA qz) (piShape sA sB)), Eq {goal} (r16_wkCastS D (KExpr.pi A B) (piShape sA qz) (piShape sA sB) weq2 (WK.pi D A B sA qz whA whB2)) {tgt})");
    let congs = format!("(Eq.trans {goal} (WK.pi D A B sA sB whA whB2) (WK.pi D A B sA sB hA whB2) {tgt} (Eq.cong (WK D A sA) {goal} (fun (zx : WK D A sA) => WK.pi D A B sA sB zx whB2) whA hA (Eq.symm (WK D A sA) hA whA (ihA whA))) (Eq.cong (WK {dsa} B sB) {goal} (fun (zy : WK {dsa} B sB) => WK.pi D A B sA sB hA zy) whB2 hB (Eq.symm (WK {dsa} B sB) hB whB2 (ihB whB2))))");
    let inner_base = format!("(fun (whB2 : WK {dsa} B sB) (weq2 : Eq Sk (piShape sA sB) (piShape sA sB)) => Eq.trans {goal} (r16_wkCastS D (KExpr.pi A B) (piShape sA sB) (piShape sA sB) weq2 (WK.pi D A B sA sB whA whB2)) (WK.pi D A B sA sB whA whB2) {tgt} (r16_wkCastS_refl D (KExpr.pi A B) (piShape sA sB) weq2 (WK.pi D A B sA sB whA whB2)) {congs})");
    let outer_mot = format!("(fun (qz : Sk) (qp : Eq Sk sA qz) => forall (whA : WK D A qz) (wsB : Sk) (whB : WK (skcons (domSk qz) D) B wsB) (weq : Eq Sk (piShape qz wsB) (piShape sA sB)), Eq {goal} (r16_wkCastS D (KExpr.pi A B) (piShape qz wsB) (piShape sA sB) weq (WK.pi D A B qz wsB whA whB)) {tgt})");
    let outer_base = format!("(fun (whA : WK D A sA) (wsB : Sk) (whB : WK {dsa} B wsB) => Eq.rec Sk sB {inner_mot} {inner_base} wsB (r16_wk_shape_unique {dsa} B sB hB wsB whB) whB)");
    format!("fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK {dsa} B sB) (ihA : forall (zh : WK D A sA), Eq (WK D A sA) hA zh) (ihB : forall (zh : WK {dsa} B sB), Eq (WK {dsa} B sB) hB zh) (zsA : Sk) (zsB : Sk) (zhA : WK D A zsA) (zhB : WK (skcons (domSk zsA) D) B zsB) (zeq : Eq Sk (piShape zsA zsB) (piShape sA sB)) => Eq.rec Sk sA {outer_mot} {outer_base} zsA (r16_wk_shape_unique D A sA hA zsA zhA) zhA zsB zhB zeq")
}

/// The `WK.lam` alignment. Same two J's; the annotation's derivation is a FIELD
/// of `WK.lam`, so unlike `r15_val_step_lamA` (where the annotation is
/// semantically inert) it does take part here — derivation equality is finer
/// than semantic equality.
pub(super) fn ty_lam_align() -> String {
    let dsa = "(skcons (domSk sA) D)";
    format!("forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK {dsa} b c) (ihA : forall (zh : WK D A sA), Eq (WK D A sA) hA zh) (ihb : forall (zh : WK {dsa} b c), Eq (WK {dsa} b c) hb zh) (zsA : Sk) (zc : Sk) (zhA : WK D A zsA) (zhb : WK (skcons (domSk zsA) D) b zc) (zeq : Eq Sk (Sk.arr (domSk zsA) zc) (Sk.arr (domSk sA) c)), Eq (WK D (KExpr.lam A b) (Sk.arr (domSk sA) c)) (r16_wkCastS D (KExpr.lam A b) (Sk.arr (domSk zsA) zc) (Sk.arr (domSk sA) c) zeq (WK.lam D A b zsA zc zhA zhb)) (WK.lam D A b sA c hA hb)")
}

pub(super) fn val_lam_align() -> String {
    let dsa = "(skcons (domSk sA) D)";
    let goal = "(WK D (KExpr.lam A b) (Sk.arr (domSk sA) c))";
    let tgt = "(WK.lam D A b sA c hA hb)";
    let inner_mot = format!("(fun (qz : Sk) (qp : Eq Sk c qz) => forall (whb2 : WK {dsa} b qz) (weq2 : Eq Sk (Sk.arr (domSk sA) qz) (Sk.arr (domSk sA) c)), Eq {goal} (r16_wkCastS D (KExpr.lam A b) (Sk.arr (domSk sA) qz) (Sk.arr (domSk sA) c) weq2 (WK.lam D A b sA qz whA whb2)) {tgt})");
    let congs = format!("(Eq.trans {goal} (WK.lam D A b sA c whA whb2) (WK.lam D A b sA c hA whb2) {tgt} (Eq.cong (WK D A sA) {goal} (fun (zx : WK D A sA) => WK.lam D A b sA c zx whb2) whA hA (Eq.symm (WK D A sA) hA whA (ihA whA))) (Eq.cong (WK {dsa} b c) {goal} (fun (zy : WK {dsa} b c) => WK.lam D A b sA c hA zy) whb2 hb (Eq.symm (WK {dsa} b c) hb whb2 (ihb whb2))))");
    let inner_base = format!("(fun (whb2 : WK {dsa} b c) (weq2 : Eq Sk (Sk.arr (domSk sA) c) (Sk.arr (domSk sA) c)) => Eq.trans {goal} (r16_wkCastS D (KExpr.lam A b) (Sk.arr (domSk sA) c) (Sk.arr (domSk sA) c) weq2 (WK.lam D A b sA c whA whb2)) (WK.lam D A b sA c whA whb2) {tgt} (r16_wkCastS_refl D (KExpr.lam A b) (Sk.arr (domSk sA) c) weq2 (WK.lam D A b sA c whA whb2)) {congs})");
    let outer_mot = format!("(fun (qz : Sk) (qp : Eq Sk sA qz) => forall (whA : WK D A qz) (wc : Sk) (whb : WK (skcons (domSk qz) D) b wc) (weq : Eq Sk (Sk.arr (domSk qz) wc) (Sk.arr (domSk sA) c)), Eq {goal} (r16_wkCastS D (KExpr.lam A b) (Sk.arr (domSk qz) wc) (Sk.arr (domSk sA) c) weq (WK.lam D A b qz wc whA whb)) {tgt})");
    let outer_base = format!("(fun (whA : WK D A sA) (wc : Sk) (whb : WK {dsa} b wc) => Eq.rec Sk c {inner_mot} {inner_base} wc (r16_wk_shape_unique {dsa} b c hb wc whb) whb)");
    format!("fun (D : Nat -> Sk) (A : KExpr) (b : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK {dsa} b c) (ihA : forall (zh : WK D A sA), Eq (WK D A sA) hA zh) (ihb : forall (zh : WK {dsa} b c), Eq (WK {dsa} b c) hb zh) (zsA : Sk) (zc : Sk) (zhA : WK D A zsA) (zhb : WK (skcons (domSk zsA) D) b zc) (zeq : Eq Sk (Sk.arr (domSk zsA) zc) (Sk.arr (domSk sA) c)) => Eq.rec Sk sA {outer_mot} {outer_base} zsA (r16_wk_shape_unique D A sA hA zsA zhA) zhA zc zhb zeq")
}

/// The `WK.app` alignment — **one** J and NO cast at all: `WK.app`'s conclusion
/// carries the codomain shape as a bare index, so the inversion already lands at
/// the caller's shape and only the DOMAIN shape has to be aligned.
pub(super) const TY_APP_ALIGN: &str = "forall (D : Nat -> Sk) (f : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hf : WK D f (Sk.arr d c)) (ha : WK D a d) (ihf : forall (zh : WK D f (Sk.arr d c)), Eq (WK D f (Sk.arr d c)) hf zh) (iha : forall (zh : WK D a d), Eq (WK D a d) ha zh) (zd : Sk) (zhf : WK D f (Sk.arr zd c)) (zha : WK D a zd), Eq (WK D (KExpr.app f a) c) (WK.app D f a zd c zhf zha) (WK.app D f a d c hf ha)";

pub(super) fn val_app_align() -> String {
    let goal = "(WK D (KExpr.app f a) c)";
    let tgt = "(WK.app D f a d c hf ha)";
    let mot = format!("(fun (qz : Sk) (qp : Eq Sk d qz) => forall (whf : WK D f (Sk.arr qz c)) (wha : WK D a qz), Eq {goal} (WK.app D f a qz c whf wha) {tgt})");
    let base = format!("(fun (whf : WK D f (Sk.arr d c)) (wha : WK D a d) => Eq.trans {goal} (WK.app D f a d c whf wha) (WK.app D f a d c hf wha) {tgt} (Eq.cong (WK D f (Sk.arr d c)) {goal} (fun (zx : WK D f (Sk.arr d c)) => WK.app D f a d c zx wha) whf hf (Eq.symm (WK D f (Sk.arr d c)) hf whf (ihf whf))) (Eq.cong (WK D a d) {goal} (fun (zy : WK D a d) => WK.app D f a d c hf zy) wha ha (Eq.symm (WK D a d) ha wha (iha wha))))");
    format!("fun (D : Nat -> Sk) (f : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hf : WK D f (Sk.arr d c)) (ha : WK D a d) (ihf : forall (zh : WK D f (Sk.arr d c)), Eq (WK D f (Sk.arr d c)) hf zh) (iha : forall (zh : WK D a d), Eq (WK D a d) ha zh) (zd : Sk) (zhf : WK D f (Sk.arr zd c)) (zha : WK D a zd) => Eq.rec Sk d {mot} {base} zd (r16_wk_shape_unique D a d ha zd zha) zhf zha")
}

// ---- the five arms ----

pub(super) const TY_UNIQ_VAR: &str = "forall (D : Nat -> Sk) (i : Nat) (h2 : WK D (KExpr.bvar i) (D i)), Eq (WK D (KExpr.bvar i) (D i)) (WK.var D i) h2";
pub(super) const VAL_UNIQ_VAR: &str = "fun (D : Nat -> Sk) (i : Nat) (h2 : WK D (KExpr.bvar i) (D i)) => r16_wk_inv D (Eq (WK D (KExpr.bvar i) (D i)) (WK.var D i) h2) (KExpr.bvar i) (D i) h2 (fun (zeq : Eq Sk (D i) (D i)) (zh : Eq (WK D (KExpr.bvar i) (D i)) h2 (r16_wkCastS D (KExpr.bvar i) (D i) (D i) zeq (WK.var D i))) => Eq.symm (WK D (KExpr.bvar i) (D i)) h2 (WK.var D i) (Eq.trans (WK D (KExpr.bvar i) (D i)) h2 (r16_wkCastS D (KExpr.bvar i) (D i) (D i) zeq (WK.var D i)) (WK.var D i) zh (r16_wkCastS_refl D (KExpr.bvar i) (D i) zeq (WK.var D i))))";

pub(super) const TY_UNIQ_SORT: &str = "forall (D : Nat -> Sk) (n : Level) (h2 : WK D (KExpr.sort n) (Sk.kd Sk.ty)), Eq (WK D (KExpr.sort n) (Sk.kd Sk.ty)) (WK.sort D n) h2";
pub(super) const VAL_UNIQ_SORT: &str = "fun (D : Nat -> Sk) (n : Level) (h2 : WK D (KExpr.sort n) (Sk.kd Sk.ty)) => r16_wk_inv D (Eq (WK D (KExpr.sort n) (Sk.kd Sk.ty)) (WK.sort D n) h2) (KExpr.sort n) (Sk.kd Sk.ty) h2 (fun (zeq : Eq Sk (Sk.kd Sk.ty) (Sk.kd Sk.ty)) (zh : Eq (WK D (KExpr.sort n) (Sk.kd Sk.ty)) h2 (r16_wkCastS D (KExpr.sort n) (Sk.kd Sk.ty) (Sk.kd Sk.ty) zeq (WK.sort D n))) => Eq.symm (WK D (KExpr.sort n) (Sk.kd Sk.ty)) h2 (WK.sort D n) (Eq.trans (WK D (KExpr.sort n) (Sk.kd Sk.ty)) h2 (r16_wkCastS D (KExpr.sort n) (Sk.kd Sk.ty) (Sk.kd Sk.ty) zeq (WK.sort D n)) (WK.sort D n) zh (r16_wkCastS_refl D (KExpr.sort n) (Sk.kd Sk.ty) zeq (WK.sort D n))))";

pub(super) fn ty_uniq_pi() -> String {
    let dsa = "(skcons (domSk sA) D)";
    format!("forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK {dsa} B sB) (ihA : forall (zh : WK D A sA), Eq (WK D A sA) hA zh) (ihB : forall (zh : WK {dsa} B sB), Eq (WK {dsa} B sB) hB zh) (h2 : WK D (KExpr.pi A B) (piShape sA sB)), Eq (WK D (KExpr.pi A B) (piShape sA sB)) (WK.pi D A B sA sB hA hB) h2")
}

pub(super) fn val_uniq_pi() -> String {
    let dsa = "(skcons (domSk sA) D)";
    let goal = "(WK D (KExpr.pi A B) (piShape sA sB))";
    let cast = "(r16_wkCastS D (KExpr.pi A B) (piShape zsA zsB) (piShape sA sB) zeq (WK.pi D A B zsA zsB zhA zhB))";
    let k = format!("(fun (zsA : Sk) (zsB : Sk) (zhA : WK D A zsA) (zhB : WK (skcons (domSk zsA) D) B zsB) (zeq : Eq Sk (piShape zsA zsB) (piShape sA sB)) (zh : Eq {goal} h2 {cast}) => Eq.symm {goal} h2 (WK.pi D A B sA sB hA hB) (Eq.trans {goal} h2 {cast} (WK.pi D A B sA sB hA hB) zh (r16_pi_align D A B sA sB hA hB ihA ihB zsA zsB zhA zhB zeq)))");
    format!("fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK {dsa} B sB) (ihA : forall (zh : WK D A sA), Eq (WK D A sA) hA zh) (ihB : forall (zh : WK {dsa} B sB), Eq (WK {dsa} B sB) hB zh) (h2 : WK D (KExpr.pi A B) (piShape sA sB)) => r16_wk_inv D (Eq {goal} (WK.pi D A B sA sB hA hB) h2) (KExpr.pi A B) (piShape sA sB) h2 {k}")
}

pub(super) fn ty_uniq_lam() -> String {
    let dsa = "(skcons (domSk sA) D)";
    format!("forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK {dsa} b c) (ihA : forall (zh : WK D A sA), Eq (WK D A sA) hA zh) (ihb : forall (zh : WK {dsa} b c), Eq (WK {dsa} b c) hb zh) (h2 : WK D (KExpr.lam A b) (Sk.arr (domSk sA) c)), Eq (WK D (KExpr.lam A b) (Sk.arr (domSk sA) c)) (WK.lam D A b sA c hA hb) h2")
}

pub(super) fn val_uniq_lam() -> String {
    let dsa = "(skcons (domSk sA) D)";
    let goal = "(WK D (KExpr.lam A b) (Sk.arr (domSk sA) c))";
    let cast = "(r16_wkCastS D (KExpr.lam A b) (Sk.arr (domSk zsA) zc) (Sk.arr (domSk sA) c) zeq (WK.lam D A b zsA zc zhA zhb))";
    let k = format!("(fun (zsA : Sk) (zc : Sk) (zhA : WK D A zsA) (zhb : WK (skcons (domSk zsA) D) b zc) (zeq : Eq Sk (Sk.arr (domSk zsA) zc) (Sk.arr (domSk sA) c)) (zh : Eq {goal} h2 {cast}) => Eq.symm {goal} h2 (WK.lam D A b sA c hA hb) (Eq.trans {goal} h2 {cast} (WK.lam D A b sA c hA hb) zh (r16_lam_align D A b sA c hA hb ihA ihb zsA zc zhA zhb zeq)))");
    format!("fun (D : Nat -> Sk) (A : KExpr) (b : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK {dsa} b c) (ihA : forall (zh : WK D A sA), Eq (WK D A sA) hA zh) (ihb : forall (zh : WK {dsa} b c), Eq (WK {dsa} b c) hb zh) (h2 : WK D (KExpr.lam A b) (Sk.arr (domSk sA) c)) => r16_wk_inv D (Eq {goal} (WK.lam D A b sA c hA hb) h2) (KExpr.lam A b) (Sk.arr (domSk sA) c) h2 {k}")
}

pub(super) const TY_UNIQ_APP: &str = "forall (D : Nat -> Sk) (f : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hf : WK D f (Sk.arr d c)) (ha : WK D a d) (ihf : forall (zh : WK D f (Sk.arr d c)), Eq (WK D f (Sk.arr d c)) hf zh) (iha : forall (zh : WK D a d), Eq (WK D a d) ha zh) (h2 : WK D (KExpr.app f a) c), Eq (WK D (KExpr.app f a) c) (WK.app D f a d c hf ha) h2";

pub(super) fn val_uniq_app() -> String {
    let goal = "(WK D (KExpr.app f a) c)";
    let k = format!("(fun (zd : Sk) (zhf : WK D f (Sk.arr zd c)) (zha : WK D a zd) (zh : Eq {goal} h2 (WK.app D f a zd c zhf zha)) => Eq.symm {goal} h2 (WK.app D f a d c hf ha) (Eq.trans {goal} h2 (WK.app D f a zd c zhf zha) (WK.app D f a d c hf ha) zh (r16_app_align D f a d c hf ha ihf iha zd zhf zha)))");
    format!("fun (D : Nat -> Sk) (f : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hf : WK D f (Sk.arr d c)) (ha : WK D a d) (ihf : forall (zh : WK D f (Sk.arr d c)), Eq (WK D f (Sk.arr d c)) hf zh) (iha : forall (zh : WK D a d), Eq (WK D a d) ha zh) (h2 : WK D (KExpr.app f a) c) => r16_wk_inv D (Eq {goal} (WK.app D f a d c hf ha) h2) (KExpr.app f a) c h2 {k}")
}

// ================================================================
// Group F — THE HEADLINE and the payoff R15 set up.
// ================================================================

/// **`WK` IS A SUBSINGLETON.** Shape typing is syntax-directed and its shapes are
/// unique, so a term has AT MOST ONE derivation at a shape — proved, not
/// asserted. This is strictly stronger than the `sval` irrelevance R15 asked
/// for, and it makes that one `Eq.cong`.
pub(super) const TY_DERIV_UNIQUE: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h1 : WK D e s) (h2 : WK D e s), Eq (WK D e s) h1 h2";

pub(super) fn val_deriv_unique() -> String {
    let mot = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh1 : WK qD qe qs) => forall (qh2 : WK qD qe qs), Eq (WK qD qe qs) qh1 qh2)";
    let dsa = "(skcons (domSk qsA) qD)";
    let m_var = "(fun (qD : Nat -> Sk) (qi : Nat) => r16_uniq_var qD qi)";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) => r16_uniq_sort qD qn)";
    let m_pi = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK {dsa} qB qsB) (qihA : forall (qz : WK qD qA qsA), Eq (WK qD qA qsA) qhA qz) (qihB : forall (qz : WK {dsa} qB qsB), Eq (WK {dsa} qB qsB) qhB qz) => r16_uniq_pi qD qA qB qsA qsB qhA qhB qihA qihB)");
    let m_lam = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK {dsa} qb qc) (qihA : forall (qz : WK qD qA qsA), Eq (WK qD qA qsA) qhA qz) (qihb : forall (qz : WK {dsa} qb qc), Eq (WK {dsa} qb qc) qhb qz) => r16_uniq_lam qD qA qb qsA qc qhA qhb qihA qihb)");
    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf (Sk.arr qd qcc)) (qha : WK qD qa qd) (qihf : forall (qz : WK qD qf (Sk.arr qd qcc)), Eq (WK qD qf (Sk.arr qd qcc)) qhf qz) (qiha : forall (qz : WK qD qa qd), Eq (WK qD qa qd) qha qz) => r16_uniq_app qD qf qa qd qcc qhf qha qihf qiha)";
    format!("fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h1 : WK D e s) (h2 : WK D e s) => WK.rec {mot} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h1 h2")
}

/// **`sval` DERIVATION IRRELEVANCE — the constant this rung exists for**, and
/// exactly the hypothesis `r15_val_conv_from_irrel` names.
pub(super) const TY_SVAL_IRREL: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h1 : WK D e s) (h2 : WK D e s) (r : VEnvD D), Eq (VD s) (sval D e s h1 r) (sval D e s h2 r)";
pub(super) const VAL_SVAL_IRREL: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h1 : WK D e s) (h2 : WK D e s) (r : VEnvD D) => Eq.cong (WK D e s) (VD s) (fun (qh : WK D e s) => sval D e s qh r) h1 h2 (r16_wk_deriv_unique D e s h1 h2)";

/// **`val_conv`, UNCONDITIONALLY** — R15's conditional with its hypothesis
/// discharged.
pub(super) const TY_VAL_CONV: &str = "forall (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WK D e1 s) (h2 : WK D e2 s) (r : VEnvD D) (t : KExpr), whnfStar e1 w -> whnfStar e2 w -> vcarD s (sval D e1 s h1 r) t -> vcarD s (sval D e2 s h2 r) t";
pub(super) const VAL_VAL_CONV: &str = "fun (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (w : KExpr) (s : Sk) (h1 : WK D e1 s) (h2 : WK D e2 s) (r : VEnvD D) (t : KExpr) (s1 : whnfStar e1 w) (s2 : whnfStar e2 w) (hm : vcarD s (sval D e1 s h1 r) t) => r15_val_conv_from_irrel D (fun (ze : KExpr) (zs : Sk) (zh1 : WK D ze zs) (zh2 : WK D ze zs) (zr : VEnvD D) => r16_sval_irrel D ze zs zh1 zh2 zr) e1 e2 w s h1 h2 r t s1 s2 hm";

/// **THE ∀-FORM OF `val_step`** — R15's obstruction 2, closed. The `PropBox` is
/// the non-cumulativity bridge: `r15_val_step_sem`'s continuation is quantified
/// over `C : Type` and the conclusion here is an `Eq`, which is a Prop.
pub(super) const TY_VAL_STEP: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (e2 : KExpr) (st : whnf_step e e2) (h2 : WK D e2 s) (r : VEnvD D), Eq (VD s) (sval D e2 s h2 r) (sval D e s h r)";
pub(super) const VAL_VAL_STEP: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (e2 : KExpr) (st : whnf_step e e2) (h2 : WK D e2 s) (r : VEnvD D) => r16_unbox (Eq (VD s) (sval D e2 s h2 r) (sval D e s h r)) (r15_val_step_sem D e s h e2 st (PropBox (Eq (VD s) (sval D e2 s h2 r) (sval D e s h r))) (fun (zh2 : WK D e2 s) (zhv : forall (zr : VEnvD D), Eq (VD s) (sval D e2 s zh2 zr) (sval D e s h zr)) => r16_propBox_intro (Eq (VD s) (sval D e2 s h2 r) (sval D e s h r)) (Eq.trans (VD s) (sval D e2 s h2 r) (sval D e2 s zh2 r) (sval D e s h r) (r16_sval_irrel D e2 s h2 zh2 r) (zhv r))))";

/// The same along a whole reduction SEQUENCE.
pub(super) const TY_VAL_STEP_STAR: &str = "forall (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) (s : Sk) (h : WK D e s) (hw : WK D w s) (r : VEnvD D), Eq (VD s) (sval D w s hw r) (sval D e s h r)";
pub(super) const VAL_VAL_STEP_STAR: &str = "fun (D : Nat -> Sk) (e : KExpr) (w : KExpr) (hstar : whnfStar e w) (s : Sk) (h : WK D e s) (hw : WK D w s) (r : VEnvD D) => r16_unbox (Eq (VD s) (sval D w s hw r) (sval D e s h r)) (r15_val_star_sem D e w hstar s h (PropBox (Eq (VD s) (sval D w s hw r) (sval D e s h r))) (fun (zhw : WK D w s) (zhv : forall (zr : VEnvD D), Eq (VD s) (sval D w s zhw zr) (sval D e s h zr)) => r16_propBox_intro (Eq (VD s) (sval D w s hw r) (sval D e s h r)) (Eq.trans (VD s) (sval D w s hw r) (sval D w s zhw r) (sval D e s h r) (r16_sval_irrel D w s hw zhw r) (zhv r))))";

// ================================================================
// Group G — the CONCRETE conversion contrast, and the witnesses.
//
// R15's contrast is at ONE `whnf_step`. `val_conv` is about terms with a common
// reduct and NO step between them, so the contrast is stated at a pair that
// converts without either reducing to the other: R12's β redex and a SECOND
// redex whose lambda carries a different (but same-shaped) annotation. Both
// contract to `instantiate (bvar 0) (sort 0)`; neither reduces to the other.
// ================================================================

/// The second redex: `(fun (x : bvar 1). x) (Sort 0)`. Every slot of
/// `r12_betaEnv` is `kd (kd ty)`, so `bvar 1` annotates exactly as `bvar 0` does
/// and the derivation mirrors `r12_betaDeriv`.
pub(super) fn src_conv_redex2() -> String {
    format!("def r16_convRedex2 : KExpr := KExpr.app (KExpr.lam {V1} {V0}) {S0}")
}

pub(super) fn src_conv_deriv2() -> String {
    let lam = format!("(WK.lam r12_betaEnv {V1} {V0} {KDKDTY} {KDTY} (WK.var r12_betaEnv (Nat.succ Nat.zero)) (WK.var (skcons {KDTY} r12_betaEnv) Nat.zero))");
    format!("def r16_convDeriv2 : WK r12_betaEnv r16_convRedex2 {KDTY} := WK.app r12_betaEnv (KExpr.lam {V1} {V0}) {S0} {KDTY} {KDTY} {lam} (WK.sort r12_betaEnv Level.zero)")
}

pub(super) fn ty_conv_step2() -> String {
    format!("whnf_step r16_convRedex2 {INST0}")
}
pub(super) fn val_conv_step2() -> String {
    format!("whnf_step.beta r16_convRedex2 {INST0} (beta_reduces.beta {V1} {V0} {S0})")
}

pub(super) fn src_conv_star1() -> String {
    format!("def r16_convStar1 : whnfStar r12_betaRedex {INST0} := whnfStar.step r12_betaRedex {INST0} {INST0} (r14_beta_step {V0} {V0} {S0}) (whnfStar.refl {INST0})")
}

pub(super) fn src_conv_star2() -> String {
    format!("def r16_convStar2 : whnfStar r16_convRedex2 {INST0} := whnfStar.step r16_convRedex2 {INST0} {INST0} r16_convStep2 (whnfStar.refl {INST0})")
}

/// The membership transport across that CONVERSION, as a named `Type` so it can
/// sit inside an `AndType` beside R11's refutation. CONCRETE for the universe
/// reason R15 measured: any generic statement here quantifies over a valuation
/// and `VEnvD D` is `Type 1`, so a `def … : Type` carrying one is refused.
pub(super) fn src_sval_conv_transports() -> String {
    format!("def r16_svalConvTransports : Type := forall (qe : KExpr), vcarD {KDTY} (sval r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r12_betaJunkEnv) qe -> vcarD {KDTY} (sval r12_betaEnv r16_convRedex2 {KDTY} r16_convDeriv2 r12_betaJunkEnv) qe")
}

pub(super) const TY_CONV_TRANSPORTS: &str = "r16_svalConvTransports";
pub(super) fn val_conv_transports() -> String {
    format!("fun (qe : KExpr) (hm : vcarD {KDTY} (sval r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r12_betaJunkEnv) qe) => r16_val_conv r12_betaEnv r12_betaRedex r16_convRedex2 {INST0} {KDTY} r12_betaDeriv r16_convDeriv2 r12_betaJunkEnv qe r16_convStar1 r16_convStar2 hm")
}

/// R12's / R15's contrast pattern one rung on: R11's refutation of
/// conversion-invariance for `candInterp`, and UNCONDITIONAL conversion-invariance
/// for `sval`, in ONE kernel-checked constant. It RE-ASSERTS R11 rather than
/// repairing it — the positive half is about a different interpretation, on
/// shape-typed terms only.
pub(super) const TY_CONV_CONTRAST: &str =
    "AndType (r12_candInterpStepConv -> Empty) r16_svalConvTransports";
pub(super) const VAL_CONV_CONTRAST: &str = "AndType.intro (r12_candInterpStepConv -> Empty) r16_svalConvTransports r11_candInterp_step_conv_refuted r16_sval_conv_transports";

// ---- witnesses ----

/// Shape uniqueness at TWO derivation terms of the same term built by different
/// routes: R14's `wk_inst` and R15's `wk_step`.
pub(super) fn ty_shape_unique_witness() -> String {
    format!("Eq Sk {KDTY} {KDTY}")
}
pub(super) fn val_shape_unique_witness() -> String {
    format!(
        "r16_wk_shape_unique r12_betaEnv {INST0} {KDTY} r15_instDeriv {KDTY} r15_wk_step_witness"
    )
}

/// **NON-VACUITY, at two genuinely different derivation TERMS.**
/// `r15_instDeriv` is built by R14's `wk_inst` out of `WK.var`/`WK.sort`;
/// `r15_wk_step_witness` is R15's `wk_step` run on `r12_betaDeriv` through the
/// whole computed step inversion. Both inhabit `WK r12_betaEnv (instantiate
/// (bvar 0) (sort 0)) (kd ty)`, and this constant proves them EQUAL.
pub(super) fn ty_deriv_unique_witness() -> String {
    format!("Eq (WK r12_betaEnv {INST0} {KDTY}) r15_instDeriv r15_wk_step_witness")
}
pub(super) fn val_deriv_unique_witness() -> String {
    format!("r16_wk_deriv_unique r12_betaEnv {INST0} {KDTY} r15_instDeriv r15_wk_step_witness")
}

/// Irrelevance at a derivation the kernel CANNOT unfold: `r15_wk_step_sort` is
/// registered as a theorem, hence `Opaque`, so `sval` at it is stuck and the
/// equation is not `Eq.refl` in disguise. The paired refusal test measures
/// exactly that.
pub(super) fn ty_irrel_witness() -> String {
    format!("Eq (VD {KDTY}) (sval r12_betaEnv {S0} {KDTY} (WK.sort r12_betaEnv Level.zero) r12_betaJunkEnv) (sval r12_betaEnv {S0} {KDTY} r15_wk_step_sort r12_betaJunkEnv)")
}
pub(super) fn val_irrel_witness() -> String {
    format!("r16_sval_irrel r12_betaEnv {S0} {KDTY} (WK.sort r12_betaEnv Level.zero) r15_wk_step_sort r12_betaJunkEnv")
}

/// The ∀-form of `val_step` COMPUTED at R12's registered redex: the reduct's
/// interpretation at an ARBITRARY derivation — here `r15_instDeriv`, which
/// `r15_val_step_sem` never produced — agrees with the subject's.
pub(super) fn ty_val_step_witness() -> String {
    format!("Eq (VD {KDTY}) (sval r12_betaEnv {INST0} {KDTY} r15_instDeriv r12_betaJunkEnv) (sval r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r12_betaJunkEnv)")
}
pub(super) fn val_val_step_witness() -> String {
    format!("r16_val_step r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv {INST0} (r14_beta_step {V0} {V0} {S0}) r15_instDeriv r12_betaJunkEnv")
}

// ---- negative controls, not registered ----

/// Derivation uniqueness claimed ACROSS TWO DIFFERENT TERMS. `r12_betaDeriv`
/// derives the redex, `r15_instDeriv` its contractum; the kernel must refuse.
#[cfg(test)]
pub(super) fn probe_cross_term() -> String {
    format!("def r16_cross_term_probe : Eq (WK r12_betaEnv r12_betaRedex {KDTY}) r12_betaDeriv r15_instDeriv := r16_wk_deriv_unique r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r15_instDeriv")
}

/// The witness's DISCRIMINATING control: the same equation claimed by `Eq.refl`.
/// If the kernel accepted it, `r16_irrel_witness` would be definitional and
/// would witness nothing.
#[cfg(test)]
pub(super) fn probe_irrel_refl() -> String {
    format!("def r16_irrel_refl_probe : Eq (VD {KDTY}) (sval r12_betaEnv {S0} {KDTY} (WK.sort r12_betaEnv Level.zero) r12_betaJunkEnv) (sval r12_betaEnv {S0} {KDTY} r15_wk_step_sort r12_betaJunkEnv) := Eq.refl (VD {KDTY}) (sval r12_betaEnv {S0} {KDTY} (WK.sort r12_betaEnv Level.zero) r12_betaJunkEnv)")
}

/// Shape uniqueness claimed at a term with NO derivation at the second shape.
#[cfg(test)]
pub(super) fn probe_wrong_shape() -> String {
    format!("def r16_wrong_shape_probe : Eq Sk {KDTY} Sk.ty := r16_wk_shape_unique r12_betaEnv {INST0} {KDTY} r15_instDeriv Sk.ty r15_instDeriv")
}

// ================================================================
// The single ORDERED table.
// ================================================================

/// One registration item, in dependency order.
pub(super) enum R16Item {
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
impl R16Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R16Item::Ind { name, .. } | R16Item::Def { name, .. } | R16Item::Thm { name, .. } => {
                name
            }
        }
    }

    /// The item as ONE parse-checkable declaration, for the parse gate.
    pub(super) fn decl_source(&self) -> String {
        match self {
            R16Item::Ind { src, .. } | R16Item::Def { src, .. } => src.clone(),
            R16Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn i(name: &str, src: &str) -> R16Item {
    R16Item::Ind {
        name: name.to_string(),
        src: src.to_string(),
    }
}

fn d(name: &str, src: String) -> R16Item {
    R16Item::Def {
        name: name.to_string(),
        src,
    }
}

fn t(name: &str, ty: String, val: String) -> R16Item {
    R16Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R16 constant, in registration order.
pub(super) fn r16_items() -> Vec<R16Item> {
    vec![
        d("r16_propUnit", SRC_PROP_UNIT.to_string()),
        d("r16_propTriv", SRC_PROP_TRIV.to_string()),
        d("r16_arrCod", SRC_ARR_COD.to_string()),
        i("PropBox", SRC_PROP_BOX),
        d("r16_propBox_intro", SRC_PROP_BOX_INTRO.to_string()),
        d("r16_unbox", SRC_UNBOX.to_string()),
        d("r16_shapeOf", SRC_SHAPE_OF.to_string()),
        t(
            "r16_shape_correct",
            TY_SHAPE_CORRECT.to_string(),
            val_shape_correct(),
        ),
        t(
            "r16_wk_shape_unique",
            TY_SHAPE_UNIQUE.to_string(),
            VAL_SHAPE_UNIQUE.to_string(),
        ),
        d("r16_wkCastS", SRC_WK_CAST_S.to_string()),
        t(
            "r16_wkCastS_refl",
            TY_WK_CAST_S_REFL.to_string(),
            VAL_WK_CAST_S_REFL.to_string(),
        ),
        d("r16_wkT", src_wk_t()),
        d("r16_wk_inv", src_wk_inv()),
        t(
            "r16_uniq_var",
            TY_UNIQ_VAR.to_string(),
            VAL_UNIQ_VAR.to_string(),
        ),
        t(
            "r16_uniq_sort",
            TY_UNIQ_SORT.to_string(),
            VAL_UNIQ_SORT.to_string(),
        ),
        t("r16_pi_align", ty_pi_align(), val_pi_align()),
        t("r16_uniq_pi", ty_uniq_pi(), val_uniq_pi()),
        t("r16_lam_align", ty_lam_align(), val_lam_align()),
        t("r16_uniq_lam", ty_uniq_lam(), val_uniq_lam()),
        t("r16_app_align", TY_APP_ALIGN.to_string(), val_app_align()),
        t("r16_uniq_app", TY_UNIQ_APP.to_string(), val_uniq_app()),
        t(
            "r16_wk_deriv_unique",
            TY_DERIV_UNIQUE.to_string(),
            val_deriv_unique(),
        ),
        t(
            "r16_sval_irrel",
            TY_SVAL_IRREL.to_string(),
            VAL_SVAL_IRREL.to_string(),
        ),
        t(
            "r16_val_conv",
            TY_VAL_CONV.to_string(),
            VAL_VAL_CONV.to_string(),
        ),
        t(
            "r16_val_step",
            TY_VAL_STEP.to_string(),
            VAL_VAL_STEP.to_string(),
        ),
        t(
            "r16_val_step_star",
            TY_VAL_STEP_STAR.to_string(),
            VAL_VAL_STEP_STAR.to_string(),
        ),
        d("r16_convRedex2", src_conv_redex2()),
        d("r16_convDeriv2", src_conv_deriv2()),
        t("r16_convStep2", ty_conv_step2(), val_conv_step2()),
        d("r16_convStar1", src_conv_star1()),
        d("r16_convStar2", src_conv_star2()),
        d("r16_svalConvTransports", src_sval_conv_transports()),
        t(
            "r16_sval_conv_transports",
            TY_CONV_TRANSPORTS.to_string(),
            val_conv_transports(),
        ),
        t(
            "r16_conv_contrast",
            TY_CONV_CONTRAST.to_string(),
            VAL_CONV_CONTRAST.to_string(),
        ),
        t(
            "r16_shape_unique_witness",
            ty_shape_unique_witness(),
            val_shape_unique_witness(),
        ),
        t(
            "r16_deriv_unique_witness",
            ty_deriv_unique_witness(),
            val_deriv_unique_witness(),
        ),
        t("r16_irrel_witness", ty_irrel_witness(), val_irrel_witness()),
        t(
            "r16_val_step_witness",
            ty_val_step_witness(),
            val_val_step_witness(),
        ),
    ]
}

/// Every R16 source as a parse-checkable declaration, for the parse gate, the
/// drift-proof premise test and the scratch harness.
#[cfg(test)]
pub(super) fn r16_all_sources() -> Vec<(String, String)> {
    r16_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
