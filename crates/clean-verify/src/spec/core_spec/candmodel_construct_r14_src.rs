// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R14 sources — the WEAKENING and SUBSTITUTION **operations** on `WK` shape
//! derivations, and the semantic lemmas they unlock (`val_lift`, `val_psub`,
//! `val_inst`, `val_beta`).
//!
//! Read `candmodel_construct_r14.rs` first: it carries the rung's verdict, the
//! honesty notes and the measured elaborator facts.
//!
//! **This module deliberately imports nothing.** Every source it emits is built
//! from local constants, so the whole file can be `#[path]`-included into a
//! scratch crate that depends only on `clean-parser` and parse-checked in a
//! second, without a `clean-verify` build — the convention
//! `candmodel_construct_r10_src.rs` set and R12/R13 kept.

// ================================================================
// Shared spellings.
// ================================================================

/// The lift amount. Weakening inserts exactly ONE slot, and pinning the amount
/// is what keeps the index arithmetic definitional: `Nat.add i (Nat.succ
/// Nat.zero)` reduces to `Nat.succ i` because `Nat.add` recurses on its SECOND
/// argument, so `lift_bvar_at`'s "above the cut" branch needs no lemma.
pub(super) const ONE: &str = "(Nat.succ Nat.zero)";

/// `bvar 0`.
pub(super) const V0: &str = "(KExpr.bvar Nat.zero)";
/// `sort 0`.
pub(super) const S0: &str = "(KExpr.sort Level.zero)";
/// The shape of a semantic type-of-types.
pub(super) const KDTY: &str = "(Sk.kd Sk.ty)";
/// The cast used everywhere: transport a VALUE along an equality of SHAPES.
///
/// It names `r14_vdCast`, a registered `def`, and NOT `Eq.substType` — measured
/// 2026-08-27, and it is the elaborator fact that cost this rung a cycle.
/// `Eq.substType` is registered with `add_definition_checked`, so it does NOT
/// delta-unfold in whnf; a transport written with it never exposes its `Eq.rec`
/// and therefore never iota-reduces at `Eq.refl`. Every transport a later proof
/// must REDUCE THROUGH has to go through a `def` that unfolds to a bare
/// `Eq.rec` — the same class of fact as R12's `add_definition`-lowers-to-Opaque
/// note, one level further in, and it bites the FOUNDATION's own transport
/// combinator rather than only spec witnesses.
pub(super) const VDCAST: &str = "r14_vdCast";

// ================================================================
// Group A1 — the shape-environment insertion algebra.
// Corpus: Stratified/FWK.lean `skins` (:39) and `skins_succ` (:42).
// ================================================================

/// Inserting a shape slot at cutoff `c`. The corpus writes this with a decidable
/// `if i < c`; here it is a `Nat.rec` on the CUTOFF, which is not a stylistic
/// choice — it makes `skins_succ` and `skins_zero` DEFINITIONAL (the corpus
/// needs `funext` plus `omega` for `skins_succ`), and every binder case of
/// `wk_lift` then needs no transport at all.
pub(super) const SRC_SKINS: &str = "def skins (c : Nat) (t : Sk) (D : Nat -> Sk) (i : Nat) : Sk := Nat.rec (fun (qc : Nat) => (Nat -> Sk) -> Nat -> Sk) (fun (qD : Nat -> Sk) => skcons t qD) (fun (qc : Nat) (qih : (Nat -> Sk) -> Nat -> Sk) (qD : Nat -> Sk) => skcons (qD Nat.zero) (qih (fun (qj : Nat) => qD (Nat.succ qj)))) c D i";

/// The de Bruijn position of variable `i` after inserting a slot at cutoff `c`.
/// Same `Nat.rec`-on-`(c - i)` discriminator shape as `lift_bvar_at`, so the two
/// compute in step. A private copy of the subject-reduction bundle's `wkpos`,
/// which is Full-bundle-only (`bundles.rs`, `in_substitution: false`) and
/// therefore not in scope here.
pub(super) const SRC_WKPOS: &str = "def r14_wkpos (i : Nat) (c : Nat) : Nat := Nat.rec (fun (qn : Nat) => Nat) (Nat.succ i) (fun (qa : Nat) (qb : Nat) => i) (Nat.sub c i)";

// ================================================================
// Group A2 — the two derivation-level OPERATIONS.
// Corpus: FWK.lean `wk_lift` (:109), `wk_lift0` (:142), `wk_psub` (:149),
// `wk_inst` (:172).
// ================================================================

/// Transport a `WK` derivation along an equality of TERMS, as a REDUCIBLE
/// `def` whose body is a bare `Eq.rec`. `Eq.substType` will not do: it is
/// registered with `add_definition_checked` and does not delta-unfold, so a
/// transport spelled with it is opaque and `r14_sval_cast_term`'s base case
/// cannot fire the iota rule at `Eq.refl`.
pub(super) const SRC_WK_CAST_T: &str = "def r14_wkCastT (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (s : Sk) (heq : Eq KExpr e1 e2) (h : WK D e1 s) : WK D e2 s := Eq.rec KExpr e1 (fun (qz : KExpr) (qp : Eq KExpr e1 qz) => WK D qz s) h e2 heq";

/// The same for an equality of SHAPES.
pub(super) const SRC_WK_CAST_S: &str = "def r14_wkCastS (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (s2 : Sk) (heq : Eq Sk s1 s2) (h : WK D e s1) : WK D e s2 := Eq.rec Sk s1 (fun (qs : Sk) (qp : Eq Sk s1 qs) => WK D e qs) h s2 heq";

/// ...and for a VALUE along an equality of shapes. This is the one the K-like
/// reduction acts on: at a REFLEXIVE shape equality the `Eq.rec` collapses even
/// though the proof term is stuck, which is what makes `r14_venvLift_at`'s
/// corners `Eq.refl`.
pub(super) const SRC_VD_CAST: &str = "def r14_vdCast (s1 : Sk) (s2 : Sk) (heq : Eq Sk s1 s2) (v : VD s1) : VD s2 := Eq.rec Sk s1 (fun (qs : Sk) (qp : Eq Sk s1 qs) => VD qs) v s2 heq";

/// The `var` leaf of weakening, and the ONLY place in the whole rung that needs
/// a transport. One in TERM position (`lift_at (bvar i) c 1` is stuck on
/// `Nat.sub c i`, so it must be rewritten to `bvar (r14_wkpos i c)`) and one in
/// SHAPE position (`WK.var` concludes at `skins c t D (r14_wkpos i c)`, and
/// `r14_skins_idx` is what identifies that with `D i`).
///
/// It is a `def`, not a theorem: `r14_val_lift`'s var case has to REDUCE
/// `wk_lift` down to this constant, and an `add_definition` registration lowers
/// to `Opaque` and stops that (R12's measured elaborator fact (b)).
pub(super) fn src_wk_lift_var() -> String {
    let shape_cast = "r14_wkCastS (skins c t D) (KExpr.bvar (r14_wkpos i c)) (skins c t D (r14_wkpos i c)) (D i) (r14_skins_idx c i t D) (WK.var (skins c t D) (r14_wkpos i c))";
    format!(
        "def r14_wk_lift_var (c : Nat) (i : Nat) (t : Sk) (D : Nat -> Sk) : WK (skins c t D) (lift_at (KExpr.bvar i) c {ONE}) (D i) := r14_wkCastT (skins c t D) (KExpr.bvar (r14_wkpos i c)) (lift_at (KExpr.bvar i) c {ONE}) (D i) (Eq.symm KExpr (lift_at (KExpr.bvar i) c {ONE}) (KExpr.bvar (r14_wkpos i c)) (r14_lift_at_bvar_wkpos i c)) ({shape_cast})"
    )
}

/// **THE WEAKENING OPERATION.** Corpus `wk_lift` (FWK.lean:109): a `WK`
/// derivation transports to the shape environment with one slot inserted at an
/// arbitrary cutoff, at the lifted term.
///
/// Every binder case is transport-free because `skins (succ c) t (skcons s D)`
/// is DEFINITIONALLY `skcons s (skins c t D)` under the recursive `skins`
/// (`Nat.rec` ι at `Nat.succ qj`, then function eta). The corpus needs
/// `skins_succ` as a `funext` lemma there.
pub(super) fn src_wk_lift() -> String {
    let motive = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => forall (qk : Nat) (qt : Sk), WK (skins qk qt qD) (lift_at qe qk (Nat.succ Nat.zero)) qs)";
    let m_var =
        "(fun (qD : Nat -> Sk) (qi : Nat) (qk : Nat) (qt : Sk) => r14_wk_lift_var qk qi qt qD)";
    let m_sort =
        "(fun (qD : Nat -> Sk) (qn : Level) (qk : Nat) (qt : Sk) => WK.sort (skins qk qt qD) qn)";
    let ih_a = "(qihA : forall (qk : Nat) (qt : Sk), WK (skins qk qt qD) (lift_at qA qk (Nat.succ Nat.zero)) qsA)";
    let ih_pb = "(qihB : forall (qk : Nat) (qt : Sk), WK (skins qk qt (skcons (domSk qsA) qD)) (lift_at qB qk (Nat.succ Nat.zero)) qsB)";
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK (skcons (domSk qsA) qD) qB qsB) {ih_a} {ih_pb} (qk : Nat) (qt : Sk) => WK.pi (skins qk qt qD) (lift_at qA qk {ONE}) (lift_at qB (Nat.succ qk) {ONE}) qsA qsB (qihA qk qt) (qihB (Nat.succ qk) qt))"
    );
    let ih_lb = "(qihb : forall (qk : Nat) (qt : Sk), WK (skins qk qt (skcons (domSk qsA) qD)) (lift_at qb qk (Nat.succ Nat.zero)) qc)";
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK (skcons (domSk qsA) qD) qb qc) {ih_a} {ih_lb} (qk : Nat) (qt : Sk) => WK.lam (skins qk qt qD) (lift_at qA qk {ONE}) (lift_at qb (Nat.succ qk) {ONE}) qsA qc (qihA qk qt) (qihb (Nat.succ qk) qt))"
    );
    let ih_f = "(qihf : forall (qk : Nat) (qt : Sk), WK (skins qk qt qD) (lift_at qf qk (Nat.succ Nat.zero)) (Sk.arr qd qcc))";
    let ih_ar = "(qiha : forall (qk : Nat) (qt : Sk), WK (skins qk qt qD) (lift_at qa qk (Nat.succ Nat.zero)) qd)";
    let m_app = format!(
        "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf (Sk.arr qd qcc)) (qha : WK qD qa qd) {ih_f} {ih_ar} (qk : Nat) (qt : Sk) => WK.app (skins qk qt qD) (lift_at qf qk {ONE}) (lift_at qa qk {ONE}) qd qcc (qihf qk qt) (qiha qk qt))"
    );
    format!(
        "def wk_lift (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (k : Nat) (t : Sk) : WK (skins k t D) (lift_at e k {ONE}) s := WK.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h k t"
    )
}

/// Weakening at the HEAD of the shape environment. Corpus `wk_lift0`
/// (FWK.lean:142). Definitional at cutoff zero: `skins Nat.zero t D` IS
/// `skcons t D`.
pub(super) fn src_wk_lift0() -> String {
    format!(
        "def wk_lift0 (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (t : Sk) : WK (skcons t D) (lift_at e Nat.zero {ONE}) s := wk_lift D e s h Nat.zero t"
    )
}

/// The `up`-closure of a shape-typed substitution — the ONE place weakening
/// enters substitution, and the reason the two cannot be proved in either order
/// alone. `up sg Nat.zero` is `bvar 0` (so `WK.var` closes it with no
/// transport, because `skcons d Dp Nat.zero` reduces to `d`) and
/// `up sg (Nat.succ n)` is `lift_at (sg n) Nat.zero 1` — which is exactly
/// `wk_lift0`'s conclusion.
pub(super) const SRC_WK_UP: &str = "def wk_up (D : Nat -> Sk) (Dp : Nat -> Sk) (sg : Nat -> KExpr) (d : Sk) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) (i : Nat) : WK (skcons d D) (up sg i) (skcons d Dp i) := Nat.rec (fun (qi : Nat) => WK (skcons d D) (up sg qi) (skcons d Dp qi)) (WK.var (skcons d D) Nat.zero) (fun (qn : Nat) (qih : WK (skcons d D) (up sg qn) (skcons d Dp qn)) => wk_lift0 D (sg qn) (Dp qn) (hsg qn) d) i";

/// **THE SUBSTITUTION OPERATION.** Corpus `wk_psub` (FWK.lean:149): a `WK`
/// derivation transports along any substitution whose every component is
/// shape-typed at the matching slot. Completely transport-free — the `var` case
/// is literally the hypothesis at `i`, which is why the corpus states it with a
/// hypothesis rather than with a cutoff.
pub(super) fn src_wk_psub() -> String {
    let motive = "(fun (qDp : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qDp qe qs) => forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WK qD (qsg qi) (qDp qi)) -> WK qD (psubst qsg qe) qs)";
    let m_var = "(fun (qDp : Nat -> Sk) (qi : Nat) (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qj : Nat), WK qD (qsg qj) (qDp qj)) => qhsg qi)";
    let m_sort = "(fun (qDp : Nat -> Sk) (qn : Level) (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qj : Nat), WK qD (qsg qj) (qDp qj)) => WK.sort qD qn)";
    let ih_a = "(qihA : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WK qD (qsg qi) (qDp qi)) -> WK qD (psubst qsg qA) qsA)";
    let ih_pb = "(qihB : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WK qD (qsg qi) (skcons (domSk qsA) qDp qi)) -> WK qD (psubst qsg qB) qsB)";
    let m_pi = format!(
        "(fun (qDp : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qDp qA qsA) (qhB : WK (skcons (domSk qsA) qDp) qB qsB) {ih_a} {ih_pb} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qi : Nat), WK qD (qsg qi) (qDp qi)) => WK.pi qD (psubst qsg qA) (psubst (up qsg) qB) qsA qsB (qihA qsg qD qhsg) (qihB (up qsg) (skcons (domSk qsA) qD) (wk_up qD qDp qsg (domSk qsA) qhsg)))"
    );
    let ih_lb = "(qihb : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WK qD (qsg qi) (skcons (domSk qsA) qDp qi)) -> WK qD (psubst qsg qb) qc)";
    let m_lam = format!(
        "(fun (qDp : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qDp qA qsA) (qhb : WK (skcons (domSk qsA) qDp) qb qc) {ih_a} {ih_lb} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qi : Nat), WK qD (qsg qi) (qDp qi)) => WK.lam qD (psubst qsg qA) (psubst (up qsg) qb) qsA qc (qihA qsg qD qhsg) (qihb (up qsg) (skcons (domSk qsA) qD) (wk_up qD qDp qsg (domSk qsA) qhsg)))"
    );
    let ih_f = "(qihf : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WK qD (qsg qi) (qDp qi)) -> WK qD (psubst qsg qf) (Sk.arr qd qcc))";
    let ih_ar = "(qiha : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk), (forall (qi : Nat), WK qD (qsg qi) (qDp qi)) -> WK qD (psubst qsg qa) qd)";
    let m_app = format!(
        "(fun (qDp : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qDp qf (Sk.arr qd qcc)) (qha : WK qDp qa qd) {ih_f} {ih_ar} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qi : Nat), WK qD (qsg qi) (qDp qi)) => WK.app qD (psubst qsg qf) (psubst qsg qa) qd qcc (qihf qsg qD qhsg) (qiha qsg qD qhsg))"
    );
    format!(
        "def wk_psub (Dp : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK Dp e s) (sg : Nat -> KExpr) (D : Nat -> Sk) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) : WK D (psubst sg e) s := WK.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} Dp e s h sg D hsg"
    )
}

/// The single-slot substitution `scons a idsubst`, shape-typed. Corpus
/// `wk_inst`'s inner `intro i; cases i` (FWK.lean:175-179), and transport-free:
/// `scons a idsubst Nat.zero` is `a` against `skcons d D Nat.zero` = `d`, and
/// `scons a idsubst (Nat.succ n)` is `bvar n` against `D n`.
pub(super) const SRC_SCONS_TYPED: &str = "def r14_scons_typed (D : Nat -> Sk) (a : KExpr) (d : Sk) (ha : WK D a d) (i : Nat) : WK D (scons a idsubst i) (skcons d D i) := Nat.rec (fun (qi : Nat) => WK D (scons a idsubst qi) (skcons d D qi)) ha (fun (qn : Nat) (qih : WK D (scons a idsubst qn) (skcons d D qn)) => WK.var D qn) i";

/// Substitution for the ZEROTH slot, at the kernel's own `instantiate`. Corpus
/// `wk_inst` (FWK.lean:172). The one transport is `instantiate_eq_psubst`,
/// which is the spec's landed bridge between `instantiate` and `psubst`.
pub(super) const SRC_WK_INST: &str = "def wk_inst (D : Nat -> Sk) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hb : WK (skcons d D) b c) (ha : WK D a d) : WK D (instantiate b a) c := r14_wkCastT D (psubst (scons a idsubst) b) (instantiate b a) c (Eq.symm KExpr (instantiate b a) (psubst (scons a idsubst) b) (instantiate_eq_psubst b a)) (wk_psub (skcons d D) b c hb (scons a idsubst) D (r14_scons_typed D a d ha))";

// ================================================================
// Group A3 — the valuation transports the two operations need.
// Corpus: FInterp.lean `venvLift` (:140) and `venvSub` (:197).
// ================================================================

/// Dropping the inserted slot from a valuation. Corpus `venvLift`
/// (FInterp.lean:140) is `fun i => ρ (if i < c then i else i + 1)` on an
/// UNTYPED valuation; R12's valuations are DEPENDENT (`VEnvD D` is
/// `forall i, VD (D i)`), so the corpus's index formula would need a `VD`-cast
/// at every index. Recursing on the cutoff instead makes every clause type-check
/// definitionally and leaves `r14_venvLift_vcons` — the lemma the binder cases
/// consume — provable with `Eq.refl` in both branches.
pub(super) const SRC_VENV_LIFT_D: &str = "def venvLiftD (c : Nat) (t : Sk) (D : Nat -> Sk) (r : VEnvD (skins c t D)) (i : Nat) : VD (D i) := Nat.rec (fun (qc : Nat) => forall (qt : Sk) (qD : Nat -> Sk), VEnvD (skins qc qt qD) -> VEnvD qD) (fun (qt : Sk) (qD : Nat -> Sk) (qr : VEnvD (skins Nat.zero qt qD)) (qi : Nat) => qr (Nat.succ qi)) (fun (qc : Nat) (qih : forall (qt : Sk) (qD : Nat -> Sk), VEnvD (skins qc qt qD) -> VEnvD qD) (qt : Sk) (qD : Nat -> Sk) (qr : VEnvD (skins (Nat.succ qc) qt qD)) (qi : Nat) => Nat.rec (fun (qj : Nat) => VD (qD qj)) (qr Nat.zero) (fun (qn : Nat) (qz : VD (qD qn)) => qih qt (fun (qj : Nat) => qD (Nat.succ qj)) (fun (qj : Nat) => qr (Nat.succ qj)) qn) qi) c t D r i";

/// The valuation induced by a shape-typed substitution. Corpus `venvSub`
/// (FInterp.lean:197). NO cast is needed here and none is used: `hsg i` is a
/// derivation at exactly `Dp i`, so `sval` lands in `VD (Dp i)` on the nose.
pub(super) const SRC_VENV_SUB_D: &str = "def venvSubD (sg : Nat -> KExpr) (D : Nat -> Sk) (Dp : Nat -> Sk) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) (r : VEnvD D) (i : Nat) : VD (Dp i) := sval D (sg i) (Dp i) (hsg i) r";

// ================================================================
// Group B — the index algebra. Private copies of the subject-reduction
// bundle's `wkpos` tower, which is Full-bundle-only.
// ================================================================

pub(super) const TY_SKINS_ZERO: &str =
    "forall (t : Sk) (D : Nat -> Sk), Eq (Nat -> Sk) (skins Nat.zero t D) (skcons t D)";
pub(super) const VAL_SKINS_ZERO: &str =
    "fun (t : Sk) (D : Nat -> Sk) => Eq.refl (Nat -> Sk) (skcons t D)";

/// **The definitional `skins_succ`.** The corpus proves this with `funext` and
/// four `omega` calls (FWK.lean:42-59); here it is `Eq.refl`, because `skins`
/// recurses on the cutoff. Registered as a GUARD: if a future edit re-spells
/// `skins` with a decidable comparison, this constant stops being `Eq.refl` and
/// every binder case of `wk_lift` silently starts needing a transport.
pub(super) const TY_SKINS_SUCC: &str = "forall (c : Nat) (t : Sk) (s : Sk) (D : Nat -> Sk), Eq (Nat -> Sk) (skins (Nat.succ c) t (skcons s D)) (skcons s (skins c t D))";
pub(super) const VAL_SKINS_SUCC: &str = "fun (c : Nat) (t : Sk) (s : Sk) (D : Nat -> Sk) => Eq.refl (Nat -> Sk) (skcons s (skins c t D))";

pub(super) const TY_WKPOS_ZERO: &str =
    "forall (i : Nat), Eq Nat (r14_wkpos i Nat.zero) (Nat.succ i)";
pub(super) const VAL_WKPOS_ZERO: &str = "fun (i : Nat) => Eq.cong Nat Nat (fun (qn : Nat) => Nat.rec (fun (qm : Nat) => Nat) (Nat.succ i) (fun (qa : Nat) (qb : Nat) => i) qn) (Nat.sub Nat.zero i) Nat.zero (nat_sub_zero_left i)";

pub(super) const TY_WKPOS_REC_SUCC: &str = "forall (j : Nat) (n : Nat), Eq Nat (Nat.rec (fun (qm : Nat) => Nat) (Nat.succ (Nat.succ j)) (fun (qa : Nat) (qb : Nat) => Nat.succ j) n) (Nat.succ (Nat.rec (fun (qm : Nat) => Nat) (Nat.succ j) (fun (qa : Nat) (qb : Nat) => j) n))";
pub(super) const VAL_WKPOS_REC_SUCC: &str = "fun (j : Nat) (n : Nat) => Nat.rec (fun (qm : Nat) => Eq Nat (Nat.rec (fun (qk : Nat) => Nat) (Nat.succ (Nat.succ j)) (fun (qa : Nat) (qb : Nat) => Nat.succ j) qm) (Nat.succ (Nat.rec (fun (qk : Nat) => Nat) (Nat.succ j) (fun (qa : Nat) (qb : Nat) => j) qm))) (Eq.refl Nat (Nat.succ (Nat.succ j))) (fun (qk : Nat) (qih : Eq Nat (Nat.rec (fun (qm2 : Nat) => Nat) (Nat.succ (Nat.succ j)) (fun (qa : Nat) (qb : Nat) => Nat.succ j) qk) (Nat.succ (Nat.rec (fun (qm2 : Nat) => Nat) (Nat.succ j) (fun (qa : Nat) (qb : Nat) => j) qk))) => Eq.refl Nat (Nat.succ j)) n";

pub(super) const TY_WKPOS_SUCC_SUCC: &str = "forall (j : Nat) (c : Nat), Eq Nat (r14_wkpos (Nat.succ j) (Nat.succ c)) (Nat.succ (r14_wkpos j c))";
pub(super) const VAL_WKPOS_SUCC_SUCC: &str = "fun (j : Nat) (c : Nat) => Eq.trans Nat (r14_wkpos (Nat.succ j) (Nat.succ c)) (Nat.rec (fun (qm : Nat) => Nat) (Nat.succ (Nat.succ j)) (fun (qa : Nat) (qb : Nat) => Nat.succ j) (Nat.sub c j)) (Nat.succ (r14_wkpos j c)) (Eq.cong Nat Nat (fun (qn : Nat) => Nat.rec (fun (qm : Nat) => Nat) (Nat.succ (Nat.succ j)) (fun (qa : Nat) (qb : Nat) => Nat.succ j) qn) (Nat.sub (Nat.succ c) (Nat.succ j)) (Nat.sub c j) (nat_sub_succ_succ c j)) (r14_wkpos_rec_succ j (Nat.sub c j))";

pub(super) const TY_LIFT_BVAR_WKPOS_REC: &str = "forall (i : Nat) (n : Nat), Eq KExpr (Nat.rec (fun (qm : Nat) => KExpr) (KExpr.bvar (Nat.add i (Nat.succ Nat.zero))) (fun (qa : Nat) (qb : KExpr) => KExpr.bvar i) n) (KExpr.bvar (Nat.rec (fun (qm : Nat) => Nat) (Nat.succ i) (fun (qa : Nat) (qb : Nat) => i) n))";
pub(super) const VAL_LIFT_BVAR_WKPOS_REC: &str = "fun (i : Nat) (n : Nat) => Nat.rec (fun (qm : Nat) => Eq KExpr (Nat.rec (fun (qk : Nat) => KExpr) (KExpr.bvar (Nat.add i (Nat.succ Nat.zero))) (fun (qa : Nat) (qb : KExpr) => KExpr.bvar i) qm) (KExpr.bvar (Nat.rec (fun (qk : Nat) => Nat) (Nat.succ i) (fun (qa : Nat) (qb : Nat) => i) qm))) (Eq.refl KExpr (KExpr.bvar (Nat.succ i))) (fun (qk : Nat) (qih : Eq KExpr (Nat.rec (fun (qm2 : Nat) => KExpr) (KExpr.bvar (Nat.add i (Nat.succ Nat.zero))) (fun (qa : Nat) (qb : KExpr) => KExpr.bvar i) qk) (KExpr.bvar (Nat.rec (fun (qm2 : Nat) => Nat) (Nat.succ i) (fun (qa : Nat) (qb : Nat) => i) qk))) => Eq.refl KExpr (KExpr.bvar i)) n";

pub(super) fn ty_lift_at_bvar_wkpos() -> String {
    format!("forall (i : Nat) (c : Nat), Eq KExpr (lift_at (KExpr.bvar i) c {ONE}) (KExpr.bvar (r14_wkpos i c))")
}
pub(super) const VAL_LIFT_AT_BVAR_WKPOS: &str =
    "fun (i : Nat) (c : Nat) => r14_lift_bvar_wkpos_rec i (Nat.sub c i)";

/// **The shape-lookup law of insertion.** Corpus `wk_lift`'s `var` arm inline
/// (FWK.lean:112-128). Double `Nat.rec` — on the cutoff, then on the index —
/// with the `succ/succ` corner carried by `r14_wkpos_succ_succ`; the
/// `succ/zero` corner is `Eq.refl` because `Nat.sub (Nat.succ c) Nat.zero`
/// reduces to `Nat.succ c` and `r14_wkpos` then takes its "below the cut"
/// branch definitionally.
pub(super) const TY_SKINS_IDX: &str = "forall (c : Nat) (i : Nat) (t : Sk) (D : Nat -> Sk), Eq Sk (skins c t D (r14_wkpos i c)) (D i)";
pub(super) fn val_skins_idx() -> String {
    let motive = "(fun (qc : Nat) => forall (qi : Nat) (qD : Nat -> Sk), Eq Sk (skins qc t qD (r14_wkpos qi qc)) (qD qi))";
    let zero = "(fun (qi : Nat) (qD : Nat -> Sk) => Eq.cong Nat Sk (fun (qz : Nat) => skcons t qD qz) (r14_wkpos qi Nat.zero) (Nat.succ qi) (r14_wkpos_zero qi))";
    let inner_motive =
        "(fun (qj : Nat) => Eq Sk (skins (Nat.succ qc) t qD (r14_wkpos qj (Nat.succ qc))) (qD qj))";
    let inner_zero = "(Eq.refl Sk (qD Nat.zero))";
    let inner_succ = "(fun (qn : Nat) (qihn : Eq Sk (skins (Nat.succ qc) t qD (r14_wkpos qn (Nat.succ qc))) (qD qn)) => Eq.trans Sk (skins (Nat.succ qc) t qD (r14_wkpos (Nat.succ qn) (Nat.succ qc))) (skins (Nat.succ qc) t qD (Nat.succ (r14_wkpos qn qc))) (qD (Nat.succ qn)) (Eq.cong Nat Sk (fun (qz : Nat) => skins (Nat.succ qc) t qD qz) (r14_wkpos (Nat.succ qn) (Nat.succ qc)) (Nat.succ (r14_wkpos qn qc)) (r14_wkpos_succ_succ qn qc)) (qih qn (fun (qj : Nat) => qD (Nat.succ qj))))";
    let succ = format!(
        "(fun (qc : Nat) (qih : forall (qi : Nat) (qD : Nat -> Sk), Eq Sk (skins qc t qD (r14_wkpos qi qc)) (qD qi)) (qi : Nat) (qD : Nat -> Sk) => Nat.rec {inner_motive} {inner_zero} {inner_succ} qi)"
    );
    format!(
        "fun (c : Nat) (i : Nat) (t : Sk) (D : Nat -> Sk) => Nat.rec {motive} {zero} {succ} c i D"
    )
}

// ================================================================
// Group C — the three generic transport lemmas.
//
// `sval` recurses on the DERIVATION, so a derivation that has been transported
// along an `Eq` does not reduce. These three peel the transports back off. All
// three are based `Eq.rec` (Martin-Lof J) with a PROOF-DEPENDENT motive, which
// the spec's `Eq.rec` supports (`foundation_types.rs:213` uses exactly that
// shape for `Eq.symm`).
// ================================================================

pub(super) const TY_SVAL_CAST_TERM: &str = "forall (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (s : Sk) (heq : Eq KExpr e1 e2) (h : WK D e1 s) (r : VEnvD D), Eq (VD s) (sval D e2 s (r14_wkCastT D e1 e2 s heq h) r) (sval D e1 s h r)";
pub(super) const VAL_SVAL_CAST_TERM: &str = "fun (D : Nat -> Sk) (e1 : KExpr) (e2 : KExpr) (s : Sk) (heq : Eq KExpr e1 e2) (h : WK D e1 s) (r : VEnvD D) => Eq.rec KExpr e1 (fun (qz : KExpr) (qp : Eq KExpr e1 qz) => Eq (VD s) (sval D qz s (r14_wkCastT D e1 qz s qp h) r) (sval D e1 s h r)) (Eq.refl (VD s) (sval D e1 s h r)) e2 heq";

pub(super) fn ty_sval_cast_shape() -> String {
    format!("forall (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (s2 : Sk) (heq : Eq Sk s1 s2) (h : WK D e s1) (r : VEnvD D), Eq (VD s2) (sval D e s2 (r14_wkCastS D e s1 s2 heq h) r) ({VDCAST} s1 s2 heq (sval D e s1 h r))")
}
pub(super) fn val_sval_cast_shape() -> String {
    format!("fun (D : Nat -> Sk) (e : KExpr) (s1 : Sk) (s2 : Sk) (heq : Eq Sk s1 s2) (h : WK D e s1) (r : VEnvD D) => Eq.rec Sk s1 (fun (qs2 : Sk) (qp : Eq Sk s1 qs2) => Eq (VD qs2) (sval D e qs2 (r14_wkCastS D e s1 qs2 qp h) r) ({VDCAST} s1 qs2 qp (sval D e s1 h r))) (Eq.refl (VD s1) (sval D e s1 h r)) s2 heq")
}

/// **THE K-LIKE MEASUREMENT.** A `VD`-cast along a STUCK proof of a REFLEXIVE
/// shape equality is the value itself, by `Eq.refl`.
///
/// This is the one constant in the rung whose acceptance is a fact about the
/// KERNEL rather than about the proof: `Eq.rec` reduces here only because `Eq`
/// is K-like (`env/inductive_recursor.rs:1036` — Prop, one constructor, zero
/// fields after parameter promotion; the comment names `Eq` and says it enables
/// UIP), so the kernel replaces the stuck proof by `Eq.refl` and fires iota.
/// Proof irrelevance cannot do this: irrelevance identifies two PROOFS, it does
/// not reduce a recursor applied to one. Registered here, where the appeal to K
/// is visible, instead of buried inside a bigger proof.
pub(super) const TY_VDCAST_REFL: &str =
    "forall (s1 : Sk) (p : Eq Sk s1 s1) (v : VD s1), Eq (VD s1) (r14_vdCast s1 s1 p v) v";
pub(super) const VAL_VDCAST_REFL: &str =
    "fun (s1 : Sk) (p : Eq Sk s1 s1) (v : VD s1) => Eq.refl (VD s1) v";

/// UIP for the cast: two `VD`-casts along two proofs of the SAME shape equality
/// agree. Based `Eq.rec` on the first proof reduces the goal to the reflexive
/// case, where `r14_vdCast_refl` closes it.
///
/// **Why this exists as a separate constant, measured 2026-08-27.** The step is
/// also closable by `Eq.refl` — the KERNEL applies proof irrelevance, and
/// `probe_cast_irrel_refl` registers cleanly through `add_recursive_def`
/// (`test_candmodel_r14_cast_irrelevance_needs_a_standalone_constant` asserts
/// that). But written INLINE as the base minor of `r14_cast_idx`'s `Eq.rec`,
/// the identical step was REFUSED: the ELABORATOR's unifier compared the two
/// proof binders as free variables and reported `fvar mismatch`. So an
/// irrelevance step has to be a standalone, kernel-checked constant that the
/// elaborated proof term APPLIES; it cannot sit inline inside a recursor minor.
/// That is a position-dependence in the elaborator, not a fact about the
/// theorem, and it is transferable to every later rung.
pub(super) const TY_VDCAST_IRREL: &str = "forall (s1 : Sk) (s2 : Sk) (p : Eq Sk s1 s2) (q : Eq Sk s1 s2) (v : VD s1), Eq (VD s2) (r14_vdCast s1 s2 p v) (r14_vdCast s1 s2 q v)";
pub(super) const VAL_VDCAST_IRREL: &str = "fun (s1 : Sk) (s2 : Sk) (p : Eq Sk s1 s2) (q : Eq Sk s1 s2) (v : VD s1) => Eq.rec Sk s1 (fun (qs2 : Sk) (qp : Eq Sk s1 qs2) => forall (qq : Eq Sk s1 qs2), Eq (VD qs2) (r14_vdCast s1 qs2 qp v) (r14_vdCast s1 qs2 qq v)) (fun (qq : Eq Sk s1 s1) => Eq.symm (VD s1) (r14_vdCast s1 s1 qq v) v (r14_vdCast_refl s1 qq v)) s2 p q";

/// Two `VD`-casts of the SAME valuation at two PROVABLY EQUAL indices agree.
/// The base case is where proof irrelevance does the work: at `j2 := j1` the
/// two casts differ only in their `Eq` proofs, and the kernel holds any two
/// proofs of a `Prop` definitionally equal, so `Eq.refl` closes it.
pub(super) fn ty_cast_idx() -> String {
    format!("forall (E : Nat -> Sk) (s : Sk) (j1 : Nat) (j2 : Nat) (hj : Eq Nat j1 j2) (r : VEnvD E) (p1 : Eq Sk (E j1) s) (p2 : Eq Sk (E j2) s), Eq (VD s) ({VDCAST} (E j1) s p1 (r j1)) ({VDCAST} (E j2) s p2 (r j2))")
}
pub(super) fn val_cast_idx() -> String {
    format!("fun (E : Nat -> Sk) (s : Sk) (j1 : Nat) (j2 : Nat) (hj : Eq Nat j1 j2) (r : VEnvD E) (p1 : Eq Sk (E j1) s) (p2 : Eq Sk (E j2) s) => Eq.rec Nat j1 (fun (qj : Nat) (qh : Eq Nat j1 qj) => forall (qp : Eq Sk (E qj) s), Eq (VD s) ({VDCAST} (E j1) s p1 (r j1)) ({VDCAST} (E qj) s qp (r qj))) (fun (qp : Eq Sk (E j1) s) => r14_vdCast_irrel (E j1) s p1 qp (r j1)) j2 hj p2")
}

// ================================================================
// Group D — the valuation laws.
// ================================================================

/// The recursive `venvLiftD` agrees with the corpus's index formula, read as a
/// cast. This is the bridge between the definition that makes the BINDER cases
/// definitional and the form the VAR case produces.
pub(super) fn ty_venv_lift_at() -> String {
    format!("forall (c : Nat) (t : Sk) (D : Nat -> Sk) (r : VEnvD (skins c t D)) (i : Nat), Eq (VD (D i)) (venvLiftD c t D r i) ({VDCAST} (skins c t D (r14_wkpos i c)) (D i) (r14_skins_idx c i t D) (r (r14_wkpos i c)))")
}
pub(super) fn val_venv_lift_at() -> String {
    let motive = format!("(fun (qc : Nat) => forall (qt : Sk) (qD : Nat -> Sk) (qr : VEnvD (skins qc qt qD)) (qi : Nat), Eq (VD (qD qi)) (venvLiftD qc qt qD qr qi) ({VDCAST} (skins qc qt qD (r14_wkpos qi qc)) (qD qi) (r14_skins_idx qc qi qt qD) (qr (r14_wkpos qi qc))))");
    let zero = format!("(fun (qt : Sk) (qD : Nat -> Sk) (qr : VEnvD (skins Nat.zero qt qD)) (qi : Nat) => Eq.symm (VD (qD qi)) ({VDCAST} (skins Nat.zero qt qD (r14_wkpos qi Nat.zero)) (qD qi) (r14_skins_idx Nat.zero qi qt qD) (qr (r14_wkpos qi Nat.zero))) (qr (Nat.succ qi)) (r14_cast_idx (skins Nat.zero qt qD) (qD qi) (r14_wkpos qi Nat.zero) (Nat.succ qi) (r14_wkpos_zero qi) qr (r14_skins_idx Nat.zero qi qt qD) (Eq.refl Sk (qD qi))))");
    let inner_motive = format!("(fun (qj : Nat) => Eq (VD (qD qj)) (venvLiftD (Nat.succ qc) qt qD qr qj) ({VDCAST} (skins (Nat.succ qc) qt qD (r14_wkpos qj (Nat.succ qc))) (qD qj) (r14_skins_idx (Nat.succ qc) qj qt qD) (qr (r14_wkpos qj (Nat.succ qc)))))");
    let inner_zero = "(Eq.refl (VD (qD Nat.zero)) (qr Nat.zero))";
    // The succ/succ corner: the outer IH at the shifted environment, then
    // r14_cast_idx to move the index from wkpos (succ n) (succ c) to
    // succ (wkpos n c) -- after which both casts are syntactically identical.
    let ih_at =
        "(qih qt (fun (qj : Nat) => qD (Nat.succ qj)) (fun (qj : Nat) => qr (Nat.succ qj)) qn)"
            .to_string();
    let mid = format!("({VDCAST} (skins qc qt (fun (qj : Nat) => qD (Nat.succ qj)) (r14_wkpos qn qc)) (qD (Nat.succ qn)) (r14_skins_idx qc qn qt (fun (qj : Nat) => qD (Nat.succ qj))) (qr (Nat.succ (r14_wkpos qn qc))))");
    let tgt = format!("({VDCAST} (skins (Nat.succ qc) qt qD (r14_wkpos (Nat.succ qn) (Nat.succ qc))) (qD (Nat.succ qn)) (r14_skins_idx (Nat.succ qc) (Nat.succ qn) qt qD) (qr (r14_wkpos (Nat.succ qn) (Nat.succ qc))))");
    let bridge = "(r14_cast_idx (skins (Nat.succ qc) qt qD) (qD (Nat.succ qn)) (r14_wkpos (Nat.succ qn) (Nat.succ qc)) (Nat.succ (r14_wkpos qn qc)) (r14_wkpos_succ_succ qn qc) qr (r14_skins_idx (Nat.succ qc) (Nat.succ qn) qt qD) (r14_skins_idx qc qn qt (fun (qj : Nat) => qD (Nat.succ qj))))".to_string();
    let inner_succ = format!("(fun (qn : Nat) (qz : Eq (VD (qD qn)) (venvLiftD (Nat.succ qc) qt qD qr qn) ({VDCAST} (skins (Nat.succ qc) qt qD (r14_wkpos qn (Nat.succ qc))) (qD qn) (r14_skins_idx (Nat.succ qc) qn qt qD) (qr (r14_wkpos qn (Nat.succ qc))))) => Eq.trans (VD (qD (Nat.succ qn))) (venvLiftD (Nat.succ qc) qt qD qr (Nat.succ qn)) {mid} {tgt} {ih_at} (Eq.symm (VD (qD (Nat.succ qn))) {tgt} {mid} {bridge}))");
    let succ = format!("(fun (qc : Nat) (qih : forall (qt : Sk) (qD : Nat -> Sk) (qr : VEnvD (skins qc qt qD)) (qi : Nat), Eq (VD (qD qi)) (venvLiftD qc qt qD qr qi) ({VDCAST} (skins qc qt qD (r14_wkpos qi qc)) (qD qi) (r14_skins_idx qc qi qt qD) (qr (r14_wkpos qi qc)))) (qt : Sk) (qD : Nat -> Sk) (qr : VEnvD (skins (Nat.succ qc) qt qD)) (qi : Nat) => Nat.rec {inner_motive} {inner_zero} {inner_succ} qi)");
    format!("fun (c : Nat) (t : Sk) (D : Nat -> Sk) (r : VEnvD (skins c t D)) (i : Nat) => Nat.rec {motive} {zero} {succ} c t D r i")
}

/// **The value of a weakened variable.** The composite of the two cast lemmas
/// and `r14_venvLift_at`; it is the whole `var` case of `r14_val_lift`.
pub(super) fn ty_sval_wk_lift_var() -> String {
    format!("forall (c : Nat) (i : Nat) (t : Sk) (D : Nat -> Sk) (r : VEnvD (skins c t D)), Eq (VD (D i)) (sval (skins c t D) (lift_at (KExpr.bvar i) c {ONE}) (D i) (r14_wk_lift_var c i t D) r) (venvLiftD c t D r i)")
}
pub(super) fn val_sval_wk_lift_var() -> String {
    let shape_cast = "(r14_wkCastS (skins c t D) (KExpr.bvar (r14_wkpos i c)) (skins c t D (r14_wkpos i c)) (D i) (r14_skins_idx c i t D) (WK.var (skins c t D) (r14_wkpos i c)))";
    let a = format!(
        "(sval (skins c t D) (lift_at (KExpr.bvar i) c {ONE}) (D i) (r14_wk_lift_var c i t D) r)"
    );
    let b = format!("(sval (skins c t D) (KExpr.bvar (r14_wkpos i c)) (D i) {shape_cast} r)");
    let cc = format!("({VDCAST} (skins c t D (r14_wkpos i c)) (D i) (r14_skins_idx c i t D) (r (r14_wkpos i c)))");
    let step1 = format!("(r14_sval_cast_term (skins c t D) (KExpr.bvar (r14_wkpos i c)) (lift_at (KExpr.bvar i) c {ONE}) (D i) (Eq.symm KExpr (lift_at (KExpr.bvar i) c {ONE}) (KExpr.bvar (r14_wkpos i c)) (r14_lift_at_bvar_wkpos i c)) {shape_cast} r)");
    let step2 = "(r14_sval_cast_shape (skins c t D) (KExpr.bvar (r14_wkpos i c)) (skins c t D (r14_wkpos i c)) (D i) (r14_skins_idx c i t D) (WK.var (skins c t D) (r14_wkpos i c)) r)";
    let step3 = "(Eq.symm (VD (D i)) (venvLiftD c t D r i) CCC (r14_venvLift_at c t D r i))";
    let step3 = step3.replace("CCC", &cc);
    format!("fun (c : Nat) (i : Nat) (t : Sk) (D : Nat -> Sk) (r : VEnvD (skins c t D)) => Eq.trans (VD (D i)) {a} {cc} (venvLiftD c t D r i) (Eq.trans (VD (D i)) {a} {b} {cc} {step1} {step2}) {step3}")
}

/// **Weakening commutes with valuation extension.** Corpus `venvLift_vcons`
/// (FInterp.lean:142). Both branches are `Eq.refl` — the point of defining
/// `venvLiftD` by recursion on the cutoff — and `r13_venvD_funext` (R13) turns
/// the pointwise statement into the equality of the two VALUATIONS, which is
/// what `Eq.cong` needs downstream. This is the first place the ladder cashes
/// R13's dependent funext for something other than a congruence.
pub(super) const TY_VENV_LIFT_VCONS: &str = "forall (c : Nat) (t : Sk) (d : Sk) (D : Nat -> Sk) (v : VD d) (r : VEnvD (skins c t D)), Eq (VEnvD (skcons d D)) (venvLiftD (Nat.succ c) t (skcons d D) (vconsD d (skins c t D) v r)) (vconsD d D v (venvLiftD c t D r))";
pub(super) const VAL_VENV_LIFT_VCONS: &str = "fun (c : Nat) (t : Sk) (d : Sk) (D : Nat -> Sk) (v : VD d) (r : VEnvD (skins c t D)) => r13_venvD_funext (skcons d D) (venvLiftD (Nat.succ c) t (skcons d D) (vconsD d (skins c t D) v r)) (vconsD d D v (venvLiftD c t D r)) (fun (i : Nat) => Nat.rec (fun (qi : Nat) => Eq (VD (skcons d D qi)) (venvLiftD (Nat.succ c) t (skcons d D) (vconsD d (skins c t D) v r) qi) (vconsD d D v (venvLiftD c t D r) qi)) (Eq.refl (VD d) v) (fun (qn : Nat) (qih : Eq (VD (skcons d D qn)) (venvLiftD (Nat.succ c) t (skcons d D) (vconsD d (skins c t D) v r) qn) (vconsD d D v (venvLiftD c t D r) qn)) => Eq.refl (VD (D qn)) (venvLiftD c t D r qn)) i)";

/// **Substitution commutes with valuation extension.** Corpus `venvSub_up`
/// (FInterp.lean:199). The `succ` branch is exactly `r14_val_lift0` — this is
/// where the semantic weakening lemma is CONSUMED, and why `val_psub` cannot be
/// proved before `val_lift`.
pub(super) const TY_VENV_SUB_UP: &str = "forall (D : Nat -> Sk) (Dp : Nat -> Sk) (sg : Nat -> KExpr) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) (d : Sk) (v : VD d) (r : VEnvD D), Eq (VEnvD (skcons d Dp)) (venvSubD (up sg) (skcons d D) (skcons d Dp) (wk_up D Dp sg d hsg) (vconsD d D v r)) (vconsD d Dp v (venvSubD sg D Dp hsg r))";
pub(super) const VAL_VENV_SUB_UP: &str = "fun (D : Nat -> Sk) (Dp : Nat -> Sk) (sg : Nat -> KExpr) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) (d : Sk) (v : VD d) (r : VEnvD D) => r13_venvD_funext (skcons d Dp) (venvSubD (up sg) (skcons d D) (skcons d Dp) (wk_up D Dp sg d hsg) (vconsD d D v r)) (vconsD d Dp v (venvSubD sg D Dp hsg r)) (fun (i : Nat) => Nat.rec (fun (qi : Nat) => Eq (VD (skcons d Dp qi)) (venvSubD (up sg) (skcons d D) (skcons d Dp) (wk_up D Dp sg d hsg) (vconsD d D v r) qi) (vconsD d Dp v (venvSubD sg D Dp hsg r) qi)) (Eq.refl (VD d) v) (fun (qn : Nat) (qih : Eq (VD (skcons d Dp qn)) (venvSubD (up sg) (skcons d D) (skcons d Dp) (wk_up D Dp sg d hsg) (vconsD d D v r) qn) (vconsD d Dp v (venvSubD sg D Dp hsg r) qn)) => r14_val_lift0 D (sg qn) (Dp qn) (hsg qn) d v r) i)";

/// Corpus `val_inst`'s valuation half (FInterp.lean:237-243): the valuation
/// induced by `scons a idsubst` IS the extension by `a`'s value. Both branches
/// `Eq.refl`.
pub(super) const TY_VENV_SUB_SCONS: &str = "forall (D : Nat -> Sk) (a : KExpr) (d : Sk) (ha : WK D a d) (r : VEnvD D), Eq (VEnvD (skcons d D)) (venvSubD (scons a idsubst) D (skcons d D) (r14_scons_typed D a d ha) r) (vconsD d D (sval D a d ha r) r)";
pub(super) const VAL_VENV_SUB_SCONS: &str = "fun (D : Nat -> Sk) (a : KExpr) (d : Sk) (ha : WK D a d) (r : VEnvD D) => r13_venvD_funext (skcons d D) (venvSubD (scons a idsubst) D (skcons d D) (r14_scons_typed D a d ha) r) (vconsD d D (sval D a d ha r) r) (fun (i : Nat) => Nat.rec (fun (qi : Nat) => Eq (VD (skcons d D qi)) (venvSubD (scons a idsubst) D (skcons d D) (r14_scons_typed D a d ha) r qi) (vconsD d D (sval D a d ha r) r qi)) (Eq.refl (VD d) (sval D a d ha r)) (fun (qn : Nat) (qih : Eq (VD (skcons d D qn)) (venvSubD (scons a idsubst) D (skcons d D) (r14_scons_typed D a d ha) r qn) (vconsD d D (sval D a d ha r) r qn)) => Eq.refl (VD (D qn)) (r qn)) i)";

// ================================================================
// Group E — the two congruence combinators the binder/app cases consume.
// ================================================================

/// Semantic application is a congruence in both slots. `VD (Sk.arr d c)`
/// iota-reduces to `VD d -> VD c`, which is what lets `qF x` typecheck.
pub(super) const TY_VAPPLY_CONGR: &str = "forall (d : Sk) (c : Sk) (F : VD (Sk.arr d c)) (F2 : VD (Sk.arr d c)) (x : VD d) (x2 : VD d), Eq (VD (Sk.arr d c)) F F2 -> Eq (VD d) x x2 -> Eq (VD c) (F x) (F2 x2)";
pub(super) const VAL_VAPPLY_CONGR: &str = "fun (d : Sk) (c : Sk) (F : VD (Sk.arr d c)) (F2 : VD (Sk.arr d c)) (x : VD d) (x2 : VD d) (hF : Eq (VD (Sk.arr d c)) F F2) (hx : Eq (VD d) x x2) => Eq.trans (VD c) (F x) (F2 x) (F2 x2) (Eq.cong (VD (Sk.arr d c)) (VD c) (fun (qF : VD (Sk.arr d c)) => qF x) F F2 hF) (Eq.cong (VD d) (VD c) (fun (qx : VD d) => F2 qx) x x2 hx)";

/// The Pi clause of `sval` is a congruence in the domain value and in the
/// codomain value. This is the `piA`/`piB` pair of the corpus's `val_step`
/// (FWK.lean:295-307) as ONE combinator, and unlike the corpus's `piVal_congr`
/// it needs no `propext`: R13 already showed the congruence is an `Eq.cong` in
/// the value, never a biimplication between two `Type`s.
pub(super) const TY_SVAL_PI_CONGR: &str = "forall (sA : Sk) (sB : Sk) (vA : VD sA) (vA2 : VD sA) (vB : VD sB) (vB2 : VD sB), Eq (VD sA) vA vA2 -> Eq (VD sB) vB vB2 -> Eq (VD (piShape sA sB)) (mkTyD sA sB (PiSet (vcarD sA vA) (fun (qa : KExpr) => vcarD sB vB))) (mkTyD sA sB (PiSet (vcarD sA vA2) (fun (qa : KExpr) => vcarD sB vB2)))";
pub(super) const VAL_SVAL_PI_CONGR: &str = "fun (sA : Sk) (sB : Sk) (vA : VD sA) (vA2 : VD sA) (vB : VD sB) (vB2 : VD sB) (hA : Eq (VD sA) vA vA2) (hB : Eq (VD sB) vB vB2) => Eq.trans (VD (piShape sA sB)) (mkTyD sA sB (PiSet (vcarD sA vA) (fun (qa : KExpr) => vcarD sB vB))) (mkTyD sA sB (PiSet (vcarD sA vA2) (fun (qa : KExpr) => vcarD sB vB))) (mkTyD sA sB (PiSet (vcarD sA vA2) (fun (qa : KExpr) => vcarD sB vB2))) (Eq.cong (VD sA) (VD (piShape sA sB)) (fun (qv : VD sA) => mkTyD sA sB (PiSet (vcarD sA qv) (fun (qa : KExpr) => vcarD sB vB))) vA vA2 hA) (Eq.cong (VD sB) (VD (piShape sA sB)) (fun (qw : VD sB) => mkTyD sA sB (PiSet (vcarD sA vA2) (fun (qa : KExpr) => vcarD sB qw))) vB vB2 hB)";

// ================================================================
// Group F — the two SEMANTIC lemmas the operations exist for.
// Corpus: FInterp.lean `val_lift` (:159) and `val_psub` (:209).
// ================================================================

/// Shared spellings of the objects the `val_lift` minors mention. Kept as
/// functions so every occurrence is byte-identical: a one-character divergence
/// between a minor's IH type and the motive's instantiation costs a whole
/// elaboration cycle.
fn vl_ek() -> String {
    "(skins qk qt qD)".to_string()
}
fn vl_db() -> String {
    "(skcons (domSk qsA) qD)".to_string()
}
fn vl_ekb() -> String {
    "(skcons (domSk qsA) (skins qk qt qD))".to_string()
}
fn vl_rl() -> String {
    "(venvLiftD qk qt qD qr)".to_string()
}

/// **`val_lift` — THE SEMANTIC WEAKENING LEMMA.** Corpus `val_lift`
/// (FInterp.lean:159), which is an induction on the TERM because the corpus's
/// `val` recurses on the term. Here `sval` recurses on the DERIVATION, so this
/// is an induction on the derivation and its subject is `wk_lift` — which is
/// exactly why the operation had to exist before the lemma could be stated.
pub(super) fn ty_val_lift() -> String {
    format!("forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (k : Nat) (t : Sk) (r : VEnvD (skins k t D)), Eq (VD s) (sval (skins k t D) (lift_at e k {ONE}) s (wk_lift D e s h k t) r) (sval D e s h (venvLiftD k t D r))")
}

#[allow(clippy::too_many_lines)]
pub(super) fn val_val_lift() -> String {
    let ek = vl_ek();
    let db = vl_db();
    let ekb = vl_ekb();
    let rl = vl_rl();
    let motive = format!("(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => forall (qk : Nat) (qt : Sk) (qr : VEnvD (skins qk qt qD)), Eq (VD qs) (sval {ek} (lift_at qe qk {ONE}) qs (wk_lift qD qe qs qh qk qt) qr) (sval qD qe qs qh {rl}))");
    let m_var = format!("(fun (qD : Nat -> Sk) (qi : Nat) (qk : Nat) (qt : Sk) (qr : VEnvD {ek}) => r14_sval_wk_lift_var qk qi qt qD qr)");
    let m_sort = format!("(fun (qD : Nat -> Sk) (qn : Level) (qk : Nat) (qt : Sk) (qr : VEnvD {ek}) => Eq.refl (VD (Sk.kd Sk.ty)) (fun (qe2 : KExpr) => whnf_acc qe2))");

    let ih_a = format!("(qihA : forall (qk : Nat) (qt : Sk) (qr : VEnvD {ek}), Eq (VD qsA) (sval {ek} (lift_at qA qk {ONE}) qsA (wk_lift qD qA qsA qhA qk qt) qr) (sval qD qA qsA qhA {rl}))");

    // --- pi ---
    let ih_pb = format!("(qihB : forall (qk : Nat) (qt : Sk) (qr : VEnvD (skins qk qt {db})), Eq (VD qsB) (sval (skins qk qt {db}) (lift_at qB qk {ONE}) qsB (wk_lift {db} qB qsB qhB qk qt) qr) (sval {db} qB qsB qhB (venvLiftD qk qt {db} qr)))");
    let jb = "(junkD (domSk qsA))";
    let yb = format!("(vconsD (domSk qsA) {ek} {jb} qr)");
    let p_va = format!("(sval {ek} (lift_at qA qk {ONE}) qsA (wk_lift qD qA qsA qhA qk qt) qr)");
    let p_va2 = format!("(sval qD qA qsA qhA {rl})");
    let p_vb = format!("(sval {ekb} (lift_at qB (Nat.succ qk) {ONE}) qsB (wk_lift {db} qB qsB qhB (Nat.succ qk) qt) {yb})");
    let p_mid = format!("(sval {db} qB qsB qhB (venvLiftD (Nat.succ qk) qt {db} {yb}))");
    let p_vb2 = format!("(sval {db} qB qsB qhB (vconsD (domSk qsA) qD {jb} {rl}))");
    let p_cong = format!("(Eq.cong (VEnvD {db}) (VD qsB) (fun (qrr : VEnvD {db}) => sval {db} qB qsB qhB qrr) (venvLiftD (Nat.succ qk) qt {db} {yb}) (vconsD (domSk qsA) qD {jb} {rl}) (r14_venvLift_vcons qk qt (domSk qsA) qD {jb} qr))");
    let p_hb =
        format!("(Eq.trans (VD qsB) {p_vb} {p_mid} {p_vb2} (qihB (Nat.succ qk) qt {yb}) {p_cong})");
    let m_pi = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK {db} qB qsB) {ih_a} {ih_pb} (qk : Nat) (qt : Sk) (qr : VEnvD {ek}) => r14_sval_pi_congr qsA qsB {p_va} {p_va2} {p_vb} {p_vb2} (qihA qk qt qr) {p_hb})");

    // --- lam ---
    let ih_lb = format!("(qihb : forall (qk : Nat) (qt : Sk) (qr : VEnvD (skins qk qt {db})), Eq (VD qc) (sval (skins qk qt {db}) (lift_at qb qk {ONE}) qc (wk_lift {db} qb qc qhb qk qt) qr) (sval {db} qb qc qhb (venvLiftD qk qt {db} qr)))");
    let l_f = format!("(sval {ek} (lift_at (KExpr.lam qA qb) qk {ONE}) (Sk.arr (domSk qsA) qc) (wk_lift qD (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc) (WK.lam qD qA qb qsA qc qhA qhb) qk qt) qr)");
    let l_g = format!(
        "(sval qD (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc) (WK.lam qD qA qb qsA qc qhA qhb) {rl})"
    );
    let yx = format!("(vconsD (domSk qsA) {ek} qx qr)");
    let l_x1 = format!("(sval {ekb} (lift_at qb (Nat.succ qk) {ONE}) qc (wk_lift {db} qb qc qhb (Nat.succ qk) qt) {yx})");
    let l_x2 = format!("(sval {db} qb qc qhb (venvLiftD (Nat.succ qk) qt {db} {yx}))");
    let l_x3 = format!("(sval {db} qb qc qhb (vconsD (domSk qsA) qD qx {rl}))");
    let l_cong = format!("(Eq.cong (VEnvD {db}) (VD qc) (fun (qrr : VEnvD {db}) => sval {db} qb qc qhb qrr) (venvLiftD (Nat.succ qk) qt {db} {yx}) (vconsD (domSk qsA) qD qx {rl}) (r14_venvLift_vcons qk qt (domSk qsA) qD qx qr))");
    let l_point = format!("(fun (qx : VD (domSk qsA)) => Eq.trans (VD qc) {l_x1} {l_x2} {l_x3} (qihb (Nat.succ qk) qt {yx}) {l_cong})");
    let m_lam = format!("(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK {db} qb qc) {ih_a} {ih_lb} (qk : Nat) (qt : Sk) (qr : VEnvD {ek}) => r13_vd_arr_funext (domSk qsA) qc {l_f} {l_g} {l_point})");

    // --- app ---
    let ih_f = format!("(qihf : forall (qk : Nat) (qt : Sk) (qr : VEnvD {ek}), Eq (VD (Sk.arr qd qcc)) (sval {ek} (lift_at qf qk {ONE}) (Sk.arr qd qcc) (wk_lift qD qf (Sk.arr qd qcc) qhf qk qt) qr) (sval qD qf (Sk.arr qd qcc) qhf {rl}))");
    let ih_ar = format!("(qiha : forall (qk : Nat) (qt : Sk) (qr : VEnvD {ek}), Eq (VD qd) (sval {ek} (lift_at qa qk {ONE}) qd (wk_lift qD qa qd qha qk qt) qr) (sval qD qa qd qha {rl}))");
    let a_f = format!("(sval {ek} (lift_at qf qk {ONE}) (Sk.arr qd qcc) (wk_lift qD qf (Sk.arr qd qcc) qhf qk qt) qr)");
    let a_f2 = format!("(sval qD qf (Sk.arr qd qcc) qhf {rl})");
    let a_x = format!("(sval {ek} (lift_at qa qk {ONE}) qd (wk_lift qD qa qd qha qk qt) qr)");
    let a_x2 = format!("(sval qD qa qd qha {rl})");
    let m_app = format!("(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qD qf (Sk.arr qd qcc)) (qha : WK qD qa qd) {ih_f} {ih_ar} (qk : Nat) (qt : Sk) (qr : VEnvD {ek}) => r14_vapply_congr qd qcc {a_f} {a_f2} {a_x} {a_x2} (qihf qk qt qr) (qiha qk qt qr))");

    format!("fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) => WK.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h")
}

/// `val_lift` at the context HEAD. Corpus `val_lift0` (FInterp.lean:191).
/// Definitional on both sides at cutoff zero: `skins Nat.zero t D` is
/// `skcons t D`, and `venvLiftD Nat.zero t D (vconsD t D v r)` is `r` (one
/// `Nat.rec` iota, then function eta).
pub(super) fn ty_val_lift0() -> String {
    format!("forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (t : Sk) (v : VD t) (r : VEnvD D), Eq (VD s) (sval (skcons t D) (lift_at e Nat.zero {ONE}) s (wk_lift0 D e s h t) (vconsD t D v r)) (sval D e s h r)")
}
pub(super) const VAL_VAL_LIFT0: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (t : Sk) (v : VD t) (r : VEnvD D) => r14_val_lift D e s h Nat.zero t (vconsD t D v r)";

/// **`val_psub` — THE SEMANTIC SUBSTITUTION LEMMA.** Corpus `val_psub`
/// (FInterp.lean:209). Its `var` case is `Eq.refl`, which is the payoff of
/// stating `wk_psub` with a hypothesis rather than with a cutoff: the
/// derivation the operation produces at a variable IS the hypothesis, so the
/// interpretation is the induced valuation on the nose.
pub(super) const TY_VAL_PSUB: &str = "forall (Dp : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK Dp e s) (sg : Nat -> KExpr) (D : Nat -> Sk) (hsg : forall (qi : Nat), WK D (sg qi) (Dp qi)) (r : VEnvD D), Eq (VD s) (sval D (psubst sg e) s (wk_psub Dp e s h sg D hsg) r) (sval Dp e s h (venvSubD sg D Dp hsg r))";

#[allow(clippy::too_many_lines)]
pub(super) fn val_val_psub() -> String {
    let hyp = "(forall (qi : Nat), WK qD (qsg qi) (qDp qi))";
    let subd = "(skcons (domSk qsA) qD)";
    let subdp = "(skcons (domSk qsA) qDp)";
    let wu = "(wk_up qD qDp qsg (domSk qsA) qhsg)";
    let rs = "(venvSubD qsg qD qDp qhsg qr)";
    let jb = "(junkD (domSk qsA))";

    let motive = "(fun (qDp : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qDp qe qs) => forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : forall (qi : Nat), WK qD (qsg qi) (qDp qi)) (qr : VEnvD qD), Eq (VD qs) (sval qD (psubst qsg qe) qs (wk_psub qDp qe qs qh qsg qD qhsg) qr) (sval qDp qe qs qh (venvSubD qsg qD qDp qhsg qr)))";
    let m_var = format!("(fun (qDp : Nat -> Sk) (qi : Nat) (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => Eq.refl (VD (qDp qi)) (sval qD (qsg qi) (qDp qi) (qhsg qi) qr))");
    let m_sort = format!("(fun (qDp : Nat -> Sk) (qn : Level) (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => Eq.refl (VD (Sk.kd Sk.ty)) (fun (qe2 : KExpr) => whnf_acc qe2))");

    let ih_a = format!("(qihA : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD), Eq (VD qsA) (sval qD (psubst qsg qA) qsA (wk_psub qDp qA qsA qhA qsg qD qhsg) qr) (sval qDp qA qsA qhA (venvSubD qsg qD qDp qhsg qr)))");
    let hypb = "(forall (qi : Nat), WK qD (qsg qi) (skcons (domSk qsA) qDp qi))";
    let ih_pb = format!("(qihB : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hypb}) (qr : VEnvD qD), Eq (VD qsB) (sval qD (psubst qsg qB) qsB (wk_psub (skcons (domSk qsA) qDp) qB qsB qhB qsg qD qhsg) qr) (sval (skcons (domSk qsA) qDp) qB qsB qhB (venvSubD qsg qD (skcons (domSk qsA) qDp) qhsg qr)))");

    let yb = format!("(vconsD (domSk qsA) qD {jb} qr)");
    let p_va = "(sval qD (psubst qsg qA) qsA (wk_psub qDp qA qsA qhA qsg qD qhsg) qr)";
    let p_va2 = format!("(sval qDp qA qsA qhA {rs})");
    let p_vb = format!("(sval {subd} (psubst (up qsg) qB) qsB (wk_psub {subdp} qB qsB qhB (up qsg) {subd} {wu}) {yb})");
    let p_mid = format!("(sval {subdp} qB qsB qhB (venvSubD (up qsg) {subd} {subdp} {wu} {yb}))");
    let p_vb2 = format!("(sval {subdp} qB qsB qhB (vconsD (domSk qsA) qDp {jb} {rs}))");
    let p_cong = format!("(Eq.cong (VEnvD {subdp}) (VD qsB) (fun (qrr : VEnvD {subdp}) => sval {subdp} qB qsB qhB qrr) (venvSubD (up qsg) {subd} {subdp} {wu} {yb}) (vconsD (domSk qsA) qDp {jb} {rs}) (r14_venvSub_up qD qDp qsg qhsg (domSk qsA) {jb} qr))");
    let p_hb = format!(
        "(Eq.trans (VD qsB) {p_vb} {p_mid} {p_vb2} (qihB (up qsg) {subd} {wu} {yb}) {p_cong})"
    );
    let m_pi = format!("(fun (qDp : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qDp qA qsA) (qhB : WK {subdp} qB qsB) {ih_a} {ih_pb} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => r14_sval_pi_congr qsA qsB {p_va} {p_va2} {p_vb} {p_vb2} (qihA qsg qD qhsg qr) {p_hb})");

    let ih_lb = format!("(qihb : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hypb}) (qr : VEnvD qD), Eq (VD qc) (sval qD (psubst qsg qb) qc (wk_psub (skcons (domSk qsA) qDp) qb qc qhb qsg qD qhsg) qr) (sval (skcons (domSk qsA) qDp) qb qc qhb (venvSubD qsg qD (skcons (domSk qsA) qDp) qhsg qr)))");
    let yx = "(vconsD (domSk qsA) qD qx qr)".to_string();
    let l_f = "(sval qD (psubst qsg (KExpr.lam qA qb)) (Sk.arr (domSk qsA) qc) (wk_psub qDp (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc) (WK.lam qDp qA qb qsA qc qhA qhb) qsg qD qhsg) qr)".to_string();
    let l_g = format!("(sval qDp (KExpr.lam qA qb) (Sk.arr (domSk qsA) qc) (WK.lam qDp qA qb qsA qc qhA qhb) {rs})");
    let l_x1 = format!("(sval {subd} (psubst (up qsg) qb) qc (wk_psub {subdp} qb qc qhb (up qsg) {subd} {wu}) {yx})");
    let l_x2 = format!("(sval {subdp} qb qc qhb (venvSubD (up qsg) {subd} {subdp} {wu} {yx}))");
    let l_x3 = format!("(sval {subdp} qb qc qhb (vconsD (domSk qsA) qDp qx {rs}))");
    let l_cong = format!("(Eq.cong (VEnvD {subdp}) (VD qc) (fun (qrr : VEnvD {subdp}) => sval {subdp} qb qc qhb qrr) (venvSubD (up qsg) {subd} {subdp} {wu} {yx}) (vconsD (domSk qsA) qDp qx {rs}) (r14_venvSub_up qD qDp qsg qhsg (domSk qsA) qx qr))");
    let l_point = format!("(fun (qx : VD (domSk qsA)) => Eq.trans (VD qc) {l_x1} {l_x2} {l_x3} (qihb (up qsg) {subd} {wu} {yx}) {l_cong})");
    let m_lam = format!("(fun (qDp : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qDp qA qsA) (qhb : WK {subdp} qb qc) {ih_a} {ih_lb} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => r13_vd_arr_funext (domSk qsA) qc {l_f} {l_g} {l_point})");

    let ih_f = format!("(qihf : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD), Eq (VD (Sk.arr qd qcc)) (sval qD (psubst qsg qf) (Sk.arr qd qcc) (wk_psub qDp qf (Sk.arr qd qcc) qhf qsg qD qhsg) qr) (sval qDp qf (Sk.arr qd qcc) qhf (venvSubD qsg qD qDp qhsg qr)))");
    let ih_ar = format!("(qiha : forall (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD), Eq (VD qd) (sval qD (psubst qsg qa) qd (wk_psub qDp qa qd qha qsg qD qhsg) qr) (sval qDp qa qd qha (venvSubD qsg qD qDp qhsg qr)))");
    let a_f = "(sval qD (psubst qsg qf) (Sk.arr qd qcc) (wk_psub qDp qf (Sk.arr qd qcc) qhf qsg qD qhsg) qr)";
    let a_f2 = format!("(sval qDp qf (Sk.arr qd qcc) qhf {rs})");
    let a_x = "(sval qD (psubst qsg qa) qd (wk_psub qDp qa qd qha qsg qD qhsg) qr)";
    let a_x2 = format!("(sval qDp qa qd qha {rs})");
    let m_app = format!("(fun (qDp : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qcc : Sk) (qhf : WK qDp qf (Sk.arr qd qcc)) (qha : WK qDp qa qd) {ih_f} {ih_ar} (qsg : Nat -> KExpr) (qD : Nat -> Sk) (qhsg : {hyp}) (qr : VEnvD qD) => r14_vapply_congr qd qcc {a_f} {a_f2} {a_x} {a_x2} (qihf qsg qD qhsg qr) (qiha qsg qD qhsg qr))");

    format!("fun (Dp : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK Dp e s) => WK.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} Dp e s h")
}

/// **`val_inst`** — corpus `val_inst` (FInterp.lean:237), at the KERNEL's own
/// `instantiate` rather than at a hand-written substitution. `val_psub` at
/// `scons a idsubst`, with `instantiate_eq_psubst` peeled by
/// `r14_sval_cast_term` and the valuation identified by `r14_venvSub_scons`.
pub(super) const TY_VAL_INST: &str = "forall (D : Nat -> Sk) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hb : WK (skcons d D) b c) (ha : WK D a d) (r : VEnvD D), Eq (VD c) (sval D (instantiate b a) c (wk_inst D b a d c hb ha) r) (sval (skcons d D) b c hb (vconsD d D (sval D a d ha r) r))";
pub(super) fn val_val_inst() -> String {
    let hsub = "(r14_scons_typed D a d ha)";
    let sym = "(Eq.symm KExpr (instantiate b a) (psubst (scons a idsubst) b) (instantiate_eq_psubst b a))";
    let wps = format!("(wk_psub (skcons d D) b c hb (scons a idsubst) D {hsub})");
    let x1 = "(sval D (instantiate b a) c (wk_inst D b a d c hb ha) r)".to_string();
    let x2 = format!("(sval D (psubst (scons a idsubst) b) c {wps} r)");
    let x3 =
        format!("(sval (skcons d D) b c hb (venvSubD (scons a idsubst) D (skcons d D) {hsub} r))");
    let x4 = "(sval (skcons d D) b c hb (vconsD d D (sval D a d ha r) r))";
    let s1 = format!(
        "(r14_sval_cast_term D (psubst (scons a idsubst) b) (instantiate b a) c {sym} {wps} r)"
    );
    let s2 = format!("(r14_val_psub (skcons d D) b c hb (scons a idsubst) D {hsub} r)");
    let s3 = format!("(Eq.cong (VEnvD (skcons d D)) (VD c) (fun (qrr : VEnvD (skcons d D)) => sval (skcons d D) b c hb qrr) (venvSubD (scons a idsubst) D (skcons d D) {hsub} r) (vconsD d D (sval D a d ha r) r) (r14_venvSub_scons D a d ha r))");
    format!("fun (D : Nat -> Sk) (b : KExpr) (a : KExpr) (d : Sk) (c : Sk) (hb : WK (skcons d D) b c) (ha : WK D a d) (r : VEnvD D) => Eq.trans (VD c) {x1} {x3} {x4} (Eq.trans (VD c) {x1} {x2} {x3} {s1} {s2}) {s3}")
}

// ================================================================
// Group G — PART B: the head-beta case of `val_step`, at the REAL step.
// ================================================================

/// The head-beta step of an ARBITRARY redex, stated at the kernel's own
/// contractum. R12's `r12_beta_step_general` is the `bvar 0` body only, because
/// without `wk_inst` there was no derivation at `instantiate b a` to pair it
/// with.
pub(super) const TY_BETA_STEP: &str = "forall (A : KExpr) (b : KExpr) (a : KExpr), whnf_step (KExpr.app (KExpr.lam A b) a) (instantiate b a)";
pub(super) const VAL_BETA_STEP: &str = "fun (A : KExpr) (b : KExpr) (a : KExpr) => whnf_step.beta (KExpr.app (KExpr.lam A b) a) (instantiate b a) (beta_reduces.beta A b a)";

/// **The corpus's `val_beta` (FInterp.lean:248), spec-side.** R12 landed the
/// derivation-level beta law (`r12_sval_beta`, `Eq.refl`), whose right-hand side
/// is a valuation extension rather than a TERM. This is the term-level law: the
/// redex and the real `instantiate` contractum have the SAME interpretation.
pub(super) const TY_VAL_BETA: &str = "forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (a : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK (skcons (domSk sA) D) b c) (ha : WK D a (domSk sA)) (r : VEnvD D), Eq (VD c) (sval D (KExpr.app (KExpr.lam A b) a) c (WK.app D (KExpr.lam A b) a (domSk sA) c (WK.lam D A b sA c hA hb) ha) r) (sval D (instantiate b a) c (wk_inst D b a (domSk sA) c hb ha) r)";
pub(super) const VAL_VAL_BETA: &str = "fun (D : Nat -> Sk) (A : KExpr) (b : KExpr) (a : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK (skcons (domSk sA) D) b c) (ha : WK D a (domSk sA)) (r : VEnvD D) => Eq.symm (VD c) (sval D (instantiate b a) c (wk_inst D b a (domSk sA) c hb ha) r) (sval (skcons (domSk sA) D) b c hb (vconsD (domSk sA) D (sval D a (domSk sA) ha r) r)) (r14_val_inst D b a (domSk sA) c hb ha r)";

/// The CONTRAST with R11, at the real step. `r11_candInterp_step_conv_refuted`
/// proves `candInterp` cannot transport membership across ONE `whnf_step` of
/// the type; here membership transports across the real head-beta step at an
/// ARBITRARY shape-typed redex, with the contractum spelled `instantiate b a`
/// exactly as `beta_reduces.beta` produces it.
pub(super) const TY_TRANSPORTS_REAL_BETA: &str = "forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (a : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK (skcons (domSk sA) D) b c) (ha : WK D a (domSk sA)) (r : VEnvD D) (w : KExpr), vcarD c (sval D (KExpr.app (KExpr.lam A b) a) c (WK.app D (KExpr.lam A b) a (domSk sA) c (WK.lam D A b sA c hA hb) ha) r) w -> vcarD c (sval D (instantiate b a) c (wk_inst D b a (domSk sA) c hb ha) r) w";
pub(super) const VAL_TRANSPORTS_REAL_BETA: &str = "fun (D : Nat -> Sk) (A : KExpr) (b : KExpr) (a : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK (skcons (domSk sA) D) b c) (ha : WK D a (domSk sA)) (r : VEnvD D) (w : KExpr) (hm : vcarD c (sval D (KExpr.app (KExpr.lam A b) a) c (WK.app D (KExpr.lam A b) a (domSk sA) c (WK.lam D A b sA c hA hb) ha) r) w) => Eq.substType (VD c) (fun (qv : VD c) => vcarD c qv w) (sval D (KExpr.app (KExpr.lam A b) a) c (WK.app D (KExpr.lam A b) a (domSk sA) c (WK.lam D A b sA c hA hb) ha) r) (sval D (instantiate b a) c (wk_inst D b a (domSk sA) c hb ha) r) (r14_val_beta D A b a sA c hA hb ha r) hm";

// ================================================================
// Group H — witnesses. Every one applies an operation at a REGISTERED R12
// object and pins the result, so none of them is compatible with the
// operation being the identity or junk.
// ================================================================

/// NON-VACUITY of the index algebra: weakening at cutoff 0 really MOVES the
/// variable. If `lift_at` were the identity on bvars this constant would not
/// typecheck.
pub(super) fn ty_lift_bvar0_witness() -> String {
    format!("Eq KExpr (lift_at {V0} Nat.zero {ONE}) (KExpr.bvar (Nat.succ Nat.zero))")
}
pub(super) const VAL_LIFT_BVAR0_WITNESS: &str = "r14_lift_at_bvar_wkpos Nat.zero Nat.zero";

/// The weakening operation applied at a REAL derivation: R12's all-`Sk.ty`
/// shape environment with a KIND-of-kinds slot inserted at the head.
pub(super) fn src_wk_lift_witness() -> String {
    format!("def r14_wk_lift_witness : WK (skcons {KDTY} r12_piEnv) (lift_at {V0} Nat.zero {ONE}) Sk.ty := wk_lift0 r12_piEnv {V0} Sk.ty (WK.var r12_piEnv Nat.zero) {KDTY}")
}

/// ...and the DISCRIMINATING form: after weakening, the old variable is
/// `bvar 1` and STILL has shape `Sk.ty`, even though slot 0 now holds
/// `Sk.kd Sk.ty`. A junk operation that returned a derivation at index 0 would
/// have to conclude at `Sk.kd Sk.ty`, and the companion refusal test measures
/// exactly that.
pub(super) fn ty_wk_lift_shifts() -> String {
    format!("WK (skcons {KDTY} r12_piEnv) (KExpr.bvar (Nat.succ Nat.zero)) Sk.ty")
}
pub(super) fn val_wk_lift_shifts() -> String {
    format!("r14_wkCastT (skcons {KDTY} r12_piEnv) (lift_at {V0} Nat.zero {ONE}) (KExpr.bvar (Nat.succ Nat.zero)) Sk.ty r14_lift_bvar0_witness r14_wk_lift_witness")
}

/// The POSITION control, not registered: the SAME statement `r14_vdCast_irrel`
/// proves, closed by `Eq.refl`. It is ACCEPTED — the kernel does apply proof
/// irrelevance — and the identical step written inline as the base minor of
/// `r14_cast_idx`'s `Eq.rec` was REFUSED with an `fvar` mismatch between the
/// two proof binders. Registering this probe is what turns "an irrelevance step
/// must be a standalone constant the proof term applies, not an inline minor"
/// from a note into a measurement.
#[cfg(test)]
pub(super) fn probe_cast_irrel_refl() -> String {
    "def r14_cast_irrel_refl_probe (s1 : Sk) (s2 : Sk) (p : Eq Sk s1 s2) (q : Eq Sk s1 s2) (v : VD s1) : Eq (VD s2) (r14_vdCast s1 s2 p v) (r14_vdCast s1 s2 q v) := Eq.refl (VD s2) (r14_vdCast s1 s2 p v)".to_string()
}

/// The NEGATIVE control, not registered: the same weakened derivation claimed
/// at the INSERTED slot's shape. The refusal test feeds this to the kernel.
#[cfg(test)]
pub(super) fn probe_wk_lift_wrong_shape() -> String {
    format!("def r14_wk_lift_wrong_shape_probe : WK (skcons {KDTY} r12_piEnv) (lift_at {V0} Nat.zero {ONE}) {KDTY} := wk_lift0 r12_piEnv {V0} Sk.ty (WK.var r12_piEnv Nat.zero) {KDTY}")
}

/// The substitution operation applied at a REAL derivation: substituting
/// `sort 0` for the zeroth variable of `bvar 0` yields a derivation of
/// `sort 0`, not of `bvar 0` and not of junk.
pub(super) fn src_wk_inst_witness() -> String {
    format!("def r14_wk_inst_witness : WK r12_piEnv {S0} {KDTY} := r14_wkCastT r12_piEnv (instantiate {V0} {S0}) {S0} {KDTY} (r12_beta_contractum_is_arg {S0}) (wk_inst r12_piEnv {V0} {S0} {KDTY} {KDTY} (WK.var (skcons {KDTY} r12_piEnv) Nat.zero) (WK.sort r12_piEnv Level.zero))")
}

/// `val_lift0` at that same weakening: the value of the weakened variable is
/// the ORIGINAL valuation's slot 0, not the inserted value `v`.
pub(super) fn ty_val_lift_witness() -> String {
    format!("forall (v : VD {KDTY}) (r : VEnvD r12_piEnv), Eq (VD Sk.ty) (sval (skcons {KDTY} r12_piEnv) (lift_at {V0} Nat.zero {ONE}) Sk.ty (wk_lift0 r12_piEnv {V0} Sk.ty (WK.var r12_piEnv Nat.zero) {KDTY}) (vconsD {KDTY} r12_piEnv v r)) (r Nat.zero)")
}
pub(super) fn val_val_lift_witness() -> String {
    format!("fun (v : VD {KDTY}) (r : VEnvD r12_piEnv) => r14_val_lift0 r12_piEnv {V0} Sk.ty (WK.var r12_piEnv Nat.zero) {KDTY} v r")
}

/// `val_inst` at that same substitution: the value of `instantiate (bvar 0)
/// (sort 0)` is the SORT's candidate — the substituted value's interpretation,
/// computed, not assumed.
pub(super) fn ty_val_inst_witness() -> String {
    format!("forall (r : VEnvD r12_piEnv), Eq (VD {KDTY}) (sval r12_piEnv (instantiate {V0} {S0}) {KDTY} (wk_inst r12_piEnv {V0} {S0} {KDTY} {KDTY} (WK.var (skcons {KDTY} r12_piEnv) Nat.zero) (WK.sort r12_piEnv Level.zero)) r) (fun (qe : KExpr) => whnf_acc qe)")
}
pub(super) fn val_val_inst_witness() -> String {
    format!("fun (r : VEnvD r12_piEnv) => r14_val_inst r12_piEnv {V0} {S0} {KDTY} {KDTY} (WK.var (skcons {KDTY} r12_piEnv) Nat.zero) (WK.sort r12_piEnv Level.zero) r")
}

// ================================================================
// The single ORDERED table. R12 and R13 used two tables (decls, then
// theorems); R14 cannot, because `r14_wk_lift_var` is a `def` that depends on
// the THEOREMS `r14_skins_idx` and `r14_lift_at_bvar_wkpos`. Interleaving is
// the point of the enum.
// ================================================================

/// One registration item, in dependency order.
pub(super) enum R14Item {
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
impl R14Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R14Item::Def { name, .. } | R14Item::Thm { name, .. } => name,
        }
    }

    /// The item as ONE parse-checkable `def`, for the parse gate.
    pub(super) fn decl_source(&self) -> String {
        match self {
            R14Item::Def { src, .. } => src.clone(),
            R14Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn def_item(name: &str, src: &str) -> R14Item {
    R14Item::Def {
        name: name.to_string(),
        src: src.to_string(),
    }
}

fn thm_item(name: &str, ty: &str, val: &str) -> R14Item {
    R14Item::Thm {
        name: name.to_string(),
        ty: ty.to_string(),
        val: val.to_string(),
    }
}

/// Every R14 constant, in registration order.
#[allow(clippy::too_many_lines)]
pub(super) fn r14_items() -> Vec<R14Item> {
    vec![
        def_item("skins", SRC_SKINS),
        def_item("r14_wkpos", SRC_WKPOS),
        def_item("r14_wkCastT", SRC_WK_CAST_T),
        def_item("r14_wkCastS", SRC_WK_CAST_S),
        def_item("r14_vdCast", SRC_VD_CAST),
        thm_item("r14_skins_zero", TY_SKINS_ZERO, VAL_SKINS_ZERO),
        thm_item("r14_skins_succ", TY_SKINS_SUCC, VAL_SKINS_SUCC),
        thm_item("r14_wkpos_zero", TY_WKPOS_ZERO, VAL_WKPOS_ZERO),
        thm_item("r14_wkpos_rec_succ", TY_WKPOS_REC_SUCC, VAL_WKPOS_REC_SUCC),
        thm_item(
            "r14_wkpos_succ_succ",
            TY_WKPOS_SUCC_SUCC,
            VAL_WKPOS_SUCC_SUCC,
        ),
        thm_item(
            "r14_lift_bvar_wkpos_rec",
            TY_LIFT_BVAR_WKPOS_REC,
            VAL_LIFT_BVAR_WKPOS_REC,
        ),
        R14Item::Thm {
            name: "r14_lift_at_bvar_wkpos".to_string(),
            ty: ty_lift_at_bvar_wkpos(),
            val: VAL_LIFT_AT_BVAR_WKPOS.to_string(),
        },
        R14Item::Thm {
            name: "r14_skins_idx".to_string(),
            ty: TY_SKINS_IDX.to_string(),
            val: val_skins_idx(),
        },
        R14Item::Def {
            name: "r14_wk_lift_var".to_string(),
            src: src_wk_lift_var(),
        },
        R14Item::Def {
            name: "wk_lift".to_string(),
            src: src_wk_lift(),
        },
        R14Item::Def {
            name: "wk_lift0".to_string(),
            src: src_wk_lift0(),
        },
        def_item("wk_up", SRC_WK_UP),
        R14Item::Def {
            name: "wk_psub".to_string(),
            src: src_wk_psub(),
        },
        def_item("r14_scons_typed", SRC_SCONS_TYPED),
        def_item("wk_inst", SRC_WK_INST),
        def_item("venvLiftD", SRC_VENV_LIFT_D),
        def_item("venvSubD", SRC_VENV_SUB_D),
        thm_item("r14_sval_cast_term", TY_SVAL_CAST_TERM, VAL_SVAL_CAST_TERM),
        R14Item::Thm {
            name: "r14_sval_cast_shape".to_string(),
            ty: ty_sval_cast_shape(),
            val: val_sval_cast_shape(),
        },
        thm_item("r14_vdCast_refl", TY_VDCAST_REFL, VAL_VDCAST_REFL),
        thm_item("r14_vdCast_irrel", TY_VDCAST_IRREL, VAL_VDCAST_IRREL),
        R14Item::Thm {
            name: "r14_cast_idx".to_string(),
            ty: ty_cast_idx(),
            val: val_cast_idx(),
        },
        R14Item::Thm {
            name: "r14_venvLift_at".to_string(),
            ty: ty_venv_lift_at(),
            val: val_venv_lift_at(),
        },
        R14Item::Thm {
            name: "r14_sval_wk_lift_var".to_string(),
            ty: ty_sval_wk_lift_var(),
            val: val_sval_wk_lift_var(),
        },
        thm_item(
            "r14_venvLift_vcons",
            TY_VENV_LIFT_VCONS,
            VAL_VENV_LIFT_VCONS,
        ),
        thm_item("r14_vapply_congr", TY_VAPPLY_CONGR, VAL_VAPPLY_CONGR),
        thm_item("r14_sval_pi_congr", TY_SVAL_PI_CONGR, VAL_SVAL_PI_CONGR),
        R14Item::Thm {
            name: "r14_val_lift".to_string(),
            ty: ty_val_lift(),
            val: val_val_lift(),
        },
        R14Item::Thm {
            name: "r14_val_lift0".to_string(),
            ty: ty_val_lift0(),
            val: VAL_VAL_LIFT0.to_string(),
        },
        thm_item("r14_venvSub_up", TY_VENV_SUB_UP, VAL_VENV_SUB_UP),
        R14Item::Thm {
            name: "r14_val_psub".to_string(),
            ty: TY_VAL_PSUB.to_string(),
            val: val_val_psub(),
        },
        thm_item("r14_venvSub_scons", TY_VENV_SUB_SCONS, VAL_VENV_SUB_SCONS),
        R14Item::Thm {
            name: "r14_val_inst".to_string(),
            ty: TY_VAL_INST.to_string(),
            val: val_val_inst(),
        },
        thm_item("r14_beta_step", TY_BETA_STEP, VAL_BETA_STEP),
        thm_item("r14_val_beta", TY_VAL_BETA, VAL_VAL_BETA),
        thm_item(
            "r14_sval_transports_real_beta",
            TY_TRANSPORTS_REAL_BETA,
            VAL_TRANSPORTS_REAL_BETA,
        ),
        R14Item::Thm {
            name: "r14_lift_bvar0_witness".to_string(),
            ty: ty_lift_bvar0_witness(),
            val: VAL_LIFT_BVAR0_WITNESS.to_string(),
        },
        R14Item::Def {
            name: "r14_wk_lift_witness".to_string(),
            src: src_wk_lift_witness(),
        },
        R14Item::Thm {
            name: "r14_wk_lift_shifts".to_string(),
            ty: ty_wk_lift_shifts(),
            val: val_wk_lift_shifts(),
        },
        R14Item::Def {
            name: "r14_wk_inst_witness".to_string(),
            src: src_wk_inst_witness(),
        },
        R14Item::Thm {
            name: "r14_val_lift_witness".to_string(),
            ty: ty_val_lift_witness(),
            val: val_val_lift_witness(),
        },
        R14Item::Thm {
            name: "r14_val_inst_witness".to_string(),
            ty: ty_val_inst_witness(),
            val: val_val_inst_witness(),
        },
    ]
}

/// Every R14 source as a parse-checkable declaration, for the parse gate, the
/// drift-proof premise test and the scratch harness.
#[cfg(test)]
pub(super) fn r14_all_sources() -> Vec<(String, String)> {
    r14_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
