// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source builders for R12 of the candidate-model construction ladder — the
//! pure string half of the SHAPE / DENOTATION SPLIT.
//!
//! A sibling module rather than a region of `candmodel_construct_r12.rs`, on
//! the convention `candmodel_construct_r10_src.rs` set. Read
//! `candmodel_construct_r12.rs` first: it carries the rung's verdict, the two
//! PROVED obstructions and the honesty notes.
//!
//! **This module deliberately imports nothing.** Every source it emits is built
//! from local constants, so the whole file can be `include!`d into a scratch
//! crate that depends only on `clean-parser` and parse-checked in a second,
//! without a `clean-verify` build. `r12_all_sources` is the entry point that
//! harness iterates.

// ================================================================
// Shared spellings.
// ================================================================

/// `bvar 0`.
pub(super) const V0: &str = "(KExpr.bvar Nat.zero)";
/// `sort 0`.
pub(super) const S0: &str = "(KExpr.sort Level.zero)";
/// The shape of a semantic type-of-types (every sort gets this one).
pub(super) const KDTY: &str = "(Sk.kd Sk.ty)";
/// The shape of a KIND OF KINDS. A variable of this shape is the only way to
/// annotate a lambda whose bound variable is itself a TYPE, which is what makes
/// a type-level beta redex shape-typed.
pub(super) const KDKDTY: &str = "(Sk.kd (Sk.kd Sk.ty))";
/// The top candidate, spelled as a set.
pub(super) const TOPSET: &str = "(fun (qe : KExpr) => whnf_acc qe)";
/// R11's non-dependent function type, reused verbatim.
pub(super) const PI00: &str = "(KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))";

// ================================================================
// Group A — the shape algebra and the shape-indexed value domain.
// Corpus: Stratified/Shapes.lean (`Sk`, `VD`, `Val`, `vcar`, `Good`).
// ================================================================

/// The shape algebra. Corpus `Sk` (Shapes.lean:36) verbatim: a semantic type, a
/// semantic kind tagged with the shape of its inhabitants, and a semantic
/// constructor. Three constructors, no indices, `Type 0`.
pub(super) const SRC_SK: &str = "inductive Sk : Type
| ty : Sk
| kd : Sk -> Sk
| arr : Sk -> Sk -> Sk";

/// The shape of the inhabitants of a kind; junk (`ty`) off the kinds.
pub(super) const SRC_DOM_SK: &str = "def domSk (s : Sk) : Sk := Sk.rec (fun (qs : Sk) => Sk) Sk.ty (fun (qs1 : Sk) (qih : Sk) => qs1) (fun (qd : Sk) (qc : Sk) (qihd : Sk) (qihc : Sk) => Sk.ty) s";

/// The shape of a Pi: a Pi of kinds is a kind, anything else is a type. Corpus
/// `piShape` (FInterp.lean:57). A DOUBLE `Sk.rec`, because the outer recursion
/// leaves `piShape (kd s1) t` stuck on a variable `t`.
pub(super) const SRC_PI_SHAPE: &str = "def piShape (s : Sk) (t : Sk) : Sk := Sk.rec (fun (qs : Sk) => Sk -> Sk) (fun (qt : Sk) => Sk.ty) (fun (qs1 : Sk) (qih : Sk -> Sk) (qt1 : Sk) => Sk.rec (fun (qt2 : Sk) => Sk) Sk.ty (fun (qs2 : Sk) (qih2 : Sk) => Sk.kd (Sk.arr qs1 qs2)) (fun (qd : Sk) (qc : Sk) (qa : Sk) (qb : Sk) => Sk.ty) qt1) (fun (qd : Sk) (qc : Sk) (qa : Sk -> Sk) (qb : Sk -> Sk) (qt : Sk) => Sk.ty) s t";

/// **THE LARGE ELIMINATION.** The domain of values of a shape: a type and a
/// kind both carry a candidate, a constructor carries a FUNCTION between value
/// domains. Corpus `VD` (Shapes.lean:58). This is the definition that makes a
/// semantic function representable at all — an inductive
/// `SVal | fn : (SVal -> SVal) -> SVal` is not strictly positive and the kernel
/// refuses it, which is exactly why the corpus indexes by a shape.
///
/// Note the universe. The spec's candidates are `KExpr -> Type` (Type-valued,
/// because `whnf_acc` is `Acc`-shaped), so `VD s : Type 1` where the corpus's is
/// `Type 0` (its candidates are `Tm -> Prop`). That one-universe offset is the
/// whole content of R12's first obstruction — see `SRC_PI_CAND_V`.
pub(super) const SRC_VD: &str = "def VD (s : Sk) : Type 1 := Sk.rec (fun (qs : Sk) => Type 1) (KExpr -> Type) (fun (qs1 : Sk) (qih : Type 1) => KExpr -> Type) (fun (qd : Sk) (qc : Sk) (qX : Type 1) (qY : Type 1) => qX -> qY) s";

/// The candidate a value denotes: itself at a type or a kind, the top candidate
/// at a constructor. Corpus `vcar` (Shapes.lean:161), indexed rather than
/// packaged.
pub(super) const SRC_VCAR_D: &str = "def vcarD (s : Sk) (v : VD s) : KExpr -> Type := Sk.rec (fun (qs : Sk) => VD qs -> KExpr -> Type) (fun (qC : VD Sk.ty) => qC) (fun (qs1 : Sk) (qih : VD qs1 -> KExpr -> Type) (qC : VD (Sk.kd qs1)) => qC) (fun (qd : Sk) (qc : Sk) (qihd : VD qd -> KExpr -> Type) (qihc : VD qc -> KExpr -> Type) (qf : VD (Sk.arr qd qc)) (qe : KExpr) => whnf_acc qe) s v";

/// Package a candidate at a Pi-shape. Corpus `mkTy` (Shapes.lean:91) with the
/// shape taken from the two shape-typing premises instead of from a junk probe:
/// the derivation-indexed interpretation already knows both shapes, so the
/// corpus's `G (junkV (domSk sA))` probe is not needed.
pub(super) const SRC_MK_TY_D: &str = "def mkTyD (s : Sk) (t : Sk) (C : KExpr -> Type) : VD (piShape s t) := Sk.rec (fun (qs : Sk) => forall (qt : Sk), (KExpr -> Type) -> VD (piShape qs qt)) (fun (qt : Sk) (qC : KExpr -> Type) => qC) (fun (qs1 : Sk) (qih : forall (qt : Sk), (KExpr -> Type) -> VD (piShape qs1 qt)) => Sk.rec (fun (qt : Sk) => (KExpr -> Type) -> VD (piShape (Sk.kd qs1) qt)) (fun (qC : KExpr -> Type) => qC) (fun (qs2 : Sk) (qa : (KExpr -> Type) -> VD (piShape (Sk.kd qs1) qs2)) (qC : KExpr -> Type) => qC) (fun (qd : Sk) (qc : Sk) (qa : (KExpr -> Type) -> VD (piShape (Sk.kd qs1) qd)) (qb : (KExpr -> Type) -> VD (piShape (Sk.kd qs1) qc)) (qC : KExpr -> Type) => qC)) (fun (qd : Sk) (qc : Sk) (qa : forall (qt : Sk), (KExpr -> Type) -> VD (piShape qd qt)) (qb : forall (qt : Sk), (KExpr -> Type) -> VD (piShape qc qt)) (qt : Sk) (qC : KExpr -> Type) => qC) s t C";

/// The junk value of each shape. Corpus `junkD` (Shapes.lean:67) with `SN`
/// replaced by the spec's `whnf_acc`. Its existence is what makes `GoodD`
/// inhabited at EVERY shape, which the dependent Pi-candidate's cr1 needs.
pub(super) const SRC_JUNK_D: &str = "def junkD (s : Sk) : VD s := Sk.rec (fun (qs : Sk) => VD qs) (fun (qe : KExpr) => whnf_acc qe) (fun (qs1 : Sk) (qih : VD qs1) (qe : KExpr) => whnf_acc qe) (fun (qd : Sk) (qc : Sk) (qihd : VD qd) (qihc : VD qc) (qx : VD qd) => qihc) s";

/// The `Type 1` lift of R10's candidate interface, with NO new inductive: a
/// constant function out of a `Sort 2` domain IS a universe lift. `GoodD` must
/// land in `Type 1` because its `arr` clause quantifies over `VD d : Type 1`,
/// and the kernel is NON-CUMULATIVE, so `IsCandHI S : Type 0` cannot be the base
/// clause directly.
pub(super) const SRC_GOOD_SET: &str =
    "def GoodSet (S : KExpr -> Type) : Type 1 := forall (qX : KExpr -> Type), IsCandHI S";

/// A value is GOOD when every candidate buried in it really is one. Corpus
/// `GoodD` (Shapes.lean:126) at R10's HEAD-INERT candidate interface — not at
/// the unrestricted one, because R10 proved unrestricted cr3 false for the
/// Pi-candidate over the real reflected environment.
pub(super) const SRC_GOOD_D: &str = "def GoodD (s : Sk) (v : VD s) : Type 1 := Sk.rec (fun (qs : Sk) => VD qs -> Type 1) (fun (qC : VD Sk.ty) => GoodSet qC) (fun (qs1 : Sk) (qih : VD qs1 -> Type 1) (qC : VD (Sk.kd qs1)) => GoodSet qC) (fun (qd : Sk) (qc : Sk) (qihd : VD qd -> Type 1) (qihc : VD qc -> Type 1) (qf : VD (Sk.arr qd qc)) => forall (qx : VD qd), qihd qx -> qihc (qf qx)) s v";

/// THE PACKAGED VALUE TYPE. Corpus `Val := Sigma s : Sk, VD s`
/// (Shapes.lean:64) as a one-constructor inductive, since the spec has no sigma.
/// `Type 1` because its second field is.
pub(super) const SRC_VAL: &str = "inductive Val : Type 1
| mk : forall (s : Sk), VD s -> Val";

/// The shape of a packaged value (corpus `.1`).
pub(super) const SRC_VAL_S: &str =
    "def valS (v : Val) : Sk := Val.rec (fun (qv : Val) => Sk) (fun (qs : Sk) (qx : VD qs) => qs) v";

/// The payload of a packaged value (corpus `.2`) — a DEPENDENT projection, so
/// its motive is `fun qv => VD (valS qv)`.
pub(super) const SRC_VAL_D: &str = "def valD (v : Val) : VD (valS v) := Val.rec (fun (qv : Val) => VD (valS qv)) (fun (qs : Sk) (qx : VD qs) => qx) v";

/// The candidate a packaged value denotes (corpus `vcar`).
pub(super) const SRC_VAL_CAR: &str =
    "def valCar (v : Val) : KExpr -> Type := vcarD (valS v) (valD v)";

/// A good packaged value (corpus `Good`).
pub(super) const SRC_VAL_GOOD: &str = "def valGood (v : Val) : Type 1 := GoodD (valS v) (valD v)";

/// The junk value of a shape, packaged (corpus `junkV`).
pub(super) const SRC_VAL_JUNK: &str = "def valJunk (s : Sk) : Val := Val.mk s (junkD s)";

// ================================================================
// Group B — shape environments, shape typing, and the interpretation.
// Corpus: Stratified/FWK.lean (`SkEnv`, `skcons`, `WK`) and FInterp.lean
// (`VEnv`, `vcons`, `val`).
// ================================================================

/// Extending a shape environment under a binder. Corpus `skcons` (FWK.lean:33).
pub(super) const SRC_SKCONS: &str = "def skcons (s : Sk) (D : Nat -> Sk) (i : Nat) : Sk := Nat.rec (fun (qi : Nat) => Sk) s (fun (qn : Nat) (qih : Sk) => D qn) i";

/// A DEPENDENT valuation: a value of the RIGHT SHAPE for every de Bruijn index.
/// Corpus `VEnv` (FInterp.lean:36) is untyped and needs `MatchEnv`
/// (FWK.lean:218) beside it; indexing the valuation by the shape environment
/// makes `MatchEnv` hold by construction and deletes it — and with it every
/// `coeD` coercion, the decidable equality on `Sk` those coercions need, and
/// every shape side condition in the Pi clause.
pub(super) const SRC_VENV_D: &str =
    "def VEnvD (D : Nat -> Sk) : Type 1 := forall (qi : Nat), VD (D qi)";

/// Extending a dependent valuation. Corpus `vcons` (FInterp.lean:39), with the
/// `Nat.rec` motive carrying the shape so both branches typecheck.
pub(super) const SRC_VCONS_D: &str = "def vconsD (s : Sk) (D : Nat -> Sk) (v : VD s) (r : VEnvD D) (i : Nat) : VD (skcons s D i) := Nat.rec (fun (qi : Nat) => VD (skcons s D qi)) v (fun (qn : Nat) (qih : VD (skcons s D qn)) => r qn) i";

/// A valuation is good when all its values are. Corpus `GoodEnv`
/// (FInterp.lean:45).
pub(super) const SRC_GOOD_ENV_D: &str =
    "def GoodEnvD (D : Nat -> Sk) (r : VEnvD D) : Type 1 := forall (qi : Nat), GoodD (D qi) (r qi)";

/// SHAPE TYPING. Corpus `WK` (FWK.lean:73) on `KExpr`/`Level`: a simple type
/// system on the raw syntax that assigns to a term the SHAPE of its value.
/// Levels are semantically inert — every sort gets `kd ty`, exactly as the
/// corpus has it, which is why `Level`'s `param`/`max`/`imax` trees cost this
/// route nothing where they killed the coupled route (design verdict 2).
pub(super) const SRC_WK: &str = "inductive WK : (Nat -> Sk) -> KExpr -> Sk -> Type
| var : forall (D : Nat -> Sk) (i : Nat), WK D (KExpr.bvar i) (D i)
| sort : forall (D : Nat -> Sk) (n : Level), WK D (KExpr.sort n) (Sk.kd Sk.ty)
| pi : forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk), WK D A sA -> WK (skcons (domSk sA) D) B sB -> WK D (KExpr.pi A B) (piShape sA sB)
| lam : forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (sA : Sk) (c : Sk), WK D A sA -> WK (skcons (domSk sA) D) b c -> WK D (KExpr.lam A b) (Sk.arr (domSk sA) c)
| app : forall (D : Nat -> Sk) (f : KExpr) (a : KExpr) (d : Sk) (c : Sk), WK D f (Sk.arr d c) -> WK D a d -> WK D (KExpr.app f a) c";

/// **THE SHAPE-INDEXED INTERPRETATION.** Corpus `val` (FInterp.lean:72), by
/// recursion on the SHAPE DERIVATION rather than on the term, which is what
/// keeps it coercion-free and junk-free.
///
/// The two clauses that matter: `lam` denotes a SEMANTIC FUNCTION
/// `fun x => sval b (x :: r)`, and `app` denotes semantic application. The
/// semantic beta law is therefore definitional (`r12_sval_beta`) — the law R11
/// proved `candInterp` cannot have.
///
/// The `pi` clause here is the JUNK-PROBE Girard candidate. It is NOT the
/// corpus's intersection over all good values of the domain shape; see
/// `SRC_PI_CAND_V` (universe horn) and `SRC_PI_CAND_DEP` (recursion horn) for
/// why that one cannot be a clause of THIS recursion, and what is built instead.
pub(super) fn src_sval() -> String {
    let motive =
        "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => VEnvD qD -> VD qs)";
    let m_var = "(fun (qD : Nat -> Sk) (qi : Nat) (qr : VEnvD qD) => qr qi)";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) (qr : VEnvD qD) (qe : KExpr) => whnf_acc qe)";
    let m_pi = "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK (skcons (domSk qsA) qD) qB qsB) (qihA : VEnvD qD -> VD qsA) (qihB : VEnvD (skcons (domSk qsA) qD) -> VD qsB) (qr : VEnvD qD) => mkTyD qsA qsB (PiSet (vcarD qsA (qihA qr)) (fun (qa : KExpr) => vcarD qsB (qihB (vconsD (domSk qsA) qD (junkD (domSk qsA)) qr)))))";
    let m_lam = "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK (skcons (domSk qsA) qD) qb qc) (qihA : VEnvD qD -> VD qsA) (qihb : VEnvD (skcons (domSk qsA) qD) -> VD qc) (qr : VEnvD qD) (qx : VD (domSk qsA)) => qihb (vconsD (domSk qsA) qD qx qr))";
    let m_app = "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qc : Sk) (qhf : WK qD qf (Sk.arr qd qc)) (qha : WK qD qa qd) (qihf : VEnvD qD -> VD (Sk.arr qd qc)) (qiha : VEnvD qD -> VD qd) (qr : VEnvD qD) => qihf qr (qiha qr))";
    format!(
        "def sval (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D) : VD s := WK.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h r"
    )
}

// ================================================================
// Group C — the dependent Pi candidate, built ON TOP of `sval`.
// ================================================================

/// The intersection index of the dependent codomain: the codomain
/// interpretation at the value of EVERY shape-typed term of the domain shape.
/// A `KExpr`/`WK`-indexed intersection, so it stays in `Type 0` where the
/// corpus's value-indexed one would not.
pub(super) const SRC_PI_COD_DEP_IDX: &str = "def piCodDepIdx (D : Nat -> Sk) (d : Sk) (sB : Sk) (GB : VD d -> VD sB) (r : VEnvD D) (w : KExpr) : Type := forall (qy : KExpr) (qhy : WK D qy d), vcarD sB (GB (sval D qy d qhy r)) w";

/// The dependent codomain candidate: the junk probe — which supplies cr1 when
/// the intersection index is empty, exactly as the corpus's `good_junkV` does —
/// intersected with the derivation-indexed family.
pub(super) const SRC_PI_COD_DEP: &str = "def piCodDep (D : Nat -> Sk) (d : Sk) (sB : Sk) (GB : VD d -> VD sB) (r : VEnvD D) (w : KExpr) : Type := AndType (vcarD sB (GB (junkD d)) w) (piCodDepIdx D d sB GB r w)";

/// **THE DEPENDENT PI CANDIDATE** — what R6 proved non-portable for
/// `candInterp`. The codomain is interpreted in the environment EXTENDED BY THE
/// ARGUMENT'S OWN VALUE, and the recursion R6 showed unmeasurable
/// (`candInterp (instantiate B a)`, whose argument is reachable from the type
/// being defined) is replaced by an environment extension on the structurally
/// smaller `B`.
pub(super) const SRC_PI_CAND_DEP: &str = "def piCandDep (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) (r : VEnvD D) : KExpr -> Type := PiSet CA (fun (qa : KExpr) => piCodDep D d sB GB r)";

/// The dependent Pi candidate at a REAL shape-typing premise pair: the domain
/// candidate is the domain type's interpretation, the codomain family is the
/// codomain type's under the extended environment.
pub(super) const SRC_WK_PI_DEP: &str = "def wkPiDep (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK (skcons (domSk sA) D) B sB) (r : VEnvD D) : KExpr -> Type := piCandDep D (domSk sA) sB (vcarD sA (sval D A sA hA r)) (fun (qv : VD (domSk sA)) => sval (skcons (domSk sA) D) B sB hB (vconsD (domSk sA) D qv r)) r";

/// **THE UNIVERSE OBSTRUCTION, REGISTERED AT ITS TRUE UNIVERSE.** The corpus's
/// Pi clause (FInterp.lean:63 `piVal`) quantifies over the whole value domain of
/// the domain shape. It is a perfectly good definition — and it lands in
/// `KExpr -> Type 1`, one universe ABOVE the `KExpr -> Type` that `VD Sk.ty` is,
/// because `VD d : Type 1` and `Type` is PREDICATIVE. The corpus lands the same
/// clause in `Prop`, which is IMPREDICATIVE. Shifting does not help: at
/// `VD ty := KExpr -> Type 1` the clause lands at `Type 2`.
pub(super) const SRC_PI_CAND_V: &str = "def piCandV (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) : KExpr -> Type 1 := fun (qt : KExpr) => forall (qx : KExpr), CA qx -> forall (qv : VD d), GoodD d qv -> vcarD sB (GB qv) (KExpr.app qt qx)";

// ================================================================
// Group D — the concrete R11 contrast.
// ================================================================

/// A shape environment in which every index is a KIND OF KINDS.
pub(super) const SRC_BETA_ENV: &str = "def r12_betaEnv (i : Nat) : Sk := Sk.kd (Sk.kd Sk.ty)";

/// **THE TYPE-LEVEL BETA REDEX, SHAPE-TYPED.** `(fun x. x) (Sort 0)` — R11's
/// counterexample SHAPE (an identity lambda applied at the type level) with the
/// annotation moved to a kind-of-kinds variable so that a `WK` derivation
/// exists. R11's own redex `app (lam (sort 0) (bvar 0)) (pi (sort 0) (sort 0))`
/// is NOT shape-typed: annotated at `sort 0` the lambda takes an argument of
/// shape `ty`, while `pi (sort 0) (sort 0)` has shape `kd (arr ty ty)`.
pub(super) const SRC_BETA_REDEX: &str = "def r12_betaRedex : KExpr := KExpr.app (KExpr.lam (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)";

/// The all-junk valuation of the contrast environment.
pub(super) const SRC_BETA_JUNK_ENV: &str =
    "def r12_betaJunkEnv (i : Nat) : VD (r12_betaEnv i) := junkD (r12_betaEnv i)";

/// The shape derivation of the contrast redex.
pub(super) fn src_beta_deriv() -> String {
    let lam = format!("(WK.lam r12_betaEnv {V0} {V0} {KDKDTY} {KDTY} (WK.var r12_betaEnv Nat.zero) (WK.var (skcons {KDTY} r12_betaEnv) Nat.zero))");
    format!("def r12_betaDeriv : WK r12_betaEnv r12_betaRedex {KDTY} := WK.app r12_betaEnv (KExpr.lam {V0} {V0}) {S0} {KDTY} {KDTY} {lam} (WK.sort r12_betaEnv Level.zero)")
}

/// The premise R11 refuted, as a named `Type` so it can sit inside an `AndType`
/// without a parenthesised `forall` in argument position.
pub(super) const SRC_CANDINTERP_STEP_CONV: &str = "def r12_candInterpStepConv : Type := forall (qA : KExpr) (qB : KExpr) (qe : KExpr), whnf_step qA qB -> candInterp qA qe -> candInterp qB qe";

/// ...and the same transport for `sval`, at the concrete shape-typed redex.
pub(super) fn src_sval_transports_beta() -> String {
    format!("def r12_svalTransportsBeta : Type := forall (qe : KExpr), vcarD {KDTY} (sval r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r12_betaJunkEnv) qe -> vcarD {KDTY} (sval r12_betaEnv {S0} {KDTY} (WK.sort r12_betaEnv Level.zero) r12_betaJunkEnv) qe")
}

/// The shape environment of the properness witness — every index a plain type.
pub(super) const SRC_PI_ENV: &str = "def r12_piEnv (i : Nat) : Sk := Sk.ty";

/// The all-junk dependent valuation at an ARBITRARY shape environment — the
/// premise gate's supply for `VEnvD`, and the proof that a valuation always
/// exists (so every `GoodEnvD`-premised statement below is non-vacuous).
pub(super) const SRC_JUNK_ENV: &str =
    "def r12_junkEnv (D : Nat -> Sk) : VEnvD D := fun (qi : Nat) => junkD (D qi)";

// ================================================================
// Group E — theorem statements and proof terms.
// ================================================================

pub(super) const TY_GOODSET_UP: &str = "forall (S : KExpr -> Type), IsCandHI S -> GoodSet S";
pub(super) const VAL_GOODSET_UP: &str =
    "fun (S : KExpr -> Type) (h : IsCandHI S) (qX : KExpr -> Type) => h";

pub(super) const TY_GOODSET_DOWN: &str = "forall (S : KExpr -> Type), GoodSet S -> IsCandHI S";
pub(super) fn val_goodset_down() -> String {
    format!("fun (S : KExpr -> Type) (h : GoodSet S) => h {TOPSET}")
}

pub(super) fn ty_goodset_whnfacc() -> String {
    format!("GoodSet {TOPSET}")
}
pub(super) fn val_goodset_whnfacc() -> String {
    format!("goodSet_up {TOPSET} isCandHI_whnfAcc")
}

pub(super) const TY_VCARD_MKTYD: &str = "forall (s : Sk) (t : Sk) (C : KExpr -> Type), Eq (KExpr -> Type) (vcarD (piShape s t) (mkTyD s t C)) C";
pub(super) const VAL_VCARD_MKTYD: &str = "fun (s : Sk) (t : Sk) (C : KExpr -> Type) => Sk.rec (fun (qs : Sk) => forall (qt : Sk), Eq (KExpr -> Type) (vcarD (piShape qs qt) (mkTyD qs qt C)) C) (fun (qt : Sk) => Eq.refl (KExpr -> Type) C) (fun (qs1 : Sk) (qih : forall (qt : Sk), Eq (KExpr -> Type) (vcarD (piShape qs1 qt) (mkTyD qs1 qt C)) C) => Sk.rec (fun (qt : Sk) => Eq (KExpr -> Type) (vcarD (piShape (Sk.kd qs1) qt) (mkTyD (Sk.kd qs1) qt C)) C) (Eq.refl (KExpr -> Type) C) (fun (qs2 : Sk) (qa : Eq (KExpr -> Type) (vcarD (piShape (Sk.kd qs1) qs2) (mkTyD (Sk.kd qs1) qs2 C)) C) => Eq.refl (KExpr -> Type) C) (fun (qd : Sk) (qc : Sk) (qa : Eq (KExpr -> Type) (vcarD (piShape (Sk.kd qs1) qd) (mkTyD (Sk.kd qs1) qd C)) C) (qb : Eq (KExpr -> Type) (vcarD (piShape (Sk.kd qs1) qc) (mkTyD (Sk.kd qs1) qc C)) C) => Eq.refl (KExpr -> Type) C)) (fun (qd : Sk) (qc : Sk) (qa : forall (qt : Sk), Eq (KExpr -> Type) (vcarD (piShape qd qt) (mkTyD qd qt C)) C) (qb : forall (qt : Sk), Eq (KExpr -> Type) (vcarD (piShape qc qt) (mkTyD qc qt C)) C) (qt : Sk) => Eq.refl (KExpr -> Type) C) s t";

pub(super) const TY_GOODD_MKTYD: &str =
    "forall (s : Sk) (t : Sk) (C : KExpr -> Type), IsCandHI C -> GoodD (piShape s t) (mkTyD s t C)";
pub(super) const VAL_GOODD_MKTYD: &str = "fun (s : Sk) (t : Sk) (C : KExpr -> Type) (h : IsCandHI C) => Sk.rec (fun (qs : Sk) => forall (qt : Sk), GoodD (piShape qs qt) (mkTyD qs qt C)) (fun (qt : Sk) => goodSet_up C h) (fun (qs1 : Sk) (qih : forall (qt : Sk), GoodD (piShape qs1 qt) (mkTyD qs1 qt C)) => Sk.rec (fun (qt : Sk) => GoodD (piShape (Sk.kd qs1) qt) (mkTyD (Sk.kd qs1) qt C)) (goodSet_up C h) (fun (qs2 : Sk) (qa : GoodD (piShape (Sk.kd qs1) qs2) (mkTyD (Sk.kd qs1) qs2 C)) => goodSet_up C h) (fun (qd : Sk) (qc : Sk) (qa : GoodD (piShape (Sk.kd qs1) qd) (mkTyD (Sk.kd qs1) qd C)) (qb : GoodD (piShape (Sk.kd qs1) qc) (mkTyD (Sk.kd qs1) qc C)) => goodSet_up C h)) (fun (qd : Sk) (qc : Sk) (qa : forall (qt : Sk), GoodD (piShape qd qt) (mkTyD qd qt C)) (qb : forall (qt : Sk), GoodD (piShape qc qt) (mkTyD qc qt C)) (qt : Sk) => goodSet_up C h) s t";

pub(super) const TY_GOODD_JUNKD: &str = "forall (s : Sk), GoodD s (junkD s)";
pub(super) const VAL_GOODD_JUNKD: &str = "fun (s : Sk) => Sk.rec (fun (qs : Sk) => GoodD qs (junkD qs)) goodSet_whnfAcc (fun (qs1 : Sk) (qih : GoodD qs1 (junkD qs1)) => goodSet_whnfAcc) (fun (qd : Sk) (qc : Sk) (qihd : GoodD qd (junkD qd)) (qihc : GoodD qc (junkD qc)) (qx : VD qd) (qhx : GoodD qd qx) => qihc) s";

pub(super) const TY_ISCANDHI_VCARD: &str =
    "forall (s : Sk) (v : VD s), GoodD s v -> IsCandHI (vcarD s v)";
pub(super) const VAL_ISCANDHI_VCARD: &str = "fun (s : Sk) (v : VD s) (h : GoodD s v) => Sk.rec (fun (qs : Sk) => forall (qv : VD qs), GoodD qs qv -> IsCandHI (vcarD qs qv)) (fun (qC : VD Sk.ty) (qh : GoodD Sk.ty qC) => goodSet_down qC qh) (fun (qs1 : Sk) (qih : forall (qv : VD qs1), GoodD qs1 qv -> IsCandHI (vcarD qs1 qv)) (qC : VD (Sk.kd qs1)) (qh : GoodD (Sk.kd qs1) qC) => goodSet_down qC qh) (fun (qd : Sk) (qc : Sk) (qa : forall (qv : VD qd), GoodD qd qv -> IsCandHI (vcarD qd qv)) (qb : forall (qv : VD qc), GoodD qc qv -> IsCandHI (vcarD qc qv)) (qf : VD (Sk.arr qd qc)) (qh : GoodD (Sk.arr qd qc) qf) => isCandHI_whnfAcc) s v h";

pub(super) const TY_GOODENVD_VCONSD: &str = "forall (s : Sk) (D : Nat -> Sk) (v : VD s) (r : VEnvD D), GoodD s v -> GoodEnvD D r -> GoodEnvD (skcons s D) (vconsD s D v r)";
pub(super) const VAL_GOODENVD_VCONSD: &str = "fun (s : Sk) (D : Nat -> Sk) (v : VD s) (r : VEnvD D) (hv : GoodD s v) (hr : GoodEnvD D r) (i : Nat) => Nat.rec (fun (qi : Nat) => GoodD (skcons s D qi) (vconsD s D v r qi)) hv (fun (qn : Nat) (qih : GoodD (skcons s D qn) (vconsD s D v r qn)) => hr qn) i";

pub(super) const TY_GOODENVD_JUNK: &str =
    "forall (D : Nat -> Sk), GoodEnvD D (fun (qi : Nat) => junkD (D qi))";
pub(super) const VAL_GOODENVD_JUNK: &str = "fun (D : Nat -> Sk) (i : Nat) => goodD_junkD (D i)";

pub(super) const TY_VALGOOD_JUNK: &str = "forall (s : Sk), valGood (valJunk s)";
pub(super) const VAL_VALGOOD_JUNK: &str = "fun (s : Sk) => goodD_junkD s";

pub(super) const TY_ISCANDHI_VALCAR: &str = "forall (v : Val), valGood v -> IsCandHI (valCar v)";
pub(super) const VAL_ISCANDHI_VALCAR: &str =
    "fun (v : Val) (h : valGood v) => isCandHI_vcarD (valS v) (valD v) h";

// --- the fundamental candidate-hood theorem -------------------------------

pub(super) const TY_SVAL_GOOD: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D), GoodEnvD D r -> GoodD s (sval D e s h r)";

pub(super) fn val_sval_good() -> String {
    let motive = "(fun (qD : Nat -> Sk) (qe : KExpr) (qs : Sk) (qh : WK qD qe qs) => forall (qr : VEnvD qD), GoodEnvD qD qr -> GoodD qs (sval qD qe qs qh qr))";
    let m_var =
        "(fun (qD : Nat -> Sk) (qi : Nat) (qr : VEnvD qD) (qhr : GoodEnvD qD qr) => qhr qi)";
    let m_sort = "(fun (qD : Nat -> Sk) (qn : Level) (qr : VEnvD qD) (qhr : GoodEnvD qD qr) => goodSet_whnfAcc)";

    // pi: the goal reduces to `GoodD (piShape qsA qsB) (mkTyD qsA qsB SET)`.
    let ca = "(vcarD qsA (sval qD qA qsA qhA qr))";
    let jenv = "(vconsD (domSk qsA) qD (junkD (domSk qsA)) qr)";
    let cbc = format!("(vcarD qsB (sval (skcons (domSk qsA) qD) qB qsB qhB {jenv}))");
    let cb = format!("(fun (qa : KExpr) => {cbc})");
    let set = format!("(PiSet {ca} {cb})");
    let hca = "(isCandHI_vcarD qsA (sval qD qA qsA qhA qr) (qihgA qr qhr))";
    let hgood_jenv =
        "(goodEnvD_vconsD (domSk qsA) qD (junkD (domSk qsA)) qr (goodD_junkD (domSk qsA)) qhr)"
            .to_string();
    let hcb = format!("(fun (qa2 : KExpr) (qm : {ca} qa2) => isCandHI_vcarD qsB (sval (skcons (domSk qsA) qD) qB qsB qhB {jenv}) (qihgB {jenv} {hgood_jenv}))");
    let hinv = format!("(fun (qa1 : KExpr) (qa2 : KExpr) (qw : KExpr) (qm1 : {ca} qa1) (qst : whnf_step qa1 qa2) (qm : {cbc} qw) => qm)");
    let ih_a =
        "(qihgA : forall (qr2 : VEnvD qD), GoodEnvD qD qr2 -> GoodD qsA (sval qD qA qsA qhA qr2))";
    let ih_b = "(qihgB : forall (qr2 : VEnvD (skcons (domSk qsA) qD)), GoodEnvD (skcons (domSk qsA) qD) qr2 -> GoodD qsB (sval (skcons (domSk qsA) qD) qB qsB qhB qr2))";
    let m_pi = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qB : KExpr) (qsA : Sk) (qsB : Sk) (qhA : WK qD qA qsA) (qhB : WK (skcons (domSk qsA) qD) qB qsB) {ih_a} {ih_b} (qr : VEnvD qD) (qhr : GoodEnvD qD qr) => goodD_mkTyD qsA qsB {set} (isCandHI_piSet {ca} {cb} {hca} {hcb} {hinv}))"
    );

    let ih_la =
        "(qihgA : forall (qr2 : VEnvD qD), GoodEnvD qD qr2 -> GoodD qsA (sval qD qA qsA qhA qr2))";
    let ih_lb = "(qihgb : forall (qr2 : VEnvD (skcons (domSk qsA) qD)), GoodEnvD (skcons (domSk qsA) qD) qr2 -> GoodD qc (sval (skcons (domSk qsA) qD) qb qc qhb qr2))";
    let m_lam = format!(
        "(fun (qD : Nat -> Sk) (qA : KExpr) (qb : KExpr) (qsA : Sk) (qc : Sk) (qhA : WK qD qA qsA) (qhb : WK (skcons (domSk qsA) qD) qb qc) {ih_la} {ih_lb} (qr : VEnvD qD) (qhr : GoodEnvD qD qr) (qx : VD (domSk qsA)) (qhx : GoodD (domSk qsA) qx) => qihgb (vconsD (domSk qsA) qD qx qr) (goodEnvD_vconsD (domSk qsA) qD qx qr qhx qhr))"
    );

    let ih_af = "(qihgf : forall (qr2 : VEnvD qD), GoodEnvD qD qr2 -> GoodD (Sk.arr qd qc) (sval qD qf (Sk.arr qd qc) qhf qr2))";
    let ih_aa =
        "(qihga : forall (qr2 : VEnvD qD), GoodEnvD qD qr2 -> GoodD qd (sval qD qa qd qha qr2))";
    let m_app = format!(
        "(fun (qD : Nat -> Sk) (qf : KExpr) (qa : KExpr) (qd : Sk) (qc : Sk) (qhf : WK qD qf (Sk.arr qd qc)) (qha : WK qD qa qd) {ih_af} {ih_aa} (qr : VEnvD qD) (qhr : GoodEnvD qD qr) => qihgf qr qhr (sval qD qa qd qha qr) (qihga qr qhr))"
    );

    format!(
        "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) => WK.rec {motive} {m_var} {m_sort} {m_pi} {m_lam} {m_app} D e s h"
    )
}

pub(super) const TY_ISCANDHI_SVAL: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D), GoodEnvD D r -> IsCandHI (vcarD s (sval D e s h r))";
pub(super) const VAL_ISCANDHI_SVAL: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D) (hr : GoodEnvD D r) => isCandHI_vcarD s (sval D e s h r) (sval_good D e s h r hr)";

pub(super) const TY_SVAL_MEMBERS_SN: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D), GoodEnvD D r -> forall (x : KExpr), vcarD s (sval D e s h r) x -> whnf_acc x";
pub(super) const VAL_SVAL_MEMBERS_SN: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D) (hr : GoodEnvD D r) => isCandHI_cr1 (vcarD s (sval D e s h r)) (isCandHI_sval D e s h r hr)";

pub(super) const TY_SVAL_EXCLUDES_OMEGA: &str = "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D), GoodEnvD D r -> vcarD s (sval D e s h r) r5_omegaV -> Empty";
pub(super) const VAL_SVAL_EXCLUDES_OMEGA: &str = "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (h : WK D e s) (r : VEnvD D) (hr : GoodEnvD D r) (hm : vcarD s (sval D e s h r) r5_omegaV) => r5_omegaV_not_whnfAcc (sval_members_sn D e s h r hr r5_omegaV hm)";

// --- the semantic beta law: R11's wall, crossed --------------------------

pub(super) const TY_SVAL_BETA: &str = "forall (D : Nat -> Sk) (A : KExpr) (b : KExpr) (a : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK (skcons (domSk sA) D) b c) (ha : WK D a (domSk sA)) (r : VEnvD D), Eq (VD c) (sval D (KExpr.app (KExpr.lam A b) a) c (WK.app D (KExpr.lam A b) a (domSk sA) c (WK.lam D A b sA c hA hb) ha) r) (sval (skcons (domSk sA) D) b c hb (vconsD (domSk sA) D (sval D a (domSk sA) ha r) r))";
pub(super) const VAL_SVAL_BETA: &str = "fun (D : Nat -> Sk) (A : KExpr) (b : KExpr) (a : KExpr) (sA : Sk) (c : Sk) (hA : WK D A sA) (hb : WK (skcons (domSk sA) D) b c) (ha : WK D a (domSk sA)) (r : VEnvD D) => Eq.refl (VD c) (sval (skcons (domSk sA) D) b c hb (vconsD (domSk sA) D (sval D a (domSk sA) ha r) r))";

/// `instantiate (bvar 0) a` IS `a`, at an arbitrary `a`. Not `Eq.refl`:
/// `instantiate_bvar_geq` substitutes the LIFTED value, so the redex's
/// contractum reduces to `lift_at a 0 0`, which is stuck on a variable `a`.
/// `lift_zero_identity` is exactly that lemma, and it is what turns the head
/// beta step below into a step to `a` itself.
pub(super) const TY_BETA_CONTRACTUM_IS_ARG: &str =
    "forall (a : KExpr), Eq KExpr (instantiate (KExpr.bvar Nat.zero) a) a";
pub(super) const VAL_BETA_CONTRACTUM_IS_ARG: &str = "fun (a : KExpr) => lift_zero_identity a";

/// The head beta step of the identity redex, at an ARBITRARY annotation and an
/// ARBITRARY argument, stated at the contractum `a` itself.
pub(super) const TY_BETA_STEP_GENERAL: &str =
    "forall (A : KExpr) (a : KExpr), whnf_step (KExpr.app (KExpr.lam A (KExpr.bvar Nat.zero)) a) a";
pub(super) const VAL_BETA_STEP_GENERAL: &str = "fun (A : KExpr) (a : KExpr) => Eq.substType KExpr (fun (qz : KExpr) => whnf_step (KExpr.app (KExpr.lam A (KExpr.bvar Nat.zero)) a) qz) (instantiate (KExpr.bvar Nat.zero) a) a (r12_beta_contractum_is_arg a) (whnf_step.beta (KExpr.app (KExpr.lam A (KExpr.bvar Nat.zero)) a) (instantiate (KExpr.bvar Nat.zero) a) (beta_reduces.beta A (KExpr.bvar Nat.zero) a))";

/// **THE GENERAL CONVERSION-INVARIANCE STATEMENT.** Paired with
/// `r12_beta_step_general`, which says the LHS's subject takes a real
/// `whnf_step` to the RHS's, this is exactly the class
/// `r11_candInterp_step_conv_refuted` refutes for `candInterp` — at an
/// ARBITRARY shape environment, annotation, argument and valuation, not at one
/// exhibit.
pub(super) const TY_SVAL_BETA_CONTRACTUM: &str = "forall (D : Nat -> Sk) (A : KExpr) (a : KExpr) (sA : Sk) (hA : WK D A sA) (ha : WK D a (domSk sA)) (r : VEnvD D), Eq (VD (domSk sA)) (sval D (KExpr.app (KExpr.lam A (KExpr.bvar Nat.zero)) a) (domSk sA) (WK.app D (KExpr.lam A (KExpr.bvar Nat.zero)) a (domSk sA) (domSk sA) (WK.lam D A (KExpr.bvar Nat.zero) sA (domSk sA) hA (WK.var (skcons (domSk sA) D) Nat.zero)) ha) r) (sval D a (domSk sA) ha r)";
pub(super) const VAL_SVAL_BETA_CONTRACTUM: &str = "fun (D : Nat -> Sk) (A : KExpr) (a : KExpr) (sA : Sk) (hA : WK D A sA) (ha : WK D a (domSk sA)) (r : VEnvD D) => Eq.refl (VD (domSk sA)) (sval D a (domSk sA) ha r)";

pub(super) fn ty_beta_step_witness() -> String {
    format!("whnf_step r12_betaRedex {S0}")
}
pub(super) fn val_beta_step_witness() -> String {
    format!("whnf_step.beta r12_betaRedex {S0} (beta_reduces.beta {V0} {V0} {S0})")
}

pub(super) fn ty_sval_beta_transports() -> String {
    format!("forall (r : VEnvD r12_betaEnv), Eq (VD {KDTY}) (sval r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r) (sval r12_betaEnv {S0} {KDTY} (WK.sort r12_betaEnv Level.zero) r)")
}
pub(super) fn val_sval_beta_transports() -> String {
    format!("fun (r : VEnvD r12_betaEnv) => Eq.refl (VD {KDTY}) (sval r12_betaEnv {S0} {KDTY} (WK.sort r12_betaEnv Level.zero) r)")
}

/// THE CONTRAST, in one kernel-checked constant: R11's refutation of one
/// `whnf_step` of the TYPE through `candInterp`, paired with the same step
/// transported through `sval`.
pub(super) const TY_CONV_CONTRAST: &str =
    "AndType (r12_candInterpStepConv -> Empty) r12_svalTransportsBeta";
pub(super) fn val_conv_contrast() -> String {
    format!("AndType.intro (r12_candInterpStepConv -> Empty) r12_svalTransportsBeta r11_candInterp_step_conv_refuted (fun (qe : KExpr) (qh : vcarD {KDTY} (sval r12_betaEnv r12_betaRedex {KDTY} r12_betaDeriv r12_betaJunkEnv) qe) => qh)")
}

// --- the dependent Pi candidate -----------------------------------------

pub(super) const TY_PICODDEP_INTRO: &str = "forall (D : Nat -> Sk) (d : Sk) (sB : Sk) (GB : VD d -> VD sB) (r : VEnvD D) (w : KExpr), vcarD sB (GB (junkD d)) w -> piCodDepIdx D d sB GB r w -> piCodDep D d sB GB r w";
pub(super) const VAL_PICODDEP_INTRO: &str = "fun (D : Nat -> Sk) (d : Sk) (sB : Sk) (GB : VD d -> VD sB) (r : VEnvD D) (w : KExpr) (hj : vcarD sB (GB (junkD d)) w) (hd : piCodDepIdx D d sB GB r w) => AndType.intro (vcarD sB (GB (junkD d)) w) (piCodDepIdx D d sB GB r w) hj hd";

pub(super) const TY_ISCANDHI_PICODDEP: &str = "forall (D : Nat -> Sk) (d : Sk) (sB : Sk) (GB : VD d -> VD sB) (r : VEnvD D), GoodEnvD D r -> GoodD (Sk.arr d sB) GB -> IsCandHI (piCodDep D d sB GB r)";

pub(super) fn val_iscandhi_picoddep() -> String {
    let jset = "(vcarD sB (GB (junkD d)))";
    let hj = "(isCandHI_vcarD sB (GB (junkD d)) (hG (junkD d) (goodD_junkD d)))";
    let yset = "(vcarD sB (GB (sval D qy d qhy r)))";
    let hy = "(isCandHI_vcarD sB (GB (sval D qy d qhy r)) (hG (sval D qy d qhy r) (sval_good D qy d qhy r hr)))";
    let jc = |w: &str| format!("(vcarD sB (GB (junkD d)) {w})");
    let ix = |w: &str| format!("(piCodDepIdx D d sB GB r {w})");
    let left = |w: &str| format!("AndType.left {} {}", jc(w), ix(w));
    let right = |w: &str| format!("AndType.right {} {}", jc(w), ix(w));
    let f_cr1 = format!(
        "(fun (qw : KExpr) (qh : piCodDep D d sB GB r qw) => isCandHI_cr1 {jset} {hj} qw ({} qh))",
        left("qw")
    );
    let f_cr2 = format!(
        "(fun (qw : KExpr) (qw2 : KExpr) (qh : piCodDep D d sB GB r qw) (qs : whnf_step qw qw2) => AndType.intro {} {} (isCandHI_cr2 {jset} {hj} qw qw2 ({} qh) qs) (fun (qy : KExpr) (qhy : WK D qy d) => isCandHI_cr2 {yset} {hy} qw qw2 ({} qh qy qhy) qs))",
        jc("qw2"),
        ix("qw2"),
        left("qw"),
        right("qw")
    );
    let f_cr3 = format!(
        "(fun (qw : KExpr) (qhi : HeadInert qw) (qhn : Neutral qw) (qhred : forall (qw3 : KExpr), whnf_step qw qw3 -> piCodDep D d sB GB r qw3) => AndType.intro {} {} (isCandHI_cr3 {jset} {hj} qw qhi qhn (fun (qw2 : KExpr) (qs : whnf_step qw qw2) => {} (qhred qw2 qs))) (fun (qy : KExpr) (qhy : WK D qy d) => isCandHI_cr3 {yset} {hy} qw qhi qhn (fun (qw2 : KExpr) (qs : whnf_step qw qw2) => {} (qhred qw2 qs) qy qhy)))",
        jc("qw"),
        ix("qw"),
        left("qw2"),
        right("qw2")
    );
    format!(
        "fun (D : Nat -> Sk) (d : Sk) (sB : Sk) (GB : VD d -> VD sB) (r : VEnvD D) (hr : GoodEnvD D r) (hG : GoodD (Sk.arr d sB) GB) => isCandHI_intro (piCodDep D d sB GB r) {f_cr1} {f_cr2} {f_cr3}"
    )
}

pub(super) const TY_ISCANDHI_PICANDDEP: &str = "forall (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) (r : VEnvD D), IsCandHI CA -> GoodEnvD D r -> GoodD (Sk.arr d sB) GB -> IsCandHI (piCandDep D d sB CA GB r)";
pub(super) const VAL_ISCANDHI_PICANDDEP: &str = "fun (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) (r : VEnvD D) (hCA : IsCandHI CA) (hr : GoodEnvD D r) (hG : GoodD (Sk.arr d sB) GB) => isCandHI_piSet CA (fun (qa : KExpr) => piCodDep D d sB GB r) hCA (fun (qa2 : KExpr) (qm : CA qa2) => isCandHI_piCodDep D d sB GB r hr hG) (fun (qa1 : KExpr) (qa3 : KExpr) (qw : KExpr) (qm1 : CA qa1) (qst : whnf_step qa1 qa3) (qm : piCodDep D d sB GB r qw) => qm)";

pub(super) const TY_PICANDDEP_INTRO: &str = "forall (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) (r : VEnvD D) (t : KExpr), (forall (a : KExpr), CA a -> piCodDep D d sB GB r (KExpr.app t a)) -> piCandDep D d sB CA GB r t";
pub(super) const VAL_PICANDDEP_INTRO: &str = "fun (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) (r : VEnvD D) (t : KExpr) (h : forall (a : KExpr), CA a -> piCodDep D d sB GB r (KExpr.app t a)) => h";

pub(super) const TY_PICANDDEP_ELIM: &str = "forall (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) (r : VEnvD D) (t : KExpr), piCandDep D d sB CA GB r t -> forall (a : KExpr), CA a -> forall (ha : WK D a d), vcarD sB (GB (sval D a d ha r)) (KExpr.app t a)";
pub(super) const VAL_PICANDDEP_ELIM: &str = "fun (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) (r : VEnvD D) (t : KExpr) (ht : piCandDep D d sB CA GB r t) (a : KExpr) (hca : CA a) (ha : WK D a d) => AndType.right (vcarD sB (GB (junkD d)) (KExpr.app t a)) (piCodDepIdx D d sB GB r (KExpr.app t a)) (ht a hca) a ha";

pub(super) const TY_ISCANDHI_WKPIDEP: &str = "forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK (skcons (domSk sA) D) B sB) (r : VEnvD D), GoodEnvD D r -> IsCandHI (wkPiDep D A B sA sB hA hB r)";
pub(super) const VAL_ISCANDHI_WKPIDEP: &str = "fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK (skcons (domSk sA) D) B sB) (r : VEnvD D) (hr : GoodEnvD D r) => isCandHI_piCandDep D (domSk sA) sB (vcarD sA (sval D A sA hA r)) (fun (qv : VD (domSk sA)) => sval (skcons (domSk sA) D) B sB hB (vconsD (domSk sA) D qv r)) r (isCandHI_sval D A sA hA r hr) hr (fun (qx : VD (domSk sA)) (qhx : GoodD (domSk sA) qx) => sval_good (skcons (domSk sA) D) B sB hB (vconsD (domSk sA) D qx r) (goodEnvD_vconsD (domSk sA) D qx r qhx hr))";

/// **THE DEPENDENT ELIMINATION** — `pi_elim` with the codomain read at the
/// ARGUMENT'S OWN interpretation.
pub(super) const TY_WKPIDEP_ELIM: &str = "forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK (skcons (domSk sA) D) B sB) (r : VEnvD D) (t : KExpr), wkPiDep D A B sA sB hA hB r t -> forall (a : KExpr), vcarD sA (sval D A sA hA r) a -> forall (ha : WK D a (domSk sA)), vcarD sB (sval (skcons (domSk sA) D) B sB hB (vconsD (domSk sA) D (sval D a (domSk sA) ha r) r)) (KExpr.app t a)";
pub(super) const VAL_WKPIDEP_ELIM: &str = "fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK (skcons (domSk sA) D) B sB) (r : VEnvD D) (t : KExpr) (ht : wkPiDep D A B sA sB hA hB r t) (a : KExpr) (hca : vcarD sA (sval D A sA hA r) a) (ha : WK D a (domSk sA)) => piCandDep_elim D (domSk sA) sB (vcarD sA (sval D A sA hA r)) (fun (qv : VD (domSk sA)) => sval (skcons (domSk sA) D) B sB hB (vconsD (domSk sA) D qv r)) r t ht a hca ha";

/// THE PREMISE GATE'S SUPPLY FOR `piCodDepIdx`, and a genuine non-vacuity
/// witness for the derivation-indexed intersection: a VARIABLE is in the
/// codomain candidate at every derivation-value at once.
pub(super) const TY_PICODDEPIDX_VAR_WITNESS: &str = "forall (D : Nat -> Sk) (d : Sk) (sB : Sk) (GB : VD d -> VD sB) (r : VEnvD D) (i : Nat), GoodEnvD D r -> GoodD (Sk.arr d sB) GB -> piCodDepIdx D d sB GB r (KExpr.bvar i)";
pub(super) const VAL_PICODDEPIDX_VAR_WITNESS: &str = "fun (D : Nat -> Sk) (d : Sk) (sB : Sk) (GB : VD d -> VD sB) (r : VEnvD D) (i : Nat) (hr : GoodEnvD D r) (hG : GoodD (Sk.arr d sB) GB) (qy : KExpr) (qhy : WK D qy d) => candHF_var_mem (vcarD sB (GB (sval D qy d qhy r))) (isCandHI_weaken (vcarD sB (GB (sval D qy d qhy r))) (isCandHI_vcarD sB (GB (sval D qy d qhy r)) (hG (sval D qy d qhy r) (sval_good D qy d qhy r hr)))) i";

/// THE PREMISE GATE'S SUPPLY FOR `wkPiDep`, and `pi_intro` at the real
/// shape-typing premise pair. Definitional.
pub(super) const TY_WKPIDEP_INTRO: &str = "forall (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK (skcons (domSk sA) D) B sB) (r : VEnvD D) (t : KExpr), (forall (a : KExpr), vcarD sA (sval D A sA hA r) a -> piCodDep D (domSk sA) sB (fun (qv : VD (domSk sA)) => sval (skcons (domSk sA) D) B sB hB (vconsD (domSk sA) D qv r)) r (KExpr.app t a)) -> wkPiDep D A B sA sB hA hB r t";
pub(super) const VAL_WKPIDEP_INTRO: &str = "fun (D : Nat -> Sk) (A : KExpr) (B : KExpr) (sA : Sk) (sB : Sk) (hA : WK D A sA) (hB : WK (skcons (domSk sA) D) B sB) (r : VEnvD D) (t : KExpr) (h : forall (a : KExpr), vcarD sA (sval D A sA hA r) a -> piCodDep D (domSk sA) sB (fun (qv : VD (domSk sA)) => sval (skcons (domSk sA) D) B sB hB (vconsD (domSk sA) D qv r)) r (KExpr.app t a)) => h";

/// THE PREMISE GATE'S SUPPLY FOR `piCandV`: the corpus's value-quantified
/// clause is inhabited by exactly its defining condition. Definitional, and at
/// `Type 1` like the clause itself.
pub(super) const TY_PICANDV_INTRO: &str = "forall (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) (t : KExpr), (forall (a : KExpr), CA a -> forall (v : VD d), GoodD d v -> vcarD sB (GB v) (KExpr.app t a)) -> piCandV D d sB CA GB t";
pub(super) const VAL_PICANDV_INTRO: &str = "fun (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) (t : KExpr) (h : forall (a : KExpr), CA a -> forall (v : VD d), GoodD d v -> vcarD sB (GB v) (KExpr.app t a)) => h";

pub(super) const TY_PICANDV_ELIM: &str = "forall (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) (t : KExpr), piCandV D d sB CA GB t -> forall (a : KExpr), CA a -> forall (v : VD d), GoodD d v -> vcarD sB (GB v) (KExpr.app t a)";
pub(super) const VAL_PICANDV_ELIM: &str = "fun (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) (GB : VD d -> VD sB) (t : KExpr) (h : piCandV D d sB CA GB t) (a : KExpr) (hca : CA a) (v : VD d) (hv : GoodD d v) => h a hca v hv";

// --- witnesses -----------------------------------------------------------

/// The three `WK` witnesses are registered as plain DEFS, not as theorems, and
/// that is load-bearing rather than cosmetic. Measured 2026-08-27: a witness
/// registered through `add_definition` does not delta-unfold in the
/// elaborator's whnf, so `sval .. r12_wk_pi_witness ..` stayed stuck at a
/// `WK.rec` spine and `r12_sval_pi_proper` died with "Too many arguments".
/// Anything a later proof must REDUCE THROUGH has to be a def.
pub(super) fn src_wk_sort_witness() -> String {
    "def r12_wk_sort_witness (D : Nat -> Sk) (n : Level) : WK D (KExpr.sort n) (Sk.kd Sk.ty) := WK.sort D n".to_string()
}

pub(super) fn src_wk_id_witness() -> String {
    format!("def r12_wk_id_witness (D : Nat -> Sk) : WK D (KExpr.lam {S0} {V0}) (Sk.arr Sk.ty Sk.ty) := WK.lam D {S0} {V0} {KDTY} Sk.ty (WK.sort D Level.zero) (WK.var (skcons Sk.ty D) Nat.zero)")
}

pub(super) fn src_wk_pi_witness() -> String {
    format!("def r12_wk_pi_witness : WK r12_piEnv {PI00} (piShape {KDTY} {KDTY}) := WK.pi r12_piEnv {S0} {S0} {KDTY} {KDTY} (WK.sort r12_piEnv Level.zero) (WK.sort (skcons Sk.ty r12_piEnv) Level.zero)")
}

fn pi_witness_set() -> String {
    format!("(vcarD (piShape {KDTY} {KDTY}) (sval r12_piEnv {PI00} (piShape {KDTY} {KDTY}) r12_wk_pi_witness r))")
}

/// THE NON-DEGENERACY GUARD, R5's `candInterp_pi_not_total` at this
/// interpretation: `r5_omegaLam` is `whnf_acc` and is NOT in the Pi type's
/// interpretation.
pub(super) fn ty_sval_pi_proper() -> String {
    let s = pi_witness_set();
    format!("forall (r : VEnvD r12_piEnv), {s} r5_omegaLam -> Empty")
}
pub(super) fn val_sval_pi_proper() -> String {
    let s = pi_witness_set();
    format!("fun (r : VEnvD r12_piEnv) (h : {s} r5_omegaLam) => r5_omegaV_not_whnfAcc (h r5_omegaLam r5_whnfAcc_omegaLam)")
}

/// ...and the positive half of the same guard: the interpretation is not EMPTY
/// either — every variable inhabits it, through R5's `candHF_var_mem`.
pub(super) fn ty_sval_pi_var_witness() -> String {
    let s = pi_witness_set();
    format!("forall (r : VEnvD r12_piEnv), GoodEnvD r12_piEnv r -> {s} {V0}")
}
pub(super) fn val_sval_pi_var_witness() -> String {
    let s = pi_witness_set();
    format!("fun (r : VEnvD r12_piEnv) (hr : GoodEnvD r12_piEnv r) => candHF_var_mem {s} (isCandHI_weaken {s} (isCandHI_sval r12_piEnv {PI00} (piShape {KDTY} {KDTY}) r12_wk_pi_witness r hr)) Nat.zero")
}

// ================================================================
// The tables the registration half and the parse harness both read.
// ================================================================

/// Every declaration-shaped source of the rung, in registration order, as
/// `(kind, name, source)` where `kind` is `"inductive"` or `"def"`.
pub(super) fn r12_decl_sources() -> Vec<(&'static str, String, String)> {
    let d = |n: &str, s: &str| ("def", n.to_string(), s.to_string());
    vec![
        ("inductive", "Sk".to_string(), SRC_SK.to_string()),
        d("domSk", SRC_DOM_SK),
        d("piShape", SRC_PI_SHAPE),
        d("VD", SRC_VD),
        d("vcarD", SRC_VCAR_D),
        d("mkTyD", SRC_MK_TY_D),
        d("junkD", SRC_JUNK_D),
        d("GoodSet", SRC_GOOD_SET),
        d("GoodD", SRC_GOOD_D),
        ("inductive", "Val".to_string(), SRC_VAL.to_string()),
        d("valS", SRC_VAL_S),
        d("valD", SRC_VAL_D),
        d("valCar", SRC_VAL_CAR),
        d("valGood", SRC_VAL_GOOD),
        d("valJunk", SRC_VAL_JUNK),
        d("skcons", SRC_SKCONS),
        d("VEnvD", SRC_VENV_D),
        d("vconsD", SRC_VCONS_D),
        d("GoodEnvD", SRC_GOOD_ENV_D),
        ("inductive", "WK".to_string(), SRC_WK.to_string()),
        ("def", "sval".to_string(), src_sval()),
        d("piCodDepIdx", SRC_PI_COD_DEP_IDX),
        d("piCodDep", SRC_PI_COD_DEP),
        d("piCandDep", SRC_PI_CAND_DEP),
        d("wkPiDep", SRC_WK_PI_DEP),
        d("piCandV", SRC_PI_CAND_V),
        d("r12_betaEnv", SRC_BETA_ENV),
        d("r12_betaRedex", SRC_BETA_REDEX),
        d("r12_betaJunkEnv", SRC_BETA_JUNK_ENV),
        ("def", "r12_betaDeriv".to_string(), src_beta_deriv()),
        d("r12_candInterpStepConv", SRC_CANDINTERP_STEP_CONV),
        (
            "def",
            "r12_svalTransportsBeta".to_string(),
            src_sval_transports_beta(),
        ),
        d("r12_piEnv", SRC_PI_ENV),
        d("r12_junkEnv", SRC_JUNK_ENV),
        (
            "def",
            "r12_wk_sort_witness".to_string(),
            src_wk_sort_witness(),
        ),
        ("def", "r12_wk_id_witness".to_string(), src_wk_id_witness()),
        ("def", "r12_wk_pi_witness".to_string(), src_wk_pi_witness()),
    ]
}

/// Every theorem of the rung, in registration order, as `(name, type, value)`.
pub(super) fn r12_theorem_sources() -> Vec<(String, String, String)> {
    let t = |n: &str, ty: &str, v: &str| (n.to_string(), ty.to_string(), v.to_string());
    vec![
        t("goodSet_up", TY_GOODSET_UP, VAL_GOODSET_UP),
        (
            "goodSet_down".to_string(),
            TY_GOODSET_DOWN.to_string(),
            val_goodset_down(),
        ),
        (
            "goodSet_whnfAcc".to_string(),
            ty_goodset_whnfacc(),
            val_goodset_whnfacc(),
        ),
        t("vcarD_mkTyD", TY_VCARD_MKTYD, VAL_VCARD_MKTYD),
        t("goodD_mkTyD", TY_GOODD_MKTYD, VAL_GOODD_MKTYD),
        t("goodD_junkD", TY_GOODD_JUNKD, VAL_GOODD_JUNKD),
        t("isCandHI_vcarD", TY_ISCANDHI_VCARD, VAL_ISCANDHI_VCARD),
        t("goodEnvD_vconsD", TY_GOODENVD_VCONSD, VAL_GOODENVD_VCONSD),
        t("goodEnvD_junk", TY_GOODENVD_JUNK, VAL_GOODENVD_JUNK),
        t("valGood_junk", TY_VALGOOD_JUNK, VAL_VALGOOD_JUNK),
        t("isCandHI_valCar", TY_ISCANDHI_VALCAR, VAL_ISCANDHI_VALCAR),
        (
            "sval_good".to_string(),
            TY_SVAL_GOOD.to_string(),
            val_sval_good(),
        ),
        t("isCandHI_sval", TY_ISCANDHI_SVAL, VAL_ISCANDHI_SVAL),
        t("sval_members_sn", TY_SVAL_MEMBERS_SN, VAL_SVAL_MEMBERS_SN),
        t(
            "r12_sval_excludes_omega",
            TY_SVAL_EXCLUDES_OMEGA,
            VAL_SVAL_EXCLUDES_OMEGA,
        ),
        t("r12_sval_beta", TY_SVAL_BETA, VAL_SVAL_BETA),
        t(
            "r12_beta_contractum_is_arg",
            TY_BETA_CONTRACTUM_IS_ARG,
            VAL_BETA_CONTRACTUM_IS_ARG,
        ),
        t(
            "r12_beta_step_general",
            TY_BETA_STEP_GENERAL,
            VAL_BETA_STEP_GENERAL,
        ),
        t(
            "r12_sval_beta_contractum",
            TY_SVAL_BETA_CONTRACTUM,
            VAL_SVAL_BETA_CONTRACTUM,
        ),
        (
            "r12_beta_step_witness".to_string(),
            ty_beta_step_witness(),
            val_beta_step_witness(),
        ),
        (
            "r12_sval_beta_transports".to_string(),
            ty_sval_beta_transports(),
            val_sval_beta_transports(),
        ),
        (
            "r12_conv_contrast".to_string(),
            TY_CONV_CONTRAST.to_string(),
            val_conv_contrast(),
        ),
        t("piCodDep_intro", TY_PICODDEP_INTRO, VAL_PICODDEP_INTRO),
        (
            "isCandHI_piCodDep".to_string(),
            TY_ISCANDHI_PICODDEP.to_string(),
            val_iscandhi_picoddep(),
        ),
        t(
            "piCodDepIdx_var_witness",
            TY_PICODDEPIDX_VAR_WITNESS,
            VAL_PICODDEPIDX_VAR_WITNESS,
        ),
        t(
            "isCandHI_piCandDep",
            TY_ISCANDHI_PICANDDEP,
            VAL_ISCANDHI_PICANDDEP,
        ),
        t("piCandDep_intro", TY_PICANDDEP_INTRO, VAL_PICANDDEP_INTRO),
        t("piCandDep_elim", TY_PICANDDEP_ELIM, VAL_PICANDDEP_ELIM),
        t(
            "isCandHI_wkPiDep",
            TY_ISCANDHI_WKPIDEP,
            VAL_ISCANDHI_WKPIDEP,
        ),
        t("wkPiDep_intro", TY_WKPIDEP_INTRO, VAL_WKPIDEP_INTRO),
        t("wkPiDep_elim", TY_WKPIDEP_ELIM, VAL_WKPIDEP_ELIM),
        t("piCandV_intro", TY_PICANDV_INTRO, VAL_PICANDV_INTRO),
        t("piCandV_elim", TY_PICANDV_ELIM, VAL_PICANDV_ELIM),
        (
            "r12_sval_pi_proper".to_string(),
            ty_sval_pi_proper(),
            val_sval_pi_proper(),
        ),
        (
            "r12_sval_pi_var_witness".to_string(),
            ty_sval_pi_var_witness(),
            val_sval_pi_var_witness(),
        ),
    ]
}

/// Every source of the rung as a full declaration, for the parse harness and
/// the battery. Not consumed by the registration itself, which iterates the two
/// tables directly so every constant keeps its own description.
#[cfg(test)]
pub(super) fn r12_all_sources() -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = r12_decl_sources()
        .into_iter()
        .map(|(_, n, s)| (n, s))
        .collect();
    for (name, ty, val) in r12_theorem_sources() {
        let src = format!("def {name} : {ty} := {val}");
        out.push((name, src));
    }
    out
}
