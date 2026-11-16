// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R13 sources — `funext`, DERIVED in the spec's own source language.
//!
//! This module deliberately imports nothing, so the pre-validation parse
//! harness can `#[path]`-include it into a scratch crate that depends only on
//! `clean-parser`.
//!
//! Every source here is written against the SPEC's `Eq`
//! (`inductive Eq (α : Sort u) : α → α → Prop`, type argument EXPLICIT) and the
//! SPEC's `Eq.cong`
//! (`forall (α : Sort u) (β : Sort v) (f : α -> β) (a : α) (b : α), Eq α a b ->
//! Eq β (f a) (f b)`, every argument explicit) — not against the kernel's
//! implicit-`α` `congrArg`. The quotient primitives are used through `@`
//! explicit application for the same reason: nothing here depends on
//! higher-order implicit solving.

/// The dependent function space `forall (x : A), B x`, parenthesised for
/// argument position. Spelled once so every consumer is byte-identical.
pub(super) const TFN: &str = "(forall (x : A), B x)";

/// The same type with the bound variable renamed, for the places where `x` is
/// already taken by an enclosing binder (`spec_fnapp`'s own `x`).
pub(super) const TFNY: &str = "(forall (y : A), B y)";

/// The pointwise-equality hypothesis, unparenthesised (binder position).
pub(super) const HPW: &str = "forall (x : A), @Eq (B x) (f x) (g x)";

/// The universe-polymorphic binder prefix shared by every R13 constant.
pub(super) const AB: &str = "(A : Sort u) (B : A -> Sort v)";

// ================================================================
// Group 1 — the quotient construction.
//
// `spec_fneq` is extensional equality on the dependent function space; it is
// `Prop`-valued because `Quot`'s relation argument is fixed at `Prop`
// (`Quot.{u} : {α : Sort u} → (r : α → α → Prop) → Sort u`), and
// `forall (x : A), <Prop>` lands in `Sort (imax u 0) = Prop` however big `u`
// is. That single fact is why the derivation survives the spec's
// `Type`-valued candidates: nothing here asks a `Type` to be a `Prop`.
//
// All three go through `add_recursive_def` — they are `Declaration::Definition`
// and therefore DELTA-UNFOLD in the elaborator's whnf. That is load-bearing,
// not stylistic: `spec_funext`'s kernel check has to reduce
// `spec_fnapp A B (Quot.mk (spec_fneq A B) f)` all the way to `f`, and an
// `add_definition`-registered constant lowers to `Declaration::Opaque` and
// would stop that reduction dead.
// ================================================================

/// `spec_fneq A B f g` — `f` and `g` agree pointwise. The relation the function
/// space is quotiented by.
pub(super) fn src_fneq() -> String {
    format!("def spec_fneq {AB} (f : {TFN}) (g : {TFN}) : Prop := {HPW}")
}

/// `spec_fnapp` — the application map out of the quotient, `Quot.liftOn` at the
/// point `x`. This is the whole trick: the lift's respect obligation at `x` is
/// discharged by the pointwise hypothesis AT `x`, so the map exists without any
/// choice principle.
///
/// `spec_fnapp A B (Quot.mk (spec_fneq A B) c)` ι-reduces (the `Quot.lift`
/// computation rule, `clean-kernel/src/quot.rs:598`) to `fun (x : A) => c x`,
/// which is `c` by function eta (`clean-kernel/src/tc/eta.rs`). Those two
/// kernel facts are the only reason the theorem below type-checks.
pub(super) fn src_fnapp() -> String {
    format!(
        "def spec_fnapp {AB} (q : @Quot {TFN} (spec_fneq A B)) (x : A) : B x := \
         @Quot.lift {TFNY} (spec_fneq A B) (B x) \
         (fun (phi : {TFNY}) => phi x) \
         (fun (a : {TFNY}) (b : {TFNY}) (hab : spec_fneq A B a b) => hab x) \
         q"
    )
}

/// `spec_quot_fn` — a registered DEFINITION concluding in `@Quot ...`.
///
/// The premise-witness gate excludes axioms from the supply side, and `Quot` is
/// an axiom (a CIC type former), so a hypothesis whose head is `Quot` — which
/// `spec_fnapp`'s own `q` binder is — needs a concluding definition or the gate
/// records it as an assumed-but-never-established premise. This is that
/// definition, and it doubles as the quotient's introduction form.
pub(super) fn src_quot_fn() -> String {
    format!(
        "def spec_quot_fn {AB} (f : {TFN}) : @Quot {TFN} (spec_fneq A B) := \
         @Quot.mk {TFN} (spec_fneq A B) f"
    )
}

// ================================================================
// Group 2 — the theorems. Registered with `add_definition`, so the kernel's
// `add_decl` type-checks each proof term against its declared type.
// ================================================================

/// `spec_fneq_intro` — the concluding definition for `spec_fneq`, which
/// `spec_fnapp`'s respect-proof binder assumes. `fun ... h => h` is a genuine
/// proof, not a restatement: it is the delta-unfolding of `spec_fneq`.
pub(super) fn ty_fneq_intro() -> String {
    format!("forall {AB} (f : {TFN}) (g : {TFN}), ({HPW}) -> spec_fneq A B f g")
}

pub(super) fn val_fneq_intro() -> String {
    format!("fun {AB} (f : {TFN}) (g : {TFN}) (h : {HPW}) => h")
}

/// `spec_fneq_elim` — the other direction, so `spec_fneq` is pinned as exactly
/// pointwise equality and not something weaker that happens to be inhabited.
pub(super) fn ty_fneq_elim() -> String {
    format!("forall {AB} (f : {TFN}) (g : {TFN}), spec_fneq A B f g -> ({HPW})")
}

pub(super) fn val_fneq_elim() -> String {
    format!("fun {AB} (f : {TFN}) (g : {TFN}) (h : spec_fneq A B f g) => h")
}

/// **`spec_funext`** — function extensionality, DERIVED.
///
/// `Eq.cong` at `spec_fnapp` transports `Quot.sound`'s equality of the two
/// classes to an equality of their applications, and both applications reduce
/// (quotient ι, then beta, then eta) to the functions themselves. Exactly Lean
/// 4 core's derivation, written in the spec's own source language against the
/// spec's own explicit-argument `Eq.cong`.
///
/// Axiom closure: `Quot.sound` (foundational) plus the `Quot`/`Quot.mk`/
/// `Quot.lift` type formers, every one of them already inside
/// `spec_axiom_closure::EXPLICIT_FOUNDATIONAL_BASE`. ZERO new axioms, zero
/// residual DerivedProved debt.
pub(super) fn ty_funext() -> String {
    format!("forall {AB} (f : {TFN}) (g : {TFN}), ({HPW}) -> @Eq {TFN} f g")
}

pub(super) fn val_funext() -> String {
    format!(
        "fun {AB} (f : {TFN}) (g : {TFN}) (h : {HPW}) => \
         @Eq.cong (@Quot {TFN} (spec_fneq A B)) {TFN} (spec_fnapp A B) \
         (@Quot.mk {TFN} (spec_fneq A B) f) \
         (@Quot.mk {TFN} (spec_fneq A B) g) \
         (@Quot.sound {TFN} (spec_fneq A B) f g h)"
    )
}

/// `spec_funext_nd` — the non-dependent corollary, `B := fun _ => C`. Every
/// R12 semantic function lives here: `VD (arr d c) = VD d -> VD c` is a plain
/// function space, so this is the form part B actually applies.
pub(super) const TY_FUNEXT_ND: &str =
    "forall (A : Sort u) (C : Sort v) (f : A -> C) (g : A -> C), \
     (forall (x : A), @Eq C (f x) (g x)) -> @Eq (A -> C) f g";

pub(super) const VAL_FUNEXT_ND: &str = "fun (A : Sort u) (C : Sort v) (f : A -> C) (g : A -> C) \
     (h : forall (x : A), @Eq C (f x) (g x)) => \
     spec_funext A (fun (qx : A) => C) f g h";

/// `spec_funext_witness` — NON-VACUITY, at two functions the kernel does NOT
/// hold definitionally equal.
///
/// `Nat.add` recurses on its SECOND argument (`foundation_types.rs:525`), so
/// `Nat.add Nat.zero n` is stuck on the variable `n` and
/// `fun (n : Nat) => Nat.add Nat.zero n` is not def-eq to `fun (n : Nat) => n`.
/// `nat_zero_add` supplies the pointwise proof by induction; `spec_funext_nd`
/// turns it into the equality of the two functions. The companion refusal test
/// `test_candmodel_r13_reflexivity_is_refused_at_the_witness` measures the
/// other half — `Eq.refl` at that very statement is REJECTED by the kernel — so
/// this constant records work that funext genuinely did.
pub(super) const TY_FUNEXT_WITNESS: &str =
    "@Eq (Nat -> Nat) (fun (n : Nat) => Nat.add Nat.zero n) (fun (n : Nat) => n)";

pub(super) const VAL_FUNEXT_WITNESS: &str =
    "spec_funext_nd Nat Nat (fun (n : Nat) => Nat.add Nat.zero n) (fun (n : Nat) => n) \
     (fun (n : Nat) => nat_zero_add n)";

/// The same statement with a reflexivity proof. NOT registered — it is the
/// negative control the refusal test feeds to `add_definition`.
#[cfg(test)]
pub(super) const VAL_FUNEXT_WITNESS_REFL_PROBE: &str =
    "@Eq.refl (Nat -> Nat) (fun (n : Nat) => Nat.add Nat.zero n)";

// ================================================================
// Group 3 — PART B: the R12 wall.
//
// R12 recorded, and `dependent_sn_richmodel.rs:664` recorded before it, that
// the corpus's `val_psub` / `val_lift` / the `piB`-`lamB` cases of `val_step`
// "equate two SEMANTIC FUNCTIONS that agree pointwise" and that the spec's
// funext-free pointwise congruence cannot substitute there because the objects
// being equated ARE functions. These are those substitutions, with the
// functions being R12's own `VD (arr d c)` and `VEnvD D`.
// ================================================================

/// `r13_vd_arr_funext` — extensionality for a semantic function at an ARROW
/// shape. `VD (Sk.arr d c)` ι-reduces to `VD d -> VD c` (`SRC_VD`), so this is
/// `spec_funext_nd` read through R12's large elimination.
pub(super) const TY_VD_ARR_FUNEXT: &str =
    "forall (d : Sk) (c : Sk) (F : VD (Sk.arr d c)) (G : VD (Sk.arr d c)), \
     (forall (a : VD d), @Eq (VD c) (F a) (G a)) -> @Eq (VD (Sk.arr d c)) F G";

pub(super) const VAL_VD_ARR_FUNEXT: &str =
    "fun (d : Sk) (c : Sk) (F : VD (Sk.arr d c)) (G : VD (Sk.arr d c)) \
     (h : forall (a : VD d), @Eq (VD c) (F a) (G a)) => \
     spec_funext_nd (VD d) (VD c) F G h";

/// `r13_venvD_funext` — extensionality for a VALUATION. `VEnvD D` is the
/// DEPENDENT function space `forall (qi : Nat), VD (D qi)` (R12's deliberate
/// divergence from the corpus), so this one needs the dependent `spec_funext`
/// and not the corollary.
pub(super) const TY_VENVD_FUNEXT: &str = "forall (D : Nat -> Sk) (r : VEnvD D) (r2 : VEnvD D), \
     (forall (i : Nat), @Eq (VD (D i)) (r i) (r2 i)) -> @Eq (VEnvD D) r r2";

pub(super) const VAL_VENVD_FUNEXT: &str = "fun (D : Nat -> Sk) (r : VEnvD D) (r2 : VEnvD D) \
     (h : forall (i : Nat), @Eq (VD (D i)) (r i) (r2 i)) => \
     spec_funext Nat (fun (qi : Nat) => VD (D qi)) r r2 h";

/// **`r13_sval_env_congr`** — the interpretation respects pointwise-equal
/// valuations, at EVERY shape environment, term, shape and derivation.
///
/// This is the lemma R12 could not state: pointwise agreement of `r` and `r2`
/// is not substitutable into `sval` because a valuation IS a function.
/// `r13_venvD_funext` converts it to an equality of valuations and one
/// `Eq.cong` finishes. It is the engine the corpus's `val_psub` / `val_lift`
/// run on.
pub(super) const TY_SVAL_ENV_CONGR: &str =
    "forall (D : Nat -> Sk) (e : KExpr) (s : Sk) (hw : WK D e s) (r : VEnvD D) (r2 : VEnvD D), \
     (forall (i : Nat), @Eq (VD (D i)) (r i) (r2 i)) -> \
     @Eq (VD s) (sval D e s hw r) (sval D e s hw r2)";

pub(super) const VAL_SVAL_ENV_CONGR: &str =
    "fun (D : Nat -> Sk) (e : KExpr) (s : Sk) (hw : WK D e s) (r : VEnvD D) (r2 : VEnvD D) \
     (h : forall (i : Nat), @Eq (VD (D i)) (r i) (r2 i)) => \
     @Eq.cong (VEnvD D) (VD s) (fun (qr : VEnvD D) => sval D e s hw qr) r r2 \
     (r13_venvD_funext D r r2 h)";

/// `r13_vconsD_env_congr` — the valuation-extension respects equal valuations,
/// so the congruence engine survives going under a binder. `vconsD s D v r`
/// inhabits `VEnvD (skcons s D)` definitionally, which is what lets one
/// `Eq.cong` carry the equality across the extension.
pub(super) const TY_VCONSD_ENV_CONGR: &str =
    "forall (s : Sk) (D : Nat -> Sk) (v : VD s) (r : VEnvD D) (r2 : VEnvD D), \
     @Eq (VEnvD D) r r2 -> \
     @Eq (VEnvD (skcons s D)) (vconsD s D v r) (vconsD s D v r2)";

pub(super) const VAL_VCONSD_ENV_CONGR: &str =
    "fun (s : Sk) (D : Nat -> Sk) (v : VD s) (r : VEnvD D) (r2 : VEnvD D) \
     (heq : @Eq (VEnvD D) r r2) => \
     @Eq.cong (VEnvD D) (VEnvD (skcons s D)) (fun (qr : VEnvD D) => vconsD s D v qr) r r2 heq";

/// **`r13_piCandDep_fn_congr`** — the `piB` congruence case, at R12's dependent
/// Pi candidate.
///
/// The corpus proves this with `piVal_congr`, whose proof is `funext` AND
/// `propext` — and R12 recorded that `propext` is unusable for a `Type`-valued
/// candidate. It is not needed: with genuine funext on the semantic function
/// `GB`, the congruence is a single `Eq.cong` in the FUNCTION argument, never a
/// biimplication between two `Type`s. That is a strictly better route than the
/// corpus's, not a workaround.
pub(super) const TY_PICANDDEP_FN_CONGR: &str =
    "forall (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) \
     (GB : VD d -> VD sB) (GB2 : VD d -> VD sB) (r : VEnvD D), \
     (forall (a : VD d), @Eq (VD sB) (GB a) (GB2 a)) -> \
     @Eq (KExpr -> Type) (piCandDep D d sB CA GB r) (piCandDep D d sB CA GB2 r)";

pub(super) const VAL_PICANDDEP_FN_CONGR: &str =
    "fun (D : Nat -> Sk) (d : Sk) (sB : Sk) (CA : KExpr -> Type) \
     (GB : VD d -> VD sB) (GB2 : VD d -> VD sB) (r : VEnvD D) \
     (h : forall (a : VD d), @Eq (VD sB) (GB a) (GB2 a)) => \
     @Eq.cong (VD d -> VD sB) (KExpr -> Type) \
     (fun (qG : VD d -> VD sB) => piCandDep D d sB CA qG r) GB GB2 \
     (spec_funext_nd (VD d) (VD sB) GB GB2 h)";

/// `r13_wkPiDep_env_congr` — the same congruence at the constructed dependent
/// Pi clause `wkPiDep`, in the valuation. `wkPiDep` reads `sval` at BOTH the
/// domain and the extended-valuation codomain, so this is the composite the
/// `piB` case of `val_step` needs, and it exists only because a valuation can
/// now be substituted.
pub(super) const TY_WKPIDEP_ENV_CONGR: &str =
    "forall (D : Nat -> Sk) (A : KExpr) (Bd : KExpr) (sA : Sk) (sB : Sk) \
     (hA : WK D A sA) (hB : WK (skcons (domSk sA) D) Bd sB) (r : VEnvD D) (r2 : VEnvD D), \
     (forall (i : Nat), @Eq (VD (D i)) (r i) (r2 i)) -> \
     @Eq (KExpr -> Type) (wkPiDep D A Bd sA sB hA hB r) (wkPiDep D A Bd sA sB hA hB r2)";

pub(super) const VAL_WKPIDEP_ENV_CONGR: &str =
    "fun (D : Nat -> Sk) (A : KExpr) (Bd : KExpr) (sA : Sk) (sB : Sk) \
     (hA : WK D A sA) (hB : WK (skcons (domSk sA) D) Bd sB) (r : VEnvD D) (r2 : VEnvD D) \
     (h : forall (i : Nat), @Eq (VD (D i)) (r i) (r2 i)) => \
     @Eq.cong (VEnvD D) (KExpr -> Type) \
     (fun (qr : VEnvD D) => wkPiDep D A Bd sA sB hA hB qr) r r2 \
     (r13_venvD_funext D r r2 h)";

/// `r13_sval_env_congr_witness` — the B lemmas at a REGISTERED derivation, so
/// their premises are visibly satisfiable and their conclusions visibly
/// inhabited. `r12_wk_sort_witness` is R12's own sort derivation and
/// `r12_junkEnv` its own valuation; `Eq.refl` at every index supplies the
/// pointwise premise.
pub(super) const TY_SVAL_ENV_CONGR_WITNESS: &str = "@Eq (VD (Sk.kd Sk.ty)) \
     (sval r12_piEnv (KExpr.sort Level.zero) (Sk.kd Sk.ty) \
      (r12_wk_sort_witness r12_piEnv Level.zero) (r12_junkEnv r12_piEnv)) \
     (sval r12_piEnv (KExpr.sort Level.zero) (Sk.kd Sk.ty) \
      (r12_wk_sort_witness r12_piEnv Level.zero) (r12_junkEnv r12_piEnv))";

pub(super) const VAL_SVAL_ENV_CONGR_WITNESS: &str =
    "r13_sval_env_congr r12_piEnv (KExpr.sort Level.zero) (Sk.kd Sk.ty) \
     (r12_wk_sort_witness r12_piEnv Level.zero) (r12_junkEnv r12_piEnv) \
     (r12_junkEnv r12_piEnv) \
     (fun (i : Nat) => @Eq.refl (VD (r12_piEnv i)) (r12_junkEnv r12_piEnv i))";

/// `r13_vd_arr_funext_witness` — the arrow-shape extensionality at a concrete
/// shape, through `junkD`. `VD (Sk.arr Sk.ty Sk.ty)` is a real semantic
/// function space and `junkD` inhabits it, so the lemma is applied, not merely
/// stated.
pub(super) const TY_VD_ARR_FUNEXT_WITNESS: &str =
    "@Eq (VD (Sk.arr Sk.ty Sk.ty)) (junkD (Sk.arr Sk.ty Sk.ty)) (junkD (Sk.arr Sk.ty Sk.ty))";

pub(super) const VAL_VD_ARR_FUNEXT_WITNESS: &str =
    "r13_vd_arr_funext Sk.ty Sk.ty (junkD (Sk.arr Sk.ty Sk.ty)) (junkD (Sk.arr Sk.ty Sk.ty)) \
     (fun (a : VD Sk.ty) => @Eq.refl (VD Sk.ty) (junkD (Sk.arr Sk.ty Sk.ty) a))";

/// The R12-blocked statement with a REFLEXIVITY proof, the negative control for
/// `test_candmodel_r13_pointwise_does_not_substitute`. NOT registered.
#[cfg(test)]
pub(super) fn probe_pointwise_refl() -> String {
    format!(
        "def r13_pointwise_refl_probe {AB} (f : {TFN}) (g : {TFN}) (h : {HPW}) : @Eq {TFN} f g := \
         @Eq.refl {TFN} f"
    )
}

// ================================================================
// The registration tables.
// ================================================================

/// `(kind, name, source)` for every R13 declaration handled by
/// `add_inductive` / `add_recursive_def`, in registration order.
pub(super) fn r13_decl_sources() -> Vec<(&'static str, String, String)> {
    vec![
        ("def", "spec_fneq".to_string(), src_fneq()),
        ("def", "spec_fnapp".to_string(), src_fnapp()),
        ("def", "spec_quot_fn".to_string(), src_quot_fn()),
    ]
}

/// `(name, type, value)` for every R13 theorem, in registration order.
pub(super) fn r13_theorem_sources() -> Vec<(String, String, String)> {
    let t = |n: &str, ty: String, v: String| (n.to_string(), ty, v);
    vec![
        t("spec_fneq_intro", ty_fneq_intro(), val_fneq_intro()),
        t("spec_fneq_elim", ty_fneq_elim(), val_fneq_elim()),
        t("spec_funext", ty_funext(), val_funext()),
        t(
            "spec_funext_nd",
            TY_FUNEXT_ND.to_string(),
            VAL_FUNEXT_ND.to_string(),
        ),
        t(
            "spec_funext_witness",
            TY_FUNEXT_WITNESS.to_string(),
            VAL_FUNEXT_WITNESS.to_string(),
        ),
        t(
            "r13_vd_arr_funext",
            TY_VD_ARR_FUNEXT.to_string(),
            VAL_VD_ARR_FUNEXT.to_string(),
        ),
        t(
            "r13_venvD_funext",
            TY_VENVD_FUNEXT.to_string(),
            VAL_VENVD_FUNEXT.to_string(),
        ),
        t(
            "r13_sval_env_congr",
            TY_SVAL_ENV_CONGR.to_string(),
            VAL_SVAL_ENV_CONGR.to_string(),
        ),
        t(
            "r13_vconsD_env_congr",
            TY_VCONSD_ENV_CONGR.to_string(),
            VAL_VCONSD_ENV_CONGR.to_string(),
        ),
        t(
            "r13_piCandDep_fn_congr",
            TY_PICANDDEP_FN_CONGR.to_string(),
            VAL_PICANDDEP_FN_CONGR.to_string(),
        ),
        t(
            "r13_wkPiDep_env_congr",
            TY_WKPIDEP_ENV_CONGR.to_string(),
            VAL_WKPIDEP_ENV_CONGR.to_string(),
        ),
        t(
            "r13_sval_env_congr_witness",
            TY_SVAL_ENV_CONGR_WITNESS.to_string(),
            VAL_SVAL_ENV_CONGR_WITNESS.to_string(),
        ),
        t(
            "r13_vd_arr_funext_witness",
            TY_VD_ARR_FUNEXT_WITNESS.to_string(),
            VAL_VD_ARR_FUNEXT_WITNESS.to_string(),
        ),
    ]
}

/// Every R13 source as a single parse-checkable `def`, for the parse gate and
/// the drift-proof premise test. Test-only: registration walks the two tables
/// separately so each constant keeps its own description.
#[cfg(test)]
pub(super) fn r13_all_sources() -> Vec<(String, String)> {
    let mut all: Vec<(String, String)> = r13_decl_sources()
        .into_iter()
        .map(|(_, n, s)| (n, s))
        .collect();
    for (name, ty, val) in r13_theorem_sources() {
        all.push((name.clone(), format!("def {name} : {ty} := {val}")));
    }
    all
}
