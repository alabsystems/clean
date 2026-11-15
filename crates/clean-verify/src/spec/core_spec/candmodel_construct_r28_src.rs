// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R28 sources — **THE TYPE VOCABULARY A TERM JUDGMENT NEEDS**: `InertTy`, the
//! `ty`-shaped types built from inert reflected constants by `r25_arrow`, with
//! the three facts about them a Tait `lam` case consumes.
//!
//! See the module doc of [`super::candmodel_construct_r28`] for the argument,
//! and `designs/2026-09-17-r28-term-judgment-on-the-wkc-lineage.md` for the
//! design this implements and the measurements behind it.

// **This module deliberately imports nothing** — the R12-R27 convention.

/// `r25_arrow`'s codomain, spelled out. Every statement below has to name it
/// literally, because `r25_arrow A B` is `KExpr.pi A (lift_at B 0 1)` and the
/// lift is exactly what the two rewriting lemmas are about.
const B1: &str = "(lift_at B Nat.zero (Nat.succ Nat.zero))";

/// The `konst` constructor's two inertness premises, verbatim from `WKC.konst`
/// (`candmodel_construct_r17_src.rs`). They are re-spelled rather than
/// imported, per this module's no-imports convention — and they must stay
/// byte-identical to R17's, since `InertTy.konst` feeds them straight to
/// `WKC.konst`.
fn defval_none(n: &str) -> String {
    format!("Eq (OptionType KExpr) (defval_for (red_def the_red_env) {n}) (OptionType.none KExpr)")
}

fn recmeta_none(n: &str) -> String {
    format!(
        "Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) {n}) (OptionType.none RecMeta)"
    )
}

// ================================================================
// Group A — the type class, and the three facts about it.
// ================================================================

/// **`InertTy`** — R6's `SimpleTy`, rebuilt at the `WKC`/`xval` lineage.
///
/// Two differences from `SimpleTy`, both forced:
///
/// * **The base case is a CONSTANT, not a sort.** `WKC.sort` concludes at
///   `Sk.kd Sk.ty` and not at `Sk.ty`, so a sort is not a `ty`-shaped type on
///   this lineage and `r24_RedAt` — which is indexed by `WKC D A Sk.ty` —
///   cannot even be stated at one. `WKC.konst`'s inert reflected constants are
///   the `ty`-shaped base, so `InertTy.konst` carries its two inertness
///   equations verbatim and hands them straight back.
/// * **The arrow is `r25_arrow`, so it carries a LIFT.** `r25_arrow A B` is
///   `KExpr.pi A (lift_at B 0 1)`: non-dependence faked inside a dependent
///   `pi`. `SimpleTy.arrow` concludes at a bare `KExpr.pi A B` and never meets
///   this. Every lemma below pays for that lift exactly once.
pub(super) fn src_inert_ty() -> String {
    format!(
        "inductive InertTy : KExpr -> Type\n\
         | konst : forall (n : Name) (us : ListType Level), {dv} -> {rm} -> InertTy (KExpr.const n us)\n\
         | arrow : forall (A : KExpr) (B : KExpr), InertTy A -> InertTy B -> InertTy (r25_arrow A B)",
        dv = defval_none("n"),
        rm = recmeta_none("n"),
    )
}

/// **`r28_inertTy_wkc`** — every inert type is `ty`-shaped, at EVERY shape
/// environment.
///
/// `D` is bound outside the induction because no clause changes it: `InertTy`
/// mentions no environment at all, which is the point of restricting to closed
/// types. The `konst` arm hands `WKC.konst` the two equations it was carrying;
/// the `arrow` arm is `r25_arrowWkc`, whose own typing rests on
/// `piShape Sk.ty t = Sk.ty` and `domSk Sk.ty = Sk.ty`.
pub(super) fn ty_inert_wkc() -> String {
    "forall (D : Nat -> Sk) (T : KExpr), InertTy T -> WKC D T Sk.ty".to_string()
}

pub(super) fn val_inert_wkc() -> String {
    format!(
        "fun (D : Nat -> Sk) (T : KExpr) (h : InertTy T) => \
         InertTy.rec (fun (z : KExpr) (_hz : InertTy z) => WKC D z Sk.ty) \
         (fun (n : Name) (us : ListType Level) (hd : {dv}) (hr : {rm}) => WKC.konst D n us hd hr) \
         (fun (A : KExpr) (B : KExpr) (_hA : InertTy A) (_hB : InertTy B) \
         (ihA : WKC D A Sk.ty) (ihB : WKC D B Sk.ty) => r25_arrowWkc D A B ihA ihB) \
         T h",
        dv = defval_none("n"),
        rm = recmeta_none("n"),
    )
}

/// **`r28_inertTy_lift`** — lifting fixes an inert type, at EVERY cutoff and
/// amount.
///
/// **The generalisation is the whole trick.** The statement this lemma is
/// wanted for is the single instance `lift_at T Nat.zero (Nat.succ Nat.zero) =
/// T`, and that instance does NOT admit an induction: `lift_at`'s `pi` clause
/// recurses on the codomain at `Nat.succ cutoff`, so the arrow arm needs the
/// lemma at a depth the fixed statement cannot supply. Quantifying over `d` and
/// `k` is the standard de Bruijn repair, and it is why this looked like a
/// missing closedness bridge (`is_closed_at` + `lift_invariant_closed`) when it
/// is two lines.
///
/// The arrow arm uses its IH THREE times: once at `(0, 1)` to see through
/// `r25_arrow`'s own lift, once at `(succ d, k)` for the codomain, and once at
/// `(d, k)` for the domain.
pub(super) fn ty_inert_lift() -> String {
    "forall (T : KExpr), InertTy T -> forall (d : Nat) (k : Nat), Eq KExpr (lift_at T d k) T"
        .to_string()
}

pub(super) fn val_inert_lift() -> String {
    let ih = "forall (d2 : Nat) (k2 : Nat), Eq KExpr (lift_at z2 d2 k2) z2";
    let ih_a = ih.replace("z2", "A");
    let ih_b = ih.replace("z2", "B");
    // `lift_at B1 (succ d) k = B1`, obtained by rewriting B1 back to B.
    let h_b1 = format!(
        "(Eq.substType KExpr (fun (z : KExpr) => Eq KExpr (lift_at z (Nat.succ d) k) z) B {B1} \
         (Eq.symm KExpr {B1} B (ihB Nat.zero (Nat.succ Nat.zero))) (ihB (Nat.succ d) k))"
    );
    let arrow = format!(
        "(Eq.substType KExpr \
         (fun (za : KExpr) => Eq KExpr (KExpr.pi za (lift_at {B1} (Nat.succ d) k)) (KExpr.pi A {B1})) \
         A (lift_at A d k) (Eq.symm KExpr (lift_at A d k) A (ihA d k)) \
         (Eq.substType KExpr \
         (fun (zb : KExpr) => Eq KExpr (KExpr.pi A zb) (KExpr.pi A {B1})) \
         {B1} (lift_at {B1} (Nat.succ d) k) \
         (Eq.symm KExpr (lift_at {B1} (Nat.succ d) k) {B1} {h_b1}) \
         (Eq.refl KExpr (KExpr.pi A {B1}))))"
    );
    format!(
        "fun (T : KExpr) (h : InertTy T) => \
         InertTy.rec (fun (z2 : KExpr) (_hz : InertTy z2) => {ih}) \
         (fun (n : Name) (us : ListType Level) (_hd : {dv}) (_hr : {rm}) (d : Nat) (k : Nat) => \
         Eq.refl KExpr (KExpr.const n us)) \
         (fun (A : KExpr) (B : KExpr) (_hA : InertTy A) (_hB : InertTy B) \
         (ihA : {ih_a}) (ihB : {ih_b}) (d : Nat) (k : Nat) => {arrow}) \
         T h",
        dv = defval_none("n"),
        rm = recmeta_none("n"),
    )
}

/// **`r28_inertTy_psubst`** — substitution fixes an inert type, for EVERY
/// substitution.
///
/// The R6 analogue is `simpleTy_psubst`, and its own description gives the
/// reason in one line: simple types are closed, so substitution is inert. The
/// same holds here and for the same reason, but the arrow arm has to see
/// through `r25_arrow`'s lift first — which is what `r28_inertTy_lift` is for,
/// used at `(0, 1)` and then rewritten back.
///
/// **This is what removes every `psubst` reshaping from the fundamental
/// theorem's statement**: with it, `r24_RedAt D T hT r (psubst s e)` needs no
/// `psubst s T` on the type side, exactly as R6's `synTy_fundamental` needs no
/// `psubst_instantiate`.
pub(super) fn ty_inert_psubst() -> String {
    "forall (T : KExpr), InertTy T -> forall (s : Nat -> KExpr), Eq KExpr (psubst s T) T"
        .to_string()
}

pub(super) fn val_inert_psubst() -> String {
    let ih = "forall (s2 : Nat -> KExpr), Eq KExpr (psubst s2 z2) z2";
    let ih_a = ih.replace("z2", "A");
    let ih_b = ih.replace("z2", "B");
    let h_b1 = format!(
        "(Eq.substType KExpr (fun (z : KExpr) => Eq KExpr (psubst (up s) z) z) B {B1} \
         (Eq.symm KExpr {B1} B (r28_inertTy_lift B hBi Nat.zero (Nat.succ Nat.zero))) \
         (ihB (up s)))"
    );
    let arrow = format!(
        "(Eq.substType KExpr \
         (fun (za : KExpr) => Eq KExpr (KExpr.pi za (psubst (up s) {B1})) (KExpr.pi A {B1})) \
         A (psubst s A) (Eq.symm KExpr (psubst s A) A (ihA s)) \
         (Eq.substType KExpr \
         (fun (zb : KExpr) => Eq KExpr (KExpr.pi A zb) (KExpr.pi A {B1})) \
         {B1} (psubst (up s) {B1}) \
         (Eq.symm KExpr (psubst (up s) {B1}) {B1} {h_b1}) \
         (Eq.refl KExpr (KExpr.pi A {B1}))))"
    );
    format!(
        "fun (T : KExpr) (h : InertTy T) => \
         InertTy.rec (fun (z2 : KExpr) (_hz : InertTy z2) => {ih}) \
         (fun (n : Name) (us : ListType Level) (_hd : {dv}) (_hr : {rm}) (s : Nat -> KExpr) => \
         Eq.refl KExpr (KExpr.const n us)) \
         (fun (A : KExpr) (B : KExpr) (_hA : InertTy A) (hBi : InertTy B) \
         (ihA : {ih_a}) (ihB : {ih_b}) (s : Nat -> KExpr) => {arrow}) \
         T h",
        dv = defval_none("n"),
        rm = recmeta_none("n"),
    )
}

/// **`r28_inertTy_whnfAcc`** — every inert type is strongly normalizing.
///
/// This is the premise `r26_red_lam_one` takes as `whnf_acc ann`, and R6 gets
/// its analogue the same way (`simpleTy_whnfAcc`, through `whnfAcc_sort` and
/// `whnfAcc_pi`). Here the base case is a CONSTANT rather than a sort, and it
/// is free for a sharper reason than R6's: `r17_const_no_step` is a CPS
/// inverter — given any `whnf_step` out of an inert constant it returns any
/// type at all — so the accessibility arm is discharged by a function with no
/// cases, not by a landed SN theorem.
pub(super) fn ty_inert_whnf_acc() -> String {
    "forall (T : KExpr), InertTy T -> whnf_acc T".to_string()
}

pub(super) fn val_inert_whnf_acc() -> String {
    let h_b1 = format!(
        "(Eq.substType KExpr (fun (z : KExpr) => whnf_acc z) B {B1} \
         (Eq.symm KExpr {B1} B (r28_inertTy_lift B hBi Nat.zero (Nat.succ Nat.zero))) ihB)"
    );
    format!(
        "fun (T : KExpr) (h : InertTy T) => \
         InertTy.rec (fun (z : KExpr) (_hz : InertTy z) => whnf_acc z) \
         (fun (n : Name) (us : ListType Level) (hd : {dv}) (_hr : {rm}) => \
         whnf_acc.intro (KExpr.const n us) \
         (fun (g2 : KExpr) (hs : whnf_step (KExpr.const n us) g2) => \
         r17_const_no_step n us g2 (whnf_acc g2) hd hs)) \
         (fun (A : KExpr) (B : KExpr) (_hA : InertTy A) (hBi : InertTy B) \
         (ihA : whnf_acc A) (ihB : whnf_acc B) => whnfAcc_pi A {B1} ihA {h_b1}) \
         T h",
        dv = defval_none("n"),
        rm = recmeta_none("n"),
    )
}

/// **`r28_notBvar`** — the head discriminator the non-degeneracy proof needs.
///
/// `KExpr.rec` into `Type`, sending `bvar` to `Empty` and every other head to
/// `ConstFreeUnit`. Its shape (nine minors, in the order sort / bvar / app /
/// lam / pi / const / let_ / proj / lit) is `kapp_head_bvar_absurd`'s
/// (`hnf3_residual.rs`), re-spelled here rather than imported per this module's
/// no-imports convention — and simplified: that one descends the application
/// spine, which this has no use for.
pub(super) fn src_not_bvar() -> String {
    "def r28_notBvar (e : KExpr) : Type := KExpr.rec (fun (_z : KExpr) => Type) \
     (fun (sl : Level) => ConstFreeUnit) \
     (fun (bi : Nat) => Empty) \
     (fun (af : KExpr) (aa : KExpr) (_cf : Type) (_ca : Type) => ConstFreeUnit) \
     (fun (lty : KExpr) (lb : KExpr) (_cty : Type) (_cb : Type) => ConstFreeUnit) \
     (fun (pty : KExpr) (pb : KExpr) (_cty : Type) (_cb : Type) => ConstFreeUnit) \
     (fun (cn : Name) (cus : ListType Level) => ConstFreeUnit) \
     (fun (zty : KExpr) (zv : KExpr) (zb : KExpr) (_c1 : Type) (_c2 : Type) (_c3 : Type) => \
     ConstFreeUnit) \
     (fun (psn : Name) (pix : Nat) (psub : KExpr) (_csub : Type) => ConstFreeUnit) \
     (fun (lv : Nat) => ConstFreeUnit) e"
        .to_string()
}

/// **`r28_inertTy_not_total`** — a bound variable is NOT an inert type.
///
/// **This is a PROOF, not a refused probe, and the difference is the point.**
/// A refusal says the kernel would not accept one particular derivation; this
/// says no derivation exists. Without it `InertTy` could be degenerate — true
/// of everything — and all four lemmas above would be statements about
/// everything, kernel-checked and worthless. R6 pins exactly this with
/// `simpleTy_not_total`, and its own description calls it the NON-DEGENERACY of
/// the type class.
///
/// `bvar` is the sharpest witness available: it is precisely the shape that
/// restricting to CLOSED types excludes, and closedness is what makes `psubst`
/// and `lift_at` inert — which is the entire reason this class exists.
///
/// The proof is the standard equality-generalised inversion: the motive is
/// `Eq KExpr z (KExpr.bvar Nat.zero) -> Empty`, both arms transport
/// `r28_notBvar` along that equation, and the recursor is applied to the index
/// with `Eq.refl`.
pub(super) fn ty_inert_not_total() -> String {
    "InertTy (KExpr.bvar Nat.zero) -> Empty".to_string()
}

pub(super) fn val_inert_not_total() -> String {
    format!(
        "fun (h : InertTy (KExpr.bvar Nat.zero)) => \
         InertTy.rec (fun (z : KExpr) (_hz : InertTy z) => \
         Eq KExpr z (KExpr.bvar Nat.zero) -> Empty) \
         (fun (n : Name) (us : ListType Level) (_hd : {dv}) (_hr : {rm}) \
         (he : Eq KExpr (KExpr.const n us) (KExpr.bvar Nat.zero)) => \
         Eq.substType KExpr r28_notBvar (KExpr.const n us) (KExpr.bvar Nat.zero) he \
         ConstFreeUnit.triv) \
         (fun (A : KExpr) (B : KExpr) (_hA : InertTy A) (_hB : InertTy B) \
         (_ihA : Eq KExpr A (KExpr.bvar Nat.zero) -> Empty) \
         (_ihB : Eq KExpr B (KExpr.bvar Nat.zero) -> Empty) \
         (he : Eq KExpr (r25_arrow A B) (KExpr.bvar Nat.zero)) => \
         Eq.substType KExpr r28_notBvar (r25_arrow A B) (KExpr.bvar Nat.zero) he \
         ConstFreeUnit.triv) \
         (KExpr.bvar Nat.zero) h (Eq.refl KExpr (KExpr.bvar Nat.zero))",
        dv = defval_none("n"),
        rm = recmeta_none("n"),
    )
}

// ================================================================
// Negative controls — none of these is registered.
// ================================================================

/// The lift lemma claimed WITHOUT the generalisation — the exact statement the
/// design says cannot be proved by this induction. If the kernel ever accepts
/// it, the `d`/`k` quantification is not doing the work this module says it
/// does and the arrow arm is closing for some other reason.
#[cfg(test)]
pub(super) fn probe_lift_fixed_depth() -> String {
    let ih = "Eq KExpr (lift_at z2 Nat.zero (Nat.succ Nat.zero)) z2";
    format!(
        "def r28_probe_lift_fixed_depth : forall (T : KExpr), InertTy T -> \
         Eq KExpr (lift_at T Nat.zero (Nat.succ Nat.zero)) T := \
         fun (T : KExpr) (h : InertTy T) => \
         InertTy.rec (fun (z2 : KExpr) (_hz : InertTy z2) => {ih}) \
         (fun (n : Name) (us : ListType Level) (_hd : {dv}) (_hr : {rm}) => \
         Eq.refl KExpr (KExpr.const n us)) \
         (fun (A : KExpr) (B : KExpr) (_hA : InertTy A) (_hB : InertTy B) \
         (ihA : {ih_a}) (ihB : {ih_b}) => Eq.refl KExpr (r25_arrow A B)) \
         T h",
        dv = defval_none("n"),
        rm = recmeta_none("n"),
        ih_a = ih.replace("z2", "A"),
        ih_b = ih.replace("z2", "B"),
    )
}

// ================================================================
// The item table.
// ================================================================

pub(super) enum R28Item {
    Ind {
        name: String,
        src: String,
    },
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

/// Test-only, like R27's: `name` and `decl_source` are read by the scratch
/// harness and by nothing in a normal build, so an ungated impl is a
/// `never used` warning and `-D warnings` denies it.
#[cfg(test)]
impl R28Item {
    pub(super) fn name(&self) -> &str {
        match self {
            R28Item::Ind { name, .. } | R28Item::Def { name, .. } | R28Item::Thm { name, .. } => {
                name
            }
        }
    }

    #[cfg(test)]
    pub(super) fn decl_source(&self) -> String {
        match self {
            R28Item::Ind { src, .. } | R28Item::Def { src, .. } => src.clone(),
            R28Item::Thm { name, ty, val } => format!("def {name} : {ty} := {val}"),
        }
    }
}

fn i(name: &str, src: String) -> R28Item {
    R28Item::Ind {
        name: name.to_string(),
        src,
    }
}

fn d(name: &str, src: String) -> R28Item {
    R28Item::Def {
        name: name.to_string(),
        src,
    }
}

fn t(name: &str, ty: String, val: String) -> R28Item {
    R28Item::Thm {
        name: name.to_string(),
        ty,
        val,
    }
}

/// Every R28 constant, in registration order. `InertTy` first — the three
/// lemmas are inductions over it — and `r28_inertTy_lift` before the two that
/// consume it.
pub(super) fn r28_items() -> Vec<R28Item> {
    vec![
        i("InertTy", src_inert_ty()),
        t("r28_inertTy_wkc", ty_inert_wkc(), val_inert_wkc()),
        t("r28_inertTy_lift", ty_inert_lift(), val_inert_lift()),
        t("r28_inertTy_psubst", ty_inert_psubst(), val_inert_psubst()),
        t(
            "r28_inertTy_whnfAcc",
            ty_inert_whnf_acc(),
            val_inert_whnf_acc(),
        ),
        d("r28_notBvar", src_not_bvar()),
        t(
            "r28_inertTy_not_total",
            ty_inert_not_total(),
            val_inert_not_total(),
        ),
    ]
}

#[cfg(test)]
pub(super) fn r28_all_sources() -> Vec<(String, String)> {
    r28_items()
        .into_iter()
        .map(|it| (it.name().to_string(), it.decl_source()))
        .collect()
}
