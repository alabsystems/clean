// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R1 of the candidate-model construction ladder: the Tait head-expansion
//! ENGINE layer — the beta engine `candExp_beta` (any candidate set is closed
//! under beta-expansion at the head, over the spec's FULL env-fixed
//! `whnf_step`), the zeta engine `whnfAcc_zeta_expand` (the same expansion for
//! `let_`, at the base whole-SN set), the app-/lam-/let-headed step-inversion
//! machinery they run on, and the §6-mandated discriminating witnesses —
//! including the REFUTATION `zeta_expansion_not_generic` showing the zeta
//! engine cannot be per-set generic in this calculus.
//!
//! Port of the corpus `Stratified/Cand.lean` `candExp` (rung `stratified-sn`)
//! + `LetDeltaSN.lean` `reducible_letE_expand` per
//! `designs/2026-08-23-spec-candmodel-port.md` §5 rung R1. Builds directly on
//! R0's `IsCandSet` interface (`candmodel_construct_r0.rs`).
//!
//! ## Honesty notes (read before quoting)
//!
//! - **The engine premise is a FAMILY, not the corpus's single contractum.**
//!   Corpus `candExp` takes `S (inst b a)` for the ONE given argument and
//!   transports it through the congruence arms with the substitution-step
//!   lemmas `subst_step` / `subst_arg_steps`. Those lemmas do NOT exist
//!   spec-side, and their one-step analogue
//!   `beta_reduces e e2 -> beta_reduces (psubst s e) (psubst s e2)` is NOT an
//!   R1-provable brick: `beta_reduces` embeds iota via
//!   `iota_step (red_rec the_red_env)` (and lift/psubst commutation with a
//!   REAL-env iota fire is exactly the env-closure work the design defers to
//!   R2+, items B1/B3). `candExp_beta` therefore takes the premise the spec's
//!   own `CandModel.redAbstraction` field takes — membership of the contractum
//!   for EVERY reducible argument (`SA a2`) — extended over every
//!   `betaStar`-development of the body (`b2`), which is what survives the
//!   `lam_body` congruence arm without any substitution transport. The corpus
//!   single-contractum spelling is DERIVABLE from this one only once the
//!   substitution-step lemmas land; until then this is the honest interface.
//! - **The redex IS neutral; that is what makes the beta engine per-set.**
//!   The spec's `Neutral` (dependent_sn_richmodel.rs) sends every `app` head
//!   to `ConstFreeUnit`, so `app (lam ty b) a` is Neutral and cr3 applies —
//!   exactly the corpus pivot (`Cand.lean` header comment).
//! - **The zeta engine is NOT per-set generic, and that is PROVED, not
//!   presumed.** `Neutral (let_ ..) = Empty`, so cr3 never applies to a zeta
//!   redex, and the loss is real: `zetaGuardSet e` (whnf_acc AND the probe
//!   redex `zetaProbe = let_ (bvar 1) (bvar 1) (bvar 0)` is `whnfStar`-
//!   unreachable from e) is a genuine candidate set (`isCand_zetaGuard`)
//!   containing the probe's type/value/body/contractum but NOT the probe
//!   itself — `zeta_expansion_not_generic` refutes the let_-headed engine of
//!   EXACTLY `candExp_beta`'s shape (same premises, conclusion redex
//!   `app (lam ty b) a` swapped for `let_ ty a b`, the spelling of
//!   `CandModel.redLet`). The TRUE zeta fact this rung lands is
//!   `whnfAcc_zeta_expand`: the same expansion AT THE BASE whole-SN set,
//!   where `whnf_acc.intro` plays cr3's role with no neutrality demanded.
//!   Consequence for later rungs: `redLet` for an interp cannot be discharged
//!   by a per-set engine — it needs the interp's own structure (design row 1:
//!   let_ interpreted via its contractum).
//! - **The argument-side premise is load-bearing, and that is proved too.**
//!   `appOmega_arg_acc_necessary` is the §6.1 pair: for the arg-ignoring body
//!   `sort 0`, the contractum `instantiate (sort 0) omegaLoop = sort 0` IS
//!   whnf_acc while the redex `appOmega = app (lam (sort 0) (sort 0))
//!   omegaLoop` is NOT (it self-loops through the `app_right` congruence arm
//!   on R0's omega loop; `selfLoop_not_whnfAcc` is the generic Acc refutation
//!   of any one-step self-loop). So no engine variant may drop the `SA a`
//!   membership (whose cr1 face supplies `whnf_acc a`).
//! - **The step relation is full and env-fixed.** All inversions here handle
//!   the COMPLETE reduct set of the redexes: top beta/zeta, the three-or-four
//!   congruence arms, and the head-iota/delta arms killed computationally —
//!   `kexpr_const_name (kapp_fn redex)` computes to `none` on lam-headed-app /
//!   lam / let_ heads, so `iota_step_head_none_absurd_type` /
//!   `delta_step_head_none_absurd_type` close them by `Eq.refl`.
//!
//! ## Census
//!
//! ZERO new axioms: every constant is value-bearing (two genuine inductives
//! via `add_inductive`, plain defs via `add_recursive_def`, theorems via
//! `add_definition` with kernel `add_decl` checking). Census-neutral.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ==== R1 SOURCES BEGIN (dependency-free: consts + pure string builders; ====
// ==== extracted verbatim by the pre-validation parse harness)           ====

// ================================================================
// Group A — the two reflexive-transitive step closures. Shape mirrors the
// landed `whnf_to` / `below_plus` / `natSteps` star relations (measured
// promotion-safe: the recursive occurrence's first index differs from the
// leading binder, so the uniform-leading-argument recursor promotion of
// micro_verifies_r0's RECURSOR-SHAPE PIN cannot fire).
// ================================================================

pub(super) const SRC_BETA_STAR: &str = "inductive betaStar : KExpr -> KExpr -> Type\n| refl : forall (e : KExpr), betaStar e e\n| step : forall (e : KExpr) (e2 : KExpr) (e3 : KExpr), beta_reduces e e2 -> betaStar e2 e3 -> betaStar e e3";

pub(super) const SRC_WHNF_STAR: &str = "inductive whnfStar : KExpr -> KExpr -> Type\n| refl : forall (e : KExpr), whnfStar e e\n| step : forall (e : KExpr) (e2 : KExpr) (e3 : KExpr), whnf_step e e2 -> whnfStar e2 e3 -> whnfStar e e3";

// ================================================================
// Group B — the bvar/star toolbox the witnesses discharge families with.
// ================================================================

pub(super) const TY_INST_BVAR0: &str =
    "forall (v : KExpr), Eq KExpr (instantiate (KExpr.bvar Nat.zero) v) v";
// instantiate (bvar 0) v computes to lift_at v 0 0 (instantiate_at -> bvar arm
// -> instantiate_bvar_at 0 0 v -> instantiate_bvar_geq base, Nat.sub 0 0 = 0
// throughout), which lift_at_amount_zero closes at cutoff 0.
pub(super) const VAL_INST_BVAR0: &str = "fun (v : KExpr) => lift_at_amount_zero v Nat.zero";

pub(super) const TY_BETASTAR_BVAR_COLLAPSE: &str =
    "forall (i : Nat) (b2 : KExpr), betaStar (KExpr.bvar i) b2 -> Eq KExpr b2 (KExpr.bvar i)";
// NOTE the Empty.rec detour in the step arm: no_whnf_step_bvar's C is
// Type-valued, and the goal Eq lives in Prop (spec Eq is Prop; the kernel is
// non-cumulative), so the absurdity lands in Empty first and Empty.rec
// eliminates into the Prop goal (const_ne_let idiom).
pub(super) const VAL_BETASTAR_BVAR_COLLAPSE: &str = "fun (i : Nat) (b2 : KExpr) (h : betaStar (KExpr.bvar i) b2) => betaStar.rec (fun (s : KExpr) (t : KExpr) (_ : betaStar s t) => Eq KExpr s (KExpr.bvar i) -> Eq KExpr t (KExpr.bvar i)) (fun (e : KExpr) (heq : Eq KExpr e (KExpr.bvar i)) => heq) (fun (e : KExpr) (e2 : KExpr) (e3 : KExpr) (hstep : beta_reduces e e2) (_hrest : betaStar e2 e3) (_ih : Eq KExpr e2 (KExpr.bvar i) -> Eq KExpr e3 (KExpr.bvar i)) (heq : Eq KExpr e (KExpr.bvar i)) => Empty.rec (fun (_ : Empty) => Eq KExpr e3 (KExpr.bvar i)) (no_whnf_step_bvar i e2 Empty (whnf_step.beta (KExpr.bvar i) e2 (Eq.rec KExpr e (fun (x : KExpr) (_ : Eq KExpr e x) => beta_reduces x e2) hstep (KExpr.bvar i) heq)))) (KExpr.bvar i) b2 h (Eq.refl KExpr (KExpr.bvar i))";

pub(super) const TY_BETASTAR_BVAR0_FAM: &str = "forall (S : KExpr -> Type) (b2 : KExpr), betaStar (KExpr.bvar Nat.zero) b2 -> forall (v2 : KExpr), S v2 -> S (instantiate b2 v2)";
pub(super) const VAL_BETASTAR_BVAR0_FAM: &str = "fun (S : KExpr -> Type) (b2 : KExpr) (hstar : betaStar (KExpr.bvar Nat.zero) b2) (v2 : KExpr) (hv2 : S v2) => Eq.substType KExpr (fun (w : KExpr) => S (instantiate w v2)) (KExpr.bvar Nat.zero) b2 (Eq.symm KExpr b2 (KExpr.bvar Nat.zero) (betaStar_bvar_collapse Nat.zero b2 hstar)) (Eq.substType KExpr (fun (w : KExpr) => S w) v2 (instantiate (KExpr.bvar Nat.zero) v2) (Eq.symm KExpr (instantiate (KExpr.bvar Nat.zero) v2) v2 (cand_inst_bvar0 v2)) hv2)";

// ================================================================
// Group C — the CPS step inversions for the two redex shapes.
// Template idiom: const_no_beta_reduces (natrec.rs) / wRecSpine1_step_inv
// (acc_wtype.rs). Arm order = beta_reduces constructor order: beta, app_left,
// app_right, lam_ty, lam_body, pi_dom, pi_cod, forall_congr_dom,
// forall_congr_cod, zeta, let_ty, let_val, let_body, iota, proj.
// ================================================================

const RED_A: &str = "(KExpr.app (KExpr.lam ty b) a)";
const RED_L: &str = "(KExpr.lam ty b)";
const RED_T: &str = "(KExpr.let_ ty v b)";

/// Head-iota computational kill at a source whose spine head is not a const:
/// `kexpr_const_name (kapp_fn src)` computes to `none`, so the transported
/// `iota_reduces` step is absurd.
fn iota_kill(src: &str) -> String {
    format!(
        "iota_step_head_none_absurd_type (red_rec the_red_env) {src} e02 C (Eq.refl (OptionType Name) (OptionType.none Name)) (iota_reduces_to_step {src} e02 (Eq.substType KExpr (fun (w : KExpr) => iota_reduces w e02) e0 {src} heq hiota))"
    )
}

/// The engine statement shape shared by the beta engine and the refuted
/// let_-headed analogue: two candidate sets, acc type annotation, acc body,
/// the contractum family over every betaStar-development of the body and
/// every SA member, concluding membership of `redex`.
fn engine_ty(redex: &str) -> String {
    format!(
        "forall (S : KExpr -> Type) (SA : KExpr -> Type), IsCandSet S -> IsCandSet SA -> forall (ty : KExpr), whnf_acc ty -> forall (b : KExpr), whnf_acc b -> (forall (b2 : KExpr), betaStar b b2 -> forall (a2 : KExpr), SA a2 -> S (instantiate b2 a2)) -> forall (a : KExpr), SA a -> S {redex}"
    )
}

pub(super) fn ty_candexp_beta() -> String {
    engine_ty(RED_A)
}

pub(super) fn ty_zeta_engine_hypothesis() -> String {
    engine_ty("(KExpr.let_ ty a b)")
}

// ---------------- lamHead_beta_inv ----------------

pub(super) fn ty_lamhead_beta_inv() -> String {
    let kty = "forall (ty2 : KExpr), beta_reduces ty ty2 -> Eq KExpr g2 (KExpr.lam ty2 b) -> C";
    let kbd = "forall (b2 : KExpr), beta_reduces b b2 -> Eq KExpr g2 (KExpr.lam ty b2) -> C";
    format!(
        "forall (ty : KExpr) (b : KExpr) (g2 : KExpr) (C : Type), beta_reduces (KExpr.lam ty b) g2 -> ({kty}) -> ({kbd}) -> C"
    )
}

pub(super) fn val_lamhead_beta_inv() -> String {
    let kty = |t: &str| {
        format!("forall (ty2 : KExpr), beta_reduces ty ty2 -> Eq KExpr {t} (KExpr.lam ty2 b) -> C")
    };
    let kbd = |t: &str| {
        format!("forall (b2 : KExpr), beta_reduces b b2 -> Eq KExpr {t} (KExpr.lam ty b2) -> C")
    };
    let mot = format!(
        "(fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => Eq KExpr s {RED_L} -> ({}) -> ({}) -> C)",
        kty("t"),
        kbd("t")
    );
    let ih = |x: &str, y: &str| {
        format!(
            "(_ih : Eq KExpr {x} {RED_L} -> ({}) -> ({}) -> C)",
            kty(y),
            kbd(y)
        )
    };
    // kill arms bind both continuations unused
    let ks = |t: &str| format!("(_k1 : {}) (_k2 : {})", kty(t), kbd(t));
    let a_beta = format!(
        "(fun (A0 : KExpr) (body0 : KExpr) (arg0 : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body0) arg0) {RED_L}) {} => app_ne_lam (KExpr.lam A0 body0) arg0 ty b C heq)",
        ks("(instantiate body0 arg0)")
    );
    let a_appl = format!(
        "(fun (f : KExpr) (f2 : KExpr) (a0 : KExpr) (_hstep : beta_reduces f f2) {} (heq : Eq KExpr (KExpr.app f a0) {RED_L}) {} => app_ne_lam f a0 ty b C heq)",
        ih("f", "f2"),
        ks("(KExpr.app f2 a0)")
    );
    let a_appr = format!(
        "(fun (f : KExpr) (a0 : KExpr) (a2 : KExpr) (_hstep : beta_reduces a0 a2) {} (heq : Eq KExpr (KExpr.app f a0) {RED_L}) {} => app_ne_lam f a0 ty b C heq)",
        ih("a0", "a2"),
        ks("(KExpr.app f a2)")
    );
    let a_lamty = format!(
        "(fun (lty : KExpr) (lty2 : KExpr) (lbody : KExpr) (hstep : beta_reduces lty lty2) {} (heq : Eq KExpr (KExpr.lam lty lbody) {RED_L}) (k1 : {}) (_k2 : {}) => k1 lty2 (Eq.rec KExpr lty (fun (x : KExpr) (_ : Eq KExpr lty x) => beta_reduces x lty2) hstep ty (lam_inj_fst lty lbody ty b heq)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam lty2 w) lbody b (lam_inj_snd lty lbody ty b heq)))",
        ih("lty", "lty2"),
        kty("(KExpr.lam lty2 lbody)"),
        kbd("(KExpr.lam lty2 lbody)")
    );
    let a_lambd = format!(
        "(fun (lty : KExpr) (lbody : KExpr) (lbody2 : KExpr) (hstep : beta_reduces lbody lbody2) {} (heq : Eq KExpr (KExpr.lam lty lbody) {RED_L}) (_k1 : {}) (k2 : {}) => k2 lbody2 (Eq.rec KExpr lbody (fun (x : KExpr) (_ : Eq KExpr lbody x) => beta_reduces x lbody2) hstep b (lam_inj_snd lty lbody ty b heq)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w lbody2) lty ty (lam_inj_fst lty lbody ty b heq)))",
        ih("lbody", "lbody2"),
        kty("(KExpr.lam lty lbody2)"),
        kbd("(KExpr.lam lty lbody2)")
    );
    let a_pidom = format!(
        "(fun (pdom : KExpr) (pdom2 : KExpr) (pbody : KExpr) (_hstep : beta_reduces pdom pdom2) {} (heq : Eq KExpr (KExpr.pi pdom pbody) {RED_L}) {} => pi_ne_lam pdom pbody ty b C heq)",
        ih("pdom", "pdom2"),
        ks("(KExpr.pi pdom2 pbody)")
    );
    let a_picod = format!(
        "(fun (pdom : KExpr) (pbody : KExpr) (pbody2 : KExpr) (_hstep : beta_reduces pbody pbody2) {} (heq : Eq KExpr (KExpr.pi pdom pbody) {RED_L}) {} => pi_ne_lam pdom pbody ty b C heq)",
        ih("pbody", "pbody2"),
        ks("(KExpr.pi pdom pbody2)")
    );
    let a_fadom = format!(
        "(fun (fdom : KExpr) (fdom2 : KExpr) (fbody : KExpr) (_hstep : beta_reduces fdom fdom2) {} (heq : Eq KExpr (KExpr.forall_ fdom fbody) {RED_L}) {} => pi_ne_lam fdom fbody ty b C heq)",
        ih("fdom", "fdom2"),
        ks("(KExpr.forall_ fdom2 fbody)")
    );
    let a_facod = format!(
        "(fun (fdom : KExpr) (fbody : KExpr) (fbody2 : KExpr) (_hstep : beta_reduces fbody fbody2) {} (heq : Eq KExpr (KExpr.forall_ fdom fbody) {RED_L}) {} => pi_ne_lam fdom fbody ty b C heq)",
        ih("fbody", "fbody2"),
        ks("(KExpr.forall_ fdom fbody2)")
    );
    let a_zeta = format!(
        "(fun (zty : KExpr) (zval : KExpr) (zbody : KExpr) (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_L}) {} => let_ne_lam zty zval zbody ty b C heq)",
        ks("(instantiate zbody zval)")
    );
    let a_letty = format!(
        "(fun (zty : KExpr) (zty2 : KExpr) (zval : KExpr) (zbody : KExpr) (_hstep : beta_reduces zty zty2) {} (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_L}) {} => let_ne_lam zty zval zbody ty b C heq)",
        ih("zty", "zty2"),
        ks("(KExpr.let_ zty2 zval zbody)")
    );
    let a_letval = format!(
        "(fun (zty : KExpr) (zval : KExpr) (zval2 : KExpr) (zbody : KExpr) (_hstep : beta_reduces zval zval2) {} (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_L}) {} => let_ne_lam zty zval zbody ty b C heq)",
        ih("zval", "zval2"),
        ks("(KExpr.let_ zty zval2 zbody)")
    );
    let a_letbd = format!(
        "(fun (zty : KExpr) (zval : KExpr) (zbody : KExpr) (zbody2 : KExpr) (_hstep : beta_reduces zbody zbody2) {} (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_L}) {} => let_ne_lam zty zval zbody ty b C heq)",
        ih("zbody", "zbody2"),
        ks("(KExpr.let_ zty zval zbody2)")
    );
    let a_iota = format!(
        "(fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : Eq KExpr e0 {RED_L}) {} => {})",
        ks("e02"),
        iota_kill(RED_L)
    );
    let a_proj = format!(
        "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub2 : KExpr) (_hstep : beta_reduces psub psub2) {} (heq : Eq KExpr (KExpr.proj ps pidx psub) {RED_L}) {} => proj_ne_lam ps pidx psub ty b C heq)",
        ih("psub", "psub2"),
        ks("(KExpr.proj ps pidx psub2)")
    );
    format!(
        "fun (ty : KExpr) (b : KExpr) (g2 : KExpr) (C : Type) (hb : beta_reduces {RED_L} g2) (kTy : {}) (kBody : {}) => beta_reduces.rec {mot} {a_beta} {a_appl} {a_appr} {a_lamty} {a_lambd} {a_pidom} {a_picod} {a_fadom} {a_facod} {a_zeta} {a_letty} {a_letval} {a_letbd} {a_iota} {a_proj} {RED_L} g2 hb (Eq.refl KExpr {RED_L}) kTy kBody",
        kty("g2"),
        kbd("g2")
    )
}

// ---------------- betaRedex_beta_inv ----------------

pub(super) fn ty_betaredex_beta_inv() -> String {
    format!(
        "forall (ty : KExpr) (b : KExpr) (a : KExpr) (g2 : KExpr) (C : Type), beta_reduces {RED_A} g2 -> (Eq KExpr g2 (instantiate b a) -> C) -> (forall (ty2 : KExpr), beta_reduces ty ty2 -> Eq KExpr g2 (KExpr.app (KExpr.lam ty2 b) a) -> C) -> (forall (b2 : KExpr), beta_reduces b b2 -> Eq KExpr g2 (KExpr.app (KExpr.lam ty b2) a) -> C) -> (forall (a2 : KExpr), beta_reduces a a2 -> Eq KExpr g2 (KExpr.app (KExpr.lam ty b) a2) -> C) -> C"
    )
}

pub(super) fn val_betaredex_beta_inv() -> String {
    let kb = |t: &str| format!("Eq KExpr {t} (instantiate b a) -> C");
    let kt = |t: &str| {
        format!(
            "forall (ty2 : KExpr), beta_reduces ty ty2 -> Eq KExpr {t} (KExpr.app (KExpr.lam ty2 b) a) -> C"
        )
    };
    let kd = |t: &str| {
        format!(
            "forall (b2 : KExpr), beta_reduces b b2 -> Eq KExpr {t} (KExpr.app (KExpr.lam ty b2) a) -> C"
        )
    };
    let ka = |t: &str| {
        format!(
            "forall (a2 : KExpr), beta_reduces a a2 -> Eq KExpr {t} (KExpr.app (KExpr.lam ty b) a2) -> C"
        )
    };
    let mot = format!(
        "(fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => Eq KExpr s {RED_A} -> ({}) -> ({}) -> ({}) -> ({}) -> C)",
        kb("t"),
        kt("t"),
        kd("t"),
        ka("t")
    );
    let ih = |x: &str, y: &str| {
        format!(
            "(_ih : Eq KExpr {x} {RED_A} -> ({}) -> ({}) -> ({}) -> ({}) -> C)",
            kb(y),
            kt(y),
            kd(y),
            ka(y)
        )
    };
    let ks = |t: &str| {
        format!(
            "(_kb : {}) (_kt : {}) (_kd : {}) (_ka : {})",
            kb(t),
            kt(t),
            kd(t),
            ka(t)
        )
    };
    let a_beta = format!(
        "(fun (A0 : KExpr) (body0 : KExpr) (arg0 : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body0) arg0) {RED_A}) (kb : {}) (_kt : {}) (_kd : {}) (_ka : {}) => kb (Eq.trans KExpr (instantiate body0 arg0) (instantiate b arg0) (instantiate b a) (Eq.cong KExpr KExpr (fun (w : KExpr) => instantiate w arg0) body0 b (lam_inj_snd A0 body0 ty b (app_inj_fst (KExpr.lam A0 body0) arg0 (KExpr.lam ty b) a heq))) (Eq.cong KExpr KExpr (fun (w : KExpr) => instantiate b w) arg0 a (app_inj_snd (KExpr.lam A0 body0) arg0 (KExpr.lam ty b) a heq))))",
        kb("(instantiate body0 arg0)"),
        kt("(instantiate body0 arg0)"),
        kd("(instantiate body0 arg0)"),
        ka("(instantiate body0 arg0)")
    );
    let a_appl = format!(
        "(fun (f : KExpr) (f2 : KExpr) (a0 : KExpr) (hstep : beta_reduces f f2) {} (heq : Eq KExpr (KExpr.app f a0) {RED_A}) (_kb : {}) (kt : {}) (kd : {}) (_ka : {}) => lamHead_beta_inv ty b f2 C (Eq.rec KExpr f (fun (x : KExpr) (_ : Eq KExpr f x) => beta_reduces x f2) hstep (KExpr.lam ty b) (app_inj_fst f a0 (KExpr.lam ty b) a heq)) (fun (ty2 : KExpr) (hty2 : beta_reduces ty ty2) (heq2 : Eq KExpr f2 (KExpr.lam ty2 b)) => kt ty2 hty2 (Eq.trans KExpr (KExpr.app f2 a0) (KExpr.app (KExpr.lam ty2 b) a0) (KExpr.app (KExpr.lam ty2 b) a) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w a0) f2 (KExpr.lam ty2 b) heq2) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app (KExpr.lam ty2 b) w) a0 a (app_inj_snd f a0 (KExpr.lam ty b) a heq)))) (fun (b2 : KExpr) (hb2 : beta_reduces b b2) (heq2 : Eq KExpr f2 (KExpr.lam ty b2)) => kd b2 hb2 (Eq.trans KExpr (KExpr.app f2 a0) (KExpr.app (KExpr.lam ty b2) a0) (KExpr.app (KExpr.lam ty b2) a) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w a0) f2 (KExpr.lam ty b2) heq2) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app (KExpr.lam ty b2) w) a0 a (app_inj_snd f a0 (KExpr.lam ty b) a heq)))))",
        ih("f", "f2"),
        kb("(KExpr.app f2 a0)"),
        kt("(KExpr.app f2 a0)"),
        kd("(KExpr.app f2 a0)"),
        ka("(KExpr.app f2 a0)")
    );
    // CAPTURE HAZARD (measured on the first heavy run, fvar mismatch 91/85):
    // the continuation templates kb/kt/kd/ka quantify their own ty2/b2/a2, so
    // the arm-target expression substituted into them must not mention those
    // names. This arm's stepped-argument binder is therefore `aw`, NOT `a2` —
    // with `a2` the target (KExpr.app f a2) was captured by ka's own
    // `forall (a2 : KExpr)` binder. The only arm in the three inversions
    // whose constructor binder collides with a template binder.
    let a_appr = format!(
        "(fun (f : KExpr) (a0 : KExpr) (aw : KExpr) (hstep : beta_reduces a0 aw) {} (heq : Eq KExpr (KExpr.app f a0) {RED_A}) (_kb : {}) (_kt : {}) (_kd : {}) (ka : {}) => ka aw (Eq.rec KExpr a0 (fun (x : KExpr) (_ : Eq KExpr a0 x) => beta_reduces x aw) hstep a (app_inj_snd f a0 (KExpr.lam ty b) a heq)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w aw) f (KExpr.lam ty b) (app_inj_fst f a0 (KExpr.lam ty b) a heq)))",
        ih("a0", "aw"),
        kb("(KExpr.app f aw)"),
        kt("(KExpr.app f aw)"),
        kd("(KExpr.app f aw)"),
        ka("(KExpr.app f aw)")
    );
    let a_lamty = format!(
        "(fun (lty : KExpr) (lty2 : KExpr) (lbody : KExpr) (_hstep : beta_reduces lty lty2) {} (heq : Eq KExpr (KExpr.lam lty lbody) {RED_A}) {} => lam_ne_app lty lbody (KExpr.lam ty b) a C heq)",
        ih("lty", "lty2"),
        ks("(KExpr.lam lty2 lbody)")
    );
    let a_lambd = format!(
        "(fun (lty : KExpr) (lbody : KExpr) (lbody2 : KExpr) (_hstep : beta_reduces lbody lbody2) {} (heq : Eq KExpr (KExpr.lam lty lbody) {RED_A}) {} => lam_ne_app lty lbody (KExpr.lam ty b) a C heq)",
        ih("lbody", "lbody2"),
        ks("(KExpr.lam lty lbody2)")
    );
    let a_pidom = format!(
        "(fun (pdom : KExpr) (pdom2 : KExpr) (pbody : KExpr) (_hstep : beta_reduces pdom pdom2) {} (heq : Eq KExpr (KExpr.pi pdom pbody) {RED_A}) {} => pi_ne_app pdom pbody (KExpr.lam ty b) a C heq)",
        ih("pdom", "pdom2"),
        ks("(KExpr.pi pdom2 pbody)")
    );
    let a_picod = format!(
        "(fun (pdom : KExpr) (pbody : KExpr) (pbody2 : KExpr) (_hstep : beta_reduces pbody pbody2) {} (heq : Eq KExpr (KExpr.pi pdom pbody) {RED_A}) {} => pi_ne_app pdom pbody (KExpr.lam ty b) a C heq)",
        ih("pbody", "pbody2"),
        ks("(KExpr.pi pdom pbody2)")
    );
    let a_fadom = format!(
        "(fun (fdom : KExpr) (fdom2 : KExpr) (fbody : KExpr) (_hstep : beta_reduces fdom fdom2) {} (heq : Eq KExpr (KExpr.forall_ fdom fbody) {RED_A}) {} => pi_ne_app fdom fbody (KExpr.lam ty b) a C heq)",
        ih("fdom", "fdom2"),
        ks("(KExpr.forall_ fdom2 fbody)")
    );
    let a_facod = format!(
        "(fun (fdom : KExpr) (fbody : KExpr) (fbody2 : KExpr) (_hstep : beta_reduces fbody fbody2) {} (heq : Eq KExpr (KExpr.forall_ fdom fbody) {RED_A}) {} => pi_ne_app fdom fbody (KExpr.lam ty b) a C heq)",
        ih("fbody", "fbody2"),
        ks("(KExpr.forall_ fdom fbody2)")
    );
    let a_zeta = format!(
        "(fun (zty : KExpr) (zval : KExpr) (zbody : KExpr) (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_A}) {} => let_ne_app zty zval zbody (KExpr.lam ty b) a C heq)",
        ks("(instantiate zbody zval)")
    );
    let a_letty = format!(
        "(fun (zty : KExpr) (zty2 : KExpr) (zval : KExpr) (zbody : KExpr) (_hstep : beta_reduces zty zty2) {} (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_A}) {} => let_ne_app zty zval zbody (KExpr.lam ty b) a C heq)",
        ih("zty", "zty2"),
        ks("(KExpr.let_ zty2 zval zbody)")
    );
    let a_letval = format!(
        "(fun (zty : KExpr) (zval : KExpr) (zval2 : KExpr) (zbody : KExpr) (_hstep : beta_reduces zval zval2) {} (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_A}) {} => let_ne_app zty zval zbody (KExpr.lam ty b) a C heq)",
        ih("zval", "zval2"),
        ks("(KExpr.let_ zty zval2 zbody)")
    );
    let a_letbd = format!(
        "(fun (zty : KExpr) (zval : KExpr) (zbody : KExpr) (zbody2 : KExpr) (_hstep : beta_reduces zbody zbody2) {} (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_A}) {} => let_ne_app zty zval zbody (KExpr.lam ty b) a C heq)",
        ih("zbody", "zbody2"),
        ks("(KExpr.let_ zty zval zbody2)")
    );
    let a_iota = format!(
        "(fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : Eq KExpr e0 {RED_A}) {} => {})",
        ks("e02"),
        iota_kill(RED_A)
    );
    let a_proj = format!(
        "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub2 : KExpr) (_hstep : beta_reduces psub psub2) {} (heq : Eq KExpr (KExpr.proj ps pidx psub) {RED_A}) {} => proj_ne_app ps pidx psub (KExpr.lam ty b) a C heq)",
        ih("psub", "psub2"),
        ks("(KExpr.proj ps pidx psub2)")
    );
    format!(
        "fun (ty : KExpr) (b : KExpr) (a : KExpr) (g2 : KExpr) (C : Type) (hb : beta_reduces {RED_A} g2) (kBeta : {}) (kTy : {}) (kBody : {}) (kArg : {}) => beta_reduces.rec {mot} {a_beta} {a_appl} {a_appr} {a_lamty} {a_lambd} {a_pidom} {a_picod} {a_fadom} {a_facod} {a_zeta} {a_letty} {a_letval} {a_letbd} {a_iota} {a_proj} {RED_A} g2 hb (Eq.refl KExpr {RED_A}) kBeta kTy kBody kArg",
        kb("g2"),
        kt("g2"),
        kd("g2"),
        ka("g2")
    )
}

// ---------------- letHead_beta_inv ----------------

pub(super) fn ty_lethead_beta_inv() -> String {
    format!(
        "forall (ty : KExpr) (v : KExpr) (b : KExpr) (g2 : KExpr) (C : Type), beta_reduces {RED_T} g2 -> (Eq KExpr g2 (instantiate b v) -> C) -> (forall (ty2 : KExpr), beta_reduces ty ty2 -> Eq KExpr g2 (KExpr.let_ ty2 v b) -> C) -> (forall (v2 : KExpr), beta_reduces v v2 -> Eq KExpr g2 (KExpr.let_ ty v2 b) -> C) -> (forall (b2 : KExpr), beta_reduces b b2 -> Eq KExpr g2 (KExpr.let_ ty v b2) -> C) -> C"
    )
}

pub(super) fn val_lethead_beta_inv() -> String {
    let kz = |t: &str| format!("Eq KExpr {t} (instantiate b v) -> C");
    let kt = |t: &str| {
        format!(
            "forall (ty2 : KExpr), beta_reduces ty ty2 -> Eq KExpr {t} (KExpr.let_ ty2 v b) -> C"
        )
    };
    let kv = |t: &str| {
        format!("forall (v2 : KExpr), beta_reduces v v2 -> Eq KExpr {t} (KExpr.let_ ty v2 b) -> C")
    };
    let kd = |t: &str| {
        format!("forall (b2 : KExpr), beta_reduces b b2 -> Eq KExpr {t} (KExpr.let_ ty v b2) -> C")
    };
    let mot = format!(
        "(fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => Eq KExpr s {RED_T} -> ({}) -> ({}) -> ({}) -> ({}) -> C)",
        kz("t"),
        kt("t"),
        kv("t"),
        kd("t")
    );
    let ih = |x: &str, y: &str| {
        format!(
            "(_ih : Eq KExpr {x} {RED_T} -> ({}) -> ({}) -> ({}) -> ({}) -> C)",
            kz(y),
            kt(y),
            kv(y),
            kd(y)
        )
    };
    let ks = |t: &str| {
        format!(
            "(_kz : {}) (_kt : {}) (_kv : {}) (_kd : {})",
            kz(t),
            kt(t),
            kv(t),
            kd(t)
        )
    };
    let inj = |field: &str| format!("(let_inj_{field} zty zval zbody ty v b heq)");
    let a_beta = format!(
        "(fun (A0 : KExpr) (body0 : KExpr) (arg0 : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body0) arg0) {RED_T}) {} => app_ne_let (KExpr.lam A0 body0) arg0 ty v b C heq)",
        ks("(instantiate body0 arg0)")
    );
    let a_appl = format!(
        "(fun (f : KExpr) (f2 : KExpr) (a0 : KExpr) (_hstep : beta_reduces f f2) {} (heq : Eq KExpr (KExpr.app f a0) {RED_T}) {} => app_ne_let f a0 ty v b C heq)",
        ih("f", "f2"),
        ks("(KExpr.app f2 a0)")
    );
    let a_appr = format!(
        "(fun (f : KExpr) (a0 : KExpr) (a2 : KExpr) (_hstep : beta_reduces a0 a2) {} (heq : Eq KExpr (KExpr.app f a0) {RED_T}) {} => app_ne_let f a0 ty v b C heq)",
        ih("a0", "a2"),
        ks("(KExpr.app f a2)")
    );
    let a_lamty = format!(
        "(fun (lty : KExpr) (lty2 : KExpr) (lbody : KExpr) (_hstep : beta_reduces lty lty2) {} (heq : Eq KExpr (KExpr.lam lty lbody) {RED_T}) {} => lam_ne_let lty lbody ty v b C heq)",
        ih("lty", "lty2"),
        ks("(KExpr.lam lty2 lbody)")
    );
    let a_lambd = format!(
        "(fun (lty : KExpr) (lbody : KExpr) (lbody2 : KExpr) (_hstep : beta_reduces lbody lbody2) {} (heq : Eq KExpr (KExpr.lam lty lbody) {RED_T}) {} => lam_ne_let lty lbody ty v b C heq)",
        ih("lbody", "lbody2"),
        ks("(KExpr.lam lty lbody2)")
    );
    let a_pidom = format!(
        "(fun (pdom : KExpr) (pdom2 : KExpr) (pbody : KExpr) (_hstep : beta_reduces pdom pdom2) {} (heq : Eq KExpr (KExpr.pi pdom pbody) {RED_T}) {} => pi_ne_let pdom pbody ty v b C heq)",
        ih("pdom", "pdom2"),
        ks("(KExpr.pi pdom2 pbody)")
    );
    let a_picod = format!(
        "(fun (pdom : KExpr) (pbody : KExpr) (pbody2 : KExpr) (_hstep : beta_reduces pbody pbody2) {} (heq : Eq KExpr (KExpr.pi pdom pbody) {RED_T}) {} => pi_ne_let pdom pbody ty v b C heq)",
        ih("pbody", "pbody2"),
        ks("(KExpr.pi pdom pbody2)")
    );
    let a_fadom = format!(
        "(fun (fdom : KExpr) (fdom2 : KExpr) (fbody : KExpr) (_hstep : beta_reduces fdom fdom2) {} (heq : Eq KExpr (KExpr.forall_ fdom fbody) {RED_T}) {} => pi_ne_let fdom fbody ty v b C heq)",
        ih("fdom", "fdom2"),
        ks("(KExpr.forall_ fdom2 fbody)")
    );
    let a_facod = format!(
        "(fun (fdom : KExpr) (fbody : KExpr) (fbody2 : KExpr) (_hstep : beta_reduces fbody fbody2) {} (heq : Eq KExpr (KExpr.forall_ fdom fbody) {RED_T}) {} => pi_ne_let fdom fbody ty v b C heq)",
        ih("fbody", "fbody2"),
        ks("(KExpr.forall_ fdom fbody2)")
    );
    let a_zeta = format!(
        "(fun (zty : KExpr) (zval : KExpr) (zbody : KExpr) (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_T}) (kz : {}) (_kt : {}) (_kv : {}) (_kd : {}) => kz (Eq.trans KExpr (instantiate zbody zval) (instantiate b zval) (instantiate b v) (Eq.cong KExpr KExpr (fun (w : KExpr) => instantiate w zval) zbody b {ithd}) (Eq.cong KExpr KExpr (fun (w : KExpr) => instantiate b w) zval v {isnd})))",
        kz("(instantiate zbody zval)"),
        kt("(instantiate zbody zval)"),
        kv("(instantiate zbody zval)"),
        kd("(instantiate zbody zval)"),
        ithd = inj("thd"),
        isnd = inj("snd")
    );
    let a_letty = format!(
        "(fun (zty : KExpr) (zty2 : KExpr) (zval : KExpr) (zbody : KExpr) (hstep : beta_reduces zty zty2) {} (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_T}) (_kz : {}) (kt : {}) (_kv : {}) (_kd : {}) => kt zty2 (Eq.rec KExpr zty (fun (x : KExpr) (_ : Eq KExpr zty x) => beta_reduces x zty2) hstep ty {ifst}) (Eq.trans KExpr (KExpr.let_ zty2 zval zbody) (KExpr.let_ zty2 v zbody) (KExpr.let_ zty2 v b) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ zty2 w zbody) zval v {isnd}) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ zty2 v w) zbody b {ithd})))",
        ih("zty", "zty2"),
        kz("(KExpr.let_ zty2 zval zbody)"),
        kt("(KExpr.let_ zty2 zval zbody)"),
        kv("(KExpr.let_ zty2 zval zbody)"),
        kd("(KExpr.let_ zty2 zval zbody)"),
        ifst = inj("fst"),
        isnd = inj("snd"),
        ithd = inj("thd")
    );
    let a_letval = format!(
        "(fun (zty : KExpr) (zval : KExpr) (zval2 : KExpr) (zbody : KExpr) (hstep : beta_reduces zval zval2) {} (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_T}) (_kz : {}) (_kt : {}) (kv : {}) (_kd : {}) => kv zval2 (Eq.rec KExpr zval (fun (x : KExpr) (_ : Eq KExpr zval x) => beta_reduces x zval2) hstep v {isnd}) (Eq.trans KExpr (KExpr.let_ zty zval2 zbody) (KExpr.let_ ty zval2 zbody) (KExpr.let_ ty zval2 b) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w zval2 zbody) zty ty {ifst}) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ty zval2 w) zbody b {ithd})))",
        ih("zval", "zval2"),
        kz("(KExpr.let_ zty zval2 zbody)"),
        kt("(KExpr.let_ zty zval2 zbody)"),
        kv("(KExpr.let_ zty zval2 zbody)"),
        kd("(KExpr.let_ zty zval2 zbody)"),
        isnd = inj("snd"),
        ifst = inj("fst"),
        ithd = inj("thd")
    );
    let a_letbd = format!(
        "(fun (zty : KExpr) (zval : KExpr) (zbody : KExpr) (zbody2 : KExpr) (hstep : beta_reduces zbody zbody2) {} (heq : Eq KExpr (KExpr.let_ zty zval zbody) {RED_T}) (_kz : {}) (_kt : {}) (_kv : {}) (kd : {}) => kd zbody2 (Eq.rec KExpr zbody (fun (x : KExpr) (_ : Eq KExpr zbody x) => beta_reduces x zbody2) hstep b {ithd}) (Eq.trans KExpr (KExpr.let_ zty zval zbody2) (KExpr.let_ ty zval zbody2) (KExpr.let_ ty v zbody2) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w zval zbody2) zty ty {ifst}) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ty w zbody2) zval v {isnd})))",
        ih("zbody", "zbody2"),
        kz("(KExpr.let_ zty zval zbody2)"),
        kt("(KExpr.let_ zty zval zbody2)"),
        kv("(KExpr.let_ zty zval zbody2)"),
        kd("(KExpr.let_ zty zval zbody2)"),
        ithd = inj("thd"),
        ifst = inj("fst"),
        isnd = inj("snd")
    );
    let a_iota = format!(
        "(fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : Eq KExpr e0 {RED_T}) {} => {})",
        ks("e02"),
        iota_kill(RED_T)
    );
    let a_proj = format!(
        "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub2 : KExpr) (_hstep : beta_reduces psub psub2) {} (heq : Eq KExpr (KExpr.proj ps pidx psub) {RED_T}) {} => proj_ne_let ps pidx psub ty v b C heq)",
        ih("psub", "psub2"),
        ks("(KExpr.proj ps pidx psub2)")
    );
    format!(
        "fun (ty : KExpr) (v : KExpr) (b : KExpr) (g2 : KExpr) (C : Type) (hb : beta_reduces {RED_T} g2) (kZeta : {}) (kTy : {}) (kVal : {}) (kBody : {}) => beta_reduces.rec {mot} {a_beta} {a_appl} {a_appr} {a_lamty} {a_lambd} {a_pidom} {a_picod} {a_fadom} {a_facod} {a_zeta} {a_letty} {a_letval} {a_letbd} {a_iota} {a_proj} {RED_T} g2 hb (Eq.refl KExpr {RED_T}) kZeta kTy kVal kBody",
        kz("g2"),
        kt("g2"),
        kv("g2"),
        kd("g2")
    )
}

// ---------------- the whnf_step-level wrappers ----------------
// whnf_step's uniform (e, e') constructor prefix IS promoted, so its recursor
// takes the indices first and a motive over the value only (the
// no_whnf_step_bvar calling convention). The delta arm dies computationally:
// delta_reduct = opt_bind over kexpr_const_name (kapp_fn e), none on both
// redex shapes.

pub(super) fn ty_betaredex_whnf_inv() -> String {
    format!(
        "forall (ty : KExpr) (b : KExpr) (a : KExpr) (g2 : KExpr) (C : Type), whnf_step {RED_A} g2 -> (Eq KExpr g2 (instantiate b a) -> C) -> (forall (ty2 : KExpr), beta_reduces ty ty2 -> Eq KExpr g2 (KExpr.app (KExpr.lam ty2 b) a) -> C) -> (forall (b2 : KExpr), beta_reduces b b2 -> Eq KExpr g2 (KExpr.app (KExpr.lam ty b2) a) -> C) -> (forall (a2 : KExpr), beta_reduces a a2 -> Eq KExpr g2 (KExpr.app (KExpr.lam ty b) a2) -> C) -> C"
    )
}

pub(super) fn val_betaredex_whnf_inv() -> String {
    format!(
        "fun (ty : KExpr) (b : KExpr) (a : KExpr) (g2 : KExpr) (C : Type) (hs : whnf_step {RED_A} g2) (kBeta : Eq KExpr g2 (instantiate b a) -> C) (kTy : forall (ty2 : KExpr), beta_reduces ty ty2 -> Eq KExpr g2 (KExpr.app (KExpr.lam ty2 b) a) -> C) (kBody : forall (b2 : KExpr), beta_reduces b b2 -> Eq KExpr g2 (KExpr.app (KExpr.lam ty b2) a) -> C) (kArg : forall (a2 : KExpr), beta_reduces a a2 -> Eq KExpr g2 (KExpr.app (KExpr.lam ty b) a2) -> C) => whnf_step.rec {RED_A} g2 (fun (_ : whnf_step {RED_A} g2) => C) (fun (hbr : beta_reduces {RED_A} g2) => betaRedex_beta_inv ty b a g2 C hbr kBeta kTy kBody kArg) (fun (hdr : delta_reduces {RED_A} g2) => delta_step_head_none_absurd_type (red_def the_red_env) {RED_A} g2 C (Eq.refl (OptionType Name) (OptionType.none Name)) (delta_reduces_to_step {RED_A} g2 hdr)) hs"
    )
}

pub(super) fn ty_letredex_whnf_inv() -> String {
    format!(
        "forall (ty : KExpr) (v : KExpr) (b : KExpr) (g2 : KExpr) (C : Type), whnf_step {RED_T} g2 -> (Eq KExpr g2 (instantiate b v) -> C) -> (forall (ty2 : KExpr), beta_reduces ty ty2 -> Eq KExpr g2 (KExpr.let_ ty2 v b) -> C) -> (forall (v2 : KExpr), beta_reduces v v2 -> Eq KExpr g2 (KExpr.let_ ty v2 b) -> C) -> (forall (b2 : KExpr), beta_reduces b b2 -> Eq KExpr g2 (KExpr.let_ ty v b2) -> C) -> C"
    )
}

pub(super) fn val_letredex_whnf_inv() -> String {
    format!(
        "fun (ty : KExpr) (v : KExpr) (b : KExpr) (g2 : KExpr) (C : Type) (hs : whnf_step {RED_T} g2) (kZeta : Eq KExpr g2 (instantiate b v) -> C) (kTy : forall (ty2 : KExpr), beta_reduces ty ty2 -> Eq KExpr g2 (KExpr.let_ ty2 v b) -> C) (kVal : forall (v2 : KExpr), beta_reduces v v2 -> Eq KExpr g2 (KExpr.let_ ty v2 b) -> C) (kBody : forall (b2 : KExpr), beta_reduces b b2 -> Eq KExpr g2 (KExpr.let_ ty v b2) -> C) => whnf_step.rec {RED_T} g2 (fun (_ : whnf_step {RED_T} g2) => C) (fun (hbr : beta_reduces {RED_T} g2) => letHead_beta_inv ty v b g2 C hbr kZeta kTy kVal kBody) (fun (hdr : delta_reduces {RED_T} g2) => delta_step_head_none_absurd_type (red_def the_red_env) {RED_T} g2 C (Eq.refl (OptionType Name) (OptionType.none Name)) (delta_reduces_to_step {RED_T} g2 hdr)) hs"
    )
}

// ================================================================
// Group D — the two engines: the triple-Acc Tait argument.
// ================================================================

pub(super) fn val_candexp_beta() -> String {
    let famb = |bv: &str| {
        format!(
            "forall (b2 : KExpr), betaStar {bv} b2 -> forall (a2 : KExpr), SA a2 -> S (instantiate b2 a2)"
        )
    };
    let p_ty = |tyv: &str| {
        format!(
            "forall (b : KExpr), whnf_acc b -> ({}) -> forall (a : KExpr), whnf_acc a -> SA a -> S (KExpr.app (KExpr.lam {tyv} b) a)",
            famb("b")
        )
    };
    let p_b = |bv: &str| {
        format!(
            "({}) -> forall (a : KExpr), whnf_acc a -> SA a -> S (KExpr.app (KExpr.lam ty0 {bv}) a)",
            famb(bv)
        )
    };
    let core = "isCandSet_cr3 S hS (KExpr.app (KExpr.lam ty0 b0) a0) ConstFreeUnit.triv (fun (e2 : KExpr) (hstep : whnf_step (KExpr.app (KExpr.lam ty0 b0) a0) e2) => betaRedex_whnf_inv ty0 b0 a0 e2 (S e2) hstep (fun (heq : Eq KExpr e2 (instantiate b0 a0)) => Eq.substType KExpr (fun (w : KExpr) => S w) (instantiate b0 a0) e2 (Eq.symm KExpr e2 (instantiate b0 a0) heq) (hfam b0 (betaStar.refl b0) a0 hmem)) (fun (t2 : KExpr) (hst : beta_reduces ty0 t2) (heq : Eq KExpr e2 (KExpr.app (KExpr.lam t2 b0) a0)) => Eq.substType KExpr (fun (w : KExpr) => S w) (KExpr.app (KExpr.lam t2 b0) a0) e2 (Eq.symm KExpr e2 (KExpr.app (KExpr.lam t2 b0) a0) heq) (ihty t2 (whnf_step.beta ty0 t2 hst) b0 (whnf_acc.intro b0 hbs) hfam a0 (whnf_acc.intro a0 has) hmem)) (fun (u2 : KExpr) (hsb : beta_reduces b0 u2) (heq : Eq KExpr e2 (KExpr.app (KExpr.lam ty0 u2) a0)) => Eq.substType KExpr (fun (w : KExpr) => S w) (KExpr.app (KExpr.lam ty0 u2) a0) e2 (Eq.symm KExpr e2 (KExpr.app (KExpr.lam ty0 u2) a0) heq) (ihb u2 (whnf_step.beta b0 u2 hsb) (fun (b3 : KExpr) (hstar : betaStar u2 b3) (a3 : KExpr) (ha3 : SA a3) => hfam b3 (betaStar.step b0 u2 b3 hsb hstar) a3 ha3) a0 (whnf_acc.intro a0 has) hmem)) (fun (w2 : KExpr) (hsa : beta_reduces a0 w2) (heq : Eq KExpr e2 (KExpr.app (KExpr.lam ty0 b0) w2)) => Eq.substType KExpr (fun (w : KExpr) => S w) (KExpr.app (KExpr.lam ty0 b0) w2) e2 (Eq.symm KExpr e2 (KExpr.app (KExpr.lam ty0 b0) w2) heq) (iha w2 (whnf_step.beta a0 w2 hsa) (isCandSet_cr2 SA hSA a0 w2 hmem (whnf_step.beta a0 w2 hsa)))))"
        .to_string();
    let arm_a = format!(
        "(fun (a0 : KExpr) (has : forall (w2 : KExpr), whnf_step a0 w2 -> whnf_acc w2) (iha : forall (w2 : KExpr), whnf_step a0 w2 -> SA w2 -> S (KExpr.app (KExpr.lam ty0 b0) w2)) (hmem : SA a0) => {core})"
    );
    let arm_b = format!(
        "(fun (b0 : KExpr) (hbs : forall (u2 : KExpr), whnf_step b0 u2 -> whnf_acc u2) (ihb : forall (u2 : KExpr), whnf_step b0 u2 -> {pbu}) (hfam : {fam0}) (aarg : KExpr) (haacc : whnf_acc aarg) => whnf_acc.rec (fun (a0 : KExpr) (_ : whnf_acc a0) => SA a0 -> S (KExpr.app (KExpr.lam ty0 b0) a0)) {arm_a} aarg haacc)",
        pbu = p_b("u2"),
        fam0 = famb("b0")
    );
    let arm_ty = format!(
        "(fun (ty0 : KExpr) (_htys : forall (t2 : KExpr), whnf_step ty0 t2 -> whnf_acc t2) (ihty : forall (t2 : KExpr), whnf_step ty0 t2 -> {ptyt}) (barg : KExpr) (hbacc : whnf_acc barg) => whnf_acc.rec (fun (b0 : KExpr) (_ : whnf_acc b0) => {pb0}) {arm_b} barg hbacc)",
        ptyt = p_ty("t2"),
        pb0 = p_b("b0")
    );
    format!(
        "fun (S : KExpr -> Type) (SA : KExpr -> Type) (hS : IsCandSet S) (hSA : IsCandSet SA) (ty : KExpr) (hty : whnf_acc ty) (b : KExpr) (hb : whnf_acc b) (hfam0 : {famb_b}) (a : KExpr) (ha : SA a) => whnf_acc.rec (fun (ty0 : KExpr) (_ : whnf_acc ty0) => {pty0}) {arm_ty} ty hty b hb hfam0 a (isCandSet_cr1 SA hSA a ha) ha",
        famb_b = famb("b"),
        pty0 = p_ty("ty0")
    )
}

pub(super) fn ty_zeta_expand() -> String {
    "forall (ty : KExpr), whnf_acc ty -> forall (b : KExpr), whnf_acc b -> (forall (b2 : KExpr), betaStar b b2 -> forall (v2 : KExpr), whnf_acc v2 -> whnf_acc (instantiate b2 v2)) -> forall (v : KExpr), whnf_acc v -> whnf_acc (KExpr.let_ ty v b)".to_string()
}

pub(super) fn val_zeta_expand() -> String {
    let famz = |bv: &str| {
        format!(
            "forall (b2 : KExpr), betaStar {bv} b2 -> forall (v2 : KExpr), whnf_acc v2 -> whnf_acc (instantiate b2 v2)"
        )
    };
    let p_ty = |tyv: &str| {
        format!(
            "forall (b : KExpr), whnf_acc b -> ({}) -> forall (v : KExpr), whnf_acc v -> whnf_acc (KExpr.let_ {tyv} v b)",
            famz("b")
        )
    };
    let p_b = |bv: &str| {
        format!(
            "({}) -> forall (v : KExpr), whnf_acc v -> whnf_acc (KExpr.let_ ty0 v {bv})",
            famz(bv)
        )
    };
    let core = "whnf_acc.intro (KExpr.let_ ty0 v0 b0) (fun (e2 : KExpr) (hstep : whnf_step (KExpr.let_ ty0 v0 b0) e2) => letRedex_whnf_inv ty0 v0 b0 e2 (whnf_acc e2) hstep (fun (heq : Eq KExpr e2 (instantiate b0 v0)) => Eq.substType KExpr (fun (w : KExpr) => whnf_acc w) (instantiate b0 v0) e2 (Eq.symm KExpr e2 (instantiate b0 v0) heq) (hfam b0 (betaStar.refl b0) v0 (whnf_acc.intro v0 hvs))) (fun (t2 : KExpr) (hst : beta_reduces ty0 t2) (heq : Eq KExpr e2 (KExpr.let_ t2 v0 b0)) => Eq.substType KExpr (fun (w : KExpr) => whnf_acc w) (KExpr.let_ t2 v0 b0) e2 (Eq.symm KExpr e2 (KExpr.let_ t2 v0 b0) heq) (ihty t2 (whnf_step.beta ty0 t2 hst) b0 (whnf_acc.intro b0 hbs) hfam v0 (whnf_acc.intro v0 hvs))) (fun (w2 : KExpr) (hsv : beta_reduces v0 w2) (heq : Eq KExpr e2 (KExpr.let_ ty0 w2 b0)) => Eq.substType KExpr (fun (w : KExpr) => whnf_acc w) (KExpr.let_ ty0 w2 b0) e2 (Eq.symm KExpr e2 (KExpr.let_ ty0 w2 b0) heq) (ihv w2 (whnf_step.beta v0 w2 hsv))) (fun (u2 : KExpr) (hsb : beta_reduces b0 u2) (heq : Eq KExpr e2 (KExpr.let_ ty0 v0 u2)) => Eq.substType KExpr (fun (w : KExpr) => whnf_acc w) (KExpr.let_ ty0 v0 u2) e2 (Eq.symm KExpr e2 (KExpr.let_ ty0 v0 u2) heq) (ihb u2 (whnf_step.beta b0 u2 hsb) (fun (b3 : KExpr) (hstar : betaStar u2 b3) (v3 : KExpr) (hv3 : whnf_acc v3) => hfam b3 (betaStar.step b0 u2 b3 hsb hstar) v3 hv3) v0 (whnf_acc.intro v0 hvs))))"
        .to_string();
    let arm_v = format!(
        "(fun (v0 : KExpr) (hvs : forall (w2 : KExpr), whnf_step v0 w2 -> whnf_acc w2) (ihv : forall (w2 : KExpr), whnf_step v0 w2 -> whnf_acc (KExpr.let_ ty0 w2 b0)) => {core})"
    );
    let arm_b = format!(
        "(fun (b0 : KExpr) (hbs : forall (u2 : KExpr), whnf_step b0 u2 -> whnf_acc u2) (ihb : forall (u2 : KExpr), whnf_step b0 u2 -> {pbu}) (hfam : {fam0}) (varg : KExpr) (hvacc : whnf_acc varg) => whnf_acc.rec (fun (v0 : KExpr) (_ : whnf_acc v0) => whnf_acc (KExpr.let_ ty0 v0 b0)) {arm_v} varg hvacc)",
        pbu = p_b("u2"),
        fam0 = famz("b0")
    );
    let arm_ty = format!(
        "(fun (ty0 : KExpr) (_htys : forall (t2 : KExpr), whnf_step ty0 t2 -> whnf_acc t2) (ihty : forall (t2 : KExpr), whnf_step ty0 t2 -> {ptyt}) (barg : KExpr) (hbacc : whnf_acc barg) => whnf_acc.rec (fun (b0 : KExpr) (_ : whnf_acc b0) => {pb0}) {arm_b} barg hbacc)",
        ptyt = p_ty("t2"),
        pb0 = p_b("b0")
    );
    format!(
        "fun (ty : KExpr) (hty : whnf_acc ty) (b : KExpr) (hb : whnf_acc b) (hfam0 : {famz_b}) (v : KExpr) (hv : whnf_acc v) => whnf_acc.rec (fun (ty0 : KExpr) (_ : whnf_acc ty0) => {pty0}) {arm_ty} ty hty b hb hfam0 v hv",
        famz_b = famz("b"),
        pty0 = p_ty("ty0")
    )
}

// ================================================================
// Group E — the beta witnesses: positive (through the engine) and the
// argument-premise-necessity pair.
// ================================================================

pub(super) const TY_CANDEXP_BETA_BASE_WITNESS: &str = "whnf_acc (KExpr.app (KExpr.lam (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))";
pub(super) const VAL_CANDEXP_BETA_BASE_WITNESS: &str = "candExp_beta (fun (e : KExpr) => whnf_acc e) (fun (e : KExpr) => whnf_acc e) isCand_whnfAcc isCand_whnfAcc (KExpr.bvar Nat.zero) cand_var_witness (KExpr.bvar Nat.zero) cand_var_witness (betaStar_bvar0_fam (fun (e : KExpr) => whnf_acc e)) (KExpr.bvar Nat.zero) cand_var_witness";

pub(super) const SRC_APP_OMEGA: &str = "def appOmega : KExpr := KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)) omegaLoop";

pub(super) const TY_APP_OMEGA_STEP_SELF: &str = "whnf_step appOmega appOmega";
pub(super) const VAL_APP_OMEGA_STEP_SELF: &str = "whnf_step.beta appOmega appOmega (beta_reduces.app_right (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)) omegaLoop omegaLoop (beta_reduces.beta (KExpr.sort Level.zero) (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) selfApp))";

pub(super) const TY_SELFLOOP_NOT_WHNFACC: &str =
    "forall (e : KExpr), whnf_step e e -> whnf_acc e -> Empty";
pub(super) const VAL_SELFLOOP_NOT_WHNFACC: &str = "fun (e : KExpr) (hself : whnf_step e e) (h : whnf_acc e) => whnf_acc.rec (fun (e0 : KExpr) (_ : whnf_acc e0) => Eq KExpr e e0 -> Empty) (fun (e0 : KExpr) (_hsteps : forall (e1 : KExpr), whnf_step e0 e1 -> whnf_acc e1) (ih : forall (e1 : KExpr), whnf_step e0 e1 -> Eq KExpr e e1 -> Empty) (heq : Eq KExpr e e0) => ih e (Eq.substType KExpr (fun (z : KExpr) => whnf_step z e) e e0 heq hself) (Eq.refl KExpr e)) e h (Eq.refl KExpr e)";

pub(super) const TY_APP_OMEGA_ARG_ACC_NECESSARY: &str = "AndType (whnf_acc (instantiate (KExpr.sort Level.zero) omegaLoop)) (whnf_acc appOmega -> Empty)";
pub(super) const VAL_APP_OMEGA_ARG_ACC_NECESSARY: &str = "AndType.intro (whnf_acc (instantiate (KExpr.sort Level.zero) omegaLoop)) (whnf_acc appOmega -> Empty) (whnfAcc_sort Level.zero) (fun (h : whnf_acc appOmega) => selfLoop_not_whnfAcc appOmega appOmega_step_self h)";

// ================================================================
// Group F — the zeta genericity refutation.
// ================================================================

pub(super) const SRC_ZETA_PROBE: &str = "def zetaProbe : KExpr := KExpr.let_ (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)";

pub(super) const SRC_ZETA_GUARD_SET: &str =
    "def zetaGuardSet (e : KExpr) : Type := AndType (whnf_acc e) (whnfStar e zetaProbe -> Empty)";

pub(super) const TY_ISCAND_ZETAGUARD: &str = "IsCandSet (fun (e : KExpr) => zetaGuardSet e)";
pub(super) fn val_iscand_zetaguard() -> String {
    let cr1 = "(fun (e : KExpr) (h : zetaGuardSet e) => AndType.left (whnf_acc e) (whnfStar e zetaProbe -> Empty) h)";
    let cr2 = "(fun (e : KExpr) (e2 : KExpr) (h : zetaGuardSet e) (hs : whnf_step e e2) => AndType.intro (whnf_acc e2) (whnfStar e2 zetaProbe -> Empty) (whnfAcc_inv_step e (AndType.left (whnf_acc e) (whnfStar e zetaProbe -> Empty) h) e2 hs) (fun (hst : whnfStar e2 zetaProbe) => AndType.right (whnf_acc e) (whnfStar e zetaProbe -> Empty) h (whnfStar.step e e2 zetaProbe hs hst)))";
    let star_refl_arm = "(fun (x : KExpr) (hteq : Eq KExpr x zetaProbe) (hseq : Eq KExpr x e) => Eq.substType KExpr (fun (w : KExpr) => Neutral w) e zetaProbe (Eq.trans KExpr e x zetaProbe (Eq.symm KExpr x e hseq) hteq) hn)";
    let star_step_arm = "(fun (x : KExpr) (x2 : KExpr) (x3 : KExpr) (hs : whnf_step x x2) (hrest : whnfStar x2 x3) (_ih : Eq KExpr x3 zetaProbe -> Eq KExpr x2 e -> Empty) (hteq : Eq KExpr x3 zetaProbe) (hseq : Eq KExpr x e) => AndType.right (whnf_acc x2) (whnfStar x2 zetaProbe -> Empty) (hred x2 (Eq.substType KExpr (fun (w : KExpr) => whnf_step w x2) x e hseq hs)) (Eq.substType KExpr (fun (w : KExpr) => whnfStar x2 w) x3 zetaProbe hteq hrest))";
    let cr3 = format!(
        "(fun (e : KExpr) (hn : Neutral e) (hred : forall (e2 : KExpr), whnf_step e e2 -> zetaGuardSet e2) => AndType.intro (whnf_acc e) (whnfStar e zetaProbe -> Empty) (whnf_acc.intro e (fun (e2 : KExpr) (hs : whnf_step e e2) => AndType.left (whnf_acc e2) (whnfStar e2 zetaProbe -> Empty) (hred e2 hs))) (fun (hst : whnfStar e zetaProbe) => whnfStar.rec (fun (s : KExpr) (t : KExpr) (_ : whnfStar s t) => Eq KExpr t zetaProbe -> Eq KExpr s e -> Empty) {star_refl_arm} {star_step_arm} e zetaProbe hst (Eq.refl KExpr zetaProbe) (Eq.refl KExpr e)))"
    );
    format!("isCandSet_intro (fun (e : KExpr) => zetaGuardSet e) {cr1} {cr2} {cr3}")
}

pub(super) fn ty_zeta_not_generic() -> String {
    format!("({}) -> Empty", ty_zeta_engine_hypothesis())
}

pub(super) fn val_zeta_not_generic() -> String {
    format!(
        "fun (E : {hyp}) => AndType.right (whnf_acc zetaProbe) (whnfStar zetaProbe zetaProbe -> Empty) (E (fun (e : KExpr) => zetaGuardSet e) (fun (e : KExpr) => zetaGuardSet e) isCand_zetaGuard isCand_zetaGuard (KExpr.bvar (Nat.succ Nat.zero)) (cand_var_mem (fun (e : KExpr) => whnf_acc e) isCand_whnfAcc (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero) cand_var_witness (betaStar_bvar0_fam (fun (e : KExpr) => zetaGuardSet e)) (KExpr.bvar (Nat.succ Nat.zero)) (cand_var_mem (fun (e : KExpr) => zetaGuardSet e) isCand_zetaGuard (Nat.succ Nat.zero))) (whnfStar.refl zetaProbe)",
        hyp = ty_zeta_engine_hypothesis()
    )
}

// ==== R1 SOURCES END ====

impl Specification {
    /// Register the R1 head-expansion engine layer: the two star closures,
    /// the bvar/star toolbox, the CPS step inversions for the beta and zeta
    /// redex shapes, the beta engine over any candidate set, the zeta engine
    /// at the base whole-SN set, and the discriminating witnesses (positive
    /// engine run, the argument-premise-necessity pair, and the zeta
    /// genericity refutation).
    ///
    /// MUST be registered AFTER `add_candmodel_construct_r0` (`IsCandSet`
    /// interface + `whnfAcc_inv_step` + omega objects), which itself sits
    /// after `add_dependent_sn_richmodel` (`Neutral` / `no_whnf_step_bvar` /
    /// `whnfAcc_sort`). Also consumes: the discrimination lemmas
    /// (`add_expr_model_*_discrimination`), `iota_reduces_to_step` /
    /// `iota_step_head_none_absurd_type` / `delta_reduces_to_step` /
    /// `delta_step_head_none_absurd_type` (iota/delta bridges +
    /// par-reduction absurdity helpers), `lift_at_amount_zero`
    /// (`add_expr_model_lift_lemmas`), and `whnf_reduction` /
    /// `whnf_progress` / `expr_model` foundations.
    pub(super) fn add_candmodel_construct_r1(&mut self) -> Result<(), SpecError> {
        // --- Group A: the star closures ---
        self.add_inductive(
            SRC_BETA_STAR,
            "betaStar: reflexive-transitive closure of beta_reduces (cons-from-the-left, the \
             whnf_to/natSteps star shape). Indexes the body-development family premise of the \
             R1 head-expansion engines: one lam_body congruence step extends the family by one \
             betaStar.step, so no substitution-transport lemma is needed.",
        )?;
        self.add_inductive(
            SRC_WHNF_STAR,
            "whnfStar: reflexive-transitive closure of the FULL whnf_step (beta/zeta/iota union \
             delta at the fixed the_red_env). Reachability order for the zetaGuardSet \
             refutation set — the second component must be closed under EVERY step, delta \
             included, which betaStar cannot express.",
        )?;

        // --- Group B: bvar/star toolbox ---
        // NAMED `cand_inst_bvar0`, not `inst_bvar0`: `add_acc_wtype` has
        // registered a definition called `inst_bvar0` -- the same proposition,
        // proved via `lift_zero_identity` instead of `lift_at_amount_zero` --
        // since 752baa12f (2026-07-25). This bundle runs at bundles.rs:947 and
        // `add_acc_wtype` at :1537, so claiming the bare name here did not
        // collide locally: it made the INCUMBENT's later registration fail with
        // `Duplicate declaration: inst_bvar0`, which aborts `Specification::new()`
        // and therefore every one of the 55 integration targets that builds the
        // full spec. Keep this name distinct from the acc_wtype one.
        self.add_definition(SpecDefinition {
            name: "cand_inst_bvar0".to_string(),
            type_src: TY_INST_BVAR0.to_string(),
            value_src: Some(VAL_INST_BVAR0.to_string()),
            is_axiom: false,
            description: "Computation pin: instantiate (bvar 0) v = v. NOT definitional on an \
                          open v — instantiate (bvar 0) v computes to lift_at v 0 0, which is \
                          stuck on a variable — so this is lift_at_amount_zero at cutoff 0, \
                          transported through the (fully computing) instantiate_bvar_at chain. \
                          The identity every witness family-discharge transports along. Zero \
                          axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate".to_string(),
                "lift_at_amount_zero".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "betaStar_bvar_collapse".to_string(),
            type_src: TY_BETASTAR_BVAR_COLLAPSE.to_string(),
            value_src: Some(VAL_BETASTAR_BVAR_COLLAPSE.to_string()),
            is_axiom: false,
            description: "A betaStar chain from a bvar is trivial: betaStar (bvar i) b2 forces \
                          b2 = bvar i. betaStar.rec with a source-eq motive; the step arm is \
                          absurd by no_whnf_step_bvar (the beta_reduces step wrapped as a \
                          whnf_step), routed Empty.rec-through because the Prop-valued Eq goal \
                          cannot instantiate no_whnf_step_bvar's Type-valued C. Zero \
                          axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "betaStar".to_string(),
                "betaStar.rec".to_string(),
                "no_whnf_step_bvar".to_string(),
                "whnf_step.beta".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "betaStar_bvar0_fam".to_string(),
            type_src: TY_BETASTAR_BVAR0_FAM.to_string(),
            value_src: Some(VAL_BETASTAR_BVAR0_FAM.to_string()),
            is_axiom: false,
            description: "The identity-body family discharge: for b = bvar 0, every S-member v2 \
                          gives S (instantiate b2 v2) for every betaStar-development b2 of the \
                          body (the star collapses by betaStar_bvar_collapse; instantiate \
                          (bvar 0) v2 = v2 by cand_inst_bvar0). Generic in S — no candidate laws \
                          consumed. Feeds both the positive engine witness and the zeta \
                          refutation. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "betaStar".to_string(),
                "betaStar_bvar_collapse".to_string(),
                "cand_inst_bvar0".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group C: CPS inversions ---
        self.add_definition(SpecDefinition {
            name: "lamHead_beta_inv".to_string(),
            type_src: ty_lamhead_beta_inv(),
            value_src: Some(val_lamhead_beta_inv()),
            is_axiom: false,
            description: "CPS inversion of a beta_reduces step out of a lam head: only lam_ty \
                          and lam_body apply (continuations receive the stepped component, \
                          transported through lam injectivity). 15-arm beta_reduces.rec with a \
                          source-eq motive (wRecSpine1_step_inv idiom); every other source \
                          shape dies by discrimination, the iota arm computationally \
                          (kexpr_const_name (kapp_fn (lam ty b)) = none). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces.rec".to_string(),
                "app_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "let_ne_lam".to_string(),
                "proj_ne_lam".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "iota_reduces_to_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "betaRedex_beta_inv".to_string(),
            type_src: ty_betaredex_beta_inv(),
            value_src: Some(val_betaredex_beta_inv()),
            is_axiom: false,
            description: "CPS inversion of a beta_reduces step out of the beta redex \
                          app (lam ty b) a: top beta (contractum pinned to instantiate b a via \
                          app/lam injectivity), or exactly one of the three congruence \
                          positions ty/b/a (the app_left arm recurses through \
                          lamHead_beta_inv). 15-arm beta_reduces.rec, source-eq motive; \
                          head-iota killed computationally. THE complete reduct classification \
                          of the beta redex under beta_reduces. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces.rec".to_string(),
                "lamHead_beta_inv".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
                "lam_inj_snd".to_string(),
                "lam_ne_app".to_string(),
                "pi_ne_app".to_string(),
                "let_ne_app".to_string(),
                "proj_ne_app".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "iota_reduces_to_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "betaRedex_whnf_inv".to_string(),
            type_src: ty_betaredex_whnf_inv(),
            value_src: Some(val_betaredex_whnf_inv()),
            is_axiom: false,
            description: "Full whnf_step inversion at the beta redex: the beta leg dispatches \
                          to betaRedex_beta_inv; the delta leg is absurd computationally \
                          (delta_reduct's head lookup: kexpr_const_name (kapp_fn (app (lam ty \
                          b) a)) = none, via delta_step_head_none_absurd_type). The engine's \
                          cr3 feed. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step.rec".to_string(),
                "betaRedex_beta_inv".to_string(),
                "delta_step_head_none_absurd_type".to_string(),
                "delta_reduces_to_step".to_string(),
                "red_def".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "letHead_beta_inv".to_string(),
            type_src: ty_lethead_beta_inv(),
            value_src: Some(val_lethead_beta_inv()),
            is_axiom: false,
            description: "CPS inversion of a beta_reduces step out of the zeta redex \
                          let_ ty v b: top zeta (contractum pinned to instantiate b v via \
                          let_ injectivity) or exactly one of the three let_ congruence \
                          positions. 15-arm beta_reduces.rec, source-eq motive; head-iota \
                          killed computationally (a let_ head is never a const spine). Zero \
                          axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces.rec".to_string(),
                "app_ne_let".to_string(),
                "lam_ne_let".to_string(),
                "pi_ne_let".to_string(),
                "proj_ne_let".to_string(),
                "let_inj_fst".to_string(),
                "let_inj_snd".to_string(),
                "let_inj_thd".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "iota_reduces_to_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "letRedex_whnf_inv".to_string(),
            type_src: ty_letredex_whnf_inv(),
            value_src: Some(val_letredex_whnf_inv()),
            is_axiom: false,
            description: "Full whnf_step inversion at the zeta redex: beta leg to \
                          letHead_beta_inv, delta leg absurd computationally. The \
                          whnfAcc_zeta_expand intro feed. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step.rec".to_string(),
                "letHead_beta_inv".to_string(),
                "delta_step_head_none_absurd_type".to_string(),
                "delta_reduces_to_step".to_string(),
                "red_def".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group D: the engines ---
        self.add_definition(SpecDefinition {
            name: "candExp_beta".to_string(),
            type_src: ty_candexp_beta(),
            value_src: Some(val_candexp_beta()),
            is_axiom: false,
            description: "THE BETA HEAD-EXPANSION ENGINE (corpus candExp, Stratified/Cand.lean \
                          :60, over the spec's FULL env-fixed step relation): for candidate \
                          sets S (result) and SA (argument), whnf_acc ty, whnf_acc b, and the \
                          contractum family — S (instantiate b2 a2) for every betaStar-\
                          development b2 of b and every SA-member a2 — every SA-member a puts \
                          the redex app (lam ty b) a in S. Triple nested whnf_acc.rec (ty, b, \
                          a) + cr3 at the NEUTRAL redex (app heads are ConstFreeUnit) + \
                          betaRedex_whnf_inv; the lam_body arm consumes one betaStar.step, the \
                          app_right arm one SA-cr2 step, whnf_acc a comes from SA-cr1. \
                          HONESTY: the premise is the CandModel.redAbstraction family shape \
                          extended over body developments, STRONGER than the corpus's single \
                          contractum — the corpus spelling needs the substitution-step lemmas \
                          (iota-under-psubst over the real env), which are R2+ build items, \
                          not R1 bricks. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "isCandSet_cr1".to_string(),
                "isCandSet_cr2".to_string(),
                "isCandSet_cr3".to_string(),
                "betaStar".to_string(),
                "betaRedex_whnf_inv".to_string(),
                "whnf_acc.rec".to_string(),
                "whnf_acc.intro".to_string(),
                "whnf_step.beta".to_string(),
                "ConstFreeUnit".to_string(),
                "Neutral".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "whnfAcc_zeta_expand".to_string(),
            type_src: ty_zeta_expand(),
            value_src: Some(val_zeta_expand()),
            is_axiom: false,
            description: "THE ZETA HEAD-EXPANSION ENGINE AT THE BASE SET (corpus \
                          reducible_letE_expand, LetDeltaSN.lean:820, specialized to the \
                          whole-SN set): whnf_acc ty, whnf_acc b, the contractum family \
                          (whnf_acc (instantiate b2 v2) for every betaStar-development b2 and \
                          every whnf_acc v2), and whnf_acc v give whnf_acc (let_ ty v b). \
                          Triple nested whnf_acc.rec (ty, b, v) + whnf_acc.intro + \
                          letRedex_whnf_inv — NO cr3 and NO neutrality: Acc-intro plays cr3's \
                          role at the base set. HONESTY — base set ONLY, and necessarily so: \
                          the spec's Neutral sends let_ to Empty, and \
                          zeta_expansion_not_generic PROVES the per-candidate-set version of \
                          this engine (candExp_beta's exact shape at the let_ redex) is FALSE. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "betaStar".to_string(),
                "letRedex_whnf_inv".to_string(),
                "whnf_acc.rec".to_string(),
                "whnf_acc.intro".to_string(),
                "whnf_step.beta".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group E: beta witnesses ---
        self.add_definition(SpecDefinition {
            name: "candExp_beta_base_witness".to_string(),
            type_src: TY_CANDEXP_BETA_BASE_WITNESS.to_string(),
            value_src: Some(VAL_CANDEXP_BETA_BASE_WITNESS.to_string()),
            is_axiom: false,
            description: "Positive discriminating witness (§6.1 control): the identity redex \
                          app (lam (bvar 0) (bvar 0)) (bvar 0) is whnf_acc THROUGH the \
                          engine — candExp_beta at S = SA = the base whole-SN set, with the \
                          family discharged by betaStar_bvar0_fam and every acc premise by \
                          R0's cand_var_witness. Exercises every engine premise at concrete \
                          arguments. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "candExp_beta".to_string(),
                "isCand_whnfAcc".to_string(),
                "cand_var_witness".to_string(),
                "betaStar_bvar0_fam".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_recursive_def(
            SRC_APP_OMEGA,
            "appOmega = app (lam (sort 0) (sort 0)) omegaLoop — the beta redex whose body \
             IGNORES its argument (closed body sort 0) applied to R0's diverging omega loop. \
             The negative-guard object: its contractum is whnf_acc, itself is not. Plain def.",
        )?;
        self.add_definition(SpecDefinition {
            name: "appOmega_step_self".to_string(),
            type_src: TY_APP_OMEGA_STEP_SELF.to_string(),
            value_src: Some(VAL_APP_OMEGA_STEP_SELF.to_string()),
            is_axiom: false,
            description: "appOmega whnf_steps to ITSELF through the app_right congruence arm: \
                          the argument omegaLoop takes its R0 self-step (top beta of selfApp \
                          selfApp, contractum computing back to omegaLoop) INSIDE the redex, \
                          leaving the redex unchanged. The precise arm that makes the \
                          argument-side premise of candExp_beta load-bearing. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "appOmega".to_string(),
                "omegaLoop".to_string(),
                "selfApp".to_string(),
                "whnf_step.beta".to_string(),
                "beta_reduces.app_right".to_string(),
                "beta_reduces.beta".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "selfLoop_not_whnfAcc".to_string(),
            type_src: TY_SELFLOOP_NOT_WHNFACC.to_string(),
            value_src: Some(VAL_SELFLOOP_NOT_WHNFACC.to_string()),
            is_axiom: false,
            description: "GENERIC one-step-loop Acc refutation: any e with whnf_step e e is \
                          not whnf_acc (R0's omega_not_whnfAcc argument, generalized — \
                          whnf_acc.rec with the equality-generalized motive, the self-step \
                          transported along the equation feeding the IH at e itself). Zero \
                          axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_acc".to_string(),
                "whnf_acc.rec".to_string(),
                "whnf_step".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "appOmega_arg_acc_necessary".to_string(),
            type_src: TY_APP_OMEGA_ARG_ACC_NECESSARY.to_string(),
            value_src: Some(VAL_APP_OMEGA_ARG_ACC_NECESSARY.to_string()),
            is_axiom: false,
            description: "Negative-shaped guard (the §6.1 PAIR, task item 3): the contractum \
                          instantiate (sort 0) omegaLoop IS whnf_acc (it computes to sort 0; \
                          whnfAcc_sort), while the redex appOmega is NOT (selfLoop_not_\
                          whnfAcc on appOmega_step_self). So contractum membership alone can \
                          NEVER yield redex membership: the argument-side premise (SA a, whose \
                          cr1 face is whnf_acc a) of candExp_beta is necessary, not \
                          decorative. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "appOmega".to_string(),
                "appOmega_step_self".to_string(),
                "selfLoop_not_whnfAcc".to_string(),
                "whnfAcc_sort".to_string(),
                "AndType.intro".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group F: the zeta genericity refutation ---
        self.add_recursive_def(
            SRC_ZETA_PROBE,
            "zetaProbe = let_ (bvar 1) (bvar 1) (bvar 0) — the concrete zeta redex the guard \
             set excludes. Chosen all-bvar so every membership/irreducibility fact discharges \
             through no_whnf_step_bvar and let_ne_bvar, with contractum instantiate (bvar 0) \
             (bvar 1) = bvar 1. Plain def.",
        )?;
        self.add_recursive_def(
            SRC_ZETA_GUARD_SET,
            "zetaGuardSet e = AndType (whnf_acc e) (whnfStar e zetaProbe -> Empty): the \
             strongly-normalizing terms from which the probe redex is unreachable under the \
             full step relation. The reachability-complement construction that refutes \
             per-set zeta expansion. Plain def.",
        )?;
        self.add_definition(SpecDefinition {
            name: "isCand_zetaGuard".to_string(),
            type_src: TY_ISCAND_ZETAGUARD.to_string(),
            value_src: Some(val_iscand_zetaguard()),
            is_axiom: false,
            description: "zetaGuardSet IS a candidate set: cr1 by projection; cr2 because \
                          reachability-complements are closed under steps (star cons); cr3 \
                          because a NEUTRAL term is never the (let_-headed, Neutral = Empty) \
                          probe and its star to the probe must factor through a reduct already \
                          in the set. This is exactly where let_'s non-neutrality does the \
                          work: the same construction at an app-headed probe would fail cr3 \
                          (cr3 would force the probe in). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "isCandSet_intro".to_string(),
                "zetaGuardSet".to_string(),
                "zetaProbe".to_string(),
                "whnfStar".to_string(),
                "whnfAcc_inv_step".to_string(),
                "whnf_acc.intro".to_string(),
                "Neutral".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "zeta_expansion_not_generic".to_string(),
            type_src: ty_zeta_not_generic(),
            value_src: Some(val_zeta_not_generic()),
            is_axiom: false,
            description: "THE ZETA GENERICITY REFUTATION (§6 honesty artifact): the let_-headed \
                          head-expansion engine of EXACTLY candExp_beta's shape — same two \
                          sets, same acc premises, same contractum family, conclusion redex \
                          swapped app (lam ty b) a -> let_ ty a b (the CandModel.redLet \
                          spelling) — implies Empty. Instantiate it at S = SA = zetaGuardSet, \
                          ty = v = bvar 1, b = bvar 0: every premise holds (isCand_zetaGuard; \
                          cand_var_mem for the bvars; betaStar_bvar0_fam for the family), the \
                          conclusion is zetaGuardSet zetaProbe, and the probe reaches itself \
                          by whnfStar.refl. Corollary: zeta expansion is only available where \
                          extra structure replaces cr3 — the base whole-SN set \
                          (whnfAcc_zeta_expand) or an interp-specific argument at redLet \
                          time. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "isCand_zetaGuard".to_string(),
                "zetaGuardSet".to_string(),
                "zetaProbe".to_string(),
                "whnfStar".to_string(),
                "betaStar_bvar0_fam".to_string(),
                "cand_var_mem".to_string(),
                "cand_var_witness".to_string(),
                "isCand_whnfAcc".to_string(),
                "AndType.right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::parse_check;

    /// Every plain-def / inductive source in registration order.
    fn def_sources() -> Vec<(&'static str, String)> {
        vec![
            ("betaStar", SRC_BETA_STAR.to_string()),
            ("whnfStar", SRC_WHNF_STAR.to_string()),
            ("appOmega", SRC_APP_OMEGA.to_string()),
            ("zetaProbe", SRC_ZETA_PROBE.to_string()),
            ("zetaGuardSet", SRC_ZETA_GUARD_SET.to_string()),
        ]
    }

    /// Every (name, type, value) triple registered via `add_definition`, in
    /// registration order.
    fn theorem_sources() -> Vec<(&'static str, String, String)> {
        vec![
            (
                "cand_inst_bvar0",
                TY_INST_BVAR0.to_string(),
                VAL_INST_BVAR0.to_string(),
            ),
            (
                "betaStar_bvar_collapse",
                TY_BETASTAR_BVAR_COLLAPSE.to_string(),
                VAL_BETASTAR_BVAR_COLLAPSE.to_string(),
            ),
            (
                "betaStar_bvar0_fam",
                TY_BETASTAR_BVAR0_FAM.to_string(),
                VAL_BETASTAR_BVAR0_FAM.to_string(),
            ),
            (
                "lamHead_beta_inv",
                ty_lamhead_beta_inv(),
                val_lamhead_beta_inv(),
            ),
            (
                "betaRedex_beta_inv",
                ty_betaredex_beta_inv(),
                val_betaredex_beta_inv(),
            ),
            (
                "betaRedex_whnf_inv",
                ty_betaredex_whnf_inv(),
                val_betaredex_whnf_inv(),
            ),
            (
                "letHead_beta_inv",
                ty_lethead_beta_inv(),
                val_lethead_beta_inv(),
            ),
            (
                "letRedex_whnf_inv",
                ty_letredex_whnf_inv(),
                val_letredex_whnf_inv(),
            ),
            ("candExp_beta", ty_candexp_beta(), val_candexp_beta()),
            ("whnfAcc_zeta_expand", ty_zeta_expand(), val_zeta_expand()),
            (
                "candExp_beta_base_witness",
                TY_CANDEXP_BETA_BASE_WITNESS.to_string(),
                VAL_CANDEXP_BETA_BASE_WITNESS.to_string(),
            ),
            (
                "appOmega_step_self",
                TY_APP_OMEGA_STEP_SELF.to_string(),
                VAL_APP_OMEGA_STEP_SELF.to_string(),
            ),
            (
                "selfLoop_not_whnfAcc",
                TY_SELFLOOP_NOT_WHNFACC.to_string(),
                VAL_SELFLOOP_NOT_WHNFACC.to_string(),
            ),
            (
                "appOmega_arg_acc_necessary",
                TY_APP_OMEGA_ARG_ACC_NECESSARY.to_string(),
                VAL_APP_OMEGA_ARG_ACC_NECESSARY.to_string(),
            ),
            (
                "isCand_zetaGuard",
                TY_ISCAND_ZETAGUARD.to_string(),
                val_iscand_zetaguard(),
            ),
            (
                "zeta_expansion_not_generic",
                ty_zeta_not_generic(),
                val_zeta_not_generic(),
            ),
        ]
    }

    /// Parse-check every generated source — the fast guard for the commonest
    /// failure class (syntax-level assembly mistakes invisible to cargo
    /// check), doubly important here because the CPS inversions are
    /// format!-assembled.
    #[test]
    fn test_candmodel_r1_sources_parse() {
        for (name, src) in def_sources() {
            parse_check(&src)
                .unwrap_or_else(|e| panic!("{name} def source should parse: {e}\n{src}"));
        }
        for (name, ty, val) in theorem_sources() {
            let assembled = format!("def {name} : {ty} := {val}");
            parse_check(&assembled)
                .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
        }
    }

    /// Paren balance on every source (cheap structural guard for the long
    /// single-line proof terms).
    #[test]
    fn test_candmodel_r1_sources_paren_balanced() {
        let mut all: Vec<(String, String)> = def_sources()
            .into_iter()
            .map(|(n, s)| (n.to_string(), s))
            .collect();
        for (n, ty, val) in theorem_sources() {
            all.push((format!("{n}::ty"), ty));
            all.push((format!("{n}::val"), val));
        }
        for (name, src) in &all {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in {name}: {src}");
            }
            assert_eq!(depth, 0, "unbalanced parens in {name}: {src}");
        }
    }

    /// Shape guards. (1) The refuted zeta engine hypothesis is EXACTLY the
    /// beta engine's statement with the conclusion redex swapped — the
    /// refutation must target the engine's real shape, or it refutes a straw
    /// man. (2) Every beta_reduces-level inversion carries its computational
    /// head-iota kill, and every whnf_step-level wrapper its delta kill —
    /// dropping an arm would surface only at heavy-run time.
    #[test]
    fn test_candmodel_r1_shape_guards() {
        // (1) parallel-shape: both types are instances of engine_ty.
        assert_eq!(
            ty_candexp_beta(),
            engine_ty("(KExpr.app (KExpr.lam ty b) a)"),
            "beta engine type must be the shared engine shape at the beta redex"
        );
        assert_eq!(
            ty_zeta_engine_hypothesis(),
            engine_ty("(KExpr.let_ ty a b)"),
            "refuted hypothesis must be the shared engine shape at the zeta redex"
        );
        assert_eq!(
            ty_zeta_not_generic(),
            format!("({}) -> Empty", ty_zeta_engine_hypothesis()),
            "the refutation must negate exactly the parallel engine statement"
        );
        // (2) kill coverage.
        for (name, val) in [
            ("lamHead_beta_inv", val_lamhead_beta_inv()),
            ("betaRedex_beta_inv", val_betaredex_beta_inv()),
            ("letHead_beta_inv", val_lethead_beta_inv()),
        ] {
            assert_eq!(
                val.matches("iota_step_head_none_absurd_type").count(),
                1,
                "{name} must kill its head-iota arm exactly once"
            );
        }
        for (name, val) in [
            ("betaRedex_whnf_inv", val_betaredex_whnf_inv()),
            ("letRedex_whnf_inv", val_letredex_whnf_inv()),
        ] {
            assert_eq!(
                val.matches("delta_step_head_none_absurd_type").count(),
                1,
                "{name} must kill its delta leg exactly once"
            );
        }
    }

    /// Registration + kernel re-verification against the substitution bundle:
    /// the stage registers every constant, and every theorem — engines,
    /// inversions, witnesses, and the zeta refutation — re-typechecks in the
    /// live kernel environment.
    #[test]
    fn test_candmodel_r1_registered_and_reverifies() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();
        for name in [
            "betaStar",
            "whnfStar",
            "cand_inst_bvar0",
            "betaStar_bvar_collapse",
            "betaStar_bvar0_fam",
            "lamHead_beta_inv",
            "betaRedex_beta_inv",
            "betaRedex_whnf_inv",
            "letHead_beta_inv",
            "letRedex_whnf_inv",
            "candExp_beta",
            "whnfAcc_zeta_expand",
            "candExp_beta_base_witness",
            "appOmega",
            "appOmega_step_self",
            "selfLoop_not_whnfAcc",
            "appOmega_arg_acc_necessary",
            "zetaProbe",
            "zetaGuardSet",
            "isCand_zetaGuard",
            "zeta_expansion_not_generic",
        ] {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the candmodel_construct_r1 stage"
            );
        }
        for name in [
            "cand_inst_bvar0",
            "betaStar_bvar_collapse",
            "betaStar_bvar0_fam",
            "lamHead_beta_inv",
            "betaRedex_beta_inv",
            "betaRedex_whnf_inv",
            "letHead_beta_inv",
            "letRedex_whnf_inv",
            "candExp_beta",
            "whnfAcc_zeta_expand",
            "candExp_beta_base_witness",
            "appOmega_step_self",
            "selfLoop_not_whnfAcc",
            "appOmega_arg_acc_necessary",
            "isCand_zetaGuard",
            "zeta_expansion_not_generic",
        ] {
            spec.verify_definition(name).unwrap_or_else(|e| {
                panic!("{name} should re-typecheck in the spec environment: {e:?}")
            });
        }
    }
}
