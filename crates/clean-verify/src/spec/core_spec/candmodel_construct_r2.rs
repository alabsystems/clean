// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R2 of the candidate-model construction ladder: the delta/const head-expansion
//! ENGINE `candExp_delta` (any candidate set absorbs a bare const whose
//! `the_red_env` delta-unfolding lands in the set — via cr3 at the NEUTRAL
//! const plus the complete reduct classification `constRedex_whnf_inv`), and
//! the SUBSTITUTION-TRANSPORT UNLOCK `betaRed_inst_transport` (one full
//! `beta_reduces` step — beta, zeta, congruence AND the real-env iota arm —
//! commutes with `instantiate_at`), from which the corpus-spelling
//! single-contractum beta engine `candExp_beta_subst` is DERIVED from R1's
//! `candExp_beta` by composition, exactly as the R1 handoff projected.
//!
//! Port of the corpus `LetDeltaSN.lean` `konst_red_aux` delta case (rung
//! `let-delta-sn`) + `Stratified/Cand.lean` `candExp`'s substitution-step
//! transport per `designs/2026-08-23-spec-candmodel-port.md` §5 rung R2.
//! Builds directly on R0 (`IsCandSet`) and R1 (`candExp_beta`, `betaStar`,
//! `lamHead_beta_inv`).
//!
//! ## Honesty notes (read before quoting)
//!
//! - **R2 scope is the BARE const redex.** `candExp_delta` covers
//!   `KExpr.const c us` with NO application spine. That scope is COMPLETE for
//!   bare consts of any kind — including recursor names — because a bare const
//!   can never iota-fire (`iota_reduct_const_none`: the major-premise slot of
//!   an empty spine is `none`, unconditionally in the env), never beta/zeta-
//!   fires (wrong head shape), and delta fires only at the ROOT (`whnf_step`'s
//!   delta leg has NO congruence — `beta_reduces` embeds iota but not delta).
//!   APPLIED const spines `app (const c us) a…` — where iota genuinely fires on
//!   live recursors and delta re-applies the spine — are the R3 rung, not
//!   handled here.
//! - **The delta engine is per-set generic AND rank-free, and both are
//!   structural facts, not simplifications.** Per-set: a const IS Neutral
//!   (`Neutral (const c us)` computes to `ConstFreeUnit`), so cr3 applies —
//!   unlike zeta, whose per-set engine R1 REFUTED (`zeta_expansion_not_
//!   generic`; `Neutral (let_ …) = Empty`). Rank-free: `delta_reduct` is a
//!   total function, so the bare const's reduct set is the SINGLETON `{body}`
//!   (`delta_step_deterministic`) and cr3 closes with no Acc induction at all.
//!   The corpus `konst_red_aux` (LetDeltaSN.lean:910) wraps its delta case in
//!   a well-founded RANK recursion because it proves `Reducible` of EVERY env
//!   constant at once: the rank (`EnvAcyclic`) feeds lower-rank consts to the
//!   fundamental theorem, which discharges the body premise. Spec-side that
//!   iterated capstone is NOT an R2 target: no `EnvAcyclic`/`WfEnv` analogue
//!   is registered anywhere in core_spec (checked by grep, 2026-08-23), and
//!   the per-body premise (`S body`) is dischargeable only by an interp
//!   fundamental theorem (design rungs R5/R6). When that rung lands it must
//!   take the rank as an EXPLICIT premise — `rk : Name -> Nat` with
//!   delta-decrease `delta_step (red_def the_red_env) (const c us) body ->
//!   const_occurs c2 body -> Lt (rk c2) (rk c)` — where `const_occurs` is
//!   itself an unlanded build item (the corpus's `Tm.mentions`); see
//!   `docs/analysis/wf-ac-premises-2026-08-17.md` for why wf/ac are carried
//!   premises, proved jointly satisfiable and independently necessary, never
//!   discharged globally. `constAcc_body_acc` here is the premise-necessity
//!   guard: body membership is FORCED (whnf_acc of the const yields whnf_acc
//!   of the body), so no engine variant may drop it.
//! - **The transport is the `instantiate_at` spelling, not general `psubst` —
//!   deliberately.** The R1 handoff named
//!   `beta_reduces e e2 -> beta_reduces (psubst s e) (psubst s e2)` as the
//!   unlock. The landed iota/delta substitution-commutation tower
//!   (`iota_subst_commutes` / `delta_subst_commutes` and the whole
//!   `iota_reduct_inst_eq` machinery behind them) is `instantiate_at`-shaped;
//!   a general-`psubst` transport would need that entire tower re-derived for
//!   parallel substitutions — a campaign, not a brick, and it is NOT needed:
//!   the corpus-spelling derivation consumes the transport only at
//!   `instantiate b a = instantiate_at b a 0`. So `betaRed_inst_transport`
//!   lands ALL FIFTEEN `beta_reduces` arms (beta and zeta via
//!   `instantiate_nested_commutes_zero_subst`, congruences via the
//!   `instantiate_at_*` unfolding lemmas, iota via `iota_subst_commutes`) for
//!   `instantiate_at`, and the general-psubst spelling stays an open item with
//!   that named blocker.
//! - **The iota arm rides on a CARRIED closedness premise.**
//!   `RecEnvClosed (red_rec the_red_env)` (and `DefEnvClosed (red_def
//!   the_red_env)` for the whnf-level wrapper's delta leg) are hypotheses of
//!   the transports, NOT discharged here: the one-rfl discharge witnesses live
//!   in later registration stages (`faithful_checkers.rs` /
//!   `env_closed_checkers_depth.rs` payoff witnesses), out of scope at this
//!   stage position. This is the standing carried-hypothesis discipline
//!   (i3/i5 of the wall-A/wh3 assemblies); consumers at later stages can
//!   apply the discharged witnesses directly.
//! - **The delta witnesses compute over `the_red_env` — designated-discharge
//!   posture.** `candExp_delta_witness` proves `whnf_acc` of the REAL kernel
//!   constant `def_env_lift_closed_b` (`kcre_witness_delta_head`, the
//!   outermost reflected DefEnv entry) THROUGH the engine, consuming the
//!   existing Guard-4 step witness `the_red_env_delta_nonvacuous` (no new
//!   step computation) plus refl-computed iota/delta deadness of the body's
//!   components (`fixture_def_env_name`, `fixture_def_env_closed_b_name` — neither is a recursor;
//!   `fixture_def_env_name` is not delta-defined; the body's inner redex positions
//!   are a bare const and a bvar, so it is whnf-stuck). Per the_red_env.rs
//!   Guard 3 this module is thereby one of the designated witness-discharge
//!   sites; the witness references generated `kcre_*` atoms, so a
//!   semantic aliases follow the current interning table. A regeneration
//!   that changes the selected body or reduction facts still fails these
//!   proofs CLOSED rather than silently drifting.
//!
//! ## Census
//!
//! ZERO new axioms: every constant is value-bearing (all theorems via
//! `add_definition` with kernel `add_decl` checking; no new inductives, no
//! new axioms). Census-neutral.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ==== R2 SOURCES BEGIN (dependency-free: consts + pure string builders; ====
// ==== extracted verbatim by the pre-validation parse harness)           ====

// ================================================================
// Group A — const-headed no-confusion (local re-mints).
// `const_ne_let` / `const_ne_proj` exist only in natrec.rs (stage
// `add_natrec`, NOT in the substitution bundle and registered after this
// stage), so R2 re-mints them locally in the par_reduces_d_diamond
// discriminator idiom (named constructor -> Empty, else Nat; transport
// Nat.zero along the false equation; Empty.rec into any Type).
// ================================================================

/// Inline `KExpr.rec` discriminator into Type: the selected constructor maps
/// to `Empty`, every other constructor to `Nat`. Constructor order: sort,
/// bvar, app, lam, pi, const, let_, proj, lit.
fn kexpr_discr(target_let: bool, target_proj: bool) -> String {
    let arm = |is_target: bool| if is_target { "Empty" } else { "Nat" };
    format!(
        "(@KExpr.rec (fun (_ : KExpr) => Type) \
         (fun (_ : Level) => Nat) \
         (fun (_ : Nat) => Nat) \
         (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
         (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
         (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
         (fun (_ : Name) (_ : ListType Level) => Nat) \
         (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => {letv}) \
         (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => {projv}) \
         (fun (_ : Nat) => Nat))",
        letv = arm(target_let),
        projv = arm(target_proj),
    )
}

pub(super) const TY_R2_CONST_NE_LET: &str = "forall (nm : Name) (us : ListType Level) (A : KExpr) (v0 : KExpr) (b0 : KExpr) (R : Type), @Eq KExpr (KExpr.const nm us) (KExpr.let_ A v0 b0) -> R";

pub(super) fn val_r2_const_ne_let() -> String {
    format!(
        "fun (nm : Name) (us : ListType Level) (A : KExpr) (v0 : KExpr) (b0 : KExpr) (R : Type) (h : @Eq KExpr (KExpr.const nm us) (KExpr.let_ A v0 b0)) => @Empty.rec (fun (_ : Empty) => R) (@Eq.substType KExpr {discr} (KExpr.const nm us) (KExpr.let_ A v0 b0) h Nat.zero)",
        discr = kexpr_discr(true, false)
    )
}

pub(super) const TY_R2_CONST_NE_PROJ: &str = "forall (nm : Name) (us : ListType Level) (ps : Name) (pidx : Nat) (psub : KExpr) (R : Type), @Eq KExpr (KExpr.const nm us) (KExpr.proj ps pidx psub) -> R";

pub(super) fn val_r2_const_ne_proj() -> String {
    format!(
        "fun (nm : Name) (us : ListType Level) (ps : Name) (pidx : Nat) (psub : KExpr) (R : Type) (h : @Eq KExpr (KExpr.const nm us) (KExpr.proj ps pidx psub)) => @Empty.rec (fun (_ : Empty) => R) (@Eq.substType KExpr {discr} (KExpr.const nm us) (KExpr.proj ps pidx psub) h Nat.zero)",
        discr = kexpr_discr(false, true)
    )
}

// ================================================================
// Group B — the const-headed beta inversion + whnf classification.
// r2_const_no_beta_reduces is a local RE-MINT of natrec.rs
// const_no_beta_reduces (stage `add_natrec`, not in the substitution
// bundle) with the let/proj discrimination routed through the Group A
// re-mints. Arm order = beta_reduces constructor order.
// ================================================================

pub(super) const TY_R2_CONST_NO_BETA: &str = "forall (n : Name) (us : ListType Level) (e2 : KExpr) (C : Type), beta_reduces (KExpr.const n us) e2 -> C";

pub(super) fn val_r2_const_no_beta() -> String {
    let cn = "(KExpr.const n us)";
    let mot =
        format!("(fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => @Eq KExpr s {cn} -> C)");
    let sym = |s: &str| format!("(@Eq.symm KExpr {s} {cn} heq)");
    let c_beta = format!("(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : @Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) {cn}) => const_ne_app n us (KExpr.lam A0 body) arg C {})", sym("(KExpr.app (KExpr.lam A0 body) arg)"));
    let c_appl = format!("(fun (f : KExpr) (f2 : KExpr) (a : KExpr) (_hstep : beta_reduces f f2) (_ih : @Eq KExpr f {cn} -> C) (heq : @Eq KExpr (KExpr.app f a) {cn}) => const_ne_app n us f a C {})", sym("(KExpr.app f a)"));
    let c_appr = format!("(fun (f : KExpr) (a : KExpr) (a2 : KExpr) (_hstep : beta_reduces a a2) (_ih : @Eq KExpr a {cn} -> C) (heq : @Eq KExpr (KExpr.app f a) {cn}) => const_ne_app n us f a C {})", sym("(KExpr.app f a)"));
    let c_lamty = format!("(fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : @Eq KExpr ty {cn} -> C) (heq : @Eq KExpr (KExpr.lam ty body) {cn}) => const_ne_lam n us ty body C {})", sym("(KExpr.lam ty body)"));
    let c_lambd = format!("(fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : @Eq KExpr body {cn} -> C) (heq : @Eq KExpr (KExpr.lam ty body) {cn}) => const_ne_lam n us ty body C {})", sym("(KExpr.lam ty body)"));
    let c_pidom = format!("(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : @Eq KExpr dom {cn} -> C) (heq : @Eq KExpr (KExpr.pi dom body) {cn}) => const_ne_pi n us dom body C {})", sym("(KExpr.pi dom body)"));
    let c_picod = format!("(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : @Eq KExpr body {cn} -> C) (heq : @Eq KExpr (KExpr.pi dom body) {cn}) => const_ne_pi n us dom body C {})", sym("(KExpr.pi dom body)"));
    let c_fadom = format!("(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : @Eq KExpr dom {cn} -> C) (heq : @Eq KExpr (KExpr.forall_ dom body) {cn}) => const_ne_pi n us dom body C {})", sym("(KExpr.forall_ dom body)"));
    let c_facod = format!("(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : @Eq KExpr body {cn} -> C) (heq : @Eq KExpr (KExpr.forall_ dom body) {cn}) => const_ne_pi n us dom body C {})", sym("(KExpr.forall_ dom body)"));
    let c_zeta = format!("(fun (ty : KExpr) (val : KExpr) (body : KExpr) (heq : @Eq KExpr (KExpr.let_ ty val body) {cn}) => r2_const_ne_let n us ty val body C {})", sym("(KExpr.let_ ty val body)"));
    let c_letty = format!("(fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : @Eq KExpr ty {cn} -> C) (heq : @Eq KExpr (KExpr.let_ ty val body) {cn}) => r2_const_ne_let n us ty val body C {})", sym("(KExpr.let_ ty val body)"));
    let c_letval = format!("(fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hstep : beta_reduces val val2) (_ih : @Eq KExpr val {cn} -> C) (heq : @Eq KExpr (KExpr.let_ ty val body) {cn}) => r2_const_ne_let n us ty val body C {})", sym("(KExpr.let_ ty val body)"));
    let c_letbd = format!("(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : @Eq KExpr body {cn} -> C) (heq : @Eq KExpr (KExpr.let_ ty val body) {cn}) => r2_const_ne_let n us ty val body C {})", sym("(KExpr.let_ ty val body)"));
    let c_iota = format!("(fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : @Eq KExpr e0 {cn}) => option_none_ne_some_type KExpr e02 C (@Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (iota_reduct (red_rec the_red_env) e0) (@OptionType.some KExpr e02) (@Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (@OptionType.none KExpr) (@Eq.trans (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (iota_reduct (red_rec the_red_env) {cn}) (@OptionType.none KExpr) (@Eq.cong KExpr (OptionType KExpr) (fun (x : KExpr) => iota_reduct (red_rec the_red_env) x) e0 {cn} heq) (iota_reduct_const_none (red_rec the_red_env) n us))) (iota_reduces_to_step e0 e02 hiota)))");
    let c_proj = format!("(fun (ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (_hstep : beta_reduces sub sub2) (_ih : @Eq KExpr sub {cn} -> C) (heq : @Eq KExpr (KExpr.proj ps pin sub) {cn}) => r2_const_ne_proj n us ps pin sub C {})", sym("(KExpr.proj ps pin sub)"));
    format!(
        "fun (n : Name) (us : ListType Level) (e2 : KExpr) (C : Type) (hbr : beta_reduces {cn} e2) => @beta_reduces.rec {mot} {c_beta} {c_appl} {c_appr} {c_lamty} {c_lambd} {c_pidom} {c_picod} {c_fadom} {c_facod} {c_zeta} {c_letty} {c_letval} {c_letbd} {c_iota} {c_proj} {cn} e2 hbr (@Eq.refl KExpr {cn})"
    )
}

pub(super) const TY_CONSTREDEX_WHNF_INV: &str = "forall (c : Name) (us : ListType Level) (g2 : KExpr) (C : Type), whnf_step (KExpr.const c us) g2 -> (delta_step (red_def the_red_env) (KExpr.const c us) g2 -> C) -> C";

pub(super) fn val_constredex_whnf_inv() -> String {
    let cn = "(KExpr.const c us)";
    format!(
        "fun (c : Name) (us : ListType Level) (g2 : KExpr) (C : Type) (hs : whnf_step {cn} g2) (k : delta_step (red_def the_red_env) {cn} g2 -> C) => @whnf_step.rec {cn} g2 (fun (_ : whnf_step {cn} g2) => C) (fun (hbr : beta_reduces {cn} g2) => r2_const_no_beta_reduces c us g2 C hbr) (fun (hdr : delta_reduces {cn} g2) => k (delta_reduces_to_step {cn} g2 hdr)) hs"
    )
}

// ================================================================
// Group C — the delta engine and its premise-necessity guard.
// ================================================================

pub(super) const TY_CANDEXP_DELTA: &str = "forall (S : KExpr -> Type), IsCandSet S -> forall (c : Name) (us : ListType Level) (body : KExpr), delta_step (red_def the_red_env) (KExpr.const c us) body -> S body -> S (KExpr.const c us)";

pub(super) fn val_candexp_delta() -> String {
    let cn = "(KExpr.const c us)";
    format!(
        "fun (S : KExpr -> Type) (hS : IsCandSet S) (c : Name) (us : ListType Level) (body : KExpr) (hdelta : delta_step (red_def the_red_env) {cn} body) (hbody : S body) => isCandSet_cr3 S hS {cn} ConstFreeUnit.triv (fun (e2 : KExpr) (hstep : whnf_step {cn} e2) => constRedex_whnf_inv c us e2 (S e2) hstep (fun (hstep2 : delta_step (red_def the_red_env) {cn} e2) => @Eq.substType KExpr (fun (z : KExpr) => S z) body e2 (delta_step_deterministic (red_def the_red_env) {cn} body e2 hdelta hstep2) hbody))"
    )
}

pub(super) const TY_CONSTACC_BODY_ACC: &str = "forall (c : Name) (us : ListType Level) (body : KExpr), delta_step (red_def the_red_env) (KExpr.const c us) body -> whnf_acc (KExpr.const c us) -> whnf_acc body";
pub(super) const VAL_CONSTACC_BODY_ACC: &str = "fun (c : Name) (us : ListType Level) (body : KExpr) (hdelta : delta_step (red_def the_red_env) (KExpr.const c us) body) (hacc : whnf_acc (KExpr.const c us)) => whnfAcc_inv_step (KExpr.const c us) hacc body (whnf_step.delta (KExpr.const c us) body (delta_step_to_reduces (KExpr.const c us) body hdelta))";

// ================================================================
// Group D — the delta discriminating witnesses at the REAL reflected env
// constant def_env_lift_closed_b (kcre_witness_delta_head,
// the outermost DefEnv entry; its value kcre_witness_delta_value =
// lam (const fixture_def_env_name nil) (app (const fixture_def_env_closed_b_name nil) (bvar 0))).
// fixture_def_env_closed_b_name (def_env_closed_b) is NOT a recursor, so the body's app is
// iota-dead by refl; fixture_def_env_name is not delta-defined and a bare const is
// beta-dead generically; delta never fires under a binder (whnf_step's
// delta leg is root-only) — so the body is whnf-STUCK and its whnf_acc is
// the vacuous intro.
// ================================================================

const W_HEAD: &str = "(KExpr.const fixture_def_env_closed_b_name (@ListType.nil Level))";
const W_ARG: &str = "(KExpr.bvar kcre_nat_0)";
const W_APP: &str =
    "(KExpr.app (KExpr.const fixture_def_env_closed_b_name (@ListType.nil Level)) (KExpr.bvar kcre_nat_0))";
const W_DOM: &str = "(KExpr.const fixture_def_env_name (@ListType.nil Level))";

pub(super) fn ty_witness_body_no_beta() -> String {
    format!("forall (e2 : KExpr) (C : Type), beta_reduces {W_APP} e2 -> C")
}

pub(super) fn val_witness_body_no_beta() -> String {
    let mot =
        format!("(fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => @Eq KExpr s {W_APP} -> C)");
    let w_beta = format!("(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : @Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) {W_APP}) => const_ne_lam fixture_def_env_closed_b_name (@ListType.nil Level) A0 body C (@Eq.symm KExpr (KExpr.lam A0 body) {W_HEAD} (app_inj_fst (KExpr.lam A0 body) arg {W_HEAD} {W_ARG} heq)))");
    let w_appl = format!("(fun (f : KExpr) (f2 : KExpr) (a : KExpr) (hstep : beta_reduces f f2) (_ih : @Eq KExpr f {W_APP} -> C) (heq : @Eq KExpr (KExpr.app f a) {W_APP}) => r2_const_no_beta_reduces fixture_def_env_closed_b_name (@ListType.nil Level) f2 C (@Eq.rec KExpr f (fun (x : KExpr) (_ : @Eq KExpr f x) => beta_reduces x f2) hstep {W_HEAD} (app_inj_fst f a {W_HEAD} {W_ARG} heq)))");
    let w_appr = format!("(fun (f : KExpr) (a : KExpr) (a2 : KExpr) (hstep : beta_reduces a a2) (_ih : @Eq KExpr a {W_APP} -> C) (heq : @Eq KExpr (KExpr.app f a) {W_APP}) => no_whnf_step_bvar kcre_nat_0 a2 C (whnf_step.beta {W_ARG} a2 (@Eq.rec KExpr a (fun (x : KExpr) (_ : @Eq KExpr a x) => beta_reduces x a2) hstep {W_ARG} (app_inj_snd f a {W_HEAD} {W_ARG} heq))))");
    let w_lamty = format!("(fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : @Eq KExpr ty {W_APP} -> C) (heq : @Eq KExpr (KExpr.lam ty body) {W_APP}) => lam_ne_app ty body {W_HEAD} {W_ARG} C heq)");
    let w_lambd = format!("(fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : @Eq KExpr body {W_APP} -> C) (heq : @Eq KExpr (KExpr.lam ty body) {W_APP}) => lam_ne_app ty body {W_HEAD} {W_ARG} C heq)");
    let w_pidom = format!("(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : @Eq KExpr dom {W_APP} -> C) (heq : @Eq KExpr (KExpr.pi dom body) {W_APP}) => pi_ne_app dom body {W_HEAD} {W_ARG} C heq)");
    let w_picod = format!("(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : @Eq KExpr body {W_APP} -> C) (heq : @Eq KExpr (KExpr.pi dom body) {W_APP}) => pi_ne_app dom body {W_HEAD} {W_ARG} C heq)");
    let w_fadom = format!("(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : @Eq KExpr dom {W_APP} -> C) (heq : @Eq KExpr (KExpr.forall_ dom body) {W_APP}) => pi_ne_app dom body {W_HEAD} {W_ARG} C heq)");
    let w_facod = format!("(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : @Eq KExpr body {W_APP} -> C) (heq : @Eq KExpr (KExpr.forall_ dom body) {W_APP}) => pi_ne_app dom body {W_HEAD} {W_ARG} C heq)");
    let w_zeta = format!("(fun (ty : KExpr) (val : KExpr) (body : KExpr) (heq : @Eq KExpr (KExpr.let_ ty val body) {W_APP}) => let_ne_app ty val body {W_HEAD} {W_ARG} C heq)");
    let w_letty = format!("(fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : @Eq KExpr ty {W_APP} -> C) (heq : @Eq KExpr (KExpr.let_ ty val body) {W_APP}) => let_ne_app ty val body {W_HEAD} {W_ARG} C heq)");
    let w_letval = format!("(fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hstep : beta_reduces val val2) (_ih : @Eq KExpr val {W_APP} -> C) (heq : @Eq KExpr (KExpr.let_ ty val body) {W_APP}) => let_ne_app ty val body {W_HEAD} {W_ARG} C heq)");
    let w_letbd = format!("(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : @Eq KExpr body {W_APP} -> C) (heq : @Eq KExpr (KExpr.let_ ty val body) {W_APP}) => let_ne_app ty val body {W_HEAD} {W_ARG} C heq)");
    let w_iota = format!("(fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : @Eq KExpr e0 {W_APP}) => option_none_ne_some_type KExpr e02 C (@Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (iota_reduct (red_rec the_red_env) e0) (@OptionType.some KExpr e02) (@Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (@OptionType.none KExpr) (@Eq.trans (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (iota_reduct (red_rec the_red_env) {W_APP}) (@OptionType.none KExpr) (@Eq.cong KExpr (OptionType KExpr) (fun (x : KExpr) => iota_reduct (red_rec the_red_env) x) e0 {W_APP} heq) (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)))) (iota_reduces_to_step e0 e02 hiota)))");
    let w_proj = format!("(fun (ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (_hstep : beta_reduces sub sub2) (_ih : @Eq KExpr sub {W_APP} -> C) (heq : @Eq KExpr (KExpr.proj ps pin sub) {W_APP}) => proj_ne_app ps pin sub {W_HEAD} {W_ARG} C heq)");
    format!(
        "fun (e2 : KExpr) (C : Type) (hbr : beta_reduces {W_APP} e2) => @beta_reduces.rec {mot} {w_beta} {w_appl} {w_appr} {w_lamty} {w_lambd} {w_pidom} {w_picod} {w_fadom} {w_facod} {w_zeta} {w_letty} {w_letval} {w_letbd} {w_iota} {w_proj} {W_APP} e2 hbr (@Eq.refl KExpr {W_APP})"
    )
}

pub(super) const TY_WITNESS_BODY_ACC: &str = "whnf_acc kcre_witness_delta_value";

pub(super) fn val_witness_body_acc() -> String {
    format!(
        "whnf_acc.intro kcre_witness_delta_value (fun (e2 : KExpr) (hs : whnf_step kcre_witness_delta_value e2) => @whnf_step.rec kcre_witness_delta_value e2 (fun (_ : whnf_step kcre_witness_delta_value e2) => whnf_acc e2) (fun (hbr : beta_reduces kcre_witness_delta_value e2) => lamHead_beta_inv {W_DOM} {W_APP} e2 (whnf_acc e2) hbr (fun (ty2 : KExpr) (hstepty : beta_reduces {W_DOM} ty2) (_heq : @Eq KExpr e2 (KExpr.lam ty2 {W_APP})) => r2_const_no_beta_reduces fixture_def_env_name (@ListType.nil Level) ty2 (whnf_acc e2) hstepty) (fun (b2 : KExpr) (hstepb : beta_reduces {W_APP} b2) (_heq : @Eq KExpr e2 (KExpr.lam {W_DOM} b2)) => r2_deltaWitness_body_no_beta b2 (whnf_acc e2) hstepb)) (fun (hdr : delta_reduces kcre_witness_delta_value e2) => delta_step_head_none_absurd_type (red_def the_red_env) kcre_witness_delta_value e2 (whnf_acc e2) (@Eq.refl (OptionType Name) (@OptionType.none Name)) (delta_reduces_to_step kcre_witness_delta_value e2 hdr)) hs)"
    )
}

pub(super) const TY_CANDEXP_DELTA_WITNESS: &str =
    "whnf_acc (KExpr.const kcre_witness_delta_head (@ListType.nil Level))";
pub(super) const VAL_CANDEXP_DELTA_WITNESS: &str = "candExp_delta (fun (e : KExpr) => whnf_acc e) isCand_whnfAcc kcre_witness_delta_head (@ListType.nil Level) kcre_witness_delta_value the_red_env_delta_nonvacuous r2_deltaWitness_body_acc";

// ================================================================
// Group E — the substitution transport: one full beta_reduces step
// commutes with instantiate_at. All 15 arms. instantiate_at does NOT
// reliably reduce on symbolic-field constructors (the documented iota
// false negative behind instantiate_at_app's structural registration), so
// every structural arm transports BOTH endpoints explicitly through the
// instantiate_at_* unfolding lemmas.
// ================================================================

/// The double-endpoint transport sandwich: from `core : beta_reduces
/// lhs_unf rhs_unf` and unfolding equations `lhs_eq : Eq lhs_raw lhs_unf`,
/// `rhs_eq : Eq rhs_raw rhs_unf`, produce `beta_reduces lhs_raw rhs_raw`.
/// CAPTURE AUDIT: template binders are `z` only; no substituted expression
/// uses a bare `z` identifier (arm binders are constructor-field names and
/// `w`/`dd`, checked per arm below).
fn tport(
    lhs_raw: &str,
    lhs_unf: &str,
    lhs_eq: &str,
    rhs_raw: &str,
    rhs_unf: &str,
    rhs_eq: &str,
    core: &str,
) -> String {
    format!(
        "@Eq.substType KExpr (fun (z : KExpr) => beta_reduces z {rhs_raw}) {lhs_unf} {lhs_raw} (@Eq.symm KExpr {lhs_raw} {lhs_unf} {lhs_eq}) (@Eq.substType KExpr (fun (z : KExpr) => beta_reduces {lhs_unf} z) {rhs_unf} {rhs_raw} (@Eq.symm KExpr {rhs_raw} {rhs_unf} {rhs_eq}) {core})"
    )
}

/// `instantiate_at t w <depth>` where depth is `dd` or `(Nat.succ dd)`.
fn ia(t: &str, depth: &str) -> String {
    format!("(instantiate_at {t} w {depth})")
}

pub(super) const TY_BETARED_INST_TRANSPORT: &str = "forall (e : KExpr) (e2 : KExpr), beta_reduces e e2 -> RecEnvClosed (red_rec the_red_env) -> forall (w : KExpr) (dd : Nat), beta_reduces (instantiate_at e w dd) (instantiate_at e2 w dd)";

pub(super) fn val_betared_inst_transport() -> String {
    let ih = |src: &str, dst: &str| {
        format!(
            "(ih : forall (w0 : KExpr) (d0 : Nat), beta_reduces (instantiate_at {src} w0 d0) (instantiate_at {dst} w0 d0))"
        )
    };
    let mot = "(fun (x : KExpr) (y : KExpr) (_ : beta_reduces x y) => forall (w : KExpr) (dd : Nat), beta_reduces (instantiate_at x w dd) (instantiate_at y w dd))";
    // A1 beta. Binders xA/xb/xa; template binders w/dd/z distinct.
    let a_beta = {
        let i_a = ia("xA", "dd");
        let i_b = ia("xb", "(Nat.succ dd)");
        let i_arg = ia("xa", "dd");
        let lhs_raw = "(instantiate_at (KExpr.app (KExpr.lam xA xb) xa) w dd)";
        let lhs_unf = format!("(KExpr.app (KExpr.lam {i_a} {i_b}) {i_arg})");
        let lam_raw = "(instantiate_at (KExpr.lam xA xb) w dd)";
        let lhs_eq = format!(
            "(@Eq.trans KExpr {lhs_raw} (KExpr.app {lam_raw} {i_arg}) {lhs_unf} (instantiate_at_app (KExpr.lam xA xb) xa w dd) (@Eq.cong KExpr KExpr (fun (z2 : KExpr) => KExpr.app z2 {i_arg}) {lam_raw} (KExpr.lam {i_a} {i_b}) (instantiate_at_lam xA xb w dd)))"
        );
        let rhs_raw = "(instantiate_at (instantiate xb xa) w dd)";
        let rhs_unf = format!("(instantiate_at {i_b} {i_arg} Nat.zero)");
        let rhs_eq = "(instantiate_nested_commutes_zero_subst xb xa w dd)";
        let core = format!("(beta_reduces.beta {i_a} {i_b} {i_arg})");
        format!(
            "(fun (xA : KExpr) (xb : KExpr) (xa : KExpr) (w : KExpr) (dd : Nat) => {})",
            tport(lhs_raw, &lhs_unf, &lhs_eq, rhs_raw, &rhs_unf, rhs_eq, &core)
        )
    };
    // Congruence arm builder over app.
    let app_arm = |b1: &str, b2: &str, b3: &str, src: &str, dst: &str, core: &str| {
        let lhs_raw = format!("(instantiate_at (KExpr.app {src}) w dd)");
        let (sf, sa) = src.split_once(' ').expect("app src has two fields");
        let (df, da) = dst.split_once(' ').expect("app dst has two fields");
        let lhs_unf = format!("(KExpr.app {} {})", ia(sf, "dd"), ia(sa, "dd"));
        let rhs_raw = format!("(instantiate_at (KExpr.app {dst}) w dd)");
        let rhs_unf = format!("(KExpr.app {} {})", ia(df, "dd"), ia(da, "dd"));
        let lhs_eq = format!("(instantiate_at_app {sf} {sa} w dd)");
        let rhs_eq = format!("(instantiate_at_app {df} {da} w dd)");
        format!(
            "(fun ({b1} : KExpr) ({b2} : KExpr) ({b3} : KExpr) (hx : beta_reduces {hs} {hd}) {ihb} (w : KExpr) (dd : Nat) => {})",
            tport(&lhs_raw, &lhs_unf, &lhs_eq, &rhs_raw, &rhs_unf, &rhs_eq, core),
            hs = if b2 == "xf2" { "xf" } else { "xa" },
            hd = if b2 == "xf2" { "xf2" } else { "xa2" },
            ihb = if b2 == "xf2" {
                ih("xf", "xf2")
            } else {
                ih("xa", "xa2")
            },
        )
    };
    let a_appl = app_arm(
        "xf",
        "xf2",
        "xa",
        "xf xa",
        "xf2 xa",
        &format!(
            "(beta_reduces.app_left {} {} {} (ih w dd))",
            ia("xf", "dd"),
            ia("xf2", "dd"),
            ia("xa", "dd")
        ),
    );
    let a_appr = {
        // app_right binds (xf xa xa2), step on xa.
        let lhs_raw = "(instantiate_at (KExpr.app xf xa) w dd)";
        let lhs_unf = format!("(KExpr.app {} {})", ia("xf", "dd"), ia("xa", "dd"));
        let rhs_raw = "(instantiate_at (KExpr.app xf xa2) w dd)";
        let rhs_unf = format!("(KExpr.app {} {})", ia("xf", "dd"), ia("xa2", "dd"));
        let core = format!(
            "(beta_reduces.app_right {} {} {} (ih w dd))",
            ia("xf", "dd"),
            ia("xa", "dd"),
            ia("xa2", "dd")
        );
        format!(
            "(fun (xf : KExpr) (xa : KExpr) (xa2 : KExpr) (hx : beta_reduces xa xa2) {} (w : KExpr) (dd : Nat) => {})",
            ih("xa", "xa2"),
            tport(
                lhs_raw,
                &lhs_unf,
                "(instantiate_at_app xf xa w dd)",
                rhs_raw,
                &rhs_unf,
                "(instantiate_at_app xf xa2 w dd)",
                &core
            )
        )
    };
    // Two-field binder arm builder (lam/pi share the shape via ctor + lemma).
    let binder_arm = |ctor: &str,
                      lemma: &str,
                      b1: &str,
                      b2: &str,
                      b3: &str,
                      src: (&str, &str),
                      dst: (&str, &str),
                      stepped: (&str, &str),
                      ih_depth: &str,
                      core_args: &str| {
        let lhs_raw = format!("(instantiate_at (@{ctor} {} {}) w dd)", src.0, src.1);
        let lhs_unf = format!(
            "(@{ctor} {} {})",
            ia(src.0, "dd"),
            ia(src.1, "(Nat.succ dd)")
        );
        let rhs_raw = format!("(instantiate_at (@{ctor} {} {}) w dd)", dst.0, dst.1);
        let rhs_unf = format!(
            "(@{ctor} {} {})",
            ia(dst.0, "dd"),
            ia(dst.1, "(Nat.succ dd)")
        );
        let lhs_eq = format!("({lemma} {} {} w dd)", src.0, src.1);
        let rhs_eq = format!("({lemma} {} {} w dd)", dst.0, dst.1);
        let core = format!("({core_args} (ih w {ih_depth}))");
        format!(
            "(fun ({b1} : KExpr) ({b2} : KExpr) ({b3} : KExpr) (hx : beta_reduces {} {}) {} (w : KExpr) (dd : Nat) => {})",
            stepped.0,
            stepped.1,
            ih(stepped.0, stepped.1),
            tport(&lhs_raw, &lhs_unf, &lhs_eq, &rhs_raw, &rhs_unf, &rhs_eq, &core)
        )
    };
    let a_lamty = binder_arm(
        "KExpr.lam",
        "instantiate_at_lam",
        "xty",
        "xty2",
        "xb",
        ("xty", "xb"),
        ("xty2", "xb"),
        ("xty", "xty2"),
        "dd",
        &format!(
            "beta_reduces.lam_ty {} {} {}",
            ia("xty", "dd"),
            ia("xty2", "dd"),
            ia("xb", "(Nat.succ dd)")
        ),
    );
    let a_lambd = binder_arm(
        "KExpr.lam",
        "instantiate_at_lam",
        "xty",
        "xb",
        "xb2",
        ("xty", "xb"),
        ("xty", "xb2"),
        ("xb", "xb2"),
        "(Nat.succ dd)",
        &format!(
            "beta_reduces.lam_body {} {} {}",
            ia("xty", "dd"),
            ia("xb", "(Nat.succ dd)"),
            ia("xb2", "(Nat.succ dd)")
        ),
    );
    let pi_dom_arm = binder_arm(
        "KExpr.pi",
        "instantiate_at_pi",
        "xdo",
        "xdo2",
        "xb",
        ("xdo", "xb"),
        ("xdo2", "xb"),
        ("xdo", "xdo2"),
        "dd",
        &format!(
            "beta_reduces.pi_dom {} {} {}",
            ia("xdo", "dd"),
            ia("xdo2", "dd"),
            ia("xb", "(Nat.succ dd)")
        ),
    );
    let pi_cod_arm = binder_arm(
        "KExpr.pi",
        "instantiate_at_pi",
        "xdo",
        "xb",
        "xb2",
        ("xdo", "xb"),
        ("xdo", "xb2"),
        ("xb", "xb2"),
        "(Nat.succ dd)",
        &format!(
            "beta_reduces.pi_cod {} {} {}",
            ia("xdo", "dd"),
            ia("xb", "(Nat.succ dd)"),
            ia("xb2", "(Nat.succ dd)")
        ),
    );
    // forall_ is the reducible pi alias: the pi-spelled transport bodies
    // defeq-check against the forall_-spelled arm goals.
    let a_fadom = pi_dom_arm.clone();
    let a_facod = pi_cod_arm.clone();
    // A10 zeta.
    let a_zeta = {
        let i_t = ia("xt", "dd");
        let i_v = ia("xv", "dd");
        let i_b = ia("xb", "(Nat.succ dd)");
        let lhs_raw = "(instantiate_at (KExpr.let_ xt xv xb) w dd)";
        let lhs_unf = format!("(KExpr.let_ {i_t} {i_v} {i_b})");
        let lhs_eq = "(instantiate_at_let_ xt xv xb w dd)";
        let rhs_raw = "(instantiate_at (instantiate xb xv) w dd)";
        let rhs_unf = format!("(instantiate_at {i_b} {i_v} Nat.zero)");
        let rhs_eq = "(instantiate_nested_commutes_zero_subst xb xv w dd)";
        let core = format!("(beta_reduces.zeta {i_t} {i_v} {i_b})");
        format!(
            "(fun (xt : KExpr) (xv : KExpr) (xb : KExpr) (w : KExpr) (dd : Nat) => {})",
            tport(lhs_raw, &lhs_unf, lhs_eq, rhs_raw, &rhs_unf, rhs_eq, &core)
        )
    };
    // let_ congruence arm builder.
    let let_arm = |b: [&str; 4],
                   src: [&str; 3],
                   dst: [&str; 3],
                   stepped: (&str, &str),
                   ih_depth: &str,
                   core_ctor: &str,
                   core_fields: [&str; 4]| {
        let lhs_raw = format!(
            "(instantiate_at (KExpr.let_ {} {} {}) w dd)",
            src[0], src[1], src[2]
        );
        let lhs_unf = format!(
            "(KExpr.let_ {} {} {})",
            ia(src[0], "dd"),
            ia(src[1], "dd"),
            ia(src[2], "(Nat.succ dd)")
        );
        let rhs_raw = format!(
            "(instantiate_at (KExpr.let_ {} {} {}) w dd)",
            dst[0], dst[1], dst[2]
        );
        let rhs_unf = format!(
            "(KExpr.let_ {} {} {})",
            ia(dst[0], "dd"),
            ia(dst[1], "dd"),
            ia(dst[2], "(Nat.succ dd)")
        );
        let lhs_eq = format!(
            "(instantiate_at_let_ {} {} {} w dd)",
            src[0], src[1], src[2]
        );
        let rhs_eq = format!(
            "(instantiate_at_let_ {} {} {} w dd)",
            dst[0], dst[1], dst[2]
        );
        let core = format!(
            "({core_ctor} {} {} {} {} (ih w {ih_depth}))",
            core_fields[0], core_fields[1], core_fields[2], core_fields[3]
        );
        format!(
            "(fun ({} : KExpr) ({} : KExpr) ({} : KExpr) ({} : KExpr) (hx : beta_reduces {} {}) {} (w : KExpr) (dd : Nat) => {})",
            b[0],
            b[1],
            b[2],
            b[3],
            stepped.0,
            stepped.1,
            ih(stepped.0, stepped.1),
            tport(&lhs_raw, &lhs_unf, &lhs_eq, &rhs_raw, &rhs_unf, &rhs_eq, &core)
        )
    };
    let i_xt = ia("xt", "dd");
    let i_xt2 = ia("xt2", "dd");
    let i_xv = ia("xv", "dd");
    let i_xv2 = ia("xv2", "dd");
    let i_xb = ia("xb", "(Nat.succ dd)");
    let i_xb2 = ia("xb2", "(Nat.succ dd)");
    let a_letty = let_arm(
        ["xt", "xt2", "xv", "xb"],
        ["xt", "xv", "xb"],
        ["xt2", "xv", "xb"],
        ("xt", "xt2"),
        "dd",
        "beta_reduces.let_ty",
        [&i_xt, &i_xt2, &i_xv, &i_xb],
    );
    let a_letval = let_arm(
        ["xt", "xv", "xv2", "xb"],
        ["xt", "xv", "xb"],
        ["xt", "xv2", "xb"],
        ("xv", "xv2"),
        "dd",
        "beta_reduces.let_val",
        [&i_xt, &i_xv, &i_xv2, &i_xb],
    );
    let a_letbd = let_arm(
        ["xt", "xv", "xb", "xb2"],
        ["xt", "xv", "xb"],
        ["xt", "xv", "xb2"],
        ("xb", "xb2"),
        "(Nat.succ dd)",
        "beta_reduces.let_body",
        [&i_xt, &i_xv, &i_xb, &i_xb2],
    );
    // A14 iota: the real-env commutation under the carried closedness premise.
    let a_iota = "(fun (xe : KExpr) (xe2 : KExpr) (hx : iota_reduces xe xe2) (w : KExpr) (dd : Nat) => beta_reduces.iota (instantiate_at xe w dd) (instantiate_at xe2 w dd) (iota_step_to_reduces (instantiate_at xe w dd) (instantiate_at xe2 w dd) (iota_subst_commutes (red_rec the_red_env) xe xe2 w dd hcl (iota_reduces_to_step xe xe2 hx))))"
        .to_string();
    // A15 proj.
    let a_proj = {
        let lhs_raw = "(instantiate_at (KExpr.proj xs xi xsub) w dd)";
        let lhs_unf = format!("(KExpr.proj xs xi {})", ia("xsub", "dd"));
        let rhs_raw = "(instantiate_at (KExpr.proj xs xi xsub2) w dd)";
        let rhs_unf = format!("(KExpr.proj xs xi {})", ia("xsub2", "dd"));
        let core = format!(
            "(beta_reduces.proj xs xi {} {} (ih w dd))",
            ia("xsub", "dd"),
            ia("xsub2", "dd")
        );
        format!(
            "(fun (xs : Name) (xi : Nat) (xsub : KExpr) (xsub2 : KExpr) (hx : beta_reduces xsub xsub2) {} (w : KExpr) (dd : Nat) => {})",
            ih("xsub", "xsub2"),
            tport(
                lhs_raw,
                &lhs_unf,
                "(instantiate_at_proj xs xi xsub w dd)",
                rhs_raw,
                &rhs_unf,
                "(instantiate_at_proj xs xi xsub2 w dd)",
                &core
            )
        )
    };
    format!(
        "fun (e : KExpr) (e2 : KExpr) (h : beta_reduces e e2) (hcl : RecEnvClosed (red_rec the_red_env)) => @beta_reduces.rec {mot} {a_beta} {a_appl} {a_appr} {a_lamty} {a_lambd} {pi_dom_arm} {pi_cod_arm} {a_fadom} {a_facod} {a_zeta} {a_letty} {a_letval} {a_letbd} {a_iota} {a_proj} e e2 h"
    )
}

pub(super) const TY_WHNFSTEP_INST_TRANSPORT: &str = "forall (e : KExpr) (e2 : KExpr), whnf_step e e2 -> RecEnvClosed (red_rec the_red_env) -> DefEnvClosed (red_def the_red_env) -> forall (w : KExpr) (dd : Nat), whnf_step (instantiate_at e w dd) (instantiate_at e2 w dd)";

pub(super) const VAL_WHNFSTEP_INST_TRANSPORT: &str = "fun (e : KExpr) (e2 : KExpr) (hs : whnf_step e e2) (hcl : RecEnvClosed (red_rec the_red_env)) (hdl : DefEnvClosed (red_def the_red_env)) (w : KExpr) (dd : Nat) => @whnf_step.rec e e2 (fun (_ : whnf_step e e2) => whnf_step (instantiate_at e w dd) (instantiate_at e2 w dd)) (fun (hbr : beta_reduces e e2) => whnf_step.beta (instantiate_at e w dd) (instantiate_at e2 w dd) (betaRed_inst_transport e e2 hbr hcl w dd)) (fun (hdr : delta_reduces e e2) => whnf_step.delta (instantiate_at e w dd) (instantiate_at e2 w dd) (delta_step_to_reduces (instantiate_at e w dd) (instantiate_at e2 w dd) (delta_subst_commutes (red_def the_red_env) e e2 w dd hdl (delta_reduces_to_step e e2 hdr)))) hs";

// The concrete instance computing by refl (the §6 pin): the step
// app (lam *0 (bvar 1)) *0  ->  bvar 0 (contractum mentions the OUTER free
// variable), transported under instantiate_at · (sort 0) 0. Both endpoints
// compute — the redex side substitutes bvar 1 UNDER the binder, the
// contractum side substitutes bvar 0 — and the transported step is one bare
// beta_reduces.beta whose endpoints the kernel evaluates to a match.
pub(super) const TY_BETARED_INST_WITNESS: &str = "beta_reduces (instantiate_at (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.sort Level.zero)) (KExpr.sort Level.zero) Nat.zero) (instantiate_at (instantiate (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero) Nat.zero)";
pub(super) const VAL_BETARED_INST_WITNESS: &str =
    "beta_reduces.beta (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.sort Level.zero)";

// ================================================================
// Group F — the corpus-spelling derivation.
// ================================================================

pub(super) const TY_BETASTAR_INST_TRANSPORT: &str = "forall (b : KExpr) (b2 : KExpr), betaStar b b2 -> RecEnvClosed (red_rec the_red_env) -> forall (a : KExpr), betaStar (instantiate b a) (instantiate b2 a)";
pub(super) const VAL_BETASTAR_INST_TRANSPORT: &str = "fun (b : KExpr) (b2 : KExpr) (hstar : betaStar b b2) (hcl : RecEnvClosed (red_rec the_red_env)) (a : KExpr) => @betaStar.rec (fun (x : KExpr) (y : KExpr) (_ : betaStar x y) => betaStar (instantiate x a) (instantiate y a)) (fun (xe : KExpr) => betaStar.refl (instantiate xe a)) (fun (xe : KExpr) (xe2 : KExpr) (xe3 : KExpr) (hx : beta_reduces xe xe2) (_hrest : betaStar xe2 xe3) (ih : betaStar (instantiate xe2 a) (instantiate xe3 a)) => betaStar.step (instantiate xe a) (instantiate xe2 a) (instantiate xe3 a) (betaRed_inst_transport xe xe2 hx hcl a Nat.zero) ih) b b2 hstar";

pub(super) const TY_CANDSET_BETASTAR_CLOSED: &str = "forall (S : KExpr -> Type), IsCandSet S -> forall (x : KExpr) (y : KExpr), betaStar x y -> S x -> S y";
pub(super) const VAL_CANDSET_BETASTAR_CLOSED: &str = "fun (S : KExpr -> Type) (hS : IsCandSet S) (x : KExpr) (y : KExpr) (hstar : betaStar x y) => @betaStar.rec (fun (x0 : KExpr) (y0 : KExpr) (_ : betaStar x0 y0) => S x0 -> S y0) (fun (xe : KExpr) (hx : S xe) => hx) (fun (xe : KExpr) (xe2 : KExpr) (xe3 : KExpr) (hstep : beta_reduces xe xe2) (_hrest : betaStar xe2 xe3) (ih : S xe2 -> S xe3) (hx : S xe) => ih (isCandSet_cr2 S hS xe xe2 hx (whnf_step.beta xe xe2 hstep))) x y hstar";

pub(super) const TY_CANDEXP_BETA_SUBST: &str = "forall (S : KExpr -> Type) (SA : KExpr -> Type), IsCandSet S -> IsCandSet SA -> RecEnvClosed (red_rec the_red_env) -> forall (ty : KExpr), whnf_acc ty -> forall (b : KExpr), whnf_acc b -> (forall (a2 : KExpr), SA a2 -> S (instantiate b a2)) -> forall (a : KExpr), SA a -> S (KExpr.app (KExpr.lam ty b) a)";
pub(super) const VAL_CANDEXP_BETA_SUBST: &str = "fun (S : KExpr -> Type) (SA : KExpr -> Type) (hS : IsCandSet S) (hSA : IsCandSet SA) (hcl : RecEnvClosed (red_rec the_red_env)) (ty : KExpr) (hty : whnf_acc ty) (b : KExpr) (hb : whnf_acc b) (hone : forall (a2 : KExpr), SA a2 -> S (instantiate b a2)) (a : KExpr) (ha : SA a) => candExp_beta S SA hS hSA ty hty b hb (fun (b2 : KExpr) (hstar : betaStar b b2) (a2 : KExpr) (ha2 : SA a2) => candSet_betaStar_closed S hS (instantiate b a2) (instantiate b2 a2) (betaStar_inst_transport b b2 hstar hcl a2) (hone a2 ha2)) a ha";

// ==== R2 SOURCES END ====

impl Specification {
    /// Register the R2 delta/const engine layer and the substitution
    /// transport: the const-headed no-confusion re-mints, the bare-const beta
    /// inversion and complete whnf classification, the delta head-expansion
    /// engine over any candidate set, the body-premise necessity guard, the
    /// real-env engine witnesses, the 15-arm `instantiate_at` transport for
    /// `beta_reduces` (iota arm included, under the carried
    /// `RecEnvClosed`), its whnf-level wrapper (delta leg under the carried
    /// `DefEnvClosed`), the betaStar transport, candidate-set star closure,
    /// and the DERIVED corpus-spelling single-contractum beta engine.
    ///
    /// MUST be registered AFTER `add_candmodel_construct_r1` (`IsCandSet`
    /// consumption API, `candExp_beta`, `betaStar`, `lamHead_beta_inv`).
    /// Also consumes: `const_ne_app/lam/pi` + `delta_step_head_none_absurd_type`
    /// (add_par_reduces_d_diamond), `iota_reduct_const_none`
    /// (add_par_reduces_p_topdev), `option_none_ne_some_type`
    /// (add_par_reduces_c), `iota_subst_commutes` (add_iota_core),
    /// `delta_subst_commutes` (add_delta_subst), the iota/delta bridges
    /// (add_iota_step_bridge / add_delta_step_bridge), `delta_step` keystones
    /// (add_delta_step), `instantiate_at_*` unfoldings (add_whnf_lemmas),
    /// `instantiate_nested_commutes_zero_subst`
    /// (add_substitution_commutation_nested_lemmas), `RecEnvClosed`
    /// (add_rec_env_closed), `DefEnvClosed` (add_delta_subst), the reflected
    /// env atoms + Guard-4 witnesses (add_kernel_core_red_env /
    /// add_the_red_env), and `no_whnf_step_bvar` (add_dependent_sn_richmodel).
    pub(super) fn add_candmodel_construct_r2(&mut self) -> Result<(), SpecError> {
        // --- Group A: const-headed no-confusion re-mints ---
        self.add_definition(SpecDefinition {
            name: "r2_const_ne_let".to_string(),
            type_src: TY_R2_CONST_NE_LET.to_string(),
            value_src: Some(val_r2_const_ne_let()),
            is_axiom: false,
            description: "const != let_ discrimination (Type-valued). LOCAL RE-MINT: \
                          natrec.rs registers const_ne_let in the add_natrec stage, which \
                          is NOT in the substitution bundle and registers after this stage, \
                          so R2 re-mints it in the par_reduces_d_diamond discriminator idiom \
                          (let_ -> Empty, else Nat; Eq.substType transport of Nat.zero; \
                          Empty.rec). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "r2_const_ne_proj".to_string(),
            type_src: TY_R2_CONST_NE_PROJ.to_string(),
            value_src: Some(val_r2_const_ne_proj()),
            is_axiom: false,
            description: "const != proj discrimination (Type-valued). LOCAL RE-MINT of \
                          natrec.rs const_ne_proj (add_natrec stage is outside the \
                          substitution bundle); same discriminator idiom as r2_const_ne_let. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group B: bare-const beta inversion + whnf classification ---
        self.add_definition(SpecDefinition {
            name: "r2_const_no_beta_reduces".to_string(),
            type_src: TY_R2_CONST_NO_BETA.to_string(),
            value_src: Some(val_r2_const_no_beta()),
            is_axiom: false,
            description: "A bare const admits NO beta_reduces step — for ANY name, recursor \
                          names included: 14 arms die by source discrimination \
                          (const_ne_app/lam/pi + the r2_ let/proj re-mints), the iota arm by \
                          iota_reduct_const_none (an empty spine has no major premise, \
                          unconditionally). LOCAL RE-MINT of natrec.rs const_no_beta_reduces \
                          (add_natrec is outside the substitution bundle), 15-arm \
                          beta_reduces.rec with a source-eq motive. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces.rec".to_string(),
                "const_ne_app".to_string(),
                "const_ne_lam".to_string(),
                "const_ne_pi".to_string(),
                "r2_const_ne_let".to_string(),
                "r2_const_ne_proj".to_string(),
                "iota_reduct_const_none".to_string(),
                "iota_reduces_to_step".to_string(),
                "option_none_ne_some_type".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "constRedex_whnf_inv".to_string(),
            type_src: TY_CONSTREDEX_WHNF_INV.to_string(),
            value_src: Some(val_constredex_whnf_inv()),
            is_axiom: false,
            description: "THE complete reduct classification at a bare const head: every \
                          whnf_step out of KExpr.const c us IS a delta_step over the fixed \
                          the_red_env (beta leg absurd by r2_const_no_beta_reduces — iota \
                          included; delta leg passes the step through the tightened-family \
                          bridge delta_reduces_to_step). The delta mirror of R1's \
                          betaRedex_whnf_inv / letRedex_whnf_inv, and the cr3 feed of \
                          candExp_delta. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step.rec".to_string(),
                "r2_const_no_beta_reduces".to_string(),
                "delta_reduces_to_step".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group C: the delta engine + necessity guard ---
        self.add_definition(SpecDefinition {
            name: "candExp_delta".to_string(),
            type_src: TY_CANDEXP_DELTA.to_string(),
            value_src: Some(val_candexp_delta()),
            is_axiom: false,
            description: "THE DELTA/CONST HEAD-EXPANSION ENGINE (corpus konst_red_aux delta \
                          case, LetDeltaSN.lean:910, per-set form): for any candidate set S, \
                          if the bare const c us delta-unfolds in the_red_env to a body \
                          already in S, then const c us is in S — cr3 at the NEUTRAL const \
                          (Neutral (const ..) computes to ConstFreeUnit, so the delta engine \
                          IS per-set generic, unlike zeta) + constRedex_whnf_inv + \
                          delta_step_deterministic pinning the unique reduct. RANK-FREE by \
                          structure: delta_reduct is a function and a bare const has no \
                          congruence positions, so the reduct set is the singleton {body} \
                          and no Acc/rank induction is needed. The corpus's WfEnv/EnvAcyclic \
                          rank recursion belongs to the ITERATED env-closure capstone (all \
                          env constants in S), which additionally needs an interp fundamental \
                          theorem to discharge S at each body — an R5/R6-era rung whose rank \
                          must enter as an EXPLICIT premise (rk : Name -> Nat + \
                          delta-decrease over a const-occurrence relation, both unlanded); \
                          no EnvAcyclic-style witness for the_red_env is registered anywhere \
                          in core_spec today. SCOPE: bare consts only; applied const spines \
                          (live recursor iota) are R3. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "isCandSet_cr3".to_string(),
                "constRedex_whnf_inv".to_string(),
                "delta_step_deterministic".to_string(),
                "ConstFreeUnit".to_string(),
                "Neutral".to_string(),
                "Eq.substType".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "constAcc_body_acc".to_string(),
            type_src: TY_CONSTACC_BODY_ACC.to_string(),
            value_src: Some(VAL_CONSTACC_BODY_ACC.to_string()),
            is_axiom: false,
            description: "Premise-necessity guard (§6.1 pair for the delta engine): the \
                          S-body premise of candExp_delta is FORCED, not decorative — at the \
                          base set, whnf_acc (const c us) yields whnf_acc body back (the \
                          const steps to its body, so accessibility descends via \
                          whnfAcc_inv_step). A premise-less engine variant would therefore \
                          claim SN of a const whose body diverges, contradicting this \
                          inversion. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnfAcc_inv_step".to_string(),
                "whnf_step.delta".to_string(),
                "delta_step_to_reduces".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group D: the real-env delta witnesses ---
        // Frequency-ranked interning tags may change when reflection grows.
        // Resolve semantic names through the same validated table used by the
        // current artifact (including the generator's fresh in-memory table).
        // The body-shape and non-reduction proofs below still check against
        // the actual selected reflected definition and fail on semantic drift.
        for (alias, semantic_name) in [
            ("fixture_nat_rec_name", "Nat.rec"),
            ("fixture_nat_zero_name", "Nat.zero"),
            ("fixture_nat_succ_name", "Nat.succ"),
            ("fixture_def_env_name", "DefEnv"),
            ("fixture_def_env_closed_b_name", "def_env_closed_b"),
        ] {
            let tag = self.reflected_name_tag(semantic_name)?;
            self.add_recursive_def(
                &format!("def {alias} : Name := kcre_name_{tag}"),
                "Resolve the witness's semantic constant name through the validated current reflection table. This is a naming adapter, not an assumed body-shape or reduction theorem.",
            )?;
        }
        self.add_definition(SpecDefinition {
            name: "r2_deltaWitness_body_no_beta".to_string(),
            type_src: ty_witness_body_no_beta(),
            value_src: Some(val_witness_body_no_beta()),
            is_axiom: false,
            description: "Witness support: app (const fixture_def_env_closed_b_name nil) (bvar 0) — the body \
                          of the reflected kernel definition def_env_lift_closed_b — admits \
                          no beta_reduces step: head is a bare const (r2_const_no_beta_\
                          reduces), argument is a bvar (no_whnf_step_bvar), top-beta dies by \
                          lam/const no-confusion, and the iota arm dies by REFL — \
                          fixture_def_env_closed_b_name (def_env_closed_b) carries no RecMeta in the real \
                          reflected env, so iota_reduct computes to none. Guard-3 posture: \
                          this is a designated-witness value computation over the_red_env; \
                          semantic-name aliases tolerate table renumbering, but changed \
                          body shape or reduction behavior still fails this proof closed. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces.rec".to_string(),
                "r2_const_no_beta_reduces".to_string(),
                "no_whnf_step_bvar".to_string(),
                "const_ne_lam".to_string(),
                "lam_ne_app".to_string(),
                "pi_ne_app".to_string(),
                "let_ne_app".to_string(),
                "proj_ne_app".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
                "iota_reduces_to_step".to_string(),
                "option_none_ne_some_type".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "r2_deltaWitness_body_acc".to_string(),
            type_src: TY_WITNESS_BODY_ACC.to_string(),
            value_src: Some(val_witness_body_acc()),
            is_axiom: false,
            description: "kcre_witness_delta_value — the REAL unfolding body of \
                          def_env_lift_closed_b, lam (const fixture_def_env_name nil) (app (const \
                          fixture_def_env_closed_b_name nil) (bvar 0)) — is whnf_acc, VACUOUSLY: it admits no \
                          whnf_step at all. Delta never fires at a lam head (root-only, \
                          kexpr_const_name = none by refl) and never under a binder \
                          (whnf_step's delta leg has no congruence); the beta leg's two live \
                          lamHead_beta_inv arms die by r2_const_no_beta_reduces (the domain \
                          const) and r2_deltaWitness_body_no_beta (the body app). Feeds the \
                          engine witness. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_acc.intro".to_string(),
                "whnf_step.rec".to_string(),
                "lamHead_beta_inv".to_string(),
                "r2_const_no_beta_reduces".to_string(),
                "r2_deltaWitness_body_no_beta".to_string(),
                "delta_step_head_none_absurd_type".to_string(),
                "delta_reduces_to_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "candExp_delta_witness".to_string(),
            type_src: TY_CANDEXP_DELTA_WITNESS.to_string(),
            value_src: Some(VAL_CANDEXP_DELTA_WITNESS.to_string()),
            is_axiom: false,
            description: "Positive discriminating witness (§6.1 control) THROUGH the delta \
                          engine at a REAL kernel constant: whnf_acc (const \
                          kcre_witness_delta_head nil) — def_env_lift_closed_b, the \
                          outermost reflected DefEnv entry — via candExp_delta at the base \
                          whole-SN set, consuming the existing Guard-4 step witness \
                          the_red_env_delta_nonvacuous (no new step computation) and \
                          r2_deltaWitness_body_acc. Exercises every engine premise at \
                          concrete arguments: a genuine delta-unfoldable const of the real \
                          reflected env is SN because its real body is. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "candExp_delta".to_string(),
                "isCand_whnfAcc".to_string(),
                "the_red_env_delta_nonvacuous".to_string(),
                "r2_deltaWitness_body_acc".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group E: the substitution transport ---
        self.add_definition(SpecDefinition {
            name: "betaRed_inst_transport".to_string(),
            type_src: TY_BETARED_INST_TRANSPORT.to_string(),
            value_src: Some(val_betared_inst_transport()),
            is_axiom: false,
            description: "THE SUBSTITUTION-TRANSPORT UNLOCK (R1 handoff item B, corpus \
                          subst_step): one full beta_reduces step commutes with \
                          instantiate_at — ALL 15 arms: beta/zeta via \
                          instantiate_nested_commutes_zero_subst, all congruences via the \
                          instantiate_at_* unfolding lemmas (binder arms at Nat.succ dd), \
                          and the IOTA arm via the landed real-env commutation \
                          iota_subst_commutes under the CARRIED premise RecEnvClosed \
                          (red_rec the_red_env) — carried, not discharged: the one-rfl \
                          discharge witnesses live in later stages (faithful_checkers / \
                          env_closed_checkers_depth), per the standing carried-hypothesis \
                          discipline. HONESTY: this is the instantiate_at spelling, not \
                          general psubst — the entire landed iota-commutation tower is \
                          instantiate_at-shaped, and a psubst-general transport would need \
                          that tower re-derived for parallel substitutions (the named open \
                          blocker); the corpus-spelling derivation needs only this form. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces.rec".to_string(),
                "instantiate_at_app".to_string(),
                "instantiate_at_lam".to_string(),
                "instantiate_at_pi".to_string(),
                "instantiate_at_let_".to_string(),
                "instantiate_at_proj".to_string(),
                "instantiate_nested_commutes_zero_subst".to_string(),
                "iota_subst_commutes".to_string(),
                "iota_reduces_to_step".to_string(),
                "iota_step_to_reduces".to_string(),
                "RecEnvClosed".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "whnfStep_inst_transport".to_string(),
            type_src: TY_WHNFSTEP_INST_TRANSPORT.to_string(),
            value_src: Some(VAL_WHNFSTEP_INST_TRANSPORT.to_string()),
            is_axiom: false,
            description: "The whnf_step-level wrapper of the transport: beta leg via \
                          betaRed_inst_transport (carried RecEnvClosed), delta leg via the \
                          landed delta_subst_commutes (carried DefEnvClosed (red_def \
                          the_red_env)) through the tightened-family bridges. With this, \
                          FULL one-step reduction — beta, zeta, iota AND delta — commutes \
                          with instantiate_at under the two carried closedness premises. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step.rec".to_string(),
                "whnf_step.beta".to_string(),
                "whnf_step.delta".to_string(),
                "betaRed_inst_transport".to_string(),
                "delta_subst_commutes".to_string(),
                "delta_step_to_reduces".to_string(),
                "delta_reduces_to_step".to_string(),
                "DefEnvClosed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "betaRed_inst_witness".to_string(),
            type_src: TY_BETARED_INST_WITNESS.to_string(),
            value_src: Some(VAL_BETARED_INST_WITNESS.to_string()),
            is_axiom: false,
            description: "Concrete transport instance computing by refl (§6 pin): the step \
                          app (lam *0 (bvar 1)) *0 -> bvar 0 — whose contractum mentions the \
                          OUTER free variable — transported under instantiate_at (sort 0) at \
                          depth 0. Both stated endpoints kernel-compute (the redex side \
                          substitutes bvar 1 UNDER the binder, the contractum side \
                          substitutes bvar 0), and the transported step is one bare \
                          beta_reduces.beta at sort 0. Pins the binder-shift arithmetic the \
                          transport's beta arm rides on. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces.beta".to_string(),
                "instantiate".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group F: the corpus-spelling derivation ---
        self.add_definition(SpecDefinition {
            name: "betaStar_inst_transport".to_string(),
            type_src: TY_BETASTAR_INST_TRANSPORT.to_string(),
            value_src: Some(VAL_BETASTAR_INST_TRANSPORT.to_string()),
            is_axiom: false,
            description: "The star closure of the transport at depth 0: a betaStar \
                          development of the body induces a betaStar development of every \
                          instantiation (betaStar.rec, each step through \
                          betaRed_inst_transport at Nat.zero). The corpus subst_arg_steps \
                          analogue. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "betaStar".to_string(),
                "betaStar.rec".to_string(),
                "betaRed_inst_transport".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "candSet_betaStar_closed".to_string(),
            type_src: TY_CANDSET_BETASTAR_CLOSED.to_string(),
            value_src: Some(VAL_CANDSET_BETASTAR_CLOSED.to_string()),
            is_axiom: false,
            description: "Any candidate set is closed along a betaStar chain: iterate the \
                          cr2 face, each betaStar step wrapped as whnf_step.beta. The star \
                          walker candExp_beta_subst uses to move contractum membership along \
                          body developments. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "isCandSet_cr2".to_string(),
                "betaStar".to_string(),
                "betaStar.rec".to_string(),
                "whnf_step.beta".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "candExp_beta_subst".to_string(),
            type_src: TY_CANDEXP_BETA_SUBST.to_string(),
            value_src: Some(VAL_CANDEXP_BETA_SUBST.to_string()),
            is_axiom: false,
            description: "THE CORPUS-SPELLING SINGLE-CONTRACTUM BETA ENGINE (corpus candExp, \
                          Stratified/Cand.lean:60, exact premise shape): the family premise \
                          quantifies ONLY the original body b — S (instantiate b a2) for \
                          every SA-member a2 — no betaStar developments. DERIVED from R1's \
                          candExp_beta by composition, exactly as the R1 honesty note \
                          projected: the development family is rebuilt by transporting each \
                          body step under instantiation (betaStar_inst_transport) and \
                          walking S along the resulting chain with cr2 \
                          (candSet_betaStar_closed). Carries the transport's RecEnvClosed \
                          (red_rec the_red_env) premise (the iota arm's closedness), \
                          discharged by later-stage checker witnesses, not here. Zero \
                          axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "candExp_beta".to_string(),
                "candSet_betaStar_closed".to_string(),
                "betaStar_inst_transport".to_string(),
                "IsCandSet".to_string(),
                "RecEnvClosed".to_string(),
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

    /// Every (name, type, value) triple registered via `add_definition`, in
    /// registration order.
    fn theorem_sources() -> Vec<(&'static str, String, String)> {
        vec![
            (
                "r2_const_ne_let",
                TY_R2_CONST_NE_LET.to_string(),
                val_r2_const_ne_let(),
            ),
            (
                "r2_const_ne_proj",
                TY_R2_CONST_NE_PROJ.to_string(),
                val_r2_const_ne_proj(),
            ),
            (
                "r2_const_no_beta_reduces",
                TY_R2_CONST_NO_BETA.to_string(),
                val_r2_const_no_beta(),
            ),
            (
                "constRedex_whnf_inv",
                TY_CONSTREDEX_WHNF_INV.to_string(),
                val_constredex_whnf_inv(),
            ),
            (
                "candExp_delta",
                TY_CANDEXP_DELTA.to_string(),
                val_candexp_delta(),
            ),
            (
                "constAcc_body_acc",
                TY_CONSTACC_BODY_ACC.to_string(),
                VAL_CONSTACC_BODY_ACC.to_string(),
            ),
            (
                "r2_deltaWitness_body_no_beta",
                ty_witness_body_no_beta(),
                val_witness_body_no_beta(),
            ),
            (
                "r2_deltaWitness_body_acc",
                TY_WITNESS_BODY_ACC.to_string(),
                val_witness_body_acc(),
            ),
            (
                "candExp_delta_witness",
                TY_CANDEXP_DELTA_WITNESS.to_string(),
                VAL_CANDEXP_DELTA_WITNESS.to_string(),
            ),
            (
                "betaRed_inst_transport",
                TY_BETARED_INST_TRANSPORT.to_string(),
                val_betared_inst_transport(),
            ),
            (
                "whnfStep_inst_transport",
                TY_WHNFSTEP_INST_TRANSPORT.to_string(),
                VAL_WHNFSTEP_INST_TRANSPORT.to_string(),
            ),
            (
                "betaRed_inst_witness",
                TY_BETARED_INST_WITNESS.to_string(),
                VAL_BETARED_INST_WITNESS.to_string(),
            ),
            (
                "betaStar_inst_transport",
                TY_BETASTAR_INST_TRANSPORT.to_string(),
                VAL_BETASTAR_INST_TRANSPORT.to_string(),
            ),
            (
                "candSet_betaStar_closed",
                TY_CANDSET_BETASTAR_CLOSED.to_string(),
                VAL_CANDSET_BETASTAR_CLOSED.to_string(),
            ),
            (
                "candExp_beta_subst",
                TY_CANDEXP_BETA_SUBST.to_string(),
                VAL_CANDEXP_BETA_SUBST.to_string(),
            ),
        ]
    }

    /// Parse-check every generated source — the fast guard for the commonest
    /// failure class (syntax-level assembly mistakes invisible to cargo
    /// check), doubly important here because the transport and the const
    /// inversions are format!-assembled.
    #[test]
    fn test_candmodel_r2_sources_parse() {
        for (name, ty, val) in theorem_sources() {
            let assembled = format!("def {name} : {ty} := {val}");
            parse_check(&assembled)
                .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
        }
    }

    /// PER-STRING paren balance on every source (cheap structural guard for
    /// the long format!-assembled proof terms).
    #[test]
    fn test_candmodel_r2_sources_paren_balanced() {
        let mut all: Vec<(String, String)> = Vec::new();
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

    /// Shape guards. (1) The const beta inversion kills its iota arm exactly
    /// once through iota_reduct_const_none and routes let/proj discrimination
    /// through the local re-mints. (2) The whnf classification's delta leg is
    /// LIVE (passes the step through), not killed. (3) The transport covers
    /// its three special arms: exactly one iota_subst_commutes and exactly
    /// two instantiate_nested_commutes_zero_subst (beta + zeta). (4) The
    /// corpus-spelling engine really is a composition of the R1 engine with
    /// the transport machinery, and its family premise is the
    /// single-contractum spelling (no betaStar in the type).
    #[test]
    fn test_candmodel_r2_shape_guards() {
        let no_beta = val_r2_const_no_beta();
        assert_eq!(
            no_beta.matches("iota_reduct_const_none").count(),
            1,
            "const inversion must kill its iota arm exactly once"
        );
        assert_eq!(
            no_beta.matches("r2_const_ne_let").count(),
            4,
            "const inversion must route zeta + 3 let congruence arms through the let re-mint"
        );
        assert_eq!(
            no_beta.matches("r2_const_ne_proj").count(),
            1,
            "const inversion must route the proj arm through the proj re-mint"
        );
        let whnf_inv = val_constredex_whnf_inv();
        assert_eq!(
            whnf_inv.matches("delta_reduces_to_step").count(),
            1,
            "const whnf classification must pass its LIVE delta leg through the bridge once"
        );
        assert!(
            !whnf_inv.contains("delta_step_head_none_absurd"),
            "const whnf classification must NOT kill its delta leg — a const head is delta-live"
        );
        let transport = val_betared_inst_transport();
        assert_eq!(
            transport.matches("iota_subst_commutes").count(),
            1,
            "transport must discharge its iota arm through the real-env commutation exactly once"
        );
        assert_eq!(
            transport
                .matches("instantiate_nested_commutes_zero_subst")
                .count(),
            2,
            "transport must close exactly the beta and zeta contractum slots with the nested \
             substitution lemma"
        );
        for needle in [
            "candExp_beta",
            "betaStar_inst_transport",
            "candSet_betaStar_closed",
        ] {
            assert!(
                VAL_CANDEXP_BETA_SUBST.contains(needle),
                "candExp_beta_subst must be the {needle} composition"
            );
        }
        assert!(
            !TY_CANDEXP_BETA_SUBST.contains("betaStar"),
            "the corpus-spelling family premise must quantify only the original body"
        );
    }

    /// Registration + kernel re-verification against the substitution bundle:
    /// the stage registers every constant, and every theorem — the delta
    /// engine, the transport, the derived corpus-spelling engine, and all
    /// witnesses — re-typechecks in the live kernel environment.
    #[test]
    fn test_candmodel_r2_registered_and_reverifies() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();
        let names = [
            "r2_const_ne_let",
            "r2_const_ne_proj",
            "r2_const_no_beta_reduces",
            "constRedex_whnf_inv",
            "candExp_delta",
            "constAcc_body_acc",
            "r2_deltaWitness_body_no_beta",
            "r2_deltaWitness_body_acc",
            "candExp_delta_witness",
            "betaRed_inst_transport",
            "whnfStep_inst_transport",
            "betaRed_inst_witness",
            "betaStar_inst_transport",
            "candSet_betaStar_closed",
            "candExp_beta_subst",
        ];
        for name in names {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the candmodel_construct_r2 stage"
            );
        }
        for name in names {
            spec.verify_definition(name).unwrap_or_else(|e| {
                panic!("{name} should re-typecheck in the spec environment: {e:?}")
            });
        }
    }
}
