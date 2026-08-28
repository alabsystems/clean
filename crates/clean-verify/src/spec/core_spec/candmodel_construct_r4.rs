// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R4 of the candidate-model construction ladder: the ONE four-argument
//! const-spine iota engine (`candExp_iota_spine4`) — generic in the head
//! constant, in the contractum FAMILY, and in all four arguments — and its two
//! instantiations: the successor-major `Nat.rec` engine
//! (`candExp_iota_natrec_succ`, R3's promised fourth `Acc` layer) and the
//! GENERIC-RECURSOR direction (`candExp_iota_genRec2`, the `redRecGen` shape
//! for a candidate-set-valued `Red` at two-minor signature families).
//!
//! Port of the corpus `StratifiedU/DataCand.lean` `red_natrec_core` at the
//! successor rule, plus the first spec-side attack on the design's row 11
//! (`redRecGen`), per `designs/2026-08-23-spec-candmodel-port.md` §5 rung R2/R4
//! and §3 row 11. Builds on R0 (`IsCandSet`), R1 (`betaStar`,
//! `betaStar_bvar_collapse`, `cand_var_witness`), R2
//! (`r2_const_no_beta_reduces`, `constRedex_whnf_inv`) and R3
//! (`constApp1_beta_inv` / `constApp1_whnf_inv`, the `beta_inv_body` 15-arm
//! scaffold, `natRecS_iota_fires`, `natRecZ_iota_fires`).
//!
//! ## One engine, two directions
//!
//! R3 landed the zero-major engine by inverting the CONCRETE `Nat.rec` spine
//! (`natRecSpine4_whnf_inv`). R4 does not add a second copy of that argument:
//! it generalizes the spine inversion to an ARBITRARY const head
//! (`constSpine2/3/4_beta_inv`, `constSpine4_whnf_inv`) and proves the engine
//! ONCE over four plain `whnf_acc.rec` layers. The two directions the task
//! asks for are then applications:
//!
//! - **A (successor major).** `candExp_iota_natrec_succ` instantiates the
//!   engine at `c := kcre_name_27`, `x4 := app Nat.succ n`, with the
//!   contractum family `K b1 b2 b3 b4 = apply_spine (kapp_args b4) (rhsSucc b1
//!   b2 b3)` — which at `b4 = app Nat.succ n2` computes to the real successor
//!   contractum. The fourth `Acc` layer is over the MAJOR (matching the
//!   `CandModel` field's `whnf_acc t`, not the weaker-to-state / stronger-to-
//!   assume `whnf_acc n`), and the fire is R3's `natRecS_iota_fires`
//!   transported along `succApp_betaStar_shape` — the development-shape lemma
//!   that says every `betaStar`-development of `app Nat.succ n` is again
//!   `app Nat.succ n2`.
//! - **B (generic recursor).** `candExp_iota_genRec2` instantiates the engine
//!   at `c := genRecName fam sig`, `us := [u]`, and is a ONE-LINE derivation:
//!   `genRecApp fam sig u m [z,s] t` IS a four-argument const spine by `rfl`
//!   (`apply_spine` + `list_append` compute), exactly as `genRecApp_nat` is an
//!   `Eq.refl`.
//!
//! ## B, precisely: what is landed and what is OBSTRUCTED
//!
//! **Landed.** `candExp_iota_genRec2` is generic in `fam`, `sig`, `u`, the
//! contractum family and all four arguments, and delivers `redRecGen`'s
//! conclusion `Red T (genRecApp …)` for `Red := S` any `IsCandSet`. Its
//! premises are the schema well-formedness conditions' REAL-ENV COMPUTATIONAL
//! CONTENT: δ-deadness of the recursor name in `red_def the_red_env`,
//! ι-deadness of the head below arity four in `red_rec the_red_env`, and the
//! ι-fire to the contractum along developments.
//!
//! **Obstructed, and this is why the field itself is not derivable.**
//! `redRecGen` supplies instead `GenFresh fam sig denv` and
//! `GenRecEnvOK fam sig u renv` — over `denv`/`renv` that the field
//! QUANTIFIES, while `whnf_step` is pinned to `the_red_env`
//! (scoping note verdict 3). The quantifier placement, not a missing lemma, is
//! the obstruction, and two registered witnesses make that mechanical rather
//! than rhetorical:
//!
//! 1. `r4_genFresh_empty` — `GenFresh fam sig DefEnv.empty` holds for EVERY
//!    `fam` and EVERY `sig`. So the freshness premise is satisfiable no matter
//!    what `red_def the_red_env` does, and therefore implies nothing about it.
//! 2. `r4_genRecName_aliases_deltaHead` + `r4_genRecHead_delta_live` — the
//!    schema's recursor name is `Name.str fam (sigLength sig)` and the
//!    reflected kernel names are `Name.str Name.anonymous k`, so
//!    `genRecName Name.anonymous <118-element sig>` IS
//!    `kcre_witness_delta_head`, the constant the Guard-4 witness δ-unfolds.
//!    A schema family the field accepts can therefore have a recursor constant
//!    that is δ-LIVE in the real env: the exact clause that fails is cr3's δ
//!    leg at the spine, whose reduct `Red T contractum` says nothing about.
//!    The ι side is the same story one name over:
//!    `r4_genRecName_aliases_natRec` + `r4_genRecC_iota_fires_natRec` exhibit a
//!    `(fam, sig)` whose `genRecName` IS the live reflected `Nat.rec`, so the
//!    real env fires the REAL `Nat.rec` rule — not the schema's
//!    `GenRecContract` contractum, which is built from `genRecRhs fam sig u`.
//!
//! The nearest landed lemma on the other side is `iota_fires_gen`
//! (`schema.rs:1147`): it computes the fire, but at the CONSTRUCTED env
//! `genREnv fam sig u`, never at `red_rec the_red_env`, and it lives in
//! `add_snschema` (Full bundle only). Generalizing it to an arbitrary
//! `GenRecEnvOK`-conformant `renv` is mechanical and would still not close the
//! gap, because `redRecGen` never instantiates `renv := red_rec the_red_env`.
//! Closing `redRecGen` as stated requires the FIELD to be re-stated against
//! the fixed env (or an extra premise pinning it) — a telescope change, and
//! therefore a decision for the R5/R6 interpretation rung, not a proof.
//!
//! ## Honesty notes (read before quoting)
//!
//! - **The engine is per-set and model-independent, like every rung so far.**
//!   `IsCandSet` has no `pi_elim`; nothing here advances the `M : CandModel`
//!   hypothesis of `whnf_terminates_well_typed_dependent`.
//! - **`whnf_acc` of the MAJOR, not of the numeral.** The successor engine
//!   assumes `whnf_acc (app Nat.succ n)`, and that is the premise whose
//!   necessity is registered (`natRecS_major_acc_necessary`). The numeral's own
//!   accessibility is NOT interchangeable with it: `delta_reduces` has no
//!   congruence rule, so a δ-step of `n` has no image at all in the spine's
//!   reduct set, and the Acc-induction route from the redex to `whnf_acc n`
//!   is blocked at the source. (Whether `whnf_acc redex -> whnf_acc n` happens
//!   to be TRUE for the reflected env is a different question — it turns on
//!   δ-acyclicity of `red_def the_red_env`, the design's build item B3 — and
//!   R4 settles neither it nor needs it.) Taking the major matches what the
//!   `CandModel` `redRec*` fields themselves assume (`whnf_acc t`).
//! - **The two concrete engine runs are CONDITIONAL, deliberately** — the same
//!   posture R3 recorded. `natRecS_engine_concrete` discharges every premise at
//!   the numeral `succ zero` EXCEPT strong normalization of the successor
//!   contractum, which it carries: the real successor RHS is a four-lambda over
//!   reflected annotations whose SN is a fundamental-theorem obligation (design
//!   rungs R5/R6). The UNCONDITIONAL content of this rung is the reduction
//!   facts (all `Eq.refl` over the real env), the necessity guards, and
//!   `r4_natrecZ_via_spine4`.
//! - **`r4_natrecZ_via_spine4` is a non-degeneracy cross-check, not filler.**
//!   It re-derives R3's `candExp_iota_natrec_zero` STATEMENT through the new
//!   generic engine, at the LIVE reflected `Nat.rec`. A degenerate engine
//!   (one whose ι continuation never consumes a fire) could not produce it.
//! - **Every reflected atom is a generated `kcre_*` name and every contractum
//!   is PROJECTED** (R3's rule): `rhsSucc` is the `OptionType.rec` projection
//!   of a closed probe's own ι reduct, so a regeneration of
//!   `kernel_core_red_env` fails these proofs CLOSED rather than drifting.
//! - **No new inductives and no new plain defs**, so the measured
//!   uniform-leading-argument recursor-promotion hazard cannot fire; the shape
//!   guard pins that.
//!
//! ## Census
//!
//! ZERO new axioms: every constant is value-bearing (all theorems via
//! `add_definition` with kernel `add_decl` checking). Census-neutral.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ==== R4 SOURCES BEGIN (pure string builders; the pre-validation parse ====
// ==== harness extracts this region TOGETHER WITH R3's, whose scaffold   ====
// ==== (`beta_inv_body` / `Cont` / `ap` / `sp` / the reflected atoms) is  ====
// ==== reused verbatim rather than duplicated.                           ====

use super::candmodel_construct_r3::{
    ap, beta_inv_body, conts_at, conts_ty_at, rhss, scontract, sp, zcontract, Cont, NSUCC, NZERO,
};

// ================================================================
// Group 0 — the GENERIC const-headed spine and its deadness hypotheses.
//
// `CHEAD` is the head of every generic spine below: a bare `KExpr.const c us`
// with `c`/`us` OUTER binders, so `kapp_fn` and `kexpr_const_name` compute
// through it even though the name itself is a variable. That is what makes
// `constSpine4_delta_none` a single `Eq.cong` and the whole engine generic.
// ================================================================

/// The generic spine head `KExpr.const c us`.
pub const CHEAD: &str = "(KExpr.const c us)";

/// The generic const-headed application spine over the given argument terms.
pub fn spc(args: &[&str]) -> String {
    let mut t = CHEAD.to_string();
    for a in args {
        t = ap(&t, a);
    }
    t
}

/// Argument binder names of the generic spine.
const XS: [&str; 4] = ["x1", "x2", "x3", "x4"];
/// Universally-quantified argument names of the deadness hypotheses.
const YS: [&str; 4] = ["y1", "y2", "y3", "y4"];

/// `forall y1..yk, iota_reduct (red_rec the_red_env) (spc y1..yk) = none` —
/// the arity-`k` ι-deadness hypothesis of the head constant. At the concrete
/// `Nat.rec` head each of these is one `Eq.refl` over the real env; at a
/// generic recursor name they are premises, because nothing in `redRecGen`
/// constrains what the real env does at that name (module docs, B).
pub fn hdead_ty(k: usize) -> String {
    format!(
        "forall {}, Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) {}) (OptionType.none KExpr)",
        kexpr_binders(k),
        spc(&YS[..k])
    )
}

/// `(y1 : KExpr) .. (yk : KExpr)` — the shared binder prefix of the deadness
/// hypotheses (comma-terminated by the caller, which is where the first
/// assembly bug of this rung lived).
fn kexpr_binders(k: usize) -> String {
    YS[..k]
        .iter()
        .map(|y| format!("({y} : KExpr)"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// The `h1 .. hn` deadness binders of an arity-`n` inversion (arity 4 keeps
/// its OWN ι arm live, so it binds only `h1 h2 h3`).
fn hyp_binders(n: usize) -> String {
    let upto = if n >= 4 { 3 } else { n };
    (1..=upto)
        .map(|i| format!("(h{i} : {}) ", hdead_ty(i)))
        .collect::<Vec<_>>()
        .join("")
}

/// The `h1 .. hn` deadness ARGUMENTS at a call site.
fn hyp_args(n: usize) -> String {
    let upto = if n >= 4 { 3 } else { n };
    (1..=upto)
        .map(|i| format!("h{i}"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// Refute a transported `iota_reduces qe qe2` inside a `beta_inv_body` ι arm,
/// using a HYPOTHESIS `hyp : iota_reduct env <redex> = none` in place of R3's
/// `Eq.refl` (whose truth depends on the head being the concrete `Nat.rec`).
fn iota_kill_hyp(redex: &str, hyp: &str) -> String {
    format!(
        "option_none_ne_some_type KExpr qe2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct (red_rec the_red_env) qe) (OptionType.some KExpr qe2) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) qe) (OptionType.none KExpr) (Eq.trans (OptionType KExpr) (iota_reduct (red_rec the_red_env) qe) (iota_reduct (red_rec the_red_env) {redex}) (OptionType.none KExpr) (Eq.cong KExpr (OptionType KExpr) (fun (qz : KExpr) => iota_reduct (red_rec the_red_env) qz) qe {redex} heq) {hyp})) (iota_reduces_to_step qe qe2 qio))"
    )
}

/// Refute an ι continuation whose reduct term is already known (no `heq`
/// transport needed) — used for the arity-1 sub-inversion's LIVE ι arm.
fn iota_kill_direct(redex: &str, reduct: &str, hvar: &str, hyp: &str) -> String {
    format!(
        "option_none_ne_some_type KExpr {reduct} C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct (red_rec the_red_env) {redex}) (OptionType.some KExpr {reduct}) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) {redex}) (OptionType.none KExpr) {hyp}) (iota_reduces_to_step {redex} {reduct} {hvar}))"
    )
}

// ================================================================
// Group A — the generic const-spine reduct classification (arity 2..4).
//
// Same 15-arm `beta_reduces.rec` scaffold as R3 (`beta_inv_body`), same
// ARM-ARITY discipline (every recursive structural minor binds its
// `beta_reduces` premise BEFORE its induction hypothesis), same CAPTURE
// discipline (template binders are `q`-prefixed; the substituted terms mention
// only `c`/`us`/`x1..x4`/`h1..h3`, none of which is `q`-prefixed).
// ================================================================

/// The `k1..kn` argument-step continuations of an arity-`n` generic spine.
fn spc_conts(args: &[&str]) -> Vec<Cont> {
    (0..args.len())
        .map(|i| {
            let mut repl: Vec<&str> = args.to_vec();
            repl[i] = "qy";
            let name: &'static str = match i {
                0 => "k1",
                1 => "k2",
                2 => "k3",
                _ => "k4",
            };
            Cont {
                name,
                ty: format!(
                    "forall (qy : KExpr), beta_reduces {} qy -> Eq KExpr @R@ {} -> C",
                    args[i],
                    spc(&repl)
                ),
            }
        })
        .collect()
}

/// The four live arm bodies of the arity-`n` generic spine inversion.
fn spc_live_arms(n: usize) -> (String, String, String, String) {
    let args = &XS[..n];
    let redex = spc(args);
    let head = spc(&args[..n - 1]);
    let arg = args[n - 1];
    // 1 beta: the redex is an application whose function is itself an
    // application (n >= 2), so the top-level beta constructor's `lam` head is
    // impossible.
    let inner_head = spc(&args[..n - 2]);
    let inner_arg = args[n - 2];
    let live_beta = format!(
        "lam_ne_app qA qb {inner_head} {inner_arg} C (app_inj_fst (KExpr.lam qA qb) qarg {head} {arg} heq)"
    );
    // 2 app_left: recurse into the (n-1)-argument spine.
    let step_transport = format!(
        "(Eq.rec KExpr qf (fun (qx : KExpr) (_ : Eq KExpr qf qx) => beta_reduces qx qf2) qstep {head} (app_inj_fst qf qa {head} {arg} heq))"
    );
    let sub_conts: Vec<String> = (0..n - 1)
        .map(|i| {
            let mut repl: Vec<&str> = args.to_vec();
            repl[i] = "qy";
            let inner = spc(&repl[..n - 1]);
            let outer = spc(&repl);
            let kname = match i {
                0 => "k1",
                1 => "k2",
                _ => "k3",
            };
            format!(
                "(fun (qy : KExpr) (hy : beta_reduces {} qy) (heq2 : Eq KExpr qf2 {inner}) => {kname} qy hy (Eq.trans KExpr (KExpr.app qf2 qa) (KExpr.app {inner} qa) {outer} (Eq.cong KExpr KExpr (fun (qz : KExpr) => KExpr.app qz qa) qf2 {inner} heq2) (Eq.cong KExpr KExpr (fun (qz : KExpr) => KExpr.app {inner} qz) qa {arg} (app_inj_snd qf qa {head} {arg} heq))))",
                args[i]
            )
        })
        .collect();
    let live_appl = if n == 2 {
        // The arity-1 sub-inversion is R3's `constApp1_beta_inv`, whose ι arm
        // is LIVE (a generic head MAY be a one-slot recursor) — killed here by
        // the caller's h1.
        let r1 = spc(&["x1"]);
        format!(
            "constApp1_beta_inv c us x1 qf2 C {step_transport} {} (fun (qio2 : iota_reduces {r1} qf2) => {})",
            sub_conts[0],
            iota_kill_direct(&r1, "qf2", "qio2", "(h1 x1)")
        )
    } else {
        format!(
            "constSpine{}_beta_inv c us {} {} qf2 C {step_transport} {}",
            n - 1,
            hyp_args(n - 1),
            args[..n - 1].join(" "),
            sub_conts.join(" ")
        )
    };
    // 3 app_right.
    let kname = match n {
        2 => "k2",
        3 => "k3",
        _ => "k4",
    };
    let live_appr = format!(
        "{kname} qa2 (Eq.rec KExpr qa (fun (qx : KExpr) (_ : Eq KExpr qa qx) => beta_reduces qx qa2) qstep {arg} (app_inj_snd qf qa {head} {arg} heq)) (Eq.cong KExpr KExpr (fun (qz : KExpr) => KExpr.app qz qa2) qf {head} (app_inj_fst qf qa {head} {arg} heq))"
    );
    // 14 iota: LIVE at arity 4, killed by the caller's h_n below it.
    let live_iota = if n == 4 {
        format!(
            "kIota (Eq.substType KExpr (fun (qz : KExpr) => iota_reduces qz qe2) qe {redex} heq qio)"
        )
    } else {
        iota_kill_hyp(&redex, &format!("(h{n} {})", args.join(" ")))
    };
    (live_beta, live_appl, live_appr, live_iota)
}

pub fn ty_const_spine_beta_inv(n: usize) -> String {
    let args = &XS[..n];
    let redex = spc(args);
    let mut cs = spc_conts(args);
    if n == 4 {
        cs.push(Cont {
            name: "kIota",
            ty: format!("iota_reduces {redex} @R@ -> C"),
        });
    }
    let xb = args
        .iter()
        .map(|a| format!("({a} : KExpr) "))
        .collect::<Vec<_>>()
        .join("");
    format!(
        "forall (c : Name) (us : ListType Level) {}{xb}(g2 : KExpr) (C : Type), beta_reduces {redex} g2 -> {}C",
        hyp_binders(n),
        conts_ty_at(&cs, "g2")
    )
}

pub fn val_const_spine_beta_inv(n: usize) -> String {
    let args = &XS[..n];
    let redex = spc(args);
    let head = spc(&args[..n - 1]);
    let arg = args[n - 1];
    let mut cs = spc_conts(args);
    if n == 4 {
        cs.push(Cont {
            name: "kIota",
            ty: format!("iota_reduces {redex} @R@ -> C"),
        });
    }
    let (lb, la, lr, li) = spc_live_arms(n);
    let body = beta_inv_body(&redex, &head, arg, &cs, &lb, &la, &lr, &li);
    let xb = args
        .iter()
        .map(|a| format!("({a} : KExpr) "))
        .collect::<Vec<_>>()
        .join("");
    format!(
        "fun (c : Name) (us : ListType Level) {}{xb}(g2 : KExpr) (C : Type) (hb : beta_reduces {redex} g2){} => {body}",
        hyp_binders(n),
        conts_at(&cs, "g2", "")
    )
}

/// The whnf continuations of the arity-4 generic spine: the four argument
/// steps, the LIVE ι, and the LIVE δ (the head IS a const, so δ genuinely
/// fires whenever the env defines it — this is the leg R3's `Nat.rec` spine
/// could refute by `rfl` and a generic head cannot).
fn spc4_whnf_conts() -> Vec<Cont> {
    let redex = spc(&XS);
    let mut cs = spc_conts(&XS);
    cs.push(Cont {
        name: "kIota",
        ty: format!("iota_reduces {redex} @R@ -> C"),
    });
    cs.push(Cont {
        name: "kDelta",
        ty: format!("delta_step (red_def the_red_env) {redex} @R@ -> C"),
    });
    cs
}

pub fn ty_const_spine4_whnf_inv() -> String {
    let redex = spc(&XS);
    let cs = spc4_whnf_conts();
    let xb = XS
        .iter()
        .map(|a| format!("({a} : KExpr) "))
        .collect::<Vec<_>>()
        .join("");
    format!(
        "forall (c : Name) (us : ListType Level) {}{xb}(g2 : KExpr) (C : Type), whnf_step {redex} g2 -> {}C",
        hyp_binders(4),
        conts_ty_at(&cs, "g2")
    )
}

pub fn val_const_spine4_whnf_inv() -> String {
    let redex = spc(&XS);
    let cs = spc4_whnf_conts();
    let xb = XS
        .iter()
        .map(|a| format!("({a} : KExpr) "))
        .collect::<Vec<_>>()
        .join("");
    format!(
        "fun (c : Name) (us : ListType Level) {}{xb}(g2 : KExpr) (C : Type) (hs : whnf_step {redex} g2){} => whnf_step.rec {redex} g2 (fun (_ : whnf_step {redex} g2) => C) (fun (hbr : beta_reduces {redex} g2) => constSpine4_beta_inv c us h1 h2 h3 x1 x2 x3 x4 g2 C hbr k1 k2 k3 k4 kIota) (fun (hdr : delta_reduces {redex} g2) => kDelta (delta_reduces_to_step {redex} g2 hdr)) hs",
        hyp_binders(4),
        conts_at(&cs, "g2", "")
    )
}

/// δ-deadness of a whole four-argument spine from δ-deadness of its HEAD:
/// `delta_reduct` looks the name up at `kapp_fn` and re-applies `kapp_args`,
/// so a `none` lookup propagates through ONE `Eq.cong` over the option — no
/// case analysis, hence no Type-valued eliminator anywhere near the Prop `Eq`.
pub fn ty_const_spine4_delta_none() -> String {
    format!(
        "forall (c : Name) (us : ListType Level), Eq (OptionType KExpr) (defval_for (red_def the_red_env) c) (OptionType.none KExpr) -> forall (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (x4 : KExpr), Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) {}) (OptionType.none KExpr)",
        spc(&XS)
    )
}

pub fn val_const_spine4_delta_none() -> String {
    let redex = spc(&XS);
    format!(
        "fun (c : Name) (us : ListType Level) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) c) (OptionType.none KExpr)) (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (x4 : KExpr) => Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (qo : OptionType KExpr) => opt_bind KExpr KExpr qo (fun (qv : KExpr) => OptionType.some KExpr (apply_spine (kapp_args {redex}) qv))) (defval_for (red_def the_red_env) c) (OptionType.none KExpr) hdef"
    )
}

// ================================================================
// Group B — THE ENGINE: one candidate-set head-expansion for a four-argument
// const spine that ι-fires to a contractum FAMILY, over four plain `Acc`
// layers. Corpus shape: `red_natrec_core` (DataCand.lean:278), generalized
// from one recursor to any const head and any contractum family.
// ================================================================

fn fire_ty(z: &[&str]) -> String {
    format!(
        "forall (b1 : KExpr) (b2 : KExpr) (b3 : KExpr) (b4 : KExpr), betaStar {} b1 -> betaStar {} b2 -> betaStar {} b3 -> betaStar {} b4 -> iota_reduces {} (K b1 b2 b3 b4)",
        z[0],
        z[1],
        z[2],
        z[3],
        spc(&["b1", "b2", "b3", "b4"])
    )
}

fn fam_ty(z: &[&str]) -> String {
    format!(
        "forall (b1 : KExpr) (b2 : KExpr) (b3 : KExpr) (b4 : KExpr), betaStar {} b1 -> betaStar {} b2 -> betaStar {} b3 -> betaStar {} b4 -> S (K b1 b2 b3 b4)",
        z[0], z[1], z[2], z[3]
    )
}

/// The engine's motive after `i` arguments have been peeled (`i` = 1..4): the
/// remaining arguments stay universally quantified with their `Acc` proofs.
fn engine_motive(i: usize, a: &str) -> String {
    let mut z: Vec<&str> = vec!["t1", "t2", "t3", "t4"];
    z[i - 1] = a;
    let ws: [&str; 3] = ["w2", "w3", "w4"];
    let mut pre = String::new();
    for (k, item) in ws.iter().enumerate().take(4 - i) {
        z[i + k] = item;
        pre.push_str(&format!("forall ({item} : KExpr), whnf_acc {item} -> "));
    }
    format!(
        "{pre}({}) -> ({}) -> S {}",
        fire_ty(&z),
        fam_ty(&z),
        spc(&z)
    )
}

pub fn ty_candexp_iota_spine4() -> String {
    let z = ["x1", "x2", "x3", "x4"];
    format!(
        "forall (S : KExpr -> Type), IsCandSet S -> forall (c : Name) (us : ListType Level) {}(hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) c) (OptionType.none KExpr)) (K : KExpr -> KExpr -> KExpr -> KExpr -> KExpr) (x1 : KExpr), whnf_acc x1 -> forall (x2 : KExpr), whnf_acc x2 -> forall (x3 : KExpr), whnf_acc x3 -> forall (x4 : KExpr), whnf_acc x4 -> ({}) -> ({}) -> S {}",
        hyp_binders(4),
        fire_ty(&z),
        fam_ty(&z),
        spc(&z)
    )
}

pub fn val_candexp_iota_spine4() -> String {
    let ts = ["t1", "t2", "t3", "t4"];
    let redex = spc(&ts);
    let kc = "(K t1 t2 t3 t4)";
    // The four argument continuations.
    let cong = |slot: usize| {
        let mut repl: Vec<&str> = ts.to_vec();
        repl[slot] = "qy";
        let target = spc(&repl);
        let src = ts[slot];
        // Re-base the fire/fam families along the step `hy : src -> qy`.
        let shift = |fname: &str| {
            let binders = "(b1 : KExpr) (b2 : KExpr) (b3 : KExpr) (b4 : KExpr)";
            let mut prem = String::new();
            for (j, item) in repl.iter().enumerate() {
                prem.push_str(&format!(" (p{} : betaStar {} b{})", j + 1, item, j + 1));
            }
            let args = (0..4)
                .map(|j| {
                    if j == slot {
                        format!("(betaStar.step {src} qy b{} hy p{})", slot + 1, slot + 1)
                    } else {
                        format!("p{}", j + 1)
                    }
                })
                .collect::<Vec<_>>()
                .join(" ");
            format!("(fun {binders}{prem} => {fname} b1 b2 b3 b4 {args})")
        };
        // The remaining Acc proofs are rebuilt from the layers' step fields.
        let mut rest = String::new();
        for item in ts.iter().skip(slot + 1) {
            rest.push_str(&format!(" {item} (whnf_acc.intro {item} s{item}f)"));
        }
        let ih = format!(
            "ih{} qy (whnf_step.beta {src} qy hy){rest} {} {}",
            slot + 1,
            shift("hfire"),
            shift("hfam")
        );
        format!(
            "(fun (qy : KExpr) (hy : beta_reduces {src} qy) (heq : Eq KExpr e2 {target}) => Eq.substType KExpr (fun (qw : KExpr) => S qw) {target} e2 (Eq.symm KExpr e2 {target} heq) ({ih}))"
        )
    };
    let fire_refl = "hfire t1 t2 t3 t4 (betaStar.refl t1) (betaStar.refl t2) (betaStar.refl t3) (betaStar.refl t4)";
    let fam_refl = "hfam t1 t2 t3 t4 (betaStar.refl t1) (betaStar.refl t2) (betaStar.refl t3) (betaStar.refl t4)";
    let k_iota = format!(
        "(fun (hio : iota_reduces {redex} e2) => Eq.substType KExpr (fun (qw : KExpr) => S qw) {kc} e2 (option_some_inj KExpr {kc} e2 (Eq.trans (OptionType KExpr) (OptionType.some KExpr {kc}) (iota_reduct (red_rec the_red_env) {redex}) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) {redex}) (OptionType.some KExpr {kc}) (iota_reduces_to_step {redex} {kc} ({fire_refl}))) (iota_reduces_to_step {redex} e2 hio))) ({fam_refl}))"
    );
    let k_delta = format!(
        "(fun (hdl : delta_step (red_def the_red_env) {redex} e2) => option_none_ne_some_type KExpr e2 (S e2) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def the_red_env) {redex}) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) {redex}) (OptionType.none KExpr) (constSpine4_delta_none c us hdef t1 t2 t3 t4)) hdl))"
    );
    let core = format!(
        "isCandSet_cr3 S hS {redex} ConstFreeUnit.triv (fun (e2 : KExpr) (hstep : whnf_step {redex} e2) => constSpine4_whnf_inv c us h1 h2 h3 t1 t2 t3 t4 e2 (S e2) hstep {} {} {} {} {k_iota} {k_delta})",
        cong(0),
        cong(1),
        cong(2),
        cong(3)
    );
    // Innermost layer: the major, both families now fully instantiated.
    let arm4 = format!(
        "(fun (t4 : KExpr) (st4f : forall (w : KExpr), whnf_step t4 w -> whnf_acc w) (ih4 : forall (w : KExpr), whnf_step t4 w -> {}) (hfire : {}) (hfam : {}) => {core})",
        engine_motive(4, "w"),
        fire_ty(&ts),
        fam_ty(&ts)
    );
    let arm3 = format!(
        "(fun (t3 : KExpr) (st3f : forall (w : KExpr), whnf_step t3 w -> whnf_acc w) (ih3 : forall (w : KExpr), whnf_step t3 w -> {}) (a4 : KExpr) (ha4 : whnf_acc a4) => whnf_acc.rec (fun (t4 : KExpr) (_ : whnf_acc t4) => {}) {arm4} a4 ha4)",
        engine_motive(3, "w"),
        engine_motive(4, "t4")
    );
    let arm2 = format!(
        "(fun (t2 : KExpr) (st2f : forall (w : KExpr), whnf_step t2 w -> whnf_acc w) (ih2 : forall (w : KExpr), whnf_step t2 w -> {}) (a3 : KExpr) (ha3 : whnf_acc a3) => whnf_acc.rec (fun (t3 : KExpr) (_ : whnf_acc t3) => {}) {arm3} a3 ha3)",
        engine_motive(2, "w"),
        engine_motive(3, "t3")
    );
    let arm1 = format!(
        "(fun (t1 : KExpr) (st1f : forall (w : KExpr), whnf_step t1 w -> whnf_acc w) (ih1 : forall (w : KExpr), whnf_step t1 w -> {}) (a2 : KExpr) (ha2 : whnf_acc a2) => whnf_acc.rec (fun (t2 : KExpr) (_ : whnf_acc t2) => {}) {arm2} a2 ha2)",
        engine_motive(1, "w"),
        engine_motive(2, "t2")
    );
    let z = ["x1", "x2", "x3", "x4"];
    format!(
        "fun (S : KExpr -> Type) (hS : IsCandSet S) (c : Name) (us : ListType Level) {}(hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) c) (OptionType.none KExpr)) (K : KExpr -> KExpr -> KExpr -> KExpr -> KExpr) (x1 : KExpr) (hx1 : whnf_acc x1) (x2 : KExpr) (hx2 : whnf_acc x2) (x3 : KExpr) (hx3 : whnf_acc x3) (x4 : KExpr) (hx4 : whnf_acc x4) (hfire0 : {}) (hfam0 : {}) => whnf_acc.rec (fun (t1 : KExpr) (_ : whnf_acc t1) => {}) {arm1} x1 hx1 x2 hx2 x3 hx3 x4 hx4 hfire0 hfam0",
        hyp_binders(4),
        fire_ty(&z),
        fam_ty(&z),
        engine_motive(1, "t1")
    )
}

// ================================================================
// Group C — the real-env reduction facts of the `Nat.rec` / `Nat.succ` heads
// (every one an `Eq.refl` over the reflected kernel core).
// ================================================================

/// `iota_reduct` of a `Nat.rec` spine BELOW arity 4 is `none` — the major slot
/// of the reflected `Nat.rec` metadata is index 3, so a shorter spine has no
/// major at all. R3 proved these inline inside its inversions; the generic
/// engine needs them as first-class terms.
pub fn ty_natrec_spine_iota_none(k: usize) -> String {
    format!(
        "forall {}, Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) {}) (OptionType.none KExpr)",
        kexpr_binders(k),
        sp(&YS[..k])
    )
}

pub fn val_natrec_spine_iota_none(k: usize) -> String {
    let binders = YS[..k]
        .iter()
        .map(|y| format!("({y} : KExpr) "))
        .collect::<Vec<_>>()
        .join("");
    format!("fun {binders}=> Eq.refl (OptionType KExpr) (OptionType.none KExpr)")
}

pub const TY_NATREC_DEFVAL_NONE: &str =
    "Eq (OptionType KExpr) (defval_for (red_def the_red_env) kcre_name_27) (OptionType.none KExpr)";
pub const VAL_NATREC_DEFVAL_NONE: &str = "Eq.refl (OptionType KExpr) (OptionType.none KExpr)";

pub fn ty_succapp_iota_none() -> String {
    format!(
        "forall (a : KExpr), Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) {}) (OptionType.none KExpr)",
        ap(NSUCC, "a")
    )
}

pub fn ty_succapp_delta_none() -> String {
    format!(
        "forall (a : KExpr), Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) {}) (OptionType.none KExpr)",
        ap(NSUCC, "a")
    )
}

pub const VAL_SUCCAPP_NONE: &str =
    "fun (a : KExpr) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)";

// ================================================================
// Group D — the successor major: its one-step classification, its development
// shape, and the ENGINE instance.
// ================================================================

/// `whnf_step (app Nat.succ n) w` can only be an argument beta step: the head
/// is a bare const (no top beta, no head beta), `Nat.succ` is not a recursor
/// (ι dead by `rfl`) and is not δ-defined (δ dead by `rfl`).
pub fn ty_succapp_whnf_inv() -> String {
    format!(
        "forall (n : KExpr) (g2 : KExpr) (C : Type), whnf_step {} g2 -> (forall (n2 : KExpr), beta_reduces n n2 -> Eq KExpr g2 {} -> C) -> C",
        ap(NSUCC, "n"),
        ap(NSUCC, "n2")
    )
}

pub fn val_succapp_whnf_inv() -> String {
    let r = ap(NSUCC, "n");
    format!(
        "fun (n : KExpr) (g2 : KExpr) (C : Type) (hs : whnf_step {r} g2) (k : forall (n2 : KExpr), beta_reduces n n2 -> Eq KExpr g2 {} -> C) => constApp1_whnf_inv kcre_name_10 (ListType.nil Level) n g2 C hs k (fun (hio : iota_reduces {r} g2) => {}) (fun (hdl : delta_step (red_def the_red_env) {r} g2) => option_none_ne_some_type KExpr g2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def the_red_env) {r}) (OptionType.some KExpr g2) (Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) {r}) (OptionType.none KExpr) (natSuccApp_delta_none n)) hdl))",
        ap(NSUCC, "n2"),
        iota_kill_direct(&r, "g2", "hio", "(natSuccApp_iota_none n)")
    )
}

/// Every `betaStar`-development of `app Nat.succ n` is again `app Nat.succ n2`
/// for a development `n2` of `n`. This is what lets the successor ι fire
/// survive the engine's fourth `Acc` layer, and it is CPS-stated at a
/// `(C : Type)` so it can be instantiated at the Type-valued `iota_reduces`
/// (never at the Prop-valued `iota_step` — the measured Prop/Type trap).
pub fn ty_succapp_betastar_shape() -> String {
    format!(
        "forall (n : KExpr) (b : KExpr) (C : Type), betaStar {} b -> (forall (n2 : KExpr), betaStar n n2 -> Eq KExpr b {} -> C) -> C",
        ap(NSUCC, "n"),
        ap(NSUCC, "n2")
    )
}

pub fn val_succapp_betastar_shape() -> String {
    let rn0 = ap(NSUCC, "n0");
    let mot = format!(
        "(fun (qs : KExpr) (qt : KExpr) (_ : betaStar qs qt) => forall (n0 : KExpr), Eq KExpr qs {rn0} -> (forall (n2 : KExpr), betaStar n0 n2 -> Eq KExpr qt {} -> C) -> C)",
        ap(NSUCC, "n2")
    );
    let arm_refl = "(fun (qe : KExpr) (n0 : KExpr) (heq : Eq KExpr qe (KExpr.app (KExpr.const kcre_name_10 (ListType.nil Level)) n0)) (k : forall (n2 : KExpr), betaStar n0 n2 -> Eq KExpr qe (KExpr.app (KExpr.const kcre_name_10 (ListType.nil Level)) n2) -> C) => k n0 (betaStar.refl n0) heq)";
    let arm_step = format!(
        "(fun (qe : KExpr) (qe2 : KExpr) (qe3 : KExpr) (qstep : beta_reduces qe qe2) (_qrest : betaStar qe2 qe3) (qih : forall (n0 : KExpr), Eq KExpr qe2 {rn0} -> (forall (n2 : KExpr), betaStar n0 n2 -> Eq KExpr qe3 {rn2} -> C) -> C) (n0 : KExpr) (heq : Eq KExpr qe {rn0}) (k : forall (n2 : KExpr), betaStar n0 n2 -> Eq KExpr qe3 {rn2} -> C) => constApp1_beta_inv kcre_name_10 (ListType.nil Level) n0 qe2 C (Eq.rec KExpr qe (fun (qx : KExpr) (_ : Eq KExpr qe qx) => beta_reduces qx qe2) qstep {rn0} heq) (fun (qy : KExpr) (hy : beta_reduces n0 qy) (heq2 : Eq KExpr qe2 {ry}) => qih qy heq2 (fun (n2 : KExpr) (hst : betaStar qy n2) (heq3 : Eq KExpr qe3 {rn2}) => k n2 (betaStar.step n0 qy n2 hy hst) heq3)) (fun (qio : iota_reduces {rn0} qe2) => {}))",
        iota_kill_direct(&rn0, "qe2", "qio", "(natSuccApp_iota_none n0)"),
        rn2 = ap(NSUCC, "n2"),
        ry = ap(NSUCC, "qy")
    );
    format!(
        "fun (n : KExpr) (b : KExpr) (C : Type) (hstar : betaStar {} b) (k0 : forall (n2 : KExpr), betaStar n n2 -> Eq KExpr b {} -> C) => betaStar.rec {mot} {arm_refl} {arm_step} {} b hstar n (Eq.refl KExpr {}) k0",
        ap(NSUCC, "n"),
        ap(NSUCC, "n2"),
        ap(NSUCC, "n"),
        ap(NSUCC, "n")
    )
}

/// The successor contractum FAMILY, as a function of the four spine arguments:
/// at `b4 = app Nat.succ n2` it computes to `rhsSucc b1 b2 b3 n2` because
/// `kapp_args (app Nat.succ n2)` is `[n2]`. Written this way (rather than as a
/// projection of `b4`) so that the engine's generic `K` slot is filled by a
/// term that needs no inversion to evaluate.
pub fn succ_family() -> String {
    format!(
        "(fun (b1 : KExpr) (b2 : KExpr) (b3 : KExpr) (b4 : KExpr) => apply_spine (kapp_args b4) {})",
        ap(&ap(&ap(&rhss(), "b1"), "b2"), "b3")
    )
}

fn sfam(a1: &str, a2: &str, a3: &str, n: &str) -> String {
    format!(
        "forall (b1 : KExpr), betaStar {a1} b1 -> forall (b2 : KExpr), betaStar {a2} b2 -> forall (b3 : KExpr), betaStar {a3} b3 -> forall (b4 : KExpr), betaStar {n} b4 -> S {}",
        scontract("b1", "b2", "b3", "b4")
    )
}

fn sredex(a1: &str, a2: &str, a3: &str, n: &str) -> String {
    sp(&[a1, a2, a3, &ap(NSUCC, n)])
}

pub fn ty_candexp_iota_natrec_succ() -> String {
    format!(
        "forall (S : KExpr -> Type), IsCandSet S -> forall (mot : KExpr), whnf_acc mot -> forall (m0 : KExpr), whnf_acc m0 -> forall (m1 : KExpr), whnf_acc m1 -> forall (n : KExpr), whnf_acc {} -> ({}) -> S {}",
        ap(NSUCC, "n"),
        sfam("mot", "m0", "m1", "n"),
        sredex("mot", "m0", "m1", "n")
    )
}

pub fn val_candexp_iota_natrec_succ() -> String {
    let kfam = succ_family();
    let prem = "(p1 : betaStar mot b1) (p2 : betaStar m0 b2) (p3 : betaStar m1 b3) (p4 : betaStar (KExpr.app (KExpr.const kcre_name_10 (ListType.nil Level)) n) b4)";
    let binders = "(b1 : KExpr) (b2 : KExpr) (b3 : KExpr) (b4 : KExpr)";
    let fire_goal = format!(
        "iota_reduces {} ({kfam} b1 b2 b3 b4)",
        sp(&["b1", "b2", "b3", "b4"])
    );
    let fire = format!(
        "(fun {binders} {prem} => succApp_betaStar_shape n b4 ({fire_goal}) p4 (fun (n2 : KExpr) (hst : betaStar n n2) (heq : Eq KExpr b4 {rn2}) => Eq.substType KExpr (fun (qw : KExpr) => iota_reduces {} ({kfam} b1 b2 b3 qw)) {rn2} b4 (Eq.symm KExpr b4 {rn2} heq) (iota_step_to_reduces {} {} (natRecS_iota_fires b1 b2 b3 n2))))",
        sp(&["b1", "b2", "b3", "qw"]),
        sp(&["b1", "b2", "b3", &ap(NSUCC, "n2")]),
        scontract("b1", "b2", "b3", "n2"),
        rn2 = ap(NSUCC, "n2")
    );
    let fam = format!(
        "(fun {binders} {prem} => succApp_betaStar_shape n b4 (S ({kfam} b1 b2 b3 b4)) p4 (fun (n2 : KExpr) (hst : betaStar n n2) (heq : Eq KExpr b4 {rn2}) => Eq.substType KExpr (fun (qw : KExpr) => S ({kfam} b1 b2 b3 qw)) {rn2} b4 (Eq.symm KExpr b4 {rn2} heq) (hfam0 b1 p1 b2 p2 b3 p3 n2 hst)))",
        rn2 = ap(NSUCC, "n2")
    );
    format!(
        "fun (S : KExpr -> Type) (hS : IsCandSet S) (mot : KExpr) (hmot : whnf_acc mot) (m0 : KExpr) (hm0 : whnf_acc m0) (m1 : KExpr) (hm1 : whnf_acc m1) (n : KExpr) (hmaj : whnf_acc {}) (hfam0 : {}) => candExp_iota_spine4 S hS kcre_name_27 (ListType.nil Level) natRecSpine1_iota_none natRecSpine2_iota_none natRecSpine3_iota_none natRec_defval_none {kfam} mot hmot m0 hm0 m1 hm1 {} hmaj {fire} {fam}",
        ap(NSUCC, "n"),
        sfam("mot", "m0", "m1", "n"),
        ap(NSUCC, "n")
    )
}

// ================================================================
// Group E — the GENERIC-RECURSOR direction, and the obstruction that keeps it
// from being the `redRecGen` field itself.
// ================================================================

fn gsp(m: &str, z: &str, s: &str, t: &str) -> String {
    format!("(genRecApp fam sig u {m} (ListType.cons KExpr {z} (ListType.cons KExpr {s} (ListType.nil KExpr))) {t})")
}

/// The generic-recursor spine head, arity `k`.
fn gspine(args: &[&str]) -> String {
    let mut t = "(genRecC fam sig u)".to_string();
    for a in args {
        t = ap(&t, a);
    }
    t
}

fn ghdead_ty(k: usize) -> String {
    format!(
        "forall {}, Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) {}) (OptionType.none KExpr)",
        kexpr_binders(k),
        gspine(&YS[..k])
    )
}

fn gfire_ty() -> String {
    format!(
        "forall (b1 : KExpr) (b2 : KExpr) (b3 : KExpr) (b4 : KExpr), betaStar m b1 -> betaStar z b2 -> betaStar s b3 -> betaStar t b4 -> iota_reduces {} (K b1 b2 b3 b4)",
        gsp("b1", "b2", "b3", "b4")
    )
}

const GFAM_TY: &str = "forall (b1 : KExpr) (b2 : KExpr) (b3 : KExpr) (b4 : KExpr), betaStar m b1 -> betaStar z b2 -> betaStar s b3 -> betaStar t b4 -> S (K b1 b2 b3 b4)";

pub fn ty_candexp_iota_genrec2() -> String {
    format!(
        "forall (S : KExpr -> Type), IsCandSet S -> forall (fam : Name) (sig : ListType Nat) (u : Level) (h1 : {}) (h2 : {}) (h3 : {}) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) (genRecName fam sig)) (OptionType.none KExpr)) (K : KExpr -> KExpr -> KExpr -> KExpr -> KExpr) (m : KExpr), whnf_acc m -> forall (z : KExpr), whnf_acc z -> forall (s : KExpr), whnf_acc s -> forall (t : KExpr), whnf_acc t -> ({}) -> ({GFAM_TY}) -> S {}",
        ghdead_ty(1),
        ghdead_ty(2),
        ghdead_ty(3),
        gfire_ty(),
        gsp("m", "z", "s", "t")
    )
}

pub fn val_candexp_iota_genrec2() -> String {
    format!(
        "fun (S : KExpr -> Type) (hS : IsCandSet S) (fam : Name) (sig : ListType Nat) (u : Level) (h1 : {}) (h2 : {}) (h3 : {}) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) (genRecName fam sig)) (OptionType.none KExpr)) (K : KExpr -> KExpr -> KExpr -> KExpr -> KExpr) (m : KExpr) (hm : whnf_acc m) (z : KExpr) (hz : whnf_acc z) (s : KExpr) (hs : whnf_acc s) (t : KExpr) (ht : whnf_acc t) (hfire : {}) (hfam : {GFAM_TY}) => candExp_iota_spine4 S hS (genRecName fam sig) (ListType.cons Level u (ListType.nil Level)) h1 h2 h3 hdef K m hm z hz s hs t ht hfire hfam",
        ghdead_ty(1),
        ghdead_ty(2),
        ghdead_ty(3),
        gfire_ty()
    )
}

/// A `ListType Nat` of `n` zeros — the signature whose `sigLength` is `n`, and
/// therefore whose `genRecName Name.anonymous` is the reflected atom
/// `kcre_name_n` (`Name.str Name.anonymous kcre_nat_n`).
pub fn sig_of_len(n: usize) -> String {
    let mut t = "(ListType.nil Nat)".to_string();
    for _ in 0..n {
        t = format!("(ListType.cons Nat Nat.zero {t})");
    }
    t
}

pub const TY_R4_GENFRESH_EMPTY: &str =
    "forall (fam : Name) (sig : ListType Nat), GenFresh fam sig DefEnv.empty";
pub const VAL_R4_GENFRESH_EMPTY: &str = "fun (fam : Name) (sig : ListType Nat) => GenFresh.mk fam sig DefEnv.empty (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (j : Nat) (_ : Lt j (sigLength sig)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType KExpr) (OptionType.none KExpr))";

pub fn ty_r4_genrecname_aliases_delta_head() -> String {
    format!(
        "Eq Name (genRecName Name.anonymous {}) kcre_witness_delta_head",
        sig_of_len(118)
    )
}
pub const VAL_R4_GENRECNAME_ALIASES_DELTA_HEAD: &str = "Eq.refl Name kcre_witness_delta_head";

pub fn ty_r4_genrechead_delta_live() -> String {
    format!(
        "delta_step (red_def the_red_env) (KExpr.const (genRecName Name.anonymous {}) (ListType.nil Level)) kcre_witness_delta_value",
        sig_of_len(118)
    )
}
pub const VAL_R4_GENRECHEAD_DELTA_LIVE: &str = "the_red_env_delta_nonvacuous";

pub fn ty_r4_genrecname_aliases_natrec() -> String {
    format!(
        "Eq Name (genRecName Name.anonymous {}) kcre_name_27",
        sig_of_len(27)
    )
}
pub const VAL_R4_GENRECNAME_ALIASES_NATREC: &str = "Eq.refl Name kcre_name_27";

pub fn ty_r4_genrecc_iota_fires_natrec() -> String {
    let head = format!("(genRecC Name.anonymous {} u)", sig_of_len(27));
    let mut spine = head;
    for a in ["x1", "x2", "x3"] {
        spine = ap(&spine, a);
    }
    spine = ap(&spine, NZERO);
    format!(
        "forall (u : Level) (x1 : KExpr) (x2 : KExpr) (x3 : KExpr), iota_step (red_rec the_red_env) {spine} {}",
        zcontract("x1", "x2", "x3")
    )
}

pub fn val_r4_genrecc_iota_fires_natrec() -> String {
    format!(
        "fun (u : Level) (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) => Eq.refl (OptionType KExpr) (OptionType.some KExpr {})",
        zcontract("x1", "x2", "x3")
    )
}

// ================================================================
// Group F — the §6 discriminating witnesses and the necessity guards.
// ================================================================

pub const TY_BETASTAR_CONST_COLLAPSE: &str = "forall (c : Name) (us : ListType Level) (b2 : KExpr), betaStar (KExpr.const c us) b2 -> Eq KExpr b2 (KExpr.const c us)";
pub const VAL_BETASTAR_CONST_COLLAPSE: &str = "fun (c : Name) (us : ListType Level) (b2 : KExpr) (h : betaStar (KExpr.const c us) b2) => betaStar.rec (fun (qs : KExpr) (qt : KExpr) (_ : betaStar qs qt) => Eq KExpr qs (KExpr.const c us) -> Eq KExpr qt (KExpr.const c us)) (fun (qe : KExpr) (heq : Eq KExpr qe (KExpr.const c us)) => heq) (fun (qe : KExpr) (qe2 : KExpr) (qe3 : KExpr) (qstep : beta_reduces qe qe2) (_qrest : betaStar qe2 qe3) (_qih : Eq KExpr qe2 (KExpr.const c us) -> Eq KExpr qe3 (KExpr.const c us)) (heq : Eq KExpr qe (KExpr.const c us)) => Empty.rec (fun (_ : Empty) => Eq KExpr qe3 (KExpr.const c us)) (r2_const_no_beta_reduces c us qe2 Empty (Eq.rec KExpr qe (fun (qx : KExpr) (_ : Eq KExpr qe qx) => beta_reduces qx qe2) qstep (KExpr.const c us) heq))) (KExpr.const c us) b2 h (Eq.refl KExpr (KExpr.const c us))";

pub const TY_R4_DEADCONST_ACC: &str = "forall (c : Name) (us : ListType Level), Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.const c us)) (OptionType.none KExpr) -> whnf_acc (KExpr.const c us)";
pub const VAL_R4_DEADCONST_ACC: &str = "fun (c : Name) (us : ListType Level) (hd : Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.const c us)) (OptionType.none KExpr)) => whnf_acc.intro (KExpr.const c us) (fun (e2 : KExpr) (hs : whnf_step (KExpr.const c us) e2) => constRedex_whnf_inv c us e2 (whnf_acc e2) hs (fun (hdl : delta_step (red_def the_red_env) (KExpr.const c us) e2) => option_none_ne_some_type KExpr e2 (whnf_acc e2) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def the_red_env) (KExpr.const c us)) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.const c us)) (OptionType.none KExpr) hd) hdl)))";

pub const TY_R4_CONSTAPP1_INERT_ACC: &str = "forall (c : Name) (us : ListType Level) (a : KExpr), Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.app (KExpr.const c us) a)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) (KExpr.app (KExpr.const c us) a)) (OptionType.none KExpr) -> (forall (a2 : KExpr) (C : Type), beta_reduces a a2 -> C) -> whnf_acc (KExpr.app (KExpr.const c us) a)";

pub fn val_r4_constapp1_inert_acc() -> String {
    let r = "(KExpr.app (KExpr.const c us) a)";
    format!(
        "fun (c : Name) (us : ListType Level) (a : KExpr) (hdn : Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) {r}) (OptionType.none KExpr)) (hin : Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) {r}) (OptionType.none KExpr)) (hno : forall (a2 : KExpr) (C : Type), beta_reduces a a2 -> C) => whnf_acc.intro {r} (fun (e2 : KExpr) (hs : whnf_step {r} e2) => constApp1_whnf_inv c us a e2 (whnf_acc e2) hs (fun (qy : KExpr) (hy : beta_reduces a qy) (_heq : Eq KExpr e2 (KExpr.app (KExpr.const c us) qy)) => hno qy (whnf_acc e2) hy) (fun (hio : iota_reduces {r} e2) => option_none_ne_some_type KExpr e2 (whnf_acc e2) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct (red_rec the_red_env) {r}) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) {r}) (OptionType.none KExpr) hin) (iota_reduces_to_step {r} e2 hio))) (fun (hdl : delta_step (red_def the_red_env) {r} e2) => option_none_ne_some_type KExpr e2 (whnf_acc e2) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def the_red_env) {r}) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) {r}) (OptionType.none KExpr) hdn) hdl)))"
    )
}

pub fn ty_succzero_whnf_acc() -> String {
    format!("whnf_acc {}", ap(NSUCC, NZERO))
}

pub fn val_succzero_whnf_acc() -> String {
    format!(
        "r4_constApp1_inert_acc kcre_name_10 (ListType.nil Level) {NZERO} (natSuccApp_delta_none {NZERO}) (natSuccApp_iota_none {NZERO}) (fun (a2 : KExpr) (C : Type) (hb : beta_reduces {NZERO} a2) => r2_const_no_beta_reduces kcre_name_18 (ListType.nil Level) a2 C hb)"
    )
}

/// The MAJOR's accessibility is forced by the redex's: every beta step of
/// `app Nat.succ n` lifts through two `app_right` congruences to a step of the
/// whole spine, and `succApp_whnf_inv` says those are the only steps it has.
pub fn ty_natrecs_major_acc_necessary() -> String {
    format!(
        "forall (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (n : KExpr), whnf_acc {} -> whnf_acc {}",
        sredex("x1", "x2", "x3", "n"),
        ap(NSUCC, "n")
    )
}

pub fn val_natrecs_major_acc_necessary() -> String {
    let sp3 = sp(&["x1", "x2", "x3"]);
    let r0 = sredex("x1", "x2", "x3", "n0");
    let r2 = sredex("x1", "x2", "x3", "n2");
    let mn0 = ap(NSUCC, "n0");
    let mn2 = ap(NSUCC, "n2");
    let step = format!(
        "(Eq.substType KExpr (fun (qz : KExpr) => whnf_step qz {r2}) {r0} qe0 (Eq.symm KExpr qe0 {r0} heq) (whnf_step.beta {r0} {r2} (beta_reduces.app_right {sp3} {mn0} {mn2} (beta_reduces.app_right {NSUCC} n0 n2 hb))))"
    );
    format!(
        "fun (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (n : KExpr) (hacc : whnf_acc {}) => whnf_acc.rec (fun (qe : KExpr) (_ : whnf_acc qe) => forall (n0 : KExpr), Eq KExpr qe {r0} -> whnf_acc {mn0}) (fun (qe0 : KExpr) (_qsteps : forall (qw : KExpr), whnf_step qe0 qw -> whnf_acc qw) (qih : forall (qw : KExpr), whnf_step qe0 qw -> forall (n0 : KExpr), Eq KExpr qw {r0} -> whnf_acc {mn0}) (n0 : KExpr) (heq : Eq KExpr qe0 {r0}) => whnf_acc.intro {mn0} (fun (qw : KExpr) (hw : whnf_step {mn0} qw) => succApp_whnf_inv n0 qw (whnf_acc qw) hw (fun (n2 : KExpr) (hb : beta_reduces n0 n2) (heqw : Eq KExpr qw {mn2}) => Eq.substType KExpr (fun (qv : KExpr) => whnf_acc qv) {mn2} qw (Eq.symm KExpr qw {mn2} heqw) (qih {r2} {step} n2 (Eq.refl KExpr {r2}))))) {} hacc n (Eq.refl KExpr {})",
        sredex("x1", "x2", "x3", "n"),
        sredex("x1", "x2", "x3", "n"),
        sredex("x1", "x2", "x3", "n")
    )
}

/// SN of the successor redex FORCES SN of the successor contractum — so no
/// engine variant may drop the family premise (R3's `natRecZ_...` at the other
/// rule).
pub fn ty_natrecs_contract_acc_necessary() -> String {
    format!(
        "forall (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (n : KExpr), whnf_acc {} -> whnf_acc {}",
        sredex("x1", "x2", "x3", "n"),
        scontract("x1", "x2", "x3", "n")
    )
}

pub fn val_natrecs_contract_acc_necessary() -> String {
    let r = sredex("x1", "x2", "x3", "n");
    let c = scontract("x1", "x2", "x3", "n");
    format!(
        "fun (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (n : KExpr) (hacc : whnf_acc {r}) => whnfAcc_inv_step {r} hacc {c} (whnf_step.beta {r} {c} (beta_reduces.iota {r} {c} (iota_step_to_reduces {r} {c} (natRecS_iota_fires x1 x2 x3 n))))"
    )
}

/// One CONCRETE run of the successor engine at the numeral `succ zero`.
pub fn ty_natrecs_engine_concrete() -> String {
    let b0 = "(KExpr.bvar Nat.zero)";
    format!(
        "whnf_acc {} -> whnf_acc {}",
        scontract(b0, b0, b0, NZERO),
        sredex(b0, b0, b0, NZERO)
    )
}

pub fn val_natrecs_engine_concrete() -> String {
    let b0 = "(KExpr.bvar Nat.zero)";
    let collapse_bvar =
        |v: &str| format!("(Eq.symm KExpr {v} {b0} (betaStar_bvar_collapse Nat.zero {v} h{v}))");
    let collapse_zero = format!(
        "(Eq.symm KExpr b4 {NZERO} (betaStar_const_collapse kcre_name_18 (ListType.nil Level) b4 hb4))"
    );
    let s0 = format!(
        "(Eq.substType KExpr (fun (qw : KExpr) => whnf_acc {}) {NZERO} b4 {collapse_zero} hc)",
        scontract(b0, b0, b0, "qw")
    );
    let s1 = format!(
        "(Eq.substType KExpr (fun (qw : KExpr) => whnf_acc {}) {b0} b3 {} {s0})",
        scontract(b0, b0, "qw", "b4"),
        collapse_bvar("b3")
    );
    let s2 = format!(
        "(Eq.substType KExpr (fun (qw : KExpr) => whnf_acc {}) {b0} b2 {} {s1})",
        scontract(b0, "qw", "b3", "b4"),
        collapse_bvar("b2")
    );
    let s3 = format!(
        "(Eq.substType KExpr (fun (qw : KExpr) => whnf_acc {}) {b0} b1 {} {s2})",
        scontract("qw", "b2", "b3", "b4"),
        collapse_bvar("b1")
    );
    format!(
        "fun (hc : whnf_acc {}) => candExp_iota_natrec_succ (fun (e : KExpr) => whnf_acc e) isCand_whnfAcc {b0} cand_var_witness {b0} cand_var_witness {b0} cand_var_witness {NZERO} succZero_whnf_acc (fun (b1 : KExpr) (hb1 : betaStar {b0} b1) (b2 : KExpr) (hb2 : betaStar {b0} b2) (b3 : KExpr) (hb3 : betaStar {b0} b3) (b4 : KExpr) (hb4 : betaStar {NZERO} b4) => {s3})",
        scontract(b0, b0, b0, NZERO)
    )
}

/// R3's zero-major engine STATEMENT, re-derived through the generic engine at
/// the LIVE reflected `Nat.rec` — the non-degeneracy cross-check for
/// `candExp_iota_spine4`.
fn zfam(a1: &str, a2: &str, a3: &str) -> String {
    format!(
        "forall (b1 : KExpr), betaStar {a1} b1 -> forall (b2 : KExpr), betaStar {a2} b2 -> forall (b3 : KExpr), betaStar {a3} b3 -> S {}",
        zcontract("b1", "b2", "b3")
    )
}

pub fn ty_r4_natrecz_via_spine4() -> String {
    format!(
        "forall (S : KExpr -> Type), IsCandSet S -> forall (mot : KExpr), whnf_acc mot -> forall (m0 : KExpr), whnf_acc m0 -> forall (m1 : KExpr), whnf_acc m1 -> ({}) -> S {}",
        zfam("mot", "m0", "m1"),
        sp(&["mot", "m0", "m1", NZERO])
    )
}

pub fn val_r4_natrecz_via_spine4() -> String {
    let kfam = format!(
        "(fun (b1 : KExpr) (b2 : KExpr) (b3 : KExpr) (b4 : KExpr) => {})",
        zcontract("b1", "b2", "b3")
    );
    let binders = "(b1 : KExpr) (b2 : KExpr) (b3 : KExpr) (b4 : KExpr)";
    let prem = format!("(p1 : betaStar mot b1) (p2 : betaStar m0 b2) (p3 : betaStar m1 b3) (p4 : betaStar {NZERO} b4)");
    let collapse = format!("(Eq.symm KExpr b4 {NZERO} (betaStar_const_collapse kcre_name_18 (ListType.nil Level) b4 p4))");
    let fire = format!(
        "(fun {binders} {prem} => Eq.substType KExpr (fun (qw : KExpr) => iota_reduces {} {}) {NZERO} b4 {collapse} (iota_step_to_reduces {} {} (natRecZ_iota_fires b1 b2 b3)))",
        sp(&["b1", "b2", "b3", "qw"]),
        zcontract("b1", "b2", "b3"),
        sp(&["b1", "b2", "b3", NZERO]),
        zcontract("b1", "b2", "b3")
    );
    let fam = format!("(fun {binders} {prem} => hfam0 b1 p1 b2 p2 b3 p3)");
    format!(
        "fun (S : KExpr -> Type) (hS : IsCandSet S) (mot : KExpr) (hmot : whnf_acc mot) (m0 : KExpr) (hm0 : whnf_acc m0) (m1 : KExpr) (hm1 : whnf_acc m1) (hfam0 : {}) => candExp_iota_spine4 S hS kcre_name_27 (ListType.nil Level) natRecSpine1_iota_none natRecSpine2_iota_none natRecSpine3_iota_none natRec_defval_none {kfam} mot hmot m0 hm0 m1 hm1 {NZERO} (r4_deadConst_acc kcre_name_18 (ListType.nil Level) (Eq.refl (OptionType KExpr) (OptionType.none KExpr))) {fire} {fam}",
        zfam("mot", "m0", "m1")
    )
}

// ==== R4 SOURCES END ====

impl Specification {
    /// R4: the generic four-argument const-spine iota engine, the successor
    /// `Nat.rec` instance, and the generic-recursor direction with its
    /// obstruction witnesses.
    pub(super) fn add_candmodel_construct_r4(&mut self) -> Result<(), SpecError> {
        let mut add = |name: &str, ty: String, val: String, deps: &[&str], desc: &str| {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: ty,
                value_src: Some(val),
                is_axiom: false,
                description: desc.to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(
                    deps.iter()
                        .map(|d| (*d).to_string())
                        .collect::<HashSet<_>>(),
                ),
                axiom_deps: HashSet::new(),
            })
        };

        // --- Group A: the generic const-spine machinery ---
        add(
            "constSpine4_delta_none",
            ty_const_spine4_delta_none(),
            val_const_spine4_delta_none(),
            &["delta_reduct", "defval_for", "opt_bind", "Eq.cong"],
            "δ-deadness of a FOUR-ARGUMENT const spine from δ-deadness of its head alone. \
             delta_reduct looks the definition name up at kapp_fn (the spine head) and \
             re-applies kapp_args, so `defval_for env c = none` propagates through ONE Eq.cong \
             under (fun o => opt_bind o (fun v => some (apply_spine args v))) — whose value at \
             none computes to none. No case analysis, hence no Type-valued eliminator anywhere \
             near the Prop-valued Eq (the measured 2026-08-24 Prop/Type trap). Generic in the \
             head name, the levels and all four arguments. Zero axiom_deps.",
        )?;
        for n in 2usize..=4 {
            let live = if n == 4 {
                "LIVE (delivered to the kIota continuation)"
            } else {
                "refuted from the caller's deadness hypothesis"
            };
            add(
                &format!("constSpine{n}_beta_inv"),
                ty_const_spine_beta_inv(n),
                val_const_spine_beta_inv(n),
                &[
                    "beta_reduces.rec",
                    "constApp1_beta_inv",
                    "r2_const_no_beta_reduces",
                    "app_inj_fst",
                    "app_inj_snd",
                ],
                &format!(
                    "Complete beta_reduces reduct classification of an arity-{n} spine at an \
                     ARBITRARY const head, in CPS: one continuation per argument slot, and the \
                     spine's own iota arm {live}. Generalizes R3's natRecSpine{n}_beta_inv from \
                     the concrete kcre_name_27 head to any (c, us) — which is what lets ONE \
                     engine serve both the Nat.rec successor rule and the generic-signature \
                     recursor. The ι-deadness of the SHORTER spines cannot be computed for a \
                     generic head (the real env's metadata at that name is unknown), so it \
                     enters as the hypotheses h1..h{n}; at the Nat.rec head each is one Eq.refl. \
                     15-arm beta_reduces.rec on R3's shared scaffold, every recursive structural \
                     minor binding its beta_reduces premise before its IH. Zero axiom_deps."
                ),
            )?;
        }
        add(
            "constSpine4_whnf_inv",
            ty_const_spine4_whnf_inv(),
            val_const_spine4_whnf_inv(),
            &["constSpine4_beta_inv", "whnf_step", "delta_reduces_to_step"],
            "The whnf_step classification of a four-argument spine at an arbitrary const head: \
             the four argument continuations and the LIVE ι leg of constSpine4_beta_inv, plus a \
             LIVE δ leg. R3's Nat.rec version could refute δ by rfl (Nat.rec has no defval_for \
             entry); a GENERIC head cannot — the real env may define it — so δ is delivered to a \
             continuation and the engine refutes it from its own hdef premise. Zero axiom_deps.",
        )?;
        add(
            "candExp_iota_spine4",
            ty_candexp_iota_spine4(),
            val_candexp_iota_spine4(),
            &[
                "IsCandSet",
                "isCandSet_cr3",
                "constSpine4_whnf_inv",
                "constSpine4_delta_none",
                "betaStar",
                "whnf_acc.rec",
                "option_some_inj",
            ],
            "THE R4 ENGINE: any candidate set absorbs a four-argument const spine that ι-fires \
             to a contractum FAMILY. Premises: ι-deadness of the head below arity 4 and \
             δ-deadness of the head in the real reflected env, SN of all four arguments, the \
             fire `iota_reduces (spine b1..b4) (K b1..b4)` along every betaStar-development of \
             the arguments, and membership of `K b1..b4` for those same developments. cr3 \
             applies because an application is Neutral; FOUR plain whnf_acc.rec layers cover the \
             four congruence legs, the ι leg consumes the fire through option_some_inj, and the \
             δ leg dies by constSpine4_delta_none. Generic in the head const, the levels, the \
             contractum family and all four arguments — R3's per-rule engine, done once. \
             Model-independent (per-set, any IsCandSet). Zero axiom_deps.",
        )?;

        // --- Group C: the real-env reduction facts ---
        for k in 1usize..=3 {
            add(
                &format!("natRecSpine{k}_iota_none"),
                ty_natrec_spine_iota_none(k),
                val_natrec_spine_iota_none(k),
                &["iota_reduct", "the_red_env"],
                &format!(
                    "Refl over the real env: an arity-{k} Nat.rec spine does NOT ι-fire — the \
                     reflected Nat.rec metadata puts the major at index 3, so below arity 4 the \
                     major slot lookup is none. R3 proved this inline inside its inversions; the \
                     generic engine needs it as a first-class term to discharge \
                     constSpine{k}_beta_inv's deadness hypothesis at the Nat.rec head. \
                     Zero axiom_deps."
                ),
            )?;
        }
        add(
            "natRec_defval_none",
            TY_NATREC_DEFVAL_NONE.to_string(),
            VAL_NATREC_DEFVAL_NONE.to_string(),
            &["defval_for", "the_red_env"],
            "Refl over the real env: kcre_name_27 (Nat.rec) has no defval_for entry, so the \
             engine's δ-deadness premise is discharged at the Nat.rec head by computation. The \
             HEAD-level companion of R3's spine-level natRecSpine4_delta_none. Zero axiom_deps.",
        )?;
        add(
            "natSuccApp_iota_none",
            ty_succapp_iota_none(),
            VAL_SUCCAPP_NONE.to_string(),
            &["iota_reduct", "the_red_env"],
            "Refl over the real env: Nat.succ is a CONSTRUCTOR, not a recursor, so \
             recmeta_for finds nothing and a one-argument Nat.succ spine never ι-fires — for \
             EVERY argument. This is what makes the successor major's own reduct set purely \
             congruential. Zero axiom_deps.",
        )?;
        add(
            "natSuccApp_delta_none",
            ty_succapp_delta_none(),
            VAL_SUCCAPP_NONE.to_string(),
            &["delta_reduct", "the_red_env"],
            "Refl over the real env: Nat.succ has no defval_for entry, so a Nat.succ spine \
             never δ-unfolds. Together with natSuccApp_iota_none this is the complete deadness \
             of the successor major's head, and it is exactly why whnf_acc of the MAJOR (rather \
             than of the numeral) is the premise whose necessity can be proved. Zero axiom_deps.",
        )?;

        // --- Group D: the successor major ---
        add(
            "succApp_whnf_inv",
            ty_succapp_whnf_inv(),
            val_succapp_whnf_inv(),
            &[
                "constApp1_whnf_inv",
                "natSuccApp_iota_none",
                "natSuccApp_delta_none",
            ],
            "The complete whnf_step classification of the successor major app Nat.succ n: the \
             ONLY steps are argument beta steps. R3's generic one-argument const-spine inverter \
             with both of its live legs refuted by computation over the real env. \
             Zero axiom_deps.",
        )?;
        add(
            "succApp_betaStar_shape",
            ty_succapp_betastar_shape(),
            val_succapp_betastar_shape(),
            &["betaStar.rec", "constApp1_beta_inv", "natSuccApp_iota_none"],
            "Development shape of the successor major: every betaStar-development of \
             app Nat.succ n is app Nat.succ n2 for a development n2 of n. This is what lets the \
             successor ι fire survive the engine's fourth Acc layer — the engine's fire premise \
             quantifies over developments of the MAJOR, and the fire is only known at succ-shaped \
             majors. CPS-stated at a (C : Type) so it can be instantiated at the Type-valued \
             iota_reduces; instantiating it at the Prop-valued iota_step would hit the measured \
             non-cumulative universe rejection. Zero axiom_deps.",
        )?;
        add(
            "candExp_iota_natrec_succ",
            ty_candexp_iota_natrec_succ(),
            val_candexp_iota_natrec_succ(),
            &[
                "candExp_iota_spine4",
                "natRecS_iota_fires",
                "succApp_betaStar_shape",
                "natRecSpine1_iota_none",
                "natRec_defval_none",
            ],
            "THE SUCCESSOR-MAJOR ι ENGINE (R4-A, the fourth Acc layer R3 deferred): a candidate \
             set absorbs a four-argument Nat.rec spine whose major is app Nat.succ n, given SN \
             of the motive, both minors and THE MAJOR, and membership of the successor \
             contractum along every development. An instantiation of candExp_iota_spine4 at \
             c := kcre_name_27 with contractum family \
             K b1 b2 b3 b4 = apply_spine (kapp_args b4) (rhsSucc b1 b2 b3) — which at \
             b4 = app Nat.succ n2 computes to the real successor contractum, so the engine's \
             generic ι continuation consumes R3's natRecS_iota_fires unchanged. The major's own \
             reducts are handled by the fourth Acc layer plus succApp_betaStar_shape. \
             Zero axiom_deps.",
        )?;

        // --- Group E: the generic-recursor direction + the obstruction ---
        add(
            "candExp_iota_genRec2",
            ty_candexp_iota_genrec2(),
            val_candexp_iota_genrec2(),
            &["candExp_iota_spine4", "genRecApp", "genRecC", "genRecName"],
            "THE GENERIC-RECURSOR DIRECTION (R4-B): redRecGen's CONCLUSION for a \
             candidate-set-valued Red, generic in the family name, the signature and the \
             universe, at two-minor signatures. genRecApp fam sig u m [z,s] t IS a four-argument \
             const spine at head genRecC fam sig u by rfl (apply_spine + list_append compute — \
             the same rfl that makes genRecApp_nat hold), so this is a one-line instantiation of \
             candExp_iota_spine4. WHAT IT IS NOT: a discharge of the redRecGen FIELD. The field \
             supplies GenFresh fam sig denv and GenRecEnvOK fam sig u renv over denv/renv it \
             QUANTIFIES, while whnf_step is pinned to the_red_env; this engine instead takes \
             those conditions' real-env computational content (hdef at red_def the_red_env, \
             h1..h3 and the fire at red_rec the_red_env). The gap is the quantifier placement, \
             not a missing lemma — see r4_genFresh_empty and the two aliasing witnesses. \
             Zero axiom_deps.",
        )?;
        add(
            "r4_genFresh_empty",
            TY_R4_GENFRESH_EMPTY.to_string(),
            VAL_R4_GENFRESH_EMPTY.to_string(),
            &["GenFresh", "defval_for", "DefEnv.empty"],
            "OBSTRUCTION WITNESS 1 (why redRecGen's freshness premise carries no real-env \
             information): GenFresh fam sig DefEnv.empty holds for EVERY family name and EVERY \
             signature — all three fields are Eq.refl, since defval_for DefEnv.empty is none by \
             computation. redRecGen quantifies denv, so a prover may always take denv := empty; \
             the premise therefore constrains nothing about red_def the_red_env, which is the \
             env whnf_step actually uses. Zero axiom_deps.",
        )?;
        add(
            "r4_genRecName_aliases_deltaHead",
            ty_r4_genrecname_aliases_delta_head(),
            VAL_R4_GENRECNAME_ALIASES_DELTA_HEAD.to_string(),
            &["genRecName", "sigLength", "kcre_witness_delta_head"],
            "OBSTRUCTION WITNESS 2a (the schema's namespace is NOT disjoint from the reflected \
             kernel's): genRecName fam sig is Name.str fam (sigLength sig) and every reflected \
             kernel name is Name.str Name.anonymous k, so at fam := Name.anonymous and a \
             118-element signature the schema's recursor name IS kcre_witness_delta_head — the \
             very constant the Guard-4 δ witness unfolds. One Eq.refl; no hand-copied literal, \
             so it fails CLOSED if the reflection is regenerated. Zero axiom_deps.",
        )?;
        add(
            "r4_genRecHead_delta_live",
            ty_r4_genrechead_delta_live(),
            VAL_R4_GENRECHEAD_DELTA_LIVE.to_string(),
            &[
                "the_red_env_delta_nonvacuous",
                "r4_genRecName_aliases_deltaHead",
            ],
            "OBSTRUCTION WITNESS 2b (the aliasing is not cosmetic — the real env REDUCES there): \
             the schema recursor constant of the family witnessed by \
             r4_genRecName_aliases_deltaHead δ-unfolds in red_def the_red_env, proved by handing \
             the goal the landed Guard-4 witness verbatim (the two names are definitionally \
             equal). So a (fam, sig) that satisfies redRecGen's GenFresh premise at the \
             quantified denv can have a recursor constant that is δ-LIVE in the fixed env: cr3's \
             δ leg at its spine then has a reduct about which `Red T contractum` says nothing. \
             That is the exact clause that fails. Zero axiom_deps.",
        )?;
        add(
            "r4_genRecName_aliases_natRec",
            ty_r4_genrecname_aliases_natrec(),
            VAL_R4_GENRECNAME_ALIASES_NATREC.to_string(),
            &["genRecName", "sigLength"],
            "OBSTRUCTION WITNESS 3a (the ι side of the same aliasing): at fam := Name.anonymous \
             and a 27-element signature, genRecName IS kcre_name_27 — the live reflected \
             Nat.rec. One Eq.refl. Zero axiom_deps.",
        )?;
        add(
            "r4_genRecC_iota_fires_natRec",
            ty_r4_genrecc_iota_fires_natrec(),
            val_r4_genrecc_iota_fires_natrec(),
            &[
                "genRecC",
                "iota_step",
                "the_red_env",
                "r4_genRecName_aliases_natRec",
            ],
            "OBSTRUCTION WITNESS 3b: the aliased schema recursor constant genuinely FIRES the \
             REAL Nat.rec rule in red_rec the_red_env — a four-argument spine at that head with \
             a Nat.zero major reduces to the real zero-rule contractum (ι ignores the level \
             list, so the schema's [u] annotation changes nothing). The schema's own \
             GenRecContract for that family would demand genRecRhs fam sig u instead. So \
             GenRecEnvOK at the QUANTIFIED renv is satisfiable (genREnv_ok) while the same \
             condition at red_rec the_red_env is false for that family: the two envs disagree, \
             and redRecGen's premises are about the wrong one. Zero axiom_deps.",
        )?;

        // --- Group F: witnesses and necessity guards ---
        add(
            "betaStar_const_collapse",
            TY_BETASTAR_CONST_COLLAPSE.to_string(),
            VAL_BETASTAR_CONST_COLLAPSE.to_string(),
            &["betaStar.rec", "r2_const_no_beta_reduces", "Empty.rec"],
            "A betaStar development of a bare const is the const itself (the const analogue of \
             R1's betaStar_bvar_collapse), which is what collapses the engine's development- \
             quantified premises at a canonical constructor major. NOTE the Empty.rec detour: \
             r2_const_no_beta_reduces's C is (C : Type) and the goal Eq lives in Prop, so the \
             absurdity must land in Empty first — the same non-cumulative universe trap R1 \
             recorded. Zero axiom_deps.",
        )?;
        add(
            "r4_deadConst_acc",
            TY_R4_DEADCONST_ACC.to_string(),
            VAL_R4_DEADCONST_ACC.to_string(),
            &["constRedex_whnf_inv", "whnf_acc.intro"],
            "A constant whose δ reduct is none is strongly normalizing: R2's bare-const whnf \
             inverter has exactly one live leg, and it is refuted by the premise. The \
             substitution-bundle counterpart of acc_wtype's whnfAcc_const (which is Full-bundle \
             only). Zero axiom_deps.",
        )?;
        add(
            "r4_constApp1_inert_acc",
            TY_R4_CONSTAPP1_INERT_ACC.to_string(),
            val_r4_constapp1_inert_acc(),
            &["constApp1_whnf_inv", "whnf_acc.intro"],
            "A one-argument const spine is strongly normalizing when all three of its reduct \
             legs are dead: δ and ι refuted by computation over the real env, and the argument \
             admitting no beta step at all. No induction is needed precisely because the third \
             premise makes the congruence leg vacuous — the shape that holds at a constructor \
             applied to a constructor. Zero axiom_deps.",
        )?;
        add(
            "succZero_whnf_acc",
            ty_succzero_whnf_acc(),
            val_succzero_whnf_acc(),
            &[
                "r4_constApp1_inert_acc",
                "natSuccApp_delta_none",
                "natSuccApp_iota_none",
                "r2_const_no_beta_reduces",
            ],
            "The numeral `Nat.succ Nat.zero` is strongly normalizing, by inertness of both \
             reflected constructors. This is the successor engine's major-accessibility premise \
             at the concrete numeral, discharged rather than assumed. Zero axiom_deps.",
        )?;
        add(
            "natRecS_major_acc_necessary",
            ty_natrecs_major_acc_necessary(),
            val_natrecs_major_acc_necessary(),
            &["succApp_whnf_inv", "whnf_acc.rec", "beta_reduces.app_right"],
            "PREMISE-NECESSITY GUARD for R4's added premise: SN of the successor redex FORCES SN \
             of the MAJOR, so candExp_iota_natrec_succ's whnf_acc (app Nat.succ n) may not be \
             dropped. Proved by Acc induction on the redex with a shape-carrying motive: every \
             whnf_step of the major is an argument beta step (succApp_whnf_inv), and each lifts \
             through two app_right congruences to a step of the whole spine. MEASURED SCOPE \
             NOTE — the same statement with `whnf_acc n` in place of \
             `whnf_acc (app Nat.succ n)` is NOT reachable by this route: delta_reduces has no \
             congruence, so a δ-step of n has no image in the spine's reduct set and the Acc \
             induction has nothing to recurse on. (Its TRUTH turns on δ-acyclicity of the \
             reflected def-env — design build item B3 — which R4 neither settles nor needs.) \
             That is why the engine assumes the MAJOR's accessibility, which is also what the \
             CandModel redRec* fields assume. Zero axiom_deps.",
        )?;
        add(
            "natRecS_contract_acc_necessary",
            ty_natrecs_contract_acc_necessary(),
            val_natrecs_contract_acc_necessary(),
            &[
                "natRecS_iota_fires",
                "whnfAcc_inv_step",
                "iota_step_to_reduces",
            ],
            "PREMISE-NECESSITY GUARD for the family premise at the successor rule (R3's \
             natRecZ_contract_acc_necessary one rule over): SN of the redex forces SN of the \
             successor contractum, since the ι fire is one whnf_step. Zero axiom_deps.",
        )?;
        add(
            "natRecS_engine_concrete",
            ty_natrecs_engine_concrete(),
            val_natrecs_engine_concrete(),
            &[
                "candExp_iota_natrec_succ",
                "isCand_whnfAcc",
                "cand_var_witness",
                "succZero_whnf_acc",
                "betaStar_const_collapse",
                "betaStar_bvar_collapse",
            ],
            "§6.1 POSITIVE WITNESS: one CONCRETE run of the successor engine at the numeral \
             `succ zero` with (bvar 0) motive and minors. Every premise is discharged — the base \
             candidate set through the interface, argument SN by R0's cand_var_witness, major SN \
             by succZero_whnf_acc, and the four development families collapsed by \
             betaStar_bvar_collapse / betaStar_const_collapse — EXCEPT strong normalization of \
             the successor contractum, which is CARRIED. That hypothesis is honest: the real \
             successor RHS is a four-lambda over reflected annotations whose SN is a \
             fundamental-theorem obligation (design rungs R5/R6), not an R4 brick. \
             Zero axiom_deps.",
        )?;
        add(
            "r4_natrecZ_via_spine4",
            ty_r4_natrecz_via_spine4(),
            val_r4_natrecz_via_spine4(),
            &[
                "candExp_iota_spine4",
                "natRecZ_iota_fires",
                "betaStar_const_collapse",
                "r4_deadConst_acc",
            ],
            "NON-DEGENERACY CROSS-CHECK: R3's candExp_iota_natrec_zero STATEMENT, re-derived \
             through the new generic engine at the LIVE reflected Nat.rec with the constant \
             contractum family K b1 b2 b3 b4 = rhsZero b1 b2 b3. An engine whose ι continuation \
             never consumed a real fire could not produce this, so it discriminates \
             candExp_iota_spine4 against the degenerate shapes §6.1 warns about — and it is the \
             generic engine's only run at a family the real env actually reduces. \
             Zero axiom_deps.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::parse_check;

    /// Every (name, type, value) triple registered by the stage, in
    /// registration order.
    fn theorem_sources() -> Vec<(String, String, String)> {
        let mut v: Vec<(String, String, String)> = vec![(
            "constSpine4_delta_none".to_string(),
            ty_const_spine4_delta_none(),
            val_const_spine4_delta_none(),
        )];
        for n in 2usize..=4 {
            v.push((
                format!("constSpine{n}_beta_inv"),
                ty_const_spine_beta_inv(n),
                val_const_spine_beta_inv(n),
            ));
        }
        v.push((
            "constSpine4_whnf_inv".to_string(),
            ty_const_spine4_whnf_inv(),
            val_const_spine4_whnf_inv(),
        ));
        v.push((
            "candExp_iota_spine4".to_string(),
            ty_candexp_iota_spine4(),
            val_candexp_iota_spine4(),
        ));
        for k in 1usize..=3 {
            v.push((
                format!("natRecSpine{k}_iota_none"),
                ty_natrec_spine_iota_none(k),
                val_natrec_spine_iota_none(k),
            ));
        }
        v.push((
            "natRec_defval_none".to_string(),
            TY_NATREC_DEFVAL_NONE.to_string(),
            VAL_NATREC_DEFVAL_NONE.to_string(),
        ));
        v.push((
            "natSuccApp_iota_none".to_string(),
            ty_succapp_iota_none(),
            VAL_SUCCAPP_NONE.to_string(),
        ));
        v.push((
            "natSuccApp_delta_none".to_string(),
            ty_succapp_delta_none(),
            VAL_SUCCAPP_NONE.to_string(),
        ));
        v.push((
            "succApp_whnf_inv".to_string(),
            ty_succapp_whnf_inv(),
            val_succapp_whnf_inv(),
        ));
        v.push((
            "succApp_betaStar_shape".to_string(),
            ty_succapp_betastar_shape(),
            val_succapp_betastar_shape(),
        ));
        v.push((
            "candExp_iota_natrec_succ".to_string(),
            ty_candexp_iota_natrec_succ(),
            val_candexp_iota_natrec_succ(),
        ));
        v.push((
            "candExp_iota_genRec2".to_string(),
            ty_candexp_iota_genrec2(),
            val_candexp_iota_genrec2(),
        ));
        v.push((
            "r4_genFresh_empty".to_string(),
            TY_R4_GENFRESH_EMPTY.to_string(),
            VAL_R4_GENFRESH_EMPTY.to_string(),
        ));
        v.push((
            "r4_genRecName_aliases_deltaHead".to_string(),
            ty_r4_genrecname_aliases_delta_head(),
            VAL_R4_GENRECNAME_ALIASES_DELTA_HEAD.to_string(),
        ));
        v.push((
            "r4_genRecHead_delta_live".to_string(),
            ty_r4_genrechead_delta_live(),
            VAL_R4_GENRECHEAD_DELTA_LIVE.to_string(),
        ));
        v.push((
            "r4_genRecName_aliases_natRec".to_string(),
            ty_r4_genrecname_aliases_natrec(),
            VAL_R4_GENRECNAME_ALIASES_NATREC.to_string(),
        ));
        v.push((
            "r4_genRecC_iota_fires_natRec".to_string(),
            ty_r4_genrecc_iota_fires_natrec(),
            val_r4_genrecc_iota_fires_natrec(),
        ));
        v.push((
            "betaStar_const_collapse".to_string(),
            TY_BETASTAR_CONST_COLLAPSE.to_string(),
            VAL_BETASTAR_CONST_COLLAPSE.to_string(),
        ));
        v.push((
            "r4_deadConst_acc".to_string(),
            TY_R4_DEADCONST_ACC.to_string(),
            VAL_R4_DEADCONST_ACC.to_string(),
        ));
        v.push((
            "r4_constApp1_inert_acc".to_string(),
            TY_R4_CONSTAPP1_INERT_ACC.to_string(),
            val_r4_constapp1_inert_acc(),
        ));
        v.push((
            "succZero_whnf_acc".to_string(),
            ty_succzero_whnf_acc(),
            val_succzero_whnf_acc(),
        ));
        v.push((
            "natRecS_major_acc_necessary".to_string(),
            ty_natrecs_major_acc_necessary(),
            val_natrecs_major_acc_necessary(),
        ));
        v.push((
            "natRecS_contract_acc_necessary".to_string(),
            ty_natrecs_contract_acc_necessary(),
            val_natrecs_contract_acc_necessary(),
        ));
        v.push((
            "natRecS_engine_concrete".to_string(),
            ty_natrecs_engine_concrete(),
            val_natrecs_engine_concrete(),
        ));
        v.push((
            "r4_natrecZ_via_spine4".to_string(),
            ty_r4_natrecz_via_spine4(),
            val_r4_natrecz_via_spine4(),
        ));
        v
    }

    /// Parse-check every generated source — the fast guard for the commonest
    /// failure class (syntax-level assembly mistakes invisible to cargo
    /// check), doubly important here because every inversion is
    /// `format!`-assembled from R3's shared 15-arm scaffold.
    #[test]
    fn test_candmodel_r4_sources_parse() {
        for (name, ty, val) in theorem_sources() {
            let assembled = format!("def {name} : {ty} := {val}");
            parse_check(&assembled)
                .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
        }
    }

    /// PER-STRING paren balance on every source (this guard caught a bug the
    /// parser tolerated on an earlier rung, so it is not redundant with the
    /// parse test).
    #[test]
    fn test_candmodel_r4_sources_paren_balanced() {
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

    /// Skip a run of parenthesised binder groups starting at `i`, returning
    /// (index after the groups, how many groups were skipped).
    fn skip_binder_groups(b: &[char], mut i: usize) -> (usize, usize) {
        let mut n = 0usize;
        loop {
            while i < b.len() && b[i] == ' ' {
                i += 1;
            }
            if i >= b.len() || b[i] != '(' {
                break;
            }
            let mut d = 0i64;
            while i < b.len() {
                if b[i] == '(' {
                    d += 1;
                } else if b[i] == ')' {
                    d -= 1;
                    if d == 0 {
                        i += 1;
                        break;
                    }
                }
                i += 1;
            }
            n += 1;
        }
        while i < b.len() && b[i] == ' ' {
            i += 1;
        }
        (i, n)
    }

    /// STRUCTURAL GUARD, from the first measured assembly bug of this rung: a
    /// `forall` binder run must be terminated by a COMMA, and a `fun` binder
    /// run by `=>`. A missing comma parses as an application in some positions
    /// and only surfaces as an incomprehensible elaboration error, so it is
    /// pinned here rather than left to the parse test.
    #[test]
    fn test_candmodel_r4_binder_runs_terminated() {
        for (name, ty, val) in theorem_sources() {
            for src in [&ty, &val] {
                let b: Vec<char> = src.chars().collect();
                for (kw, close) in [("forall ", ","), ("fun ", "=>")] {
                    let mut from = 0usize;
                    while let Some(rel) = src[from..].find(kw) {
                        let start = from + rel;
                        from = start + 1;
                        let ci = src[..start].chars().count() + kw.chars().count();
                        let (after, groups) = skip_binder_groups(&b, ci);
                        assert!(groups > 0, "{name}: `{kw}` with no parenthesised binder");
                        let tail: String = b[after..(after + 2).min(b.len())].iter().collect();
                        assert!(
                            tail.starts_with(close),
                            "{name}: `{kw}` binder run is not terminated by `{close}` — found \
                             `{tail}` (the measured R4 assembly bug)"
                        );
                    }
                }
            }
        }
    }

    /// Shape guards.
    #[test]
    fn test_candmodel_r4_shape_guards() {
        // (1) ARM-ARITY PIN (R3's measured 2026-08-24 failure): every 15-arm
        // `beta_reduces.rec` must bind the RECURSIVE PREMISE of each recursive
        // minor before its IH — 10 structural minors plus the 2 app
        // congruences; beta/zeta/iota take no such binder.
        for n in 2usize..=4 {
            let v = val_const_spine_beta_inv(n);
            let name = format!("constSpine{n}_beta_inv");
            assert_eq!(
                v.matches("(_qstep : beta_reduces ").count(),
                10,
                "{name}: each of the 10 recursive structural minors must bind its \
                 beta_reduces premise before its IH"
            );
            assert_eq!(
                v.matches("(qstep : beta_reduces ").count(),
                2,
                "{name}: app_left and app_right must bind their beta_reduces premise"
            );
            assert_eq!(
                v.matches("(qio : iota_reduces ").count(),
                1,
                "{name}: the iota minor binds an iota_reduces premise and has no IH"
            );
        }
        // (2) ι is LIVE at arity 4 and refuted FROM A HYPOTHESIS below it —
        // never by an Eq.refl, which would silently re-pin the generic head to
        // the concrete Nat.rec.
        for n in 2usize..=3 {
            let v = val_const_spine_beta_inv(n);
            assert!(
                v.contains(&format!("(h{n} x1")),
                "constSpine{n}_beta_inv must kill its own iota arm from hypothesis h{n}"
            );
            assert!(
                !v.contains("kIota"),
                "constSpine{n}_beta_inv has no live iota continuation"
            );
        }
        let v4 = val_const_spine_beta_inv(4);
        assert!(
            v4.contains("kIota (Eq.substType"),
            "constSpine4_beta_inv must pass its LIVE iota arm to the continuation"
        );
        assert!(
            !v4.contains("Eq.refl (OptionType KExpr) (OptionType.none KExpr)"),
            "no generic-head inversion may refute a reduct by computing the real env"
        );
        // (3) The engine really is FOUR Acc layers and consumes the fire and
        // the delta refutation exactly once each.
        let eng = val_candexp_iota_spine4();
        assert_eq!(
            eng.matches("whnf_acc.rec").count(),
            4,
            "the engine must be a quadruple Acc nesting (three arguments + the major)"
        );
        assert_eq!(
            eng.matches("constSpine4_delta_none").count(),
            1,
            "the engine must refute its delta leg exactly once, from hdef"
        );
        assert_eq!(
            eng.matches("option_some_inj").count(),
            1,
            "the engine must consume the fire through option_some_inj exactly once"
        );
        // (4) Both directions are INSTANCES of the one engine, not copies.
        for (name, v) in [
            ("candExp_iota_natrec_succ", val_candexp_iota_natrec_succ()),
            ("candExp_iota_genRec2", val_candexp_iota_genrec2()),
            ("r4_natrecZ_via_spine4", val_r4_natrecz_via_spine4()),
        ] {
            assert!(
                v.contains("candExp_iota_spine4"),
                "{name} must be an instantiation of the shared engine"
            );
            assert!(
                !v.contains("whnf_acc.rec"),
                "{name} must not re-run the Acc nesting"
            );
        }
        // (5) The successor instance consumes R3's fire and the shape lemma;
        // the zero cross-check consumes R3's OTHER fire. Neither may refute a
        // fire — that is the stuck route, and it is R3's.
        let s = val_candexp_iota_natrec_succ();
        assert!(
            s.contains("natRecS_iota_fires") && s.contains("succApp_betaStar_shape"),
            "the successor instance must consume the successor fire through the shape lemma"
        );
        assert!(
            val_r4_natrecz_via_spine4().contains("natRecZ_iota_fires"),
            "the cross-check must consume the ZERO fire"
        );
        // (6) The obstruction witnesses must be aliasing facts about the REAL
        // env, with no hand-copied reflected literal: the delta one reuses the
        // landed Guard-4 witness verbatim, and both name equations are refl.
        assert_eq!(
            VAL_R4_GENRECHEAD_DELTA_LIVE, "the_red_env_delta_nonvacuous",
            "the delta-aliasing witness must BE the landed Guard-4 witness"
        );
        assert!(
            ty_r4_genrecname_aliases_delta_head().contains("kcre_witness_delta_head")
                && ty_r4_genrecname_aliases_natrec().contains("kcre_name_27"),
            "the aliasing statements must name the generated atoms"
        );
        assert_eq!(
            sig_of_len(118).matches("ListType.cons Nat").count(),
            118,
            "the delta-head alias needs sigLength 118 (kcre_name_118)"
        );
        assert_eq!(
            sig_of_len(27).matches("ListType.cons Nat").count(),
            27,
            "the Nat.rec alias needs sigLength 27 (kcre_name_27)"
        );
        // (7) PROP/TYPE PIN (measured 2026-08-24): the spec's Eq is Prop and
        // the kernel is NON-CUMULATIVE, so a (C : Type)-parameterised CPS
        // eliminator may never be instantiated at an Eq goal.
        for (name, ty, val) in theorem_sources() {
            for src in [&ty, &val] {
                for (elim, c_index) in [
                    ("option_none_ne_some_type", 2usize),
                    ("no_whnf_step_bvar", 2),
                    ("r2_const_no_beta_reduces", 3),
                    ("const_ne_lam", 4),
                    ("lam_ne_app", 4),
                    ("pi_ne_app", 4),
                    ("let_ne_app", 5),
                    ("proj_ne_app", 5),
                ] {
                    for c in type_valued_c_slots(src, elim, c_index) {
                        assert!(
                            !c.starts_with("(Eq ") && c != "Prop",
                            "{name}: {elim}'s C parameter is (C : Type) but got the Prop term \
                             {c} — the spec's Eq is Prop and the kernel is non-cumulative. \
                             Route the absurdity through Empty first."
                        );
                    }
                }
            }
        }
        // (8) The Prop-valued `iota_step` may never be handed to a
        // (C : Type) CPS eliminator either; the engine's fire premise is
        // therefore the Type-valued `iota_reduces`.
        assert!(
            ty_candexp_iota_spine4().contains("iota_reduces")
                && !ty_candexp_iota_spine4().contains("iota_step "),
            "the engine's fire premise must be Type-valued iota_reduces"
        );
        // (9) RECURSOR-SHAPE PIN: R4 registers no new inductive and no new
        // plain def, so the measured uniform-leading-argument recursor
        // promotion cannot fire here.
        let src = include_str!("candmodel_construct_r4.rs");
        let body = src
            .split("pub(super) fn add_candmodel_construct_r4")
            .nth(1)
            .expect("the stage function must exist");
        let body = body.split("#[cfg(test)]").next().unwrap_or(body);
        assert!(
            !body.contains("self.add_inductive("),
            "RECURSOR-SHAPE PIN: R4 must register no new inductive"
        );
        assert!(
            !body.contains("self.add_recursive_def("),
            "RECURSOR-SHAPE PIN: R4 must register no new plain def"
        );
    }

    /// Paren-aware extraction of the `c_index`-th argument of every
    /// application of `elim` in `src` (0-based from the first argument).
    fn type_valued_c_slots(src: &str, elim: &str, c_index: usize) -> Vec<String> {
        let bytes: Vec<char> = src.chars().collect();
        let mut out = Vec::new();
        let mut from = 0usize;
        while let Some(rel) = src[from..].find(elim) {
            let start = from + rel;
            from = start + elim.len();
            let before_ok =
                start == 0 || !src[..start].ends_with(|c: char| c.is_alphanumeric() || c == '_');
            let after = src[start + elim.len()..].chars().next();
            if !before_ok || after != Some(' ') {
                continue;
            }
            let mut i = src[..start].chars().count() + elim.chars().count();
            let mut args: Vec<String> = Vec::new();
            while i < bytes.len() && args.len() <= c_index {
                while i < bytes.len() && bytes[i] == ' ' {
                    i += 1;
                }
                if i >= bytes.len() || bytes[i] == ')' {
                    break;
                }
                let s = i;
                if bytes[i] == '(' {
                    let mut d = 0i64;
                    while i < bytes.len() {
                        if bytes[i] == '(' {
                            d += 1;
                        } else if bytes[i] == ')' {
                            d -= 1;
                            if d == 0 {
                                i += 1;
                                break;
                            }
                        }
                        i += 1;
                    }
                } else {
                    while i < bytes.len() && bytes[i] != ' ' && bytes[i] != ')' {
                        i += 1;
                    }
                }
                args.push(bytes[s..i].iter().collect());
            }
            if let Some(c) = args.get(c_index) {
                out.push(c.clone());
            }
        }
        out
    }

    /// Registration + kernel re-verification against the substitution bundle.
    #[test]
    fn test_candmodel_r4_registered_and_reverifies() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();
        let names: Vec<String> = theorem_sources().into_iter().map(|(n, _, _)| n).collect();
        for name in &names {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the candmodel_construct_r4 stage"
            );
        }
        for name in &names {
            spec.verify_definition(name).unwrap_or_else(|e| {
                panic!("{name} should re-typecheck in the spec environment: {e:?}")
            });
        }
    }
}
