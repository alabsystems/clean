// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R3 of the candidate-model construction ladder: the APPLIED const spine —
//! the applied-delta transport `delta_app_lift` plus its engine
//! `candExp_delta_app`, and the IOTA ENGINE `candExp_iota_natrec_zero` for
//! the REAL reflected `Nat.rec` at the canonical `Nat.zero` major, together
//! with the complete reduct classification of a four-argument `Nat.rec` spine
//! (`natRecSpine1..4_beta_inv` / `natRecSpine4_whnf_inv`) both engines run on.
//!
//! Port of the corpus `StratifiedU/DataCand.lean` `red_natrec` /
//! `red_natrec_core` (rung `stratified-unified-sn`) + the applied case of
//! `LetDeltaSN.lean` `konst_red_aux`, per
//! `designs/2026-08-23-spec-candmodel-port.md` §5 rung R2/R3 (the design's
//! per-former iota engine at the LIVE recursor name). Builds directly on R0
//! (`IsCandSet`), R1 (`betaStar`, `betaStar_bvar_collapse`, `cand_var_witness`)
//! and R2 (`r2_const_no_beta_reduces`, `delta_step_to_reduces`).
//!
//! ## The delta-under-a-spine question, SETTLED FROM SOURCE
//!
//! R2's module docs scoped R3 with: *"delta fires only at the ROOT
//! (`whnf_step`'s delta leg has NO congruence — `beta_reduces` embeds iota but
//! not delta). APPLIED const spines `app (const c us) a…` — where iota
//! genuinely fires on live recursors and delta re-applies the spine — are the
//! R3 rung."* Both halves are exactly right, and the second half is the one
//! that decides R3-A. From `delta_step.rs:61`:
//!
//! ```text
//! def delta_reduct (env : DefEnv) (e : KExpr) : OptionType KExpr :=
//!   opt_bind Name KExpr (kexpr_const_name (kapp_fn e)) (fun (dname : Name) =>
//!     opt_bind KExpr KExpr (defval_for env dname) (fun (val : KExpr) =>
//!       OptionType.some KExpr (apply_spine (kapp_args e) val)))
//! ```
//!
//! The name lookup is at `kapp_fn e` — the SPINE HEAD, not the root — and the
//! reduct re-applies `kapp_args e`. So applied-head delta IS a reduction of
//! this calculus: `app (const c us) a` delta-steps to `app v a` whenever the
//! bare `const c us` delta-steps to `v`. "No congruence" means delta never
//! fires in a NON-spine subterm position (under a binder, in a `let_` value,
//! in a `proj` scrutinee) — the whnf root must be the spine itself. R3-A is
//! therefore NOT the composite fallback the task allowed: `delta_app_lift` is
//! a real one-step transport theorem, proved by case analysis on
//! `defval_for env c` (`OptionType.rec`), and it is what `candExp_delta_app`'s
//! delta leg consumes. `r3_appliedDelta_witness` mints the corresponding step
//! on the REAL reflected env at a one-argument spine.
//!
//! ## Honesty notes (read before quoting)
//!
//! - **The iota engine is ONE recursor family at ONE canonical major.**
//!   `candExp_iota_natrec_zero` covers `Nat.rec mot m0 m1 Nat.zero` — the
//!   reflected `kcre_name_27` recursor at the reflected `kcre_name_18`
//!   constructor. Generic/indexed/mutual recursors, and the `Nat.succ` major's
//!   ENGINE, are NOT here: the succ major adds a fourth accessibility layer
//!   (the numeral argument steps under `app_right`) and is R4. What R3 DOES
//!   land at the succ major is the FIRE — `natRecS_iota_fires` and its numeral
//!   instance `natRecSuccZero_iota_fires` — so R4 inherits the reduct equation
//!   and only has to add the Acc layer.
//! - **The contractum is PROJECTED, never hand-copied.** The zero-rule RHS is
//!   `kapp_fn kcre_witness_nat_zero_reduct` and the succ-rule RHS is the
//!   `OptionType.rec` projection of a closed probe's own iota reduct. Neither
//!   spelling duplicates a reflected literal, so a regeneration of
//!   `kernel_core_red_env` that moves the Nat.rec rules fails these proofs
//!   CLOSED (the `Eq.refl`s stop computing) rather than drifting silently.
//!   This is the same designated-discharge posture R2 adopted (the_red_env.rs
//!   Guard 3) and it is why every fire here is `Eq.refl` over the real env.
//! - **The iota fire is GENERIC in the motive and both minors, and that is a
//!   structural fact.** `iota_reduct` inspects only the spine head, the arity,
//!   and the MAJOR's head const; it never looks inside `mot`/`m0`/`m1`. So
//!   `natRecZ_iota_fires` is one `Eq.refl` with three free variables, and the
//!   engine needs no substitution transport at all — R2's
//!   `betaRed_inst_transport` is NOT consumed here. (It becomes load-bearing
//!   for the W/generic rungs, where the contractum substitutes into a minor.)
//! - **Nat.rec is not delta-defined, and that is checked, not assumed.**
//!   `natRecSpine4_delta_none` is a refl over the real env: `kcre_name_27` has
//!   no `defval_for` entry, so the whnf delta leg of a Nat.rec spine is dead.
//!   Without it the spine's reduct classification would be incomplete.
//! - **The necessity guard is a DISTINCT route, not the same theorem.**
//!   `natRecV_iota_none` shows a stuck (bvar) major does NOT fire iota — the
//!   major's `kexpr_const_name (kapp_fn ..)` is `none`. `natRecStuck_cand_mem`
//!   then puts the fully stuck spine into EVERY candidate set through cr3
//!   alone, with the iota continuation refuted rather than consumed. So the
//!   two routes through `natRecSpine4_whnf_inv` are exercised separately and
//!   the iota premise is visibly load-bearing: `natRecZ_contract_acc_necessary`
//!   proves the converse (SN of the redex FORCES SN of the contractum), so no
//!   engine variant may drop it.
//! - **The two concrete engine runs are CONDITIONAL, deliberately.**
//!   `natRecZ_engine_concrete` and `r3_deltaApp_concrete` discharge every
//!   premise of their engine at concrete arguments EXCEPT the contractum's own
//!   strong normalization, which they carry as a hypothesis. That is honest:
//!   the real `Nat.rec` zero-rule RHS is a three-lambda over reflected
//!   annotations and the real DefEnv values are lambdas whose bodies mention
//!   further delta-live constants, so SN of a contractum is a fundamental-
//!   theorem obligation (design rungs R5/R6), not an R3 brick. The
//!   unconditional positive membership this rung DOES land is
//!   `natRecStuck_witness` (a real four-argument `Nat.rec` spine in the base
//!   candidate set, through cr3), and the unconditional reduction content is
//!   the four `Eq.refl` fires/deadnesses over the real env.
//! - **No new inductives, so the recursor-promotion hazard cannot fire.**
//!   R3 registers only `add_definition` theorems: there is no new `inductive`
//!   whose uniform LEADING constructor argument could be promoted to an
//!   implicit recursor parameter (the measured 2026-08-23 hazard). The shape
//!   guard `test_candmodel_r3_shape_guards` pins that by asserting the stage
//!   body contains no `add_inductive` / `add_recursive_def` call.
//!
//! ## Census
//!
//! ZERO new axioms: every constant is value-bearing (all theorems via
//! `add_definition` with kernel `add_decl` checking; no new inductives, no new
//! axioms). Census-neutral.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ==== R3 SOURCES BEGIN (dependency-free: consts + pure string builders; ====
// ==== extracted verbatim by the pre-validation parse harness)           ====

// ================================================================
// Group 0 — the reflected atoms and the spine builders.
//
// Every literal is a GENERATED `kcre_*` atom, never a hand-written Name or
// KExpr: `kcre_name_27` is Nat.rec, `kcre_name_18` is Nat.zero,
// `kcre_name_10` is Nat.succ, and the zero-rule RHS is projected out of the
// generated Guard-4 iota reduct with `kapp_fn`.
// ================================================================

/// `Nat.rec` as a reflected const with an empty level list.
pub const NREC: &str = "(KExpr.const kcre_name_27 (ListType.nil Level))";
/// `Nat.zero` — the canonical major of the zero rule.
pub const NZERO: &str = "(KExpr.const kcre_name_18 (ListType.nil Level))";
/// `Nat.succ` — the head of the successor major.
pub const NSUCC: &str = "(KExpr.const kcre_name_10 (ListType.nil Level))";
/// The REAL `Nat.rec` zero-rule RHS, projected from the generated Guard-4
/// reduct `kcre_witness_nat_zero_reduct = rhs (sort 0) (sort 0) (sort 0)`.
pub const RHSZ: &str = "(kapp_fn kcre_witness_nat_zero_reduct)";
/// A closed probe whose iota reduct exposes the REAL successor-rule RHS.
pub const SUCC_PROBE: &str = "(KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const kcre_name_27 (ListType.nil Level)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero)) (KExpr.app (KExpr.const kcre_name_10 (ListType.nil Level)) (KExpr.sort Level.zero)))";
/// The REAL `Nat.rec` successor-rule RHS: the head of the probe's own iota
/// reduct, extracted with a bare `OptionType.rec` (no `opt_default`
/// dependency, so this stays inside the substitution bundle).
pub fn rhss() -> String {
    format!(
        "(kapp_fn (OptionType.rec KExpr (fun (_ : OptionType KExpr) => KExpr) (KExpr.sort Level.zero) (fun (qr : KExpr) => qr) (iota_reduct (red_rec the_red_env) {SUCC_PROBE})))"
    )
}

/// `KExpr.app f a`.
pub fn ap(f: &str, a: &str) -> String {
    format!("(KExpr.app {f} {a})")
}

/// The `Nat.rec` application spine over the given argument terms.
pub fn sp(args: &[&str]) -> String {
    let mut t = NREC.to_string();
    for a in args {
        t = ap(&t, a);
    }
    t
}

/// The zero-rule contractum `rhsZero mot m0 m1`.
pub fn zcontract(x1: &str, x2: &str, x3: &str) -> String {
    ap(&ap(&ap(RHSZ, x1), x2), x3)
}

/// The successor-rule contractum `rhsSucc mot m0 m1 n`.
pub fn scontract(x1: &str, x2: &str, x3: &str, n: &str) -> String {
    ap(&ap(&ap(&ap(&rhss(), x1), x2), x3), n)
}

// ================================================================
// Group A — the 15-arm `beta_reduces.rec` CPS inversion scaffold.
//
// Template idiom: `wRecSpine1_step_inv` / `wRecSpine2_step_inv`
// (acc_wtype.rs) and R1's `betaRedex_beta_inv`. Arm order = beta_reduces
// constructor order: beta, app_left, app_right, lam_ty, lam_body, pi_dom,
// pi_cod, forall_congr_dom, forall_congr_cod, zeta, let_ty, let_val,
// let_body, iota, proj.
//
// CAPTURE HAZARD AUDIT (the R1 module-doc rule): every binder this scaffold
// introduces is `q`-prefixed (`qs`/`qt`/`qA`/`qb`/`qarg`/`qf`/`qf2`/`qa`/
// `qa2`/`qty`/`qty2`/`qbody`/`qbody2`/`qdom`/`qdom2`/`qval`/`qval2`/`qsub`/
// `qsub2`/`qps`/`qpi`/`qe`/`qe2`/`qio`/`qz`/`qx`) or `heq`/`k<n>`; the
// substituted terms are caller-chosen outer names (`x1..x4`, `c`, `us`,
// `arg0`, `g2`, `C`) and reflected `kcre_*` atoms, none of which is
// `q`-prefixed. So no substituted target can be captured by a template
// binder.
// ================================================================

/// A continuation of the inversion: its binder name and its type as a
/// function of the reduct term (the `@R@` placeholder).
pub struct Cont {
    pub name: &'static str,
    pub ty: String,
}

/// Continuation BINDERS at a given reduct target (R4 reuses this scaffold).
pub fn conts_at(conts: &[Cont], target: &str, binder_prefix: &str) -> String {
    conts
        .iter()
        .map(|c| {
            format!(
                " ({binder_prefix}{} : {})",
                c.name,
                c.ty.replace("@R@", target)
            )
        })
        .collect::<Vec<_>>()
        .join("")
}

/// Continuation TYPES at a given reduct target (R4 reuses this scaffold).
pub fn conts_ty_at(conts: &[Cont], target: &str) -> String {
    conts
        .iter()
        .map(|c| format!("({}) -> ", c.ty.replace("@R@", target)))
        .collect::<Vec<_>>()
        .join("")
}

/// The recursive-arm induction hypothesis: the motive at (`src`, `dst`).
fn ih_ty(conts: &[Cont], redex: &str, src: &str, dst: &str) -> String {
    format!("Eq KExpr {src} {redex} -> {}C", conts_ty_at(conts, dst))
}

/// Build the whole 15-arm inversion body (everything after the outer binders):
/// `beta_reduces.rec MOTIVE arm1 .. arm15 REDEX g2 hb (Eq.refl ..) k1 .. kn`.
///
/// `live_beta` / `live_appl` / `live_appr` / `live_iota` are the four arm
/// BODIES (the text after `=>`); every other arm is a structural
/// discrimination fixed by the redex being an application.
#[allow(clippy::too_many_arguments)]
pub fn beta_inv_body(
    redex: &str,
    head: &str,
    arg: &str,
    conts: &[Cont],
    live_beta: &str,
    live_appl: &str,
    live_appr: &str,
    live_iota: &str,
) -> String {
    let mot = format!(
        "(fun (qs : KExpr) (qt : KExpr) (_ : beta_reduces qs qt) => Eq KExpr qs {redex} -> {}C)",
        conts_ty_at(conts, "qt")
    );
    // 1 beta
    let src_beta = "(KExpr.app (KExpr.lam qA qb) qarg)";
    let a_beta = format!(
        "(fun (qA : KExpr) (qb : KExpr) (qarg : KExpr) (heq : Eq KExpr {src_beta} {redex}){} => {live_beta})",
        conts_at(conts, "(instantiate qb qarg)", "")
    );
    // 2 app_left
    let a_appl = format!(
        "(fun (qf : KExpr) (qf2 : KExpr) (qa : KExpr) (qstep : beta_reduces qf qf2) (_qih : {}) (heq : Eq KExpr (KExpr.app qf qa) {redex}){} => {live_appl})",
        ih_ty(conts, redex, "qf", "qf2"),
        conts_at(conts, "(KExpr.app qf2 qa)", "")
    );
    // 3 app_right
    let a_appr = format!(
        "(fun (qf : KExpr) (qa : KExpr) (qa2 : KExpr) (qstep : beta_reduces qa qa2) (_qih : {}) (heq : Eq KExpr (KExpr.app qf qa) {redex}){} => {live_appr})",
        ih_ty(conts, redex, "qa", "qa2"),
        conts_at(conts, "(KExpr.app qf qa2)", "")
    );
    // Structural dead arms.
    // ARM-ARITY NOTE (the second 2026-08-24 measured failure): a `beta_reduces`
    // minor binds its constructor fields, then the RECURSIVE PREMISE, then the
    // induction hypothesis. The first R3 attempt bound fields + IH and dropped
    // the premise, shifting every later binder by one; the kernel reported it
    // far downstream as `cannot unify expressions of different shape:
    // Discriminant(6) vs Discriminant(4)` (KExpr `let_` vs `pi`) inside the
    // lam_ty arm. Both landed precedents bind it —
    // `wRecSpine1_step_inv` (acc_wtype.rs) and `r2_const_no_beta_reduces`
    // (candmodel_construct_r2.rs) each carry `(_hstep : beta_reduces ty ty2)`.
    // `beta`, `zeta` and `iota` take NO premise binder of this kind: the first
    // two have no recursive argument and `iota`'s premise is `iota_reduces`,
    // which is bound explicitly in that arm instead.
    let dead = |fields: &str, ih: Option<(&str, &str)>, src: &str, tgt: &str, body: String| {
        let ih_txt = match ih {
            Some((s, d)) => format!(
                " (_qstep : beta_reduces {s} {d}) (_qih : {})",
                ih_ty(conts, redex, s, d)
            ),
            None => String::new(),
        };
        format!(
            "(fun {fields}{ih_txt} (heq : Eq KExpr {src} {redex}){} => {body})",
            conts_at(conts, tgt, "_")
        )
    };
    let lam_kill = format!("lam_ne_app qty qbody {head} {arg} C heq");
    let pi_kill = format!("pi_ne_app qdom qbody {head} {arg} C heq");
    let let_kill = format!("let_ne_app qty qval qbody {head} {arg} C heq");
    let proj_kill = format!("proj_ne_app qps qpi qsub {head} {arg} C heq");
    let a_lamty = dead(
        "(qty : KExpr) (qty2 : KExpr) (qbody : KExpr)",
        Some(("qty", "qty2")),
        "(KExpr.lam qty qbody)",
        "(KExpr.lam qty2 qbody)",
        lam_kill.clone(),
    );
    let a_lambd = dead(
        "(qty : KExpr) (qbody : KExpr) (qbody2 : KExpr)",
        Some(("qbody", "qbody2")),
        "(KExpr.lam qty qbody)",
        "(KExpr.lam qty qbody2)",
        lam_kill,
    );
    let a_pidom = dead(
        "(qdom : KExpr) (qdom2 : KExpr) (qbody : KExpr)",
        Some(("qdom", "qdom2")),
        "(KExpr.pi qdom qbody)",
        "(KExpr.pi qdom2 qbody)",
        pi_kill.clone(),
    );
    let a_picod = dead(
        "(qdom : KExpr) (qbody : KExpr) (qbody2 : KExpr)",
        Some(("qbody", "qbody2")),
        "(KExpr.pi qdom qbody)",
        "(KExpr.pi qdom qbody2)",
        pi_kill.clone(),
    );
    let a_fadom = dead(
        "(qdom : KExpr) (qdom2 : KExpr) (qbody : KExpr)",
        Some(("qdom", "qdom2")),
        "(KExpr.forall_ qdom qbody)",
        "(KExpr.forall_ qdom2 qbody)",
        pi_kill.clone(),
    );
    let a_facod = dead(
        "(qdom : KExpr) (qbody : KExpr) (qbody2 : KExpr)",
        Some(("qbody", "qbody2")),
        "(KExpr.forall_ qdom qbody)",
        "(KExpr.forall_ qdom qbody2)",
        pi_kill,
    );
    let a_zeta = dead(
        "(qty : KExpr) (qval : KExpr) (qbody : KExpr)",
        None,
        "(KExpr.let_ qty qval qbody)",
        "(instantiate qbody qval)",
        let_kill.clone(),
    );
    let a_letty = dead(
        "(qty : KExpr) (qty2 : KExpr) (qval : KExpr) (qbody : KExpr)",
        Some(("qty", "qty2")),
        "(KExpr.let_ qty qval qbody)",
        "(KExpr.let_ qty2 qval qbody)",
        let_kill.clone(),
    );
    let a_letval = dead(
        "(qty : KExpr) (qval : KExpr) (qval2 : KExpr) (qbody : KExpr)",
        Some(("qval", "qval2")),
        "(KExpr.let_ qty qval qbody)",
        "(KExpr.let_ qty qval2 qbody)",
        let_kill.clone(),
    );
    let a_letbd = dead(
        "(qty : KExpr) (qval : KExpr) (qbody : KExpr) (qbody2 : KExpr)",
        Some(("qbody", "qbody2")),
        "(KExpr.let_ qty qval qbody)",
        "(KExpr.let_ qty qval qbody2)",
        let_kill,
    );
    let a_proj = dead(
        "(qps : Name) (qpi : Nat) (qsub : KExpr) (qsub2 : KExpr)",
        Some(("qsub", "qsub2")),
        "(KExpr.proj qps qpi qsub)",
        "(KExpr.proj qps qpi qsub2)",
        proj_kill,
    );
    // 14 iota
    let a_iota = format!(
        "(fun (qe : KExpr) (qe2 : KExpr) (qio : iota_reduces qe qe2) (heq : Eq KExpr qe {redex}){} => {live_iota})",
        conts_at(conts, "qe2", "")
    );
    let tail = conts
        .iter()
        .map(|c| format!(" {}", c.name))
        .collect::<Vec<_>>()
        .join("");
    format!(
        "beta_reduces.rec {mot} {a_beta} {a_appl} {a_appr} {a_lamty} {a_lambd} {a_pidom} {a_picod} {a_fadom} {a_facod} {a_zeta} {a_letty} {a_letval} {a_letbd} {a_iota} {a_proj} {redex} g2 hb (Eq.refl KExpr {redex}){tail}"
    )
}

/// The computational iota kill used by the short (arity < 4) `Nat.rec` spines
/// and by any const head that is not a recursor: `iota_reduct env <redex>`
/// computes to `none`, so a transported `iota_reduces` step is absurd.
fn iota_kill_refl(redex: &str) -> String {
    format!(
        "option_none_ne_some_type KExpr qe2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct (red_rec the_red_env) qe) (OptionType.some KExpr qe2) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) qe) (OptionType.none KExpr) (Eq.trans (OptionType KExpr) (iota_reduct (red_rec the_red_env) qe) (iota_reduct (red_rec the_red_env) {redex}) (OptionType.none KExpr) (Eq.cong KExpr (OptionType KExpr) (fun (qz : KExpr) => iota_reduct (red_rec the_red_env) qz) qe {redex} heq) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)))) (iota_reduces_to_step qe qe2 qio))"
    )
}

// ================================================================
// Group B — the applied-delta transport and its engine.
// ================================================================

/// `opt_bind o some = o` — the monad right-identity at `OptionType KExpr`.
///
/// PROP/TYPE NOTE (the 2026-08-24 measured failure): the motive here is a PLAIN
/// `Eq`, matching the ~80 landed `OptionType.rec (fun o => Eq ..)` precedents.
/// The first R3 attempt instead case-split with an IMPLICATION motive and
/// closed its `none` arm with `option_none_ne_some_type KExpr v <Prop goal>`.
/// That lemma's third parameter is `(C : Type)`, and the spec's `Eq` is `Prop`
/// — a non-cumulative kernel rejects the instantiation, verbatim
/// `Type mismatch: expected Sort(Succ(Zero)), got universe level conflict:
/// 0 vs 1`. R1 had already recorded the trap (`betaStar_bvar_collapse`'s
/// `Empty.rec` detour). Rather than take that detour, R3 removes the case
/// analysis from the transport entirely: this identity is the ONLY case split,
/// and `delta_app_lift` is then a single `Eq.cong` over the option.
pub const TY_R3_OPT_BIND_ID: &str = "forall (o : OptionType KExpr), Eq (OptionType KExpr) (opt_bind KExpr KExpr o (fun (qx : KExpr) => OptionType.some KExpr qx)) o";
pub const VAL_R3_OPT_BIND_ID: &str = "fun (o : OptionType KExpr) => OptionType.rec KExpr (fun (qo : OptionType KExpr) => Eq (OptionType KExpr) (opt_bind KExpr KExpr qo (fun (qx : KExpr) => OptionType.some KExpr qx)) qo) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (qw : KExpr) => Eq.refl (OptionType KExpr) (OptionType.some KExpr qw)) o";

pub const TY_DELTA_APP_LIFT: &str = "forall (env : DefEnv) (c : Name) (us : ListType Level) (v : KExpr) (a : KExpr), delta_step env (KExpr.const c us) v -> delta_step env (KExpr.app (KExpr.const c us) a) (KExpr.app v a)";

pub fn val_delta_app_lift() -> String {
    let f_id = "(fun (qx : KExpr) => OptionType.some KExpr qx)";
    let f_ap = "(fun (qx : KExpr) => OptionType.some KExpr (KExpr.app qx a))";
    let dv = "(defval_for env c)";
    let bound_id = format!("(opt_bind KExpr KExpr {dv} {f_id})");
    // hdv : defval_for env c = some v — the bare lookup equation, recovered
    // from the bare-const delta step through the right-identity.
    let hdv = format!(
        "(Eq.trans (OptionType KExpr) {dv} {bound_id} (OptionType.some KExpr v) (Eq.symm (OptionType KExpr) {bound_id} {dv} (r3_opt_bind_id {dv})) hd)"
    );
    // Congruence on the WHOLE option: `opt_bind (some v) f_ap` reduces to
    // `some (app v a)`, which is the applied delta reduct, so no case analysis
    // and no Type-valued eliminator appear anywhere in this term.
    format!(
        "fun (env : DefEnv) (c : Name) (us : ListType Level) (v : KExpr) (a : KExpr) (hd : delta_step env (KExpr.const c us) v) => Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (qo : OptionType KExpr) => opt_bind KExpr KExpr qo {f_ap}) {dv} (OptionType.some KExpr v) {hdv}"
    )
}

pub const TY_R3_APPLIED_DELTA_WITNESS: &str = "delta_step (red_def the_red_env) (KExpr.app (KExpr.const kcre_witness_delta_head (ListType.nil Level)) (KExpr.bvar Nat.zero)) (KExpr.app kcre_witness_delta_value (KExpr.bvar Nat.zero))";
pub const VAL_R3_APPLIED_DELTA_WITNESS: &str = "delta_app_lift (red_def the_red_env) kcre_witness_delta_head (ListType.nil Level) kcre_witness_delta_value (KExpr.bvar Nat.zero) the_red_env_delta_nonvacuous";

pub const TY_APPCONST_ACC_REDUCT_ACC: &str = "forall (c : Name) (us : ListType Level) (v : KExpr) (a : KExpr), delta_step (red_def the_red_env) (KExpr.const c us) v -> whnf_acc (KExpr.app (KExpr.const c us) a) -> whnf_acc (KExpr.app v a)";
pub const VAL_APPCONST_ACC_REDUCT_ACC: &str = "fun (c : Name) (us : ListType Level) (v : KExpr) (a : KExpr) (hd : delta_step (red_def the_red_env) (KExpr.const c us) v) (hacc : whnf_acc (KExpr.app (KExpr.const c us) a)) => whnfAcc_inv_step (KExpr.app (KExpr.const c us) a) hacc (KExpr.app v a) (whnf_step.delta (KExpr.app (KExpr.const c us) a) (KExpr.app v a) (delta_step_to_reduces (KExpr.app (KExpr.const c us) a) (KExpr.app v a) (delta_app_lift (red_def the_red_env) c us v a hd)))";

// ---- the const-headed one-argument spine inversion ----

const CHEAD: &str = "(KExpr.const c us)";

fn capp_redex() -> String {
    ap(CHEAD, "arg0")
}

fn capp_conts() -> Vec<Cont> {
    vec![
        Cont {
            name: "kArg",
            ty: format!(
                "forall (qy : KExpr), beta_reduces arg0 qy -> Eq KExpr @R@ {} -> C",
                ap(CHEAD, "qy")
            ),
        },
        Cont {
            name: "kIota",
            ty: format!("iota_reduces {} @R@ -> C", capp_redex()),
        },
    ]
}

pub fn ty_constapp1_beta_inv() -> String {
    let r = capp_redex();
    let cs = capp_conts();
    format!(
        "forall (c : Name) (us : ListType Level) (arg0 : KExpr) (g2 : KExpr) (C : Type), beta_reduces {r} g2 -> {}C",
        conts_ty_at(&cs, "g2")
    )
}

pub fn val_constapp1_beta_inv() -> String {
    let r = capp_redex();
    let cs = capp_conts();
    let live_beta = format!(
        "const_ne_lam c us qA qb C (Eq.symm KExpr (KExpr.lam qA qb) {CHEAD} (app_inj_fst (KExpr.lam qA qb) qarg {CHEAD} arg0 heq))"
    );
    let live_appl = format!(
        "r2_const_no_beta_reduces c us qf2 C (Eq.rec KExpr qf (fun (qx : KExpr) (_ : Eq KExpr qf qx) => beta_reduces qx qf2) qstep {CHEAD} (app_inj_fst qf qa {CHEAD} arg0 heq))"
    );
    let live_appr = format!(
        "kArg qa2 (Eq.rec KExpr qa (fun (qx : KExpr) (_ : Eq KExpr qa qx) => beta_reduces qx qa2) qstep arg0 (app_inj_snd qf qa {CHEAD} arg0 heq)) (Eq.cong KExpr KExpr (fun (qz : KExpr) => KExpr.app qz qa2) qf {CHEAD} (app_inj_fst qf qa {CHEAD} arg0 heq))"
    );
    let live_iota = format!(
        "kIota (Eq.substType KExpr (fun (qz : KExpr) => iota_reduces qz qe2) qe {r} heq qio)"
    );
    let body = beta_inv_body(
        &r, CHEAD, "arg0", &cs, &live_beta, &live_appl, &live_appr, &live_iota,
    );
    format!(
        "fun (c : Name) (us : ListType Level) (arg0 : KExpr) (g2 : KExpr) (C : Type) (hb : beta_reduces {r} g2){} => {body}",
        conts_at(&cs, "g2", "")
    )
}

fn capp_whnf_conts() -> Vec<Cont> {
    let mut cs = capp_conts();
    cs.push(Cont {
        name: "kDelta",
        ty: format!("delta_step (red_def the_red_env) {} @R@ -> C", capp_redex()),
    });
    cs
}

pub fn ty_constapp1_whnf_inv() -> String {
    let r = capp_redex();
    let cs = capp_whnf_conts();
    format!(
        "forall (c : Name) (us : ListType Level) (arg0 : KExpr) (g2 : KExpr) (C : Type), whnf_step {r} g2 -> {}C",
        conts_ty_at(&cs, "g2")
    )
}

pub fn val_constapp1_whnf_inv() -> String {
    let r = capp_redex();
    let cs = capp_whnf_conts();
    format!(
        "fun (c : Name) (us : ListType Level) (arg0 : KExpr) (g2 : KExpr) (C : Type) (hs : whnf_step {r} g2){} => whnf_step.rec {r} g2 (fun (_ : whnf_step {r} g2) => C) (fun (hbr : beta_reduces {r} g2) => constApp1_beta_inv c us arg0 g2 C hbr kArg kIota) (fun (hdr : delta_reduces {r} g2) => kDelta (delta_reduces_to_step {r} g2 hdr)) hs",
        conts_at(&cs, "g2", "")
    )
}

// ---- the applied-delta engine ----

pub fn ty_candexp_delta_app() -> String {
    let r = capp_redex();
    format!(
        "forall (S : KExpr -> Type), IsCandSet S -> forall (c : Name) (us : ListType Level) (v : KExpr), delta_step (red_def the_red_env) (KExpr.const c us) v -> forall (arg0 : KExpr), (forall (a2 : KExpr), betaStar arg0 a2 -> Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) {}) (OptionType.none KExpr)) -> whnf_acc arg0 -> (forall (a2 : KExpr), betaStar arg0 a2 -> S (KExpr.app v a2)) -> S {r}",
        ap(CHEAD, "a2")
    )
}

pub fn val_candexp_delta_app() -> String {
    let motive_body = |a: &str| {
        format!(
            "(forall (a2 : KExpr), betaStar {a} a2 -> Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) {}) (OptionType.none KExpr)) -> (forall (a2 : KExpr), betaStar {a} a2 -> S (KExpr.app v a2)) -> S {}",
            ap(CHEAD, "a2"),
            ap(CHEAD, a)
        )
    };
    let ra0 = ap(CHEAD, "a0");
    let core = format!(
        "isCandSet_cr3 S hS {ra0} ConstFreeUnit.triv (fun (e2 : KExpr) (hs : whnf_step {ra0} e2) => constApp1_whnf_inv c us a0 e2 (S e2) hs (fun (qy : KExpr) (hy : beta_reduces a0 qy) (heq : Eq KExpr e2 {ry}) => Eq.substType KExpr (fun (qw : KExpr) => S qw) {ry} e2 (Eq.symm KExpr e2 {ry} heq) (iha qy (whnf_step.beta a0 qy hy) (fun (a2 : KExpr) (hst : betaStar qy a2) => hio a2 (betaStar.step a0 qy a2 hy hst)) (fun (a2 : KExpr) (hst : betaStar qy a2) => hfam a2 (betaStar.step a0 qy a2 hy hst)))) (fun (hiota : iota_reduces {ra0} e2) => option_none_ne_some_type KExpr e2 (S e2) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct (red_rec the_red_env) {ra0}) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) {ra0}) (OptionType.none KExpr) (hio a0 (betaStar.refl a0))) (iota_reduces_to_step {ra0} e2 hiota))) (fun (hdl : delta_step (red_def the_red_env) {ra0} e2) => Eq.substType KExpr (fun (qw : KExpr) => S qw) (KExpr.app v a0) e2 (delta_step_deterministic (red_def the_red_env) {ra0} (KExpr.app v a0) e2 (delta_app_lift (red_def the_red_env) c us v a0 hdel) hdl) (hfam a0 (betaStar.refl a0))))",
        ry = ap(CHEAD, "qy")
    );
    let arm = format!(
        "(fun (a0 : KExpr) (_has : forall (w2 : KExpr), whnf_step a0 w2 -> whnf_acc w2) (iha : forall (w2 : KExpr), whnf_step a0 w2 -> {}) (hio : forall (a2 : KExpr), betaStar a0 a2 -> Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) {}) (OptionType.none KExpr)) (hfam : forall (a2 : KExpr), betaStar a0 a2 -> S (KExpr.app v a2)) => {core})",
        motive_body("w2"),
        ap(CHEAD, "a2")
    );
    format!(
        "fun (S : KExpr -> Type) (hS : IsCandSet S) (c : Name) (us : ListType Level) (v : KExpr) (hdel : delta_step (red_def the_red_env) (KExpr.const c us) v) (arg0 : KExpr) (hio0 : forall (a2 : KExpr), betaStar arg0 a2 -> Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) {}) (OptionType.none KExpr)) (hacc : whnf_acc arg0) (hfam0 : forall (a2 : KExpr), betaStar arg0 a2 -> S (KExpr.app v a2)) => whnf_acc.rec (fun (a0 : KExpr) (_ : whnf_acc a0) => {}) {arm} arg0 hacc hio0 hfam0",
        ap(CHEAD, "a2"),
        motive_body("a0")
    )
}

pub const TY_R3_DELTAAPP_IOTA_DEAD: &str = "forall (a : KExpr), Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) (KExpr.app (KExpr.const kcre_witness_delta_head (ListType.nil Level)) a)) (OptionType.none KExpr)";
pub const VAL_R3_DELTAAPP_IOTA_DEAD: &str =
    "fun (a : KExpr) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)";

pub const TY_R3_DELTAAPP_CONCRETE: &str = "whnf_acc (KExpr.app kcre_witness_delta_value (KExpr.bvar Nat.zero)) -> whnf_acc (KExpr.app (KExpr.const kcre_witness_delta_head (ListType.nil Level)) (KExpr.bvar Nat.zero))";
pub const VAL_R3_DELTAAPP_CONCRETE: &str = "fun (hc : whnf_acc (KExpr.app kcre_witness_delta_value (KExpr.bvar Nat.zero))) => candExp_delta_app (fun (e : KExpr) => whnf_acc e) isCand_whnfAcc kcre_witness_delta_head (ListType.nil Level) kcre_witness_delta_value the_red_env_delta_nonvacuous (KExpr.bvar Nat.zero) (fun (a2 : KExpr) (_ : betaStar (KExpr.bvar Nat.zero) a2) => r3_deltaApp_iota_dead a2) cand_var_witness (fun (a2 : KExpr) (hst : betaStar (KExpr.bvar Nat.zero) a2) => Eq.substType KExpr (fun (qw : KExpr) => whnf_acc (KExpr.app kcre_witness_delta_value qw)) (KExpr.bvar Nat.zero) a2 (Eq.symm KExpr a2 (KExpr.bvar Nat.zero) (betaStar_bvar_collapse Nat.zero a2 hst)) hc)";

// ================================================================
// Group C — the Nat.rec spine inversions (arity 1..4).
// ================================================================

fn spine_cont(idx: usize, args: &[&str]) -> Cont {
    let mut repl: Vec<&str> = args.to_vec();
    repl[idx] = "qy";
    let name: &'static str = match idx {
        0 => "k1",
        1 => "k2",
        2 => "k3",
        _ => "k4",
    };
    Cont {
        name,
        ty: format!(
            "forall (qy : KExpr), beta_reduces {} qy -> Eq KExpr @R@ {} -> C",
            args[idx],
            sp(&repl)
        ),
    }
}

fn spine_conts(args: &[&str]) -> Vec<Cont> {
    (0..args.len()).map(|i| spine_cont(i, args)).collect()
}

const SP_ARGS: [&str; 4] = ["x1", "x2", "x3", "x4"];

/// The shared arm bodies of a `Nat.rec` spine inversion at arity `n`.
fn spine_live_arms(n: usize, iota_live: bool) -> (String, String, String, String) {
    let args = &SP_ARGS[..n];
    let redex = sp(args);
    let head = sp(&args[..n - 1]);
    let arg = args[n - 1];
    let live_beta = if n == 1 {
        format!(
            "const_ne_lam kcre_name_27 (ListType.nil Level) qA qb C (Eq.symm KExpr (KExpr.lam qA qb) {head} (app_inj_fst (KExpr.lam qA qb) qarg {head} {arg} heq))"
        )
    } else {
        let inner_head = sp(&args[..n - 2]);
        let inner_arg = args[n - 2];
        format!(
            "lam_ne_app qA qb {inner_head} {inner_arg} C (app_inj_fst (KExpr.lam qA qb) qarg {head} {arg} heq)"
        )
    };
    let live_appl = if n == 1 {
        format!(
            "r2_const_no_beta_reduces kcre_name_27 (ListType.nil Level) qf2 C (Eq.rec KExpr qf (fun (qx : KExpr) (_ : Eq KExpr qf qx) => beta_reduces qx qf2) qstep {head} (app_inj_fst qf qa {head} {arg} heq))"
        )
    } else {
        let sub = &args[..n - 1];
        let sub_conts: Vec<String> = (0..n - 1)
            .map(|i| {
                let mut repl: Vec<&str> = args.to_vec();
                repl[i] = "qy";
                let inner = sp(&repl[..n - 1]);
                let outer = sp(&repl);
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
        format!(
            "natRecSpine{}_beta_inv {} qf2 C (Eq.rec KExpr qf (fun (qx : KExpr) (_ : Eq KExpr qf qx) => beta_reduces qx qf2) qstep {head} (app_inj_fst qf qa {head} {arg} heq)) {}",
            n - 1,
            sub.join(" "),
            sub_conts.join(" ")
        )
    };
    let kname = match n {
        1 => "k1",
        2 => "k2",
        3 => "k3",
        _ => "k4",
    };
    let live_appr = format!(
        "{kname} qa2 (Eq.rec KExpr qa (fun (qx : KExpr) (_ : Eq KExpr qa qx) => beta_reduces qx qa2) qstep {arg} (app_inj_snd qf qa {head} {arg} heq)) (Eq.cong KExpr KExpr (fun (qz : KExpr) => KExpr.app qz qa2) qf {head} (app_inj_fst qf qa {head} {arg} heq))"
    );
    let live_iota = if iota_live {
        format!("kIota (Eq.substType KExpr (fun (qz : KExpr) => iota_reduces qz qe2) qe {redex} heq qio)")
    } else {
        iota_kill_refl(&redex)
    };
    (live_beta, live_appl, live_appr, live_iota)
}

pub fn ty_natrec_spine_beta_inv(n: usize) -> String {
    let args = &SP_ARGS[..n];
    let redex = sp(args);
    let mut cs = spine_conts(args);
    if n == 4 {
        cs.push(Cont {
            name: "kIota",
            ty: format!("iota_reduces {redex} @R@ -> C"),
        });
    }
    let binders = args
        .iter()
        .map(|a| format!("({a} : KExpr) "))
        .collect::<Vec<_>>()
        .join("");
    format!(
        "forall {binders}(g2 : KExpr) (C : Type), beta_reduces {redex} g2 -> {}C",
        conts_ty_at(&cs, "g2")
    )
}

pub fn val_natrec_spine_beta_inv(n: usize) -> String {
    let args = &SP_ARGS[..n];
    let redex = sp(args);
    let head = sp(&args[..n - 1]);
    let arg = args[n - 1];
    let mut cs = spine_conts(args);
    if n == 4 {
        cs.push(Cont {
            name: "kIota",
            ty: format!("iota_reduces {redex} @R@ -> C"),
        });
    }
    let (lb, la, lr, li) = spine_live_arms(n, n == 4);
    let body = beta_inv_body(&redex, &head, arg, &cs, &lb, &la, &lr, &li);
    let binders = args
        .iter()
        .map(|a| format!("({a} : KExpr) "))
        .collect::<Vec<_>>()
        .join("");
    format!(
        "fun {binders}(g2 : KExpr) (C : Type) (hb : beta_reduces {redex} g2){} => {body}",
        conts_at(&cs, "g2", "")
    )
}

pub fn ty_natrec_spine4_delta_none() -> String {
    format!(
        "forall (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (x4 : KExpr), Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) {}) (OptionType.none KExpr)",
        sp(&SP_ARGS)
    )
}
pub const VAL_NATREC_SPINE4_DELTA_NONE: &str = "fun (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (x4 : KExpr) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)";

fn spine4_whnf_conts() -> Vec<Cont> {
    let redex = sp(&SP_ARGS);
    let mut cs = spine_conts(&SP_ARGS);
    cs.push(Cont {
        name: "kIota",
        ty: format!("iota_reduces {redex} @R@ -> C"),
    });
    cs
}

pub fn ty_natrec_spine4_whnf_inv() -> String {
    let redex = sp(&SP_ARGS);
    let cs = spine4_whnf_conts();
    format!(
        "forall (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (x4 : KExpr) (g2 : KExpr) (C : Type), whnf_step {redex} g2 -> {}C",
        conts_ty_at(&cs, "g2")
    )
}

pub fn val_natrec_spine4_whnf_inv() -> String {
    let redex = sp(&SP_ARGS);
    let cs = spine4_whnf_conts();
    format!(
        "fun (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (x4 : KExpr) (g2 : KExpr) (C : Type) (hs : whnf_step {redex} g2){} => whnf_step.rec {redex} g2 (fun (_ : whnf_step {redex} g2) => C) (fun (hbr : beta_reduces {redex} g2) => natRecSpine4_beta_inv x1 x2 x3 x4 g2 C hbr k1 k2 k3 k4 kIota) (fun (hdr : delta_reduces {redex} g2) => option_none_ne_some_type KExpr g2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def the_red_env) {redex}) (OptionType.some KExpr g2) (Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) {redex}) (OptionType.none KExpr) (natRecSpine4_delta_none x1 x2 x3 x4)) (delta_reduces_to_step {redex} g2 hdr))) hs",
        conts_at(&cs, "g2", "")
    )
}

// ================================================================
// Group D — the iota fires over the REAL reflected env (all refl).
// ================================================================

pub fn ty_natrecz_iota_fires() -> String {
    format!(
        "forall (x1 : KExpr) (x2 : KExpr) (x3 : KExpr), iota_step (red_rec the_red_env) {} {}",
        sp(&["x1", "x2", "x3", NZERO]),
        zcontract("x1", "x2", "x3")
    )
}
pub fn val_natrecz_iota_fires() -> String {
    format!(
        "fun (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) => Eq.refl (OptionType KExpr) (OptionType.some KExpr {})",
        zcontract("x1", "x2", "x3")
    )
}

pub fn ty_natrecs_iota_fires() -> String {
    format!(
        "forall (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (n : KExpr), iota_step (red_rec the_red_env) {} {}",
        sp(&["x1", "x2", "x3", &ap(NSUCC, "n")]),
        scontract("x1", "x2", "x3", "n")
    )
}
pub fn val_natrecs_iota_fires() -> String {
    format!(
        "fun (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (n : KExpr) => Eq.refl (OptionType KExpr) (OptionType.some KExpr {})",
        scontract("x1", "x2", "x3", "n")
    )
}

pub fn ty_natrec_succzero_iota_fires() -> String {
    let b0 = "(KExpr.bvar Nat.zero)";
    format!(
        "iota_step (red_rec the_red_env) {} {}",
        sp(&[b0, b0, b0, &ap(NSUCC, NZERO)]),
        scontract(b0, b0, b0, NZERO)
    )
}
pub const VAL_NATREC_SUCCZERO_IOTA_FIRES: &str = "natRecS_iota_fires (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) (KExpr.const kcre_name_18 (ListType.nil Level))";

pub fn ty_natrecv_iota_none() -> String {
    format!(
        "forall (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (i : Nat), Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) {}) (OptionType.none KExpr)",
        sp(&["x1", "x2", "x3", "(KExpr.bvar i)"])
    )
}
pub const VAL_NATRECV_IOTA_NONE: &str = "fun (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (i : Nat) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)";

// ================================================================
// Group E — the iota ENGINE at the canonical Nat.zero major.
// ================================================================

fn zfam(a1: &str, a2: &str, a3: &str) -> String {
    format!(
        "forall (b1 : KExpr), betaStar {a1} b1 -> forall (b2 : KExpr), betaStar {a2} b2 -> forall (b3 : KExpr), betaStar {a3} b3 -> S {}",
        zcontract("b1", "b2", "b3")
    )
}

fn zredex(a1: &str, a2: &str, a3: &str) -> String {
    sp(&[a1, a2, a3, NZERO])
}

pub fn ty_candexp_iota_natrec_zero() -> String {
    format!(
        "forall (S : KExpr -> Type), IsCandSet S -> forall (mot : KExpr), whnf_acc mot -> forall (m0 : KExpr), whnf_acc m0 -> forall (m1 : KExpr), whnf_acc m1 -> ({}) -> S {}",
        zfam("mot", "m0", "m1"),
        zredex("mot", "m0", "m1")
    )
}

pub fn val_candexp_iota_natrec_zero() -> String {
    // Motive at each nesting level.
    let p_mot = |t: &str| {
        format!(
            "forall (m0 : KExpr), whnf_acc m0 -> forall (m1 : KExpr), whnf_acc m1 -> ({}) -> S {}",
            zfam(t, "m0", "m1"),
            zredex(t, "m0", "m1")
        )
    };
    let p_m0 = |u: &str| {
        format!(
            "forall (m1 : KExpr), whnf_acc m1 -> ({}) -> S {}",
            zfam("t0", u, "m1"),
            zredex("t0", u, "m1")
        )
    };
    let p_m1 = |v: &str| format!("({}) -> S {}", zfam("t0", "u0", v), zredex("t0", "u0", v));
    let rz = zredex("t0", "u0", "v0");
    // The four congruence continuations plus the iota continuation.
    let cong = |slot: usize| {
        let base = ["t0", "u0", "v0", NZERO];
        let mut repl: Vec<&str> = base.to_vec();
        repl[slot] = "qy";
        let target = sp(&repl);
        let src = base[slot];
        let inner = match slot {
            0 => "ihmot qy (whnf_step.beta t0 qy hy) u0 (whnf_acc.intro u0 hus) v0 (whnf_acc.intro v0 hvs) (fun (b1 : KExpr) (h1 : betaStar qy b1) (b2 : KExpr) (h2 : betaStar u0 b2) (b3 : KExpr) (h3 : betaStar v0 b3) => hfam b1 (betaStar.step t0 qy b1 hy h1) b2 h2 b3 h3)"
                .to_string(),
            1 => "ihm0 qy (whnf_step.beta u0 qy hy) v0 (whnf_acc.intro v0 hvs) (fun (b1 : KExpr) (h1 : betaStar t0 b1) (b2 : KExpr) (h2 : betaStar qy b2) (b3 : KExpr) (h3 : betaStar v0 b3) => hfam b1 h1 b2 (betaStar.step u0 qy b2 hy h2) b3 h3)"
                .to_string(),
            2 => "ihm1 qy (whnf_step.beta v0 qy hy) (fun (b1 : KExpr) (h1 : betaStar t0 b1) (b2 : KExpr) (h2 : betaStar u0 b2) (b3 : KExpr) (h3 : betaStar qy b3) => hfam b1 h1 b2 h2 b3 (betaStar.step v0 qy b3 hy h3))"
                .to_string(),
            _ => "r2_const_no_beta_reduces kcre_name_18 (ListType.nil Level) qy (S e2) hy"
                .to_string(),
        };
        if slot == 3 {
            format!(
                "(fun (qy : KExpr) (hy : beta_reduces {src} qy) (_heq : Eq KExpr e2 {target}) => {inner})"
            )
        } else {
            format!(
                "(fun (qy : KExpr) (hy : beta_reduces {src} qy) (heq : Eq KExpr e2 {target}) => Eq.substType KExpr (fun (qw : KExpr) => S qw) {target} e2 (Eq.symm KExpr e2 {target} heq) ({inner}))"
            )
        }
    };
    let zc = zcontract("t0", "u0", "v0");
    let k_iota = format!(
        "(fun (hio : iota_reduces {rz} e2) => Eq.substType KExpr (fun (qw : KExpr) => S qw) {zc} e2 (option_some_inj KExpr {zc} e2 (Eq.trans (OptionType KExpr) (OptionType.some KExpr {zc}) (iota_reduct (red_rec the_red_env) {rz}) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) {rz}) (OptionType.some KExpr {zc}) (natRecZ_iota_fires t0 u0 v0)) (iota_reduces_to_step {rz} e2 hio))) (hfam t0 (betaStar.refl t0) u0 (betaStar.refl u0) v0 (betaStar.refl v0)))"
    );
    let core = format!(
        "isCandSet_cr3 S hS {rz} ConstFreeUnit.triv (fun (e2 : KExpr) (hstep : whnf_step {rz} e2) => natRecSpine4_whnf_inv t0 u0 v0 {NZERO} e2 (S e2) hstep {} {} {} {} {k_iota})",
        cong(0),
        cong(1),
        cong(2),
        cong(3)
    );
    let arm_m1 = format!(
        "(fun (v0 : KExpr) (hvs : forall (v2 : KExpr), whnf_step v0 v2 -> whnf_acc v2) (ihm1 : forall (v2 : KExpr), whnf_step v0 v2 -> {}) (hfam : {}) => {core})",
        p_m1("v2"),
        zfam("t0", "u0", "v0")
    );
    let arm_m0 = format!(
        "(fun (u0 : KExpr) (hus : forall (u2 : KExpr), whnf_step u0 u2 -> whnf_acc u2) (ihm0 : forall (u2 : KExpr), whnf_step u0 u2 -> {}) (m1arg : KExpr) (hm1acc : whnf_acc m1arg) => whnf_acc.rec (fun (v0 : KExpr) (_ : whnf_acc v0) => {}) {arm_m1} m1arg hm1acc)",
        p_m0("u2"),
        p_m1("v0")
    );
    let arm_mot = format!(
        "(fun (t0 : KExpr) (_hts : forall (t2 : KExpr), whnf_step t0 t2 -> whnf_acc t2) (ihmot : forall (t2 : KExpr), whnf_step t0 t2 -> {}) (m0arg : KExpr) (hm0acc : whnf_acc m0arg) => whnf_acc.rec (fun (u0 : KExpr) (_ : whnf_acc u0) => {}) {arm_m0} m0arg hm0acc)",
        p_mot("t2"),
        p_m0("u0")
    );
    format!(
        "fun (S : KExpr -> Type) (hS : IsCandSet S) (mot : KExpr) (hmot : whnf_acc mot) (m0 : KExpr) (hm0 : whnf_acc m0) (m1 : KExpr) (hm1 : whnf_acc m1) (hfam0 : {}) => whnf_acc.rec (fun (t0 : KExpr) (_ : whnf_acc t0) => {}) {arm_mot} mot hmot m0 hm0 m1 hm1 hfam0",
        zfam("mot", "m0", "m1"),
        p_mot("t0")
    )
}

// ================================================================
// Group F — the §6 discriminating witnesses.
// ================================================================

pub fn ty_natrecz_contract_acc_necessary() -> String {
    format!(
        "forall (x1 : KExpr) (x2 : KExpr) (x3 : KExpr), whnf_acc {} -> whnf_acc {}",
        zredex("x1", "x2", "x3"),
        zcontract("x1", "x2", "x3")
    )
}
pub fn val_natrecz_contract_acc_necessary() -> String {
    let r = zredex("x1", "x2", "x3");
    let c = zcontract("x1", "x2", "x3");
    format!(
        "fun (x1 : KExpr) (x2 : KExpr) (x3 : KExpr) (hacc : whnf_acc {r}) => whnfAcc_inv_step {r} hacc {c} (whnf_step.beta {r} {c} (beta_reduces.iota {r} {c} (iota_step_to_reduces {r} {c} (natRecZ_iota_fires x1 x2 x3))))"
    )
}

pub fn ty_natrecz_engine_concrete() -> String {
    let b0 = "(KExpr.bvar Nat.zero)";
    format!(
        "whnf_acc {} -> whnf_acc {}",
        zcontract(b0, b0, b0),
        zredex(b0, b0, b0)
    )
}
pub fn val_natrecz_engine_concrete() -> String {
    let b0 = "(KExpr.bvar Nat.zero)";
    let collapse =
        |v: &str| format!("(Eq.symm KExpr {v} {b0} (betaStar_bvar_collapse Nat.zero {v} h{v}))");
    let s1 = format!(
        "(Eq.substType KExpr (fun (qw : KExpr) => whnf_acc {}) {b0} b3 {} hc)",
        zcontract(b0, b0, "qw"),
        collapse("b3")
    );
    let s2 = format!(
        "(Eq.substType KExpr (fun (qw : KExpr) => whnf_acc {}) {b0} b2 {} {s1})",
        zcontract(b0, "qw", "b3"),
        collapse("b2")
    );
    let s3 = format!(
        "(Eq.substType KExpr (fun (qw : KExpr) => whnf_acc {}) {b0} b1 {} {s2})",
        zcontract("qw", "b2", "b3"),
        collapse("b1")
    );
    format!(
        "fun (hc : whnf_acc {}) => candExp_iota_natrec_zero (fun (e : KExpr) => whnf_acc e) isCand_whnfAcc {b0} cand_var_witness {b0} cand_var_witness {b0} cand_var_witness (fun (b1 : KExpr) (hb1 : betaStar {b0} b1) (b2 : KExpr) (hb2 : betaStar {b0} b2) (b3 : KExpr) (hb3 : betaStar {b0} b3) => {s3})",
        zcontract(b0, b0, b0)
    )
}

pub fn ty_natrec_stuck_cand_mem() -> String {
    format!(
        "forall (S : KExpr -> Type), IsCandSet S -> forall (i : Nat) (j : Nat) (k : Nat) (l : Nat), S {}",
        sp(&[
            "(KExpr.bvar i)",
            "(KExpr.bvar j)",
            "(KExpr.bvar k)",
            "(KExpr.bvar l)"
        ])
    )
}

pub fn val_natrec_stuck_cand_mem() -> String {
    let args = [
        "(KExpr.bvar i)",
        "(KExpr.bvar j)",
        "(KExpr.bvar k)",
        "(KExpr.bvar l)",
    ];
    let r = sp(&args);
    let idxs = ["i", "j", "k", "l"];
    let cong = |slot: usize| {
        let mut repl: Vec<&str> = args.to_vec();
        repl[slot] = "qy";
        format!(
            "(fun (qy : KExpr) (hy : beta_reduces {} qy) (_heq : Eq KExpr e2 {}) => no_whnf_step_bvar {} qy (S e2) (whnf_step.beta {} qy hy))",
            args[slot],
            sp(&repl),
            idxs[slot],
            args[slot]
        )
    };
    let k_iota = format!(
        "(fun (hio : iota_reduces {r} e2) => option_none_ne_some_type KExpr e2 (S e2) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct (red_rec the_red_env) {r}) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) {r}) (OptionType.none KExpr) (natRecV_iota_none {} {} {} l)) (iota_reduces_to_step {r} e2 hio)))",
        args[0], args[1], args[2]
    );
    format!(
        "fun (S : KExpr -> Type) (hS : IsCandSet S) (i : Nat) (j : Nat) (k : Nat) (l : Nat) => isCandSet_cr3 S hS {r} ConstFreeUnit.triv (fun (e2 : KExpr) (hstep : whnf_step {r} e2) => natRecSpine4_whnf_inv {} {} {} {} e2 (S e2) hstep {} {} {} {} {k_iota})",
        args[0],
        args[1],
        args[2],
        args[3],
        cong(0),
        cong(1),
        cong(2),
        cong(3)
    )
}

pub fn ty_natrec_stuck_witness() -> String {
    let b0 = "(KExpr.bvar Nat.zero)";
    format!("whnf_acc {}", sp(&[b0, b0, b0, b0]))
}
pub const VAL_NATREC_STUCK_WITNESS: &str = "natRecStuck_cand_mem (fun (e : KExpr) => whnf_acc e) isCand_whnfAcc Nat.zero Nat.zero Nat.zero Nat.zero";

// ==== R3 SOURCES END ====

impl Specification {
    /// R3: the applied const spine — applied-delta transport + engine, and the
    /// `Nat.rec`-at-`Nat.zero` iota engine with its complete four-argument
    /// spine reduct classification.
    pub(super) fn add_candmodel_construct_r3(&mut self) -> Result<(), SpecError> {
        // --- Group B: the applied-delta story ---
        self.add_definition(SpecDefinition {
            name: "r3_opt_bind_id".to_string(),
            type_src: TY_R3_OPT_BIND_ID.to_string(),
            value_src: Some(VAL_R3_OPT_BIND_ID.to_string()),
            is_axiom: false,
            description: "Monad right-identity at OptionType KExpr: opt_bind o some = o, by \
                          OptionType.rec with a PLAIN Eq motive, both arms Eq.refl. Exists so \
                          delta_app_lift needs no case analysis of its own: the applied-delta \
                          transport is then a single Eq.cong over the whole option. PROP/TYPE \
                          NOTE (measured 2026-08-24): the first R3 attempt case-split inside the \
                          transport and closed the none arm with option_none_ne_some_type at the \
                          Prop goal — but that lemma's C is (C : Type) and the spec's Eq is Prop, \
                          which a non-cumulative kernel rejects as 'expected Sort(Succ(Zero)), \
                          got universe level conflict: 0 vs 1'. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_bind".to_string(),
                "OptionType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "delta_app_lift".to_string(),
            type_src: TY_DELTA_APP_LIFT.to_string(),
            value_src: Some(val_delta_app_lift()),
            is_axiom: false,
            description: "THE APPLIED-DELTA TRANSPORT (R3-A, settled from source): delta fires \
                          under an application spine. delta_reduct looks the definition name up \
                          at kapp_fn e — the SPINE HEAD — and re-applies kapp_args e, so a bare \
                          const's delta step lifts to any one-argument spine: \
                          delta_step env (const c us) v gives delta_step env (app (const c us) a) \
                          (app v a). Proof: r3_opt_bind_id turns the bare-const step into the \
                          plain lookup equation defval_for env c = some v, then ONE Eq.cong under \
                          (fun o => opt_bind o (fun x => some (app x a))) — whose value at \
                          some v computes to some (app v a), the applied reduct. No case \
                          analysis, no Type-valued eliminator, generic in the DefEnv. Corrects \
                          the natural reading of R2's 'delta fires only at the ROOT': the root \
                          must be the SPINE, but the spine head is reachable — what has no \
                          congruence is delta into a non-spine subterm. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_step".to_string(),
                "delta_reduct".to_string(),
                "defval_for".to_string(),
                "opt_bind".to_string(),
                "r3_opt_bind_id".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "r3_appliedDelta_witness".to_string(),
            type_src: TY_R3_APPLIED_DELTA_WITNESS.to_string(),
            value_src: Some(VAL_R3_APPLIED_DELTA_WITNESS.to_string()),
            is_axiom: false,
            description: "Discriminating witness (§6.1): a REAL applied-delta step on the \
                          reflected kernel env — the outermost DefEnv entry \
                          def_env_lift_closed_b, applied to (bvar 0), unfolds to its reflected \
                          value applied to the same argument. Built by delta_app_lift from the \
                          existing Guard-4 bare-const step (the_red_env_delta_nonvacuous), so it \
                          computes no new reduction and fails CLOSED if the reflection moves. \
                          This is the empirical half of the delta-under-a-spine settlement. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_app_lift".to_string(),
                "the_red_env_delta_nonvacuous".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "appConstAcc_reduct_acc".to_string(),
            type_src: TY_APPCONST_ACC_REDUCT_ACC.to_string(),
            value_src: Some(VAL_APPCONST_ACC_REDUCT_ACC.to_string()),
            is_axiom: false,
            description: "Premise-necessity guard for the applied-delta engine (the R3 mirror of \
                          R2's constAcc_body_acc): SN of an applied delta redex FORCES SN of the \
                          applied unfolding, since the lifted delta step is one whnf_step. So no \
                          engine variant may drop the family premise. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_app_lift".to_string(),
                "whnfAcc_inv_step".to_string(),
                "delta_step_to_reduces".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "constApp1_beta_inv".to_string(),
            type_src: ty_constapp1_beta_inv(),
            value_src: Some(val_constapp1_beta_inv()),
            is_axiom: false,
            description: "Complete beta_reduces reduct classification of a ONE-argument const \
                          spine app (const c us) arg0, in CPS: either the argument steps (the \
                          app_right congruence) or the whole spine iota-fires. 15-arm \
                          beta_reduces.rec; the head is a bare const so const_ne_lam kills the \
                          top-beta arm and r2_const_no_beta_reduces kills app_left; every \
                          non-app source dies by lam/pi/let/proj_ne_app. The iota arm is LIVE \
                          (generic c may be a recursor), delivered to a continuation rather than \
                          refuted. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces".to_string(),
                "beta_reduces.rec".to_string(),
                "r2_const_no_beta_reduces".to_string(),
                "const_ne_lam".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "constApp1_whnf_inv".to_string(),
            type_src: ty_constapp1_whnf_inv(),
            value_src: Some(val_constapp1_whnf_inv()),
            is_axiom: false,
            description: "The whnf_step classification of a one-argument const spine: the \
                          beta_reduces legs of constApp1_beta_inv plus a LIVE delta leg (the \
                          spine head is a const, so delta genuinely fires — this is exactly the \
                          leg R2's bare-const inverter had and the lam/let-headed R1 inverters \
                          did not). Three continuations: argument step, iota, delta. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "constApp1_beta_inv".to_string(),
                "whnf_step".to_string(),
                "delta_reduces_to_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "candExp_delta_app".to_string(),
            type_src: ty_candexp_delta_app(),
            value_src: Some(val_candexp_delta_app()),
            is_axiom: false,
            description: "THE APPLIED-DELTA ENGINE (R3-A): any candidate set absorbs an applied \
                          const spine whose head delta-unfolds into the set. Premises: the bare \
                          head's delta step, iota-deadness of the spine along every \
                          betaStar-development of the argument (refl-true at any non-recursor \
                          head), SN of the argument, and membership of the applied unfolding for \
                          every development. cr3 applies because app is Neutral; one Acc \
                          induction on the argument covers the app_right congruence; the delta \
                          leg is closed by delta_app_lift plus delta determinism. Model- \
                          independent (per-set, any IsCandSet). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "isCandSet_cr3".to_string(),
                "constApp1_whnf_inv".to_string(),
                "delta_app_lift".to_string(),
                "delta_step_deterministic".to_string(),
                "betaStar".to_string(),
                "whnf_acc.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "r3_deltaApp_iota_dead".to_string(),
            type_src: TY_R3_DELTAAPP_IOTA_DEAD.to_string(),
            value_src: Some(VAL_R3_DELTAAPP_IOTA_DEAD.to_string()),
            is_axiom: false,
            description: "Refl over the real env: the Guard-4 delta head is not a recursor, so \
                          its one-argument spine never iota-fires — for EVERY argument, since \
                          iota_reduct stops at the recmeta_for lookup. This discharges \
                          candExp_delta_app's iota premise at a real reflected constant, showing \
                          that premise is satisfiable and not a hidden vacuity. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "the_red_env".to_string(),
                "kcre_witness_delta_head".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "r3_deltaApp_concrete".to_string(),
            type_src: TY_R3_DELTAAPP_CONCRETE.to_string(),
            value_src: Some(VAL_R3_DELTAAPP_CONCRETE.to_string()),
            is_axiom: false,
            description: "One CONCRETE applied-delta run of the engine at the real reflected \
                          constant def_env_lift_closed_b applied to (bvar 0): every premise is \
                          discharged — the delta step from the Guard-4 witness, iota-deadness by \
                          refl, argument SN by R0's cand_var_witness, and the family collapsed \
                          with R1's betaStar_bvar_collapse — EXCEPT strong normalization of the \
                          value applied to the argument, which is CARRIED. That hypothesis is \
                          not an oversight: the reflected DefEnv values are lambdas whose bodies \
                          mention further delta-live constants, so their SN is a fundamental- \
                          theorem obligation (design rungs R5/R6), not an R3 brick. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "candExp_delta_app".to_string(),
                "r3_deltaApp_iota_dead".to_string(),
                "the_red_env_delta_nonvacuous".to_string(),
                "cand_var_witness".to_string(),
                "betaStar_bvar_collapse".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group C: the Nat.rec spine inversions ---
        for n in 1usize..=4 {
            self.add_definition(SpecDefinition {
                name: format!("natRecSpine{n}_beta_inv"),
                type_src: ty_natrec_spine_beta_inv(n),
                value_src: Some(val_natrec_spine_beta_inv(n)),
                is_axiom: false,
                description: format!(
                    "Complete beta_reduces reduct classification of the {n}-argument reflected \
                     Nat.rec spine, in CPS: exactly one argument steps{}. 15-arm \
                     beta_reduces.rec; the app_left arm {}; every non-app source dies by \
                     lam/pi/let/proj_ne_app. {} AccWType's wRecSpine1/2_step_inv idiom, at the \
                     LIVE reflected recursor name instead of a fresh one. Zero axiom_deps.",
                    if n == 4 { ", or the spine iota-fires" } else { "" },
                    if n == 1 {
                        "dies by r2_const_no_beta_reduces (a bare const takes no beta step)"
                    } else {
                        "recurses into the next shorter spine inversion and re-applies the trailing argument"
                    },
                    if n == 4 {
                        "The iota arm is LIVE and delivered to a continuation — at arity 4 the \
                         major-premise slot is filled, so a canonical major genuinely fires."
                    } else {
                        "The iota arm is killed COMPUTATIONALLY: at arity below 4 the \
                         major-premise slot (list_head (list_drop 3 args)) is none, so \
                         iota_reduct computes to none by Eq.refl for ANY arguments."
                    }
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "beta_reduces".to_string(),
                    "beta_reduces.rec".to_string(),
                    "app_inj_fst".to_string(),
                    "app_inj_snd".to_string(),
                    "lam_ne_app".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }
        self.add_definition(SpecDefinition {
            name: "natRecSpine4_delta_none".to_string(),
            type_src: ty_natrec_spine4_delta_none(),
            value_src: Some(VAL_NATREC_SPINE4_DELTA_NONE.to_string()),
            is_axiom: false,
            description: "Refl over the real env: the reflected Nat.rec is NOT delta-defined \
                          (defval_for has no kcre_name_27 entry), so a Nat.rec spine's whnf \
                          delta leg is dead — for any arguments, since delta_reduct only reads \
                          the spine head. Without this the four-argument reduct classification \
                          would be incomplete. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_reduct".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "natRecSpine4_whnf_inv".to_string(),
            type_src: ty_natrec_spine4_whnf_inv(),
            value_src: Some(val_natrec_spine4_whnf_inv()),
            is_axiom: false,
            description: "THE four-argument Nat.rec spine whnf_step classification: five \
                          continuations (a step in any of the four arguments, or an iota fire), \
                          with the delta leg refuted by natRecSpine4_delta_none. This is the \
                          single inversion both R3 routes run on — the iota ENGINE consumes its \
                          iota continuation, and the stuck-major guard REFUTES it. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "natRecSpine4_beta_inv".to_string(),
                "natRecSpine4_delta_none".to_string(),
                "whnf_step".to_string(),
                "delta_reduces_to_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group D: the iota fires over the real env ---
        self.add_definition(SpecDefinition {
            name: "natRecZ_iota_fires".to_string(),
            type_src: ty_natrecz_iota_fires(),
            value_src: Some(val_natrecz_iota_fires()),
            is_axiom: false,
            description: "THE LIVE IOTA FIRE, generic in the motive and both minors: the \
                          reflected Nat.rec applied to any three arguments and the reflected \
                          Nat.zero constructor iota-reduces to the REAL zero-rule RHS applied to \
                          those three arguments. One Eq.refl over the real env — iota_reduct \
                          inspects only the spine head, the arity, and the major's head const, \
                          never the arguments, so no substitution transport is needed. The \
                          contractum's RHS is PROJECTED (kapp_fn of the generated Guard-4 iota \
                          reduct), never a hand-copied reflected literal. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_step".to_string(),
                "iota_reduct".to_string(),
                "the_red_env".to_string(),
                "kcre_witness_nat_zero_reduct".to_string(),
                "kapp_fn".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "natRecS_iota_fires".to_string(),
            type_src: ty_natrecs_iota_fires(),
            value_src: Some(val_natrecs_iota_fires()),
            is_axiom: false,
            description: "The SUCCESSOR-major iota fire, generic in the motive, both minors and \
                          the numeral predecessor: Nat.rec applied through a Nat.succ-headed \
                          major reduces to the REAL successor-rule RHS applied to the three \
                          prefix arguments and the predecessor. One Eq.refl; the successor RHS \
                          is projected out of a closed probe's own iota reduct with a bare \
                          OptionType.rec, so nothing is hand-copied. R3 lands the FIRE but not \
                          the successor ENGINE: the successor major itself steps (app_right into \
                          the predecessor), so its engine needs a fourth accessibility layer — \
                          that is R4, and it inherits this equation. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_step".to_string(),
                "iota_reduct".to_string(),
                "the_red_env".to_string(),
                "kapp_fn".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "natRecSuccZero_iota_fires".to_string(),
            type_src: ty_natrec_succzero_iota_fires(),
            value_src: Some(VAL_NATREC_SUCCZERO_IOTA_FIRES.to_string()),
            is_axiom: false,
            description: "Discriminating witness (§6.1): the iota fire at a CONCRETE NUMERAL \
                          major — Nat.rec at (Nat.succ Nat.zero), i.e. the numeral 1. The \
                          positive half of the necessity pair whose negative half is \
                          natRecV_iota_none (a stuck major does NOT fire). Instance of \
                          natRecS_iota_fires, so it computes nothing new. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["natRecS_iota_fires".to_string()])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "natRecV_iota_none".to_string(),
            type_src: ty_natrecv_iota_none(),
            value_src: Some(VAL_NATRECV_IOTA_NONE.to_string()),
            is_axiom: false,
            description: "THE NECESSITY GUARD (§6.1), negative half: a STUCK major does not fire \
                          iota. With a bvar in the major-premise slot, kexpr_const_name of the \
                          major's head is none and iota_reduct computes to none by refl — for \
                          any motive, minors and index. This is what makes the canonicity \
                          premise of the engine load-bearing rather than decorative. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group E: the iota engine ---
        self.add_definition(SpecDefinition {
            name: "candExp_iota_natrec_zero".to_string(),
            type_src: ty_candexp_iota_natrec_zero(),
            value_src: Some(val_candexp_iota_natrec_zero()),
            is_axiom: false,
            description: "THE IOTA ENGINE (R3-B): any candidate set absorbs the reflected \
                          Nat.rec applied to a strongly-normalizing motive and two \
                          strongly-normalizing minors at the canonical Nat.zero major, given \
                          membership of the zero-rule contractum for every betaStar development \
                          of those three arguments. cr3 applies because an application spine is \
                          Neutral; a TRIPLE nested Acc induction (motive, then first minor, then \
                          second minor) covers the three congruence continuations of \
                          natRecSpine4_whnf_inv; the major's own continuation is refuted \
                          (Nat.zero is a bare const); and the iota continuation is closed by \
                          natRecZ_iota_fires plus some-injectivity. Port of the corpus \
                          red_natrec_core (StratifiedU/DataCand.lean) to the REAL reflected \
                          recursor. SCOPE: one family, one canonical major — the Nat.succ \
                          engine and all generic/indexed/mutual shapes are R4. This does NOT \
                          discharge CandModel.redRecGen and makes no claim on the M hypothesis \
                          of whnf_terminates_well_typed_dependent. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "isCandSet_cr3".to_string(),
                "natRecSpine4_whnf_inv".to_string(),
                "natRecZ_iota_fires".to_string(),
                "betaStar".to_string(),
                "whnf_acc.rec".to_string(),
                "option_some_inj".to_string(),
                "r2_const_no_beta_reduces".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group F: the discriminating witnesses ---
        self.add_definition(SpecDefinition {
            name: "natRecZ_contract_acc_necessary".to_string(),
            type_src: ty_natrecz_contract_acc_necessary(),
            value_src: Some(val_natrecz_contract_acc_necessary()),
            is_axiom: false,
            description: "Premise-necessity guard (§6.1): SN of the Nat.rec/Nat.zero redex \
                          FORCES SN of the zero-rule contractum, because the iota fire is one \
                          whnf_step. So the engine's contractum-family premise cannot be \
                          weakened away, and together with candExp_iota_natrec_zero it makes the \
                          two an equivalence at every argument triple. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "natRecZ_iota_fires".to_string(),
                "whnfAcc_inv_step".to_string(),
                "iota_step_to_reduces".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "natRecZ_engine_concrete".to_string(),
            type_src: ty_natrecz_engine_concrete(),
            value_src: Some(val_natrecz_engine_concrete()),
            is_axiom: false,
            description: "One CONCRETE run of the iota engine at the base whole-SN candidate \
                          set with all three arguments the variable (bvar 0): the accessibility \
                          premises come from R0's cand_var_witness and the contractum family \
                          collapses through R1's betaStar_bvar_collapse, leaving exactly one \
                          CARRIED hypothesis — SN of the real zero-rule RHS applied to the three \
                          arguments. That is deliberate and stated: the reflected RHS is a \
                          three-lambda whose spine is not a head redex, so its SN needs the \
                          Pi-candidate machinery of design rungs R4/R5, not an R3 brick. The \
                          UNCONDITIONAL positive membership this rung lands is instead \
                          natRecStuck_witness. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "candExp_iota_natrec_zero".to_string(),
                "cand_var_witness".to_string(),
                "isCand_whnfAcc".to_string(),
                "betaStar_bvar_collapse".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "natRecStuck_cand_mem".to_string(),
            type_src: ty_natrec_stuck_cand_mem(),
            value_src: Some(val_natrec_stuck_cand_mem()),
            is_axiom: false,
            description: "THE NECESSITY GUARD (§6.1), positive half and the CR3-NEUTRAL ROUTE: \
                          every candidate set contains the fully stuck four-argument Nat.rec \
                          spine (all four slots variables). The redex is Neutral and has NO \
                          whnf_step at all — the four congruence continuations die by \
                          no_whnf_step_bvar, the delta leg by natRecSpine4_delta_none, and the \
                          iota continuation is REFUTED by natRecV_iota_none rather than \
                          consumed. So this membership goes through cr3 alone, on a route \
                          visibly distinct from the iota engine's. The R3 analogue of R0's \
                          cand_var_mem, at an applied recursor head. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "isCandSet_cr3".to_string(),
                "natRecSpine4_whnf_inv".to_string(),
                "natRecV_iota_none".to_string(),
                "no_whnf_step_bvar".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "natRecStuck_witness".to_string(),
            type_src: ty_natrec_stuck_witness(),
            value_src: Some(VAL_NATREC_STUCK_WITNESS.to_string()),
            is_axiom: false,
            description: "The UNCONDITIONAL positive discriminating witness of R3: a concrete \
                          four-argument reflected Nat.rec spine is in the base whole-SN \
                          candidate set, derived THROUGH the interface (natRecStuck_cand_mem at \
                          isCand_whnfAcc), exercising the cr3 face that a degenerate Empty-style \
                          set would fail — at a term whose head is a LIVE recursor of the real \
                          reflected kernel env. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "natRecStuck_cand_mem".to_string(),
                "isCand_whnfAcc".to_string(),
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

    /// Paren-aware extraction of the `c_index`-th argument of every
    /// application of `elim` in `src` (0-based, counting from the first
    /// argument after the head). Used by the PROP/TYPE pin.
    fn type_valued_c_slots(src: &str, elim: &str, c_index: usize) -> Vec<String> {
        let bytes: Vec<char> = src.chars().collect();
        let mut out = Vec::new();
        let mut from = 0usize;
        while let Some(rel) = src[from..].find(elim) {
            let start = from + rel;
            from = start + elim.len();
            // Must be a whole token.
            let before_ok =
                start == 0 || !src[..start].ends_with(|c: char| c.is_alphanumeric() || c == '_');
            let after = src[start + elim.len()..].chars().next();
            if !before_ok || after != Some(' ') {
                continue;
            }
            // Walk the argument list from just after the head.
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

    /// Every (name, type, value) triple registered via `add_definition`, in
    /// registration order.
    fn theorem_sources() -> Vec<(String, String, String)> {
        let mut v: Vec<(String, String, String)> = vec![
            (
                "r3_opt_bind_id".to_string(),
                TY_R3_OPT_BIND_ID.to_string(),
                VAL_R3_OPT_BIND_ID.to_string(),
            ),
            (
                "delta_app_lift".to_string(),
                TY_DELTA_APP_LIFT.to_string(),
                val_delta_app_lift(),
            ),
            (
                "r3_appliedDelta_witness".to_string(),
                TY_R3_APPLIED_DELTA_WITNESS.to_string(),
                VAL_R3_APPLIED_DELTA_WITNESS.to_string(),
            ),
            (
                "appConstAcc_reduct_acc".to_string(),
                TY_APPCONST_ACC_REDUCT_ACC.to_string(),
                VAL_APPCONST_ACC_REDUCT_ACC.to_string(),
            ),
            (
                "constApp1_beta_inv".to_string(),
                ty_constapp1_beta_inv(),
                val_constapp1_beta_inv(),
            ),
            (
                "constApp1_whnf_inv".to_string(),
                ty_constapp1_whnf_inv(),
                val_constapp1_whnf_inv(),
            ),
            (
                "candExp_delta_app".to_string(),
                ty_candexp_delta_app(),
                val_candexp_delta_app(),
            ),
            (
                "r3_deltaApp_iota_dead".to_string(),
                TY_R3_DELTAAPP_IOTA_DEAD.to_string(),
                VAL_R3_DELTAAPP_IOTA_DEAD.to_string(),
            ),
            (
                "r3_deltaApp_concrete".to_string(),
                TY_R3_DELTAAPP_CONCRETE.to_string(),
                VAL_R3_DELTAAPP_CONCRETE.to_string(),
            ),
        ];
        for n in 1usize..=4 {
            v.push((
                format!("natRecSpine{n}_beta_inv"),
                ty_natrec_spine_beta_inv(n),
                val_natrec_spine_beta_inv(n),
            ));
        }
        v.push((
            "natRecSpine4_delta_none".to_string(),
            ty_natrec_spine4_delta_none(),
            VAL_NATREC_SPINE4_DELTA_NONE.to_string(),
        ));
        v.push((
            "natRecSpine4_whnf_inv".to_string(),
            ty_natrec_spine4_whnf_inv(),
            val_natrec_spine4_whnf_inv(),
        ));
        v.push((
            "natRecZ_iota_fires".to_string(),
            ty_natrecz_iota_fires(),
            val_natrecz_iota_fires(),
        ));
        v.push((
            "natRecS_iota_fires".to_string(),
            ty_natrecs_iota_fires(),
            val_natrecs_iota_fires(),
        ));
        v.push((
            "natRecSuccZero_iota_fires".to_string(),
            ty_natrec_succzero_iota_fires(),
            VAL_NATREC_SUCCZERO_IOTA_FIRES.to_string(),
        ));
        v.push((
            "natRecV_iota_none".to_string(),
            ty_natrecv_iota_none(),
            VAL_NATRECV_IOTA_NONE.to_string(),
        ));
        v.push((
            "candExp_iota_natrec_zero".to_string(),
            ty_candexp_iota_natrec_zero(),
            val_candexp_iota_natrec_zero(),
        ));
        v.push((
            "natRecZ_contract_acc_necessary".to_string(),
            ty_natrecz_contract_acc_necessary(),
            val_natrecz_contract_acc_necessary(),
        ));
        v.push((
            "natRecZ_engine_concrete".to_string(),
            ty_natrecz_engine_concrete(),
            val_natrecz_engine_concrete(),
        ));
        v.push((
            "natRecStuck_cand_mem".to_string(),
            ty_natrec_stuck_cand_mem(),
            val_natrec_stuck_cand_mem(),
        ));
        v.push((
            "natRecStuck_witness".to_string(),
            ty_natrec_stuck_witness(),
            VAL_NATREC_STUCK_WITNESS.to_string(),
        ));
        v
    }

    /// Parse-check every generated source — the fast guard for the commonest
    /// failure class (syntax-level assembly mistakes invisible to cargo
    /// check), doubly important here because every inversion is
    /// `format!`-assembled from a shared 15-arm scaffold.
    #[test]
    fn test_candmodel_r3_sources_parse() {
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
    fn test_candmodel_r3_sources_paren_balanced() {
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

    /// Shape guards. (1) Every reflected atom is a generated `kcre_*` name and
    /// the contractum RHSs are PROJECTIONS, never hand-copied literals.
    /// (2) The four-argument spine inversion keeps its iota arm LIVE while the
    /// three shorter ones kill theirs computationally. (3) The whnf
    /// classification refutes its delta leg through `natRecSpine4_delta_none`,
    /// not through the head-none absurdity (a Nat.rec spine HAS a const head).
    /// (4) The engine really is a triple Acc nesting over the three
    /// non-major arguments. (5) The necessity guard runs the OTHER route:
    /// `natRecStuck_cand_mem` refutes the iota continuation and consumes no
    /// fire. (6) The applied-delta engine consumes `delta_app_lift`, so R3-A
    /// is the transport, not a composite. (7) RECURSOR-SHAPE PIN: R3 registers
    /// no new inductive and no new plain def, so the measured
    /// uniform-leading-argument recursor promotion cannot fire here.
    #[test]
    fn test_candmodel_r3_shape_guards() {
        // (1)
        assert!(RHSZ.contains("kapp_fn kcre_witness_nat_zero_reduct"));
        assert!(rhss().contains("iota_reduct (red_rec the_red_env)"));
        assert!(rhss().contains(SUCC_PROBE));
        for atom in [NREC, NZERO, NSUCC] {
            assert!(
                atom.contains("kcre_name_"),
                "{atom} must be a generated atom"
            );
        }
        // (2)
        for n in 1usize..=3 {
            let v = val_natrec_spine_beta_inv(n);
            assert!(
                !v.contains("kIota"),
                "natRecSpine{n}_beta_inv must kill its iota arm computationally"
            );
            assert_eq!(
                v.matches("option_none_ne_some_type").count(),
                1,
                "natRecSpine{n}_beta_inv must refute iota exactly once"
            );
        }
        let v4 = val_natrec_spine_beta_inv(4);
        assert!(
            v4.contains("kIota (Eq.substType"),
            "natRecSpine4_beta_inv must pass its LIVE iota arm to the continuation"
        );
        assert!(
            !v4.contains("option_none_ne_some_type"),
            "natRecSpine4_beta_inv must NOT refute iota — at arity 4 it genuinely fires"
        );
        // (3)
        let w4 = val_natrec_spine4_whnf_inv();
        assert!(
            w4.contains("natRecSpine4_delta_none"),
            "the whnf classification must refute delta through the refl-computed env fact"
        );
        assert!(
            !w4.contains("delta_step_head_none_absurd"),
            "a Nat.rec spine HAS a const head — the head-none absurdity is the wrong refutation"
        );
        // (4)
        let eng = val_candexp_iota_natrec_zero();
        assert_eq!(
            eng.matches("whnf_acc.rec").count(),
            3,
            "the iota engine must be a triple Acc nesting (motive, minor 0, minor 1)"
        );
        assert_eq!(
            eng.matches("natRecZ_iota_fires").count(),
            1,
            "the iota engine must consume the fire exactly once"
        );
        assert!(
            eng.contains("r2_const_no_beta_reduces kcre_name_18"),
            "the major continuation must be refuted: Nat.zero is a bare const"
        );
        // (5)
        let stuck = val_natrec_stuck_cand_mem();
        assert!(
            stuck.contains("natRecV_iota_none"),
            "the necessity guard must REFUTE the iota continuation"
        );
        assert!(
            !stuck.contains("natRecZ_iota_fires") && !stuck.contains("natRecS_iota_fires"),
            "the necessity guard must consume no iota fire — that is the point of the route"
        );
        assert_eq!(
            stuck.matches("no_whnf_step_bvar").count(),
            4,
            "all four argument continuations must die at a variable"
        );
        // (6)
        assert!(
            val_candexp_delta_app().contains("delta_app_lift"),
            "the applied-delta engine must close its delta leg with the transport"
        );
        assert!(
            val_delta_app_lift().contains("r3_opt_bind_id")
                && val_delta_app_lift().contains("Eq.cong"),
            "delta_app_lift must be the right-identity + single Eq.cong composition"
        );
        assert!(
            !val_delta_app_lift().contains("OptionType.rec"),
            "delta_app_lift must do NO case analysis of its own — that is r3_opt_bind_id's job"
        );
        // (7b) ARM-ARITY PIN, from the second measured 2026-08-24 failure
        // (`cannot unify expressions of different shape: Discriminant(6) vs
        // Discriminant(4)` in the lam_ty arm). Every 15-arm `beta_reduces.rec`
        // must bind the RECURSIVE PREMISE of each recursive minor, not just its
        // fields and IH: 10 structural minors (lam_ty, lam_body, pi_dom,
        // pi_cod, forall_dom, forall_cod, let_ty, let_val, let_body, proj) plus
        // the 2 live app congruences = 12 premise binders; beta/zeta/iota take
        // none of this kind.
        let inversions: Vec<(String, String)> = (1usize..=4)
            .map(|n| {
                (
                    format!("natRecSpine{n}_beta_inv"),
                    val_natrec_spine_beta_inv(n),
                )
            })
            .chain(std::iter::once((
                "constApp1_beta_inv".to_string(),
                val_constapp1_beta_inv(),
            )))
            .collect();
        for (name, v) in &inversions {
            assert_eq!(
                v.matches("(_qstep : beta_reduces ").count(),
                10,
                "{name}: each of the 10 recursive structural minors must bind its \
                 beta_reduces premise before its IH (measured failure 2026-08-24)"
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
        // (8) PROP/TYPE PIN, from the measured 2026-08-24 elaboration failure
        // (`expected Sort(Succ(Zero)), got universe level conflict: 0 vs 1`).
        // The spec's `Eq` is Prop and the kernel is NON-CUMULATIVE, so a
        // `(C : Type)`-parameterised CPS eliminator may never be instantiated
        // at an `Eq` goal. Check the C slot of every such application.
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
                             {c} — the spec's Eq is Prop and the kernel is non-cumulative \
                             (measured failure 2026-08-24). Route the absurdity through Empty \
                             first, or restructure so no Type-valued eliminator sees a Prop goal."
                        );
                    }
                }
            }
        }
        // (7)
        let src = include_str!("candmodel_construct_r3.rs");
        let body = src
            .split("pub(super) fn add_candmodel_construct_r3")
            .nth(1)
            .expect("the stage function must exist");
        let body = body.split("#[cfg(test)]").next().unwrap_or(body);
        assert!(
            !body.contains("self.add_inductive("),
            "RECURSOR-SHAPE PIN: R3 must register no new inductive"
        );
        assert!(
            !body.contains("self.add_recursive_def("),
            "RECURSOR-SHAPE PIN: R3 must register no new plain def"
        );
    }

    /// Registration + kernel re-verification against the substitution bundle:
    /// the stage registers every constant, and every theorem — both engines,
    /// the four spine inversions, the four real-env reduct facts, and all
    /// witnesses — re-typechecks in the live kernel environment.
    #[test]
    fn test_candmodel_r3_registered_and_reverifies() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();
        let names: Vec<String> = theorem_sources().into_iter().map(|(n, _, _)| n).collect();
        for name in &names {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the candmodel_construct_r3 stage"
            );
        }
        for name in &names {
            spec.verify_definition(name).unwrap_or_else(|e| {
                panic!("{name} should re-typecheck in the spec environment: {e:?}")
            });
        }
    }
}
