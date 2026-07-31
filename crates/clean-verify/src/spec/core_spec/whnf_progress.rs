// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MODEL-side progress / exit-shape lemma for WHNF over the const-free,
//! bvar-free fragment (Front-2 recursive-grounding, FIRST BRICK).
//!
//! This is the *specification* the future literal-whnf verification condition
//! discharges against — the model-level statement that the structural case
//! analysis performed by a recursive `whnf` is EXHAUSTIVE and that every shape
//! maps to a terminating exit. It is NOT literal-Rust grounding: no Rust term
//! is walked here; the content is the exit-shape closure over the abstract
//! `KExpr` model. Combined with the landed `beta_bd_sn` termination
//! (`beta_bd_sn.rs`, strong normalization of the iota-free `beta_reduces_bd`),
//! this brick supplies the PROGRESS half of "recursive whnf reaches a normal
//! form": every step either exposes a whnf exit or takes a strictly-smaller
//! `beta_reduces_bd` step.
//!
//! ## HONESTY: the naive 2-shape progress is FALSE on this fragment
//!
//! The scoping design proposed a 2-constructor witness `done (is_whnf e) |
//! step (whnf_step e e')` and T1 `const_free e -> bvar_ceiling e = 0 ->
//! whnf_progress_result e`. Verified against the LIVE model, that statement is
//! FALSE. Counterexample: `KExpr.app (KExpr.sort 0) (KExpr.sort 0)` is
//! const-free and bvar-free, yet
//!   * it is NOT `is_whnf`: the landed `is_whnf` admits `sort`/`lam`/`pi`/`lit`,
//!     projections over an `is_whnf` scrutinee, and `neutral e`, where
//!     `is_neutral` is a `const` or an application spine bottoming out at a
//!     `const`; with `const` excluded, `is_neutral` is UNINHABITED, and none of
//!     the remaining constructors classifies an application headed by `sort`;
//!   * it takes NO step: the head `sort 0` is not a `lam` (no beta redex) and
//!     neither `sort 0` nor the argument `sort 0` reduces.
//! So `app (non-lam value) (value)` is a genuine STUCK application — a normal
//! form that the narrow landed `is_whnf` fails to classify. Faking a 2-shape
//! progress here would be a masquerade.
//!
//! ## What this brick actually proves (honest scope)
//!
//! The witness `whnf_progress_result` carries THREE exit shapes, faithful to
//! what a recursive whnf actually stops on:
//!   * `done  (is_whnf e)`                — a genuine whnf value (sort/lam/pi,
//!     or a neutral spine — the landed predicate, unchanged);
//!   * `step  (beta_reduces_bd e e')`     — a single IOTA-FREE beta step (the
//!     EXACT relation `beta_bd_sn` terminates over — deliberate alignment,
//!     authorized in place of the design's `whnf_step`; a `beta_reduces_bd`
//!     step embeds into `whnf_step` via `whnf_step.beta` over the 13 non-iota
//!     `beta_reduces` constructors, so nothing is lost for the literal VC);
//!   * `stuck` / `stuck_proj`             — the honestly-NAMED residuals: an
//!     application whose head is a non-lambda normal form, or a projection over
//!     such a stuck scrutinee. These are the shapes the narrow `is_whnf` cannot
//!     express; surfacing them is the honest disclosure that a literal whnf's
//!     post-condition must account for both stuck forms, not just `is_whnf`.
//!
//! T1 `whnf_progress_bd` is then TOTAL and TRUE on the const-free bvar-free
//! fragment: `bvar_ceiling e = 0 -> const_free e -> whnf_progress_result e`,
//! by structural `KExpr.rec`. Zero new axioms; every value kernel-checked at
//! spec build (that is the witness).
//!
//! Proof skeleton (`KExpr.rec`, motive
//! `fun e => bvar_ceiling e = 0 -> const_free e -> whnf_progress_result e`):
//!   * `sort`/`lam`/`pi`  -> `done` via `is_whnf.sort/.lam/.pi`.
//!   * `bvar i`           -> vacuous: `bvar_ceiling (bvar i) = succ i`, so the
//!     ceiling-zero hypothesis is `succ i = 0`, refuted by `nat_zero_ne_succ`.
//!   * `const n us`       -> vacuous: `const_free (const n us)` reduces to
//!     `Empty`, eliminated by `Empty.rec`.
//!   * `let_ ty val body` -> `step` via `beta_reduces_bd.zeta` (a let_ is never
//!     a whnf/neutral — it is always a zeta redex-former; the whnf loop fires
//!     the top zeta unconditionally, no recursion into the components needed).
//!   * `app f a`          -> recurse on `f` (ceiling `f` from
//!     `nat_add_eq_zero_left`, `const_free f` from `AndType.left`), then case on
//!     the resulting `whnf_progress_result f`:
//!       - `step f f'`      -> `step` for `app f a` via `beta_reduces_bd.app_left`;
//!       - `stuck` head `g` -> `stuck` for `app (app g b) a` via
//!         `whnf_stuck_head.app`;
//!       - `done (is_whnf f)` -> case on `is_whnf f`:
//!           `lam ty body`  -> `step` via `beta_reduces_bd.beta` (the redex fires);
//!           `sort`/`pi`    -> `stuck` via `whnf_stuck_head.sort/.pi`;
//!           `neutral`      -> `done` for `app f a` via `is_neutral.app`
//!                             (vacuous in the const-free fragment, but the arm
//!                             is discharged without any `is_neutral.const` /
//!                             `const_whnf` reference, keeping the closure clean).
//!
//! ## T3 (whnf_normalizes) — DEFERRED, honest next step
//!
//! Composing progress with `beta_bd_acc` termination to conclude "whnf reaches
//! a normal form" is NOT landed this session. The relation alignment is
//! favourable — the `step` shape and `beta_bd_sn`'s `beta_bd_acc` are BOTH over
//! `beta_reduces_bd` — but the landed reflexive-transitive closure `whnf_to`
//! (`whnf_reduction.rs:243`) bakes `is_whnf` into its `refl` base, which does
//! NOT cover the `stuck` normal forms surfaced above. T3 therefore needs a
//! stuck-aware closure (`beta_bd_to`, `refl` over `is_whnf` OR
//! `whnf_stuck_head`) before it can be stated without a masquerade. That is the
//! next brick; see the returned report.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the const-free/bvar-free WHNF progress (exit-shape) brick.
    ///
    /// Must run after `add_whnf_reduction` (`is_whnf`/`is_neutral`),
    /// `add_expr_model` (`KExpr`/`KExpr.rec`), `add_expr_model_inst_ceiling`
    /// (`bvar_ceiling`), `add_par_reduction` (`beta_reduces_bd`),
    /// `add_iota_core` (`nat_zero_ne_succ`), `add_faithful_red_env`
    /// (`nat_add_eq_zero_left`), and the foundation layer (`Empty`/`AndType`).
    /// Purely additive; zero new axioms.
    pub(super) fn add_whnf_progress(&mut self) -> Result<(), SpecError> {
        self.add_whnf_progress_supports()?;
        self.add_whnf_progress_theorem()?;
        Ok(())
    }

    /// The const-free predicate, the stuck-head predicate, and the 3-shape
    /// progress witness.
    fn add_whnf_progress_supports(&mut self) -> Result<(), SpecError> {
        // ConstFreeUnit: a trivially-inhabited Type marker for the const-free
        // leaf cases (there is no `Unit`/`True` in the spec fragment, and the
        // Prop-sorted `Eq _ x x` cannot inhabit a `KExpr -> Type` arm).
        self.add_inductive(
            r"inductive ConstFreeUnit : Type
| triv : ConstFreeUnit",
            "Trivially-inhabited Type unit used as the const-free witness at sort/bvar leaves \
             (the fragment has no Unit/True, and Eq is Prop-sorted). Part of the WHNF \
             progress/exit-shape brick (Front-2 recursive grounding).",
        )?;

        // const_free e : the const-free predicate over KExpr as a recursive
        // Type-valued def. Reduces on constructors (KExpr.rec large elimination,
        // same shape as bvar_ceiling), so const_free (const n us) is Empty
        // (definitionally) and const_free (app f a) is AndType of the child
        // witnesses — used directly by the KExpr.rec proof below without any
        // unfolding lemma.
        self.add_recursive_def(
            r"def const_free (e : KExpr) : Type := KExpr.rec (fun (_ : KExpr) => Type) (fun (n : Level) => ConstFreeUnit) (fun (i : Nat) => ConstFreeUnit) (fun (f : KExpr) (a : KExpr) (cf : Type) (ca : Type) => AndType cf ca) (fun (ty : KExpr) (b : KExpr) (cty : Type) (cb : Type) => AndType cty cb) (fun (ty : KExpr) (b : KExpr) (cty : Type) (cb : Type) => AndType cty cb) (fun (n : Name) (us : ListType Level) => Empty) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (cty : Type) (cv : Type) (cb : Type) => AndType cty (AndType cv cb)) (fun (s : Name) (i : Nat) (sub : KExpr) (csub : Type) => csub) (fun (v : Nat) => ConstFreeUnit) e",
            "const_free e is inhabited iff e contains no KExpr.const head: ConstFreeUnit at \
             sort/bvar leaves, AndType of the child witnesses at app/lam/pi nodes (the \
             right-nested triple AndType cty (AndType cval cbody) at a let_ node, mirroring \
             the bvar_ceiling/closed_at_b component order), and Empty \
             at a const head (so a const term is provably NOT const-free). Recursive \
             Type-valued def, reduces on constructors. Part of the WHNF progress/exit-shape \
             brick (Front-2 recursive grounding).",
        )?;

        // whnf_stuck_head e : e is a whnf normal form that is NOT a lambda, so
        // applying it is stuck (no beta redex is exposed). In the const-free
        // bvar-free fragment these are exactly sort, pi, and application spines
        // over them — the residual the narrow landed is_whnf cannot classify.
        self.add_inductive(
            r"inductive whnf_stuck_head : KExpr → Type
| sort : forall (n : Level), whnf_stuck_head (KExpr.sort n)
| pi : forall (ty : KExpr) (body : KExpr), whnf_stuck_head (KExpr.pi ty body)
| app : forall (f : KExpr) (a : KExpr), whnf_stuck_head f → whnf_stuck_head (KExpr.app f a)
| proj : forall (s : Name) (i : Nat) (sub : KExpr), whnf_stuck_head sub → whnf_stuck_head (KExpr.proj s i sub)
| projw : forall (s : Name) (i : Nat) (sub : KExpr), is_whnf sub → whnf_stuck_head (KExpr.proj s i sub)
| lit : forall (v : Nat), whnf_stuck_head (KExpr.lit v)",
            "whnf_stuck_head e: e is a non-lambda normal form (a sort, pi, literal, or an \
             application/projection spine over a stuck or landed-WHNF head). In the const-free \
             bvar-free fragment, applying or projecting over the applicable stuck forms yields \
             normal forms the narrow landed is_whnf omits. The honestly-named residual of the \
             WHNF progress brick. MODEL-side exit shape, not literal-Rust grounding.",
        )?;

        // whnf_progress_result e : the 3-shape exit witness for one whnf layer.
        // done  — e is a landed is_whnf value;
        // step  — e takes a single IOTA-FREE beta_reduces_bd step (the exact
        //         relation beta_bd_sn terminates over);
        // stuck — e = app f a with a stuck (non-lambda whnf) head f;
        // stuck_proj — e = proj s i sub with a stuck scrutinee.
        self.add_inductive(
            r"inductive whnf_progress_result : KExpr → Type
| done : forall (e : KExpr), is_whnf e → whnf_progress_result e
| step : forall (e : KExpr) (e' : KExpr), beta_reduces_bd e e' → whnf_progress_result e
| stuck : forall (f : KExpr) (a : KExpr), whnf_stuck_head f → whnf_progress_result (KExpr.app f a)
| stuck_proj : forall (s : Name) (i : Nat) (sub : KExpr), whnf_stuck_head sub → whnf_progress_result (KExpr.proj s i sub)",
            "whnf_progress_result e packages the exit shape of one whnf layer over e without a \
             Sum/Sigma type (not in the current fragment): `done` a landed is_whnf value, \
             `step` a single iota-free beta_reduces_bd reduct (the relation beta_bd_sn \
             terminates over — chosen over whnf_step for exact termination alignment), or \
             `stuck`/`stuck_proj` for an application or projection over a non-lambda normal \
             form (whnf_stuck_head). The MODEL-side progress spec the future literal whnf VC cites; \
             NOT literal-Rust grounding. Part of the WHNF progress brick (Front-2).",
        )?;

        Ok(())
    }

    /// T1 `whnf_progress_bd` — total exit-shape progress on the const-free
    /// bvar-free fragment, by structural `KExpr.rec`.
    fn add_whnf_progress_theorem(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "whnf_progress_bd".to_string(),
            type_src: concat!(
                "forall (e : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> ",
                "whnf_progress_result e"
            )
            .to_string(),
            value_src: Some(whnf_progress_bd_proof()),
            is_axiom: false,
            description: concat!(
                "MODEL-side WHNF progress / exit-shape lemma (Front-2 recursive-grounding FIRST ",
                "BRICK): every const-free bvar-free KExpr exposes a whnf exit — a landed is_whnf ",
                "value (done), a single IOTA-FREE beta_reduces_bd step (step, the exact relation ",
                "beta_bd_sn terminates over), or a stuck application/projection residual ",
                "(stuck / stuck_proj / whnf_stuck_head). Structural KExpr.rec: sort/lam/pi/lit ",
                "are done; bvar is ",
                "refuted by nat_zero_ne_succ (bvar_ceiling (bvar i) = succ i vs the ceiling-zero ",
                "hypothesis); const is refuted by Empty.rec (const_free (const n us) = Empty); the ",
                "app node recurses on the head and dispatches beta (redex) / app_left (head steps) ",
                "/ stuck (non-lambda head) / neutral (is_neutral.app, vacuous but closure-clean); ",
                "the let_ node always steps by the top zeta (beta_reduces_bd.zeta — a let_ is ",
                "never a whnf/neutral, it is always a zeta redex-former). ",
                "The naive 2-shape `done | step` statement is FALSE here — app (sort 0)(sort 0) is ",
                "const-free, bvar-free, not is_whnf, and takes no step — so the `stuck` shape is a ",
                "REQUIRED, honestly-named residual, NOT a masquerade. This is the spec a literal ",
                "whnf VC discharges against, NOT literal-Rust grounding. DerivedProved, zero ",
                "axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr".to_string(),
                "KExpr.rec".to_string(),
                "bvar_ceiling".to_string(),
                "const_free".to_string(),
                "whnf_progress_result".to_string(),
                "whnf_progress_result.done".to_string(),
                "whnf_progress_result.step".to_string(),
                "whnf_progress_result.stuck".to_string(),
                "whnf_progress_result.stuck_proj".to_string(),
                "whnf_progress_result.rec".to_string(),
                "whnf_stuck_head".to_string(),
                "whnf_stuck_head.sort".to_string(),
                "whnf_stuck_head.pi".to_string(),
                "whnf_stuck_head.app".to_string(),
                "whnf_stuck_head.proj".to_string(),
                "whnf_stuck_head.projw".to_string(),
                "whnf_stuck_head.lit".to_string(),
                "is_whnf".to_string(),
                "is_whnf.sort".to_string(),
                "is_whnf.lam".to_string(),
                "is_whnf.pi".to_string(),
                "is_whnf.neutral".to_string(),
                "is_whnf.proj".to_string(),
                "is_whnf.lit".to_string(),
                "is_whnf.rec".to_string(),
                "is_neutral".to_string(),
                "is_neutral.app".to_string(),
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd.beta".to_string(),
                "beta_reduces_bd.app_left".to_string(),
                "beta_reduces_bd.proj".to_string(),
                "beta_reduces_bd.zeta".to_string(),
                "instantiate".to_string(),
                "nat_add_eq_zero_left".to_string(),
                "nat_zero_ne_succ".to_string(),
                "AndType.left".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnf_noredex_class: the NO-REDEX classification — exactly
        // whnf_progress_result WITHOUT the step arm. The conclusion shape of the
        // fixpoint-glue theorem below. Both honest stuck forms must remain here:
        // applications and projections over a stuck head.
        self.add_inductive(
            r"inductive whnf_noredex_class : KExpr → Type
| done : forall (e : KExpr), is_whnf e → whnf_noredex_class e
| stuck : forall (f : KExpr) (a : KExpr), whnf_stuck_head f → whnf_noredex_class (KExpr.app f a)
| stuck_proj : forall (s : Name) (i : Nat) (sub : KExpr), whnf_stuck_head sub → whnf_noredex_class (KExpr.proj s i sub)",
            "whnf_noredex_class e — the exit shape of a term with NO beta_reduces_bd reduct: \
             a landed is_whnf value, an application on a stuck head, or a projection over a \
             stuck head (the honest residuals). whnf_progress_result minus the step arm; the conclusion of \
             step_fixpoint_classifies_bd (the reducer-universal composition glue).",
        )?;

        // step_fixpoint_classifies_bd (the COMPOSITION GLUE, kernel-checked): a
        // const-free bvar-free term with NO beta_reduces_bd reduct is a landed
        // is_whnf value or the honest stuck residual. This is the model-side
        // implication that ties the LITERAL fixpoint-exit witness (the real
        // whnf_outer_loop returns only step-fixpoints — MIR-witnessed in
        // trust-certify) to WHNF-ness: fixpoint + progress ⟹ done-or-stuck.
        // Pure corollary of whnf_progress_bd: eliminate the progress witness with
        // a motive STRENGTHENED by the no-step hypothesis; the step arm is
        // refuted by Empty elimination.
        self.add_definition(SpecDefinition {
            name: "step_fixpoint_classifies_bd".to_string(),
            type_src: concat!(
                "forall (e : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> ",
                "(forall (e2 : KExpr), beta_reduces_bd e e2 -> Empty) -> whnf_noredex_class e"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (hb : Eq Nat (bvar_ceiling e) Nat.zero) (hc : const_free e) ",
                    "(hns : forall (e2 : KExpr), beta_reduces_bd e e2 -> Empty) => ",
                    "whnf_progress_result.rec ",
                    "(fun (e0 : KExpr) (w : whnf_progress_result e0) => ",
                    "(forall (e2 : KExpr), beta_reduces_bd e0 e2 -> Empty) -> whnf_noredex_class e0) ",
                    "(fun (e0 : KExpr) (h : is_whnf e0) ",
                    "(hn : forall (e2 : KExpr), beta_reduces_bd e0 e2 -> Empty) => ",
                    "whnf_noredex_class.done e0 h) ",
                    "(fun (e0 : KExpr) (e2 : KExpr) (hstep : beta_reduces_bd e0 e2) ",
                    "(hn : forall (e3 : KExpr), beta_reduces_bd e0 e3 -> Empty) => ",
                    "Empty.rec (fun (_ : Empty) => whnf_noredex_class e0) (hn e2 hstep)) ",
                    "(fun (f : KExpr) (a : KExpr) (hs : whnf_stuck_head f) ",
                    "(hn : forall (e2 : KExpr), beta_reduces_bd (KExpr.app f a) e2 -> Empty) => ",
                    "whnf_noredex_class.stuck f a hs) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (hs : whnf_stuck_head sub) ",
                    "(hn : forall (e2 : KExpr), beta_reduces_bd (KExpr.proj s i sub) e2 -> Empty) => ",
                    "whnf_noredex_class.stuck_proj s i sub hs) ",
                    "e (whnf_progress_bd e hb hc) hns"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "COMPOSITION GLUE (reducer universal): a const-free bvar-free KExpr with NO ",
                "beta_reduces_bd reduct is a landed is_whnf value or an honest stuck application/",
                "projection residual ",
                "(whnf_noredex_class). The model-side implication with which a literal ",
                "fixpoint-exit witness WOULD compose — the model-to-literal correspondence is ",
                "NOT kernel-checked and mints no literal-Rust authority (the reducer-universal ",
                "composite is quarantined to a validation artifact): ",
                "fixpoint of the step + progress => done-or-stuck. Pure corollary of ",
                "whnf_progress_bd via whnf_progress_result.rec with a no-step-strengthened ",
                "motive; the step arm is refuted by Empty elimination. DerivedProved, zero ",
                "axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_progress_bd".to_string(),
                "whnf_progress_result".to_string(),
                "whnf_progress_result.rec".to_string(),
                "whnf_noredex_class".to_string(),
                "whnf_noredex_class.done".to_string(),
                "whnf_noredex_class.stuck".to_string(),
                "whnf_noredex_class.stuck_proj".to_string(),
                "beta_reduces_bd".to_string(),
                "is_whnf".to_string(),
                "whnf_stuck_head".to_string(),
                "bvar_ceiling".to_string(),
                "const_free".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_mir_payload_reflection()?;
        self.add_mir_cfg_reachability()?;
        self.add_mir_dispatch_reflection()?;
        self.add_composite_lift()?;
        self.add_whnf_env_progress()?;
        self.add_consts_defined_progress()?;
        self.add_whnf_env_progress_full()?;
        self.add_env_fixpoint_classifies()?;
        self.add_red_step_progress()?;
        self.add_whnf_fuel_loop()?;
        self.add_whnf_fuel_theorems()?;
        self.add_reduce_once_sound()?;
        self.add_whnf_fuel_reaches_sound()?;
        self.add_def_env_good()?;
        self.add_reduce_once_converse()?;
        self.add_reduce_once_classifies()?;
        self.add_reduce_once_preserves_closed()?;
        self.add_whnf_fuel_capstone()?;
        self.add_reduce_once_red()?;
        self.add_reduce_once_red_head_facts()?;

        Ok(())
    }

    // X16c-3b — DEFINEDNESS PRESERVATION + THE CAPSTONE: every successful
    // fuel-loop result on a closed, fully-defined term over a good
    // environment CLASSIFIES as a landed weak-head value or the honest stuck
    // residual. The executable loop's verification circle CLOSES.

    /// X17 rung A (round-5 SpecRedLoop port, guide theorems
    /// reduceOnceRed_sound + the granularity dispatch): THE 3-WAY EXECUTABLE
    /// STEP over a combined RedEnv — β at a lam head, head recursion through
    /// the app spine with a WHOLE-SPINE ι fallback when the head is silent,
    /// ζ at a let, bare-const δ (definition component only — recursors are
    /// δ-opaque), proj-scrutinee congruence recursion, none at value leaves —
    /// plus the fuel loop over it and full step soundness against
    /// whnf_red_step. Classification/preservation (the EnvsGood ι-half) are
    /// the next rungs.
    /// Head-behaviour facts about the reflected one-step reducer.
    ///
    /// MUST be registered AFTER `add_reduce_once_red` — these reference
    /// `reduce_once_red` itself, and registering them alongside the MIR
    /// dispatch witnesses (which run 16 registrations earlier) fails with
    /// `Unknown identifier: reduce_once_red`.
    fn add_reduce_once_red_head_facts(&mut self) -> Result<(), SpecError> {
        // ── THE BEHAVIOURAL COUNTERPART ─────────────────────────────────────
        //
        // The two witnesses above are STRUCTURAL: they pin which ExprKind
        // variants the real dispatches list, and say nothing about what those
        // arms DO. These next facts are behavioural, about the reflected
        // reducer, and together with the structural half they make a
        // correspondence rather than two unrelated observations.
        //
        // `reduce_once_red` is a KExpr.rec whose arms are, in constructor order:
        //   sort -> none        app  -> reduce_app_head_red     let_ -> SOME (zeta)
        //   bvar -> none        pi   -> none                    proj -> opt_proj_lift
        //   lam  -> none        const-> defval_for              lit  -> none
        //
        // So the heads that are UNCONDITIONALLY irreducible — none for EVERY
        // RedEnv — are exactly {sort, bvar, lam, pi, lit}. That is precisely the
        // real kernel's identity set {2, 0, 5, 6, 8} pinned by
        // mir_dispatch_reflection_whnf_impl above: the reflected reducer takes no
        // step on exactly the heads the real whnf_impl returns unchanged.
        //
        // The distinction matters and is why "unconditionally" is load-bearing:
        // const and proj can ALSO yield none (a constant absent from the env, a
        // stuck projection), but only for some environments/subterms, so they are
        // not irreducible heads. Only these five are none independent of renv.
        //
        // Each is proved by KERNEL COMPUTATION: applying a KExpr.rec to a
        // constructor iota-reduces, so Eq.refl suffices and the kernel must do
        // the reduction to accept it.
        let irreducible: [(&str, &str, &str); 5] = [
            ("sort", "(n : Level)", "KExpr.sort n"),
            ("bvar", "(i : Nat)", "KExpr.bvar i"),
            ("lam", "(ty : KExpr) (b : KExpr)", "KExpr.lam ty b"),
            ("pi", "(ty : KExpr) (b : KExpr)", "KExpr.pi ty b"),
            ("lit", "(v : Nat)", "KExpr.lit v"),
        ];
        for (head, binders, ctor) in irreducible {
            let binder_names: Vec<&str> = binders
                .split(')')
                .filter_map(|b| b.trim().strip_prefix('('))
                .map(|b| b.split(':').next().unwrap_or("").trim())
                .collect();
            self.add_definition(SpecDefinition {
                name: format!("reduce_once_red_none_{head}"),
                type_src: format!(
                    "forall (renv : RedEnv) {binders}, \
                     Eq (OptionType KExpr) (reduce_once_red renv ({ctor})) (OptionType.none KExpr)"
                ),
                value_src: Some(format!(
                    "fun (renv : RedEnv) {binders} => \
                     Eq.refl (OptionType KExpr) (OptionType.none KExpr)"
                )),
                is_axiom: false,
                description: format!(
                    "reduce_once_red_none_{head}: the reflected one-step reducer takes NO step on \
                     a `{head}` head, for EVERY RedEnv — so `{head}` is an unconditionally \
                     irreducible (weak-head-normal) head. Behavioural counterpart to the \
                     structural dispatch witnesses: {{sort,bvar,lam,pi,lit}} is exactly the real \
                     kernel's identity set {{0,2,5,6,8}} pinned by \
                     mir_dispatch_reflection_whnf_impl. Contrast const/proj, which can also yield \
                     none but only for some environments/subterms. Proved by KERNEL COMPUTATION \
                     (KExpr.rec applied to a constructor iota-reduces; binders {binder_names:?}). \
                     DerivedProved, zero axiom_deps."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "reduce_once_red".to_string(),
                    "OptionType".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // NON-VACUITY, in-spec. Without this the five lemmas above could be read
        // as "the reducer never steps at all". `let_` unconditionally DOES step
        // (zeta), so the family genuinely discriminates reducible heads from
        // irreducible ones.
        self.add_definition(SpecDefinition {
            name: "reduce_once_red_some_let".to_string(),
            type_src: "forall (renv : RedEnv) (ty : KExpr) (v : KExpr) (b : KExpr), \
                       Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) \
                       (OptionType.some KExpr (instantiate b v))"
                .to_string(),
            value_src: Some(
                "fun (renv : RedEnv) (ty : KExpr) (v : KExpr) (b : KExpr) => \
                 Eq.refl (OptionType KExpr) (OptionType.some KExpr (instantiate b v))"
                    .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "reduce_once_red_some_let: the reflected reducer ALWAYS steps on a `let_` head, ",
                "by zeta, to `instantiate b v`. This is the deliberate non-vacuity control for ",
                "the reduce_once_red_none_* family — without a head that provably DOES step, ",
                "those five lemmas would be consistent with a reducer that never reduces ",
                "anything. Proved by KERNEL COMPUTATION. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once_red".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    fn add_reduce_once_red(&mut self) -> Result<(), SpecError> {
        // The ι-aware application lift: a silent head attempts the WHOLE-SPINE
        // recursor ι at the current application node (the model's
        // `| none => iotaReduct renv (.app f a)` arm); a stepped head relifts.
        self.add_recursive_def(
            r"def opt_app_ilift (renv : RedEnv) (f : KExpr) (a : KExpr) (o : OptionType KExpr) : OptionType KExpr := OptionType.rec KExpr (fun (_o : OptionType KExpr) => OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app f a)) (fun (f2 : KExpr) => OptionType.some KExpr (KExpr.app f2 a)) o",
            "opt_app_ilift renv f a o: the 3-way loop's application dispatch tail \
             — a stepped head relifts (some f2 becomes some (app f2 a)); a SILENT \
             head falls through to the whole-spine recursor ι attempt \
             iota_reduct (red_rec renv) (app f a) (round-5 reduceOnceRed port, \
             X17a).",
        )?;

        // The 3-way app-node head dispatch: lam β-fires, every other head
        // routes through the ι-aware lift.
        self.add_recursive_def(
            r"def reduce_app_head_red (renv : RedEnv) (a : KExpr) (f : KExpr) (cf : OptionType KExpr) : OptionType KExpr := KExpr.rec (fun (_e : KExpr) => OptionType KExpr) (fun (n : Level) => opt_app_ilift renv f a cf) (fun (i : Nat) => opt_app_ilift renv f a cf) (fun (g : KExpr) (b : KExpr) (_cg : OptionType KExpr) (_cb : OptionType KExpr) => opt_app_ilift renv f a cf) (fun (ty : KExpr) (b : KExpr) (_cty : OptionType KExpr) (_cb : OptionType KExpr) => OptionType.some KExpr (instantiate b a)) (fun (ty : KExpr) (b : KExpr) (_cty : OptionType KExpr) (_cb : OptionType KExpr) => opt_app_ilift renv f a cf) (fun (n : Name) (us : ListType Level) => opt_app_ilift renv f a cf) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : OptionType KExpr) (_c2 : OptionType KExpr) (_c3 : OptionType KExpr) => opt_app_ilift renv f a cf) (fun (s : Name) (i : Nat) (sub : KExpr) (_csub : OptionType KExpr) => opt_app_ilift renv f a cf) (fun (v : Nat) => opt_app_ilift renv f a cf) f",
            "reduce_app_head_red renv a f cf: the 3-way executable app-node \
             dispatch — a lam head β-fires (instantiate b a); any other head \
             lifts its own reduct through opt_app_ilift, whose none arm attempts \
             the whole-spine ι (round-5 reduceOnceRed port, X17a).",
        )?;

        // THE 3-WAY EXECUTABLE STEP (round-5 reduceOnceRed, 9-arm).
        self.add_recursive_def(
            r"def reduce_once_red (renv : RedEnv) (e : KExpr) : OptionType KExpr := KExpr.rec (fun (_e : KExpr) => OptionType KExpr) (fun (n : Level) => OptionType.none KExpr) (fun (i : Nat) => OptionType.none KExpr) (fun (f : KExpr) (a : KExpr) (cf : OptionType KExpr) (_ca : OptionType KExpr) => reduce_app_head_red renv a f cf) (fun (ty : KExpr) (b : KExpr) (_cty : OptionType KExpr) (_cb : OptionType KExpr) => OptionType.none KExpr) (fun (ty : KExpr) (b : KExpr) (_cty : OptionType KExpr) (_cb : OptionType KExpr) => OptionType.none KExpr) (fun (n : Name) (us : ListType Level) => defval_for (red_def renv) n) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : OptionType KExpr) (_c2 : OptionType KExpr) (_c3 : OptionType KExpr) => OptionType.some KExpr (instantiate b v)) (fun (s : Name) (i : Nat) (sub : KExpr) (csub : OptionType KExpr) => opt_proj_lift s i csub) (fun (v : Nat) => OptionType.none KExpr) e",
            "reduce_once_red renv e: THE 3-WAY EXECUTABLE single weak-head step \
             (round-5 reduceOnceRed port, X17a) — β at a lam-headed application, \
             ζ at a let, bare-const δ against the DEFINITION component only \
             (recursors are δ-opaque; their behaviour enters through the ι \
             fallback), head-recursion through the app spine with a whole-spine \
             ι attempt when the head is silent, proj-scrutinee congruence \
             recursion, none at value leaves. The δ is level-blind like the \
             2-way loop (documented base deviation).",
        )?;

        // The 3-way fuel loop (same generic loop_dispatch).
        self.add_recursive_def(
            r"def whnf_fuel_red (renv : RedEnv) (fuel : Nat) (e : KExpr) : OptionType KExpr := Nat.rec (fun (_k : Nat) => KExpr -> OptionType KExpr) (fun (e0 : KExpr) => OptionType.none KExpr) (fun (k : Nat) (ih : KExpr -> OptionType KExpr) => fun (e0 : KExpr) => loop_dispatch (reduce_once_red renv e0) e0 ih) fuel e",
            "whnf_fuel_red renv fuel e: the fuel-bounded 3-way \
             reduce-until-fixpoint loop over reduce_once_red — none is the \
             honest fuel bail, some r means the loop reached a reduce_once_red \
             fixpoint (round-5 whnfFuelRed port, X17a).",
        )?;

        self.add_definition(SpecDefinition {
            name: "reduce_app_ilift_sound".to_string(),
            type_src: "forall (renv : RedEnv) (f : KExpr) (a : KExpr) (e2 : KExpr), (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr e3) -> whnf_red_step renv f e3) -> Eq (OptionType KExpr) (opt_app_ilift renv f a (reduce_once_red renv f)) (OptionType.some KExpr e2) -> whnf_red_step renv (KExpr.app f a) e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (f : KExpr) (a : KExpr) (e2 : KExpr) (ih : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr e3) -> whnf_red_step renv f e3) (h : Eq (OptionType KExpr) (opt_app_ilift renv f a (reduce_once_red renv f)) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv f) o -> Eq (OptionType KExpr) (opt_app_ilift renv f a o) (OptionType.some KExpr e2) -> whnf_red_step renv (KExpr.app f a) e2) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv f a (OptionType.none KExpr)) (OptionType.some KExpr e2)) => whnf_red_step.iota renv (KExpr.app f a) e2 h2) (fun (f2 : KExpr) (heq : Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv f a (OptionType.some KExpr f2)) (OptionType.some KExpr e2)) => Eq.rec KExpr (KExpr.app f2 a) (fun (x : KExpr) (_hx : Eq KExpr (KExpr.app f2 a) x) => whnf_red_step renv (KExpr.app f a) x) (whnf_red_step.app_left renv f f2 a (ih f2 heq)) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2)) (reduce_once_red renv f) (Eq.refl (OptionType KExpr) (reduce_once_red renv f)) h".to_string()),
            is_axiom: false,
            description: "ι-AWARE APP-LIFT SOUNDNESS (X17a, round-5 redStep_app + the sound app case): a some through the 3-way application dispatch is a real whnf_red_step — the silent-head arm IS a whole-spine ι fire (whnf_red_step.iota, definitionally), the stepped-head arm lifts through the app_left congruence. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_app_ilift".to_string(),
                "reduce_once_red".to_string(),
                "whnf_red_step".to_string(),
                "whnf_red_step.iota".to_string(),
                "whnf_red_step.app_left".to_string(),
                "iota_reduct".to_string(),
                "option_some_inj".to_string(),
                "OptionType.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_proj_lift_sound_red".to_string(),
            type_src: "forall (renv : RedEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr), (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr e3) -> whnf_red_step renv sub e3) -> Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once_red renv sub)) (OptionType.some KExpr e2) -> whnf_red_step renv (KExpr.proj s i sub) e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr) (ih : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr e3) -> whnf_red_step renv sub e3) (h : Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once_red renv sub)) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv sub) o -> Eq (OptionType KExpr) (opt_proj_lift s i o) (OptionType.some KExpr e2) -> whnf_red_step renv (KExpr.proj s i sub) e2) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.none KExpr)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (whnf_red_step renv (KExpr.proj s i sub) e2) h2) (fun (sub2 : KExpr) (heq : Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr sub2)) (h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.some KExpr sub2)) (OptionType.some KExpr e2)) => Eq.rec KExpr (KExpr.proj s i sub2) (fun (x : KExpr) (_hx : Eq KExpr (KExpr.proj s i sub2) x) => whnf_red_step renv (KExpr.proj s i sub) x) (whnf_red_step.proj renv s i sub sub2 (ih sub2 heq)) e2 (option_some_inj KExpr (KExpr.proj s i sub2) e2 h2)) (reduce_once_red renv sub) (Eq.refl (OptionType KExpr) (reduce_once_red renv sub)) h".to_string()),
            is_axiom: false,
            description: "3-WAY PROJ-LIFT SOUNDNESS (X17a): a some through the executable proj lift over the 3-way step is one whnf_red_step.proj congruence step on the scrutinee. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_proj_lift".to_string(),
                "reduce_once_red".to_string(),
                "whnf_red_step".to_string(),
                "whnf_red_step.proj".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "OptionType.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_once_red_sound".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr) (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.some KExpr e2) -> whnf_red_step renv e e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv e0) (OptionType.some KExpr e2) -> whnf_red_step renv e0 e2) (fun (n : Level) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (whnf_red_step renv (KExpr.sort n) e2) h) (fun (i : Nat) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (whnf_red_step renv (KExpr.bvar i) e2) h) (fun (f : KExpr) (a : KExpr) (ihf : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr e3) -> whnf_red_step renv f e3) (_iha : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.some KExpr e3) -> whnf_red_step renv a e3) => KExpr.rec (fun (g : KExpr) => (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv g) (OptionType.some KExpr e3) -> whnf_red_step renv g e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a g (reduce_once_red renv g)) (OptionType.some KExpr e4) -> whnf_red_step renv (KExpr.app g a) e4) (fun (n : Level) (ihg : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.some KExpr e3) -> whnf_red_step renv (KExpr.sort n) e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.sort n) (reduce_once_red renv (KExpr.sort n))) (OptionType.some KExpr e2)) => reduce_app_ilift_sound renv (KExpr.sort n) a e2 ihg h) (fun (i : Nat) (ihg : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.some KExpr e3) -> whnf_red_step renv (KExpr.bvar i) e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.bvar i) (reduce_once_red renv (KExpr.bvar i))) (OptionType.some KExpr e2)) => reduce_app_ilift_sound renv (KExpr.bvar i) a e2 ihg h) (fun (g1 : KExpr) (g2 : KExpr) (_j1 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv g1) (OptionType.some KExpr e3) -> whnf_red_step renv g1 e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a g1 (reduce_once_red renv g1)) (OptionType.some KExpr e4) -> whnf_red_step renv (KExpr.app g1 a) e4) (_j2 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv g2) (OptionType.some KExpr e3) -> whnf_red_step renv g2 e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a g2 (reduce_once_red renv g2)) (OptionType.some KExpr e4) -> whnf_red_step renv (KExpr.app g2 a) e4) (ihg : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2)) (OptionType.some KExpr e3) -> whnf_red_step renv (KExpr.app g1 g2) e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.app g1 g2) (reduce_once_red renv (KExpr.app g1 g2))) (OptionType.some KExpr e2)) => reduce_app_ilift_sound renv (KExpr.app g1 g2) a e2 ihg h) (fun (ty : KExpr) (b : KExpr) (_j1 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e3) -> whnf_red_step renv ty e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a ty (reduce_once_red renv ty)) (OptionType.some KExpr e4) -> whnf_red_step renv (KExpr.app ty a) e4) (_j2 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e3) -> whnf_red_step renv b e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a b (reduce_once_red renv b)) (OptionType.some KExpr e4) -> whnf_red_step renv (KExpr.app b a) e4) (_ihg : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lam ty b)) (OptionType.some KExpr e3) -> whnf_red_step renv (KExpr.lam ty b) e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.lam ty b) (reduce_once_red renv (KExpr.lam ty b))) (OptionType.some KExpr e2)) => Eq.rec KExpr (instantiate b a) (fun (x : KExpr) (_hx : Eq KExpr (instantiate b a) x) => whnf_red_step renv (KExpr.app (KExpr.lam ty b) a) x) (whnf_red_step.beta renv (KExpr.app (KExpr.lam ty b) a) (instantiate b a) (beta_reduces_bd.beta ty b a)) e2 (option_some_inj KExpr (instantiate b a) e2 h)) (fun (ty : KExpr) (b : KExpr) (_j1 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e3) -> whnf_red_step renv ty e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a ty (reduce_once_red renv ty)) (OptionType.some KExpr e4) -> whnf_red_step renv (KExpr.app ty a) e4) (_j2 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e3) -> whnf_red_step renv b e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a b (reduce_once_red renv b)) (OptionType.some KExpr e4) -> whnf_red_step renv (KExpr.app b a) e4) (ihg : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.some KExpr e3) -> whnf_red_step renv (KExpr.pi ty b) e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.pi ty b) (reduce_once_red renv (KExpr.pi ty b))) (OptionType.some KExpr e2)) => reduce_app_ilift_sound renv (KExpr.pi ty b) a e2 ihg h) (fun (n : Name) (us : ListType Level) (ihg : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.some KExpr e3) -> whnf_red_step renv (KExpr.const n us) e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.const n us) (reduce_once_red renv (KExpr.const n us))) (OptionType.some KExpr e2)) => reduce_app_ilift_sound renv (KExpr.const n us) a e2 ihg h) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_j1 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e3) -> whnf_red_step renv ty e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a ty (reduce_once_red renv ty)) (OptionType.some KExpr e4) -> whnf_red_step renv (KExpr.app ty a) e4) (_j2 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv v) (OptionType.some KExpr e3) -> whnf_red_step renv v e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a v (reduce_once_red renv v)) (OptionType.some KExpr e4) -> whnf_red_step renv (KExpr.app v a) e4) (_j3 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e3) -> whnf_red_step renv b e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a b (reduce_once_red renv b)) (OptionType.some KExpr e4) -> whnf_red_step renv (KExpr.app b a) e4) (ihg : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.some KExpr e3) -> whnf_red_step renv (KExpr.let_ ty v b) e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.let_ ty v b) (reduce_once_red renv (KExpr.let_ ty v b))) (OptionType.some KExpr e2)) => reduce_app_ilift_sound renv (KExpr.let_ ty v b) a e2 ihg h) (fun (s : Name) (i : Nat) (sub : KExpr) (_j1 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr e3) -> whnf_red_step renv sub e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a sub (reduce_once_red renv sub)) (OptionType.some KExpr e4) -> whnf_red_step renv (KExpr.app sub a) e4) (ihg : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.some KExpr e3) -> whnf_red_step renv (KExpr.proj s i sub) e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.proj s i sub) (reduce_once_red renv (KExpr.proj s i sub))) (OptionType.some KExpr e2)) => reduce_app_ilift_sound renv (KExpr.proj s i sub) a e2 ihg h) (fun (v : Nat) (ihg : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.some KExpr e3) -> whnf_red_step renv (KExpr.lit v) e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.lit v) (reduce_once_red renv (KExpr.lit v))) (OptionType.some KExpr e2)) => reduce_app_ilift_sound renv (KExpr.lit v) a e2 ihg h) f ihf) (fun (ty : KExpr) (b : KExpr) (_i1 : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e3) -> whnf_red_step renv ty e3) (_i2 : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e3) -> whnf_red_step renv b e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lam ty b)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (whnf_red_step renv (KExpr.lam ty b) e2) h) (fun (ty : KExpr) (b : KExpr) (_i1 : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e3) -> whnf_red_step renv ty e3) (_i2 : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e3) -> whnf_red_step renv b e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (whnf_red_step renv (KExpr.pi ty b) e2) h) (fun (n : Name) (us : ListType Level) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.some KExpr e2)) => env_step_to_red renv (KExpr.const n us) e2 (const_delta_fires (red_def renv) n us e2 h)) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e3) -> whnf_red_step renv ty e3) (_i2 : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv v) (OptionType.some KExpr e3) -> whnf_red_step renv v e3) (_i3 : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e3) -> whnf_red_step renv b e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.some KExpr e2)) => Eq.rec KExpr (instantiate b v) (fun (x : KExpr) (_hx : Eq KExpr (instantiate b v) x) => whnf_red_step renv (KExpr.let_ ty v b) x) (whnf_red_step.beta renv (KExpr.let_ ty v b) (instantiate b v) (beta_reduces_bd.zeta ty v b)) e2 (option_some_inj KExpr (instantiate b v) e2 h)) (fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr e3) -> whnf_red_step renv sub e3) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.some KExpr e2)) => reduce_proj_lift_sound_red renv s i sub e2 ihsub h) (fun (v : Nat) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (whnf_red_step renv (KExpr.lit v) e2) h) e".to_string()),
            is_axiom: false,
            description: "3-WAY EXECUTABLE-STEP SOUNDNESS (X17a, round-5 proved guide theorem reduceOnceRed_sound): every some-result of the 3-way executable step is a real whnf_red_step — the lam head β-fires, the const case routes the X12 δ-liveness through the X15 embedding, let ζ-fires, the proj arm is the proj congruence, and every other app head routes through the ι-aware lift soundness (silent head = whole-spine ι fire; stepped head = app_left). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once_red".to_string(),
                "reduce_app_head_red".to_string(),
                "reduce_app_ilift_sound".to_string(),
                "reduce_proj_lift_sound_red".to_string(),
                "whnf_red_step".to_string(),
                "whnf_red_step.beta".to_string(),
                "whnf_red_step.iota".to_string(),
                "whnf_red_step.app_left".to_string(),
                "whnf_red_step.proj".to_string(),
                "env_step_to_red".to_string(),
                "const_delta_fires".to_string(),
                "beta_reduces_bd.beta".to_string(),
                "beta_reduces_bd.zeta".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "KExpr.rec".to_string(),
                "Eq.rec".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_inductive(
            r"inductive red_step_star (renv : RedEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), red_step_star renv e e
| tail : forall (a : KExpr) (b : KExpr) (c : KExpr), red_step_star renv a b → whnf_red_step renv b c → red_step_star renv a c",
            "red_step_star renv a b: the reflexive-transitive closure of whnf_red_step              — the multi-step reduction the loop's soundness path speaks. Part of the              RedLoop port (X17b, round-5 whnfFuelRed mirror).",
        )?;

        self.add_definition(SpecDefinition {
            name: "red_step_star_head".to_string(),
            type_src: concat!(
                "forall (renv : RedEnv) (a : KExpr) (b : KExpr) (c : KExpr), ",
                "whnf_red_step renv a b -> red_step_star renv b c -> red_step_star renv a c"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (renv : RedEnv) (a : KExpr) (b : KExpr) (c : KExpr) ",
                    "(hab : whnf_red_step renv a b) (hbc : red_step_star renv b c) => ",
                    "red_step_star.rec renv b ",
                    "(fun (y : KExpr) (_st : red_step_star renv b y) => ",
                    "whnf_red_step renv a b -> red_step_star renv a y) ",
                    "(fun (hab2 : whnf_red_step renv a b) => ",
                    "red_step_star.tail renv a a b (red_step_star.refl renv a) hab2) ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(hbx : red_step_star renv b x) (hxy : whnf_red_step renv x y) ",
                    "(ihx : whnf_red_step renv a b -> red_step_star renv a x) ",
                    "(hab2 : whnf_red_step renv a b) => ",
                    "red_step_star.tail renv a x y (ihx hab2) hxy) ",
                    "c hbc hab"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Star-prepend (WhnfLoop port X16a): one whnf_red_step followed by a                           star is a star — by the star recursor with a step-consuming motive.                           DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_step_star".to_string(),
                "red_step_star.rec".to_string(),
                "whnf_red_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_fuel_red_no_redex".to_string(),
            type_src: concat!(
                "forall (renv : RedEnv) (fuel : Nat) (e : KExpr) (r : KExpr), ",
                "Eq (OptionType KExpr) (whnf_fuel_red renv fuel e) (OptionType.some KExpr r) -> ",
                "Eq (OptionType KExpr) (reduce_once_red renv r) (OptionType.none KExpr)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (renv : RedEnv) (fuel : Nat) => Nat.rec ",
                    "(fun (k : Nat) => forall (e : KExpr) (r : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel_red renv k e) (OptionType.some KExpr r) -> ",
                    "Eq (OptionType KExpr) (reduce_once_red renv r) (OptionType.none KExpr)) ",
                    "(fun (e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel_red renv Nat.zero e) (OptionType.some KExpr r)) => ",
                    "option_none_ne_some KExpr r ",
                    "(Eq (OptionType KExpr) (reduce_once_red renv r) (OptionType.none KExpr)) h) ",
                    "(fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel_red renv k e0) (OptionType.some KExpr r0) -> ",
                    "Eq (OptionType KExpr) (reduce_once_red renv r0) (OptionType.none KExpr)) ",
                    "(e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel_red renv (Nat.succ k) e) (OptionType.some KExpr r)) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (reduce_once_red renv e) o -> ",
                    "Eq (OptionType KExpr) (loop_dispatch o e (fun (e2 : KExpr) => whnf_fuel_red renv k e2)) (OptionType.some KExpr r) -> ",
                    "Eq (OptionType KExpr) (reduce_once_red renv r) (OptionType.none KExpr)) ",
                    "(fun (heq : Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.none KExpr)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e (fun (e2 : KExpr) => whnf_fuel_red renv k e2)) (OptionType.some KExpr r)) => ",
                    "Eq.rec KExpr e ",
                    "(fun (x : KExpr) (_hx : Eq KExpr e x) => ",
                    "Eq (OptionType KExpr) (reduce_once_red renv x) (OptionType.none KExpr)) ",
                    "heq r (option_some_inj KExpr e r h2)) ",
                    "(fun (e2 : KExpr) ",
                    "(_heq : Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.some KExpr e2)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.some KExpr e2) e (fun (e3 : KExpr) => whnf_fuel_red renv k e3)) (OptionType.some KExpr r)) => ",
                    "ih e2 r h2) ",
                    "(reduce_once_red renv e) (Eq.refl (OptionType KExpr) (reduce_once_red renv e)) h) ",
                    "fuel"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "FIXPOINT-ONLY RETURNS (WhnfLoop port X17b mirror of the proved guide theorem                           whnfFuel_no_redex): a successful whnf_fuel result has NO reduce_once                           reduct — by fuel induction with the scrutinee-generalized loop                           dispatch; the none arm transports the fixpoint equation along                           some-injectivity, the some arm recurses. DerivedProved, zero                           axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel_red".to_string(),
                "reduce_once_red".to_string(),
                "loop_dispatch".to_string(),
                "option_some_inj".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_fuel_red_monotone".to_string(),
            type_src: concat!(
                "forall (renv : RedEnv) (fuel : Nat) (e : KExpr) (r : KExpr), ",
                "Eq (OptionType KExpr) (whnf_fuel_red renv fuel e) (OptionType.some KExpr r) -> ",
                "Eq (OptionType KExpr) (whnf_fuel_red renv (Nat.succ fuel) e) (OptionType.some KExpr r)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (renv : RedEnv) (fuel : Nat) => Nat.rec ",
                    "(fun (k : Nat) => forall (e : KExpr) (r : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel_red renv k e) (OptionType.some KExpr r) -> ",
                    "Eq (OptionType KExpr) (whnf_fuel_red renv (Nat.succ k) e) (OptionType.some KExpr r)) ",
                    "(fun (e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel_red renv Nat.zero e) (OptionType.some KExpr r)) => ",
                    "option_none_ne_some KExpr r ",
                    "(Eq (OptionType KExpr) (whnf_fuel_red renv (Nat.succ Nat.zero) e) (OptionType.some KExpr r)) h) ",
                    "(fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel_red renv k e0) (OptionType.some KExpr r0) -> ",
                    "Eq (OptionType KExpr) (whnf_fuel_red renv (Nat.succ k) e0) (OptionType.some KExpr r0)) ",
                    "(e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel_red renv (Nat.succ k) e) (OptionType.some KExpr r)) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (reduce_once_red renv e) o -> ",
                    "Eq (OptionType KExpr) (loop_dispatch o e (fun (e2 : KExpr) => whnf_fuel_red renv k e2)) (OptionType.some KExpr r) -> ",
                    "Eq (OptionType KExpr) (loop_dispatch o e (fun (e2 : KExpr) => whnf_fuel_red renv (Nat.succ k) e2)) (OptionType.some KExpr r)) ",
                    "(fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.none KExpr)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e (fun (e2 : KExpr) => whnf_fuel_red renv k e2)) (OptionType.some KExpr r)) => ",
                    "h2) ",
                    "(fun (e2 : KExpr) ",
                    "(_heq : Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.some KExpr e2)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.some KExpr e2) e (fun (e3 : KExpr) => whnf_fuel_red renv k e3)) (OptionType.some KExpr r)) => ",
                    "ih e2 r h2) ",
                    "(reduce_once_red renv e) (Eq.refl (OptionType KExpr) (reduce_once_red renv e)) h) ",
                    "fuel"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "FUEL MONOTONICITY (WhnfLoop port X17b mirror of the proved guide theorem                           whnfFuel_monotone): ONE extra unit of fuel never changes a successful loop                           answer (the general fuel-prime >= fuel form follows by iteration                           and is not registered) — the none arm's fixpoint return is fuel-independent (the                           two dispatch types are definitionally the SAME Eq), the some arm                           recurses. DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel_red".to_string(),
                "reduce_once_red".to_string(),
                "loop_dispatch".to_string(),
                "option_none_ne_some".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_fuel_red_reaches".to_string(),
            type_src: concat!(
                "forall (renv : RedEnv) (fuel : Nat) (e : KExpr) (r : KExpr), ",
                "Eq (OptionType KExpr) (whnf_fuel_red renv fuel e) (OptionType.some KExpr r) -> ",
                "(forall (a : KExpr) (b : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.some KExpr b) -> ",
                "whnf_red_step renv a b) -> ",
                "red_step_star renv e r"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (renv : RedEnv) (fuel : Nat) => Nat.rec ",
                    "(fun (k : Nat) => forall (e : KExpr) (r : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel_red renv k e) (OptionType.some KExpr r) -> ",
                    "(forall (a : KExpr) (b : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.some KExpr b) -> ",
                    "whnf_red_step renv a b) -> ",
                    "red_step_star renv e r) ",
                    "(fun (e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel_red renv Nat.zero e) (OptionType.some KExpr r)) ",
                    "(_hs : forall (a : KExpr) (b : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.some KExpr b) -> ",
                    "whnf_red_step renv a b) => ",
                    "opt_none_ne_some_t KExpr r (red_step_star renv e r) h) ",
                    "(fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel_red renv k e0) (OptionType.some KExpr r0) -> ",
                    "(forall (a : KExpr) (b : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.some KExpr b) -> ",
                    "whnf_red_step renv a b) -> ",
                    "red_step_star renv e0 r0) ",
                    "(e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel_red renv (Nat.succ k) e) (OptionType.some KExpr r)) ",
                    "(hs : forall (a : KExpr) (b : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.some KExpr b) -> ",
                    "whnf_red_step renv a b) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (reduce_once_red renv e) o -> ",
                    "Eq (OptionType KExpr) (loop_dispatch o e (fun (e2 : KExpr) => whnf_fuel_red renv k e2)) (OptionType.some KExpr r) -> ",
                    "red_step_star renv e r) ",
                    "(fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.none KExpr)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e (fun (e2 : KExpr) => whnf_fuel_red renv k e2)) (OptionType.some KExpr r)) => ",
                    "Eq.rec KExpr e ",
                    "(fun (x : KExpr) (_hx : Eq KExpr e x) => red_step_star renv e x) ",
                    "(red_step_star.refl renv e) r (option_some_inj KExpr e r h2)) ",
                    "(fun (e2 : KExpr) ",
                    "(heq : Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.some KExpr e2)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.some KExpr e2) e (fun (e3 : KExpr) => whnf_fuel_red renv k e3)) (OptionType.some KExpr r)) => ",
                    "red_step_star_head renv e e2 r (hs e e2 heq) (ih e2 r h2 hs)) ",
                    "(reduce_once_red renv e) (Eq.refl (OptionType KExpr) (reduce_once_red renv e)) h) ",
                    "fuel"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "SOUND REACH (WhnfLoop port X17b mirror of the proved guide theorem                           whnfFuel_reaches): with reduce_once-soundness as a hypothesis                           (exactly the guide's hsound), every successful loop result is                           reached by the 3-way (β/ζ+δ+ι) step star — fuel induction; the fixpoint                           arm transports refl along some-injectivity, the step arm prepends                           the sound step. DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel_red".to_string(),
                "reduce_once_red".to_string(),
                "loop_dispatch".to_string(),
                "red_step_star".to_string(),
                "red_step_star_head".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_fuel_red_reaches_sound".to_string(),
            type_src: concat!(
                "forall (renv : RedEnv) (fuel : Nat) (e : KExpr) (r : KExpr), ",
                "Eq (OptionType KExpr) (whnf_fuel_red renv fuel e) (OptionType.some KExpr r) -> ",
                "red_step_star renv e r"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (renv : RedEnv) (fuel : Nat) (e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel_red renv fuel e) (OptionType.some KExpr r)) => ",
                    "whnf_fuel_red_reaches renv fuel e r h ",
                    "(fun (a : KExpr) (b : KExpr) ",
                    "(hab : Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.some KExpr b)) => ",
                    "reduce_once_red_sound renv a b hab)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "UNCONDITIONAL REACH (X17b corollary, round-5 mirror): every successful whnf_fuel                           result is reached by the 3-way (β/ζ+δ+ι) step star — whnf_fuel_red_reaches with                           its soundness hypothesis DISCHARGED by reduce_once_red_sound. The loop's                           soundness path is now hypothesis-free. DerivedProved, zero                           axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel_red_reaches".to_string(),
                "reduce_once_red_sound".to_string(),
                "red_step_star".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "red_app_none_head_inv".to_string(),
            type_src: "forall (renv : RedEnv) (f : KExpr) (a : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app f a)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.none KExpr)".to_string(),
            value_src: Some("fun (renv : RedEnv) (f : KExpr) (a : KExpr) => KExpr.rec (fun (g : KExpr) => Eq (OptionType KExpr) (reduce_app_head_red renv a g (reduce_once_red renv g)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv g) (OptionType.none KExpr)) (fun (n : Level) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.sort n) (reduce_once_red renv (KExpr.sort n))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.sort n) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.sort n) a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.sort n) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.sort n) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.sort n)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.sort n))) h) (fun (i : Nat) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.bvar i) (reduce_once_red renv (KExpr.bvar i))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.bvar i) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.bvar i) a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.bvar i) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.bvar i) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.bvar i)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i))) h) (fun (g1 : KExpr) (g2 : KExpr) (_j1 : Eq (OptionType KExpr) (reduce_app_head_red renv a g1 (reduce_once_red renv g1)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv g1) (OptionType.none KExpr)) (_j2 : Eq (OptionType KExpr) (reduce_app_head_red renv a g2 (reduce_once_red renv g2)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv g2) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.app g1 g2) (reduce_once_red renv (KExpr.app g1 g2))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.app g1 g2) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.app g1 g2) a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.app g1 g2) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.app g1 g2) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.app g1 g2)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2))) h) (fun (ty : KExpr) (b : KExpr) (_j1 : Eq (OptionType KExpr) (reduce_app_head_red renv a ty (reduce_once_red renv ty)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr)) (_j2 : Eq (OptionType KExpr) (reduce_app_head_red renv a b (reduce_once_red renv b)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.lam ty b) (reduce_once_red renv (KExpr.lam ty b))) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (ty : KExpr) (b : KExpr) (_j1 : Eq (OptionType KExpr) (reduce_app_head_red renv a ty (reduce_once_red renv ty)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr)) (_j2 : Eq (OptionType KExpr) (reduce_app_head_red renv a b (reduce_once_red renv b)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.pi ty b) (reduce_once_red renv (KExpr.pi ty b))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.pi ty b) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.pi ty b) a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.pi ty b) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.pi ty b) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.pi ty b)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b))) h) (fun (n : Name) (us : ListType Level) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.const n us) (reduce_once_red renv (KExpr.const n us))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.const n us) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.const n us) a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.const n us) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.const n us) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.const n us)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.const n us))) h) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_j1 : Eq (OptionType KExpr) (reduce_app_head_red renv a ty (reduce_once_red renv ty)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr)) (_j2 : Eq (OptionType KExpr) (reduce_app_head_red renv a v (reduce_once_red renv v)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv v) (OptionType.none KExpr)) (_j3 : Eq (OptionType KExpr) (reduce_app_head_red renv a b (reduce_once_red renv b)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.let_ ty v b) (reduce_once_red renv (KExpr.let_ ty v b))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.let_ ty v b) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.let_ ty v b) a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.let_ ty v b) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.let_ ty v b) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.let_ ty v b)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b))) h) (fun (s : Name) (i : Nat) (sub : KExpr) (_j1 : Eq (OptionType KExpr) (reduce_app_head_red renv a sub (reduce_once_red renv sub)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.proj s i sub) (reduce_once_red renv (KExpr.proj s i sub))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.proj s i sub) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.proj s i sub) a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.proj s i sub) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.proj s i sub) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.proj s i sub)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub))) h) (fun (v : Nat) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.lit v) (reduce_once_red renv (KExpr.lit v))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.lit v) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.lit v) a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.lit v) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.lit v) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.lit v)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.lit v))) h) f".to_string()),
            is_axiom: false,
            description: "3-WAY APP-NONE HEAD EXTRACTION (X17c-1): an executable none at an application means the HEAD was silent — the lam head's conclusion is definitional (a lam is a value leaf of the 3-way step), every other head generalizes the head-reduct scrutinee through the ι-aware lift (the some arm refutes the relifted some; the none arm IS the conclusion). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once_red".to_string(),
                "reduce_app_head_red".to_string(),
                "opt_app_ilift".to_string(),
                "option_none_ne_some".to_string(),
                "OptionType.rec".to_string(),
                "KExpr.rec".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "red_app_none_iota_inv".to_string(),
            type_src: "forall (renv : RedEnv) (f : KExpr) (a : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app f a)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app f a)) (OptionType.none KExpr)".to_string(),
            value_src: Some("fun (renv : RedEnv) (f : KExpr) (a : KExpr) => KExpr.rec (fun (g : KExpr) => Eq (OptionType KExpr) (reduce_app_head_red renv a g (reduce_once_red renv g)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app g a)) (OptionType.none KExpr)) (fun (n : Level) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.sort n) (reduce_once_red renv (KExpr.sort n))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.sort n) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.sort n) a)) (OptionType.none KExpr)) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.sort n) a (OptionType.none KExpr)) (OptionType.none KExpr)) => h2) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.sort n) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.sort n) a)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.sort n) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.sort n)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.sort n))) h) (fun (i : Nat) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.bvar i) (reduce_once_red renv (KExpr.bvar i))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.bvar i) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.bvar i) a)) (OptionType.none KExpr)) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.bvar i) a (OptionType.none KExpr)) (OptionType.none KExpr)) => h2) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.bvar i) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.bvar i) a)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.bvar i) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.bvar i)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i))) h) (fun (g1 : KExpr) (g2 : KExpr) (_j1 : Eq (OptionType KExpr) (reduce_app_head_red renv a g1 (reduce_once_red renv g1)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app g1 a)) (OptionType.none KExpr)) (_j2 : Eq (OptionType KExpr) (reduce_app_head_red renv a g2 (reduce_once_red renv g2)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app g2 a)) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.app g1 g2) (reduce_once_red renv (KExpr.app g1 g2))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.app g1 g2) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.app g1 g2) a)) (OptionType.none KExpr)) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.app g1 g2) a (OptionType.none KExpr)) (OptionType.none KExpr)) => h2) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.app g1 g2) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.app g1 g2) a)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.app g1 g2) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.app g1 g2)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2))) h) (fun (ty : KExpr) (b : KExpr) (_j1 : Eq (OptionType KExpr) (reduce_app_head_red renv a ty (reduce_once_red renv ty)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app ty a)) (OptionType.none KExpr)) (_j2 : Eq (OptionType KExpr) (reduce_app_head_red renv a b (reduce_once_red renv b)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app b a)) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.lam ty b) (reduce_once_red renv (KExpr.lam ty b))) (OptionType.none KExpr)) => option_none_ne_some KExpr (instantiate b a) (Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.lam ty b) a)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (OptionType.some KExpr (instantiate b a)) (OptionType.none KExpr) h)) (fun (ty : KExpr) (b : KExpr) (_j1 : Eq (OptionType KExpr) (reduce_app_head_red renv a ty (reduce_once_red renv ty)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app ty a)) (OptionType.none KExpr)) (_j2 : Eq (OptionType KExpr) (reduce_app_head_red renv a b (reduce_once_red renv b)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app b a)) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.pi ty b) (reduce_once_red renv (KExpr.pi ty b))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.pi ty b) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.pi ty b) a)) (OptionType.none KExpr)) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.pi ty b) a (OptionType.none KExpr)) (OptionType.none KExpr)) => h2) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.pi ty b) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.pi ty b) a)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.pi ty b) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.pi ty b)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b))) h) (fun (n : Name) (us : ListType Level) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.const n us) (reduce_once_red renv (KExpr.const n us))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.const n us) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.const n us) a)) (OptionType.none KExpr)) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.const n us) a (OptionType.none KExpr)) (OptionType.none KExpr)) => h2) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.const n us) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.const n us) a)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.const n us) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.const n us)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.const n us))) h) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_j1 : Eq (OptionType KExpr) (reduce_app_head_red renv a ty (reduce_once_red renv ty)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app ty a)) (OptionType.none KExpr)) (_j2 : Eq (OptionType KExpr) (reduce_app_head_red renv a v (reduce_once_red renv v)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app v a)) (OptionType.none KExpr)) (_j3 : Eq (OptionType KExpr) (reduce_app_head_red renv a b (reduce_once_red renv b)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app b a)) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.let_ ty v b) (reduce_once_red renv (KExpr.let_ ty v b))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.let_ ty v b) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.let_ ty v b) a)) (OptionType.none KExpr)) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.let_ ty v b) a (OptionType.none KExpr)) (OptionType.none KExpr)) => h2) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.let_ ty v b) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.let_ ty v b) a)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.let_ ty v b) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.let_ ty v b)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b))) h) (fun (s : Name) (i : Nat) (sub : KExpr) (_j1 : Eq (OptionType KExpr) (reduce_app_head_red renv a sub (reduce_once_red renv sub)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app sub a)) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.proj s i sub) (reduce_once_red renv (KExpr.proj s i sub))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.proj s i sub) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.proj s i sub) a)) (OptionType.none KExpr)) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.proj s i sub) a (OptionType.none KExpr)) (OptionType.none KExpr)) => h2) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.proj s i sub) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.proj s i sub) a)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.proj s i sub) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.proj s i sub)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub))) h) (fun (v : Nat) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.lit v) (reduce_once_red renv (KExpr.lit v))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) o -> Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.lit v) a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.lit v) a)) (OptionType.none KExpr)) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.lit v) a (OptionType.none KExpr)) (OptionType.none KExpr)) => h2) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv (KExpr.lit v) a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (iota_reduct (red_rec renv) (KExpr.app (KExpr.lit v) a)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_ilift renv (KExpr.lit v) a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once_red renv (KExpr.lit v)) (Eq.refl (OptionType KExpr) (reduce_once_red renv (KExpr.lit v))) h) f".to_string()),
            is_axiom: false,
            description: "3-WAY APP-NONE SPINE-ι EXTRACTION (X17c-1): an executable none at an application means the whole-spine recursor ι found NOTHING — the ι-aware lift's none arm IS the ι attempt, so its silence is returned directly; the lam head and stepped heads refute the relifted some. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once_red".to_string(),
                "reduce_app_head_red".to_string(),
                "opt_app_ilift".to_string(),
                "iota_reduct".to_string(),
                "option_none_ne_some".to_string(),
                "OptionType.rec".to_string(),
                "KExpr.rec".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_once_red_none_delta_none".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr), Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) e) (OptionType.none KExpr)".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => Eq (OptionType KExpr) (reduce_once_red renv e0) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) e0) (OptionType.none KExpr)) (fun (n : Level) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (i : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (f : KExpr) (a : KExpr) (ihf : Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) f) (OptionType.none KExpr)) (_iha : Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) a) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app f a)) (OptionType.none KExpr)) => delta_none_app (red_def renv) f a (ihf (red_app_none_head_inv renv f a h))) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) b) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lam ty b)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) b) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (n : Name) (us : ListType Level) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.none KExpr)) => Eq.rec (OptionType KExpr) (defval_for (red_def renv) n) (fun (o : OptionType KExpr) (_ho : Eq (OptionType KExpr) (defval_for (red_def renv) n) o) => Eq (OptionType KExpr) (delta_reduct (red_def renv) (KExpr.const n us)) (opt_bind KExpr KExpr o (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.const n us)) val2)))) (Eq.refl (OptionType KExpr) (delta_reduct (red_def renv) (KExpr.const n us))) (OptionType.none KExpr) h) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv v) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) v) (OptionType.none KExpr)) (_i3 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) b) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (s : Name) (i : Nat) (sub : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct (red_def renv) sub) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (v : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) e".to_string()),
            is_axiom: false,
            description: "3-WAY GRANULARITY CONVERSE, δ side (X17c-1, round-6 target reduceOnceRed_none_delta_none): if the 3-way executable step finds nothing, the whole-spine δ has nothing to fire — non-app/non-const heads are δ-silent definitionally, the const case transports the lookup none through the bind, the app case chains the head extraction (now across the ι fallback), the IH, and the none-side δ correspondence. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once_red".to_string(),
                "delta_reduct".to_string(),
                "delta_none_app".to_string(),
                "red_app_none_head_inv".to_string(),
                "red_def".to_string(),
                "defval_for".to_string(),
                "opt_bind".to_string(),
                "apply_spine".to_string(),
                "kapp_args".to_string(),
                "KExpr.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_once_red_none_iota_none".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr), Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) e) (OptionType.none KExpr)".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => Eq (OptionType KExpr) (reduce_once_red renv e0) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) e0) (OptionType.none KExpr)) (fun (n : Level) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (i : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (f : KExpr) (a : KExpr) (_ihf : Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) f) (OptionType.none KExpr)) (_iha : Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) a) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app f a)) (OptionType.none KExpr)) => red_app_none_iota_inv renv f a h) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) b) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lam ty b)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) b) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (n : Name) (us : ListType Level) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.none KExpr)) => iota_reduct_const_none (red_rec renv) n us) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv v) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) v) (OptionType.none KExpr)) (_i3 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) b) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (s : Name) (i : Nat) (sub : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) sub) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (v : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) e".to_string()),
            is_axiom: false,
            description: "3-WAY GRANULARITY CONVERSE, ι side (X17c-1, round-6 target reduceOnceRed_none_iota_none): if the 3-way executable step finds nothing, the whole-spine recursor ι has nothing to fire — non-app non-const heads are ι-silent definitionally (their kapp_fn is not a const), a bare const has an empty spine (iota_reduct_const_none), and the app case is exactly the spine-ι extraction. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once_red".to_string(),
                "iota_reduct".to_string(),
                "iota_reduct_const_none".to_string(),
                "red_app_none_iota_inv".to_string(),
                "red_rec".to_string(),
                "KExpr.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // X17c-2a: the 3-way loop's own invariant substrate (round-6
        // SpecRedClassify port). Type-level disjunction for the two-env
        // definedness (no Sum/Or in the fragment until now).
        self.add_inductive(
            r"inductive OrType (A : Type) (B : Type) : Type
| inl : A → OrType A B
| inr : B → OrType A B",
            "Proof-relevant disjunction: OrType A B holds when A or B holds. \
             Substrate for the two-env constant definedness (X17c-2a, round-6 \
             ConstsDefined port).",
        )?;

        // Discriminator: the recursor-metadata lookup succeeded.
        self.add_recursive_def(
            r"def opt_meta_defined (o : OptionType RecMeta) : Type := OptionType.rec RecMeta (fun (_o : OptionType RecMeta) => Type) Empty (fun (m : RecMeta) => ConstFreeUnit) o",
            "opt_meta_defined o is inhabited iff the RecMeta lookup succeeded — \
             Empty at none, ConstFreeUnit at some (the recmeta_for analogue of \
             opt_defined/has_defval; X17c-2a).",
        )?;

        // Binder-counting closedness as a Type-valued def (the 3-way loop
        // invariant): iota fires apply closed-LAMBDA rule RHSs, which are
        // red_closed_at-0 but never ceiling-0, so the X16 ceiling invariant
        // cannot survive the iota arm. Round-6 closedAt, spec dialect
        // (LiftP-lifted Le at the bvar leaf).
        self.add_recursive_def(
            r"def red_closed_at (e : KExpr) : Nat -> Type := KExpr.rec (fun (_e : KExpr) => Nat -> Type) (fun (n : Level) => fun (d : Nat) => ConstFreeUnit) (fun (i : Nat) => fun (d : Nat) => LiftP (Le (Nat.succ i) d)) (fun (f : KExpr) (a : KExpr) (cf : Nat -> Type) (ca : Nat -> Type) => fun (d : Nat) => AndType (cf d) (ca d)) (fun (ty : KExpr) (b : KExpr) (cty : Nat -> Type) (cb : Nat -> Type) => fun (d : Nat) => AndType (cty d) (cb (Nat.succ d))) (fun (ty : KExpr) (b : KExpr) (cty : Nat -> Type) (cb : Nat -> Type) => fun (d : Nat) => AndType (cty d) (cb (Nat.succ d))) (fun (n : Name) (us : ListType Level) => fun (d : Nat) => ConstFreeUnit) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (c1 : Nat -> Type) (c2 : Nat -> Type) (c3 : Nat -> Type) => fun (d : Nat) => AndType (c1 d) (AndType (c2 d) (c3 (Nat.succ d)))) (fun (s : Name) (i : Nat) (sub : KExpr) (csub : Nat -> Type) => fun (d : Nat) => csub d) (fun (v : Nat) => fun (d : Nat) => ConstFreeUnit) e",
            "red_closed_at e d: binder-counting de Bruijn closedness as a \
             Type-valued def — every bvar i satisfies succ i <= d (LiftP-lifted \
             Le), lam/pi/let bodies recurse at succ d, leaves are trivially \
             closed. THE 3-way loop invariant (X17c-2a): iota fires apply \
             closed-lambda rule RHSs, red_closed_at-0 but never ceiling-0.",
        )?;

        // Two-env constant definedness: every const is delta-bound OR
        // recursor-known (round-6 ConstsDefined).
        self.add_recursive_def(
            r"def consts_defined_red (renv : RedEnv) (e : KExpr) : Type := KExpr.rec (fun (_e : KExpr) => Type) (fun (n : Level) => ConstFreeUnit) (fun (i : Nat) => ConstFreeUnit) (fun (f : KExpr) (a : KExpr) (cf : Type) (ca : Type) => AndType cf ca) (fun (ty : KExpr) (b : KExpr) (cty : Type) (cb : Type) => AndType cty cb) (fun (ty : KExpr) (b : KExpr) (cty : Type) (cb : Type) => AndType cty cb) (fun (n : Name) (us : ListType Level) => OrType (has_defval (red_def renv) n) (opt_meta_defined (recmeta_for (red_rec renv) n))) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (c1 : Type) (c2 : Type) (c3 : Type) => AndType c1 (AndType c2 c3)) (fun (s : Name) (i : Nat) (sub : KExpr) (csub : Type) => csub) (fun (v : Nat) => ConstFreeUnit) e",
            "consts_defined_red renv e: every constant head in e is bound in the \
             RedEnv's DEFINITION component (has_defval — it can delta-fire) OR \
             known to its RECURSOR component (opt_meta_defined of recmeta_for — \
             it can head an iota fire). The two-env definedness of the 3-way \
             loop (X17c-2a, round-6 ConstsDefined port) — unlike the X16 \
             one-env consts_defined, delta-opaque recursor heads are IN \
             domain.",
        )?;

        // Good combined environments (round-6 EnvsGood): delta-definientia
        // and iota rule RHSs are red_closed_at-0 (rule RHSs are closed
        // LAMBDAS) and fully two-env defined. The iota half is keyed on
        // recrule_for lookups (no rules-membership predicate in the
        // fragment).
        self.add_recursive_def(
            r"def red_env_good (renv : RedEnv) : Type := AndType (forall (n : Name) (v : KExpr), Eq (OptionType KExpr) (defval_for (red_def renv) n) (OptionType.some KExpr v) -> AndType (red_closed_at v Nat.zero) (consts_defined_red renv v)) (forall (rn : Name) (cn : Name) (rule : RecRule), Eq (OptionType RecRule) (recrule_for (red_rec renv) rn cn) (OptionType.some RecRule rule) -> AndType (red_closed_at (recrule_rhs rule) Nat.zero) (consts_defined_red renv (recrule_rhs rule)))",
            "red_env_good renv: BOTH reduction sources are good — every bound \
             definiens and every reachable recursor-rule RHS is \
             red_closed_at-0 (closed lambdas allowed — the ceiling-0 shape \
             would be FALSE for real rule RHSs) and fully two-env defined. The \
             environment hypothesis of the 3-way preservation/classification \
             rung (X17c-2a, round-6 EnvsGood port keyed on recrule_for).",
        )?;

        self.add_definition(SpecDefinition {
            name: "red_closed_le".to_string(),
            type_src: "forall (e : KExpr) (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at e d -> red_closed_at e d2".to_string(),
            value_src: Some("fun (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => forall (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at e0 d -> red_closed_at e0 d2) (fun (n : Level) (d : Nat) (d2 : Nat) (_hle : Le d d2) (h : red_closed_at (KExpr.sort n) d) => h) (fun (i : Nat) (d : Nat) (d2 : Nat) (hle : Le d d2) (h : LiftP (Le (Nat.succ i) d)) => LiftP.rec (Le (Nat.succ i) d) (fun (_p : LiftP (Le (Nat.succ i) d)) => LiftP (Le (Nat.succ i) d2)) (fun (p : Le (Nat.succ i) d) => LiftP.up (Le (Nat.succ i) d2) (le_trans (Nat.succ i) d d2 p hle)) h) (fun (f : KExpr) (a : KExpr) (ihf : forall (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at f d -> red_closed_at f d2) (iha : forall (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at a d -> red_closed_at a d2) (d : Nat) (d2 : Nat) (hle : Le d d2) (h : AndType (red_closed_at f d) (red_closed_at a d)) => AndType.intro (red_closed_at f d2) (red_closed_at a d2) (ihf d d2 hle (AndType.left (red_closed_at f d) (red_closed_at a d) h)) (iha d d2 hle (AndType.right (red_closed_at f d) (red_closed_at a d) h))) (fun (ty : KExpr) (b : KExpr) (ihty : forall (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at ty d -> red_closed_at ty d2) (ihb : forall (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at b d -> red_closed_at b d2) (d : Nat) (d2 : Nat) (hle : Le d d2) (h : AndType (red_closed_at ty d) (red_closed_at b (Nat.succ d))) => AndType.intro (red_closed_at ty d2) (red_closed_at b (Nat.succ d2)) (ihty d d2 hle (AndType.left (red_closed_at ty d) (red_closed_at b (Nat.succ d)) h)) (ihb (Nat.succ d) (Nat.succ d2) (le_succ_succ d d2 hle) (AndType.right (red_closed_at ty d) (red_closed_at b (Nat.succ d)) h))) (fun (ty : KExpr) (b : KExpr) (ihty : forall (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at ty d -> red_closed_at ty d2) (ihb : forall (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at b d -> red_closed_at b d2) (d : Nat) (d2 : Nat) (hle : Le d d2) (h : AndType (red_closed_at ty d) (red_closed_at b (Nat.succ d))) => AndType.intro (red_closed_at ty d2) (red_closed_at b (Nat.succ d2)) (ihty d d2 hle (AndType.left (red_closed_at ty d) (red_closed_at b (Nat.succ d)) h)) (ihb (Nat.succ d) (Nat.succ d2) (le_succ_succ d d2 hle) (AndType.right (red_closed_at ty d) (red_closed_at b (Nat.succ d)) h))) (fun (n : Name) (us : ListType Level) (d : Nat) (d2 : Nat) (_hle : Le d d2) (h : red_closed_at (KExpr.const n us) d) => h) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (ihty : forall (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at ty d -> red_closed_at ty d2) (ihv : forall (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at v d -> red_closed_at v d2) (ihb : forall (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at b d -> red_closed_at b d2) (d : Nat) (d2 : Nat) (hle : Le d d2) (h : AndType (red_closed_at ty d) (AndType (red_closed_at v d) (red_closed_at b (Nat.succ d)))) => AndType.intro (red_closed_at ty d2) (AndType (red_closed_at v d2) (red_closed_at b (Nat.succ d2))) (ihty d d2 hle (AndType.left (red_closed_at ty d) (AndType (red_closed_at v d) (red_closed_at b (Nat.succ d))) h)) (AndType.intro (red_closed_at v d2) (red_closed_at b (Nat.succ d2)) (ihv d d2 hle (AndType.left (red_closed_at v d) (red_closed_at b (Nat.succ d)) (AndType.right (red_closed_at ty d) (AndType (red_closed_at v d) (red_closed_at b (Nat.succ d))) h))) (ihb (Nat.succ d) (Nat.succ d2) (le_succ_succ d d2 hle) (AndType.right (red_closed_at v d) (red_closed_at b (Nat.succ d)) (AndType.right (red_closed_at ty d) (AndType (red_closed_at v d) (red_closed_at b (Nat.succ d))) h))))) (fun (sp : Name) (ip : Nat) (sub : KExpr) (ihsub : forall (d : Nat) (d2 : Nat), Le d d2 -> red_closed_at sub d -> red_closed_at sub d2) (d : Nat) (d2 : Nat) (hle : Le d d2) (h : red_closed_at sub d) => ihsub d d2 hle h) (fun (v : Nat) (d : Nat) (d2 : Nat) (_hle : Le d d2) (h : red_closed_at (KExpr.lit v) d) => h) e".to_string()),
            is_axiom: false,
            description: "CLOSEDNESS MONOTONICITY (X17c-2b, round-6 closedAt_mono): red_closed_at is monotone in the binder depth — the bvar leaf transports its Le witness through le_trans under the LiftP lift; binder arms bump both depths with le_succ_succ; leaves and proj pass through. The foundation of the 3-way preservation plumbing (the unlifted closed-value instantiate needs the value's closedness at every deeper binder level). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_closed_at".to_string(),
                "Le".to_string(),
                "le_trans".to_string(),
                "le_succ_succ".to_string(),
                "LiftP".to_string(),
                "LiftP.up".to_string(),
                "LiftP.rec".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "KExpr.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "le_zero_eq_zero".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Le a b -> Eq Nat b Nat.zero -> Eq Nat a Nat.zero".to_string(),
            value_src: Some("fun (a : Nat) (b : Nat) (h : Le a b) => Le.rec a (fun (j : Nat) (_hj : Le a j) => Eq Nat j Nat.zero -> Eq Nat a Nat.zero) (fun (hz : Eq Nat a Nat.zero) => hz) (fun (m : Nat) (_hm : Le a m) (_ih : Eq Nat m Nat.zero -> Eq Nat a Nat.zero) (hz : Eq Nat (Nat.succ m) Nat.zero) => LiftP.rec (Eq Nat a Nat.zero) (fun (_p : LiftP (Eq Nat a Nat.zero)) => Eq Nat a Nat.zero) (fun (p : Eq Nat a Nat.zero) => p) (nat_zero_ne_succ m (LiftP (Eq Nat a Nat.zero)) (Eq.symm Nat (Nat.succ m) Nat.zero hz))) b h".to_string()),
            is_axiom: false,
            description: "Le COLLAPSE AT ZERO (X17c-2b-2): a lower bound of zero is zero — Le.rec with the upper index generalized; the step arm's successor upper bound refutes the zero equation through the LiftP round-trip (nat_zero_ne_succ targets Type). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "Le.rec".to_string(),
                "nat_zero_ne_succ".to_string(),
                "LiftP".to_string(),
                "LiftP.rec".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "nat_sub_succ_le".to_string(),
            type_src: "forall (i : Nat) (d : Nat) (k : Nat), Eq Nat (Nat.sub d i) (Nat.succ k) -> Le (Nat.succ i) d".to_string(),
            value_src: Some("fun (i : Nat) => Nat.rec (fun (i0 : Nat) => forall (d : Nat) (k : Nat), Eq Nat (Nat.sub d i0) (Nat.succ k) -> Le (Nat.succ i0) d) (fun (d : Nat) (k : Nat) (h : Eq Nat (Nat.sub d Nat.zero) (Nat.succ k)) => Eq.subst Nat (fun (z : Nat) => Le (Nat.succ Nat.zero) z) (Nat.succ k) (Nat.sub d Nat.zero) (Eq.symm Nat (Nat.sub d Nat.zero) (Nat.succ k) h) (le_succ_succ Nat.zero k (le_zero_n k))) (fun (i2 : Nat) (ih : forall (d : Nat) (k : Nat), Eq Nat (Nat.sub d i2) (Nat.succ k) -> Le (Nat.succ i2) d) => fun (d : Nat) => Nat.rec (fun (d0 : Nat) => forall (k : Nat), Eq Nat (Nat.sub d0 (Nat.succ i2)) (Nat.succ k) -> Le (Nat.succ (Nat.succ i2)) d0) (fun (k : Nat) (h : Eq Nat (Nat.sub Nat.zero (Nat.succ i2)) (Nat.succ k)) => Eq.subst Nat (fun (z : Nat) => Eq Nat (Nat.pred z) (Nat.succ k) -> Le (Nat.succ (Nat.succ i2)) Nat.zero) Nat.zero (Nat.sub Nat.zero i2) (Eq.symm Nat (Nat.sub Nat.zero i2) Nat.zero (nat_sub_zero_left i2)) (fun (h1 : Eq Nat (Nat.pred Nat.zero) (Nat.succ k)) => LiftP.rec (Le (Nat.succ (Nat.succ i2)) Nat.zero) (fun (_p : LiftP (Le (Nat.succ (Nat.succ i2)) Nat.zero)) => Le (Nat.succ (Nat.succ i2)) Nat.zero) (fun (p : Le (Nat.succ (Nat.succ i2)) Nat.zero) => p) (nat_zero_ne_succ k (LiftP (Le (Nat.succ (Nat.succ i2)) Nat.zero)) h1)) h) (fun (d2 : Nat) (_ihd : forall (k : Nat), Eq Nat (Nat.sub d2 (Nat.succ i2)) (Nat.succ k) -> Le (Nat.succ (Nat.succ i2)) d2) (k : Nat) (h : Eq Nat (Nat.sub (Nat.succ d2) (Nat.succ i2)) (Nat.succ k)) => le_succ_succ (Nat.succ i2) d2 (ih d2 k (Eq.trans Nat (Nat.sub d2 i2) (Nat.sub (Nat.succ d2) (Nat.succ i2)) (Nat.succ k) (Eq.symm Nat (Nat.sub (Nat.succ d2) (Nat.succ i2)) (Nat.sub d2 i2) (nat_sub_succ_succ d2 i2)) h))) d) i".to_string()),
            is_axiom: false,
            description: "SUB-POSITIVITY GIVES STRICT BOUND (X17c-2b-2): Nat.sub d i = succ k forces succ i <= d — double Nat recursion; the (0, succ) diagonal refutes through nat_sub_zero_left + the pred collapse, the succ-succ diagonal collapses through nat_sub_succ_succ. The branch selector for the executable bvar instantiation. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "nat_sub_zero_left".to_string(),
                "nat_sub_succ_succ".to_string(),
                "nat_zero_ne_succ".to_string(),
                "le_succ_succ".to_string(),
                "le_zero_n".to_string(),
                "LiftP.rec".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "nat_sub_zero_eq".to_string(),
            type_src: "forall (i : Nat) (d : Nat), Le i d -> Eq Nat (Nat.sub d i) Nat.zero -> Eq Nat i d".to_string(),
            value_src: Some("fun (i : Nat) => Nat.rec (fun (i0 : Nat) => forall (d : Nat), Le i0 d -> Eq Nat (Nat.sub d i0) Nat.zero -> Eq Nat i0 d) (fun (d : Nat) (_hle : Le Nat.zero d) (h : Eq Nat (Nat.sub d Nat.zero) Nat.zero) => Eq.symm Nat (Nat.sub d Nat.zero) Nat.zero h) (fun (i2 : Nat) (ih : forall (d : Nat), Le i2 d -> Eq Nat (Nat.sub d i2) Nat.zero -> Eq Nat i2 d) => fun (d : Nat) => Nat.rec (fun (d0 : Nat) => Le (Nat.succ i2) d0 -> Eq Nat (Nat.sub d0 (Nat.succ i2)) Nat.zero -> Eq Nat (Nat.succ i2) d0) (fun (hle : Le (Nat.succ i2) Nat.zero) (_h : Eq Nat (Nat.sub Nat.zero (Nat.succ i2)) Nat.zero) => le_zero_eq_zero (Nat.succ i2) Nat.zero hle (Eq.refl Nat Nat.zero)) (fun (d2 : Nat) (_ihd : Le (Nat.succ i2) d2 -> Eq Nat (Nat.sub d2 (Nat.succ i2)) Nat.zero -> Eq Nat (Nat.succ i2) d2) (hle : Le (Nat.succ i2) (Nat.succ d2)) (h : Eq Nat (Nat.sub (Nat.succ d2) (Nat.succ i2)) Nat.zero) => Eq.cong Nat Nat (fun (x : Nat) => Nat.succ x) i2 d2 (ih d2 (le_pred_pred i2 d2 hle) (Eq.trans Nat (Nat.sub d2 i2) (Nat.sub (Nat.succ d2) (Nat.succ i2)) Nat.zero (Eq.symm Nat (Nat.sub (Nat.succ d2) (Nat.succ i2)) (Nat.sub d2 i2) (nat_sub_succ_succ d2 i2)) h))) d) i".to_string()),
            is_axiom: false,
            description: "SUB-ZERO GIVES EQUALITY UNDER A BOUND (X17c-2b-2): Le i d with Nat.sub d i = 0 forces i = d — double Nat recursion; the impossible (succ, 0) diagonal is discharged POSITIVELY by le_zero_eq_zero (its hypotheses already prove the goal), the succ-succ diagonal collapses through nat_sub_succ_succ + succ congruence. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "le_zero_eq_zero".to_string(),
                "le_pred_pred".to_string(),
                "nat_sub_succ_succ".to_string(),
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "lift_at_red_closed_id".to_string(),
            type_src: "forall (v : KExpr) (c : Nat) (amt : Nat), red_closed_at v c -> Eq KExpr (lift_at v c amt) v".to_string(),
            value_src: Some("fun (v : KExpr) (c : Nat) (amt : Nat) (h : red_closed_at v c) => KExpr.rec (fun (x : KExpr) => forall (a : Nat) (c2 : Nat), red_closed_at x c2 -> Eq KExpr (lift_at x c2 a) x) (fun (n : Level) (a : Nat) (c2 : Nat) (_h : red_closed_at (KExpr.sort n) c2) => Eq.refl KExpr (KExpr.sort n)) (fun (i : Nat) (a : Nat) (c2 : Nat) (hb : LiftP (Le (Nat.succ i) c2)) => LiftP.rec (Le (Nat.succ i) c2) (fun (_p : LiftP (Le (Nat.succ i) c2)) => Eq KExpr (lift_at (KExpr.bvar i) c2 a) (KExpr.bvar i)) (fun (p : Le (Nat.succ i) c2) => lift_bvar_lt i c2 a p) hb) (fun (f : KExpr) (g : KExpr) (ihf : forall (a : Nat) (c2 : Nat), red_closed_at f c2 -> Eq KExpr (lift_at f c2 a) f) (ihg : forall (a : Nat) (c2 : Nat), red_closed_at g c2 -> Eq KExpr (lift_at g c2 a) g) (a : Nat) (c2 : Nat) (hap : AndType (red_closed_at f c2) (red_closed_at g c2)) => Eq.trans KExpr (KExpr.app (lift_at f c2 a) (lift_at g c2 a)) (KExpr.app f (lift_at g c2 a)) (KExpr.app f g) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x (lift_at g c2 a)) (lift_at f c2 a) f (ihf a c2 (AndType.left (red_closed_at f c2) (red_closed_at g c2) hap))) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app f x) (lift_at g c2 a) g (ihg a c2 (AndType.right (red_closed_at f c2) (red_closed_at g c2) hap)))) (fun (ty : KExpr) (b : KExpr) (ihty : forall (a : Nat) (c2 : Nat), red_closed_at ty c2 -> Eq KExpr (lift_at ty c2 a) ty) (ihb : forall (a : Nat) (c2 : Nat), red_closed_at b c2 -> Eq KExpr (lift_at b c2 a) b) (a : Nat) (c2 : Nat) (hl : AndType (red_closed_at ty c2) (red_closed_at b (Nat.succ c2))) => Eq.trans KExpr (KExpr.lam (lift_at ty c2 a) (lift_at b (Nat.succ c2) a)) (KExpr.lam ty (lift_at b (Nat.succ c2) a)) (KExpr.lam ty b) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.lam x (lift_at b (Nat.succ c2) a)) (lift_at ty c2 a) ty (ihty a c2 (AndType.left (red_closed_at ty c2) (red_closed_at b (Nat.succ c2)) hl))) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.lam ty x) (lift_at b (Nat.succ c2) a) b (ihb a (Nat.succ c2) (AndType.right (red_closed_at ty c2) (red_closed_at b (Nat.succ c2)) hl)))) (fun (ty : KExpr) (b : KExpr) (ihty : forall (a : Nat) (c2 : Nat), red_closed_at ty c2 -> Eq KExpr (lift_at ty c2 a) ty) (ihb : forall (a : Nat) (c2 : Nat), red_closed_at b c2 -> Eq KExpr (lift_at b c2 a) b) (a : Nat) (c2 : Nat) (hl : AndType (red_closed_at ty c2) (red_closed_at b (Nat.succ c2))) => Eq.trans KExpr (KExpr.pi (lift_at ty c2 a) (lift_at b (Nat.succ c2) a)) (KExpr.pi ty (lift_at b (Nat.succ c2) a)) (KExpr.pi ty b) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi x (lift_at b (Nat.succ c2) a)) (lift_at ty c2 a) ty (ihty a c2 (AndType.left (red_closed_at ty c2) (red_closed_at b (Nat.succ c2)) hl))) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi ty x) (lift_at b (Nat.succ c2) a) b (ihb a (Nat.succ c2) (AndType.right (red_closed_at ty c2) (red_closed_at b (Nat.succ c2)) hl)))) (fun (n : Name) (us : ListType Level) (a : Nat) (c2 : Nat) (_h : red_closed_at (KExpr.const n us) c2) => Eq.refl KExpr (KExpr.const n us)) (fun (ty : KExpr) (vv : KExpr) (b : KExpr) (ihty : forall (a : Nat) (c2 : Nat), red_closed_at ty c2 -> Eq KExpr (lift_at ty c2 a) ty) (ihv : forall (a : Nat) (c2 : Nat), red_closed_at vv c2 -> Eq KExpr (lift_at vv c2 a) vv) (ihb : forall (a : Nat) (c2 : Nat), red_closed_at b c2 -> Eq KExpr (lift_at b c2 a) b) (a : Nat) (c2 : Nat) (hl : AndType (red_closed_at ty c2) (AndType (red_closed_at vv c2) (red_closed_at b (Nat.succ c2)))) => Eq.trans KExpr (KExpr.let_ (lift_at ty c2 a) (lift_at vv c2 a) (lift_at b (Nat.succ c2) a)) (KExpr.let_ ty (lift_at vv c2 a) (lift_at b (Nat.succ c2) a)) (KExpr.let_ ty vv b) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ x (lift_at vv c2 a) (lift_at b (Nat.succ c2) a)) (lift_at ty c2 a) ty (ihty a c2 (AndType.left (red_closed_at ty c2) (AndType (red_closed_at vv c2) (red_closed_at b (Nat.succ c2))) hl))) (Eq.trans KExpr (KExpr.let_ ty (lift_at vv c2 a) (lift_at b (Nat.succ c2) a)) (KExpr.let_ ty vv (lift_at b (Nat.succ c2) a)) (KExpr.let_ ty vv b) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ ty x (lift_at b (Nat.succ c2) a)) (lift_at vv c2 a) vv (ihv a c2 (AndType.left (red_closed_at vv c2) (red_closed_at b (Nat.succ c2)) (AndType.right (red_closed_at ty c2) (AndType (red_closed_at vv c2) (red_closed_at b (Nat.succ c2))) hl)))) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ ty vv x) (lift_at b (Nat.succ c2) a) b (ihb a (Nat.succ c2) (AndType.right (red_closed_at vv c2) (red_closed_at b (Nat.succ c2)) (AndType.right (red_closed_at ty c2) (AndType (red_closed_at vv c2) (red_closed_at b (Nat.succ c2))) hl)))))) (fun (sp : Name) (ip : Nat) (sub : KExpr) (ihsub : forall (a : Nat) (c2 : Nat), red_closed_at sub c2 -> Eq KExpr (lift_at sub c2 a) sub) (a : Nat) (c2 : Nat) (hs : red_closed_at sub c2) => Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj sp ip x) (lift_at sub c2 a) sub (ihsub a c2 hs)) (fun (n : Nat) (a : Nat) (c2 : Nat) (_h : red_closed_at (KExpr.lit n) c2) => Eq.refl KExpr (KExpr.lit n)) v amt c h".to_string()),
            is_axiom: false,
            description: "LIFT IDENTITY ON RED-CLOSED TERMS (X17c-2b-2, the red_closed_at analogue of lift_ceiling_id): lifting above the closedness cutoff changes nothing — every free bvar sits below the cutoff (lift_bvar_lt through the LiftP unlift), binder bodies recurse at the bumped cutoff, congruence chains rebuild the constructors. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_closed_at".to_string(),
                "lift_at".to_string(),
                "lift_bvar_lt".to_string(),
                "LiftP.rec".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.refl".to_string(),
                "KExpr.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Named scrutinee dispatchers for the executable bvar instantiation
        // (the elaborator rejects naked recursor applications in transported
        // motives — the established named-discriminator lesson).
        self.add_recursive_def(
            r"def inst_bvar_dispatch (i : Nat) (d : Nat) (val : KExpr) (s : Nat) : KExpr := Nat.rec (fun (_s : Nat) => KExpr) (instantiate_bvar_geq i d val) (fun (_k : Nat) (_r : KExpr) => KExpr.bvar i) s",
            "inst_bvar_dispatch i d val s: the branch selector of \
             instantiate_bvar_at with the scrutinee s exposed — \
             instantiate_bvar_at i d val IS inst_bvar_dispatch i d val \
             (Nat.sub d i) definitionally (X17c-2b-2).",
        )?;

        self.add_recursive_def(
            r"def inst_bvar_geq_dispatch (i : Nat) (d : Nat) (val : KExpr) (s : Nat) : KExpr := Nat.rec (fun (_s : Nat) => KExpr) (lift_at val Nat.zero d) (fun (_k : Nat) (_r : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) s",
            "inst_bvar_geq_dispatch i d val s: the branch selector of \
             instantiate_bvar_geq with the scrutinee s exposed — \
             instantiate_bvar_geq i d val IS inst_bvar_geq_dispatch i d val \
             (Nat.sub i d) definitionally (X17c-2b-2).",
        )?;

        self.add_definition(SpecDefinition {
            name: "inst_bvar_red_closed".to_string(),
            type_src: "forall (i : Nat) (d : Nat) (val : KExpr), Le (Nat.succ i) (Nat.succ d) -> red_closed_at val Nat.zero -> red_closed_at (instantiate_bvar_at i d val) d".to_string(),
            value_src: Some("fun (i : Nat) (d : Nat) (val : KExpr) (hle : Le (Nat.succ i) (Nat.succ d)) (hv : red_closed_at val Nat.zero) => Nat.rec (fun (s : Nat) => Eq Nat (Nat.sub d i) s -> red_closed_at (inst_bvar_dispatch i d val s) d) (fun (heq : Eq Nat (Nat.sub d i) Nat.zero) => Eq.rec Nat d (fun (x : Nat) (_hx : Eq Nat d x) => red_closed_at (inst_bvar_dispatch x d val Nat.zero) d) (Eq.rec Nat Nat.zero (fun (y : Nat) (_hy : Eq Nat Nat.zero y) => red_closed_at (inst_bvar_geq_dispatch d d val y) d) (Eq.rec KExpr val (fun (w : KExpr) (_hw : Eq KExpr val w) => red_closed_at w d) (red_closed_le val Nat.zero d (le_zero_n d) hv) (lift_at val Nat.zero d) (Eq.symm KExpr (lift_at val Nat.zero d) val (lift_at_red_closed_id val Nat.zero d hv))) (Nat.sub d d) (Eq.symm Nat (Nat.sub d d) Nat.zero (nat_sub_self d))) i (Eq.symm Nat i d (nat_sub_zero_eq i d (le_pred_pred i d hle) heq))) (fun (k : Nat) (_ih : Eq Nat (Nat.sub d i) k -> red_closed_at (inst_bvar_dispatch i d val k) d) (heq : Eq Nat (Nat.sub d i) (Nat.succ k)) => LiftP.up (Le (Nat.succ i) d) (nat_sub_succ_le i d k heq)) (Nat.sub d i) (Eq.refl Nat (Nat.sub d i))".to_string()),
            is_axiom: false,
            description: "EXECUTABLE BVAR INSTANTIATION CLOSEDNESS (X17c-2b-2): substituting a 0-closed value for bvar d in a (succ d)-closed variable stays d-closed — scrutinee-equation case split on Nat.sub d i through the named dispatcher: the positive branch keeps bvar i with the strict bound from nat_sub_succ_le; the zero branch forces i = d (nat_sub_zero_eq), lands on lift_at val 0 d, and the lift IDENTITY on red-closed terms plus depth monotonicity close it. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate_bvar_at".to_string(),
                "inst_bvar_dispatch".to_string(),
                "inst_bvar_geq_dispatch".to_string(),
                "nat_sub_succ_le".to_string(),
                "nat_sub_zero_eq".to_string(),
                "nat_sub_self".to_string(),
                "le_pred_pred".to_string(),
                "lift_at_red_closed_id".to_string(),
                "red_closed_le".to_string(),
                "le_zero_n".to_string(),
                "LiftP.up".to_string(),
                "Nat.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "inst_red_closed".to_string(),
            type_src: "forall (b : KExpr) (val : KExpr), red_closed_at val Nat.zero -> forall (d : Nat), red_closed_at b (Nat.succ d) -> red_closed_at (instantiate_at b val d) d".to_string(),
            value_src: Some("fun (b : KExpr) (val : KExpr) (hv : red_closed_at val Nat.zero) => KExpr.rec (fun (x : KExpr) => forall (d : Nat), red_closed_at x (Nat.succ d) -> red_closed_at (instantiate_at x val d) d) (fun (n : Level) (d : Nat) (_hb : red_closed_at (KExpr.sort n) (Nat.succ d)) => ConstFreeUnit.triv) (fun (i : Nat) (d : Nat) (hb : LiftP (Le (Nat.succ i) (Nat.succ d))) => LiftP.rec (Le (Nat.succ i) (Nat.succ d)) (fun (_p : LiftP (Le (Nat.succ i) (Nat.succ d))) => red_closed_at (instantiate_at (KExpr.bvar i) val d) d) (fun (p : Le (Nat.succ i) (Nat.succ d)) => inst_bvar_red_closed i d val p hv) hb) (fun (f : KExpr) (a : KExpr) (ihf : forall (d : Nat), red_closed_at f (Nat.succ d) -> red_closed_at (instantiate_at f val d) d) (iha : forall (d : Nat), red_closed_at a (Nat.succ d) -> red_closed_at (instantiate_at a val d) d) (d : Nat) (hb : AndType (red_closed_at f (Nat.succ d)) (red_closed_at a (Nat.succ d))) => AndType.intro (red_closed_at (instantiate_at f val d) d) (red_closed_at (instantiate_at a val d) d) (ihf d (AndType.left (red_closed_at f (Nat.succ d)) (red_closed_at a (Nat.succ d)) hb)) (iha d (AndType.right (red_closed_at f (Nat.succ d)) (red_closed_at a (Nat.succ d)) hb))) (fun (ty : KExpr) (bb : KExpr) (ihty : forall (d : Nat), red_closed_at ty (Nat.succ d) -> red_closed_at (instantiate_at ty val d) d) (ihb : forall (d : Nat), red_closed_at bb (Nat.succ d) -> red_closed_at (instantiate_at bb val d) d) (d : Nat) (hb : AndType (red_closed_at ty (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d)))) => AndType.intro (red_closed_at (instantiate_at ty val d) d) (red_closed_at (instantiate_at bb val (Nat.succ d)) (Nat.succ d)) (ihty d (AndType.left (red_closed_at ty (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d))) hb)) (ihb (Nat.succ d) (AndType.right (red_closed_at ty (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d))) hb))) (fun (ty : KExpr) (bb : KExpr) (ihty : forall (d : Nat), red_closed_at ty (Nat.succ d) -> red_closed_at (instantiate_at ty val d) d) (ihb : forall (d : Nat), red_closed_at bb (Nat.succ d) -> red_closed_at (instantiate_at bb val d) d) (d : Nat) (hb : AndType (red_closed_at ty (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d)))) => AndType.intro (red_closed_at (instantiate_at ty val d) d) (red_closed_at (instantiate_at bb val (Nat.succ d)) (Nat.succ d)) (ihty d (AndType.left (red_closed_at ty (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d))) hb)) (ihb (Nat.succ d) (AndType.right (red_closed_at ty (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d))) hb))) (fun (n : Name) (us : ListType Level) (d : Nat) (_hb : red_closed_at (KExpr.const n us) (Nat.succ d)) => ConstFreeUnit.triv) (fun (ty : KExpr) (vv : KExpr) (bb : KExpr) (ihty : forall (d : Nat), red_closed_at ty (Nat.succ d) -> red_closed_at (instantiate_at ty val d) d) (ihv : forall (d : Nat), red_closed_at vv (Nat.succ d) -> red_closed_at (instantiate_at vv val d) d) (ihb : forall (d : Nat), red_closed_at bb (Nat.succ d) -> red_closed_at (instantiate_at bb val d) d) (d : Nat) (hb : AndType (red_closed_at ty (Nat.succ d)) (AndType (red_closed_at vv (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d))))) => AndType.intro (red_closed_at (instantiate_at ty val d) d) (AndType (red_closed_at (instantiate_at vv val d) d) (red_closed_at (instantiate_at bb val (Nat.succ d)) (Nat.succ d))) (ihty d (AndType.left (red_closed_at ty (Nat.succ d)) (AndType (red_closed_at vv (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d)))) hb)) (AndType.intro (red_closed_at (instantiate_at vv val d) d) (red_closed_at (instantiate_at bb val (Nat.succ d)) (Nat.succ d)) (ihv d (AndType.left (red_closed_at vv (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d))) (AndType.right (red_closed_at ty (Nat.succ d)) (AndType (red_closed_at vv (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d)))) hb))) (ihb (Nat.succ d) (AndType.right (red_closed_at vv (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d))) (AndType.right (red_closed_at ty (Nat.succ d)) (AndType (red_closed_at vv (Nat.succ d)) (red_closed_at bb (Nat.succ (Nat.succ d)))) hb))))) (fun (sp : Name) (ip : Nat) (sub : KExpr) (ihsub : forall (d : Nat), red_closed_at sub (Nat.succ d) -> red_closed_at (instantiate_at sub val d) d) (d : Nat) (hb : red_closed_at sub (Nat.succ d)) => ihsub d hb) (fun (n : Nat) (d : Nat) (_hb : red_closed_at (KExpr.lit n) (Nat.succ d)) => ConstFreeUnit.triv) b".to_string()),
            is_axiom: false,
            description: "INSTANTIATE CLOSEDNESS (X17c-2b-2, round-6 subst_closedAt in the spec's closed-value dialect): substituting a 0-closed value at depth d of a (succ d)-closed body stays d-closed — instantiate_at passes the value UNCHANGED under binders (it lifts only at the bvar hit), so binder arms just bump the depth; the bvar leaf is inst_bvar_red_closed. The beta/zeta arm of the 3-way closedness preservation. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate_at".to_string(),
                "inst_bvar_red_closed".to_string(),
                "red_closed_at".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "ConstFreeUnit.triv".to_string(),
                "LiftP.rec".to_string(),
                "KExpr.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "inst_red_closed_zero".to_string(),
            type_src: "forall (b : KExpr) (val : KExpr), red_closed_at b (Nat.succ Nat.zero) -> red_closed_at val Nat.zero -> red_closed_at (instantiate b val) Nat.zero".to_string(),
            value_src: Some("fun (b : KExpr) (val : KExpr) (hb : red_closed_at b (Nat.succ Nat.zero)) (hv : red_closed_at val Nat.zero) => inst_red_closed b val hv Nat.zero hb".to_string()),
            is_axiom: false,
            description: "TOP-LEVEL INSTANTIATE CLOSEDNESS (X17c-2b-2): the depth-0 corollary the beta/zeta preservation arms consume (instantiate IS instantiate_at at depth zero). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "inst_red_closed".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // List closedness: every spine argument is red_closed_at d.
        self.add_recursive_def(
            r"def red_closed_list (args : ListType KExpr) (d : Nat) : Type := ListType.rec KExpr (fun (_l : ListType KExpr) => Type) ConstFreeUnit (fun (x : KExpr) (rest : ListType KExpr) (ih : Type) => AndType (red_closed_at x d) ih) args",
            "red_closed_list args d: every element of the spine-argument list is \
             red_closed_at d (ConstFreeUnit at nil, AndType chain at cons). The \
             list half of the 3-way iota-fire closedness plumbing (X17c-2b-3a).",
        )?;

        self.add_definition(SpecDefinition {
            name: "list_tail_red_closed".to_string(),
            type_src: "forall (args : ListType KExpr) (d : Nat), red_closed_list args d -> red_closed_list (list_tail args) d".to_string(),
            value_src: Some("fun (args : ListType KExpr) (d : Nat) => ListType.rec KExpr (fun (l0 : ListType KExpr) => red_closed_list l0 d -> red_closed_list (list_tail l0) d) (fun (_h : red_closed_list (ListType.nil KExpr) d) => ConstFreeUnit.triv) (fun (x : KExpr) (rest : ListType KExpr) (_ih : red_closed_list rest d -> red_closed_list (list_tail rest) d) (h : AndType (red_closed_at x d) (red_closed_list rest d)) => AndType.right (red_closed_at x d) (red_closed_list rest d) h) args".to_string()),
            is_axiom: false,
            description: "Tail preserves list closedness — nil's tail is nil (trivial), cons drops its head witness. X17c-2b-3a.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_closed_list".to_string(),
                "list_tail".to_string(),
                "AndType.right".to_string(),
                "ConstFreeUnit.triv".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "list_take_red_closed".to_string(),
            type_src: "forall (n : Nat) (l : ListType KExpr) (d : Nat), red_closed_list l d -> red_closed_list (list_take n l) d".to_string(),
            value_src: Some("fun (n : Nat) => Nat.rec (fun (_k : Nat) => forall (l : ListType KExpr) (d : Nat), red_closed_list l d -> red_closed_list (list_take _k l) d) (fun (l : ListType KExpr) (d : Nat) (_h : red_closed_list l d) => ConstFreeUnit.triv) (fun (m : Nat) (ih : forall (l : ListType KExpr) (d : Nat), red_closed_list l d -> red_closed_list (list_take m l) d) (l : ListType KExpr) (d : Nat) => ListType.rec KExpr (fun (l0 : ListType KExpr) => red_closed_list l0 d -> red_closed_list (list_take (Nat.succ m) l0) d) (fun (_h : red_closed_list (ListType.nil KExpr) d) => ConstFreeUnit.triv) (fun (x : KExpr) (rest : ListType KExpr) (_jh : red_closed_list rest d -> red_closed_list (list_take (Nat.succ m) rest) d) (h : AndType (red_closed_at x d) (red_closed_list rest d)) => AndType.intro (red_closed_at x d) (red_closed_list (list_take m rest) d) (AndType.left (red_closed_at x d) (red_closed_list rest d) h) (ih rest d (AndType.right (red_closed_at x d) (red_closed_list rest d) h))) l) n".to_string()),
            is_axiom: false,
            description: "Take preserves list closedness — zero takes nil (trivial), succ mirrors list_take's inner list dispatch, rebuilding the AndType chain with the outer fuel IH. X17c-2b-3a.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_closed_list".to_string(),
                "list_take".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "ConstFreeUnit.triv".to_string(),
                "Nat.rec".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "list_drop_red_closed".to_string(),
            type_src: "forall (n : Nat) (l : ListType KExpr) (d : Nat), red_closed_list l d -> red_closed_list (list_drop n l) d".to_string(),
            value_src: Some("fun (n : Nat) => Nat.rec (fun (_k : Nat) => forall (l : ListType KExpr) (d : Nat), red_closed_list l d -> red_closed_list (list_drop _k l) d) (fun (l : ListType KExpr) (d : Nat) (h : red_closed_list l d) => h) (fun (m : Nat) (ih : forall (l : ListType KExpr) (d : Nat), red_closed_list l d -> red_closed_list (list_drop m l) d) (l : ListType KExpr) (d : Nat) (h : red_closed_list l d) => ih (list_tail l) d (list_tail_red_closed l d h)) n".to_string()),
            is_axiom: false,
            description: "Drop preserves list closedness — zero is the identity, succ chains the tail lemma through the fuel IH (mirroring list_drop's own recursion). X17c-2b-3a.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_closed_list".to_string(),
                "list_drop".to_string(),
                "list_tail_red_closed".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "list_head_red_closed".to_string(),
            type_src: "forall (l : ListType KExpr) (d : Nat) (x : KExpr), red_closed_list l d -> Eq (OptionType KExpr) (list_head l) (OptionType.some KExpr x) -> red_closed_at x d".to_string(),
            value_src: Some("fun (l : ListType KExpr) (d : Nat) (x : KExpr) => ListType.rec KExpr (fun (l0 : ListType KExpr) => red_closed_list l0 d -> Eq (OptionType KExpr) (list_head l0) (OptionType.some KExpr x) -> red_closed_at x d) (fun (_h : red_closed_list (ListType.nil KExpr) d) (heq : Eq (OptionType KExpr) (list_head (ListType.nil KExpr)) (OptionType.some KExpr x)) => opt_none_ne_some_t KExpr x (red_closed_at x d) heq) (fun (y : KExpr) (rest : ListType KExpr) (_ih : red_closed_list rest d -> Eq (OptionType KExpr) (list_head rest) (OptionType.some KExpr x) -> red_closed_at x d) (h : AndType (red_closed_at y d) (red_closed_list rest d)) (heq : Eq (OptionType KExpr) (list_head (ListType.cons KExpr y rest)) (OptionType.some KExpr x)) => Eq.rec KExpr y (fun (z : KExpr) (_hz : Eq KExpr y z) => red_closed_at z d) (AndType.left (red_closed_at y d) (red_closed_list rest d) h) x (option_some_inj KExpr y x heq)) l".to_string()),
            is_axiom: false,
            description: "A some head of a closed list is closed — the nil case refutes the some equation, the cons case transports the head witness along some-injectivity. X17c-2b-3a.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_closed_list".to_string(),
                "list_head".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "AndType.left".to_string(),
                "Eq.rec".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "list_append_red_closed".to_string(),
            type_src: "forall (xs : ListType KExpr) (ys : ListType KExpr) (d : Nat), red_closed_list xs d -> red_closed_list ys d -> red_closed_list (list_append xs ys) d".to_string(),
            value_src: Some("fun (xs : ListType KExpr) (ys : ListType KExpr) (d : Nat) => ListType.rec KExpr (fun (l0 : ListType KExpr) => red_closed_list l0 d -> red_closed_list ys d -> red_closed_list (list_append l0 ys) d) (fun (_hx : red_closed_list (ListType.nil KExpr) d) (hy : red_closed_list ys d) => hy) (fun (x : KExpr) (rest : ListType KExpr) (ih : red_closed_list rest d -> red_closed_list ys d -> red_closed_list (list_append rest ys) d) (hx : AndType (red_closed_at x d) (red_closed_list rest d)) (hy : red_closed_list ys d) => AndType.intro (red_closed_at x d) (red_closed_list (list_append rest ys) d) (AndType.left (red_closed_at x d) (red_closed_list rest d) hx) (ih (AndType.right (red_closed_at x d) (red_closed_list rest d) hx) hy)) xs".to_string()),
            is_axiom: false,
            description: "Append preserves list closedness — structural on the left list. X17c-2b-3a.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_closed_list".to_string(),
                "list_append".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "apply_spine_red_closed".to_string(),
            type_src: "forall (args : ListType KExpr) (d : Nat), red_closed_list args d -> forall (h : KExpr), red_closed_at h d -> red_closed_at (apply_spine args h) d".to_string(),
            value_src: Some("fun (args : ListType KExpr) (d : Nat) => ListType.rec KExpr (fun (l0 : ListType KExpr) => red_closed_list l0 d -> forall (h : KExpr), red_closed_at h d -> red_closed_at (apply_spine l0 h) d) (fun (_hl : red_closed_list (ListType.nil KExpr) d) (h : KExpr) (hh : red_closed_at h d) => hh) (fun (x : KExpr) (rest : ListType KExpr) (ih : red_closed_list rest d -> forall (h2 : KExpr), red_closed_at h2 d -> red_closed_at (apply_spine rest h2) d) (hl : AndType (red_closed_at x d) (red_closed_list rest d)) (h : KExpr) (hh : red_closed_at h d) => ih (AndType.right (red_closed_at x d) (red_closed_list rest d) hl) (KExpr.app h x) (AndType.intro (red_closed_at h d) (red_closed_at x d) hh (AndType.left (red_closed_at x d) (red_closed_list rest d) hl))) args".to_string()),
            is_axiom: false,
            description: "Spine application preserves closedness — follows apply_spine's own left-fold: each step wraps the head in one app node whose closedness is the AndType of the head and the argument witnesses. X17c-2b-3a.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_closed_list".to_string(),
                "apply_spine".to_string(),
                "red_closed_at".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "kapp_red_closed".to_string(),
            type_src: "forall (e : KExpr) (d : Nat), red_closed_at e d -> AndType (red_closed_at (kapp_fn e) d) (red_closed_list (kapp_args e) d)".to_string(),
            value_src: Some("fun (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => forall (d : Nat), red_closed_at e0 d -> AndType (red_closed_at (kapp_fn e0) d) (red_closed_list (kapp_args e0) d)) (fun (n : Level) (d : Nat) (h : red_closed_at (KExpr.sort n) d) => AndType.intro (red_closed_at (kapp_fn (KExpr.sort n)) d) (red_closed_list (kapp_args (KExpr.sort n)) d) h ConstFreeUnit.triv) (fun (i : Nat) (d : Nat) (h : red_closed_at (KExpr.bvar i) d) => AndType.intro (red_closed_at (kapp_fn (KExpr.bvar i)) d) (red_closed_list (kapp_args (KExpr.bvar i)) d) h ConstFreeUnit.triv) (fun (f : KExpr) (a : KExpr) (ihf : forall (d : Nat), red_closed_at f d -> AndType (red_closed_at (kapp_fn f) d) (red_closed_list (kapp_args f) d)) (_iha : forall (d : Nat), red_closed_at a d -> AndType (red_closed_at (kapp_fn a) d) (red_closed_list (kapp_args a) d)) (d : Nat) (h : AndType (red_closed_at f d) (red_closed_at a d)) => AndType.intro (red_closed_at (kapp_fn f) d) (red_closed_list (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) d) (AndType.left (red_closed_at (kapp_fn f) d) (red_closed_list (kapp_args f) d) (ihf d (AndType.left (red_closed_at f d) (red_closed_at a d) h))) (list_append_red_closed (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)) d (AndType.right (red_closed_at (kapp_fn f) d) (red_closed_list (kapp_args f) d) (ihf d (AndType.left (red_closed_at f d) (red_closed_at a d) h))) (AndType.intro (red_closed_at a d) ConstFreeUnit (AndType.right (red_closed_at f d) (red_closed_at a d) h) ConstFreeUnit.triv))) (fun (ty : KExpr) (b : KExpr) (_i1 : forall (d : Nat), red_closed_at ty d -> AndType (red_closed_at (kapp_fn ty) d) (red_closed_list (kapp_args ty) d)) (_i2 : forall (d : Nat), red_closed_at b d -> AndType (red_closed_at (kapp_fn b) d) (red_closed_list (kapp_args b) d)) (d : Nat) (h : red_closed_at (KExpr.lam ty b) d) => AndType.intro (red_closed_at (kapp_fn (KExpr.lam ty b)) d) (red_closed_list (kapp_args (KExpr.lam ty b)) d) h ConstFreeUnit.triv) (fun (ty : KExpr) (b : KExpr) (_i1 : forall (d : Nat), red_closed_at ty d -> AndType (red_closed_at (kapp_fn ty) d) (red_closed_list (kapp_args ty) d)) (_i2 : forall (d : Nat), red_closed_at b d -> AndType (red_closed_at (kapp_fn b) d) (red_closed_list (kapp_args b) d)) (d : Nat) (h : red_closed_at (KExpr.pi ty b) d) => AndType.intro (red_closed_at (kapp_fn (KExpr.pi ty b)) d) (red_closed_list (kapp_args (KExpr.pi ty b)) d) h ConstFreeUnit.triv) (fun (n : Name) (us : ListType Level) (d : Nat) (h : red_closed_at (KExpr.const n us) d) => AndType.intro (red_closed_at (kapp_fn (KExpr.const n us)) d) (red_closed_list (kapp_args (KExpr.const n us)) d) h ConstFreeUnit.triv) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : forall (d : Nat), red_closed_at ty d -> AndType (red_closed_at (kapp_fn ty) d) (red_closed_list (kapp_args ty) d)) (_i2 : forall (d : Nat), red_closed_at v d -> AndType (red_closed_at (kapp_fn v) d) (red_closed_list (kapp_args v) d)) (_i3 : forall (d : Nat), red_closed_at b d -> AndType (red_closed_at (kapp_fn b) d) (red_closed_list (kapp_args b) d)) (d : Nat) (h : red_closed_at (KExpr.let_ ty v b) d) => AndType.intro (red_closed_at (kapp_fn (KExpr.let_ ty v b)) d) (red_closed_list (kapp_args (KExpr.let_ ty v b)) d) h ConstFreeUnit.triv) (fun (sp : Name) (ip : Nat) (sub : KExpr) (_i1 : forall (d : Nat), red_closed_at sub d -> AndType (red_closed_at (kapp_fn sub) d) (red_closed_list (kapp_args sub) d)) (d : Nat) (h : red_closed_at (KExpr.proj sp ip sub) d) => AndType.intro (red_closed_at (kapp_fn (KExpr.proj sp ip sub)) d) (red_closed_list (kapp_args (KExpr.proj sp ip sub)) d) h ConstFreeUnit.triv) (fun (v : Nat) (d : Nat) (h : red_closed_at (KExpr.lit v) d) => AndType.intro (red_closed_at (kapp_fn (KExpr.lit v)) d) (red_closed_list (kapp_args (KExpr.lit v)) d) h ConstFreeUnit.triv) e".to_string()),
            is_axiom: false,
            description: "Spine decomposition preserves closedness: the head and every argument of the application spine of a closed term are closed — non-app nodes are their own head with a nil spine, the app node splits its witness and appends the argument singleton. X17c-2b-3a.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_closed_at".to_string(),
                "red_closed_list".to_string(),
                "kapp_fn".to_string(),
                "kapp_args".to_string(),
                "list_append_red_closed".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "ConstFreeUnit.triv".to_string(),
                "KExpr.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "opt_bind_some_inv_t".to_string(),
            type_src: "forall (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (r : b) (C : Type), Eq (OptionType b) (opt_bind a b o f) (OptionType.some b r) -> (forall (w : a), Eq (OptionType a) o (OptionType.some a w) -> Eq (OptionType b) (f w) (OptionType.some b r) -> C) -> C".to_string(),
            value_src: Some("fun (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (r : b) (C : Type) (h : Eq (OptionType b) (opt_bind a b o f) (OptionType.some b r)) (k : forall (w : a), Eq (OptionType a) o (OptionType.some a w) -> Eq (OptionType b) (f w) (OptionType.some b r) -> C) => OptionType.rec a (fun (o0 : OptionType a) => Eq (OptionType b) (opt_bind a b o0 f) (OptionType.some b r) -> (forall (w : a), Eq (OptionType a) o0 (OptionType.some a w) -> Eq (OptionType b) (f w) (OptionType.some b r) -> C) -> C) (fun (h0 : Eq (OptionType b) (opt_bind a b (OptionType.none a) f) (OptionType.some b r)) (_k0 : forall (w : a), Eq (OptionType a) (OptionType.none a) (OptionType.some a w) -> Eq (OptionType b) (f w) (OptionType.some b r) -> C) => opt_none_ne_some_t b r C h0) (fun (w : a) (h0 : Eq (OptionType b) (opt_bind a b (OptionType.some a w) f) (OptionType.some b r)) (k0 : forall (w0 : a), Eq (OptionType a) (OptionType.some a w) (OptionType.some a w0) -> Eq (OptionType b) (f w0) (OptionType.some b r) -> C) => k0 w (Eq.refl (OptionType a) (OptionType.some a w)) h0) o h k".to_string()),
            is_axiom: false,
            description: "Type-targeted opt_bind some-inversion: the Prop-CPS opt_bind_some_inv cannot large-eliminate into Type-valued closedness goals, so this is its verbatim C : Type mirror (none refuted by opt_none_ne_some_t). X17c-2b-3a.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_bind".to_string(),
                "opt_none_ne_some_t".to_string(),
                "OptionType.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "iota_reduct_some_inv_t".to_string(),
            type_src: "forall (env : RecEnv) (e : KExpr) (e2 : KExpr) (C : Type), Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e2) -> (forall (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) -> Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (OptionType.some KExpr major) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))) (OptionType.some KExpr e2) -> C) -> C".to_string(),
            value_src: Some("fun (env : RecEnv) (e : KExpr) (e2 : KExpr) (C : Type) (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e2)) (k : (forall (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) -> Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (OptionType.some KExpr major) -> Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))) (OptionType.some KExpr e2) -> C)) => opt_bind_some_inv_t Name KExpr (kexpr_const_name (kapp_fn e)) (fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))))))) e2 C h (fun (recname : Name) (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) (h1r : Eq (OptionType KExpr) ((fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))))))) recname) (OptionType.some KExpr e2)) => opt_bind_some_inv_t RecMeta KExpr (recmeta_for env recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))))))) e2 C h1r (fun (meta : RecMeta) (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) (h2r : Eq (OptionType KExpr) ((fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))))))) meta) (OptionType.some KExpr e2)) => opt_bind_some_inv_t KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))))) e2 C h2r (fun (major : KExpr) (h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (OptionType.some KExpr major)) (h3r : Eq (OptionType KExpr) ((fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))))) major) (OptionType.some KExpr e2)) => opt_bind_some_inv_t Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))))) e2 C h3r (fun (cname : Name) (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) (h4r : Eq (OptionType KExpr) ((fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))))) cname) (OptionType.some KExpr e2)) => opt_bind_some_inv_t RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))) e2 C h4r (fun (rule : RecRule) (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) (h5r : Eq (OptionType KExpr) ((fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))) rule) (OptionType.some KExpr e2)) => k recname meta major cname rule h1 h2 h3 h4 h5 h5r)))))".to_string()),
            is_axiom: false,
            description: "Type-targeted iota-fire inversion: decomposes a successful iota_reduct into the recursor-name/metadata/major/constructor/rule lookup equations plus the reassembly equation, CPS into any Type-valued goal (verbatim mirror of the Prop-CPS iota_reduct_some_inv through opt_bind_some_inv_t). X17c-2b-3a.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "opt_bind_some_inv_t".to_string(),
                "opt_bind".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_args".to_string(),
                "recmeta_for".to_string(),
                "recrule_for".to_string(),
                "list_head".to_string(),
                "list_drop".to_string(),
                "list_take".to_string(),
                "apply_spine".to_string(),
                "recrule_rhs".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "iota_reduct_red_closed".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr) (e2 : KExpr), red_env_good renv -> red_closed_at e Nat.zero -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) e) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) (e2 : KExpr) (hg : red_env_good renv) (he : red_closed_at e Nat.zero) (h : Eq (OptionType KExpr) (iota_reduct (red_rec renv) e) (OptionType.some KExpr e2)) => iota_reduct_some_inv_t (red_rec renv) e e2 (red_closed_at e2 Nat.zero) h (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) (_h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) (_h2 : Eq (OptionType RecMeta) (recmeta_for (red_rec renv) recname) (OptionType.some RecMeta meta)) (h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (OptionType.some KExpr major)) (_h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) (h5 : Eq (OptionType RecRule) (recrule_for (red_rec renv) recname cname) (OptionType.some RecRule rule)) (h6 : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))) (OptionType.some KExpr e2)) => Eq.rec KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))) (fun (x : KExpr) (_hx : Eq KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))) x) => red_closed_at x Nat.zero) (apply_spine_red_closed (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) Nat.zero (list_drop_red_closed (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e) Nat.zero (AndType.right (red_closed_at (kapp_fn e) Nat.zero) (red_closed_list (kapp_args e) Nat.zero) (kapp_red_closed e Nat.zero he))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))) (apply_spine_red_closed (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) Nat.zero (list_drop_red_closed (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major) Nat.zero (AndType.right (red_closed_at (kapp_fn major) Nat.zero) (red_closed_list (kapp_args major) Nat.zero) (kapp_red_closed major Nat.zero (list_head_red_closed (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e)) Nat.zero major (list_drop_red_closed (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e) Nat.zero (AndType.right (red_closed_at (kapp_fn e) Nat.zero) (red_closed_list (kapp_args e) Nat.zero) (kapp_red_closed e Nat.zero he))) h3)))) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)) (apply_spine_red_closed (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) Nat.zero (list_take_red_closed (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e) Nat.zero (AndType.right (red_closed_at (kapp_fn e) Nat.zero) (red_closed_list (kapp_args e) Nat.zero) (kapp_red_closed e Nat.zero he))) (recrule_rhs rule) (AndType.left (red_closed_at (recrule_rhs rule) Nat.zero) (consts_defined_red renv (recrule_rhs rule)) (AndType.right (forall (n : Name) (v : KExpr), Eq (OptionType KExpr) (defval_for (red_def renv) n) (OptionType.some KExpr v) -> AndType (red_closed_at v Nat.zero) (consts_defined_red renv v)) (forall (rn : Name) (cn : Name) (rule : RecRule), Eq (OptionType RecRule) (recrule_for (red_rec renv) rn cn) (OptionType.some RecRule rule) -> AndType (red_closed_at (recrule_rhs rule) Nat.zero) (consts_defined_red renv (recrule_rhs rule))) hg recname cname rule h5))))) e2 (option_some_inj KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))) e2 h6))".to_string()),
            is_axiom: false,
            description: "IOTA-FIRE CLOSEDNESS (X17c-2b-3b, the heart of the 3-way preservation): a successful whole-spine recursor fire out of a closed term over a good environment stays closed — the Type-CPS inversion decomposes the fire; the rule RHS is closed by red_env_good's iota half (keyed on exactly the recrule_for equation the inversion supplies), the spine prefix/extras are take/drop of the closed argument spine, the major is the head of a closed drop, its fields a closed drop again; three apply_spine reassemblies and one transport along some-injectivity finish. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "iota_reduct_some_inv_t".to_string(),
                "red_env_good".to_string(),
                "red_closed_at".to_string(),
                "red_closed_list".to_string(),
                "kapp_red_closed".to_string(),
                "apply_spine_red_closed".to_string(),
                "list_take_red_closed".to_string(),
                "list_drop_red_closed".to_string(),
                "list_head_red_closed".to_string(),
                "recrule_rhs".to_string(),
                "recrule_num_fields".to_string(),
                "list_length".to_string(),
                "option_some_inj".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "Eq.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // List definedness: every spine argument is two-env defined.
        self.add_recursive_def(
            r"def consts_defined_red_list (renv : RedEnv) (args : ListType KExpr) : Type := ListType.rec KExpr (fun (_l : ListType KExpr) => Type) ConstFreeUnit (fun (x : KExpr) (rest : ListType KExpr) (ih : Type) => AndType (consts_defined_red renv x) ih) args",
            "consts_defined_red_list renv args: every element of the spine list is \
             two-env defined (X17c-2b-3c, the definedness mirror of \
             red_closed_list).",
        )?;

        // Named scrutinee-abstracted dispatcher for lift_bvar_at's Nat.rec
        // (both branches are bare bvars, so definedness is TOTAL over the
        // generic scrutinee — no Le reasoning needed).
        self.add_recursive_def(
            r"def lift_bvar_dispatch (i : Nat) (amt : Nat) (s : Nat) : KExpr := Nat.rec (fun (_s : Nat) => KExpr) (KExpr.bvar (Nat.add i amt)) (fun (_k : Nat) (_r : KExpr) => KExpr.bvar i) s",
            "lift_bvar_dispatch i amt s: lift_bvar_at's branch dispatcher with the \
             comparison scrutinee abstracted — lift_bvar_at i c amt is \
             definitionally lift_bvar_dispatch i amt (Nat.sub c i) \
             (X17c-2b-3c).",
        )?;

        self.add_definition(SpecDefinition {
            name: "lift_bvar_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (i : Nat) (amt : Nat) (s : Nat), consts_defined_red renv (lift_bvar_dispatch i amt s)".to_string(),
            value_src: Some("fun (renv : RedEnv) (i : Nat) (amt : Nat) (s : Nat) => Nat.rec (fun (s0 : Nat) => consts_defined_red renv (lift_bvar_dispatch i amt s0)) ConstFreeUnit.triv (fun (_k : Nat) (_ih : consts_defined_red renv (lift_bvar_dispatch i amt _k)) => ConstFreeUnit.triv) s".to_string()),
            is_axiom: false,
            description: "Both lift_bvar branches are bare bvars, whose two-env definedness is the trivial unit — total over the generic scrutinee. X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "lift_bvar_dispatch".to_string(),
                "consts_defined_red".to_string(),
                "ConstFreeUnit.triv".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "lift_at_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (amt : Nat) (v : KExpr) (c : Nat), consts_defined_red renv v -> consts_defined_red renv (lift_at v c amt)".to_string(),
            value_src: Some("fun (renv : RedEnv) (amt : Nat) (v : KExpr) => KExpr.rec (fun (v0 : KExpr) => forall (c : Nat), consts_defined_red renv v0 -> consts_defined_red renv (lift_at v0 c amt)) (fun (n : Level) (c : Nat) (h : consts_defined_red renv (KExpr.sort n)) => h) (fun (i : Nat) (c : Nat) (_h : consts_defined_red renv (KExpr.bvar i)) => lift_bvar_defined_red renv i amt (Nat.sub c i)) (fun (f : KExpr) (a : KExpr) (ihf : forall (c : Nat), consts_defined_red renv f -> consts_defined_red renv (lift_at f c amt)) (iha : forall (c : Nat), consts_defined_red renv a -> consts_defined_red renv (lift_at a c amt)) (c : Nat) (h : AndType (consts_defined_red renv f) (consts_defined_red renv a)) => AndType.intro (consts_defined_red renv (lift_at f c amt)) (consts_defined_red renv (lift_at a c amt)) (ihf c (AndType.left (consts_defined_red renv f) (consts_defined_red renv a) h)) (iha c (AndType.right (consts_defined_red renv f) (consts_defined_red renv a) h))) (fun (ty : KExpr) (b : KExpr) (ihty : forall (c : Nat), consts_defined_red renv ty -> consts_defined_red renv (lift_at ty c amt)) (ihb : forall (c : Nat), consts_defined_red renv b -> consts_defined_red renv (lift_at b c amt)) (c : Nat) (h : AndType (consts_defined_red renv ty) (consts_defined_red renv b)) => AndType.intro (consts_defined_red renv (lift_at ty c amt)) (consts_defined_red renv (lift_at b (Nat.succ c) amt)) (ihty c (AndType.left (consts_defined_red renv ty) (consts_defined_red renv b) h)) (ihb (Nat.succ c) (AndType.right (consts_defined_red renv ty) (consts_defined_red renv b) h))) (fun (ty : KExpr) (b : KExpr) (ihty : forall (c : Nat), consts_defined_red renv ty -> consts_defined_red renv (lift_at ty c amt)) (ihb : forall (c : Nat), consts_defined_red renv b -> consts_defined_red renv (lift_at b c amt)) (c : Nat) (h : AndType (consts_defined_red renv ty) (consts_defined_red renv b)) => AndType.intro (consts_defined_red renv (lift_at ty c amt)) (consts_defined_red renv (lift_at b (Nat.succ c) amt)) (ihty c (AndType.left (consts_defined_red renv ty) (consts_defined_red renv b) h)) (ihb (Nat.succ c) (AndType.right (consts_defined_red renv ty) (consts_defined_red renv b) h))) (fun (n : Name) (us : ListType Level) (c : Nat) (h : consts_defined_red renv (KExpr.const n us)) => h) (fun (ty : KExpr) (vv : KExpr) (b : KExpr) (ihty : forall (c : Nat), consts_defined_red renv ty -> consts_defined_red renv (lift_at ty c amt)) (ihv : forall (c : Nat), consts_defined_red renv vv -> consts_defined_red renv (lift_at vv c amt)) (ihb : forall (c : Nat), consts_defined_red renv b -> consts_defined_red renv (lift_at b c amt)) (c : Nat) (h : AndType (consts_defined_red renv ty) (AndType (consts_defined_red renv vv) (consts_defined_red renv b))) => AndType.intro (consts_defined_red renv (lift_at ty c amt)) (AndType (consts_defined_red renv (lift_at vv c amt)) (consts_defined_red renv (lift_at b (Nat.succ c) amt))) (ihty c (AndType.left (consts_defined_red renv ty) (AndType (consts_defined_red renv vv) (consts_defined_red renv b)) h)) (AndType.intro (consts_defined_red renv (lift_at vv c amt)) (consts_defined_red renv (lift_at b (Nat.succ c) amt)) (ihv c (AndType.left (consts_defined_red renv vv) (consts_defined_red renv b) (AndType.right (consts_defined_red renv ty) (AndType (consts_defined_red renv vv) (consts_defined_red renv b)) h))) (ihb (Nat.succ c) (AndType.right (consts_defined_red renv vv) (consts_defined_red renv b) (AndType.right (consts_defined_red renv ty) (AndType (consts_defined_red renv vv) (consts_defined_red renv b)) h))))) (fun (sp : Name) (ip : Nat) (sub : KExpr) (ihsub : forall (c : Nat), consts_defined_red renv sub -> consts_defined_red renv (lift_at sub c amt)) (c : Nat) (h : consts_defined_red renv sub) => ihsub c h) (fun (v2 : Nat) (c : Nat) (h : consts_defined_red renv (KExpr.lit v2)) => h) v".to_string()),
            is_axiom: false,
            description: "Lifting only renumbers bvars, so two-env definedness survives — the bvar arm is total via the dispatcher, everything else is congruence. X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "lift_at".to_string(),
                "consts_defined_red".to_string(),
                "lift_bvar_defined_red".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "KExpr.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "inst_bvar_geq_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (i : Nat) (d : Nat) (val : KExpr), consts_defined_red renv val -> forall (s : Nat), consts_defined_red renv (inst_bvar_geq_dispatch i d val s)".to_string(),
            value_src: Some("fun (renv : RedEnv) (i : Nat) (d : Nat) (val : KExpr) (hv : consts_defined_red renv val) (s : Nat) => Nat.rec (fun (s0 : Nat) => consts_defined_red renv (inst_bvar_geq_dispatch i d val s0)) (lift_at_defined_red renv d val Nat.zero hv) (fun (_k : Nat) (_ih : consts_defined_red renv (inst_bvar_geq_dispatch i d val _k)) => ConstFreeUnit.triv) s".to_string()),
            is_axiom: false,
            description: "The geq branch substitutes the lifted value (defined by the lift lemma) or a bare bvar (trivially defined) — total over the generic scrutinee. X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "inst_bvar_geq_dispatch".to_string(),
                "lift_at_defined_red".to_string(),
                "ConstFreeUnit.triv".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "inst_bvar_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (i : Nat) (d : Nat) (val : KExpr), consts_defined_red renv val -> consts_defined_red renv (instantiate_bvar_at i d val)".to_string(),
            value_src: Some("fun (renv : RedEnv) (i : Nat) (d : Nat) (val : KExpr) (hv : consts_defined_red renv val) => Nat.rec (fun (s0 : Nat) => consts_defined_red renv (inst_bvar_dispatch i d val s0)) (inst_bvar_geq_defined_red renv i d val hv (Nat.sub i d)) (fun (_k : Nat) (_ih : consts_defined_red renv (inst_bvar_dispatch i d val _k)) => ConstFreeUnit.triv) (Nat.sub d i)".to_string()),
            is_axiom: false,
            description: "instantiate_bvar_at is definitionally the dispatcher at Nat.sub d i; the lt branch is a bare bvar, the geq branch defers to the geq dispatcher lemma. X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate_bvar_at".to_string(),
                "inst_bvar_dispatch".to_string(),
                "inst_bvar_geq_defined_red".to_string(),
                "ConstFreeUnit.triv".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "inst_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (val : KExpr), consts_defined_red renv val -> forall (b : KExpr) (d : Nat), consts_defined_red renv b -> consts_defined_red renv (instantiate_at b val d)".to_string(),
            value_src: Some("fun (renv : RedEnv) (val : KExpr) (hval : consts_defined_red renv val) (b : KExpr) => KExpr.rec (fun (b0 : KExpr) => forall (d : Nat), consts_defined_red renv b0 -> consts_defined_red renv (instantiate_at b0 val d)) (fun (n : Level) (d : Nat) (h : consts_defined_red renv (KExpr.sort n)) => h) (fun (i : Nat) (d : Nat) (_h : consts_defined_red renv (KExpr.bvar i)) => inst_bvar_defined_red renv i d val hval) (fun (f : KExpr) (a : KExpr) (ihf : forall (d : Nat), consts_defined_red renv f -> consts_defined_red renv (instantiate_at f val d)) (iha : forall (d : Nat), consts_defined_red renv a -> consts_defined_red renv (instantiate_at a val d)) (d : Nat) (h : AndType (consts_defined_red renv f) (consts_defined_red renv a)) => AndType.intro (consts_defined_red renv (instantiate_at f val d)) (consts_defined_red renv (instantiate_at a val d)) (ihf d (AndType.left (consts_defined_red renv f) (consts_defined_red renv a) h)) (iha d (AndType.right (consts_defined_red renv f) (consts_defined_red renv a) h))) (fun (ty : KExpr) (bb : KExpr) (ihty : forall (d : Nat), consts_defined_red renv ty -> consts_defined_red renv (instantiate_at ty val d)) (ihb : forall (d : Nat), consts_defined_red renv bb -> consts_defined_red renv (instantiate_at bb val d)) (d : Nat) (h : AndType (consts_defined_red renv ty) (consts_defined_red renv bb)) => AndType.intro (consts_defined_red renv (instantiate_at ty val d)) (consts_defined_red renv (instantiate_at bb val (Nat.succ d))) (ihty d (AndType.left (consts_defined_red renv ty) (consts_defined_red renv bb) h)) (ihb (Nat.succ d) (AndType.right (consts_defined_red renv ty) (consts_defined_red renv bb) h))) (fun (ty : KExpr) (bb : KExpr) (ihty : forall (d : Nat), consts_defined_red renv ty -> consts_defined_red renv (instantiate_at ty val d)) (ihb : forall (d : Nat), consts_defined_red renv bb -> consts_defined_red renv (instantiate_at bb val d)) (d : Nat) (h : AndType (consts_defined_red renv ty) (consts_defined_red renv bb)) => AndType.intro (consts_defined_red renv (instantiate_at ty val d)) (consts_defined_red renv (instantiate_at bb val (Nat.succ d))) (ihty d (AndType.left (consts_defined_red renv ty) (consts_defined_red renv bb) h)) (ihb (Nat.succ d) (AndType.right (consts_defined_red renv ty) (consts_defined_red renv bb) h))) (fun (n : Name) (us : ListType Level) (d : Nat) (h : consts_defined_red renv (KExpr.const n us)) => h) (fun (ty : KExpr) (vv : KExpr) (bb : KExpr) (ihty : forall (d : Nat), consts_defined_red renv ty -> consts_defined_red renv (instantiate_at ty val d)) (ihv : forall (d : Nat), consts_defined_red renv vv -> consts_defined_red renv (instantiate_at vv val d)) (ihb : forall (d : Nat), consts_defined_red renv bb -> consts_defined_red renv (instantiate_at bb val d)) (d : Nat) (h : AndType (consts_defined_red renv ty) (AndType (consts_defined_red renv vv) (consts_defined_red renv bb))) => AndType.intro (consts_defined_red renv (instantiate_at ty val d)) (AndType (consts_defined_red renv (instantiate_at vv val d)) (consts_defined_red renv (instantiate_at bb val (Nat.succ d)))) (ihty d (AndType.left (consts_defined_red renv ty) (AndType (consts_defined_red renv vv) (consts_defined_red renv bb)) h)) (AndType.intro (consts_defined_red renv (instantiate_at vv val d)) (consts_defined_red renv (instantiate_at bb val (Nat.succ d))) (ihv d (AndType.left (consts_defined_red renv vv) (consts_defined_red renv bb) (AndType.right (consts_defined_red renv ty) (AndType (consts_defined_red renv vv) (consts_defined_red renv bb)) h))) (ihb (Nat.succ d) (AndType.right (consts_defined_red renv vv) (consts_defined_red renv bb) (AndType.right (consts_defined_red renv ty) (AndType (consts_defined_red renv vv) (consts_defined_red renv bb)) h))))) (fun (sp : Name) (ip : Nat) (sub : KExpr) (ihsub : forall (d : Nat), consts_defined_red renv sub -> consts_defined_red renv (instantiate_at sub val d)) (d : Nat) (h : consts_defined_red renv sub) => ihsub d h) (fun (v2 : Nat) (d : Nat) (h : consts_defined_red renv (KExpr.lit v2)) => h) b".to_string()),
            is_axiom: false,
            description: "Closed-value instantiation preserves two-env definedness — the bvar arm dispatches through the scrutinee-abstracted branch lemmas (val's lift is defined, bare bvars trivially so), binders pass val unchanged. X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate_at".to_string(),
                "consts_defined_red".to_string(),
                "inst_bvar_defined_red".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "KExpr.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "list_tail_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (args : ListType KExpr), consts_defined_red_list renv args -> consts_defined_red_list renv (list_tail args)".to_string(),
            value_src: Some("fun (renv : RedEnv) (args : ListType KExpr) => ListType.rec KExpr (fun (l0 : ListType KExpr) => consts_defined_red_list renv l0 -> consts_defined_red_list renv (list_tail l0)) (fun (_h : consts_defined_red_list renv (ListType.nil KExpr)) => ConstFreeUnit.triv) (fun (x : KExpr) (rest : ListType KExpr) (_ih : consts_defined_red_list renv rest -> consts_defined_red_list renv (list_tail rest)) (h : AndType (consts_defined_red renv x) (consts_defined_red_list renv rest)) => AndType.right (consts_defined_red renv x) (consts_defined_red_list renv rest) h) args".to_string()),
            is_axiom: false,
            description: "Tail preserves list definedness. X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "consts_defined_red_list".to_string(),
                "list_tail".to_string(),
                "AndType.right".to_string(),
                "ConstFreeUnit.triv".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "list_take_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (n : Nat) (l : ListType KExpr), consts_defined_red_list renv l -> consts_defined_red_list renv (list_take n l)".to_string(),
            value_src: Some("fun (renv : RedEnv) (n : Nat) => Nat.rec (fun (_k : Nat) => forall (l : ListType KExpr), consts_defined_red_list renv l -> consts_defined_red_list renv (list_take _k l)) (fun (l : ListType KExpr) (_h : consts_defined_red_list renv l) => ConstFreeUnit.triv) (fun (m : Nat) (ih : forall (l : ListType KExpr), consts_defined_red_list renv l -> consts_defined_red_list renv (list_take m l)) (l : ListType KExpr) => ListType.rec KExpr (fun (l0 : ListType KExpr) => consts_defined_red_list renv l0 -> consts_defined_red_list renv (list_take (Nat.succ m) l0)) (fun (_h : consts_defined_red_list renv (ListType.nil KExpr)) => ConstFreeUnit.triv) (fun (x : KExpr) (rest : ListType KExpr) (_jh : consts_defined_red_list renv rest -> consts_defined_red_list renv (list_take (Nat.succ m) rest)) (h : AndType (consts_defined_red renv x) (consts_defined_red_list renv rest)) => AndType.intro (consts_defined_red renv x) (consts_defined_red_list renv (list_take m rest)) (AndType.left (consts_defined_red renv x) (consts_defined_red_list renv rest) h) (ih rest (AndType.right (consts_defined_red renv x) (consts_defined_red_list renv rest) h))) l) n".to_string()),
            is_axiom: false,
            description: "Take preserves list definedness. X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "consts_defined_red_list".to_string(),
                "list_take".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "ConstFreeUnit.triv".to_string(),
                "Nat.rec".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "list_drop_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (n : Nat) (l : ListType KExpr), consts_defined_red_list renv l -> consts_defined_red_list renv (list_drop n l)".to_string(),
            value_src: Some("fun (renv : RedEnv) (n : Nat) => Nat.rec (fun (_k : Nat) => forall (l : ListType KExpr), consts_defined_red_list renv l -> consts_defined_red_list renv (list_drop _k l)) (fun (l : ListType KExpr) (h : consts_defined_red_list renv l) => h) (fun (m : Nat) (ih : forall (l : ListType KExpr), consts_defined_red_list renv l -> consts_defined_red_list renv (list_drop m l)) (l : ListType KExpr) (h : consts_defined_red_list renv l) => ih (list_tail l) (list_tail_defined_red renv l h)) n".to_string()),
            is_axiom: false,
            description: "Drop preserves list definedness. X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "consts_defined_red_list".to_string(),
                "list_drop".to_string(),
                "list_tail_defined_red".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "list_head_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (l : ListType KExpr) (x : KExpr), consts_defined_red_list renv l -> Eq (OptionType KExpr) (list_head l) (OptionType.some KExpr x) -> consts_defined_red renv x".to_string(),
            value_src: Some("fun (renv : RedEnv) (l : ListType KExpr) (x : KExpr) => ListType.rec KExpr (fun (l0 : ListType KExpr) => consts_defined_red_list renv l0 -> Eq (OptionType KExpr) (list_head l0) (OptionType.some KExpr x) -> consts_defined_red renv x) (fun (_h : consts_defined_red_list renv (ListType.nil KExpr)) (heq : Eq (OptionType KExpr) (list_head (ListType.nil KExpr)) (OptionType.some KExpr x)) => opt_none_ne_some_t KExpr x (consts_defined_red renv x) heq) (fun (y : KExpr) (rest : ListType KExpr) (_ih : consts_defined_red_list renv rest -> Eq (OptionType KExpr) (list_head rest) (OptionType.some KExpr x) -> consts_defined_red renv x) (h : AndType (consts_defined_red renv y) (consts_defined_red_list renv rest)) (heq : Eq (OptionType KExpr) (list_head (ListType.cons KExpr y rest)) (OptionType.some KExpr x)) => Eq.rec KExpr y (fun (z : KExpr) (_hz : Eq KExpr y z) => consts_defined_red renv z) (AndType.left (consts_defined_red renv y) (consts_defined_red_list renv rest) h) x (option_some_inj KExpr y x heq)) l".to_string()),
            is_axiom: false,
            description: "A some head of a defined list is defined. X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "consts_defined_red_list".to_string(),
                "list_head".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "AndType.left".to_string(),
                "Eq.rec".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "list_append_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (xs : ListType KExpr) (ys : ListType KExpr), consts_defined_red_list renv xs -> consts_defined_red_list renv ys -> consts_defined_red_list renv (list_append xs ys)".to_string(),
            value_src: Some("fun (renv : RedEnv) (xs : ListType KExpr) (ys : ListType KExpr) => ListType.rec KExpr (fun (l0 : ListType KExpr) => consts_defined_red_list renv l0 -> consts_defined_red_list renv ys -> consts_defined_red_list renv (list_append l0 ys)) (fun (_hx : consts_defined_red_list renv (ListType.nil KExpr)) (hy : consts_defined_red_list renv ys) => hy) (fun (x : KExpr) (rest : ListType KExpr) (ih : consts_defined_red_list renv rest -> consts_defined_red_list renv ys -> consts_defined_red_list renv (list_append rest ys)) (hx : AndType (consts_defined_red renv x) (consts_defined_red_list renv rest)) (hy : consts_defined_red_list renv ys) => AndType.intro (consts_defined_red renv x) (consts_defined_red_list renv (list_append rest ys)) (AndType.left (consts_defined_red renv x) (consts_defined_red_list renv rest) hx) (ih (AndType.right (consts_defined_red renv x) (consts_defined_red_list renv rest) hx) hy)) xs".to_string()),
            is_axiom: false,
            description: "Append preserves list definedness. X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "consts_defined_red_list".to_string(),
                "list_append".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "apply_spine_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (args : ListType KExpr), consts_defined_red_list renv args -> forall (h : KExpr), consts_defined_red renv h -> consts_defined_red renv (apply_spine args h)".to_string(),
            value_src: Some("fun (renv : RedEnv) (args : ListType KExpr) => ListType.rec KExpr (fun (l0 : ListType KExpr) => consts_defined_red_list renv l0 -> forall (h : KExpr), consts_defined_red renv h -> consts_defined_red renv (apply_spine l0 h)) (fun (_hl : consts_defined_red_list renv (ListType.nil KExpr)) (h : KExpr) (hh : consts_defined_red renv h) => hh) (fun (x : KExpr) (rest : ListType KExpr) (ih : consts_defined_red_list renv rest -> forall (h2 : KExpr), consts_defined_red renv h2 -> consts_defined_red renv (apply_spine rest h2)) (hl : AndType (consts_defined_red renv x) (consts_defined_red_list renv rest)) (h : KExpr) (hh : consts_defined_red renv h) => ih (AndType.right (consts_defined_red renv x) (consts_defined_red_list renv rest) hl) (KExpr.app h x) (AndType.intro (consts_defined_red renv h) (consts_defined_red renv x) hh (AndType.left (consts_defined_red renv x) (consts_defined_red_list renv rest) hl))) args".to_string()),
            is_axiom: false,
            description: "Spine application preserves definedness (left-fold mirror). X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "consts_defined_red_list".to_string(),
                "apply_spine".to_string(),
                "consts_defined_red".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "kapp_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr), consts_defined_red renv e -> AndType (consts_defined_red renv (kapp_fn e)) (consts_defined_red_list renv (kapp_args e))".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => consts_defined_red renv e0 -> AndType (consts_defined_red renv (kapp_fn e0)) (consts_defined_red_list renv (kapp_args e0))) (fun (n : Level) (h : consts_defined_red renv (KExpr.sort n)) => AndType.intro (consts_defined_red renv (kapp_fn (KExpr.sort n))) (consts_defined_red_list renv (kapp_args (KExpr.sort n))) h ConstFreeUnit.triv) (fun (i : Nat) (h : consts_defined_red renv (KExpr.bvar i)) => AndType.intro (consts_defined_red renv (kapp_fn (KExpr.bvar i))) (consts_defined_red_list renv (kapp_args (KExpr.bvar i))) h ConstFreeUnit.triv) (fun (f : KExpr) (a : KExpr) (ihf : consts_defined_red renv f -> AndType (consts_defined_red renv (kapp_fn f)) (consts_defined_red_list renv (kapp_args f))) (_iha : consts_defined_red renv a -> AndType (consts_defined_red renv (kapp_fn a)) (consts_defined_red_list renv (kapp_args a))) (h : AndType (consts_defined_red renv f) (consts_defined_red renv a)) => AndType.intro (consts_defined_red renv (kapp_fn f)) (consts_defined_red_list renv (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))) (AndType.left (consts_defined_red renv (kapp_fn f)) (consts_defined_red_list renv (kapp_args f)) (ihf (AndType.left (consts_defined_red renv f) (consts_defined_red renv a) h))) (list_append_defined_red renv (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)) (AndType.right (consts_defined_red renv (kapp_fn f)) (consts_defined_red_list renv (kapp_args f)) (ihf (AndType.left (consts_defined_red renv f) (consts_defined_red renv a) h))) (AndType.intro (consts_defined_red renv a) ConstFreeUnit (AndType.right (consts_defined_red renv f) (consts_defined_red renv a) h) ConstFreeUnit.triv))) (fun (ty : KExpr) (b : KExpr) (_i1 : consts_defined_red renv ty -> AndType (consts_defined_red renv (kapp_fn ty)) (consts_defined_red_list renv (kapp_args ty))) (_i2 : consts_defined_red renv b -> AndType (consts_defined_red renv (kapp_fn b)) (consts_defined_red_list renv (kapp_args b))) (h : consts_defined_red renv (KExpr.lam ty b)) => AndType.intro (consts_defined_red renv (kapp_fn (KExpr.lam ty b))) (consts_defined_red_list renv (kapp_args (KExpr.lam ty b))) h ConstFreeUnit.triv) (fun (ty : KExpr) (b : KExpr) (_i1 : consts_defined_red renv ty -> AndType (consts_defined_red renv (kapp_fn ty)) (consts_defined_red_list renv (kapp_args ty))) (_i2 : consts_defined_red renv b -> AndType (consts_defined_red renv (kapp_fn b)) (consts_defined_red_list renv (kapp_args b))) (h : consts_defined_red renv (KExpr.pi ty b)) => AndType.intro (consts_defined_red renv (kapp_fn (KExpr.pi ty b))) (consts_defined_red_list renv (kapp_args (KExpr.pi ty b))) h ConstFreeUnit.triv) (fun (n : Name) (us : ListType Level) (h : consts_defined_red renv (KExpr.const n us)) => AndType.intro (consts_defined_red renv (kapp_fn (KExpr.const n us))) (consts_defined_red_list renv (kapp_args (KExpr.const n us))) h ConstFreeUnit.triv) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : consts_defined_red renv ty -> AndType (consts_defined_red renv (kapp_fn ty)) (consts_defined_red_list renv (kapp_args ty))) (_i2 : consts_defined_red renv v -> AndType (consts_defined_red renv (kapp_fn v)) (consts_defined_red_list renv (kapp_args v))) (_i3 : consts_defined_red renv b -> AndType (consts_defined_red renv (kapp_fn b)) (consts_defined_red_list renv (kapp_args b))) (h : consts_defined_red renv (KExpr.let_ ty v b)) => AndType.intro (consts_defined_red renv (kapp_fn (KExpr.let_ ty v b))) (consts_defined_red_list renv (kapp_args (KExpr.let_ ty v b))) h ConstFreeUnit.triv) (fun (sp : Name) (ip : Nat) (sub : KExpr) (_i1 : consts_defined_red renv sub -> AndType (consts_defined_red renv (kapp_fn sub)) (consts_defined_red_list renv (kapp_args sub))) (h : consts_defined_red renv (KExpr.proj sp ip sub)) => AndType.intro (consts_defined_red renv (kapp_fn (KExpr.proj sp ip sub))) (consts_defined_red_list renv (kapp_args (KExpr.proj sp ip sub))) h ConstFreeUnit.triv) (fun (v : Nat) (h : consts_defined_red renv (KExpr.lit v)) => AndType.intro (consts_defined_red renv (kapp_fn (KExpr.lit v))) (consts_defined_red_list renv (kapp_args (KExpr.lit v))) h ConstFreeUnit.triv) e".to_string()),
            is_axiom: false,
            description: "Spine decomposition preserves two-env definedness (mirror of kapp_red_closed). X17c-2b-3c.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "consts_defined_red".to_string(),
                "consts_defined_red_list".to_string(),
                "kapp_fn".to_string(),
                "kapp_args".to_string(),
                "list_append_defined_red".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "ConstFreeUnit.triv".to_string(),
                "KExpr.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "iota_reduct_defined_red".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr) (e2 : KExpr), red_env_good renv -> consts_defined_red renv e -> Eq (OptionType KExpr) (iota_reduct (red_rec renv) e) (OptionType.some KExpr e2) -> consts_defined_red renv e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) (e2 : KExpr) (hg : red_env_good renv) (hd : consts_defined_red renv e) (h : Eq (OptionType KExpr) (iota_reduct (red_rec renv) e) (OptionType.some KExpr e2)) => iota_reduct_some_inv_t (red_rec renv) e e2 (consts_defined_red renv e2) h (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) (_h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) (_h2 : Eq (OptionType RecMeta) (recmeta_for (red_rec renv) recname) (OptionType.some RecMeta meta)) (h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (OptionType.some KExpr major)) (_h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) (h5 : Eq (OptionType RecRule) (recrule_for (red_rec renv) recname cname) (OptionType.some RecRule rule)) (h6 : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))) (OptionType.some KExpr e2)) => Eq.rec KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))) (fun (x : KExpr) (_hx : Eq KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))) x) => consts_defined_red renv x) (apply_spine_defined_red renv (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (list_drop_defined_red renv (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e) (AndType.right (consts_defined_red renv (kapp_fn e)) (consts_defined_red_list renv (kapp_args e)) (kapp_defined_red renv e hd))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))) (apply_spine_defined_red renv (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (list_drop_defined_red renv (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major) (AndType.right (consts_defined_red renv (kapp_fn major)) (consts_defined_red_list renv (kapp_args major)) (kapp_defined_red renv major (list_head_defined_red renv (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e)) major (list_drop_defined_red renv (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e) (AndType.right (consts_defined_red renv (kapp_fn e)) (consts_defined_red_list renv (kapp_args e)) (kapp_defined_red renv e hd))) h3)))) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)) (apply_spine_defined_red renv (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (list_take_defined_red renv (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e) (AndType.right (consts_defined_red renv (kapp_fn e)) (consts_defined_red_list renv (kapp_args e)) (kapp_defined_red renv e hd))) (recrule_rhs rule) (AndType.right (red_closed_at (recrule_rhs rule) Nat.zero) (consts_defined_red renv (recrule_rhs rule)) (AndType.right (forall (n : Name) (v : KExpr), Eq (OptionType KExpr) (defval_for (red_def renv) n) (OptionType.some KExpr v) -> AndType (red_closed_at v Nat.zero) (consts_defined_red renv v)) (forall (rn : Name) (cn : Name) (rule : RecRule), Eq (OptionType RecRule) (recrule_for (red_rec renv) rn cn) (OptionType.some RecRule rule) -> AndType (red_closed_at (recrule_rhs rule) Nat.zero) (consts_defined_red renv (recrule_rhs rule))) hg recname cname rule h5))))) e2 (option_some_inj KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))) e2 h6))".to_string()),
            is_axiom: false,
            description: "IOTA-FIRE DEFINEDNESS (X17c-2b-3c): a successful whole-spine recursor fire out of a fully-defined term over a good environment stays defined — the exact mirror of iota_reduct_red_closed through the definedness halves. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "iota_reduct_some_inv_t".to_string(),
                "red_env_good".to_string(),
                "consts_defined_red".to_string(),
                "consts_defined_red_list".to_string(),
                "kapp_defined_red".to_string(),
                "apply_spine_defined_red".to_string(),
                "list_take_defined_red".to_string(),
                "list_drop_defined_red".to_string(),
                "list_head_defined_red".to_string(),
                "recrule_rhs".to_string(),
                "recrule_num_fields".to_string(),
                "option_some_inj".to_string(),
                "AndType.right".to_string(),
                "Eq.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_app_ilift_closed".to_string(),
            type_src: "forall (renv : RedEnv) (f : KExpr) (a : KExpr) (e2 : KExpr), red_env_good renv -> (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> AndType (red_closed_at f Nat.zero) (red_closed_at a Nat.zero) -> Eq (OptionType KExpr) (opt_app_ilift renv f a (reduce_once_red renv f)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero".to_string(),
            value_src: Some("fun (renv : RedEnv) (f : KExpr) (a : KExpr) (e2 : KExpr) (hgood : red_env_good renv) (ihf : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) (hand : AndType (red_closed_at f Nat.zero) (red_closed_at a Nat.zero)) (h : Eq (OptionType KExpr) (opt_app_ilift renv f a (reduce_once_red renv f)) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv f) o -> Eq (OptionType KExpr) (opt_app_ilift renv f a o) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv f a (OptionType.none KExpr)) (OptionType.some KExpr e2)) => iota_reduct_red_closed renv (KExpr.app f a) e2 hgood (AndType.intro (red_closed_at f Nat.zero) (red_closed_at a Nat.zero) (AndType.left (red_closed_at f Nat.zero) (red_closed_at a Nat.zero) hand) (AndType.right (red_closed_at f Nat.zero) (red_closed_at a Nat.zero) hand)) h2) (fun (f2 : KExpr) (heq : Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv f a (OptionType.some KExpr f2)) (OptionType.some KExpr e2)) => Eq.rec KExpr (KExpr.app f2 a) (fun (x : KExpr) (_hx : Eq KExpr (KExpr.app f2 a) x) => red_closed_at x Nat.zero) (AndType.intro (red_closed_at f2 Nat.zero) (red_closed_at a Nat.zero) (ihf f2 heq) (AndType.right (red_closed_at f Nat.zero) (red_closed_at a Nat.zero) hand)) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2)) (reduce_once_red renv f) (Eq.refl (OptionType KExpr) (reduce_once_red renv f)) h".to_string()),
            is_axiom: false,
            description: "3-way ilift closedness (X17c-2c): a some through the ι-aware application lift stays closedAt-0 — the silent-head arm is the whole-spine ι fire (iota_reduct_red_closed), the stepped-head arm rebuilds the app AndType from the head IH. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_app_ilift".to_string(),
                "reduce_once_red".to_string(),
                "red_closed_at".to_string(),
                "red_env_good".to_string(),
                "iota_reduct_red_closed".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "option_some_inj".to_string(),
                "OptionType.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_proj_lift_closed".to_string(),
            type_src: "forall (renv : RedEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr), (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once_red renv sub)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero".to_string(),
            value_src: Some("fun (renv : RedEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr) (ih : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) (h : Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once_red renv sub)) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv sub) o -> Eq (OptionType KExpr) (opt_proj_lift s i o) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.none KExpr)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (red_closed_at e2 Nat.zero) h2) (fun (sub2 : KExpr) (heq : Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr sub2)) (h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.some KExpr sub2)) (OptionType.some KExpr e2)) => Eq.rec KExpr (KExpr.proj s i sub2) (fun (x : KExpr) (_hx : Eq KExpr (KExpr.proj s i sub2) x) => red_closed_at x Nat.zero) (ih sub2 heq) e2 (option_some_inj KExpr (KExpr.proj s i sub2) e2 h2)) (reduce_once_red renv sub) (Eq.refl (OptionType KExpr) (reduce_once_red renv sub)) h".to_string()),
            is_axiom: false,
            description: "3-way proj-lift closedness (X17c-2c): a some through the executable proj lift over the 3-way step stays closedAt-0 — proj s i sub2 is closed iff its scrutinee reduct is (the IH). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_proj_lift".to_string(),
                "reduce_once_red".to_string(),
                "red_closed_at".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "OptionType.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_once_red_preserves_closed".to_string(),
            type_src: "forall (renv : RedEnv), red_env_good renv -> forall (e : KExpr), red_closed_at e Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero".to_string(),
            value_src: Some("fun (renv : RedEnv) (hgood : red_env_good renv) (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => red_closed_at e0 Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv e0) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (fun (n : Level) (_hc : red_closed_at (KExpr.sort n) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (red_closed_at e2 Nat.zero) h) (fun (i : Nat) (_hc : red_closed_at (KExpr.bvar i) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (red_closed_at e2 Nat.zero) h) (fun (f : KExpr) (a : KExpr) (ihf : red_closed_at f Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_iha : red_closed_at a Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (hc : AndType (red_closed_at f Nat.zero) (red_closed_at a Nat.zero)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app f a)) (OptionType.some KExpr e2)) => (fun (hca : red_closed_at a Nat.zero) => KExpr.rec (fun (g : KExpr) => (red_closed_at g Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv g) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> red_closed_at g Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a g (reduce_once_red renv g)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (fun (n : Level) (ihg : red_closed_at (KExpr.sort n) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) (hcg : red_closed_at (KExpr.sort n) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.sort n) (reduce_once_red renv (KExpr.sort n))) (OptionType.some KExpr e2)) => reduce_app_ilift_closed renv (KExpr.sort n) a e2 hgood (ihg hcg) (AndType.intro (red_closed_at (KExpr.sort n) Nat.zero) (red_closed_at a Nat.zero) hcg hca) h) (fun (i : Nat) (ihg : red_closed_at (KExpr.bvar i) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) (hcg : red_closed_at (KExpr.bvar i) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.bvar i) (reduce_once_red renv (KExpr.bvar i))) (OptionType.some KExpr e2)) => reduce_app_ilift_closed renv (KExpr.bvar i) a e2 hgood (ihg hcg) (AndType.intro (red_closed_at (KExpr.bvar i) Nat.zero) (red_closed_at a Nat.zero) hcg hca) h) (fun (g1 : KExpr) (g2 : KExpr) (_ig1 : (red_closed_at g1 Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv g1) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> red_closed_at g1 Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a g1 (reduce_once_red renv g1)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_ig2 : (red_closed_at g2 Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv g2) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> red_closed_at g2 Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a g2 (reduce_once_red renv g2)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (ihg : red_closed_at (KExpr.app g1 g2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2)) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) (hcg : red_closed_at (KExpr.app g1 g2) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.app g1 g2) (reduce_once_red renv (KExpr.app g1 g2))) (OptionType.some KExpr e2)) => reduce_app_ilift_closed renv (KExpr.app g1 g2) a e2 hgood (ihg hcg) (AndType.intro (red_closed_at (KExpr.app g1 g2) Nat.zero) (red_closed_at a Nat.zero) hcg hca) h) (fun (ty2 : KExpr) (b2 : KExpr) (_ig1 : (red_closed_at ty2 Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty2) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> red_closed_at ty2 Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a ty2 (reduce_once_red renv ty2)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_ig2 : (red_closed_at b2 Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b2) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> red_closed_at b2 Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a b2 (reduce_once_red renv b2)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (ihg : red_closed_at (KExpr.lam ty2 b2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lam ty2 b2)) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) (hcg : red_closed_at (KExpr.lam ty2 b2) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.lam ty2 b2) (reduce_once_red renv (KExpr.lam ty2 b2))) (OptionType.some KExpr e2)) => Eq.rec KExpr (instantiate b2 a) (fun (x : KExpr) (_hx : Eq KExpr (instantiate b2 a) x) => red_closed_at x Nat.zero) (inst_red_closed_zero b2 a (AndType.right (red_closed_at ty2 Nat.zero) (red_closed_at b2 (Nat.succ Nat.zero)) hcg) hca) e2 (option_some_inj KExpr (instantiate b2 a) e2 h)) (fun (ty2 : KExpr) (b2 : KExpr) (_ig1 : (red_closed_at ty2 Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty2) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> red_closed_at ty2 Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a ty2 (reduce_once_red renv ty2)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_ig2 : (red_closed_at b2 Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b2) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> red_closed_at b2 Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a b2 (reduce_once_red renv b2)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (ihg : red_closed_at (KExpr.pi ty2 b2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty2 b2)) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) (hcg : red_closed_at (KExpr.pi ty2 b2) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.pi ty2 b2) (reduce_once_red renv (KExpr.pi ty2 b2))) (OptionType.some KExpr e2)) => reduce_app_ilift_closed renv (KExpr.pi ty2 b2) a e2 hgood (ihg hcg) (AndType.intro (red_closed_at (KExpr.pi ty2 b2) Nat.zero) (red_closed_at a Nat.zero) hcg hca) h) (fun (n2 : Name) (us2 : ListType Level) (ihg : red_closed_at (KExpr.const n2 us2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n2 us2)) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) (hcg : red_closed_at (KExpr.const n2 us2) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.const n2 us2) (reduce_once_red renv (KExpr.const n2 us2))) (OptionType.some KExpr e2)) => reduce_app_ilift_closed renv (KExpr.const n2 us2) a e2 hgood (ihg hcg) (AndType.intro (red_closed_at (KExpr.const n2 us2) Nat.zero) (red_closed_at a Nat.zero) hcg hca) h) (fun (ty2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_ig1 : (red_closed_at ty2 Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty2) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> red_closed_at ty2 Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a ty2 (reduce_once_red renv ty2)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_ig2 : (red_closed_at v2 Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv v2) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> red_closed_at v2 Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a v2 (reduce_once_red renv v2)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_ig3 : (red_closed_at b2 Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b2) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> red_closed_at b2 Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a b2 (reduce_once_red renv b2)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (ihg : red_closed_at (KExpr.let_ ty2 v2 b2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty2 v2 b2)) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) (hcg : red_closed_at (KExpr.let_ ty2 v2 b2) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.let_ ty2 v2 b2) (reduce_once_red renv (KExpr.let_ ty2 v2 b2))) (OptionType.some KExpr e2)) => reduce_app_ilift_closed renv (KExpr.let_ ty2 v2 b2) a e2 hgood (ihg hcg) (AndType.intro (red_closed_at (KExpr.let_ ty2 v2 b2) Nat.zero) (red_closed_at a Nat.zero) hcg hca) h) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_ig1 : (red_closed_at sub2 Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub2) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) -> red_closed_at sub2 Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a sub2 (reduce_once_red renv sub2)) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (ihg : red_closed_at (KExpr.proj s2 i2 sub2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s2 i2 sub2)) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) (hcg : red_closed_at (KExpr.proj s2 i2 sub2) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.proj s2 i2 sub2) (reduce_once_red renv (KExpr.proj s2 i2 sub2))) (OptionType.some KExpr e2)) => reduce_app_ilift_closed renv (KExpr.proj s2 i2 sub2) a e2 hgood (ihg hcg) (AndType.intro (red_closed_at (KExpr.proj s2 i2 sub2) Nat.zero) (red_closed_at a Nat.zero) hcg hca) h) (fun (v2 : Nat) (ihg : red_closed_at (KExpr.lit v2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v2)) (OptionType.some KExpr e3) -> red_closed_at e3 Nat.zero) (hcg : red_closed_at (KExpr.lit v2) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.lit v2) (reduce_once_red renv (KExpr.lit v2))) (OptionType.some KExpr e2)) => reduce_app_ilift_closed renv (KExpr.lit v2) a e2 hgood (ihg hcg) (AndType.intro (red_closed_at (KExpr.lit v2) Nat.zero) (red_closed_at a Nat.zero) hcg hca) h) f ihf (AndType.left (red_closed_at f Nat.zero) (red_closed_at a Nat.zero) hc) e2 h) (AndType.right (red_closed_at f Nat.zero) (red_closed_at a Nat.zero) hc)) (fun (ty : KExpr) (b : KExpr) (_i1 : red_closed_at ty Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_i2 : red_closed_at b Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_hc : red_closed_at (KExpr.lam ty b) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lam ty b)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (red_closed_at e2 Nat.zero) h) (fun (ty : KExpr) (b : KExpr) (_i1 : red_closed_at ty Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_i2 : red_closed_at b Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_hc : red_closed_at (KExpr.pi ty b) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (red_closed_at e2 Nat.zero) h) (fun (n : Name) (us : ListType Level) (_hc : red_closed_at (KExpr.const n us) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.some KExpr e2)) => AndType.left (red_closed_at e2 Nat.zero) (consts_defined_red renv e2) (AndType.left (forall (n2 : Name) (v : KExpr), Eq (OptionType KExpr) (defval_for (red_def renv) n2) (OptionType.some KExpr v) -> AndType (red_closed_at v Nat.zero) (consts_defined_red renv v)) (forall (rn : Name) (cn : Name) (rule : RecRule), Eq (OptionType RecRule) (recrule_for (red_rec renv) rn cn) (OptionType.some RecRule rule) -> AndType (red_closed_at (recrule_rhs rule) Nat.zero) (consts_defined_red renv (recrule_rhs rule))) hgood n e2 h)) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : red_closed_at ty Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_i2 : red_closed_at v Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv v) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (_i3 : red_closed_at b Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (hc : AndType (red_closed_at ty Nat.zero) (AndType (red_closed_at v Nat.zero) (red_closed_at b (Nat.succ Nat.zero)))) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.some KExpr e2)) => Eq.rec KExpr (instantiate b v) (fun (x : KExpr) (_hx : Eq KExpr (instantiate b v) x) => red_closed_at x Nat.zero) (inst_red_closed_zero b v (AndType.right (red_closed_at v Nat.zero) (red_closed_at b (Nat.succ Nat.zero)) (AndType.right (red_closed_at ty Nat.zero) (AndType (red_closed_at v Nat.zero) (red_closed_at b (Nat.succ Nat.zero))) hc)) (AndType.left (red_closed_at v Nat.zero) (red_closed_at b (Nat.succ Nat.zero)) (AndType.right (red_closed_at ty Nat.zero) (AndType (red_closed_at v Nat.zero) (red_closed_at b (Nat.succ Nat.zero))) hc))) e2 (option_some_inj KExpr (instantiate b v) e2 h)) (fun (s : Name) (i : Nat) (sub : KExpr) (ih : red_closed_at sub Nat.zero -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr e2) -> red_closed_at e2 Nat.zero) (hc : red_closed_at sub Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.some KExpr e2)) => reduce_proj_lift_closed renv s i sub e2 (ih hc) h) (fun (v : Nat) (_hc : red_closed_at (KExpr.lit v) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (red_closed_at e2 Nat.zero) h) e".to_string()),
            is_axiom: false,
            description: "3-WAY CLOSEDNESS PRESERVATION (X17c-2c, round-6 reduceOnceRed_preserves_closedAt): one 3-way executable step out of a closedAt-0 term stays closedAt-0 over a good environment — β/ζ by inst_red_closed_zero (closed-value substitution), δ by red_env_good's definiens half, whole-spine ι by iota_reduct_red_closed, app/proj congruence by the ilift/proj-lift closedness helpers. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once_red".to_string(),
                "reduce_app_head_red".to_string(),
                "reduce_app_ilift_closed".to_string(),
                "reduce_proj_lift_closed".to_string(),
                "red_closed_at".to_string(),
                "red_env_good".to_string(),
                "inst_red_closed_zero".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "instantiate".to_string(),
                "recrule_rhs".to_string(),
                "recrule_for".to_string(),
                "defval_for".to_string(),
                "red_def".to_string(),
                "red_rec".to_string(),
                "KExpr.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_app_ilift_defined".to_string(),
            type_src: "forall (renv : RedEnv) (f : KExpr) (a : KExpr) (e2 : KExpr), red_env_good renv -> (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr e3) -> consts_defined_red renv e3) -> AndType (consts_defined_red renv f) (consts_defined_red renv a) -> Eq (OptionType KExpr) (opt_app_ilift renv f a (reduce_once_red renv f)) (OptionType.some KExpr e2) -> consts_defined_red renv e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (f : KExpr) (a : KExpr) (e2 : KExpr) (hgood : red_env_good renv) (ihf : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr e3) -> consts_defined_red renv e3) (hand : AndType (consts_defined_red renv f) (consts_defined_red renv a)) (h : Eq (OptionType KExpr) (opt_app_ilift renv f a (reduce_once_red renv f)) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv f) o -> Eq (OptionType KExpr) (opt_app_ilift renv f a o) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv f a (OptionType.none KExpr)) (OptionType.some KExpr e2)) => iota_reduct_defined_red renv (KExpr.app f a) e2 hgood (AndType.intro (consts_defined_red renv f) (consts_defined_red renv a) (AndType.left (consts_defined_red renv f) (consts_defined_red renv a) hand) (AndType.right (consts_defined_red renv f) (consts_defined_red renv a) hand)) h2) (fun (f2 : KExpr) (heq : Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_ilift renv f a (OptionType.some KExpr f2)) (OptionType.some KExpr e2)) => Eq.rec KExpr (KExpr.app f2 a) (fun (x : KExpr) (_hx : Eq KExpr (KExpr.app f2 a) x) => consts_defined_red renv x) (AndType.intro (consts_defined_red renv f2) (consts_defined_red renv a) (ihf f2 heq) (AndType.right (consts_defined_red renv f) (consts_defined_red renv a) hand)) e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2)) (reduce_once_red renv f) (Eq.refl (OptionType KExpr) (reduce_once_red renv f)) h".to_string()),
            is_axiom: false,
            description: "3-way ilift definedness (X17c-2c t2): a some through the ι-aware application lift stays two-env-defined — silent head = whole-spine ι (iota_reduct_defined_red), stepped head rebuilds the app AndType from the head IH. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_app_ilift".to_string(),
                "reduce_once_red".to_string(),
                "consts_defined_red".to_string(),
                "iota_reduct_defined_red".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "option_some_inj".to_string(),
                "OptionType.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_proj_lift_defined".to_string(),
            type_src: "forall (renv : RedEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr), (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr e3) -> consts_defined_red renv e3) -> Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once_red renv sub)) (OptionType.some KExpr e2) -> consts_defined_red renv e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr) (ih : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr e3) -> consts_defined_red renv e3) (h : Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once_red renv sub)) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv sub) o -> Eq (OptionType KExpr) (opt_proj_lift s i o) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (fun (_heq : Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.none KExpr)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (consts_defined_red renv e2) h2) (fun (sub2 : KExpr) (heq : Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr sub2)) (h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.some KExpr sub2)) (OptionType.some KExpr e2)) => Eq.rec KExpr (KExpr.proj s i sub2) (fun (x : KExpr) (_hx : Eq KExpr (KExpr.proj s i sub2) x) => consts_defined_red renv x) (ih sub2 heq) e2 (option_some_inj KExpr (KExpr.proj s i sub2) e2 h2)) (reduce_once_red renv sub) (Eq.refl (OptionType KExpr) (reduce_once_red renv sub)) h".to_string()),
            is_axiom: false,
            description: "3-way proj-lift definedness (X17c-2c t2): a some through the executable proj lift stays two-env-defined — consts_defined_red passes through the projection to the scrutinee reduct (the IH). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_proj_lift".to_string(),
                "reduce_once_red".to_string(),
                "consts_defined_red".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "OptionType.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_once_red_preserves_defined".to_string(),
            type_src: "forall (renv : RedEnv), red_env_good renv -> forall (e : KExpr), consts_defined_red renv e -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.some KExpr e2) -> consts_defined_red renv e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (hgood : red_env_good renv) (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => consts_defined_red renv e0 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv e0) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (fun (n : Level) (_hd : consts_defined_red renv (KExpr.sort n)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (consts_defined_red renv e2) h) (fun (i : Nat) (_hd : consts_defined_red renv (KExpr.bvar i)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (consts_defined_red renv e2) h) (fun (f : KExpr) (a : KExpr) (ihf : consts_defined_red renv f -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_iha : consts_defined_red renv a -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hd : AndType (consts_defined_red renv f) (consts_defined_red renv a)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app f a)) (OptionType.some KExpr e2)) => (fun (hda : consts_defined_red renv a) => KExpr.rec (fun (g : KExpr) => (consts_defined_red renv g -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv g) (OptionType.some KExpr e2) -> consts_defined_red renv e2) -> consts_defined_red renv g -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a g (reduce_once_red renv g)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (fun (n : Level) (ihg : consts_defined_red renv (KExpr.sort n) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hdg : consts_defined_red renv (KExpr.sort n)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.sort n) (reduce_once_red renv (KExpr.sort n))) (OptionType.some KExpr e2)) => reduce_app_ilift_defined renv (KExpr.sort n) a e2 hgood (ihg hdg) (AndType.intro (consts_defined_red renv (KExpr.sort n)) (consts_defined_red renv a) hdg hda) h) (fun (i : Nat) (ihg : consts_defined_red renv (KExpr.bvar i) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hdg : consts_defined_red renv (KExpr.bvar i)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.bvar i) (reduce_once_red renv (KExpr.bvar i))) (OptionType.some KExpr e2)) => reduce_app_ilift_defined renv (KExpr.bvar i) a e2 hgood (ihg hdg) (AndType.intro (consts_defined_red renv (KExpr.bvar i)) (consts_defined_red renv a) hdg hda) h) (fun (g1 : KExpr) (g2 : KExpr) (_j1 : (consts_defined_red renv g1 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv g1) (OptionType.some KExpr e2) -> consts_defined_red renv e2) -> consts_defined_red renv g1 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a g1 (reduce_once_red renv g1)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_j2 : (consts_defined_red renv g2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv g2) (OptionType.some KExpr e2) -> consts_defined_red renv e2) -> consts_defined_red renv g2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a g2 (reduce_once_red renv g2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (ihg : consts_defined_red renv (KExpr.app g1 g2) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app g1 g2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hdg : consts_defined_red renv (KExpr.app g1 g2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.app g1 g2) (reduce_once_red renv (KExpr.app g1 g2))) (OptionType.some KExpr e2)) => reduce_app_ilift_defined renv (KExpr.app g1 g2) a e2 hgood (ihg hdg) (AndType.intro (consts_defined_red renv (KExpr.app g1 g2)) (consts_defined_red renv a) hdg hda) h) (fun (ty2 : KExpr) (b2 : KExpr) (_j1 : (consts_defined_red renv ty2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty2) (OptionType.some KExpr e2) -> consts_defined_red renv e2) -> consts_defined_red renv ty2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a ty2 (reduce_once_red renv ty2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_j2 : (consts_defined_red renv b2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b2) (OptionType.some KExpr e2) -> consts_defined_red renv e2) -> consts_defined_red renv b2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a b2 (reduce_once_red renv b2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (ihg : consts_defined_red renv (KExpr.lam ty2 b2) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lam ty2 b2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hdg : consts_defined_red renv (KExpr.lam ty2 b2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.lam ty2 b2) (reduce_once_red renv (KExpr.lam ty2 b2))) (OptionType.some KExpr e2)) => Eq.rec KExpr (instantiate b2 a) (fun (x : KExpr) (_hx : Eq KExpr (instantiate b2 a) x) => consts_defined_red renv x) (inst_defined_red renv a hda b2 Nat.zero (AndType.right (consts_defined_red renv ty2) (consts_defined_red renv b2) hdg)) e2 (option_some_inj KExpr (instantiate b2 a) e2 h)) (fun (ty2 : KExpr) (b2 : KExpr) (_j1 : (consts_defined_red renv ty2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty2) (OptionType.some KExpr e2) -> consts_defined_red renv e2) -> consts_defined_red renv ty2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a ty2 (reduce_once_red renv ty2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_j2 : (consts_defined_red renv b2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b2) (OptionType.some KExpr e2) -> consts_defined_red renv e2) -> consts_defined_red renv b2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a b2 (reduce_once_red renv b2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (ihg : consts_defined_red renv (KExpr.pi ty2 b2) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty2 b2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hdg : consts_defined_red renv (KExpr.pi ty2 b2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.pi ty2 b2) (reduce_once_red renv (KExpr.pi ty2 b2))) (OptionType.some KExpr e2)) => reduce_app_ilift_defined renv (KExpr.pi ty2 b2) a e2 hgood (ihg hdg) (AndType.intro (consts_defined_red renv (KExpr.pi ty2 b2)) (consts_defined_red renv a) hdg hda) h) (fun (n2 : Name) (us2 : ListType Level) (ihg : consts_defined_red renv (KExpr.const n2 us2) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n2 us2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hdg : consts_defined_red renv (KExpr.const n2 us2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.const n2 us2) (reduce_once_red renv (KExpr.const n2 us2))) (OptionType.some KExpr e2)) => reduce_app_ilift_defined renv (KExpr.const n2 us2) a e2 hgood (ihg hdg) (AndType.intro (consts_defined_red renv (KExpr.const n2 us2)) (consts_defined_red renv a) hdg hda) h) (fun (ty2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_j1 : (consts_defined_red renv ty2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty2) (OptionType.some KExpr e2) -> consts_defined_red renv e2) -> consts_defined_red renv ty2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a ty2 (reduce_once_red renv ty2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_j2 : (consts_defined_red renv v2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv v2) (OptionType.some KExpr e2) -> consts_defined_red renv e2) -> consts_defined_red renv v2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a v2 (reduce_once_red renv v2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_j3 : (consts_defined_red renv b2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b2) (OptionType.some KExpr e2) -> consts_defined_red renv e2) -> consts_defined_red renv b2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a b2 (reduce_once_red renv b2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (ihg : consts_defined_red renv (KExpr.let_ ty2 v2 b2) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty2 v2 b2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hdg : consts_defined_red renv (KExpr.let_ ty2 v2 b2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.let_ ty2 v2 b2) (reduce_once_red renv (KExpr.let_ ty2 v2 b2))) (OptionType.some KExpr e2)) => reduce_app_ilift_defined renv (KExpr.let_ ty2 v2 b2) a e2 hgood (ihg hdg) (AndType.intro (consts_defined_red renv (KExpr.let_ ty2 v2 b2)) (consts_defined_red renv a) hdg hda) h) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_j1 : (consts_defined_red renv sub2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub2) (OptionType.some KExpr e2) -> consts_defined_red renv e2) -> consts_defined_red renv sub2 -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_app_head_red renv a sub2 (reduce_once_red renv sub2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (ihg : consts_defined_red renv (KExpr.proj s2 i2 sub2) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s2 i2 sub2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hdg : consts_defined_red renv (KExpr.proj s2 i2 sub2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.proj s2 i2 sub2) (reduce_once_red renv (KExpr.proj s2 i2 sub2))) (OptionType.some KExpr e2)) => reduce_app_ilift_defined renv (KExpr.proj s2 i2 sub2) a e2 hgood (ihg hdg) (AndType.intro (consts_defined_red renv (KExpr.proj s2 i2 sub2)) (consts_defined_red renv a) hdg hda) h) (fun (v2 : Nat) (ihg : consts_defined_red renv (KExpr.lit v2) -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v2)) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hdg : consts_defined_red renv (KExpr.lit v2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head_red renv a (KExpr.lit v2) (reduce_once_red renv (KExpr.lit v2))) (OptionType.some KExpr e2)) => reduce_app_ilift_defined renv (KExpr.lit v2) a e2 hgood (ihg hdg) (AndType.intro (consts_defined_red renv (KExpr.lit v2)) (consts_defined_red renv a) hdg hda) h) f ihf (AndType.left (consts_defined_red renv f) (consts_defined_red renv a) hd) e2 h) (AndType.right (consts_defined_red renv f) (consts_defined_red renv a) hd)) (fun (ty : KExpr) (b : KExpr) (_i1 : consts_defined_red renv ty -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_i2 : consts_defined_red renv b -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_hd : consts_defined_red renv (KExpr.lam ty b)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lam ty b)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (consts_defined_red renv e2) h) (fun (ty : KExpr) (b : KExpr) (_i1 : consts_defined_red renv ty -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_i2 : consts_defined_red renv b -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_hd : consts_defined_red renv (KExpr.pi ty b)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (consts_defined_red renv e2) h) (fun (n : Name) (us : ListType Level) (_hd : consts_defined_red renv (KExpr.const n us)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.some KExpr e2)) => AndType.right (red_closed_at e2 Nat.zero) (consts_defined_red renv e2) (AndType.left (forall (n2 : Name) (v : KExpr), Eq (OptionType KExpr) (defval_for (red_def renv) n2) (OptionType.some KExpr v) -> AndType (red_closed_at v Nat.zero) (consts_defined_red renv v)) (forall (rn : Name) (cn : Name) (rule : RecRule), Eq (OptionType RecRule) (recrule_for (red_rec renv) rn cn) (OptionType.some RecRule rule) -> AndType (red_closed_at (recrule_rhs rule) Nat.zero) (consts_defined_red renv (recrule_rhs rule))) hgood n e2 h)) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : consts_defined_red renv ty -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_i2 : consts_defined_red renv v -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv v) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (_i3 : consts_defined_red renv b -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hd : AndType (consts_defined_red renv ty) (AndType (consts_defined_red renv v) (consts_defined_red renv b))) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.some KExpr e2)) => Eq.rec KExpr (instantiate b v) (fun (x : KExpr) (_hx : Eq KExpr (instantiate b v) x) => consts_defined_red renv x) (inst_defined_red renv v (AndType.left (consts_defined_red renv v) (consts_defined_red renv b) (AndType.right (consts_defined_red renv ty) (AndType (consts_defined_red renv v) (consts_defined_red renv b)) hd)) b Nat.zero (AndType.right (consts_defined_red renv v) (consts_defined_red renv b) (AndType.right (consts_defined_red renv ty) (AndType (consts_defined_red renv v) (consts_defined_red renv b)) hd))) e2 (option_some_inj KExpr (instantiate b v) e2 h)) (fun (s : Name) (i : Nat) (sub : KExpr) (ih : consts_defined_red renv sub -> forall (e2 : KExpr), Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.some KExpr e2) -> consts_defined_red renv e2) (hd : consts_defined_red renv sub) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.some KExpr e2)) => reduce_proj_lift_defined renv s i sub e2 (ih hd) h) (fun (v : Nat) (_hd : consts_defined_red renv (KExpr.lit v)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (consts_defined_red renv e2) h) e".to_string()),
            is_axiom: false,
            description: "3-WAY DEFINEDNESS PRESERVATION (X17c-2c t2, round-6 reduceOnceRed_preserves_defined): one 3-way executable step out of a two-env-defined term stays defined over a good environment — β/ζ by inst_defined_red, δ by red_env_good's definiens half (definedness component), whole-spine ι by iota_reduct_defined_red, app/proj congruence by the ilift/proj-lift defined helpers. No closedness hypothesis needed (definedness is depth-free). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once_red".to_string(),
                "reduce_app_head_red".to_string(),
                "reduce_app_ilift_defined".to_string(),
                "reduce_proj_lift_defined".to_string(),
                "consts_defined_red".to_string(),
                "red_env_good".to_string(),
                "iota_reduct_defined_red".to_string(),
                "inst_defined_red".to_string(),
                "red_closed_at".to_string(),
                "recrule_for".to_string(),
                "recrule_rhs".to_string(),
                "defval_for".to_string(),
                "red_def".to_string(),
                "red_rec".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "KExpr.rec".to_string(),
                "Eq.rec".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_inductive(
            r"inductive silent_head_class_red : KExpr -> Type
| lam : forall (ty : KExpr) (b : KExpr), silent_head_class_red (KExpr.lam ty b)
| neutral : forall (e : KExpr), is_neutral e -> silent_head_class_red e
| stuck : forall (e : KExpr), whnf_stuck_head e -> silent_head_class_red e",
            "silent_head_class_red e (X17c-2c t3): the head-class of a 3-way executable \
             fixpoint — a lambda, a delta/iota-silent neutral spine (is_neutral, whose \
             const arm carries const_whnf over the_red_env), or an honestly stuck head \
             (whnf_stuck_head). The round-6 SilentHeadClass, spec dialect.",
        )?;

        self.add_definition(SpecDefinition {
            name: "silent_head_class_of_none_red".to_string(),
            type_src: "forall (e : KExpr), Eq (OptionType KExpr) (reduce_once_red the_red_env e) (OptionType.none KExpr) -> red_closed_at e Nat.zero -> consts_defined_red the_red_env e -> silent_head_class_red e".to_string(),
            value_src: Some("fun (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => Eq (OptionType KExpr) (reduce_once_red the_red_env e0) (OptionType.none KExpr) -> red_closed_at e0 Nat.zero -> consts_defined_red the_red_env e0 -> silent_head_class_red e0) (fun (n : Level) (_h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.sort n)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.sort n) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.sort n)) => silent_head_class_red.stuck (KExpr.sort n) (whnf_stuck_head.sort n)) (fun (i : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.bvar i)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.bvar i) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.bvar i)) => LiftP.rec (Le (Nat.succ i) Nat.zero) (fun (_l : LiftP (Le (Nat.succ i) Nat.zero)) => silent_head_class_red (KExpr.bvar i)) (fun (l : Le (Nat.succ i) Nat.zero) => nat_zero_ne_succ i (silent_head_class_red (KExpr.bvar i)) (Eq.symm Nat (Nat.succ i) Nat.zero (le_zero_eq_zero (Nat.succ i) Nat.zero l (Eq.refl Nat Nat.zero)))) hc) (fun (f : KExpr) (a : KExpr) (ihf : Eq (OptionType KExpr) (reduce_once_red the_red_env f) (OptionType.none KExpr) -> red_closed_at f Nat.zero -> consts_defined_red the_red_env f -> silent_head_class_red f) (_iha : Eq (OptionType KExpr) (reduce_once_red the_red_env a) (OptionType.none KExpr) -> red_closed_at a Nat.zero -> consts_defined_red the_red_env a -> silent_head_class_red a) (h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.app f a)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.app f a) Nat.zero) (hd : consts_defined_red the_red_env (KExpr.app f a)) => silent_head_class_red.rec (fun (e0 : KExpr) (_c : silent_head_class_red e0) => Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.app e0 a)) (OptionType.none KExpr) -> silent_head_class_red (KExpr.app e0 a)) (fun (ty : KExpr) (b : KExpr) (hl : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.app (KExpr.lam ty b) a)) (OptionType.none KExpr)) => opt_none_ne_some_t KExpr (instantiate b a) (silent_head_class_red (KExpr.app (KExpr.lam ty b) a)) (Eq.symm (OptionType KExpr) (OptionType.some KExpr (instantiate b a)) (OptionType.none KExpr) hl)) (fun (e : KExpr) (hn : is_neutral e) (_h2 : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.app e a)) (OptionType.none KExpr)) => silent_head_class_red.neutral (KExpr.app e a) (is_neutral.app e a hn)) (fun (e : KExpr) (hs : whnf_stuck_head e) (_h2 : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.app e a)) (OptionType.none KExpr)) => silent_head_class_red.stuck (KExpr.app e a) (whnf_stuck_head.app e a hs)) f (ihf (red_app_none_head_inv the_red_env f a h) (AndType.left (red_closed_at f Nat.zero) (red_closed_at a Nat.zero) hc) (AndType.left (consts_defined_red the_red_env f) (consts_defined_red the_red_env a) hd)) h) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red the_red_env ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red the_red_env ty -> silent_head_class_red ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red the_red_env b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red the_red_env b -> silent_head_class_red b) (_h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.lam ty b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.lam ty b) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.lam ty b)) => silent_head_class_red.lam ty b) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red the_red_env ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red the_red_env ty -> silent_head_class_red ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red the_red_env b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red the_red_env b -> silent_head_class_red b) (_h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.pi ty b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.pi ty b) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.pi ty b)) => silent_head_class_red.stuck (KExpr.pi ty b) (whnf_stuck_head.pi ty b)) (fun (n : Name) (us : ListType Level) (h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.const n us)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.const n us) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.const n us)) => silent_head_class_red.neutral (KExpr.const n us) (is_neutral.const n us (reduce_once_red_none_delta_none the_red_env (KExpr.const n us) h))) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red the_red_env ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red the_red_env ty -> silent_head_class_red ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red the_red_env v) (OptionType.none KExpr) -> red_closed_at v Nat.zero -> consts_defined_red the_red_env v -> silent_head_class_red v) (_i3 : Eq (OptionType KExpr) (reduce_once_red the_red_env b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red the_red_env b -> silent_head_class_red b) (h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.let_ ty v b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.let_ ty v b) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.let_ ty v b)) => opt_none_ne_some_t KExpr (instantiate b v) (silent_head_class_red (KExpr.let_ ty v b)) (Eq.symm (OptionType KExpr) (OptionType.some KExpr (instantiate b v)) (OptionType.none KExpr) h)) (fun (s : Name) (i : Nat) (sub : KExpr) (ih : Eq (OptionType KExpr) (reduce_once_red the_red_env sub) (OptionType.none KExpr) -> red_closed_at sub Nat.zero -> consts_defined_red the_red_env sub -> silent_head_class_red sub) (h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.proj s i sub)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.proj s i sub) Nat.zero) (hd : consts_defined_red the_red_env (KExpr.proj s i sub)) => silent_head_class_red.rec (fun (e0 : KExpr) (_c : silent_head_class_red e0) => silent_head_class_red (KExpr.proj s i e0)) (fun (ty : KExpr) (b : KExpr) => silent_head_class_red.stuck (KExpr.proj s i (KExpr.lam ty b)) (whnf_stuck_head.projw s i (KExpr.lam ty b) (is_whnf.lam ty b))) (fun (e : KExpr) (hn : is_neutral e) => silent_head_class_red.stuck (KExpr.proj s i e) (whnf_stuck_head.projw s i e (is_whnf.neutral e hn))) (fun (e : KExpr) (hh : whnf_stuck_head e) => silent_head_class_red.stuck (KExpr.proj s i e) (whnf_stuck_head.proj s i e hh)) sub (ih (proj_lift_none_inv s i (reduce_once_red the_red_env sub) h) hc hd)) (fun (v : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.lit v)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.lit v) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.lit v)) => silent_head_class_red.stuck (KExpr.lit v) (whnf_stuck_head.lit v)) e".to_string()),
            is_axiom: false,
            description: "3-WAY HEAD CLASSIFICATION (X17c-2c t3, round-6 silentHeadClass_of_none): a closedAt-0, two-env-defined 3-way executable fixpoint has a lambda, neutral (delta/iota-silent const spine — const_whnf discharged from the delta-converse reduce_once_red_none_delta_none), or honestly-stuck head. 9-arm KExpr.rec with motive-carrying-hypothesis eliminations on the app/proj head classes; bvar refuted by LiftP-closedness. Pinned to the_red_env (const_whnf's fixed env). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "silent_head_class_red".to_string(),
                "silent_head_class_red.lam".to_string(),
                "silent_head_class_red.neutral".to_string(),
                "silent_head_class_red.stuck".to_string(),
                "silent_head_class_red.rec".to_string(),
                "is_neutral".to_string(),
                "is_neutral.const".to_string(),
                "is_neutral.app".to_string(),
                "is_whnf.lam".to_string(),
                "is_whnf.neutral".to_string(),
                "whnf_stuck_head.sort".to_string(),
                "whnf_stuck_head.pi".to_string(),
                "whnf_stuck_head.app".to_string(),
                "whnf_stuck_head.proj".to_string(),
                "whnf_stuck_head.projw".to_string(),
                "whnf_stuck_head.lit".to_string(),
                "reduce_once_red".to_string(),
                "reduce_once_red_none_delta_none".to_string(),
                "red_app_none_head_inv".to_string(),
                "proj_lift_none_inv".to_string(),
                "the_red_env".to_string(),
                "red_closed_at".to_string(),
                "consts_defined_red".to_string(),
                "LiftP.rec".to_string(),
                "Le".to_string(),
                "le_zero_eq_zero".to_string(),
                "nat_zero_ne_succ".to_string(),
                "opt_none_ne_some_t".to_string(),
                "instantiate".to_string(),
                "AndType.left".to_string(),
                "KExpr.rec".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_once_red_none_classifies".to_string(),
            type_src: "forall (e : KExpr), Eq (OptionType KExpr) (reduce_once_red the_red_env e) (OptionType.none KExpr) -> red_closed_at e Nat.zero -> consts_defined_red the_red_env e -> whnf_noredex_class e".to_string(),
            value_src: Some("fun (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => Eq (OptionType KExpr) (reduce_once_red the_red_env e0) (OptionType.none KExpr) -> red_closed_at e0 Nat.zero -> consts_defined_red the_red_env e0 -> whnf_noredex_class e0) (fun (n : Level) (_h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.sort n)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.sort n) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.sort n)) => whnf_noredex_class.done (KExpr.sort n) (is_whnf.sort n)) (fun (i : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.bvar i)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.bvar i) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.bvar i)) => LiftP.rec (Le (Nat.succ i) Nat.zero) (fun (_l : LiftP (Le (Nat.succ i) Nat.zero)) => whnf_noredex_class (KExpr.bvar i)) (fun (l : Le (Nat.succ i) Nat.zero) => nat_zero_ne_succ i (whnf_noredex_class (KExpr.bvar i)) (Eq.symm Nat (Nat.succ i) Nat.zero (le_zero_eq_zero (Nat.succ i) Nat.zero l (Eq.refl Nat Nat.zero)))) hc) (fun (f : KExpr) (a : KExpr) (_ihf : Eq (OptionType KExpr) (reduce_once_red the_red_env f) (OptionType.none KExpr) -> red_closed_at f Nat.zero -> consts_defined_red the_red_env f -> whnf_noredex_class f) (_iha : Eq (OptionType KExpr) (reduce_once_red the_red_env a) (OptionType.none KExpr) -> red_closed_at a Nat.zero -> consts_defined_red the_red_env a -> whnf_noredex_class a) (h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.app f a)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.app f a) Nat.zero) (hd : consts_defined_red the_red_env (KExpr.app f a)) => silent_head_class_red.rec (fun (e0 : KExpr) (_c : silent_head_class_red e0) => Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.app e0 a)) (OptionType.none KExpr) -> whnf_noredex_class (KExpr.app e0 a)) (fun (ty : KExpr) (b : KExpr) (hl : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.app (KExpr.lam ty b) a)) (OptionType.none KExpr)) => opt_none_ne_some_t KExpr (instantiate b a) (whnf_noredex_class (KExpr.app (KExpr.lam ty b) a)) (Eq.symm (OptionType KExpr) (OptionType.some KExpr (instantiate b a)) (OptionType.none KExpr) hl)) (fun (e : KExpr) (hn : is_neutral e) (_h2 : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.app e a)) (OptionType.none KExpr)) => whnf_noredex_class.done (KExpr.app e a) (is_whnf.neutral (KExpr.app e a) (is_neutral.app e a hn))) (fun (e : KExpr) (hs : whnf_stuck_head e) (_h2 : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.app e a)) (OptionType.none KExpr)) => whnf_noredex_class.stuck e a hs) f (silent_head_class_of_none_red f (red_app_none_head_inv the_red_env f a h) (AndType.left (red_closed_at f Nat.zero) (red_closed_at a Nat.zero) hc) (AndType.left (consts_defined_red the_red_env f) (consts_defined_red the_red_env a) hd)) h) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red the_red_env ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red the_red_env ty -> whnf_noredex_class ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red the_red_env b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red the_red_env b -> whnf_noredex_class b) (_h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.lam ty b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.lam ty b) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.lam ty b)) => whnf_noredex_class.done (KExpr.lam ty b) (is_whnf.lam ty b)) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red the_red_env ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red the_red_env ty -> whnf_noredex_class ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red the_red_env b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red the_red_env b -> whnf_noredex_class b) (_h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.pi ty b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.pi ty b) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.pi ty b)) => whnf_noredex_class.done (KExpr.pi ty b) (is_whnf.pi ty b)) (fun (n : Name) (us : ListType Level) (h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.const n us)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.const n us) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.const n us)) => whnf_noredex_class.done (KExpr.const n us) (is_whnf.neutral (KExpr.const n us) (is_neutral.const n us (reduce_once_red_none_delta_none the_red_env (KExpr.const n us) h)))) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red the_red_env ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red the_red_env ty -> whnf_noredex_class ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red the_red_env v) (OptionType.none KExpr) -> red_closed_at v Nat.zero -> consts_defined_red the_red_env v -> whnf_noredex_class v) (_i3 : Eq (OptionType KExpr) (reduce_once_red the_red_env b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red the_red_env b -> whnf_noredex_class b) (h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.let_ ty v b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.let_ ty v b) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.let_ ty v b)) => opt_none_ne_some_t KExpr (instantiate b v) (whnf_noredex_class (KExpr.let_ ty v b)) (Eq.symm (OptionType KExpr) (OptionType.some KExpr (instantiate b v)) (OptionType.none KExpr) h)) (fun (s : Name) (i : Nat) (sub : KExpr) (ih : Eq (OptionType KExpr) (reduce_once_red the_red_env sub) (OptionType.none KExpr) -> red_closed_at sub Nat.zero -> consts_defined_red the_red_env sub -> whnf_noredex_class sub) (h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.proj s i sub)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.proj s i sub) Nat.zero) (hd : consts_defined_red the_red_env (KExpr.proj s i sub)) => noredex_proj_class s i sub (ih (proj_lift_none_inv s i (reduce_once_red the_red_env sub) h) hc hd)) (fun (v : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red the_red_env (KExpr.lit v)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.lit v) Nat.zero) (_hd : consts_defined_red the_red_env (KExpr.lit v)) => whnf_noredex_class.done (KExpr.lit v) (is_whnf.lit v)) e".to_string()),
            is_axiom: false,
            description: "THE 3-WAY FIXPOINT CLASSIFICATION (X17c-2c t3, round-6 reduceOnceRed_none_classifies): a closedAt-0, two-env-defined 3-way executable fixpoint is a landed is_whnf value (including delta/iota-silent neutral recursor spines — const_whnf discharged from the delta-converse) or an honest stuck application/projection residual. Pinned to the_red_env. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_noredex_class".to_string(),
                "whnf_noredex_class.done".to_string(),
                "whnf_noredex_class.stuck".to_string(),
                "is_whnf.sort".to_string(),
                "is_whnf.lam".to_string(),
                "is_whnf.pi".to_string(),
                "is_whnf.lit".to_string(),
                "is_whnf.neutral".to_string(),
                "is_neutral.const".to_string(),
                "is_neutral.app".to_string(),
                "whnf_stuck_head".to_string(),
                "silent_head_class_red".to_string(),
                "silent_head_class_red.rec".to_string(),
                "silent_head_class_of_none_red".to_string(),
                "noredex_proj_class".to_string(),
                "reduce_once_red".to_string(),
                "reduce_once_red_none_delta_none".to_string(),
                "red_app_none_head_inv".to_string(),
                "proj_lift_none_inv".to_string(),
                "the_red_env".to_string(),
                "red_closed_at".to_string(),
                "consts_defined_red".to_string(),
                "LiftP.rec".to_string(),
                "Le".to_string(),
                "le_zero_eq_zero".to_string(),
                "nat_zero_ne_succ".to_string(),
                "opt_none_ne_some_t".to_string(),
                "instantiate".to_string(),
                "AndType.left".to_string(),
                "KExpr.rec".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_fuel_red_classifies".to_string(),
            type_src: "forall (hEnv : red_env_good the_red_env) (fuel : Nat) (e : KExpr) (r : KExpr), red_closed_at e Nat.zero -> consts_defined_red the_red_env e -> Eq (OptionType KExpr) (whnf_fuel_red the_red_env fuel e) (OptionType.some KExpr r) -> whnf_noredex_class r".to_string(),
            value_src: Some("fun (hEnv : red_env_good the_red_env) (fuel : Nat) => Nat.rec (fun (k : Nat) => forall (e : KExpr) (r : KExpr), red_closed_at e Nat.zero -> consts_defined_red the_red_env e -> Eq (OptionType KExpr) (whnf_fuel_red the_red_env k e) (OptionType.some KExpr r) -> whnf_noredex_class r) (fun (e : KExpr) (r : KExpr) (_hc : red_closed_at e Nat.zero) (_hd : consts_defined_red the_red_env e) (h : Eq (OptionType KExpr) (whnf_fuel_red the_red_env Nat.zero e) (OptionType.some KExpr r)) => opt_none_ne_some_t KExpr r (whnf_noredex_class r) h) (fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), red_closed_at e0 Nat.zero -> consts_defined_red the_red_env e0 -> Eq (OptionType KExpr) (whnf_fuel_red the_red_env k e0) (OptionType.some KExpr r0) -> whnf_noredex_class r0) (e : KExpr) (r : KExpr) (hc : red_closed_at e Nat.zero) (hd : consts_defined_red the_red_env e) (h : Eq (OptionType KExpr) (whnf_fuel_red the_red_env (Nat.succ k) e) (OptionType.some KExpr r)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red the_red_env e) o -> Eq (OptionType KExpr) (loop_dispatch o e (fun (e2 : KExpr) => whnf_fuel_red the_red_env k e2)) (OptionType.some KExpr r) -> whnf_noredex_class r) (fun (heq : Eq (OptionType KExpr) (reduce_once_red the_red_env e) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e (fun (e2 : KExpr) => whnf_fuel_red the_red_env k e2)) (OptionType.some KExpr r)) => Eq.rec KExpr e (fun (x : KExpr) (_hx : Eq KExpr e x) => whnf_noredex_class x) (reduce_once_red_none_classifies e heq hc hd) r (option_some_inj KExpr e r h2)) (fun (e2 : KExpr) (heq : Eq (OptionType KExpr) (reduce_once_red the_red_env e) (OptionType.some KExpr e2)) (h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.some KExpr e2) e (fun (e3 : KExpr) => whnf_fuel_red the_red_env k e3)) (OptionType.some KExpr r)) => ih e2 r (reduce_once_red_preserves_closed the_red_env hEnv e hc e2 heq) (reduce_once_red_preserves_defined the_red_env hEnv e hd e2 heq) h2) (reduce_once_red the_red_env e) (Eq.refl (OptionType KExpr) (reduce_once_red the_red_env e)) h) fuel".to_string()),
            is_axiom: false,
            description: "THE 3-WAY EXECUTABLE-LOOP CAPSTONE (X17c-2c t4, round-6 whnfFuelRed_classifies): over the_red_env (good), EVERY successful fuel-bounded 3-way loop result on a closedAt-0, two-env-defined term CLASSIFIES — a landed is_whnf value (incl. delta/iota-silent neutral recursor spines) or the honest stuck residual; a none is only ever the honest fuel bail. Nat.rec fuel induction threading both 3-way preservations, closing at the fixpoint with the 3-way classification. With this the in-spec 3-way executable loop (beta/zeta + head-delta + whole-spine iota) is verified end to end in Clean's own kernel. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel_red".to_string(),
                "loop_dispatch".to_string(),
                "reduce_once_red".to_string(),
                "reduce_once_red_none_classifies".to_string(),
                "reduce_once_red_preserves_closed".to_string(),
                "reduce_once_red_preserves_defined".to_string(),
                "red_env_good".to_string(),
                "the_red_env".to_string(),
                "red_closed_at".to_string(),
                "consts_defined_red".to_string(),
                "whnf_noredex_class".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "Nat.rec".to_string(),
                "OptionType.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_inductive(
            r"inductive is_neutral_red (renv : RedEnv) : KExpr -> Type
| const : forall (n : Name) (us : ListType Level), Eq (OptionType KExpr) (delta_reduct (red_def renv) (KExpr.const n us)) (OptionType.none KExpr) -> is_neutral_red renv (KExpr.const n us)
| app : forall (f : KExpr) (a : KExpr), is_neutral_red renv f -> is_neutral_red renv (KExpr.app f a)",
            "Parametric neutral WHNF heads over an arbitrary RedEnv (X17-gen): a constant that does NOT delta-unfold over renv (carrying the raw delta_reduct(red_def renv)=none evidence, NOT the the_red_env-pinned const_whnf) and its application spines. The env-generalized mirror of is_neutral.",
        )?;

        self.add_inductive(
            r"inductive is_whnf_red (renv : RedEnv) : KExpr -> Type
| sort : forall (n : Level), is_whnf_red renv (KExpr.sort n)
| lam : forall (ty : KExpr) (body : KExpr), is_whnf_red renv (KExpr.lam ty body)
| pi : forall (ty : KExpr) (body : KExpr), is_whnf_red renv (KExpr.pi ty body)
| neutral : forall (e : KExpr), is_neutral_red renv e -> is_whnf_red renv e
| proj : forall (s : Name) (i : Nat) (sub : KExpr), is_whnf_red renv sub -> is_whnf_red renv (KExpr.proj s i sub)
| lit : forall (v : Nat), is_whnf_red renv (KExpr.lit v)",
            "Parametric WHNF predicate over an arbitrary RedEnv (X17-gen): the env-generalized mirror of is_whnf (neutral arm carries is_neutral_red renv).",
        )?;

        self.add_inductive(
            r"inductive whnf_stuck_head_red (renv : RedEnv) : KExpr -> Type
| sort : forall (n : Level), whnf_stuck_head_red renv (KExpr.sort n)
| pi : forall (ty : KExpr) (body : KExpr), whnf_stuck_head_red renv (KExpr.pi ty body)
| app : forall (f : KExpr) (a : KExpr), whnf_stuck_head_red renv f -> whnf_stuck_head_red renv (KExpr.app f a)
| proj : forall (s : Name) (i : Nat) (sub : KExpr), whnf_stuck_head_red renv sub -> whnf_stuck_head_red renv (KExpr.proj s i sub)
| projw : forall (s : Name) (i : Nat) (sub : KExpr), is_whnf_red renv sub -> whnf_stuck_head_red renv (KExpr.proj s i sub)
| lit : forall (v : Nat), whnf_stuck_head_red renv (KExpr.lit v)",
            "Parametric stuck-head predicate over an arbitrary RedEnv (X17-gen): the env-generalized mirror of whnf_stuck_head (projw carries is_whnf_red renv).",
        )?;

        self.add_inductive(
            r"inductive whnf_noredex_class_red (renv : RedEnv) : KExpr -> Type
| done : forall (e : KExpr), is_whnf_red renv e -> whnf_noredex_class_red renv e
| stuck : forall (f : KExpr) (a : KExpr), whnf_stuck_head_red renv f -> whnf_noredex_class_red renv (KExpr.app f a)
| stuck_proj : forall (s : Name) (i : Nat) (sub : KExpr), whnf_stuck_head_red renv sub -> whnf_noredex_class_red renv (KExpr.proj s i sub)",
            "Parametric no-redex classification over an arbitrary RedEnv (X17-gen): a landed is_whnf_red value, or an honest stuck application/projection residual. The env-generalized mirror of whnf_noredex_class.",
        )?;

        self.add_inductive(
            r"inductive silent_head_class_red_gen (renv : RedEnv) : KExpr -> Type
| lam : forall (ty : KExpr) (b : KExpr), silent_head_class_red_gen renv (KExpr.lam ty b)
| neutral : forall (e : KExpr), is_neutral_red renv e -> silent_head_class_red_gen renv e
| stuck : forall (e : KExpr), whnf_stuck_head_red renv e -> silent_head_class_red_gen renv e",
            "Parametric head-class of a 3-way executable fixpoint over an arbitrary RedEnv (X17-gen): a lambda, a delta/iota-silent neutral spine, or an honestly stuck head. The env-generalized SilentHeadClass.",
        )?;

        self.add_definition(SpecDefinition {
            name: "noredex_proj_class_red".to_string(),
            type_src: "forall (renv : RedEnv) (s : Name) (i : Nat) (sub : KExpr), whnf_noredex_class_red renv sub -> whnf_noredex_class_red renv (KExpr.proj s i sub)".to_string(),
            value_src: Some("fun (renv : RedEnv) (s : Name) (i : Nat) (sub : KExpr) (c : whnf_noredex_class_red renv sub) => whnf_noredex_class_red.rec renv (fun (e0 : KExpr) (_c0 : whnf_noredex_class_red renv e0) => whnf_noredex_class_red renv (KExpr.proj s i e0)) (fun (e0 : KExpr) (hw : is_whnf_red renv e0) => whnf_noredex_class_red.done renv (KExpr.proj s i e0) (is_whnf_red.proj renv s i e0 hw)) (fun (f : KExpr) (a : KExpr) (hs : whnf_stuck_head_red renv f) => whnf_noredex_class_red.stuck_proj renv s i (KExpr.app f a) (whnf_stuck_head_red.app renv f a hs)) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (hs : whnf_stuck_head_red renv sub2) => whnf_noredex_class_red.stuck_proj renv s i (KExpr.proj s2 i2 sub2) (whnf_stuck_head_red.proj renv s2 i2 sub2 hs)) sub c".to_string()),
            is_axiom: false,
            description: "PROJ CLASS CONGRUENCE, parametric (X17-gen): the no-redex class lifts through a projection over any renv. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_noredex_class_red".to_string(),
                "whnf_noredex_class_red.rec".to_string(),
                "whnf_noredex_class_red.done".to_string(),
                "whnf_noredex_class_red.stuck_proj".to_string(),
                "is_whnf_red.proj".to_string(),
                "whnf_stuck_head_red.app".to_string(),
                "whnf_stuck_head_red.proj".to_string(),
                "KExpr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "silent_head_class_of_none_red_gen".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr), Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.none KExpr) -> red_closed_at e Nat.zero -> consts_defined_red renv e -> silent_head_class_red_gen renv e".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => Eq (OptionType KExpr) (reduce_once_red renv e0) (OptionType.none KExpr) -> red_closed_at e0 Nat.zero -> consts_defined_red renv e0 -> silent_head_class_red_gen renv e0) (fun (n : Level) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.sort n) Nat.zero) (_hd : consts_defined_red renv (KExpr.sort n)) => silent_head_class_red_gen.stuck renv (KExpr.sort n) (whnf_stuck_head_red.sort renv n)) (fun (i : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.bvar i) Nat.zero) (_hd : consts_defined_red renv (KExpr.bvar i)) => LiftP.rec (Le (Nat.succ i) Nat.zero) (fun (_l : LiftP (Le (Nat.succ i) Nat.zero)) => silent_head_class_red_gen renv (KExpr.bvar i)) (fun (l : Le (Nat.succ i) Nat.zero) => nat_zero_ne_succ i (silent_head_class_red_gen renv (KExpr.bvar i)) (Eq.symm Nat (Nat.succ i) Nat.zero (le_zero_eq_zero (Nat.succ i) Nat.zero l (Eq.refl Nat Nat.zero)))) hc) (fun (f : KExpr) (a : KExpr) (ihf : Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.none KExpr) -> red_closed_at f Nat.zero -> consts_defined_red renv f -> silent_head_class_red_gen renv f) (_iha : Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.none KExpr) -> red_closed_at a Nat.zero -> consts_defined_red renv a -> silent_head_class_red_gen renv a) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app f a)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.app f a) Nat.zero) (hd : consts_defined_red renv (KExpr.app f a)) => silent_head_class_red_gen.rec renv (fun (e0 : KExpr) (_c : silent_head_class_red_gen renv e0) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app e0 a)) (OptionType.none KExpr) -> silent_head_class_red_gen renv (KExpr.app e0 a)) (fun (ty : KExpr) (b : KExpr) (hl : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app (KExpr.lam ty b) a)) (OptionType.none KExpr)) => opt_none_ne_some_t KExpr (instantiate b a) (silent_head_class_red_gen renv (KExpr.app (KExpr.lam ty b) a)) (Eq.symm (OptionType KExpr) (OptionType.some KExpr (instantiate b a)) (OptionType.none KExpr) hl)) (fun (e : KExpr) (hn : is_neutral_red renv e) (_h2 : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app e a)) (OptionType.none KExpr)) => silent_head_class_red_gen.neutral renv (KExpr.app e a) (is_neutral_red.app renv e a hn)) (fun (e : KExpr) (hs : whnf_stuck_head_red renv e) (_h2 : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app e a)) (OptionType.none KExpr)) => silent_head_class_red_gen.stuck renv (KExpr.app e a) (whnf_stuck_head_red.app renv e a hs)) f (ihf (red_app_none_head_inv renv f a h) (AndType.left (red_closed_at f Nat.zero) (red_closed_at a Nat.zero) hc) (AndType.left (consts_defined_red renv f) (consts_defined_red renv a) hd)) h) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red renv ty -> silent_head_class_red_gen renv ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red renv b -> silent_head_class_red_gen renv b) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lam ty b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.lam ty b) Nat.zero) (_hd : consts_defined_red renv (KExpr.lam ty b)) => silent_head_class_red_gen.lam renv ty b) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red renv ty -> silent_head_class_red_gen renv ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red renv b -> silent_head_class_red_gen renv b) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.pi ty b) Nat.zero) (_hd : consts_defined_red renv (KExpr.pi ty b)) => silent_head_class_red_gen.stuck renv (KExpr.pi ty b) (whnf_stuck_head_red.pi renv ty b)) (fun (n : Name) (us : ListType Level) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.const n us) Nat.zero) (_hd : consts_defined_red renv (KExpr.const n us)) => silent_head_class_red_gen.neutral renv (KExpr.const n us) (is_neutral_red.const renv n us (reduce_once_red_none_delta_none renv (KExpr.const n us) h))) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red renv ty -> silent_head_class_red_gen renv ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv v) (OptionType.none KExpr) -> red_closed_at v Nat.zero -> consts_defined_red renv v -> silent_head_class_red_gen renv v) (_i3 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red renv b -> silent_head_class_red_gen renv b) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.let_ ty v b) Nat.zero) (_hd : consts_defined_red renv (KExpr.let_ ty v b)) => opt_none_ne_some_t KExpr (instantiate b v) (silent_head_class_red_gen renv (KExpr.let_ ty v b)) (Eq.symm (OptionType KExpr) (OptionType.some KExpr (instantiate b v)) (OptionType.none KExpr) h)) (fun (s : Name) (i : Nat) (sub : KExpr) (ih : Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.none KExpr) -> red_closed_at sub Nat.zero -> consts_defined_red renv sub -> silent_head_class_red_gen renv sub) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.proj s i sub) Nat.zero) (hd : consts_defined_red renv (KExpr.proj s i sub)) => silent_head_class_red_gen.rec renv (fun (e0 : KExpr) (_c : silent_head_class_red_gen renv e0) => silent_head_class_red_gen renv (KExpr.proj s i e0)) (fun (ty : KExpr) (b : KExpr) => silent_head_class_red_gen.stuck renv (KExpr.proj s i (KExpr.lam ty b)) (whnf_stuck_head_red.projw renv s i (KExpr.lam ty b) (is_whnf_red.lam renv ty b))) (fun (e : KExpr) (hn : is_neutral_red renv e) => silent_head_class_red_gen.stuck renv (KExpr.proj s i e) (whnf_stuck_head_red.projw renv s i e (is_whnf_red.neutral renv e hn))) (fun (e : KExpr) (hh : whnf_stuck_head_red renv e) => silent_head_class_red_gen.stuck renv (KExpr.proj s i e) (whnf_stuck_head_red.proj renv s i e hh)) sub (ih (proj_lift_none_inv s i (reduce_once_red renv sub) h) hc hd)) (fun (v : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.lit v) Nat.zero) (_hd : consts_defined_red renv (KExpr.lit v)) => silent_head_class_red_gen.stuck renv (KExpr.lit v) (whnf_stuck_head_red.lit renv v)) e".to_string()),
            is_axiom: false,
            description: "3-WAY HEAD CLASSIFICATION, PARAMETRIC (X17-gen): a closedAt-0, two-env-defined 3-way executable fixpoint over ANY renv has a lambda, neutral (const_delta-silence carried raw, no const_whnf / the_red_env pin), or honestly-stuck head. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "silent_head_class_red_gen".to_string(),
                "silent_head_class_red_gen.lam".to_string(),
                "silent_head_class_red_gen.neutral".to_string(),
                "silent_head_class_red_gen.stuck".to_string(),
                "silent_head_class_red_gen.rec".to_string(),
                "is_neutral_red".to_string(),
                "is_neutral_red.const".to_string(),
                "is_neutral_red.app".to_string(),
                "is_whnf_red.lam".to_string(),
                "is_whnf_red.neutral".to_string(),
                "whnf_stuck_head_red.sort".to_string(),
                "whnf_stuck_head_red.pi".to_string(),
                "whnf_stuck_head_red.app".to_string(),
                "whnf_stuck_head_red.proj".to_string(),
                "whnf_stuck_head_red.projw".to_string(),
                "whnf_stuck_head_red.lit".to_string(),
                "reduce_once_red".to_string(),
                "reduce_once_red_none_delta_none".to_string(),
                "red_app_none_head_inv".to_string(),
                "proj_lift_none_inv".to_string(),
                "red_closed_at".to_string(),
                "consts_defined_red".to_string(),
                "LiftP.rec".to_string(),
                "Le".to_string(),
                "le_zero_eq_zero".to_string(),
                "nat_zero_ne_succ".to_string(),
                "opt_none_ne_some_t".to_string(),
                "instantiate".to_string(),
                "AndType.left".to_string(),
                "KExpr.rec".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_once_red_none_classifies_gen".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr), Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.none KExpr) -> red_closed_at e Nat.zero -> consts_defined_red renv e -> whnf_noredex_class_red renv e".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => Eq (OptionType KExpr) (reduce_once_red renv e0) (OptionType.none KExpr) -> red_closed_at e0 Nat.zero -> consts_defined_red renv e0 -> whnf_noredex_class_red renv e0) (fun (n : Level) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.sort n)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.sort n) Nat.zero) (_hd : consts_defined_red renv (KExpr.sort n)) => whnf_noredex_class_red.done renv (KExpr.sort n) (is_whnf_red.sort renv n)) (fun (i : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.bvar i)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.bvar i) Nat.zero) (_hd : consts_defined_red renv (KExpr.bvar i)) => LiftP.rec (Le (Nat.succ i) Nat.zero) (fun (_l : LiftP (Le (Nat.succ i) Nat.zero)) => whnf_noredex_class_red renv (KExpr.bvar i)) (fun (l : Le (Nat.succ i) Nat.zero) => nat_zero_ne_succ i (whnf_noredex_class_red renv (KExpr.bvar i)) (Eq.symm Nat (Nat.succ i) Nat.zero (le_zero_eq_zero (Nat.succ i) Nat.zero l (Eq.refl Nat Nat.zero)))) hc) (fun (f : KExpr) (a : KExpr) (_ihf : Eq (OptionType KExpr) (reduce_once_red renv f) (OptionType.none KExpr) -> red_closed_at f Nat.zero -> consts_defined_red renv f -> whnf_noredex_class_red renv f) (_iha : Eq (OptionType KExpr) (reduce_once_red renv a) (OptionType.none KExpr) -> red_closed_at a Nat.zero -> consts_defined_red renv a -> whnf_noredex_class_red renv a) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app f a)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.app f a) Nat.zero) (hd : consts_defined_red renv (KExpr.app f a)) => silent_head_class_red_gen.rec renv (fun (e0 : KExpr) (_c : silent_head_class_red_gen renv e0) => Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app e0 a)) (OptionType.none KExpr) -> whnf_noredex_class_red renv (KExpr.app e0 a)) (fun (ty : KExpr) (b : KExpr) (hl : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app (KExpr.lam ty b) a)) (OptionType.none KExpr)) => opt_none_ne_some_t KExpr (instantiate b a) (whnf_noredex_class_red renv (KExpr.app (KExpr.lam ty b) a)) (Eq.symm (OptionType KExpr) (OptionType.some KExpr (instantiate b a)) (OptionType.none KExpr) hl)) (fun (e : KExpr) (hn : is_neutral_red renv e) (_h2 : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app e a)) (OptionType.none KExpr)) => whnf_noredex_class_red.done renv (KExpr.app e a) (is_whnf_red.neutral renv (KExpr.app e a) (is_neutral_red.app renv e a hn))) (fun (e : KExpr) (hs : whnf_stuck_head_red renv e) (_h2 : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.app e a)) (OptionType.none KExpr)) => whnf_noredex_class_red.stuck renv e a hs) f (silent_head_class_of_none_red_gen renv f (red_app_none_head_inv renv f a h) (AndType.left (red_closed_at f Nat.zero) (red_closed_at a Nat.zero) hc) (AndType.left (consts_defined_red renv f) (consts_defined_red renv a) hd)) h) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red renv ty -> whnf_noredex_class_red renv ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red renv b -> whnf_noredex_class_red renv b) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lam ty b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.lam ty b) Nat.zero) (_hd : consts_defined_red renv (KExpr.lam ty b)) => whnf_noredex_class_red.done renv (KExpr.lam ty b) (is_whnf_red.lam renv ty b)) (fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red renv ty -> whnf_noredex_class_red renv ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red renv b -> whnf_noredex_class_red renv b) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.pi ty b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.pi ty b) Nat.zero) (_hd : consts_defined_red renv (KExpr.pi ty b)) => whnf_noredex_class_red.done renv (KExpr.pi ty b) (is_whnf_red.pi renv ty b)) (fun (n : Name) (us : ListType Level) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.const n us)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.const n us) Nat.zero) (_hd : consts_defined_red renv (KExpr.const n us)) => whnf_noredex_class_red.done renv (KExpr.const n us) (is_whnf_red.neutral renv (KExpr.const n us) (is_neutral_red.const renv n us (reduce_once_red_none_delta_none renv (KExpr.const n us) h)))) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once_red renv ty) (OptionType.none KExpr) -> red_closed_at ty Nat.zero -> consts_defined_red renv ty -> whnf_noredex_class_red renv ty) (_i2 : Eq (OptionType KExpr) (reduce_once_red renv v) (OptionType.none KExpr) -> red_closed_at v Nat.zero -> consts_defined_red renv v -> whnf_noredex_class_red renv v) (_i3 : Eq (OptionType KExpr) (reduce_once_red renv b) (OptionType.none KExpr) -> red_closed_at b Nat.zero -> consts_defined_red renv b -> whnf_noredex_class_red renv b) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.let_ ty v b)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.let_ ty v b) Nat.zero) (_hd : consts_defined_red renv (KExpr.let_ ty v b)) => opt_none_ne_some_t KExpr (instantiate b v) (whnf_noredex_class_red renv (KExpr.let_ ty v b)) (Eq.symm (OptionType KExpr) (OptionType.some KExpr (instantiate b v)) (OptionType.none KExpr) h)) (fun (s : Name) (i : Nat) (sub : KExpr) (ih : Eq (OptionType KExpr) (reduce_once_red renv sub) (OptionType.none KExpr) -> red_closed_at sub Nat.zero -> consts_defined_red renv sub -> whnf_noredex_class_red renv sub) (h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.proj s i sub)) (OptionType.none KExpr)) (hc : red_closed_at (KExpr.proj s i sub) Nat.zero) (hd : consts_defined_red renv (KExpr.proj s i sub)) => noredex_proj_class_red renv s i sub (ih (proj_lift_none_inv s i (reduce_once_red renv sub) h) hc hd)) (fun (v : Nat) (_h : Eq (OptionType KExpr) (reduce_once_red renv (KExpr.lit v)) (OptionType.none KExpr)) (_hc : red_closed_at (KExpr.lit v) Nat.zero) (_hd : consts_defined_red renv (KExpr.lit v)) => whnf_noredex_class_red.done renv (KExpr.lit v) (is_whnf_red.lit renv v)) e".to_string()),
            is_axiom: false,
            description: "THE 3-WAY FIXPOINT CLASSIFICATION, PARAMETRIC (X17-gen): a closedAt-0, two-env-defined 3-way executable fixpoint over ANY renv is a landed is_whnf_red value (incl. delta/iota-silent neutral recursor spines) or an honest stuck app/proj residual. No the_red_env pin. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_noredex_class_red".to_string(),
                "whnf_noredex_class_red.done".to_string(),
                "whnf_noredex_class_red.stuck".to_string(),
                "is_whnf_red.sort".to_string(),
                "is_whnf_red.lam".to_string(),
                "is_whnf_red.pi".to_string(),
                "is_whnf_red.lit".to_string(),
                "is_whnf_red.neutral".to_string(),
                "is_neutral_red.const".to_string(),
                "is_neutral_red.app".to_string(),
                "whnf_stuck_head_red".to_string(),
                "silent_head_class_red_gen".to_string(),
                "silent_head_class_red_gen.rec".to_string(),
                "silent_head_class_of_none_red_gen".to_string(),
                "noredex_proj_class_red".to_string(),
                "reduce_once_red".to_string(),
                "reduce_once_red_none_delta_none".to_string(),
                "red_app_none_head_inv".to_string(),
                "proj_lift_none_inv".to_string(),
                "red_closed_at".to_string(),
                "consts_defined_red".to_string(),
                "LiftP.rec".to_string(),
                "Le".to_string(),
                "le_zero_eq_zero".to_string(),
                "nat_zero_ne_succ".to_string(),
                "opt_none_ne_some_t".to_string(),
                "instantiate".to_string(),
                "AndType.left".to_string(),
                "KExpr.rec".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_fuel_red_classifies_gen".to_string(),
            type_src: "forall (renv : RedEnv), red_env_good renv -> forall (fuel : Nat) (e : KExpr) (r : KExpr), red_closed_at e Nat.zero -> consts_defined_red renv e -> Eq (OptionType KExpr) (whnf_fuel_red renv fuel e) (OptionType.some KExpr r) -> whnf_noredex_class_red renv r".to_string(),
            value_src: Some("fun (renv : RedEnv) (hEnv : red_env_good renv) (fuel : Nat) => Nat.rec (fun (k : Nat) => forall (e : KExpr) (r : KExpr), red_closed_at e Nat.zero -> consts_defined_red renv e -> Eq (OptionType KExpr) (whnf_fuel_red renv k e) (OptionType.some KExpr r) -> whnf_noredex_class_red renv r) (fun (e : KExpr) (r : KExpr) (_hc : red_closed_at e Nat.zero) (_hd : consts_defined_red renv e) (h : Eq (OptionType KExpr) (whnf_fuel_red renv Nat.zero e) (OptionType.some KExpr r)) => opt_none_ne_some_t KExpr r (whnf_noredex_class_red renv r) h) (fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), red_closed_at e0 Nat.zero -> consts_defined_red renv e0 -> Eq (OptionType KExpr) (whnf_fuel_red renv k e0) (OptionType.some KExpr r0) -> whnf_noredex_class_red renv r0) (e : KExpr) (r : KExpr) (hc : red_closed_at e Nat.zero) (hd : consts_defined_red renv e) (h : Eq (OptionType KExpr) (whnf_fuel_red renv (Nat.succ k) e) (OptionType.some KExpr r)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red renv e) o -> Eq (OptionType KExpr) (loop_dispatch o e (fun (e2 : KExpr) => whnf_fuel_red renv k e2)) (OptionType.some KExpr r) -> whnf_noredex_class_red renv r) (fun (heq : Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e (fun (e2 : KExpr) => whnf_fuel_red renv k e2)) (OptionType.some KExpr r)) => Eq.rec KExpr e (fun (x : KExpr) (_hx : Eq KExpr e x) => whnf_noredex_class_red renv x) (reduce_once_red_none_classifies_gen renv e heq hc hd) r (option_some_inj KExpr e r h2)) (fun (e2 : KExpr) (heq : Eq (OptionType KExpr) (reduce_once_red renv e) (OptionType.some KExpr e2)) (h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.some KExpr e2) e (fun (e3 : KExpr) => whnf_fuel_red renv k e3)) (OptionType.some KExpr r)) => ih e2 r (reduce_once_red_preserves_closed renv hEnv e hc e2 heq) (reduce_once_red_preserves_defined renv hEnv e hd e2 heq) h2) (reduce_once_red renv e) (Eq.refl (OptionType KExpr) (reduce_once_red renv e)) h) fuel".to_string()),
            is_axiom: false,
            description: "THE 3-WAY EXECUTABLE-LOOP CAPSTONE, PARAMETRIC (X17-gen): over ANY good renv, every successful fuel-bounded 3-way loop result on a closedAt-0, two-env-defined term CLASSIFIES (whnf_noredex_class_red) — reached by genuine beta/zeta+delta+iota steps, a fixpoint, and CLASSIFIED. The env-generalized capstone: the 3-way loop self-verifies over an arbitrary reduction environment, not just the_red_env. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel_red".to_string(),
                "loop_dispatch".to_string(),
                "reduce_once_red".to_string(),
                "reduce_once_red_none_classifies_gen".to_string(),
                "reduce_once_red_preserves_closed".to_string(),
                "reduce_once_red_preserves_defined".to_string(),
                "red_env_good".to_string(),
                "red_closed_at".to_string(),
                "consts_defined_red".to_string(),
                "whnf_noredex_class_red".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "Nat.rec".to_string(),
                "OptionType.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_fuel_red_le".to_string(),
            type_src: "forall (renv : RedEnv) (fuel1 : Nat) (fuel2 : Nat), Le fuel1 fuel2 -> forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red renv fuel1 e) (OptionType.some KExpr r) -> Eq (OptionType KExpr) (whnf_fuel_red renv fuel2 e) (OptionType.some KExpr r)".to_string(),
            value_src: Some("fun (renv : RedEnv) (fuel1 : Nat) (fuel2 : Nat) (hle : Le fuel1 fuel2) => Le.rec fuel1 (fun (j : Nat) (_hj : Le fuel1 j) => forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red renv fuel1 e) (OptionType.some KExpr r) -> Eq (OptionType KExpr) (whnf_fuel_red renv j e) (OptionType.some KExpr r)) (fun (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel_red renv fuel1 e) (OptionType.some KExpr r)) => h) (fun (m : Nat) (_hm : Le fuel1 m) (ihm : forall (e : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red renv fuel1 e) (OptionType.some KExpr r) -> Eq (OptionType KExpr) (whnf_fuel_red renv m e) (OptionType.some KExpr r)) (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel_red renv fuel1 e) (OptionType.some KExpr r)) => whnf_fuel_red_monotone renv m e r (ihm e r h)) fuel2 hle".to_string()),
            is_axiom: false,
            description: "FUEL MONOTONICITY (Le form, X17-uniqueness): whnf_fuel_red is monotone in the fuel bound over ANY renv — a successful result survives raising the fuel to any Le-greater value, by Le.rec (subsingleton elim into the Prop goal) with the single-step whnf_fuel_red_monotone at each step. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel_red".to_string(),
                "whnf_fuel_red_monotone".to_string(),
                "Le".to_string(),
                "Le.rec".to_string(),
                "Eq".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_fuel_red_unique".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr) (fuel1 : Nat) (fuel2 : Nat) (r1 : KExpr) (r2 : KExpr), Eq (OptionType KExpr) (whnf_fuel_red renv fuel1 e) (OptionType.some KExpr r1) -> Eq (OptionType KExpr) (whnf_fuel_red renv fuel2 e) (OptionType.some KExpr r2) -> Eq KExpr r1 r2".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) (fuel1 : Nat) (fuel2 : Nat) (r1 : KExpr) (r2 : KExpr) (h1 : Eq (OptionType KExpr) (whnf_fuel_red renv fuel1 e) (OptionType.some KExpr r1)) (h2 : Eq (OptionType KExpr) (whnf_fuel_red renv fuel2 e) (OptionType.some KExpr r2)) => option_some_inj KExpr r1 r2 (Eq.trans (OptionType KExpr) (OptionType.some KExpr r1) (whnf_fuel_red renv (Nat.add fuel1 fuel2) e) (OptionType.some KExpr r2) (Eq.symm (OptionType KExpr) (whnf_fuel_red renv (Nat.add fuel1 fuel2) e) (OptionType.some KExpr r1) (whnf_fuel_red_le renv fuel1 (Nat.add fuel1 fuel2) (le_add_self_left fuel1 fuel2) e r1 h1)) (whnf_fuel_red_le renv fuel2 (Nat.add fuel1 fuel2) (le_add_self_right fuel1 fuel2) e r2 h2)))".to_string()),
            is_axiom: false,
            description: "NORMAL-FORM UNIQUENESS for the 3-way executable loop (X17-uniqueness): two successful whnf_fuel_red runs from the same term over the same renv — with ANY two fuel bounds — yield the SAME weak-head normal form. The executable 3-way reduction (β/ζ + head-δ + whole-spine-ι), when it terminates, has a UNIQUE result: raise both runs to the common bound fuel1+fuel2 by whnf_fuel_red_le (le_add_self_left/right), then some-injectivity. Together with whnf_fuel_red_reaches_sound (reached by genuine steps) and whnf_fuel_red_classifies_gen (done-or-stuck), this pins the executable normal form completely. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel_red".to_string(),
                "whnf_fuel_red_le".to_string(),
                "le_add_self_left".to_string(),
                "le_add_self_right".to_string(),
                "option_some_inj".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_inductive(
            r"inductive whnf_red_step_star (renv : RedEnv) : KExpr -> KExpr -> Type
| refl : forall (e : KExpr), whnf_red_step_star renv e e
| step : forall (e : KExpr) (e2 : KExpr) (e3 : KExpr), whnf_red_step renv e e2 -> whnf_red_step_star renv e2 e3 -> whnf_red_step_star renv e e3",
            "The reflexive-transitive closure of the 3-way weak-head step (X17-confluence): whnf_red_step_star renv e e' witnesses a multi-step beta/zeta + head-delta + head-iota reduction over renv.",
        )?;

        self.add_inductive(
            r"inductive whnf_red_join_witness (renv : RedEnv) : KExpr -> KExpr -> Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), whnf_red_step_star renv e1 e3 -> whnf_red_step_star renv e2 e3 -> whnf_red_join_witness renv e1 e2",
            "A common-reduct join for the 3-way weak-head step (X17-confluence): whnf_red_join_witness renv e1 e2 holds when e1 and e2 both whnf_red_step_star-reduce to a common e3.",
        )?;

        self.add_definition(SpecDefinition {
            name: "beta_bd_star_to_whnf_red_star".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr) (e2 : KExpr), beta_reduces_bd_star e e2 -> whnf_red_step_star renv e e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) (e2 : KExpr) (h : beta_reduces_bd_star e e2) => beta_reduces_bd_star.rec (fun (a : KExpr) (b : KExpr) (_hab : beta_reduces_bd_star a b) => whnf_red_step_star renv a b) (fun (x : KExpr) => whnf_red_step_star.refl renv x) (fun (x : KExpr) (x2 : KExpr) (x3 : KExpr) (hstep : beta_reduces_bd x x2) (_rest : beta_reduces_bd_star x2 x3) (ih : whnf_red_step_star renv x2 x3) => whnf_red_step_star.step renv x x2 x3 (whnf_red_step.beta renv x x2 hstep) ih) e e2 h".to_string()),
            is_axiom: false,
            description: "BETA/ZETA EMBEDDING (X17-confluence): every beta_reduces_bd_star reduction embeds into the 3-way whnf_red_step_star (each congruence step injects via whnf_red_step.beta). So the full 13-arm beta/zeta congruence closure is a sub-reduction of the 3-way weak-head step over ANY renv. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_red_step_star".to_string(),
                "whnf_red_step_star.refl".to_string(),
                "whnf_red_step_star.step".to_string(),
                "whnf_red_step.beta".to_string(),
                "beta_reduces_bd_star".to_string(),
                "beta_reduces_bd_star.rec".to_string(),
                "beta_reduces_bd".to_string(),
                "KExpr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_red_beta_confluent".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), beta_reduces_bd_star e e1 -> beta_reduces_bd_star e e2 -> whnf_red_join_witness renv e1 e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) (h1 : beta_reduces_bd_star e e1) (h2 : beta_reduces_bd_star e e2) => beta_bd_join_witness.rec e1 e2 (fun (_t : beta_bd_join_witness e1 e2) => whnf_red_join_witness renv e1 e2) (fun (x3 : KExpr) (hj1 : beta_reduces_bd_star e1 x3) (hj2 : beta_reduces_bd_star e2 x3) => whnf_red_join_witness.intro renv e1 e2 x3 (beta_bd_star_to_whnf_red_star renv e1 x3 hj1) (beta_bd_star_to_whnf_red_star renv e2 x3 hj2)) (beta_bd_confluent e e1 e2 h1 h2)".to_string()),
            is_axiom: false,
            description: "BETA/ZETA-CORE CONFLUENCE of the 3-way weak-head step (X17-confluence): any two beta_reduces_bd_star reductions from a common term join inside whnf_red_step_star over ANY renv — the proven beta_bd_confluent (Church-Rosser for the full 13-arm beta/zeta congruence) lifted through the beta/zeta embedding. This is the self-contained confluence rung for whnf_red_step's beta/zeta core; the residual delta/iota-commutation (a step and a head-delta/iota fire joining) is the CR-scale piece that bridges to the par_reduces parallel machinery. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_red_join_witness".to_string(),
                "whnf_red_join_witness.intro".to_string(),
                "beta_bd_star_to_whnf_red_star".to_string(),
                "beta_bd_confluent".to_string(),
                "beta_bd_join_witness".to_string(),
                "beta_bd_join_witness.rec".to_string(),
                "beta_reduces_bd_star".to_string(),
                "KExpr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "beta_reduces_bd_to_par_cd".to_string(),
            type_src: "forall (env : RedEnv) (e : KExpr) (e2 : KExpr), beta_reduces_bd e e2 -> par_reduces_cd env e e2".to_string(),
            value_src: Some("fun (env : RedEnv) (e : KExpr) (e2 : KExpr) (h : beta_reduces_bd e e2) => beta_reduces_bd.rec (fun (a : KExpr) (b : KExpr) (_h : beta_reduces_bd a b) => par_reduces_cd env a b) (fun (A : KExpr) (body : KExpr) (arg : KExpr) => par_reduces_cd.beta env A A body body arg arg (par_reduces_cd.refl env A) (par_reduces_cd.refl env body) (par_reduces_cd.refl env arg)) (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (_h : beta_reduces_bd f f2) (ih : par_reduces_cd env f f2) => par_reduces_cd.app env f f2 a a ih (par_reduces_cd.refl env a)) (fun (f : KExpr) (a : KExpr) (a2 : KExpr) (_h : beta_reduces_bd a a2) (ih : par_reduces_cd env a a2) => par_reduces_cd.app env f f a a2 (par_reduces_cd.refl env f) ih) (fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_h : beta_reduces_bd ty ty2) (ih : par_reduces_cd env ty ty2) => par_reduces_cd.lam env ty ty2 body body ih (par_reduces_cd.refl env body)) (fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_h : beta_reduces_bd body body2) (ih : par_reduces_cd env body body2) => par_reduces_cd.lam env ty ty body body2 (par_reduces_cd.refl env ty) ih) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_h : beta_reduces_bd dom dom2) (ih : par_reduces_cd env dom dom2) => par_reduces_cd.pi env dom dom2 body body ih (par_reduces_cd.refl env body)) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_h : beta_reduces_bd body body2) (ih : par_reduces_cd env body body2) => par_reduces_cd.pi env dom dom body body2 (par_reduces_cd.refl env dom) ih) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_h : beta_reduces_bd dom dom2) (ih : par_reduces_cd env dom dom2) => par_reduces_cd.forall_ env dom dom2 body body ih (par_reduces_cd.refl env body)) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_h : beta_reduces_bd body body2) (ih : par_reduces_cd env body body2) => par_reduces_cd.forall_ env dom dom body body2 (par_reduces_cd.refl env dom) ih) (fun (ty : KExpr) (val : KExpr) (body : KExpr) => par_reduces_cd.let_ env ty ty val val body body (par_reduces_cd.refl env ty) (par_reduces_cd.refl env val) (par_reduces_cd.refl env body)) (fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_h : beta_reduces_bd ty ty2) (ih : par_reduces_cd env ty ty2) => par_reduces_cd.let_cong env ty ty2 val val body body ih (par_reduces_cd.refl env val) (par_reduces_cd.refl env body)) (fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_h : beta_reduces_bd val val2) (ih : par_reduces_cd env val val2) => par_reduces_cd.let_cong env ty ty val val2 body body (par_reduces_cd.refl env ty) ih (par_reduces_cd.refl env body)) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_h : beta_reduces_bd body body2) (ih : par_reduces_cd env body body2) => par_reduces_cd.let_cong env ty ty val val body body2 (par_reduces_cd.refl env ty) (par_reduces_cd.refl env val) ih) (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (_h : beta_reduces_bd sub sub2) (ih : par_reduces_cd env sub sub2) => par_reduces_cd.proj env sn i sub sub2 ih) e e2 h".to_string()),
            is_axiom: false,
            description: "CR-BRIDGE R0: every iota-free beta_reduces_bd single step is a par_reduces_cd step over the same RedEnv — the 14 congruence arms map to par_reduces_cd's beta/let_/app/lam/pi/forall_/let_cong/proj with refl in the unreduced slots. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd.rec".to_string(),
                "par_reduces_cd".to_string(),
                "par_reduces_cd.refl".to_string(),
                "par_reduces_cd.beta".to_string(),
                "par_reduces_cd.app".to_string(),
                "par_reduces_cd.lam".to_string(),
                "par_reduces_cd.pi".to_string(),
                "par_reduces_cd.forall_".to_string(),
                "par_reduces_cd.let_".to_string(),
                "par_reduces_cd.let_cong".to_string(),
                "par_reduces_cd.proj".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_red_step_to_par_cd".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr) (e2 : KExpr), whnf_red_step renv e e2 -> par_reduces_cd renv e e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) (e2 : KExpr) (h : whnf_red_step renv e e2) => whnf_red_step.rec renv (fun (x : KExpr) (x2 : KExpr) (_h : whnf_red_step renv x x2) => par_reduces_cd renv x x2) (fun (x : KExpr) (x2 : KExpr) (hbd : beta_reduces_bd x x2) => beta_reduces_bd_to_par_cd renv x x2 hbd) (fun (x : KExpr) (x2 : KExpr) (hd : Eq (OptionType KExpr) (delta_reduct (red_def renv) x) (OptionType.some KExpr x2)) => par_reduces_cd.delta renv x x2 hd) (fun (x : KExpr) (x2 : KExpr) (hi : Eq (OptionType KExpr) (iota_reduct (red_rec renv) x) (OptionType.some KExpr x2)) => par_reduces_cd.iota renv x x2 hi) (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (_hstep : whnf_red_step renv f f2) (ih : par_reduces_cd renv f f2) => par_reduces_cd.app renv f f2 a a ih (par_reduces_cd.refl renv a)) (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (_hstep : whnf_red_step renv sub sub2) (ih : par_reduces_cd renv sub sub2) => par_reduces_cd.proj renv sn i sub sub2 ih) e e2 h".to_string()),
            is_axiom: false,
            description: "CR-BRIDGE R1: every 3-way weak-head step embeds into the atomic parallel reduction par_reduces_cd over the SAME RedEnv — beta via R0, the head-delta/head-iota premises feed par_reduces_cd.delta/.iota VERBATIM (delta_step/iota_step are definitionally the delta_reduct/iota_reduct = some equations), app_left/proj through the par_reduces_cd congruences. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_red_step".to_string(),
                "whnf_red_step.rec".to_string(),
                "beta_reduces_bd_to_par_cd".to_string(),
                "par_reduces_cd".to_string(),
                "par_reduces_cd.delta".to_string(),
                "par_reduces_cd.iota".to_string(),
                "par_reduces_cd.app".to_string(),
                "par_reduces_cd.proj".to_string(),
                "par_reduces_cd.refl".to_string(),
                "delta_reduct".to_string(),
                "iota_reduct".to_string(),
                "red_def".to_string(),
                "red_rec".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_red_step_star_to_par_cd_star".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr) (e2 : KExpr), whnf_red_step_star renv e e2 -> par_reduces_cd_star renv e e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) (e2 : KExpr) (h : whnf_red_step_star renv e e2) => whnf_red_step_star.rec renv (fun (x : KExpr) (x2 : KExpr) (_h : whnf_red_step_star renv x x2) => par_reduces_cd_star renv x x2) (fun (x : KExpr) => par_reduces_cd_star.refl renv x) (fun (x : KExpr) (x2 : KExpr) (x3 : KExpr) (hstep : whnf_red_step renv x x2) (_htail : whnf_red_step_star renv x2 x3) (ih : par_reduces_cd_star renv x2 x3) => par_reduces_cd_star.step renv x x2 x3 (whnf_red_step_to_par_cd renv x x2 hstep) ih) e e2 h".to_string()),
            is_axiom: false,
            description: "CR-BRIDGE R2: the 3-way weak-head reduction sequence embeds into the par_reduces_cd_star closure (step-by-step via R1). So whnf_red_step_star is a sub-reduction of the full atomic parallel reduction. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_red_step_star".to_string(),
                "whnf_red_step_star.rec".to_string(),
                "whnf_red_step_to_par_cd".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star.step".to_string(),
                "whnf_red_step".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_red_step_star_confluent_via_cd".to_string(),
            type_src: "forall (renv : RedEnv) (i1 : RecEnvReductNotRedex (red_rec renv)) (i2 : RecEnvCtorNoRecMeta (red_rec renv)) (i3 : RecEnvClosed (red_rec renv)) (i4 : RecEnvLiftClosed (red_rec renv)) (i5 : DefEnvClosed (red_def renv)) (i6 : DefEnvLiftClosed (red_def renv)) (i7 : RecEnvDefEnvDisjoint renv) (i8 : RecEnvCtorNoDefVal renv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), whnf_red_step_star renv e e1 -> whnf_red_step_star renv e e2 -> par_strips_witness_cd_star renv e1 e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (i1 : RecEnvReductNotRedex (red_rec renv)) (i2 : RecEnvCtorNoRecMeta (red_rec renv)) (i3 : RecEnvClosed (red_rec renv)) (i4 : RecEnvLiftClosed (red_rec renv)) (i5 : DefEnvClosed (red_def renv)) (i6 : DefEnvLiftClosed (red_def renv)) (i7 : RecEnvDefEnvDisjoint renv) (i8 : RecEnvCtorNoDefVal renv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) (h1 : whnf_red_step_star renv e e1) (h2 : whnf_red_step_star renv e e2) => par_reduces_cd_star_diamond renv i1 i2 i3 i4 i5 i6 i7 i8 e e1 e2 (whnf_red_step_star_to_par_cd_star renv e e1 h1) (whnf_red_step_star_to_par_cd_star renv e e2 h2)".to_string()),
            is_axiom: false,
            description: "CR-BRIDGE R3 — RELATIONAL CONFLUENCE of whnf_red_step (the full 3-way step) via the proven par_reduces_cd diamond: any two whnf_red_step_star reductions from a common term JOIN in par_reduces_cd_star (a par_strips_witness_cd_star cospan), over any RedEnv satisfying the 8 standard well-formedness interfaces. This supplies the delta/iota-commutation the β/ζ-core rung (whnf_red_beta_confluent) left open — the join lands in the fuller atomic parallel reduction (whnf_red_step's δ/ι are weak-head, so the cospan does NOT back-project to whnf_red_step_star under binders; that is the honest scope). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_red_step_star".to_string(),
                "whnf_red_step_star_to_par_cd_star".to_string(),
                "par_reduces_cd_star_diamond".to_string(),
                "par_strips_witness_cd_star".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "DefEnvClosed".to_string(),
                "DefEnvLiftClosed".to_string(),
                "RecEnvDefEnvDisjoint".to_string(),
                "RecEnvCtorNoDefVal".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_red_step_star_snoc".to_string(),
            type_src: "forall (renv : RedEnv) (a : KExpr) (b : KExpr) (c : KExpr), whnf_red_step_star renv a b -> whnf_red_step renv b c -> whnf_red_step_star renv a c".to_string(),
            value_src: Some("fun (renv : RedEnv) (a : KExpr) (b : KExpr) (c : KExpr) (hab : whnf_red_step_star renv a b) (hbc : whnf_red_step renv b c) => whnf_red_step_star.rec renv (fun (x : KExpr) (y : KExpr) (_h : whnf_red_step_star renv x y) => forall (z : KExpr), whnf_red_step renv y z -> whnf_red_step_star renv x z) (fun (e : KExpr) (z : KExpr) (hz : whnf_red_step renv e z) => whnf_red_step_star.step renv e z z hz (whnf_red_step_star.refl renv z)) (fun (e : KExpr) (e2 : KExpr) (e3 : KExpr) (hstep : whnf_red_step renv e e2) (_rest : whnf_red_step_star renv e2 e3) (ih : forall (z : KExpr), whnf_red_step renv e3 z -> whnf_red_step_star renv e2 z) (z : KExpr) (hz : whnf_red_step renv e3 z) => whnf_red_step_star.step renv e e2 z hstep (ih z hz)) a b hab c hbc".to_string()),
            is_axiom: false,
            description: "Append a whnf_red_step on the RIGHT of the cons-style closure (X17-confluence glue): the reflexive-transitive closure is closed under a trailing step. By whnf_red_step_star.rec threading the trailing step through the motive. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_red_step_star".to_string(),
                "whnf_red_step_star.rec".to_string(),
                "whnf_red_step_star.refl".to_string(),
                "whnf_red_step_star.step".to_string(),
                "whnf_red_step".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "red_step_star_to_whnf_red_step_star".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr) (r : KExpr), red_step_star renv e r -> whnf_red_step_star renv e r".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) (r : KExpr) (h : red_step_star renv e r) => red_step_star.rec renv e (fun (b : KExpr) (_h : red_step_star renv e b) => whnf_red_step_star renv e b) (whnf_red_step_star.refl renv e) (fun (b : KExpr) (c : KExpr) (_h1 : red_step_star renv e b) (h2 : whnf_red_step renv b c) (ih : whnf_red_step_star renv e b) => whnf_red_step_star_snoc renv e b c ih h2) r h".to_string()),
            is_axiom: false,
            description: "The X17b snoc-style red_step_star (the loop's soundness closure) coincides with the X17-confluence cons-style whnf_red_step_star: each tail step appends via whnf_red_step_star_snoc. Lets the executable loop's reach feed the confluence bridge. (red_step_star's first index is uniform, so its recursor is parameter-promoted.) DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_step_star".to_string(),
                "red_step_star.rec".to_string(),
                "red_step_star.refl".to_string(),
                "whnf_red_step_star".to_string(),
                "whnf_red_step_star.refl".to_string(),
                "whnf_red_step_star_snoc".to_string(),
                "whnf_red_step".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_fuel_red_join".to_string(),
            type_src: "forall (renv : RedEnv) (i1 : RecEnvReductNotRedex (red_rec renv)) (i2 : RecEnvCtorNoRecMeta (red_rec renv)) (i3 : RecEnvClosed (red_rec renv)) (i4 : RecEnvLiftClosed (red_rec renv)) (i5 : DefEnvClosed (red_def renv)) (i6 : DefEnvLiftClosed (red_def renv)) (i7 : RecEnvDefEnvDisjoint renv) (i8 : RecEnvCtorNoDefVal renv) (fuel : Nat) (e : KExpr) (r : KExpr) (e2 : KExpr), Eq (OptionType KExpr) (whnf_fuel_red renv fuel e) (OptionType.some KExpr r) -> whnf_red_step_star renv e e2 -> par_strips_witness_cd_star renv r e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (i1 : RecEnvReductNotRedex (red_rec renv)) (i2 : RecEnvCtorNoRecMeta (red_rec renv)) (i3 : RecEnvClosed (red_rec renv)) (i4 : RecEnvLiftClosed (red_rec renv)) (i5 : DefEnvClosed (red_def renv)) (i6 : DefEnvLiftClosed (red_def renv)) (i7 : RecEnvDefEnvDisjoint renv) (i8 : RecEnvCtorNoDefVal renv) (fuel : Nat) (e : KExpr) (r : KExpr) (e2 : KExpr) (hfuel : Eq (OptionType KExpr) (whnf_fuel_red renv fuel e) (OptionType.some KExpr r)) (h2 : whnf_red_step_star renv e e2) => whnf_red_step_star_confluent_via_cd renv i1 i2 i3 i4 i5 i6 i7 i8 e r e2 (red_step_star_to_whnf_red_step_star renv e r (whnf_fuel_red_reaches_sound renv fuel e r hfuel)) h2".to_string()),
            is_axiom: false,
            description: "EXECUTABLE-LOOP / CONFLUENCE CAPSTONE: the executable 3-way loop's result r JOINS (in par_reduces_cd_star) with EVERY whnf_red_step reduct e2 of the same source — the loop result is a confluence join point. Combines whnf_fuel_red_reaches_sound (r reached by genuine steps) with the full relational confluence R3. So the executable normal form is not just unique among fuel runs (whnf_fuel_red_unique) but confluent with the entire relational reduction. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel_red".to_string(),
                "whnf_fuel_red_reaches_sound".to_string(),
                "red_step_star_to_whnf_red_step_star".to_string(),
                "whnf_red_step_star_confluent_via_cd".to_string(),
                "whnf_red_step_star".to_string(),
                "par_strips_witness_cd_star".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "DefEnvClosed".to_string(),
                "DefEnvLiftClosed".to_string(),
                "RecEnvDefEnvDisjoint".to_string(),
                "RecEnvCtorNoDefVal".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_red_step_to_par_cd_star".to_string(),
            type_src: "forall (renv : RedEnv) (e : KExpr) (e2 : KExpr), whnf_red_step renv e e2 -> par_reduces_cd_star renv e e2".to_string(),
            value_src: Some("fun (renv : RedEnv) (e : KExpr) (e2 : KExpr) (h : whnf_red_step renv e e2) => par_subsumes_par_cd_star renv e e2 (whnf_red_step_to_par_cd renv e e2 h)".to_string()),
            is_axiom: false,
            description: "A single 3-way weak-head step is a one-element par_reduces_cd_star reduction (via the R1 embedding + par_subsumes_par_cd_star). DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_red_step".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_subsumes_par_cd_star".to_string(),
                "whnf_red_step_to_par_cd".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_inductive(
            r"inductive whnf_red_conv (renv : RedEnv) : KExpr -> KExpr -> Type
| refl : forall (e : KExpr), whnf_red_conv renv e e
| fwd : forall (a : KExpr) (b : KExpr) (c : KExpr), whnf_red_step renv a b -> whnf_red_conv renv b c -> whnf_red_conv renv a c
| bwd : forall (a : KExpr) (b : KExpr) (c : KExpr), whnf_red_step renv b a -> whnf_red_conv renv b c -> whnf_red_conv renv a c",
            "whnf_red_conv renv a b: definitional CONVERSION generated by the 3-way weak-head step — the reflexive-symmetric-transitive closure of whnf_red_step (fwd prepends a forward step, bwd prepends a reversed step). The relation whose Church-Rosser property underpins decidable definitional equality.",
        )?;

        self.add_definition(SpecDefinition {
            name: "whnf_red_conv_join".to_string(),
            type_src: "forall (renv : RedEnv) (i1 : RecEnvReductNotRedex (red_rec renv)) (i2 : RecEnvCtorNoRecMeta (red_rec renv)) (i3 : RecEnvClosed (red_rec renv)) (i4 : RecEnvLiftClosed (red_rec renv)) (i5 : DefEnvClosed (red_def renv)) (i6 : DefEnvLiftClosed (red_def renv)) (i7 : RecEnvDefEnvDisjoint renv) (i8 : RecEnvCtorNoDefVal renv) (a : KExpr) (b : KExpr), whnf_red_conv renv a b -> par_strips_witness_cd_star renv a b".to_string(),
            value_src: Some("fun (renv : RedEnv) (i1 : RecEnvReductNotRedex (red_rec renv)) (i2 : RecEnvCtorNoRecMeta (red_rec renv)) (i3 : RecEnvClosed (red_rec renv)) (i4 : RecEnvLiftClosed (red_rec renv)) (i5 : DefEnvClosed (red_def renv)) (i6 : DefEnvLiftClosed (red_def renv)) (i7 : RecEnvDefEnvDisjoint renv) (i8 : RecEnvCtorNoDefVal renv) (a : KExpr) (b : KExpr) (h : whnf_red_conv renv a b) => whnf_red_conv.rec renv (fun (x : KExpr) (y : KExpr) (_h : whnf_red_conv renv x y) => par_strips_witness_cd_star renv x y) (fun (e : KExpr) => par_strips_witness_cd_star.intro renv e e e (par_reduces_cd_star.refl renv e) (par_reduces_cd_star.refl renv e)) (fun (a2 : KExpr) (b2 : KExpr) (c2 : KExpr) (hstep : whnf_red_step renv a2 b2) (_hconv : whnf_red_conv renv b2 c2) (ih : par_strips_witness_cd_star renv b2 c2) => par_strips_witness_cd_star.rec renv b2 c2 (fun (_t : par_strips_witness_cd_star renv b2 c2) => par_strips_witness_cd_star renv a2 c2) (fun (d : KExpr) (l1 : par_reduces_cd_star renv b2 d) (l2 : par_reduces_cd_star renv c2 d) => par_strips_witness_cd_star.intro renv a2 c2 d (par_reduces_cd_star_trans renv a2 b2 d (whnf_red_step_to_par_cd_star renv a2 b2 hstep) l1) l2) ih) (fun (a2 : KExpr) (b2 : KExpr) (c2 : KExpr) (hstep : whnf_red_step renv b2 a2) (_hconv : whnf_red_conv renv b2 c2) (ih : par_strips_witness_cd_star renv b2 c2) => par_strips_witness_cd_star.rec renv b2 c2 (fun (_t : par_strips_witness_cd_star renv b2 c2) => par_strips_witness_cd_star renv a2 c2) (fun (d : KExpr) (l1 : par_reduces_cd_star renv b2 d) (l2 : par_reduces_cd_star renv c2 d) => par_strips_witness_cd_star.rec renv a2 d (fun (_t2 : par_strips_witness_cd_star renv a2 d) => par_strips_witness_cd_star renv a2 c2) (fun (e : KExpr) (m1 : par_reduces_cd_star renv a2 e) (m2 : par_reduces_cd_star renv d e) => par_strips_witness_cd_star.intro renv a2 c2 e m1 (par_reduces_cd_star_trans renv c2 d e l2 m2)) (par_reduces_cd_star_diamond renv i1 i2 i3 i4 i5 i6 i7 i8 b2 a2 d (whnf_red_step_to_par_cd_star renv b2 a2 hstep) l1)) ih) a b h".to_string()),
            is_axiom: false,
            description: "CONVERSION CHURCH-ROSSER for whnf_red_step (in-kernel; the analogue of the farmed church_rosser_conv): two convertible terms JOIN in par_reduces_cd_star — by induction on the conversion, forward steps extend the join by transitivity, and backward (peak) steps are resolved by the par_reduces_cd_star_diamond. This is the theorem that makes definitional equality (generated by the 3-way weak-head reduction) DECIDABLE by joining to a common reduct — over any RedEnv meeting the 8 standard well-formedness interfaces. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_red_conv".to_string(),
                "whnf_red_conv.rec".to_string(),
                "whnf_red_conv.refl".to_string(),
                "whnf_red_conv.fwd".to_string(),
                "whnf_red_conv.bwd".to_string(),
                "par_strips_witness_cd_star".to_string(),
                "par_strips_witness_cd_star.intro".to_string(),
                "par_strips_witness_cd_star.rec".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star_trans".to_string(),
                "par_reduces_cd_star_diamond".to_string(),
                "whnf_red_step_to_par_cd_star".to_string(),
                "whnf_red_step".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "DefEnvClosed".to_string(),
                "DefEnvLiftClosed".to_string(),
                "RecEnvDefEnvDisjoint".to_string(),
                "RecEnvCtorNoDefVal".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_red_conv_trans".to_string(),
            type_src: "forall (renv : RedEnv) (a : KExpr) (b : KExpr) (c : KExpr), whnf_red_conv renv a b -> whnf_red_conv renv b c -> whnf_red_conv renv a c".to_string(),
            value_src: Some("fun (renv : RedEnv) (a : KExpr) (b : KExpr) (c : KExpr) (hab : whnf_red_conv renv a b) (hbc : whnf_red_conv renv b c) => whnf_red_conv.rec renv (fun (x : KExpr) (y : KExpr) (_h : whnf_red_conv renv x y) => whnf_red_conv renv y c -> whnf_red_conv renv x c) (fun (e : KExpr) (h : whnf_red_conv renv e c) => h) (fun (a2 : KExpr) (b2 : KExpr) (c2 : KExpr) (hstep : whnf_red_step renv a2 b2) (_hc : whnf_red_conv renv b2 c2) (ih : whnf_red_conv renv c2 c -> whnf_red_conv renv b2 c) (h : whnf_red_conv renv c2 c) => whnf_red_conv.fwd renv a2 b2 c hstep (ih h)) (fun (a2 : KExpr) (b2 : KExpr) (c2 : KExpr) (hstep : whnf_red_step renv b2 a2) (_hc : whnf_red_conv renv b2 c2) (ih : whnf_red_conv renv c2 c -> whnf_red_conv renv b2 c) (h : whnf_red_conv renv c2 c) => whnf_red_conv.bwd renv a2 b2 c hstep (ih h)) a b hab hbc".to_string()),
            is_axiom: false,
            description: "TRANSITIVITY of whnf_red_conv (definitional conversion): append one conversion onto another, by induction on the first, prepending each step onto the appended tail. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_red_conv".to_string(),
                "whnf_red_conv.rec".to_string(),
                "whnf_red_conv.fwd".to_string(),
                "whnf_red_conv.bwd".to_string(),
                "whnf_red_step".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_red_conv_symm".to_string(),
            type_src: "forall (renv : RedEnv) (a : KExpr) (b : KExpr), whnf_red_conv renv a b -> whnf_red_conv renv b a".to_string(),
            value_src: Some("fun (renv : RedEnv) (a : KExpr) (b : KExpr) (h : whnf_red_conv renv a b) => whnf_red_conv.rec renv (fun (x : KExpr) (y : KExpr) (_h : whnf_red_conv renv x y) => whnf_red_conv renv y x) (fun (e : KExpr) => whnf_red_conv.refl renv e) (fun (a2 : KExpr) (b2 : KExpr) (c2 : KExpr) (hstep : whnf_red_step renv a2 b2) (_hc : whnf_red_conv renv b2 c2) (ih : whnf_red_conv renv c2 b2) => whnf_red_conv_trans renv c2 b2 a2 ih (whnf_red_conv.bwd renv b2 a2 a2 hstep (whnf_red_conv.refl renv a2))) (fun (a2 : KExpr) (b2 : KExpr) (c2 : KExpr) (hstep : whnf_red_step renv b2 a2) (_hc : whnf_red_conv renv b2 c2) (ih : whnf_red_conv renv c2 b2) => whnf_red_conv_trans renv c2 b2 a2 ih (whnf_red_conv.fwd renv b2 a2 a2 hstep (whnf_red_conv.refl renv a2))) a b h".to_string()),
            is_axiom: false,
            description: "SYMMETRY of whnf_red_conv: reverse a conversion, by induction reversing each step (a fwd step a->b yields a single bwd conv b->a and vice versa) composed via whnf_red_conv_trans. With refl and whnf_red_conv_trans this makes whnf_red_conv a genuine EQUIVALENCE relation — a well-formed definitional equality. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_red_conv".to_string(),
                "whnf_red_conv.rec".to_string(),
                "whnf_red_conv.refl".to_string(),
                "whnf_red_conv.fwd".to_string(),
                "whnf_red_conv.bwd".to_string(),
                "whnf_red_conv_trans".to_string(),
                "whnf_red_step".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_red_star_to_conv".to_string(),
            type_src: "forall (renv : RedEnv) (a : KExpr) (b : KExpr), whnf_red_step_star renv a b -> whnf_red_conv renv a b".to_string(),
            value_src: Some("fun (renv : RedEnv) (a : KExpr) (b : KExpr) (h : whnf_red_step_star renv a b) => whnf_red_step_star.rec renv (fun (x : KExpr) (y : KExpr) (_h : whnf_red_step_star renv x y) => whnf_red_conv renv x y) (fun (e : KExpr) => whnf_red_conv.refl renv e) (fun (e : KExpr) (e2 : KExpr) (e3 : KExpr) (hstep : whnf_red_step renv e e2) (_rest : whnf_red_step_star renv e2 e3) (ih : whnf_red_conv renv e2 e3) => whnf_red_conv.fwd renv e e2 e3 hstep ih) a b h".to_string()),
            is_axiom: false,
            description: "REDUCTION REFINES CONVERSION: every whnf_red_step_star reduction is a whnf_red_conv conversion (each forward step injects via whnf_red_conv.fwd). Confirms the proven equivalence whnf_red_conv is exactly the reflexive-symmetric-transitive CLOSURE of the 3-way weak-head reduction. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_red_step_star".to_string(),
                "whnf_red_step_star.rec".to_string(),
                "whnf_red_conv".to_string(),
                "whnf_red_conv.refl".to_string(),
                "whnf_red_conv.fwd".to_string(),
                "whnf_red_step".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "whnf_fuel_red_conv".to_string(),
            type_src: "forall (renv : RedEnv) (fuel : Nat) (e : KExpr) (r : KExpr), Eq (OptionType KExpr) (whnf_fuel_red renv fuel e) (OptionType.some KExpr r) -> whnf_red_conv renv e r".to_string(),
            value_src: Some("fun (renv : RedEnv) (fuel : Nat) (e : KExpr) (r : KExpr) (h : Eq (OptionType KExpr) (whnf_fuel_red renv fuel e) (OptionType.some KExpr r)) => whnf_red_star_to_conv renv e r (red_step_star_to_whnf_red_step_star renv e r (whnf_fuel_red_reaches_sound renv fuel e r h))".to_string()),
            is_axiom: false,
            description: "THE EXECUTABLE-DEFEQ SOUNDNESS BRICK: the executable 3-way loop's result r is DEFINITIONALLY CONVERTIBLE to its input e (whnf_red_conv e r) — reached by genuine steps (whnf_fuel_red_reaches_sound), lifted to the cons-closure and then to the conversion equivalence. So computing a weak-head normal form with whnf_fuel_red is SOUND for definitional equality: e and its normal form are convertible, and by transitivity two terms with convertible normal forms are convertible. The soundness half of deciding defeq via the executable loop. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel_red".to_string(),
                "whnf_fuel_red_reaches_sound".to_string(),
                "red_step_star_to_whnf_red_step_star".to_string(),
                "whnf_red_star_to_conv".to_string(),
                "whnf_red_conv".to_string(),
                "KExpr".to_string(),
                "RedEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    fn add_whnf_fuel_capstone(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "reduce_app_lift_defined".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (f : KExpr) (a : KExpr) (e2 : KExpr), ",
                "consts_defined env a -> ",
                "(forall (e3 : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr e3) -> ",
                "consts_defined env e3) -> ",
                "Eq (OptionType KExpr) (opt_app_lift a (reduce_once env f)) (OptionType.some KExpr e2) -> ",
                "consts_defined env e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (f : KExpr) (a : KExpr) (e2 : KExpr) ",
                    "(hda : consts_defined env a) ",
                    "(ih : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr e3) -> ",
                    "consts_defined env e3) ",
                    "(h : Eq (OptionType KExpr) (opt_app_lift a (reduce_once env f)) (OptionType.some KExpr e2)) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (reduce_once env f) o -> ",
                    "Eq (OptionType KExpr) (opt_app_lift a o) (OptionType.some KExpr e2) -> ",
                    "consts_defined env e2) ",
                    "(fun (_heq : Eq (OptionType KExpr) (reduce_once env f) (OptionType.none KExpr)) ",
                    "(h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.none KExpr)) (OptionType.some KExpr e2)) => ",
                    "opt_none_ne_some_t KExpr e2 (consts_defined env e2) h2) ",
                    "(fun (f2 : KExpr) ",
                    "(heq : Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr f2)) ",
                    "(h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.some KExpr e2)) => ",
                    "Eq.rec KExpr (KExpr.app f2 a) ",
                    "(fun (x : KExpr) (_hx : Eq KExpr (KExpr.app f2 a) x) => consts_defined env x) ",
                    "(AndType.intro (consts_defined env f2) (consts_defined env a) (ih f2 heq) hda) ",
                    "e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2)) ",
                    "(reduce_once env f) (Eq.refl (OptionType KExpr) (reduce_once env f)) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "APP-LIFT DEFINEDNESS (X16c-3b): a lifted head reduct stays fully \
                          defined — the AndType pair of the preserved head and the untouched \
                          argument, transported along some-injectivity. DerivedProved, zero \
                          axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_app_lift".to_string(),
                "reduce_once".to_string(),
                "AndType.intro".to_string(),
                "option_some_inj".to_string(),
                "opt_none_ne_some_t".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_once_preserves_defined".to_string(),
            type_src: concat!(
                "forall (env : DefEnv), def_env_good env -> forall (e : KExpr), ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> forall (e2 : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env e) (OptionType.some KExpr e2) -> ",
                "consts_defined env e2"
            )
            .to_string(),
            value_src: Some(concat!("fun (env : DefEnv) (hEnv : def_env_good env) (e : KExpr) => KExpr.rec ","(fun (e0 : KExpr) => Eq Nat (bvar_ceiling e0) Nat.zero -> consts_defined env e0 -> forall (e2 : KExpr), ","Eq (OptionType KExpr) (reduce_once env e0) (OptionType.some KExpr e2) -> ","consts_defined env e2) ","(fun (n : Level) (_hc : Eq Nat (bvar_ceiling (KExpr.sort n)) Nat.zero) (_hd : consts_defined env (KExpr.sort n)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) (OptionType.some KExpr e2)) => ","opt_none_ne_some_t KExpr e2 (consts_defined env e2) h) ","(fun (i : Nat) (_hc : Eq Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero) (_hd : consts_defined env (KExpr.bvar i)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) (OptionType.some KExpr e2)) => ","opt_none_ne_some_t KExpr e2 (consts_defined env e2) h) ","(fun (f : KExpr) (a : KExpr) ","(ihf : (Eq Nat (bvar_ceiling f) Nat.zero -> consts_defined env f -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr e3) -> consts_defined env e3)) ","(_iha : (Eq Nat (bvar_ceiling a) Nat.zero -> consts_defined env a -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env a) (OptionType.some KExpr e3) -> consts_defined env e3)) ","(hc : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) ","(hd : consts_defined env (KExpr.app f a)) (e2out : KExpr) ","(hout : Eq (OptionType KExpr) (reduce_once env (KExpr.app f a)) (OptionType.some KExpr e2out)) => ","(fun (hcf : Eq Nat (bvar_ceiling f) Nat.zero) (hca : Eq Nat (bvar_ceiling a) Nat.zero) (hdf : consts_defined env f) (hda : consts_defined env a) => ","KExpr.rec ","(fun (g : KExpr) => ","(Eq Nat (bvar_ceiling g) Nat.zero -> consts_defined env g -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env g) (OptionType.some KExpr e3) -> consts_defined env e3) -> ","Eq Nat (bvar_ceiling g) Nat.zero -> consts_defined env g -> forall (e2 : KExpr), ","Eq (OptionType KExpr) (reduce_app_head a g (reduce_once env g)) (OptionType.some KExpr e2) -> ","consts_defined env e2) ","(fun (n2 : Level) (ihg : (Eq Nat (bvar_ceiling (KExpr.sort n2)) Nat.zero -> consts_defined env (KExpr.sort n2) -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.sort n2)) (OptionType.some KExpr e3) -> consts_defined env e3)) (hcg : Eq Nat (bvar_ceiling (KExpr.sort n2)) Nat.zero) (hdg : consts_defined env (KExpr.sort n2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.sort n2) (reduce_once env (KExpr.sort n2))) (OptionType.some KExpr e2)) => reduce_app_lift_defined env (KExpr.sort n2) a e2 hda (ihg hcg hdg) h) ","(fun (i2 : Nat) (ihg : (Eq Nat (bvar_ceiling (KExpr.bvar i2)) Nat.zero -> consts_defined env (KExpr.bvar i2) -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i2)) (OptionType.some KExpr e3) -> consts_defined env e3)) (hcg : Eq Nat (bvar_ceiling (KExpr.bvar i2)) Nat.zero) (hdg : consts_defined env (KExpr.bvar i2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.bvar i2) (reduce_once env (KExpr.bvar i2))) (OptionType.some KExpr e2)) => reduce_app_lift_defined env (KExpr.bvar i2) a e2 hda (ihg hcg hdg) h) ","(fun (g1 : KExpr) (g2 : KExpr) (_j1 : ((Eq Nat (bvar_ceiling g1) Nat.zero -> consts_defined env g1 -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env g1) (OptionType.some KExpr e3) -> consts_defined env e3) -> Eq Nat (bvar_ceiling g1) Nat.zero -> consts_defined env g1 -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a g1 (reduce_once env g1)) (OptionType.some KExpr e4) -> consts_defined env e4)) (_j2 : ((Eq Nat (bvar_ceiling g2) Nat.zero -> consts_defined env g2 -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env g2) (OptionType.some KExpr e3) -> consts_defined env e3) -> Eq Nat (bvar_ceiling g2) Nat.zero -> consts_defined env g2 -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a g2 (reduce_once env g2)) (OptionType.some KExpr e4) -> consts_defined env e4)) (ihg : (Eq Nat (bvar_ceiling (KExpr.app g1 g2)) Nat.zero -> consts_defined env (KExpr.app g1 g2) -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app g1 g2)) (OptionType.some KExpr e3) -> consts_defined env e3)) (hcg : Eq Nat (bvar_ceiling (KExpr.app g1 g2)) Nat.zero) (hdg : consts_defined env (KExpr.app g1 g2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.app g1 g2) (reduce_once env (KExpr.app g1 g2))) (OptionType.some KExpr e2)) => reduce_app_lift_defined env (KExpr.app g1 g2) a e2 hda (ihg hcg hdg) h) ","(fun (ty2 : KExpr) (b2 : KExpr) ","(_j1 : ((Eq Nat (bvar_ceiling ty2) Nat.zero -> consts_defined env ty2 -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty2) (OptionType.some KExpr e3) -> consts_defined env e3) -> Eq Nat (bvar_ceiling ty2) Nat.zero -> consts_defined env ty2 -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a ty2 (reduce_once env ty2)) (OptionType.some KExpr e4) -> consts_defined env e4)) ","(_j2 : ((Eq Nat (bvar_ceiling b2) Nat.zero -> consts_defined env b2 -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b2) (OptionType.some KExpr e3) -> consts_defined env e3) -> Eq Nat (bvar_ceiling b2) Nat.zero -> consts_defined env b2 -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a b2 (reduce_once env b2)) (OptionType.some KExpr e4) -> consts_defined env e4)) ","(_ihg : (Eq Nat (bvar_ceiling (KExpr.lam ty2 b2)) Nat.zero -> consts_defined env (KExpr.lam ty2 b2) -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.lam ty2 b2)) (OptionType.some KExpr e3) -> consts_defined env e3)) ","(hcg : Eq Nat (bvar_ceiling (KExpr.lam ty2 b2)) Nat.zero) ","(hdg : consts_defined env (KExpr.lam ty2 b2)) (e2 : KExpr) ","(h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.lam ty2 b2) (reduce_once env (KExpr.lam ty2 b2))) (OptionType.some KExpr e2)) => ","(fun (hb0 : Eq Nat (bvar_ceiling b2) Nat.zero) => ","Eq.rec KExpr b2 ","(fun (x : KExpr) (_hx : Eq KExpr b2 x) => consts_defined env x) ","(AndType.right (consts_defined env ty2) (consts_defined env b2) hdg) e2 ","(Eq.trans KExpr b2 (instantiate b2 a) e2 ","(Eq.symm KExpr (instantiate b2 a) b2 (inst_closed_id b2 a hb0)) ","(option_some_inj KExpr (instantiate b2 a) e2 h))) ","(nat_add_eq_zero_right (bvar_ceiling ty2) (bvar_ceiling b2) hcg)) ","(fun (ty2 : KExpr) (b2 : KExpr) (_j1 : ((Eq Nat (bvar_ceiling ty2) Nat.zero -> consts_defined env ty2 -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty2) (OptionType.some KExpr e3) -> consts_defined env e3) -> Eq Nat (bvar_ceiling ty2) Nat.zero -> consts_defined env ty2 -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a ty2 (reduce_once env ty2)) (OptionType.some KExpr e4) -> consts_defined env e4)) (_j2 : ((Eq Nat (bvar_ceiling b2) Nat.zero -> consts_defined env b2 -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b2) (OptionType.some KExpr e3) -> consts_defined env e3) -> Eq Nat (bvar_ceiling b2) Nat.zero -> consts_defined env b2 -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a b2 (reduce_once env b2)) (OptionType.some KExpr e4) -> consts_defined env e4)) (ihg : (Eq Nat (bvar_ceiling (KExpr.pi ty2 b2)) Nat.zero -> consts_defined env (KExpr.pi ty2 b2) -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty2 b2)) (OptionType.some KExpr e3) -> consts_defined env e3)) (hcg : Eq Nat (bvar_ceiling (KExpr.pi ty2 b2)) Nat.zero) (hdg : consts_defined env (KExpr.pi ty2 b2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.pi ty2 b2) (reduce_once env (KExpr.pi ty2 b2))) (OptionType.some KExpr e2)) => reduce_app_lift_defined env (KExpr.pi ty2 b2) a e2 hda (ihg hcg hdg) h) ","(fun (n2 : Name) (us2 : ListType Level) (ihg : (Eq Nat (bvar_ceiling (KExpr.const n2 us2)) Nat.zero -> consts_defined env (KExpr.const n2 us2) -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.const n2 us2)) (OptionType.some KExpr e3) -> consts_defined env e3)) (hcg : Eq Nat (bvar_ceiling (KExpr.const n2 us2)) Nat.zero) (hdg : consts_defined env (KExpr.const n2 us2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.const n2 us2) (reduce_once env (KExpr.const n2 us2))) (OptionType.some KExpr e2)) => reduce_app_lift_defined env (KExpr.const n2 us2) a e2 hda (ihg hcg hdg) h) ","(fun (ty2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_j1 : ((Eq Nat (bvar_ceiling ty2) Nat.zero -> consts_defined env ty2 -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty2) (OptionType.some KExpr e3) -> consts_defined env e3) -> Eq Nat (bvar_ceiling ty2) Nat.zero -> consts_defined env ty2 -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a ty2 (reduce_once env ty2)) (OptionType.some KExpr e4) -> consts_defined env e4)) (_j2 : ((Eq Nat (bvar_ceiling v2) Nat.zero -> consts_defined env v2 -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env v2) (OptionType.some KExpr e3) -> consts_defined env e3) -> Eq Nat (bvar_ceiling v2) Nat.zero -> consts_defined env v2 -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a v2 (reduce_once env v2)) (OptionType.some KExpr e4) -> consts_defined env e4)) (_j3 : ((Eq Nat (bvar_ceiling b2) Nat.zero -> consts_defined env b2 -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b2) (OptionType.some KExpr e3) -> consts_defined env e3) -> Eq Nat (bvar_ceiling b2) Nat.zero -> consts_defined env b2 -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a b2 (reduce_once env b2)) (OptionType.some KExpr e4) -> consts_defined env e4)) (ihg : (Eq Nat (bvar_ceiling (KExpr.let_ ty2 v2 b2)) Nat.zero -> consts_defined env (KExpr.let_ ty2 v2 b2) -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty2 v2 b2)) (OptionType.some KExpr e3) -> consts_defined env e3)) (hcg : Eq Nat (bvar_ceiling (KExpr.let_ ty2 v2 b2)) Nat.zero) (hdg : consts_defined env (KExpr.let_ ty2 v2 b2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.let_ ty2 v2 b2) (reduce_once env (KExpr.let_ ty2 v2 b2))) (OptionType.some KExpr e2)) => reduce_app_lift_defined env (KExpr.let_ ty2 v2 b2) a e2 hda (ihg hcg hdg) h) ","(fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_j1 : ((Eq Nat (bvar_ceiling sub2) Nat.zero -> consts_defined env sub2 -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env sub2) (OptionType.some KExpr e3) -> consts_defined env e3) -> Eq Nat (bvar_ceiling sub2) Nat.zero -> consts_defined env sub2 -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a sub2 (reduce_once env sub2)) (OptionType.some KExpr e4) -> consts_defined env e4)) (ihg : (Eq Nat (bvar_ceiling (KExpr.proj s2 i2 sub2)) Nat.zero -> consts_defined env (KExpr.proj s2 i2 sub2) -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.proj s2 i2 sub2)) (OptionType.some KExpr e3) -> consts_defined env e3)) (hcg : Eq Nat (bvar_ceiling (KExpr.proj s2 i2 sub2)) Nat.zero) (hdg : consts_defined env (KExpr.proj s2 i2 sub2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.proj s2 i2 sub2) (reduce_once env (KExpr.proj s2 i2 sub2))) (OptionType.some KExpr e2)) => reduce_app_lift_defined env (KExpr.proj s2 i2 sub2) a e2 hda (ihg hcg hdg) h) ","(fun (v2 : Nat) (ihg : (Eq Nat (bvar_ceiling (KExpr.lit v2)) Nat.zero -> consts_defined env (KExpr.lit v2) -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.lit v2)) (OptionType.some KExpr e3) -> consts_defined env e3)) (hcg : Eq Nat (bvar_ceiling (KExpr.lit v2)) Nat.zero) (hdg : consts_defined env (KExpr.lit v2)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.lit v2) (reduce_once env (KExpr.lit v2))) (OptionType.some KExpr e2)) => reduce_app_lift_defined env (KExpr.lit v2) a e2 hda (ihg hcg hdg) h) ","f ihf hcf hdf e2out hout) ","(nat_add_eq_zero_left (bvar_ceiling f) (bvar_ceiling a) hc) ","(nat_add_eq_zero_right (bvar_ceiling f) (bvar_ceiling a) hc) ","(AndType.left (consts_defined env f) (consts_defined env a) hd) ","(AndType.right (consts_defined env f) (consts_defined env a) hd)) ","(fun (ty : KExpr) (b : KExpr) ","(_i1 : (Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> consts_defined env e3)) ","(_i2 : (Eq Nat (bvar_ceiling b) Nat.zero -> consts_defined env b -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> consts_defined env e3)) ","(_hc : Eq Nat (bvar_ceiling (KExpr.lam ty b)) Nat.zero) (_hd : consts_defined env (KExpr.lam ty b)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.lam ty b)) (OptionType.some KExpr e2)) => ","opt_none_ne_some_t KExpr e2 (consts_defined env e2) h) ","(fun (ty : KExpr) (b : KExpr) ","(_i1 : (Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> consts_defined env e3)) ","(_i2 : (Eq Nat (bvar_ceiling b) Nat.zero -> consts_defined env b -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> consts_defined env e3)) ","(_hc : Eq Nat (bvar_ceiling (KExpr.pi ty b)) Nat.zero) (_hd : consts_defined env (KExpr.pi ty b)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) (OptionType.some KExpr e2)) => ","opt_none_ne_some_t KExpr e2 (consts_defined env e2) h) ","(fun (n : Name) (us : ListType Level) (_hc : Eq Nat (bvar_ceiling (KExpr.const n us)) Nat.zero) (_hd : consts_defined env (KExpr.const n us)) (e2 : KExpr) ","(h : Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) (OptionType.some KExpr e2)) => ","AndType.right (LiftP (Eq Nat (bvar_ceiling e2) Nat.zero)) (consts_defined env e2) (hEnv n e2 h)) ","(fun (ty : KExpr) (v : KExpr) (b : KExpr) ","(_i1 : (Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> consts_defined env e3)) ","(_i2 : (Eq Nat (bvar_ceiling v) Nat.zero -> consts_defined env v -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env v) (OptionType.some KExpr e3) -> consts_defined env e3)) ","(_i3 : (Eq Nat (bvar_ceiling b) Nat.zero -> consts_defined env b -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> consts_defined env e3)) ","(hc : Eq Nat (bvar_ceiling (KExpr.let_ ty v b)) Nat.zero) ","(hd : consts_defined env (KExpr.let_ ty v b)) (e2 : KExpr) ","(h : Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) (OptionType.some KExpr e2)) => ","(fun (hb0 : Eq Nat (bvar_ceiling b) Nat.zero) => ","Eq.rec KExpr b ","(fun (x : KExpr) (_hx : Eq KExpr b x) => consts_defined env x) ","(AndType.right (consts_defined env v) (consts_defined env b) ","(AndType.right (consts_defined env ty) (AndType (consts_defined env v) (consts_defined env b)) hd)) e2 ","(Eq.trans KExpr b (instantiate b v) e2 ","(Eq.symm KExpr (instantiate b v) b (inst_closed_id b v hb0)) ","(option_some_inj KExpr (instantiate b v) e2 h))) ","(nat_add_eq_zero_right (bvar_ceiling v) (bvar_ceiling b) ","(nat_add_eq_zero_right (bvar_ceiling ty) (Nat.add (bvar_ceiling v) (bvar_ceiling b)) hc))) ","(fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : Eq Nat (bvar_ceiling sub) Nat.zero -> consts_defined env sub -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr e3) -> consts_defined env e3) (hc : Eq Nat (bvar_ceiling (KExpr.proj s i sub)) Nat.zero) (hd : consts_defined env (KExpr.proj s i sub)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.proj s i sub)) (OptionType.some KExpr e2)) => proj_lift_defined env s i sub e2 (ihsub hc hd) h) ","(fun (v : Nat) (_hc : Eq Nat (bvar_ceiling (KExpr.lit v)) Nat.zero) (_hd : consts_defined env (KExpr.lit v)) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.lit v)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (consts_defined env e2) h) ","e").to_string()),
            is_axiom: false,
            description: "DEFINEDNESS PRESERVATION (X16c-3b, round-4 guide \
                          reduceOnce_preserves_defined): one executable step out of a closed, \
                          fully-defined term stays fully defined over a good environment — \
                          β/ζ by the identity bridge with the definedness component, δ by the \
                          environment's definedness half, app-lift by AndType reassembly. \
                          DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once".to_string(),
                "def_env_good".to_string(),
                "inst_closed_id".to_string(),
                "reduce_app_lift_defined".to_string(),
                "nat_add_eq_zero_left".to_string(),
                "nat_add_eq_zero_right".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // THE CAPSTONE.
        self.add_definition(SpecDefinition {
            name: "whnf_fuel_classifies".to_string(),
            type_src: concat!(
                "forall (env : DefEnv), def_env_good env -> forall (fuel : Nat) (e : KExpr) (r : KExpr), ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> ",
                "Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r) -> ",
                "whnf_noredex_class r"
            )
            .to_string(),
            value_src: Some(concat!("fun (env : DefEnv) (hEnv : def_env_good env) (fuel : Nat) => Nat.rec ","(fun (k : Nat) => forall (e : KExpr) (r : KExpr), ","Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> ","Eq (OptionType KExpr) (whnf_fuel env k e) (OptionType.some KExpr r) -> ","whnf_noredex_class r) ","(fun (e : KExpr) (r : KExpr) (_hc : Eq Nat (bvar_ceiling e) Nat.zero) (_hd : consts_defined env e) ","(h : Eq (OptionType KExpr) (whnf_fuel env Nat.zero e) (OptionType.some KExpr r)) => ","opt_none_ne_some_t KExpr r (whnf_noredex_class r) h) ","(fun (k : Nat) ","(ih : forall (e0 : KExpr) (r0 : KExpr), Eq Nat (bvar_ceiling e0) Nat.zero -> consts_defined env e0 -> Eq (OptionType KExpr) (whnf_fuel env k e0) (OptionType.some KExpr r0) -> whnf_noredex_class r0) ","(e : KExpr) (r : KExpr) (hc : Eq Nat (bvar_ceiling e) Nat.zero) (hd : consts_defined env e) ","(h : Eq (OptionType KExpr) (whnf_fuel env (Nat.succ k) e) (OptionType.some KExpr r)) => ","OptionType.rec KExpr ","(fun (o : OptionType KExpr) => ","Eq (OptionType KExpr) (reduce_once env e) o -> ","Eq (OptionType KExpr) (loop_dispatch o e (fun (e2 : KExpr) => whnf_fuel env k e2)) (OptionType.some KExpr r) -> ","whnf_noredex_class r) ","(fun (heq : Eq (OptionType KExpr) (reduce_once env e) (OptionType.none KExpr)) ","(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e (fun (e2 : KExpr) => whnf_fuel env k e2)) (OptionType.some KExpr r)) => ","Eq.rec KExpr e ","(fun (x : KExpr) (_hx : Eq KExpr e x) => whnf_noredex_class x) ","(reduce_once_none_classifies env e heq hc hd) ","r (option_some_inj KExpr e r h2)) ","(fun (e2 : KExpr) ","(heq : Eq (OptionType KExpr) (reduce_once env e) (OptionType.some KExpr e2)) ","(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.some KExpr e2) e (fun (e3 : KExpr) => whnf_fuel env k e3)) (OptionType.some KExpr r)) => ","ih e2 r ","(reduce_once_preserves_closed env hEnv e hc e2 heq) ","(reduce_once_preserves_defined env hEnv e hc hd e2 heq) ","h2) ","(reduce_once env e) (Eq.refl (OptionType KExpr) (reduce_once env e)) h) ","fuel").to_string()),
            is_axiom: false,
            description: "THE EXECUTABLE-LOOP CAPSTONE (X16c-3b, round-4 guide \
                          whnfFuel_classifies_env): over a good environment, EVERY successful \
                          fuel-bounded loop result on a closed, fully-defined term CLASSIFIES \
                          — a landed is_whnf value or the honest stuck residual; a none is \
                          only ever the honest fuel bail. Fuel induction threading both \
                          preservation theorems, closing at the fixpoint with the direct \
                          executable classification. With this, the in-spec fuel loop — a \
                          β/ζ/bare-δ + proj-congruence fragment skeleton of the literal \
                          whnf_outer_loop (no ι/accelerators/cache; the correspondence to \
                          the literal loop is informal) — is verified end to end in Clean's \
                          own kernel: reached by genuine steps (M10), a fixpoint (M8), and \
                          CLASSIFIED (this theorem). DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel".to_string(),
                "loop_dispatch".to_string(),
                "reduce_once_none_classifies".to_string(),
                "reduce_once_preserves_closed".to_string(),
                "reduce_once_preserves_defined".to_string(),
                "def_env_good".to_string(),
                "whnf_noredex_class".to_string(),
                "option_some_inj".to_string(),
                "opt_none_ne_some_t".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// X16c-3a — CLOSEDNESS PRESERVATION for the executable step (round-4
    /// guide): the identity bridge (substituting into a bvar-free body is the
    /// identity), the both-zero add combiner, app-lift preservation, and the
    /// main theorem over `def_env_good`.
    fn add_reduce_once_preserves_closed(&mut self) -> Result<(), SpecError> {
        // From Eq to Le at zero, then the registered identity lemma.
        self.add_definition(SpecDefinition {
            name: "inst_closed_id".to_string(),
            type_src: concat!(
                "forall (b : KExpr) (v : KExpr), ",
                "Eq Nat (bvar_ceiling b) Nat.zero -> Eq KExpr (instantiate b v) b"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (b : KExpr) (v : KExpr) (hb : Eq Nat (bvar_ceiling b) Nat.zero) => ",
                    "inst_above_ceiling_id b v Nat.zero ",
                    "(Eq.rec Nat Nat.zero ",
                    "(fun (x : Nat) (_hx : Eq Nat Nat.zero x) => Le x Nat.zero) ",
                    "(le_zero_n Nat.zero) ",
                    "(bvar_ceiling b) ",
                    "(Eq.symm Nat (bvar_ceiling b) Nat.zero hb))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "IDENTITY BRIDGE (X16c-3a): substituting into a bvar-free body is \
                          the identity — the registered inst_above_ceiling_id at depth zero, \
                          with the Le hypothesis transported from the Eq. DerivedProved, zero \
                          axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "inst_above_ceiling_id".to_string(),
                "instantiate".to_string(),
                "le_zero_n".to_string(),
                "Eq.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "nat_both_zero_add".to_string(),
            type_src: concat!(
                "forall (x : Nat) (y : Nat), ",
                "Eq Nat x Nat.zero -> Eq Nat y Nat.zero -> Eq Nat (Nat.add x y) Nat.zero"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (x : Nat) (y : Nat) (hx : Eq Nat x Nat.zero) (hy : Eq Nat y Nat.zero) => ",
                    "Eq.trans Nat (Nat.add x y) (Nat.add Nat.zero y) Nat.zero ",
                    "(Eq.rec Nat x ",
                    "(fun (w : Nat) (_hw : Eq Nat x w) => Eq Nat (Nat.add x y) (Nat.add w y)) ",
                    "(Eq.refl Nat (Nat.add x y)) Nat.zero hx) ",
                    "(Eq.rec Nat y ",
                    "(fun (w : Nat) (_hw : Eq Nat y w) => Eq Nat (Nat.add Nat.zero y) (Nat.add Nat.zero w)) ",
                    "(Eq.refl Nat (Nat.add Nat.zero y)) Nat.zero hy)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "BOTH-ZERO ADD (X16c-3a): two zero components make a zero sum — two \
                          transports meeting at add zero zero, which computes. DerivedProved, \
                          zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["Eq.trans".to_string(), "Eq.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_app_lift_closed".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (f : KExpr) (a : KExpr) (e2 : KExpr), ",
                "Eq Nat (bvar_ceiling a) Nat.zero -> ",
                "(forall (e3 : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr e3) -> ",
                "Eq Nat (bvar_ceiling e3) Nat.zero) -> ",
                "Eq (OptionType KExpr) (opt_app_lift a (reduce_once env f)) (OptionType.some KExpr e2) -> ",
                "Eq Nat (bvar_ceiling e2) Nat.zero"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (f : KExpr) (a : KExpr) (e2 : KExpr) ",
                    "(hca : Eq Nat (bvar_ceiling a) Nat.zero) ",
                    "(ih : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr e3) -> ",
                    "Eq Nat (bvar_ceiling e3) Nat.zero) ",
                    "(h : Eq (OptionType KExpr) (opt_app_lift a (reduce_once env f)) (OptionType.some KExpr e2)) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (reduce_once env f) o -> ",
                    "Eq (OptionType KExpr) (opt_app_lift a o) (OptionType.some KExpr e2) -> ",
                    "Eq Nat (bvar_ceiling e2) Nat.zero) ",
                    "(fun (_heq : Eq (OptionType KExpr) (reduce_once env f) (OptionType.none KExpr)) ",
                    "(h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.none KExpr)) (OptionType.some KExpr e2)) => ",
                    "option_none_ne_some KExpr e2 (Eq Nat (bvar_ceiling e2) Nat.zero) h2) ",
                    "(fun (f2 : KExpr) ",
                    "(heq : Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr f2)) ",
                    "(h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.some KExpr e2)) => ",
                    "Eq.rec KExpr (KExpr.app f2 a) ",
                    "(fun (x : KExpr) (_hx : Eq KExpr (KExpr.app f2 a) x) => Eq Nat (bvar_ceiling x) Nat.zero) ",
                    "(nat_both_zero_add (bvar_ceiling f2) (bvar_ceiling a) (ih f2 heq) hca) ",
                    "e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2)) ",
                    "(reduce_once env f) (Eq.refl (OptionType KExpr) (reduce_once env f)) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "APP-LIFT CLOSEDNESS (X16c-3a): a lifted head reduct stays closed — \
                          the sum of two zero ceilings, transported along some-injectivity. \
                          DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_app_lift".to_string(),
                "reduce_once".to_string(),
                "nat_both_zero_add".to_string(),
                "option_some_inj".to_string(),
                "option_none_ne_some".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "proj_lift_closed".to_string(),
            type_src: "forall (env : DefEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr), (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once env sub)) (OptionType.some KExpr e2) -> Eq Nat (bvar_ceiling e2) Nat.zero".to_string(),
            value_src: Some("fun (env : DefEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr) (ih : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) (h : Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once env sub)) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once env sub) o -> Eq (OptionType KExpr) (opt_proj_lift s i o) (OptionType.some KExpr e2) -> Eq Nat (bvar_ceiling e2) Nat.zero) (fun (_heq : Eq (OptionType KExpr) (reduce_once env sub) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.none KExpr)) (OptionType.some KExpr e2)) => option_none_ne_some KExpr e2 (Eq Nat (bvar_ceiling e2) Nat.zero) h2) (fun (sub2 : KExpr) (heq : Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr sub2)) (h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.some KExpr sub2)) (OptionType.some KExpr e2)) => Eq.rec KExpr (KExpr.proj s i sub2) (fun (x : KExpr) (_hx : Eq KExpr (KExpr.proj s i sub2) x) => Eq Nat (bvar_ceiling x) Nat.zero) (ih sub2 heq) e2 (option_some_inj KExpr (KExpr.proj s i sub2) e2 h2)) (reduce_once env sub) (Eq.refl (OptionType KExpr) (reduce_once env sub)) h".to_string()),
            is_axiom: false,
            description: "PROJ-LIFT CLOSEDNESS (proj/lit rec-site migration, audit C1): a some through the executable proj lift stays bvar-closed — the reduct is proj s i sub2 whose ceiling IS the scrutinee reduct's ceiling, supplied by the IH. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_proj_lift".to_string(),
                "reduce_once".to_string(),
                "bvar_ceiling".to_string(),
                "option_none_ne_some".to_string(),
                "option_some_inj".to_string(),
                "OptionType.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "proj_lift_defined".to_string(),
            type_src: "forall (env : DefEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr), (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr e3) -> consts_defined env e3) -> Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once env sub)) (OptionType.some KExpr e2) -> consts_defined env e2".to_string(),
            value_src: Some("fun (env : DefEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr) (ih : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr e3) -> consts_defined env e3) (h : Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once env sub)) (OptionType.some KExpr e2)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once env sub) o -> Eq (OptionType KExpr) (opt_proj_lift s i o) (OptionType.some KExpr e2) -> consts_defined env e2) (fun (_heq : Eq (OptionType KExpr) (reduce_once env sub) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.none KExpr)) (OptionType.some KExpr e2)) => opt_none_ne_some_t KExpr e2 (consts_defined env e2) h2) (fun (sub2 : KExpr) (heq : Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr sub2)) (h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.some KExpr sub2)) (OptionType.some KExpr e2)) => Eq.rec KExpr (KExpr.proj s i sub2) (fun (x : KExpr) (_hx : Eq KExpr (KExpr.proj s i sub2) x) => consts_defined env x) (ih sub2 heq) e2 (option_some_inj KExpr (KExpr.proj s i sub2) e2 h2)) (reduce_once env sub) (Eq.refl (OptionType KExpr) (reduce_once env sub)) h".to_string()),
            is_axiom: false,
            description: "PROJ-LIFT DEFINEDNESS (proj/lit rec-site migration, audit C1): a some through the executable proj lift stays fully const-defined — consts_defined passes through the projection node to the scrutinee reduct, supplied by the IH. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_proj_lift".to_string(),
                "reduce_once".to_string(),
                "consts_defined".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "OptionType.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_once_preserves_closed".to_string(),
            type_src: concat!(
                "forall (env : DefEnv), def_env_good env -> forall (e : KExpr), ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> forall (e2 : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env e) (OptionType.some KExpr e2) -> ",
                "Eq Nat (bvar_ceiling e2) Nat.zero"
            )
            .to_string(),
            value_src: Some(concat!("fun (env : DefEnv) (hEnv : def_env_good env) (e : KExpr) => KExpr.rec ","(fun (e0 : KExpr) => Eq Nat (bvar_ceiling e0) Nat.zero -> forall (e2 : KExpr), ","Eq (OptionType KExpr) (reduce_once env e0) (OptionType.some KExpr e2) -> ","Eq Nat (bvar_ceiling e2) Nat.zero) ","(fun (n : Level) (_hc : Eq Nat (bvar_ceiling (KExpr.sort n)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) (OptionType.some KExpr e2)) => ","option_none_ne_some KExpr e2 (Eq Nat (bvar_ceiling e2) Nat.zero) h) ","(fun (i : Nat) (_hc : Eq Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) (OptionType.some KExpr e2)) => ","option_none_ne_some KExpr e2 (Eq Nat (bvar_ceiling e2) Nat.zero) h) ","(fun (f : KExpr) (a : KExpr) ","(ihf : Eq Nat (bvar_ceiling f) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) ","(_iha : Eq Nat (bvar_ceiling a) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env a) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) ","(hc : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) (e2out : KExpr) ","(hout : Eq (OptionType KExpr) (reduce_once env (KExpr.app f a)) (OptionType.some KExpr e2out)) => ","(fun (hcf : Eq Nat (bvar_ceiling f) Nat.zero) (hca : Eq Nat (bvar_ceiling a) Nat.zero) => ","KExpr.rec ","(fun (g : KExpr) => ","(Eq Nat (bvar_ceiling g) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env g) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> ","Eq Nat (bvar_ceiling g) Nat.zero -> forall (e2 : KExpr), ","Eq (OptionType KExpr) (reduce_app_head a g (reduce_once env g)) (OptionType.some KExpr e2) -> ","Eq Nat (bvar_ceiling e2) Nat.zero) ","(fun (n2 : Level) (ihg : Eq Nat (bvar_ceiling (KExpr.sort n2)) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.sort n2)) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) (hcg : Eq Nat (bvar_ceiling (KExpr.sort n2)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.sort n2) (reduce_once env (KExpr.sort n2))) (OptionType.some KExpr e2)) => reduce_app_lift_closed env (KExpr.sort n2) a e2 hca (ihg hcg) h) ","(fun (i2 : Nat) (ihg : Eq Nat (bvar_ceiling (KExpr.bvar i2)) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i2)) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) (hcg : Eq Nat (bvar_ceiling (KExpr.bvar i2)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.bvar i2) (reduce_once env (KExpr.bvar i2))) (OptionType.some KExpr e2)) => reduce_app_lift_closed env (KExpr.bvar i2) a e2 hca (ihg hcg) h) ","(fun (g1 : KExpr) (g2 : KExpr) (_j1 : (Eq Nat (bvar_ceiling g1) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env g1) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> Eq Nat (bvar_ceiling g1) Nat.zero -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a g1 (reduce_once env g1)) (OptionType.some KExpr e4) -> Eq Nat (bvar_ceiling e4) Nat.zero) (_j2 : (Eq Nat (bvar_ceiling g2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env g2) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> Eq Nat (bvar_ceiling g2) Nat.zero -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a g2 (reduce_once env g2)) (OptionType.some KExpr e4) -> Eq Nat (bvar_ceiling e4) Nat.zero) (ihg : Eq Nat (bvar_ceiling (KExpr.app g1 g2)) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app g1 g2)) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) (hcg : Eq Nat (bvar_ceiling (KExpr.app g1 g2)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.app g1 g2) (reduce_once env (KExpr.app g1 g2))) (OptionType.some KExpr e2)) => reduce_app_lift_closed env (KExpr.app g1 g2) a e2 hca (ihg hcg) h) ","(fun (ty2 : KExpr) (b2 : KExpr) ","(_j1 : (Eq Nat (bvar_ceiling ty2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty2) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> Eq Nat (bvar_ceiling ty2) Nat.zero -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a ty2 (reduce_once env ty2)) (OptionType.some KExpr e4) -> Eq Nat (bvar_ceiling e4) Nat.zero) ","(_j2 : (Eq Nat (bvar_ceiling b2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b2) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> Eq Nat (bvar_ceiling b2) Nat.zero -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a b2 (reduce_once env b2)) (OptionType.some KExpr e4) -> Eq Nat (bvar_ceiling e4) Nat.zero) ","(_ihg : Eq Nat (bvar_ceiling (KExpr.lam ty2 b2)) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.lam ty2 b2)) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) ","(hcg : Eq Nat (bvar_ceiling (KExpr.lam ty2 b2)) Nat.zero) (e2 : KExpr) ","(h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.lam ty2 b2) (reduce_once env (KExpr.lam ty2 b2))) (OptionType.some KExpr e2)) => ","(fun (hb0 : Eq Nat (bvar_ceiling b2) Nat.zero) => ","Eq.rec KExpr b2 ","(fun (x : KExpr) (_hx : Eq KExpr b2 x) => Eq Nat (bvar_ceiling x) Nat.zero) ","hb0 e2 ","(Eq.trans KExpr b2 (instantiate b2 a) e2 ","(Eq.symm KExpr (instantiate b2 a) b2 (inst_closed_id b2 a hb0)) ","(option_some_inj KExpr (instantiate b2 a) e2 h))) ","(nat_add_eq_zero_right (bvar_ceiling ty2) (bvar_ceiling b2) hcg)) ","(fun (ty2 : KExpr) (b2 : KExpr) (_j1 : (Eq Nat (bvar_ceiling ty2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty2) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> Eq Nat (bvar_ceiling ty2) Nat.zero -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a ty2 (reduce_once env ty2)) (OptionType.some KExpr e4) -> Eq Nat (bvar_ceiling e4) Nat.zero) (_j2 : (Eq Nat (bvar_ceiling b2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b2) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> Eq Nat (bvar_ceiling b2) Nat.zero -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a b2 (reduce_once env b2)) (OptionType.some KExpr e4) -> Eq Nat (bvar_ceiling e4) Nat.zero) (ihg : Eq Nat (bvar_ceiling (KExpr.pi ty2 b2)) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty2 b2)) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) (hcg : Eq Nat (bvar_ceiling (KExpr.pi ty2 b2)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.pi ty2 b2) (reduce_once env (KExpr.pi ty2 b2))) (OptionType.some KExpr e2)) => reduce_app_lift_closed env (KExpr.pi ty2 b2) a e2 hca (ihg hcg) h) ","(fun (n2 : Name) (us2 : ListType Level) (ihg : Eq Nat (bvar_ceiling (KExpr.const n2 us2)) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.const n2 us2)) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) (hcg : Eq Nat (bvar_ceiling (KExpr.const n2 us2)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.const n2 us2) (reduce_once env (KExpr.const n2 us2))) (OptionType.some KExpr e2)) => reduce_app_lift_closed env (KExpr.const n2 us2) a e2 hca (ihg hcg) h) ","(fun (ty2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_j1 : (Eq Nat (bvar_ceiling ty2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty2) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> Eq Nat (bvar_ceiling ty2) Nat.zero -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a ty2 (reduce_once env ty2)) (OptionType.some KExpr e4) -> Eq Nat (bvar_ceiling e4) Nat.zero) (_j2 : (Eq Nat (bvar_ceiling v2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env v2) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> Eq Nat (bvar_ceiling v2) Nat.zero -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a v2 (reduce_once env v2)) (OptionType.some KExpr e4) -> Eq Nat (bvar_ceiling e4) Nat.zero) (_j3 : (Eq Nat (bvar_ceiling b2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b2) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> Eq Nat (bvar_ceiling b2) Nat.zero -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a b2 (reduce_once env b2)) (OptionType.some KExpr e4) -> Eq Nat (bvar_ceiling e4) Nat.zero) (ihg : Eq Nat (bvar_ceiling (KExpr.let_ ty2 v2 b2)) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty2 v2 b2)) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) (hcg : Eq Nat (bvar_ceiling (KExpr.let_ ty2 v2 b2)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.let_ ty2 v2 b2) (reduce_once env (KExpr.let_ ty2 v2 b2))) (OptionType.some KExpr e2)) => reduce_app_lift_closed env (KExpr.let_ ty2 v2 b2) a e2 hca (ihg hcg) h) ","(fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_j1 : (Eq Nat (bvar_ceiling sub2) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env sub2) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) -> Eq Nat (bvar_ceiling sub2) Nat.zero -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a sub2 (reduce_once env sub2)) (OptionType.some KExpr e4) -> Eq Nat (bvar_ceiling e4) Nat.zero) (ihg : Eq Nat (bvar_ceiling (KExpr.proj s2 i2 sub2)) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.proj s2 i2 sub2)) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) (hcg : Eq Nat (bvar_ceiling (KExpr.proj s2 i2 sub2)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.proj s2 i2 sub2) (reduce_once env (KExpr.proj s2 i2 sub2))) (OptionType.some KExpr e2)) => reduce_app_lift_closed env (KExpr.proj s2 i2 sub2) a e2 hca (ihg hcg) h) ","(fun (v2 : Nat) (ihg : Eq Nat (bvar_ceiling (KExpr.lit v2)) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.lit v2)) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) (hcg : Eq Nat (bvar_ceiling (KExpr.lit v2)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.lit v2) (reduce_once env (KExpr.lit v2))) (OptionType.some KExpr e2)) => reduce_app_lift_closed env (KExpr.lit v2) a e2 hca (ihg hcg) h) ","f ihf hcf e2out hout) ","(nat_add_eq_zero_left (bvar_ceiling f) (bvar_ceiling a) hc) ","(nat_add_eq_zero_right (bvar_ceiling f) (bvar_ceiling a) hc)) ","(fun (ty : KExpr) (b : KExpr) ","(_i1 : Eq Nat (bvar_ceiling ty) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) ","(_i2 : Eq Nat (bvar_ceiling b) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) ","(_hc : Eq Nat (bvar_ceiling (KExpr.lam ty b)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.lam ty b)) (OptionType.some KExpr e2)) => ","option_none_ne_some KExpr e2 (Eq Nat (bvar_ceiling e2) Nat.zero) h) ","(fun (ty : KExpr) (b : KExpr) ","(_i1 : Eq Nat (bvar_ceiling ty) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) ","(_i2 : Eq Nat (bvar_ceiling b) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) ","(_hc : Eq Nat (bvar_ceiling (KExpr.pi ty b)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) (OptionType.some KExpr e2)) => ","option_none_ne_some KExpr e2 (Eq Nat (bvar_ceiling e2) Nat.zero) h) ","(fun (n : Name) (us : ListType Level) (_hc : Eq Nat (bvar_ceiling (KExpr.const n us)) Nat.zero) (e2 : KExpr) ","(h : Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) (OptionType.some KExpr e2)) => ","LiftP.rec (Eq Nat (bvar_ceiling e2) Nat.zero) ","(fun (_l : LiftP (Eq Nat (bvar_ceiling e2) Nat.zero)) => Eq Nat (bvar_ceiling e2) Nat.zero) ","(fun (p : Eq Nat (bvar_ceiling e2) Nat.zero) => p) ","(AndType.left (LiftP (Eq Nat (bvar_ceiling e2) Nat.zero)) (consts_defined env e2) (hEnv n e2 h))) ","(fun (ty : KExpr) (v : KExpr) (b : KExpr) ","(_i1 : Eq Nat (bvar_ceiling ty) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) ","(_i2 : Eq Nat (bvar_ceiling v) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env v) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) ","(_i3 : Eq Nat (bvar_ceiling b) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) ","(hc : Eq Nat (bvar_ceiling (KExpr.let_ ty v b)) Nat.zero) (e2 : KExpr) ","(h : Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) (OptionType.some KExpr e2)) => ","(fun (hb0 : Eq Nat (bvar_ceiling b) Nat.zero) => ","Eq.rec KExpr b ","(fun (x : KExpr) (_hx : Eq KExpr b x) => Eq Nat (bvar_ceiling x) Nat.zero) ","hb0 e2 ","(Eq.trans KExpr b (instantiate b v) e2 ","(Eq.symm KExpr (instantiate b v) b (inst_closed_id b v hb0)) ","(option_some_inj KExpr (instantiate b v) e2 h))) ","(nat_add_eq_zero_right (bvar_ceiling v) (bvar_ceiling b) ","(nat_add_eq_zero_right (bvar_ceiling ty) (Nat.add (bvar_ceiling v) (bvar_ceiling b)) hc))) ","(fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : Eq Nat (bvar_ceiling sub) Nat.zero -> forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr e3) -> Eq Nat (bvar_ceiling e3) Nat.zero) (hc : Eq Nat (bvar_ceiling (KExpr.proj s i sub)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.proj s i sub)) (OptionType.some KExpr e2)) => proj_lift_closed env s i sub e2 (ihsub hc) h) ","(fun (v : Nat) (_hc : Eq Nat (bvar_ceiling (KExpr.lit v)) Nat.zero) (e2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.lit v)) (OptionType.some KExpr e2)) => option_none_ne_some KExpr e2 (Eq Nat (bvar_ceiling e2) Nat.zero) h) ","e").to_string()),
            is_axiom: false,
            description: "CLOSEDNESS PRESERVATION (X16c-3a, round-4 guide \
                          reduceOnce_preserves_closed): one executable step out of a closed \
                          term stays closed over a good environment — β/ζ by the IDENTITY \
                          BRIDGE (substituting into a bvar-free body changes nothing), δ by \
                          the environment's closedness half, app-lift by the zero-sum \
                          combiner threaded through the inner head dispatch. DerivedProved, \
                          zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once".to_string(),
                "def_env_good".to_string(),
                "inst_closed_id".to_string(),
                "reduce_app_lift_closed".to_string(),
                "nat_add_eq_zero_left".to_string(),
                "nat_add_eq_zero_right".to_string(),
                "LiftP.rec".to_string(),
                "AndType.left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// X16c-2 — THE DIRECT EXECUTABLE-FIXPOINT CLASSIFICATION (round-4 guide,
    /// proved; the panel's reroute): a closed, fully-defined reduce_once
    /// fixpoint is a landed weak-head value or an honestly stuck application —
    /// NO relational no-step detour.
    fn add_reduce_once_classifies(&mut self) -> Result<(), SpecError> {
        // The stuck-head workhorse: a non-steppable, closed, defined head is
        // whnf_stuck_head — recursion on the head with the application
        // argument quantified INSIDE the motive (the argument changes at each
        // spine level).
        self.add_definition(SpecDefinition {
            name: "noredex_proj_class".to_string(),
            type_src: "forall (s : Name) (i : Nat) (sub : KExpr), whnf_noredex_class sub -> whnf_noredex_class (KExpr.proj s i sub)".to_string(),
            value_src: Some("fun (s : Name) (i : Nat) (sub : KExpr) (c : whnf_noredex_class sub) => whnf_noredex_class.rec (fun (e0 : KExpr) (_c0 : whnf_noredex_class e0) => whnf_noredex_class (KExpr.proj s i e0)) (fun (e0 : KExpr) (hw : is_whnf e0) => whnf_noredex_class.done (KExpr.proj s i e0) (is_whnf.proj s i e0 hw)) (fun (f : KExpr) (a : KExpr) (hs : whnf_stuck_head f) => whnf_noredex_class.stuck_proj s i (KExpr.app f a) (whnf_stuck_head.app f a hs)) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (hs : whnf_stuck_head sub2) => whnf_noredex_class.stuck_proj s i (KExpr.proj s2 i2 sub2) (whnf_stuck_head.proj s2 i2 sub2 hs)) sub c".to_string()),
            is_axiom: false,
            description: "PROJ CLASS CONGRUENCE (proj/lit rec-site migration, audit C1): the no-redex class lifts through a projection — a done scrutinee stays done (is_whnf.proj: this iota-free fragment has no proj-reduction), a stuck application or stuck projection scrutinee makes the projection honestly stuck_proj. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_noredex_class".to_string(),
                "whnf_noredex_class.rec".to_string(),
                "whnf_noredex_class.done".to_string(),
                "whnf_noredex_class.stuck_proj".to_string(),
                "whnf_stuck_head.app".to_string(),
                "whnf_stuck_head.proj".to_string(),
                "is_whnf.proj".to_string(),
                "KExpr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "noredex_proj_stuck".to_string(),
            type_src: "forall (s : Name) (i : Nat) (sub : KExpr), whnf_noredex_class sub -> whnf_stuck_head (KExpr.proj s i sub)".to_string(),
            value_src: Some("fun (s : Name) (i : Nat) (sub : KExpr) (c : whnf_noredex_class sub) => whnf_noredex_class.rec (fun (e0 : KExpr) (_c0 : whnf_noredex_class e0) => whnf_stuck_head (KExpr.proj s i e0)) (fun (e0 : KExpr) (hw : is_whnf e0) => whnf_stuck_head.projw s i e0 hw) (fun (f : KExpr) (a : KExpr) (hs : whnf_stuck_head f) => whnf_stuck_head.proj s i (KExpr.app f a) (whnf_stuck_head.app f a hs)) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (hs : whnf_stuck_head sub2) => whnf_stuck_head.proj s i (KExpr.proj s2 i2 sub2) (whnf_stuck_head.proj s2 i2 sub2 hs)) sub c".to_string()),
            is_axiom: false,
            description: "PROJ STUCK-HEAD CONVERSION (proj/lit rec-site migration, audit C1): a projection over a classified no-redex scrutinee is a stuck HEAD — done scrutinees via projw (a projection is never a lambda), stuck ones via the proj congruence. Feeds the app-over-proj-head stuck residual. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_noredex_class".to_string(),
                "whnf_noredex_class.rec".to_string(),
                "whnf_stuck_head.projw".to_string(),
                "whnf_stuck_head.proj".to_string(),
                "whnf_stuck_head.app".to_string(),
                "KExpr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "app_stuck_class_combined".to_string(),
            type_src: "forall (env : DefEnv) (e : KExpr), AndType (Eq (OptionType KExpr) (reduce_once env e) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> whnf_noredex_class e) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app e a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> whnf_stuck_head e)".to_string(),
            value_src: Some("fun (env : DefEnv) (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => AndType (Eq (OptionType KExpr) (reduce_once env e0) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling e0) Nat.zero -> consts_defined env e0 -> whnf_noredex_class e0) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app e0 a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling e0) Nat.zero -> consts_defined env e0 -> whnf_stuck_head e0)) (fun (n : Level) => AndType.intro (Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.sort n)) Nat.zero -> consts_defined env (KExpr.sort n) -> whnf_noredex_class (KExpr.sort n)) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.sort n) a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.sort n)) Nat.zero -> consts_defined env (KExpr.sort n) -> whnf_stuck_head (KExpr.sort n)) (fun (h : Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.sort n)) Nat.zero) (hd : consts_defined env (KExpr.sort n)) => whnf_noredex_class.done (KExpr.sort n) (is_whnf.sort n)) (fun (a2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.sort n) a2)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.sort n)) Nat.zero) (hd : consts_defined env (KExpr.sort n)) => whnf_stuck_head.sort n)) (fun (i : Nat) => AndType.intro (Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero -> consts_defined env (KExpr.bvar i) -> whnf_noredex_class (KExpr.bvar i)) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.bvar i) a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero -> consts_defined env (KExpr.bvar i) -> whnf_stuck_head (KExpr.bvar i)) (fun (h : Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero) (hd : consts_defined env (KExpr.bvar i)) => nat_zero_ne_succ i (whnf_noredex_class (KExpr.bvar i)) (Eq.symm Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero hc)) (fun (a2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.bvar i) a2)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero) (hd : consts_defined env (KExpr.bvar i)) => nat_zero_ne_succ i (whnf_stuck_head (KExpr.bvar i)) (Eq.symm Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero hc))) (fun (f : KExpr) (a : KExpr) (ihf : AndType (Eq (OptionType KExpr) (reduce_once env f) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling f) Nat.zero -> consts_defined env f -> whnf_noredex_class f) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app f a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling f) Nat.zero -> consts_defined env f -> whnf_stuck_head f)) (_iha : AndType (Eq (OptionType KExpr) (reduce_once env a) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling a) Nat.zero -> consts_defined env a -> whnf_noredex_class a) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app a a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling a) Nat.zero -> consts_defined env a -> whnf_stuck_head a)) => AndType.intro (Eq (OptionType KExpr) (reduce_once env (KExpr.app f a)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero -> consts_defined env (KExpr.app f a) -> whnf_noredex_class (KExpr.app f a)) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.app f a) a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero -> consts_defined env (KExpr.app f a) -> whnf_stuck_head (KExpr.app f a)) (fun (h : Eq (OptionType KExpr) (reduce_once env (KExpr.app f a)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) (hd : consts_defined env (KExpr.app f a)) => whnf_noredex_class.stuck f a (AndType.right (Eq (OptionType KExpr) (reduce_once env f) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling f) Nat.zero -> consts_defined env f -> whnf_noredex_class f) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app f a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling f) Nat.zero -> consts_defined env f -> whnf_stuck_head f) ihf a h (nat_add_eq_zero_left (bvar_ceiling f) (bvar_ceiling a) hc) (AndType.left (consts_defined env f) (consts_defined env a) hd))) (fun (a2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.app f a) a2)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) (hd : consts_defined env (KExpr.app f a)) => whnf_stuck_head.app f a (AndType.right (Eq (OptionType KExpr) (reduce_once env f) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling f) Nat.zero -> consts_defined env f -> whnf_noredex_class f) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app f a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling f) Nat.zero -> consts_defined env f -> whnf_stuck_head f) ihf a (reduce_app_none_inv env (KExpr.app f a) a2 h) (nat_add_eq_zero_left (bvar_ceiling f) (bvar_ceiling a) hc) (AndType.left (consts_defined env f) (consts_defined env a) hd)))) (fun (ty : KExpr) (b : KExpr) (_ity : AndType (Eq (OptionType KExpr) (reduce_once env ty) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> whnf_noredex_class ty) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app ty a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> whnf_stuck_head ty)) (_ib : AndType (Eq (OptionType KExpr) (reduce_once env b) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling b) Nat.zero -> consts_defined env b -> whnf_noredex_class b) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app b a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling b) Nat.zero -> consts_defined env b -> whnf_stuck_head b)) => AndType.intro (Eq (OptionType KExpr) (reduce_once env (KExpr.lam ty b)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.lam ty b)) Nat.zero -> consts_defined env (KExpr.lam ty b) -> whnf_noredex_class (KExpr.lam ty b)) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.lam ty b) a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.lam ty b)) Nat.zero -> consts_defined env (KExpr.lam ty b) -> whnf_stuck_head (KExpr.lam ty b)) (fun (h : Eq (OptionType KExpr) (reduce_once env (KExpr.lam ty b)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.lam ty b)) Nat.zero) (hd : consts_defined env (KExpr.lam ty b)) => whnf_noredex_class.done (KExpr.lam ty b) (is_whnf.lam ty b)) (fun (a2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.lam ty b) a2)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.lam ty b)) Nat.zero) (hd : consts_defined env (KExpr.lam ty b)) => opt_none_ne_some_t KExpr (instantiate b a2) (whnf_stuck_head (KExpr.lam ty b)) (Eq.symm (OptionType KExpr) (OptionType.some KExpr (instantiate b a2)) (OptionType.none KExpr) h))) (fun (ty : KExpr) (b : KExpr) (_ity : AndType (Eq (OptionType KExpr) (reduce_once env ty) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> whnf_noredex_class ty) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app ty a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> whnf_stuck_head ty)) (_ib : AndType (Eq (OptionType KExpr) (reduce_once env b) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling b) Nat.zero -> consts_defined env b -> whnf_noredex_class b) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app b a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling b) Nat.zero -> consts_defined env b -> whnf_stuck_head b)) => AndType.intro (Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.pi ty b)) Nat.zero -> consts_defined env (KExpr.pi ty b) -> whnf_noredex_class (KExpr.pi ty b)) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.pi ty b) a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.pi ty b)) Nat.zero -> consts_defined env (KExpr.pi ty b) -> whnf_stuck_head (KExpr.pi ty b)) (fun (h : Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.pi ty b)) Nat.zero) (hd : consts_defined env (KExpr.pi ty b)) => whnf_noredex_class.done (KExpr.pi ty b) (is_whnf.pi ty b)) (fun (a2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.pi ty b) a2)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.pi ty b)) Nat.zero) (hd : consts_defined env (KExpr.pi ty b)) => whnf_stuck_head.pi ty b)) (fun (n : Name) (us : ListType Level) => AndType.intro (Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.const n us)) Nat.zero -> consts_defined env (KExpr.const n us) -> whnf_noredex_class (KExpr.const n us)) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.const n us) a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.const n us)) Nat.zero -> consts_defined env (KExpr.const n us) -> whnf_stuck_head (KExpr.const n us)) (fun (h : Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.const n us)) Nat.zero) (hd : consts_defined env (KExpr.const n us)) => Empty.rec (fun (_e : Empty) => whnf_noredex_class (KExpr.const n us)) (Eq.rec (OptionType KExpr) (defval_for env n) (fun (o : OptionType KExpr) (_ho : Eq (OptionType KExpr) (defval_for env n) o) => opt_defined o) hd (OptionType.none KExpr) h)) (fun (a2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.const n us) a2)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.const n us)) Nat.zero) (hd : consts_defined env (KExpr.const n us)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (defval_for env n) o -> opt_defined o -> Eq (OptionType KExpr) (opt_app_lift a2 o) (OptionType.none KExpr) -> whnf_stuck_head (KExpr.const n us)) (fun (_heq : Eq (OptionType KExpr) (defval_for env n) (OptionType.none KExpr)) (hdo : Empty) (_h2 : Eq (OptionType KExpr) (opt_app_lift a2 (OptionType.none KExpr)) (OptionType.none KExpr)) => Empty.rec (fun (_e : Empty) => whnf_stuck_head (KExpr.const n us)) hdo) (fun (v : KExpr) (_heq : Eq (OptionType KExpr) (defval_for env n) (OptionType.some KExpr v)) (_hdo : ConstFreeUnit) (h2 : Eq (OptionType KExpr) (opt_app_lift a2 (OptionType.some KExpr v)) (OptionType.none KExpr)) => opt_none_ne_some_t KExpr (KExpr.app v a2) (whnf_stuck_head (KExpr.const n us)) (Eq.symm (OptionType KExpr) (opt_app_lift a2 (OptionType.some KExpr v)) (OptionType.none KExpr) h2)) (defval_for env n) (Eq.refl (OptionType KExpr) (defval_for env n)) hd h)) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_ity : AndType (Eq (OptionType KExpr) (reduce_once env ty) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> whnf_noredex_class ty) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app ty a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> whnf_stuck_head ty)) (_iv : AndType (Eq (OptionType KExpr) (reduce_once env v) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling v) Nat.zero -> consts_defined env v -> whnf_noredex_class v) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app v a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling v) Nat.zero -> consts_defined env v -> whnf_stuck_head v)) (_ib : AndType (Eq (OptionType KExpr) (reduce_once env b) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling b) Nat.zero -> consts_defined env b -> whnf_noredex_class b) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app b a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling b) Nat.zero -> consts_defined env b -> whnf_stuck_head b)) => AndType.intro (Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.let_ ty v b)) Nat.zero -> consts_defined env (KExpr.let_ ty v b) -> whnf_noredex_class (KExpr.let_ ty v b)) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.let_ ty v b) a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.let_ ty v b)) Nat.zero -> consts_defined env (KExpr.let_ ty v b) -> whnf_stuck_head (KExpr.let_ ty v b)) (fun (h : Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.let_ ty v b)) Nat.zero) (hd : consts_defined env (KExpr.let_ ty v b)) => opt_none_ne_some_t KExpr (instantiate b v) (whnf_noredex_class (KExpr.let_ ty v b)) (Eq.symm (OptionType KExpr) (OptionType.some KExpr (instantiate b v)) (OptionType.none KExpr) h)) (fun (a2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.let_ ty v b) a2)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.let_ ty v b)) Nat.zero) (hd : consts_defined env (KExpr.let_ ty v b)) => opt_none_ne_some_t KExpr (KExpr.app (instantiate b v) a2) (whnf_stuck_head (KExpr.let_ ty v b)) (Eq.symm (OptionType KExpr) (opt_app_lift a2 (OptionType.some KExpr (instantiate b v))) (OptionType.none KExpr) h))) (fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : AndType (Eq (OptionType KExpr) (reduce_once env sub) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling sub) Nat.zero -> consts_defined env sub -> whnf_noredex_class sub) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app sub a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling sub) Nat.zero -> consts_defined env sub -> whnf_stuck_head sub)) => AndType.intro (Eq (OptionType KExpr) (reduce_once env (KExpr.proj s i sub)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.proj s i sub)) Nat.zero -> consts_defined env (KExpr.proj s i sub) -> whnf_noredex_class (KExpr.proj s i sub)) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.proj s i sub) a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.proj s i sub)) Nat.zero -> consts_defined env (KExpr.proj s i sub) -> whnf_stuck_head (KExpr.proj s i sub)) (fun (h : Eq (OptionType KExpr) (reduce_once env (KExpr.proj s i sub)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.proj s i sub)) Nat.zero) (hd : consts_defined env (KExpr.proj s i sub)) => noredex_proj_class s i sub (AndType.left (Eq (OptionType KExpr) (reduce_once env sub) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling sub) Nat.zero -> consts_defined env sub -> whnf_noredex_class sub) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app sub a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling sub) Nat.zero -> consts_defined env sub -> whnf_stuck_head sub) ihsub (proj_lift_none_inv s i (reduce_once env sub) h) hc hd)) (fun (a2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.proj s i sub) a2)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.proj s i sub)) Nat.zero) (hd : consts_defined env (KExpr.proj s i sub)) => noredex_proj_stuck s i sub (AndType.left (Eq (OptionType KExpr) (reduce_once env sub) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling sub) Nat.zero -> consts_defined env sub -> whnf_noredex_class sub) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app sub a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling sub) Nat.zero -> consts_defined env sub -> whnf_stuck_head sub) ihsub (proj_lift_none_inv s i (reduce_once env sub) (reduce_app_none_inv env (KExpr.proj s i sub) a2 h)) hc hd))) (fun (v : Nat) => AndType.intro (Eq (OptionType KExpr) (reduce_once env (KExpr.lit v)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.lit v)) Nat.zero -> consts_defined env (KExpr.lit v) -> whnf_noredex_class (KExpr.lit v)) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.lit v) a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling (KExpr.lit v)) Nat.zero -> consts_defined env (KExpr.lit v) -> whnf_stuck_head (KExpr.lit v)) (fun (h : Eq (OptionType KExpr) (reduce_once env (KExpr.lit v)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.lit v)) Nat.zero) (hd : consts_defined env (KExpr.lit v)) => whnf_noredex_class.done (KExpr.lit v) (is_whnf.lit v)) (fun (a2 : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.app (KExpr.lit v) a2)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling (KExpr.lit v)) Nat.zero) (hd : consts_defined env (KExpr.lit v)) => whnf_stuck_head.lit v)) e".to_string()),
            is_axiom: false,
            description: "THE COMBINED FIXPOINT CLASSIFIER (proj/lit rec-site migration, audit C1): one KExpr induction proving BOTH the no-redex classification (P1: an executable fixpoint, closed and fully defined, is done-or-honestly-stuck) AND the stuck-head workhorse (P2: a head whose application cannot step is a whnf_stuck_head). The pairing is forced by the proj arm: classifying proj s i sub and stuck-ing a proj-headed application BOTH need the CLASS of the scrutinee, which the stuck-only motive cannot supply. app_head_stuck and reduce_once_none_classifies re-register as thin projections with unchanged statements. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr".to_string(),
                "KExpr.rec".to_string(),
                "AndType".to_string(),
                "AndType.intro".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "reduce_once".to_string(),
                "reduce_app_none_inv".to_string(),
                "proj_lift_none_inv".to_string(),
                "noredex_proj_class".to_string(),
                "noredex_proj_stuck".to_string(),
                "whnf_noredex_class.done".to_string(),
                "whnf_noredex_class.stuck".to_string(),
                "whnf_stuck_head.sort".to_string(),
                "whnf_stuck_head.pi".to_string(),
                "whnf_stuck_head.app".to_string(),
                "whnf_stuck_head.lit".to_string(),
                "is_whnf.sort".to_string(),
                "is_whnf.lam".to_string(),
                "is_whnf.pi".to_string(),
                "is_whnf.lit".to_string(),
                "opt_defined".to_string(),
                "opt_app_lift".to_string(),
                "opt_none_ne_some_t".to_string(),
                "nat_zero_ne_succ".to_string(),
                "nat_add_eq_zero_left".to_string(),
                "instantiate".to_string(),
                "defval_for".to_string(),
                "Empty.rec".to_string(),
                "Eq.rec".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "app_head_stuck".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (f : KExpr) (a : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env (KExpr.app f a)) (OptionType.none KExpr) -> ",
                "Eq Nat (bvar_ceiling f) Nat.zero -> consts_defined env f -> ",
                "whnf_stuck_head f"
            )
            .to_string(),
            value_src: Some("fun (env : DefEnv) (f : KExpr) (a : KExpr) (h : Eq (OptionType KExpr) (reduce_once env (KExpr.app f a)) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling f) Nat.zero) (hd : consts_defined env f) => AndType.right (Eq (OptionType KExpr) (reduce_once env f) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling f) Nat.zero -> consts_defined env f -> whnf_noredex_class f) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app f a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling f) Nat.zero -> consts_defined env f -> whnf_stuck_head f) (app_stuck_class_combined env f) a h hc hd".to_string()),
            is_axiom: false,
            description: "STUCK-HEAD WORKHORSE (X16c-2, round-4 guide appHead_stuck): a head \
                          whose application cannot execute a step, closed and fully defined, \
                          is honestly stuck — sort/pi stuck directly, lam/let/defined-const \
                          refute the executable none, bvar refutes closedness, and an app \
                          head recurses through the app-none extraction with the spine \
                          argument quantified in the motive. Since the proj/lit rec-site migration (audit C1) this is a thin projection of app_stuck_class_combined; the statement is unchanged. DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "app_stuck_class_combined".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "reduce_once".to_string(),
                "reduce_app_none_inv".to_string(),
                "whnf_stuck_head".to_string(),
                "opt_none_ne_some_t".to_string(),
                "opt_defined".to_string(),
                "nat_add_eq_zero_left".to_string(),
                "nat_zero_ne_succ".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // THE DIRECT CLASSIFICATION.
        self.add_definition(SpecDefinition {
            name: "reduce_once_none_classifies".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (e : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env e) (OptionType.none KExpr) -> ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> ",
                "whnf_noredex_class e"
            )
            .to_string(),
            value_src: Some("fun (env : DefEnv) (e : KExpr) (h : Eq (OptionType KExpr) (reduce_once env e) (OptionType.none KExpr)) (hc : Eq Nat (bvar_ceiling e) Nat.zero) (hd : consts_defined env e) => AndType.left (Eq (OptionType KExpr) (reduce_once env e) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> whnf_noredex_class e) (forall (a2 : KExpr), Eq (OptionType KExpr) (reduce_once env (KExpr.app e a2)) (OptionType.none KExpr) -> Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> whnf_stuck_head e) (app_stuck_class_combined env e) h hc hd".to_string()),
            is_axiom: false,
            description: "THE DIRECT EXECUTABLE-FIXPOINT CLASSIFICATION (X16c-2, round-4 \
                          guide reduceOnce_none_classifies — the fidelity panel's reroute): a \
                          closed, fully-defined reduce_once fixpoint is a landed is_whnf \
                          value or the honest stuck residual, WITHOUT any relational no-step \
                          hypothesis (which the full-congruence beta_reduces_bd makes \
                          unrealizable from an executable fixpoint). The const case is a \
                          single transport of the definedness witness along the lookup none \
                          into Empty. Since the proj/lit rec-site migration (audit C1) this is a thin projection of app_stuck_class_combined; the statement is unchanged. DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "app_stuck_class_combined".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
                "reduce_once".to_string(),
                "app_head_stuck".to_string(),
                "whnf_noredex_class".to_string(),
                "opt_defined".to_string(),
                "opt_none_ne_some_t".to_string(),
                "nat_add_eq_zero_left".to_string(),
                "nat_zero_ne_succ".to_string(),
                "Empty.rec".to_string(),
                "Eq.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// X16c-1 — THE CONVERSE CLUSTER (round-4 guide, proved): an executable
    /// `none` at the app head extracts to the head (`reduce_app_none_inv`), a
    /// δ-silent head keeps the whole application δ-silent (`delta_none_app` —
    /// the none-side of the spine correspondence), and the GRANULARITY
    /// CONVERSE: an executable fixpoint has no whole-spine δ to fire.
    fn add_reduce_once_converse(&mut self) -> Result<(), SpecError> {
        // Executable proj-lift none inversion: a silent lifted scrutinee was
        // itself silent (proj/lit rec-site migration, audit C1).
        self.add_definition(SpecDefinition {
            name: "proj_lift_none_inv".to_string(),
            type_src: concat!(
                "forall (s : Name) (i : Nat) (o : OptionType KExpr), ",
                "Eq (OptionType KExpr) (opt_proj_lift s i o) (OptionType.none KExpr) -> ",
                "Eq (OptionType KExpr) o (OptionType.none KExpr)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (s : Name) (i : Nat) (o : OptionType KExpr) => OptionType.rec KExpr ",
                    "(fun (o0 : OptionType KExpr) => Eq (OptionType KExpr) (opt_proj_lift s i o0) (OptionType.none KExpr) -> Eq (OptionType KExpr) o0 (OptionType.none KExpr)) ",
                    "(fun (_h : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.none KExpr)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ",
                    "(fun (v : KExpr) (h : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.some KExpr v)) (OptionType.none KExpr)) => ",
                    "option_none_ne_some KExpr (KExpr.proj s i v) (Eq (OptionType KExpr) (OptionType.some KExpr v) (OptionType.none KExpr)) ",
                    "(Eq.symm (OptionType KExpr) (opt_proj_lift s i (OptionType.some KExpr v)) (OptionType.none KExpr) h)) ",
                    "o"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "PROJ-LIFT NONE INVERSION (proj/lit rec-site migration, audit C1): \
                          opt_proj_lift s i o = none forces o = none — the some case relifts \
                          to a some and is refuted. DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "OptionType".to_string(),
                "OptionType.rec".to_string(),
                "opt_proj_lift".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.refl".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_app_none_inv".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (f : KExpr) (a : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env (KExpr.app f a)) (OptionType.none KExpr) -> ",
                "Eq (OptionType KExpr) (reduce_once env f) (OptionType.none KExpr)"
            )
            .to_string(),
            value_src: Some(concat!("fun (env : DefEnv) (f : KExpr) (a : KExpr) => KExpr.rec ","(fun (g : KExpr) => Eq (OptionType KExpr) (reduce_app_head a g (reduce_once env g)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env g) (OptionType.none KExpr)) ","(fun (n : Level) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.sort n) (reduce_once env (KExpr.sort n))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) o -> Eq (OptionType KExpr) (opt_app_lift a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once env (KExpr.sort n)) (Eq.refl (OptionType KExpr) (reduce_once env (KExpr.sort n))) h) ","(fun (i : Nat) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.bvar i) (reduce_once env (KExpr.bvar i))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) o -> Eq (OptionType KExpr) (opt_app_lift a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once env (KExpr.bvar i)) (Eq.refl (OptionType KExpr) (reduce_once env (KExpr.bvar i))) h) ","(fun (g1 : KExpr) (g2 : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_app_head a g1 (reduce_once env g1)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env g1) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_app_head a g2 (reduce_once env g2)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env g2) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.app g1 g2) (reduce_once env (KExpr.app g1 g2))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once env (KExpr.app g1 g2)) o -> Eq (OptionType KExpr) (opt_app_lift a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env (KExpr.app g1 g2)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once env (KExpr.app g1 g2)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once env (KExpr.app g1 g2)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once env (KExpr.app g1 g2)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once env (KExpr.app g1 g2)) (Eq.refl (OptionType KExpr) (reduce_once env (KExpr.app g1 g2))) h) ","(fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_app_head a ty (reduce_once env ty)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_app_head a b (reduce_once env b)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env b) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.lam ty b) (reduce_once env (KExpr.lam ty b))) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ","(fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_app_head a ty (reduce_once env ty)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_app_head a b (reduce_once env b)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env b) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.pi ty b) (reduce_once env (KExpr.pi ty b))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) o -> Eq (OptionType KExpr) (opt_app_lift a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once env (KExpr.pi ty b)) (Eq.refl (OptionType KExpr) (reduce_once env (KExpr.pi ty b))) h) ","(fun (n : Name) (us : ListType Level) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.const n us) (reduce_once env (KExpr.const n us))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) o -> Eq (OptionType KExpr) (opt_app_lift a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once env (KExpr.const n us)) (Eq.refl (OptionType KExpr) (reduce_once env (KExpr.const n us))) h) ","(fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_app_head a ty (reduce_once env ty)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_app_head a v (reduce_once env v)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env v) (OptionType.none KExpr)) (_i3 : Eq (OptionType KExpr) (reduce_app_head a b (reduce_once env b)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env b) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.let_ ty v b) (reduce_once env (KExpr.let_ ty v b))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) o -> Eq (OptionType KExpr) (opt_app_lift a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once env (KExpr.let_ ty v b)) (Eq.refl (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b))) h) ","(fun (s2 : Name) (i2 : Nat) (sub : KExpr) (_isub : Eq (OptionType KExpr) (reduce_app_head a sub (reduce_once env sub)) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env sub) (OptionType.none KExpr)) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.proj s2 i2 sub) (reduce_once env (KExpr.proj s2 i2 sub))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once env (KExpr.proj s2 i2 sub)) o -> Eq (OptionType KExpr) (opt_app_lift a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env (KExpr.proj s2 i2 sub)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once env (KExpr.proj s2 i2 sub)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once env (KExpr.proj s2 i2 sub)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once env (KExpr.proj s2 i2 sub)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once env (KExpr.proj s2 i2 sub)) (Eq.refl (OptionType KExpr) (reduce_once env (KExpr.proj s2 i2 sub))) h) ","(fun (v2 : Nat) (h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.lit v2) (reduce_once env (KExpr.lit v2))) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once env (KExpr.lit v2)) o -> Eq (OptionType KExpr) (opt_app_lift a o) (OptionType.none KExpr) -> Eq (OptionType KExpr) (reduce_once env (KExpr.lit v2)) (OptionType.none KExpr)) (fun (heq : Eq (OptionType KExpr) (reduce_once env (KExpr.lit v2)) (OptionType.none KExpr)) (_h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.none KExpr)) (OptionType.none KExpr)) => heq) (fun (f2 : KExpr) (_heq : Eq (OptionType KExpr) (reduce_once env (KExpr.lit v2)) (OptionType.some KExpr f2)) (h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr)) => option_none_ne_some KExpr (KExpr.app f2 a) (Eq (OptionType KExpr) (reduce_once env (KExpr.lit v2)) (OptionType.none KExpr)) (Eq.symm (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.none KExpr) h2)) (reduce_once env (KExpr.lit v2)) (Eq.refl (OptionType KExpr) (reduce_once env (KExpr.lit v2))) h) ","f").to_string()),
            is_axiom: false,
            description: "APP-NONE EXTRACTION (X16c-1): an executable none at an application \
                          extracts to the head — the lam head is impossible-free (its \
                          conclusion is definitional), every other head generalizes the \
                          head-reduct scrutinee (the none arm IS the conclusion, the some arm \
                          refutes the lifted some). DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once".to_string(),
                "reduce_app_head".to_string(),
                "opt_app_lift".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "delta_none_app".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (f : KExpr) (a : KExpr), ",
                "Eq (OptionType KExpr) (delta_reduct env f) (OptionType.none KExpr) -> ",
                "Eq (OptionType KExpr) (delta_reduct env (KExpr.app f a)) (OptionType.none KExpr)"
            )
            .to_string(),
            value_src: Some(concat!("fun (env : DefEnv) (f : KExpr) (a : KExpr) ","(hf : Eq (OptionType KExpr) (delta_reduct env f) (OptionType.none KExpr)) => ","OptionType.rec Name ","(fun (o1 : OptionType Name) => ","Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) o1 -> ","Eq (OptionType KExpr) (opt_bind Name KExpr o1 (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2)))) (OptionType.none KExpr) -> ","Eq (OptionType KExpr) (opt_bind Name KExpr o1 (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val2)))) (OptionType.none KExpr)) ","(fun (_h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.none Name)) ","(_hf2 : Eq (OptionType KExpr) (opt_bind Name KExpr (OptionType.none Name) (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2)))) (OptionType.none KExpr)) => ","Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ","(fun (dn : Name) ","(_h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name dn)) ","(hf2 : Eq (OptionType KExpr) (opt_bind Name KExpr (OptionType.some Name dn) (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2)))) (OptionType.none KExpr)) => ","OptionType.rec KExpr ","(fun (o2 : OptionType KExpr) => ","Eq (OptionType KExpr) (defval_for env dn) o2 -> ","Eq (OptionType KExpr) (opt_bind KExpr KExpr o2 (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2))) (OptionType.none KExpr) -> ","Eq (OptionType KExpr) (opt_bind KExpr KExpr o2 (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val2))) (OptionType.none KExpr)) ","(fun (_h2 : Eq (OptionType KExpr) (defval_for env dn) (OptionType.none KExpr)) ","(_hf3 : Eq (OptionType KExpr) (opt_bind KExpr KExpr (OptionType.none KExpr) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2))) (OptionType.none KExpr)) => ","Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ","(fun (val : KExpr) ","(_h2 : Eq (OptionType KExpr) (defval_for env dn) (OptionType.some KExpr val)) ","(hf3 : Eq (OptionType KExpr) (opt_bind KExpr KExpr (OptionType.some KExpr val) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2))) (OptionType.none KExpr)) => ","option_none_ne_some KExpr (apply_spine (kapp_args f) val) ","(Eq (OptionType KExpr) (opt_bind KExpr KExpr (OptionType.some KExpr val) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val2))) (OptionType.none KExpr)) ","(Eq.symm (OptionType KExpr) (opt_bind KExpr KExpr (OptionType.some KExpr val) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2))) (OptionType.none KExpr) hf3)) ","(defval_for env dn) (Eq.refl (OptionType KExpr) (defval_for env dn)) hf2) ","(kexpr_const_name (kapp_fn f)) ","(Eq.refl (OptionType Name) (kexpr_const_name (kapp_fn f))) hf").to_string()),
            is_axiom: false,
            description: "SPINE-δ CORRESPONDENCE, none side (X16c-1): a δ-silent head keeps \
                          the whole application δ-silent — the two lookup chains share every \
                          link (kapp_fn of an app is the head's spine head), so the only \
                          firing arm refutes the head's silence. Double scrutinee \
                          generalization. DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_reduct".to_string(),
                "defval_for".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_once_none_delta_none".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (e : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env e) (OptionType.none KExpr) -> ",
                "Eq (OptionType KExpr) (delta_reduct env e) (OptionType.none KExpr)"
            )
            .to_string(),
            value_src: Some(concat!("fun (env : DefEnv) (e : KExpr) => KExpr.rec ","(fun (e0 : KExpr) => Eq (OptionType KExpr) (reduce_once env e0) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct env e0) (OptionType.none KExpr)) ","(fun (n : Level) (_h : Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ","(fun (i : Nat) (_h : Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ","(fun (f : KExpr) (a : KExpr) ","(ihf : Eq (OptionType KExpr) (reduce_once env f) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct env f) (OptionType.none KExpr)) ","(_iha : Eq (OptionType KExpr) (reduce_once env a) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct env a) (OptionType.none KExpr)) ","(h : Eq (OptionType KExpr) (reduce_once env (KExpr.app f a)) (OptionType.none KExpr)) => ","delta_none_app env f a (ihf (reduce_app_none_inv env f a h))) ","(fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once env ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct env ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_once env b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct env b) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once env (KExpr.lam ty b)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ","(fun (ty : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once env ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct env ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_once env b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct env b) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ","(fun (n : Name) (us : ListType Level) ","(h : Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) (OptionType.none KExpr)) => ","Eq.rec (OptionType KExpr) (defval_for env n) ","(fun (o : OptionType KExpr) (_ho : Eq (OptionType KExpr) (defval_for env n) o) => ","Eq (OptionType KExpr) (delta_reduct env (KExpr.const n us)) (opt_bind KExpr KExpr o (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.const n us)) val2)))) ","(Eq.refl (OptionType KExpr) (delta_reduct env (KExpr.const n us))) ","(OptionType.none KExpr) h) ","(fun (ty : KExpr) (v : KExpr) (b : KExpr) (_i1 : Eq (OptionType KExpr) (reduce_once env ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct env ty) (OptionType.none KExpr)) (_i2 : Eq (OptionType KExpr) (reduce_once env v) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct env v) (OptionType.none KExpr)) (_i3 : Eq (OptionType KExpr) (reduce_once env b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct env b) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ","(fun (s2 : Name) (i2 : Nat) (sub : KExpr) (_isub : Eq (OptionType KExpr) (reduce_once env sub) (OptionType.none KExpr) -> Eq (OptionType KExpr) (delta_reduct env sub) (OptionType.none KExpr)) (_h : Eq (OptionType KExpr) (reduce_once env (KExpr.proj s2 i2 sub)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ","(fun (v : Nat) (_h : Eq (OptionType KExpr) (reduce_once env (KExpr.lit v)) (OptionType.none KExpr)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ","e").to_string()),
            is_axiom: false,
            description: "THE GRANULARITY CONVERSE (X16c-1, round-4 guide theorem \
                          reduceOnce_none_delta_none): if the executable step — bare-const δ \
                          + head recursion — finds nothing, the whole-spine δ has nothing to \
                          fire. KExpr induction: non-app/non-const heads are δ-silent \
                          definitionally, the const case transports the lookup none through \
                          the bind, the app case chains the head extraction, the IH, and the \
                          none-side correspondence. DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once".to_string(),
                "delta_reduct".to_string(),
                "reduce_app_none_inv".to_string(),
                "delta_none_app".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// X16c-0 — the GOOD-ENVIRONMENT predicate the loop-classification
    /// capstone threads: every bound definiens is closed (bvar-free, the
    /// ADD-based ceiling) AND itself fully defined. Cross-sort pair via
    /// LiftP (the ceiling Eq is Prop, consts_defined is Type). Identified as
    /// a registration gap by the round-4 fidelity audit.
    fn add_def_env_good(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def def_env_good (env : DefEnv) : Type := forall (n : Name) (v : KExpr), Eq (OptionType KExpr) (defval_for env n) (OptionType.some KExpr v) -> AndType (LiftP (Eq Nat (bvar_ceiling v) Nat.zero)) (consts_defined env v)",
            "def_env_good env: every definiens the environment binds is closed              (bvar_ceiling zero — the ADD-based ceiling, so literally bvar-free) and              itself consts-defined. The environment hypothesis the executable-loop              classification capstone threads through preservation. Part of the              WhnfLoop port (X16c-0).",
        )?;

        Ok(())
    }

    /// X16b corollary — the loop's reach, UNCONDITIONAL: the soundness
    /// hypothesis of whnf_fuel_reaches is now a theorem, so every successful
    /// loop result is reached by the δ-aware step star, full stop.
    fn add_whnf_fuel_reaches_sound(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "whnf_fuel_reaches_sound".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (fuel : Nat) (e : KExpr) (r : KExpr), ",
                "Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r) -> ",
                "env_step_star env e r"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (fuel : Nat) (e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r)) => ",
                    "whnf_fuel_reaches env fuel e r h ",
                    "(fun (a : KExpr) (b : KExpr) ",
                    "(hab : Eq (OptionType KExpr) (reduce_once env a) (OptionType.some KExpr b)) => ",
                    "reduce_once_sound env a b hab)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "UNCONDITIONAL REACH (X16b corollary): every successful whnf_fuel                           result is reached by the δ-aware step star — whnf_fuel_reaches with                           its soundness hypothesis DISCHARGED by reduce_once_sound. The loop's                           soundness path is now hypothesis-free. DerivedProved, zero                           axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel_reaches".to_string(),
                "reduce_once_sound".to_string(),
                "env_step_star".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// X16b — EXECUTABLE-STEP SOUNDNESS: every `some` result of `reduce_once`
    /// is a real `whnf_env_step`. The load-bearing new fact is the SPINE-δ
    /// CORRESPONDENCE: the appLeft-recursion reduct of a δ-fire coincides with
    /// `delta_reduct`'s whole-spine reduct (`apply_spine` over an appended
    /// argument = application of the shorter spine's value).
    fn add_reduce_once_sound(&mut self) -> Result<(), SpecError> {
        // The spine-append lemma — purely computational ListType induction
        // (both sides of the nil case compute to app v a; the cons case IS the
        // IH at the extended head).
        self.add_definition(SpecDefinition {
            name: "apply_spine_append_one".to_string(),
            type_src: concat!(
                "forall (xs : ListType KExpr) (a : KExpr) (v : KExpr), ",
                "Eq KExpr (apply_spine (list_append xs (ListType.cons KExpr a (ListType.nil KExpr))) v) ",
                "(KExpr.app (apply_spine xs v) a)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (xs : ListType KExpr) (a : KExpr) => ListType.rec KExpr ",
                    "(fun (l : ListType KExpr) => forall (v : KExpr), ",
                    "Eq KExpr (apply_spine (list_append l (ListType.cons KExpr a (ListType.nil KExpr))) v) ",
                    "(KExpr.app (apply_spine l v) a)) ",
                    "(fun (v : KExpr) => Eq.refl KExpr (KExpr.app v a)) ",
                    "(fun (x : KExpr) (rest : ListType KExpr) ",
                    "(ih : forall (v0 : KExpr), ",
                    "Eq KExpr (apply_spine (list_append rest (ListType.cons KExpr a (ListType.nil KExpr))) v0) ",
                    "(KExpr.app (apply_spine rest v0) a)) ",
                    "(v : KExpr) => ih (KExpr.app v x)) ",
                    "xs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "SPINE-APPEND (X16b): applying a spine extended by one argument =                           applying the shorter spine then the argument — by list induction                           generalizing the head; every case closes by computation.                           DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "apply_spine".to_string(),
                "list_append".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // THE SPINE-δ CORRESPONDENCE: a δ-firing head lifts to a δ-fire of the
        // whole application, with reduct exactly (app f2 a) — double scrutinee
        // generalization over the lookup chain, the two X13b transports over
        // the app-form continuation, and the spine-append rewrite.
        self.add_definition(SpecDefinition {
            name: "delta_lift_app".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (f : KExpr) (a : KExpr) (f2 : KExpr), ",
                "Eq (OptionType KExpr) (delta_reduct env f) (OptionType.some KExpr f2) -> ",
                "Eq (OptionType KExpr) (delta_reduct env (KExpr.app f a)) (OptionType.some KExpr (KExpr.app f2 a))"
            )
            .to_string(),
            value_src: Some(DELTA_LIFT_VALUE.to_string()),
            is_axiom: false,
            description: "SPINE-δ CORRESPONDENCE (X16b): if the head δ-fires to f2 then the                           application δ-fires to (app f2 a) — kapp_fn of an app is the head's                           spine head definitionally, so the same name/value lookups drive both;                           the reducts align by the spine-append lemma. Double scrutinee                           generalization + chained transports + some-congruence. DerivedProved,                           zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_reduct".to_string(),
                "apply_spine_append_one".to_string(),
                "option_some_inj".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.trans".to_string(),
                "Eq.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Soundness of the app-lift path: every sound head reduct lifts
        // directly through the application congruence, independent of which
        // whnf_env_step constructor produced it.
        self.add_definition(SpecDefinition {
            name: "reduce_app_lift_sound".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (f : KExpr) (a : KExpr) (e2 : KExpr), ",
                "(forall (e3 : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr e3) -> ",
                "whnf_env_step env f e3) -> ",
                "Eq (OptionType KExpr) (opt_app_lift a (reduce_once env f)) (OptionType.some KExpr e2) -> ",
                "whnf_env_step env (KExpr.app f a) e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (f : KExpr) (a : KExpr) (e2 : KExpr) ",
                    "(ih : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env f e3) ",
                    "(h : Eq (OptionType KExpr) (opt_app_lift a (reduce_once env f)) (OptionType.some KExpr e2)) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (reduce_once env f) o -> ",
                    "Eq (OptionType KExpr) (opt_app_lift a o) (OptionType.some KExpr e2) -> ",
                    "whnf_env_step env (KExpr.app f a) e2) ",
                    "(fun (_heq : Eq (OptionType KExpr) (reduce_once env f) (OptionType.none KExpr)) ",
                    "(h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.none KExpr)) (OptionType.some KExpr e2)) => ",
                    "opt_none_ne_some_t KExpr e2 (whnf_env_step env (KExpr.app f a) e2) h2) ",
                    "(fun (f2 : KExpr) ",
                    "(heq : Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr f2)) ",
                    "(h2 : Eq (OptionType KExpr) (opt_app_lift a (OptionType.some KExpr f2)) (OptionType.some KExpr e2)) => ",
                    "Eq.rec KExpr (KExpr.app f2 a) ",
                    "(fun (x : KExpr) (_hx : Eq KExpr (KExpr.app f2 a) x) => ",
                    "whnf_env_step env (KExpr.app f a) x) ",
                    "(whnf_env_step.app_left env f f2 a (ih f2 heq)) ",
                    "e2 (option_some_inj KExpr (KExpr.app f2 a) e2 h2)) ",
                    "(reduce_once env f) (Eq.refl (OptionType KExpr) (reduce_once env f)) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "APP-LIFT SOUNDNESS (X16b): every sound head reduct lifts directly                           through whnf_env_step.app_left; the lifted target transports along                           some-injectivity. Constructor-agnostic in the head step, including                           projection congruence. DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_app_lift".to_string(),
                "reduce_once".to_string(),
                "whnf_env_step.app_left".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // THE SOUNDNESS THEOREM: every some-result of the executable step is a
        // real δ-aware weak-head step.
        // The proj-scrutinee lift soundness: a some through the executable proj
        // lift is exactly one whnf_env_step.proj congruence step on the
        // scrutinee (proj/lit rec-site migration, audit C1).
        self.add_definition(SpecDefinition {
            name: "reduce_proj_lift_sound".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr), ",
                "(forall (e3 : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr e3) -> ",
                "whnf_env_step env sub e3) -> ",
                "Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once env sub)) (OptionType.some KExpr e2) -> ",
                "whnf_env_step env (KExpr.proj s i sub) e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (s : Name) (i : Nat) (sub : KExpr) (e2 : KExpr) ",
                    "(ih : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr e3) -> whnf_env_step env sub e3) ",
                    "(h : Eq (OptionType KExpr) (opt_proj_lift s i (reduce_once env sub)) (OptionType.some KExpr e2)) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (reduce_once env sub) o -> ",
                    "Eq (OptionType KExpr) (opt_proj_lift s i o) (OptionType.some KExpr e2) -> ",
                    "whnf_env_step env (KExpr.proj s i sub) e2) ",
                    "(fun (_heq : Eq (OptionType KExpr) (reduce_once env sub) (OptionType.none KExpr)) ",
                    "(h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.none KExpr)) (OptionType.some KExpr e2)) => ",
                    "opt_none_ne_some_t KExpr e2 (whnf_env_step env (KExpr.proj s i sub) e2) h2) ",
                    "(fun (sub2 : KExpr) ",
                    "(heq : Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr sub2)) ",
                    "(h2 : Eq (OptionType KExpr) (opt_proj_lift s i (OptionType.some KExpr sub2)) (OptionType.some KExpr e2)) => ",
                    "Eq.rec KExpr (KExpr.proj s i sub2) ",
                    "(fun (x : KExpr) (_hx : Eq KExpr (KExpr.proj s i sub2) x) => ",
                    "whnf_env_step env (KExpr.proj s i sub) x) ",
                    "(whnf_env_step.proj env s i sub sub2 (ih sub2 heq)) ",
                    "e2 (option_some_inj KExpr (KExpr.proj s i sub2) e2 h2)) ",
                    "(reduce_once env sub) (Eq.refl (OptionType KExpr) (reduce_once env sub)) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "PROJ-LIFT SOUNDNESS (proj/lit rec-site migration, audit C1): a some \
                          through the executable proj lift is exactly one whnf_env_step.proj \
                          congruence step on the scrutinee — the proj analogue of \
                          reduce_app_lift_sound. DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr".to_string(),
                "OptionType".to_string(),
                "OptionType.rec".to_string(),
                "opt_proj_lift".to_string(),
                "reduce_once".to_string(),
                "whnf_env_step".to_string(),
                "whnf_env_step.proj".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "reduce_once_sound".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (e : KExpr) (e2 : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env e) (OptionType.some KExpr e2) -> ",
                "whnf_env_step env e e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (e : KExpr) => KExpr.rec ",
                    "(fun (e0 : KExpr) => forall (e2 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env e0) (OptionType.some KExpr e2) -> ",
                    "whnf_env_step env e0 e2) ",
                    "(fun (n : Level) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) (OptionType.some KExpr e2)) => ",
                    "opt_none_ne_some_t KExpr e2 (whnf_env_step env (KExpr.sort n) e2) h) ",
                    "(fun (i : Nat) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) (OptionType.some KExpr e2)) => ",
                    "opt_none_ne_some_t KExpr e2 (whnf_env_step env (KExpr.bvar i) e2) h) ",
                    "(fun (f : KExpr) (a : KExpr) ",
                    "(ihf : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env f) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env f e3) ",
                    "(_iha : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env a) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env a e3) => ",
                    "KExpr.rec ",
                    "(fun (g : KExpr) => ",
                    "(forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env g) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env g e3) -> ",
                    "forall (e2 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_app_head a g (reduce_once env g)) (OptionType.some KExpr e2) -> ",
                    "whnf_env_step env (KExpr.app g a) e2) ",
                    "(fun (n : Level) (ihg : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env (KExpr.sort n)) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env (KExpr.sort n) e3) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.sort n) (reduce_once env (KExpr.sort n))) (OptionType.some KExpr e2)) => ",
                    "reduce_app_lift_sound env (KExpr.sort n) a e2 ihg h) ",
                    "(fun (i : Nat) (ihg : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env (KExpr.bvar i)) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env (KExpr.bvar i) e3) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.bvar i) (reduce_once env (KExpr.bvar i))) (OptionType.some KExpr e2)) => ",
                    "reduce_app_lift_sound env (KExpr.bvar i) a e2 ihg h) ",
                    "(fun (g1 : KExpr) (g2 : KExpr) ",
                    "(_ihg1 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env g1) (OptionType.some KExpr e3) -> whnf_env_step env g1 e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a g1 (reduce_once env g1)) (OptionType.some KExpr e4) -> whnf_env_step env (KExpr.app g1 a) e4) ",
                    "(_ihg2 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env g2) (OptionType.some KExpr e3) -> whnf_env_step env g2 e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a g2 (reduce_once env g2)) (OptionType.some KExpr e4) -> whnf_env_step env (KExpr.app g2 a) e4) ",
                    "(ihg : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env (KExpr.app g1 g2)) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env (KExpr.app g1 g2) e3) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.app g1 g2) (reduce_once env (KExpr.app g1 g2))) (OptionType.some KExpr e2)) => ",
                    "reduce_app_lift_sound env (KExpr.app g1 g2) a e2 ihg h) ",
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(_i1 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> whnf_env_step env ty e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a ty (reduce_once env ty)) (OptionType.some KExpr e4) -> whnf_env_step env (KExpr.app ty a) e4) ",
                    "(_i2 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> whnf_env_step env b e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a b (reduce_once env b)) (OptionType.some KExpr e4) -> whnf_env_step env (KExpr.app b a) e4) ",
                    "(_ihg : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env (KExpr.lam ty b)) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env (KExpr.lam ty b) e3) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.lam ty b) (reduce_once env (KExpr.lam ty b))) (OptionType.some KExpr e2)) => ",
                    "Eq.rec KExpr (instantiate b a) ",
                    "(fun (x : KExpr) (_hx : Eq KExpr (instantiate b a) x) => ",
                    "whnf_env_step env (KExpr.app (KExpr.lam ty b) a) x) ",
                    "(whnf_env_step.beta env (KExpr.app (KExpr.lam ty b) a) (instantiate b a) ",
                    "(beta_reduces_bd.beta ty b a)) ",
                    "e2 (option_some_inj KExpr (instantiate b a) e2 h)) ",
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(_i1 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> whnf_env_step env ty e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a ty (reduce_once env ty)) (OptionType.some KExpr e4) -> whnf_env_step env (KExpr.app ty a) e4) ",
                    "(_i2 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> whnf_env_step env b e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a b (reduce_once env b)) (OptionType.some KExpr e4) -> whnf_env_step env (KExpr.app b a) e4) ",
                    "(ihg : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env (KExpr.pi ty b) e3) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.pi ty b) (reduce_once env (KExpr.pi ty b))) (OptionType.some KExpr e2)) => ",
                    "reduce_app_lift_sound env (KExpr.pi ty b) a e2 ihg h) ",
                    "(fun (n : Name) (us : ListType Level) ",
                    "(ihg : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env (KExpr.const n us) e3) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.const n us) (reduce_once env (KExpr.const n us))) (OptionType.some KExpr e2)) => ",
                    "reduce_app_lift_sound env (KExpr.const n us) a e2 ihg h) ",
                    "(fun (ty : KExpr) (v : KExpr) (b : KExpr) ",
                    "(_i1 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> whnf_env_step env ty e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a ty (reduce_once env ty)) (OptionType.some KExpr e4) -> whnf_env_step env (KExpr.app ty a) e4) ",
                    "(_i2 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env v) (OptionType.some KExpr e3) -> whnf_env_step env v e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a v (reduce_once env v)) (OptionType.some KExpr e4) -> whnf_env_step env (KExpr.app v a) e4) ",
                    "(_i3 : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> whnf_env_step env b e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a b (reduce_once env b)) (OptionType.some KExpr e4) -> whnf_env_step env (KExpr.app b a) e4) ",
                    "(ihg : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env (KExpr.let_ ty v b) e3) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.let_ ty v b) (reduce_once env (KExpr.let_ ty v b))) (OptionType.some KExpr e2)) => ",
                    "reduce_app_lift_sound env (KExpr.let_ ty v b) a e2 ihg h) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(_ihsub : (forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr e3) -> whnf_env_step env sub e3) -> forall (e4 : KExpr), Eq (OptionType KExpr) (reduce_app_head a sub (reduce_once env sub)) (OptionType.some KExpr e4) -> whnf_env_step env (KExpr.app sub a) e4) ",
                    "(ihg : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env (KExpr.proj s i sub)) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env (KExpr.proj s i sub) e3) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.proj s i sub) (reduce_once env (KExpr.proj s i sub))) (OptionType.some KExpr e2)) => ",
                    "reduce_app_lift_sound env (KExpr.proj s i sub) a e2 ihg h) ",
                    "(fun (v : Nat) ",
                    "(ihg : forall (e3 : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env (KExpr.lit v)) (OptionType.some KExpr e3) -> ",
                    "whnf_env_step env (KExpr.lit v) e3) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_app_head a (KExpr.lit v) (reduce_once env (KExpr.lit v))) (OptionType.some KExpr e2)) => ",
                    "reduce_app_lift_sound env (KExpr.lit v) a e2 ihg h) ",
                    "f ihf) ",
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(_ihty : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> whnf_env_step env ty e3) ",
                    "(_ihb : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> whnf_env_step env b e3) ",
                    "(e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_once env (KExpr.lam ty b)) (OptionType.some KExpr e2)) => ",
                    "opt_none_ne_some_t KExpr e2 (whnf_env_step env (KExpr.lam ty b) e2) h) ",
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(_ihty : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> whnf_env_step env ty e3) ",
                    "(_ihb : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> whnf_env_step env b e3) ",
                    "(e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_once env (KExpr.pi ty b)) (OptionType.some KExpr e2)) => ",
                    "opt_none_ne_some_t KExpr e2 (whnf_env_step env (KExpr.pi ty b) e2) h) ",
                    "(fun (n : Name) (us : ListType Level) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_once env (KExpr.const n us)) (OptionType.some KExpr e2)) => ",
                    "const_delta_fires env n us e2 h) ",
                    "(fun (ty : KExpr) (v : KExpr) (b : KExpr) ",
                    "(_i1 : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env ty) (OptionType.some KExpr e3) -> whnf_env_step env ty e3) ",
                    "(_i2 : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env v) (OptionType.some KExpr e3) -> whnf_env_step env v e3) ",
                    "(_i3 : forall (e3 : KExpr), Eq (OptionType KExpr) (reduce_once env b) (OptionType.some KExpr e3) -> whnf_env_step env b e3) ",
                    "(e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_once env (KExpr.let_ ty v b)) (OptionType.some KExpr e2)) => ",
                    "Eq.rec KExpr (instantiate b v) ",
                    "(fun (x : KExpr) (_hx : Eq KExpr (instantiate b v) x) => ",
                    "whnf_env_step env (KExpr.let_ ty v b) x) ",
                    "(whnf_env_step.beta env (KExpr.let_ ty v b) (instantiate b v) ",
                    "(beta_reduces_bd.zeta ty v b)) ",
                    "e2 (option_some_inj KExpr (instantiate b v) e2 h)) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(ihsub : forall (sub2 : KExpr), Eq (OptionType KExpr) (reduce_once env sub) (OptionType.some KExpr sub2) -> whnf_env_step env sub sub2) ",
                    "(e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_once env (KExpr.proj s i sub)) (OptionType.some KExpr e2)) => ",
                    "reduce_proj_lift_sound env s i sub e2 ihsub h) ",
                    "(fun (v : Nat) (e2 : KExpr) ",
                    "(h : Eq (OptionType KExpr) (reduce_once env (KExpr.lit v)) (OptionType.some KExpr e2)) => ",
                    "opt_none_ne_some_t KExpr e2 (whnf_env_step env (KExpr.lit v) e2) h) ",
                    "e"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "EXECUTABLE-STEP SOUNDNESS (X16b, proved guide theorem                           reduceOnce_sound): every some-result of reduce_once is a real                           whnf_env_step — current nine-constructor KExpr induction with an inner                           head dispatch; lam β-fires, const uses X12 δ-liveness, let ζ-fires,                           projection lifts the scrutinee step, literal is a fixpoint, and every                           non-lam application head routes through app_left. DerivedProved, zero                           axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "reduce_once".to_string(),
                "reduce_app_head".to_string(),
                "reduce_app_lift_sound".to_string(),
                "opt_proj_lift".to_string(),
                "reduce_proj_lift_sound".to_string(),
                "const_delta_fires".to_string(),
                "whnf_env_step".to_string(),
                "whnf_env_step.proj".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// X16a part 2 — the loop THEOREMS (ports of the proved WhnfLoop guide):
    /// star-prepend, fixpoint-only returns, fuel monotonicity, and the sound
    /// reach (with step-soundness as a hypothesis, exactly as the guide).
    fn add_whnf_fuel_theorems(&mut self) -> Result<(), SpecError> {
        // Prepend one step to a star (the guide's StepStar.head).
        self.add_definition(SpecDefinition {
            name: "env_step_star_head".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (a : KExpr) (b : KExpr) (c : KExpr), ",
                "whnf_env_step env a b -> env_step_star env b c -> env_step_star env a c"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (a : KExpr) (b : KExpr) (c : KExpr) ",
                    "(hab : whnf_env_step env a b) (hbc : env_step_star env b c) => ",
                    "env_step_star.rec env b ",
                    "(fun (y : KExpr) (_st : env_step_star env b y) => ",
                    "whnf_env_step env a b -> env_step_star env a y) ",
                    "(fun (hab2 : whnf_env_step env a b) => ",
                    "env_step_star.tail env a a b (env_step_star.refl env a) hab2) ",
                    "(fun (x : KExpr) (y : KExpr) ",
                    "(hbx : env_step_star env b x) (hxy : whnf_env_step env x y) ",
                    "(ihx : whnf_env_step env a b -> env_step_star env a x) ",
                    "(hab2 : whnf_env_step env a b) => ",
                    "env_step_star.tail env a x y (ihx hab2) hxy) ",
                    "c hbc hab"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Star-prepend (WhnfLoop port X16a): one whnf_env_step followed by a                           star is a star — by the star recursor with a step-consuming motive.                           DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "env_step_star".to_string(),
                "env_step_star.rec".to_string(),
                "whnf_env_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // FIXPOINT-ONLY RETURNS: a successful loop result has no reduce_once
        // reduct — the loop only exits at the fixpoint (or bails honestly).
        self.add_definition(SpecDefinition {
            name: "whnf_fuel_no_redex".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (fuel : Nat) (e : KExpr) (r : KExpr), ",
                "Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r) -> ",
                "Eq (OptionType KExpr) (reduce_once env r) (OptionType.none KExpr)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (fuel : Nat) => Nat.rec ",
                    "(fun (k : Nat) => forall (e : KExpr) (r : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel env k e) (OptionType.some KExpr r) -> ",
                    "Eq (OptionType KExpr) (reduce_once env r) (OptionType.none KExpr)) ",
                    "(fun (e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel env Nat.zero e) (OptionType.some KExpr r)) => ",
                    "option_none_ne_some KExpr r ",
                    "(Eq (OptionType KExpr) (reduce_once env r) (OptionType.none KExpr)) h) ",
                    "(fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel env k e0) (OptionType.some KExpr r0) -> ",
                    "Eq (OptionType KExpr) (reduce_once env r0) (OptionType.none KExpr)) ",
                    "(e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel env (Nat.succ k) e) (OptionType.some KExpr r)) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (reduce_once env e) o -> ",
                    "Eq (OptionType KExpr) (loop_dispatch o e (fun (e2 : KExpr) => whnf_fuel env k e2)) (OptionType.some KExpr r) -> ",
                    "Eq (OptionType KExpr) (reduce_once env r) (OptionType.none KExpr)) ",
                    "(fun (heq : Eq (OptionType KExpr) (reduce_once env e) (OptionType.none KExpr)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e (fun (e2 : KExpr) => whnf_fuel env k e2)) (OptionType.some KExpr r)) => ",
                    "Eq.rec KExpr e ",
                    "(fun (x : KExpr) (_hx : Eq KExpr e x) => ",
                    "Eq (OptionType KExpr) (reduce_once env x) (OptionType.none KExpr)) ",
                    "heq r (option_some_inj KExpr e r h2)) ",
                    "(fun (e2 : KExpr) ",
                    "(_heq : Eq (OptionType KExpr) (reduce_once env e) (OptionType.some KExpr e2)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.some KExpr e2) e (fun (e3 : KExpr) => whnf_fuel env k e3)) (OptionType.some KExpr r)) => ",
                    "ih e2 r h2) ",
                    "(reduce_once env e) (Eq.refl (OptionType KExpr) (reduce_once env e)) h) ",
                    "fuel"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "FIXPOINT-ONLY RETURNS (WhnfLoop port X16a, proved guide theorem                           whnfFuel_no_redex): a successful whnf_fuel result has NO reduce_once                           reduct — by fuel induction with the scrutinee-generalized loop                           dispatch; the none arm transports the fixpoint equation along                           some-injectivity, the some arm recurses. DerivedProved, zero                           axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel".to_string(),
                "reduce_once".to_string(),
                "loop_dispatch".to_string(),
                "option_some_inj".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // FUEL MONOTONICITY: extra fuel never changes a successful answer.
        self.add_definition(SpecDefinition {
            name: "whnf_fuel_monotone".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (fuel : Nat) (e : KExpr) (r : KExpr), ",
                "Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r) -> ",
                "Eq (OptionType KExpr) (whnf_fuel env (Nat.succ fuel) e) (OptionType.some KExpr r)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (fuel : Nat) => Nat.rec ",
                    "(fun (k : Nat) => forall (e : KExpr) (r : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel env k e) (OptionType.some KExpr r) -> ",
                    "Eq (OptionType KExpr) (whnf_fuel env (Nat.succ k) e) (OptionType.some KExpr r)) ",
                    "(fun (e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel env Nat.zero e) (OptionType.some KExpr r)) => ",
                    "option_none_ne_some KExpr r ",
                    "(Eq (OptionType KExpr) (whnf_fuel env (Nat.succ Nat.zero) e) (OptionType.some KExpr r)) h) ",
                    "(fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel env k e0) (OptionType.some KExpr r0) -> ",
                    "Eq (OptionType KExpr) (whnf_fuel env (Nat.succ k) e0) (OptionType.some KExpr r0)) ",
                    "(e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel env (Nat.succ k) e) (OptionType.some KExpr r)) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (reduce_once env e) o -> ",
                    "Eq (OptionType KExpr) (loop_dispatch o e (fun (e2 : KExpr) => whnf_fuel env k e2)) (OptionType.some KExpr r) -> ",
                    "Eq (OptionType KExpr) (loop_dispatch o e (fun (e2 : KExpr) => whnf_fuel env (Nat.succ k) e2)) (OptionType.some KExpr r)) ",
                    "(fun (_heq : Eq (OptionType KExpr) (reduce_once env e) (OptionType.none KExpr)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e (fun (e2 : KExpr) => whnf_fuel env k e2)) (OptionType.some KExpr r)) => ",
                    "h2) ",
                    "(fun (e2 : KExpr) ",
                    "(_heq : Eq (OptionType KExpr) (reduce_once env e) (OptionType.some KExpr e2)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.some KExpr e2) e (fun (e3 : KExpr) => whnf_fuel env k e3)) (OptionType.some KExpr r)) => ",
                    "ih e2 r h2) ",
                    "(reduce_once env e) (Eq.refl (OptionType KExpr) (reduce_once env e)) h) ",
                    "fuel"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "FUEL MONOTONICITY (WhnfLoop port X16a, proved guide theorem                           whnfFuel_monotone): ONE extra unit of fuel never changes a successful loop                           answer (the general fuel-prime >= fuel form follows by iteration                           and is not registered) — the none arm's fixpoint return is fuel-independent (the                           two dispatch types are definitionally the SAME Eq), the some arm                           recurses. DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel".to_string(),
                "reduce_once".to_string(),
                "loop_dispatch".to_string(),
                "option_none_ne_some".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // SOUND REACH: with step-soundness as a hypothesis (exactly as the
        // proved guide takes it), every successful result is reached by the
        // δ-aware step star.
        self.add_definition(SpecDefinition {
            name: "whnf_fuel_reaches".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (fuel : Nat) (e : KExpr) (r : KExpr), ",
                "Eq (OptionType KExpr) (whnf_fuel env fuel e) (OptionType.some KExpr r) -> ",
                "(forall (a : KExpr) (b : KExpr), ",
                "Eq (OptionType KExpr) (reduce_once env a) (OptionType.some KExpr b) -> ",
                "whnf_env_step env a b) -> ",
                "env_step_star env e r"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (fuel : Nat) => Nat.rec ",
                    "(fun (k : Nat) => forall (e : KExpr) (r : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel env k e) (OptionType.some KExpr r) -> ",
                    "(forall (a : KExpr) (b : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env a) (OptionType.some KExpr b) -> ",
                    "whnf_env_step env a b) -> ",
                    "env_step_star env e r) ",
                    "(fun (e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel env Nat.zero e) (OptionType.some KExpr r)) ",
                    "(_hs : forall (a : KExpr) (b : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env a) (OptionType.some KExpr b) -> ",
                    "whnf_env_step env a b) => ",
                    "opt_none_ne_some_t KExpr r (env_step_star env e r) h) ",
                    "(fun (k : Nat) (ih : forall (e0 : KExpr) (r0 : KExpr), ",
                    "Eq (OptionType KExpr) (whnf_fuel env k e0) (OptionType.some KExpr r0) -> ",
                    "(forall (a : KExpr) (b : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env a) (OptionType.some KExpr b) -> ",
                    "whnf_env_step env a b) -> ",
                    "env_step_star env e0 r0) ",
                    "(e : KExpr) (r : KExpr) ",
                    "(h : Eq (OptionType KExpr) (whnf_fuel env (Nat.succ k) e) (OptionType.some KExpr r)) ",
                    "(hs : forall (a : KExpr) (b : KExpr), ",
                    "Eq (OptionType KExpr) (reduce_once env a) (OptionType.some KExpr b) -> ",
                    "whnf_env_step env a b) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (reduce_once env e) o -> ",
                    "Eq (OptionType KExpr) (loop_dispatch o e (fun (e2 : KExpr) => whnf_fuel env k e2)) (OptionType.some KExpr r) -> ",
                    "env_step_star env e r) ",
                    "(fun (_heq : Eq (OptionType KExpr) (reduce_once env e) (OptionType.none KExpr)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.none KExpr) e (fun (e2 : KExpr) => whnf_fuel env k e2)) (OptionType.some KExpr r)) => ",
                    "Eq.rec KExpr e ",
                    "(fun (x : KExpr) (_hx : Eq KExpr e x) => env_step_star env e x) ",
                    "(env_step_star.refl env e) r (option_some_inj KExpr e r h2)) ",
                    "(fun (e2 : KExpr) ",
                    "(heq : Eq (OptionType KExpr) (reduce_once env e) (OptionType.some KExpr e2)) ",
                    "(h2 : Eq (OptionType KExpr) (loop_dispatch (OptionType.some KExpr e2) e (fun (e3 : KExpr) => whnf_fuel env k e3)) (OptionType.some KExpr r)) => ",
                    "env_step_star_head env e e2 r (hs e e2 heq) (ih e2 r h2 hs)) ",
                    "(reduce_once env e) (Eq.refl (OptionType KExpr) (reduce_once env e)) h) ",
                    "fuel"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "SOUND REACH (WhnfLoop port X16a, proved guide theorem                           whnfFuel_reaches): with reduce_once-soundness as a hypothesis                           (exactly the guide's hsound), every successful loop result is                           reached by the δ-aware step star — fuel induction; the fixpoint                           arm transports refl along some-injectivity, the step arm prepends                           the sound step. DerivedProved, zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_fuel".to_string(),
                "reduce_once".to_string(),
                "loop_dispatch".to_string(),
                "env_step_star".to_string(),
                "env_step_star_head".to_string(),
                "opt_none_ne_some_t".to_string(),
                "option_some_inj".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// X16a — THE EXECUTABLE LOOP PORT (WhnfLoop guide, proved round 1): a
    /// kernel-computable single weak-head step `reduce_once` (β at a lam-headed
    /// app, ζ at let, δ at a bare const, application-head/projection-scrutinee
    /// recursion otherwise, and literals as fixpoints), the
    /// fuel-bounded `whnf_fuel` reduce-until-fixpoint loop, the step-star
    /// closure, and the loop lemmas — a returned term is a reduce_once
    /// FIXPOINT, extra fuel never changes a successful answer, and (given
    /// step-soundness as a hypothesis, exactly as the proved guide takes it)
    /// the result is reached by the step relation. Every dispatcher is a NAMED
    /// reducible def (elaborator beta-redex lesson).
    fn add_whnf_fuel_loop(&mut self) -> Result<(), SpecError> {
        // Lift a head-reduct through application: none ↦ none, some f2 ↦ some (f2 a).
        self.add_recursive_def(
            r"def opt_app_lift (a : KExpr) (o : OptionType KExpr) : OptionType KExpr := OptionType.rec KExpr (fun (_o : OptionType KExpr) => OptionType KExpr) (OptionType.none KExpr) (fun (f2 : KExpr) => OptionType.some KExpr (KExpr.app f2 a)) o",
            "opt_app_lift a o: lift an optional head-reduct through application by a              (the executable app-left congruence). Part of the WhnfLoop port (X16a).",
        )?;

        // Lift a scrutinee reduct through projection: none ↦ none,
        // some sub2 ↦ some (proj s i sub2).
        self.add_recursive_def(
            r"def opt_proj_lift (s : Name) (i : Nat) (o : OptionType KExpr) : OptionType KExpr := OptionType.rec KExpr (fun (_o : OptionType KExpr) => OptionType KExpr) (OptionType.none KExpr) (fun (sub2 : KExpr) => OptionType.some KExpr (KExpr.proj s i sub2)) o",
            "opt_proj_lift s i o: lift an optional scrutinee reduct through projection              (the executable projection congruence). Part of the current nine-constructor              WhnfLoop port (X16a).",
        )?;

        // The app-node dispatcher: β-fire on a lam head, else lift the head's
        // reduct. Cases the HEAD's constructor non-recursively.
        self.add_recursive_def(
            r"def reduce_app_head (a : KExpr) (f : KExpr) (cf : OptionType KExpr) : OptionType KExpr := KExpr.rec (fun (_e : KExpr) => OptionType KExpr) (fun (n : Level) => opt_app_lift a cf) (fun (i : Nat) => opt_app_lift a cf) (fun (g : KExpr) (b : KExpr) (_cg : OptionType KExpr) (_cb : OptionType KExpr) => opt_app_lift a cf) (fun (ty : KExpr) (b : KExpr) (_cty : OptionType KExpr) (_cb : OptionType KExpr) => OptionType.some KExpr (instantiate b a)) (fun (ty : KExpr) (b : KExpr) (_cty : OptionType KExpr) (_cb : OptionType KExpr) => opt_app_lift a cf) (fun (n : Name) (us : ListType Level) => opt_app_lift a cf) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : OptionType KExpr) (_c2 : OptionType KExpr) (_c3 : OptionType KExpr) => opt_app_lift a cf) (fun (s : Name) (i : Nat) (sub : KExpr) (_csub : OptionType KExpr) => opt_app_lift a cf) (fun (v : Nat) => opt_app_lift a cf) f",
            "reduce_app_head a f cf: the current nine-constructor executable app-node              dispatch — a lam head β-fires (instantiate b a); every other head, including              projection and literal, lifts its own reduct cf through the application.              Part of the WhnfLoop port (X16a).",
        )?;

        // The executable single weak-head step over a definition environment.
        self.add_recursive_def(
            r"def reduce_once (env : DefEnv) (e : KExpr) : OptionType KExpr := KExpr.rec (fun (_e : KExpr) => OptionType KExpr) (fun (n : Level) => OptionType.none KExpr) (fun (i : Nat) => OptionType.none KExpr) (fun (f : KExpr) (a : KExpr) (cf : OptionType KExpr) (_ca : OptionType KExpr) => reduce_app_head a f cf) (fun (ty : KExpr) (b : KExpr) (_cty : OptionType KExpr) (_cb : OptionType KExpr) => OptionType.none KExpr) (fun (ty : KExpr) (b : KExpr) (_cty : OptionType KExpr) (_cb : OptionType KExpr) => OptionType.none KExpr) (fun (n : Name) (us : ListType Level) => defval_for env n) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : OptionType KExpr) (_c2 : OptionType KExpr) (_c3 : OptionType KExpr) => OptionType.some KExpr (instantiate b v)) (fun (s : Name) (i : Nat) (sub : KExpr) (csub : OptionType KExpr) => opt_proj_lift s i csub) (fun (_v : Nat) => OptionType.none KExpr) e",
            "reduce_once env e: the EXECUTABLE single weak-head step — β at a              lam-headed application, ζ at a let, δ at a bare const (defval_for),              head-recursion through application and projection, none at weak-head values              including literals. The kernel-computable twin of one whnf_env_step. Part              of the current nine-constructor WhnfLoop port (X16a).",
        )?;

        // The loop-body dispatcher (named: fixpoint on none, recurse on some).
        self.add_recursive_def(
            r"def loop_dispatch (o : OptionType KExpr) (e0 : KExpr) (ih : KExpr -> OptionType KExpr) : OptionType KExpr := OptionType.rec KExpr (fun (_o : OptionType KExpr) => OptionType KExpr) (OptionType.some KExpr e0) (fun (e2 : KExpr) => ih e2) o",
            "loop_dispatch o e0 ih: one loop-body step — a none reduct means e0 IS the              fixpoint (return it); a some reduct recurses through ih. Part of the              WhnfLoop port (X16a).",
        )?;

        // The fuel-bounded reduce-until-fixpoint loop.
        self.add_recursive_def(
            r"def whnf_fuel (env : DefEnv) (fuel : Nat) (e : KExpr) : OptionType KExpr := Nat.rec (fun (_k : Nat) => KExpr -> OptionType KExpr) (fun (e0 : KExpr) => OptionType.none KExpr) (fun (k : Nat) (ih : KExpr -> OptionType KExpr) => fun (e0 : KExpr) => loop_dispatch (reduce_once env e0) e0 ih) fuel e",
            "whnf_fuel env fuel e: the fuel-bounded reduce-until-fixpoint loop — none              is the honest fuel bail, some r means the loop reached a reduce_once              fixpoint. A β/ζ/bare-δ + proj-congruence fragment skeleton of the literal              whnf_outer_loop — no ι arm, no nat/native/monad accelerators, no cache              model, and the fuel-none models the bail the literal loop expresses by              returning the unreduced term; the correspondence to the literal loop is              informal. The model steps the head one reduction per pass where the              literal reducer fully normalizes the head before its redex test —              fixpoints agree on the fragment, step sequences do not. Part of the              WhnfLoop port (X16a).",
        )?;

        // The reflexive-transitive closure of the δ-aware step.
        self.add_inductive(
            r"inductive env_step_star (env : DefEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), env_step_star env e e
| tail : forall (a : KExpr) (b : KExpr) (c : KExpr), env_step_star env a b → whnf_env_step env b c → env_step_star env a c",
            "env_step_star env a b: the reflexive-transitive closure of whnf_env_step              — the multi-step reduction the loop's soundness path speaks. Part of the              WhnfLoop port (X16a).",
        )?;

        Ok(())
    }

    /// X15 — THE ι-FAMILY PORT (relation level): the 3-way default-mode step
    /// `whnf_red_step` over a full `RedEnv` (β/ζ ∪ head-δ ∪ head-ι), the
    /// δ-family embedding, and the FULL progress + composition-glue theorems
    /// lifted over it. The Nat-instance ι-liveness lands in the natrec stage
    /// (which registers after this one). With this, progress and the
    /// no-reduct classification hold over EVERY reduction family the literal
    /// MIR routing brick proved live in the default kernel mode.
    fn add_red_step_progress(&mut self) -> Result<(), SpecError> {
        // The 3-way step: an iota-free β/ζ bd step, one deterministic head-δ
        // fire, or one deterministic head-ι fire, closed under the weak-head
        // application/projection contexts used by the canonical env relation.
        self.add_inductive(
            r"inductive whnf_red_step (renv : RedEnv) : KExpr → KExpr → Type
| beta : forall (e : KExpr) (e2 : KExpr), beta_reduces_bd e e2 → whnf_red_step renv e e2
| delta : forall (e : KExpr) (e2 : KExpr), Eq (OptionType KExpr) (delta_reduct (red_def renv) e) (OptionType.some KExpr e2) → whnf_red_step renv e e2
| iota : forall (e : KExpr) (e2 : KExpr), Eq (OptionType KExpr) (iota_reduct (red_rec renv) e) (OptionType.some KExpr e2) → whnf_red_step renv e e2
| app_left : forall (f : KExpr) (f2 : KExpr) (a : KExpr), whnf_red_step renv f f2 → whnf_red_step renv (KExpr.app f a) (KExpr.app f2 a)
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr), whnf_red_step renv sub sub2 → whnf_red_step renv (KExpr.proj s i sub) (KExpr.proj s i sub2)",
            "The FULL default-mode weak-head step over a combined reduction              environment: a beta_reduces_bd step (the FULL 13-arm iota-free congruence              closure — under-binder arms included, so this relation admits under-binder              steps), one deterministic head-δ fire (delta_reduct over red_def), or one              deterministic head-ι fire (iota_reduct over red_rec — recursor applied              to a constructor-headed major at the metadata-determined spine position),              closed under the canonical weak-head application-head and              projection-scrutinee contexts. Every reduction family that is live in the default kernel mode              (the routing liveness itself is a quarantined non-authoritative MIR              witness, not a kernel-checked correspondence). Part of the              ι-family port (X15).",
        )?;

        // The δ-family embedding: every whnf_env_step over the RedEnv's
        // definition component is a whnf_red_step.
        self.add_definition(SpecDefinition {
            name: "env_step_to_red".to_string(),
            type_src: concat!(
                "forall (renv : RedEnv) (e : KExpr) (e2 : KExpr), ",
                "whnf_env_step (red_def renv) e e2 -> whnf_red_step renv e e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (renv : RedEnv) (e : KExpr) (e2 : KExpr) ",
                    "(h : whnf_env_step (red_def renv) e e2) => ",
                    "whnf_env_step.rec (red_def renv) ",
                    "(fun (x : KExpr) (x2 : KExpr) ",
                    "(_h : whnf_env_step (red_def renv) x x2) => whnf_red_step renv x x2) ",
                    "(fun (x : KExpr) (x2 : KExpr) (hb : beta_reduces_bd x x2) => ",
                    "whnf_red_step.beta renv x x2 hb) ",
                    "(fun (x : KExpr) (x2 : KExpr) ",
                    "(hd : Eq (OptionType KExpr) (delta_reduct (red_def renv) x) (OptionType.some KExpr x2)) => ",
                    "whnf_red_step.delta renv x x2 hd) ",
                    "(fun (f : KExpr) (f2 : KExpr) (a : KExpr) ",
                    "(_hstep : whnf_env_step (red_def renv) f f2) ",
                    "(ih : whnf_red_step renv f f2) => ",
                    "whnf_red_step.app_left renv f f2 a ih) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) ",
                    "(_hstep : whnf_env_step (red_def renv) sub sub2) ",
                    "(ih : whnf_red_step renv sub sub2) => ",
                    "whnf_red_step.proj renv s i sub sub2 ih) ",
                    "e e2 h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "δ-family EMBEDDING (X15): every whnf_env_step over the RedEnv's definition ",
                "component embeds into the 3-way whnf_red_step (β and δ arms directly; ",
                "application/projection contexts recursively), by whnf_env_step.rec. Lifts the ENTIRE ",
                "DeltaProgress port over the combined environment. DerivedProved, zero ",
                "axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_env_step".to_string(),
                "whnf_env_step.rec".to_string(),
                "whnf_env_step.beta".to_string(),
                "whnf_env_step.delta".to_string(),
                "whnf_env_step.app_left".to_string(),
                "whnf_env_step.proj".to_string(),
                "whnf_red_step".to_string(),
                "whnf_red_step.beta".to_string(),
                "whnf_red_step.delta".to_string(),
                "whnf_red_step.app_left".to_string(),
                "whnf_red_step.proj".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The ι-aware exit witness, including both honest stuck residuals.
        self.add_inductive(
            r"inductive whnf_progress_result_red (renv : RedEnv) : KExpr → Type
| done : forall (e : KExpr), is_whnf e → whnf_progress_result_red renv e
| step : forall (e : KExpr) (e2 : KExpr), whnf_red_step renv e e2 → whnf_progress_result_red renv e
| stuck : forall (f : KExpr) (a : KExpr), whnf_stuck_head f → whnf_progress_result_red renv (KExpr.app f a)
| stuck_proj : forall (s : Name) (i : Nat) (sub : KExpr), whnf_stuck_head sub → whnf_progress_result_red renv (KExpr.proj s i sub)",
            "whnf_progress_result_red renv e: the 3-way-step exit witness for one              weak-head layer over the full RedEnv — a landed is_whnf value, a              whnf_red_step (β/ζ, head-δ, or head-ι), or one of the honest stuck              application/projection residuals. Part of the ι-family port (X15).",
        )?;

        // FULL PROGRESS over the 3-way relation: progress over a LARGER step
        // relation follows a fortiori — done/stuck carry, steps embed.
        self.add_definition(SpecDefinition {
            name: "whnf_progress_red_bd".to_string(),
            type_src: concat!(
                "forall (renv : RedEnv) (e : KExpr), ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined (red_def renv) e -> ",
                "whnf_progress_result_red renv e"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (renv : RedEnv) (e : KExpr) ",
                    "(hb : Eq Nat (bvar_ceiling e) Nat.zero) ",
                    "(hc : consts_defined (red_def renv) e) => ",
                    "whnf_progress_result_env.rec (red_def renv) ",
                    "(fun (x : KExpr) (_r : whnf_progress_result_env (red_def renv) x) => ",
                    "whnf_progress_result_red renv x) ",
                    "(fun (x : KExpr) (hw : is_whnf x) => ",
                    "whnf_progress_result_red.done renv x hw) ",
                    "(fun (x : KExpr) (e2 : KExpr) (hs : whnf_env_step (red_def renv) x e2) => ",
                    "whnf_progress_result_red.step renv x e2 (env_step_to_red renv x e2 hs)) ",
                    "(fun (f : KExpr) (a : KExpr) (hs : whnf_stuck_head f) => ",
                    "whnf_progress_result_red.stuck renv f a hs) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (hs : whnf_stuck_head sub) => ",
                    "whnf_progress_result_red.stuck_proj renv s i sub hs) ",
                    "e (whnf_progress_env_bd (red_def renv) e hb hc)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "FULL PROGRESS over the 3-way default-mode step (X15): every closed KExpr ",
                "whose constants are all defined is a weak-head value, takes a ",
                "whnf_red_step (β/ζ, head-δ, or head-ι), or is honestly stuck — the ",
                "δ-progress capstone lifted over the combined RedEnv through the step ",
                "embedding (a-fortiori: a bigger step relation only makes progress easier). ",
                "NOTE (audit M5): the consts_defined hypothesis requires every const ",
                "δ-BOUND in the definition component, which excludes δ-opaque recursor ",
                "heads — so this theorem adds no ι-progress content beyond the δ capstone; ",
                "genuine ι-liveness is separately witnessed at the Nat instances ",
                "(natrec_fires_red_zero/succ). DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_progress_env_bd".to_string(),
                "whnf_progress_result_env".to_string(),
                "whnf_progress_result_env.rec".to_string(),
                "whnf_progress_result_red".to_string(),
                "whnf_progress_result_red.done".to_string(),
                "whnf_progress_result_red.step".to_string(),
                "whnf_progress_result_red.stuck".to_string(),
                "whnf_progress_result_red.stuck_proj".to_string(),
                "env_step_to_red".to_string(),
                "consts_defined".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // THE 3-WAY COMPOSITION GLUE: no β/ζ, no head-δ, AND no head-ι reduct
        // ⟹ done-or-stuck — by the δ-glue through the embedding contrapositive.
        self.add_definition(SpecDefinition {
            name: "red_fixpoint_classifies_bd".to_string(),
            type_src: concat!(
                "forall (renv : RedEnv) (e : KExpr), ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined (red_def renv) e -> ",
                "(forall (e2 : KExpr), whnf_red_step renv e e2 -> Empty) -> ",
                "whnf_noredex_class e"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (renv : RedEnv) (e : KExpr) ",
                    "(hb : Eq Nat (bvar_ceiling e) Nat.zero) ",
                    "(hc : consts_defined (red_def renv) e) ",
                    "(hns : forall (e2 : KExpr), whnf_red_step renv e e2 -> Empty) => ",
                    "env_fixpoint_classifies_bd (red_def renv) e hb hc ",
                    "(fun (e2 : KExpr) (henv : whnf_env_step (red_def renv) e e2) => ",
                    "hns e2 (env_step_to_red renv e e2 henv))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "THE 3-WAY COMPOSITION GLUE (X15, over the complete 3-way step; the model-to-",
                "literal correspondence is not kernel-checked and mints no literal-Rust ",
                "authority): a closed, fully-defined term with NO ",
                "whnf_red_step reduct — no β, no ζ, no head-δ, AND no head-ι — is a landed ",
                "is_whnf value or the honest stuck residual. By the δ-aware glue through the ",
                "embedding contrapositive (a red-no-step hypothesis refutes every env step). ",
                "NOTE (audit M5): the consts_defined hypothesis excludes δ-opaque recursor ",
                "heads, so the ι arm is never exercised on this domain — no ι content beyond ",
                "the δ capstone; ι-liveness lives at natrec_fires_red_zero/succ. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "env_fixpoint_classifies_bd".to_string(),
                "env_step_to_red".to_string(),
                "whnf_red_step".to_string(),
                "whnf_noredex_class".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// X14 — the δ-AWARE COMPOSITION GLUE: a closed, fully-defined term with
    /// NO whnf_env_step reduct (β, ζ, OR head-δ) is a landed weak-head value
    /// or the honest stuck residual. The δ-extension of
    /// `step_fixpoint_classifies_bd`, same no-step-strengthened-motive proof,
    /// eliminating the FULL δ-progress witness.
    fn add_env_fixpoint_classifies(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "env_fixpoint_classifies_bd".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (e : KExpr), ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> ",
                "(forall (e2 : KExpr), whnf_env_step env e e2 -> Empty) -> ",
                "whnf_noredex_class e"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (e : KExpr) ",
                    "(hb : Eq Nat (bvar_ceiling e) Nat.zero) (hc : consts_defined env e) ",
                    "(hns : forall (e2 : KExpr), whnf_env_step env e e2 -> Empty) => ",
                    "whnf_progress_result_env.rec env ",
                    "(fun (e0 : KExpr) (w : whnf_progress_result_env env e0) => ",
                    "(forall (e2 : KExpr), whnf_env_step env e0 e2 -> Empty) -> whnf_noredex_class e0) ",
                    "(fun (e0 : KExpr) (h : is_whnf e0) ",
                    "(hn : forall (e2 : KExpr), whnf_env_step env e0 e2 -> Empty) => ",
                    "whnf_noredex_class.done e0 h) ",
                    "(fun (e0 : KExpr) (e2 : KExpr) (hstep : whnf_env_step env e0 e2) ",
                    "(hn : forall (e3 : KExpr), whnf_env_step env e0 e3 -> Empty) => ",
                    "Empty.rec (fun (_ : Empty) => whnf_noredex_class e0) (hn e2 hstep)) ",
                    "(fun (f : KExpr) (a : KExpr) (hs : whnf_stuck_head f) ",
                    "(hn : forall (e2 : KExpr), whnf_env_step env (KExpr.app f a) e2 -> Empty) => ",
                    "whnf_noredex_class.stuck f a hs) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (hs : whnf_stuck_head sub) ",
                    "(hn : forall (e2 : KExpr), whnf_env_step env (KExpr.proj s i sub) e2 -> Empty) => ",
                    "whnf_noredex_class.stuck_proj s i sub hs) ",
                    "e (whnf_progress_env_bd env e hb hc) hns"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "δ-AWARE COMPOSITION GLUE (X14, over the δ-extended β/ζ/δ family — family ",
                "completeness language is reserved for the X15 3-way pair): a closed term whose constants are all defined, with ",
                "NO whnf_env_step reduct (no β, no ζ, AND no head-δ), is a landed is_whnf value ",
                "or the honest stuck residual. The model-side implication with which a literal ",
                "fixpoint-exit witness WOULD compose (the correspondence is NOT kernel-checked ",
                "and mints no literal-Rust authority): fixpoint + δ-progress ⟹ ",
                "done-or-stuck. Same no-step-strengthened-motive elimination as ",
                "step_fixpoint_classifies_bd, over whnf_progress_env_bd. DerivedProved, zero ",
                "axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_progress_env_bd".to_string(),
                "whnf_progress_result_env".to_string(),
                "whnf_progress_result_env.rec".to_string(),
                "whnf_env_step".to_string(),
                "whnf_noredex_class".to_string(),
                "whnf_noredex_class.done".to_string(),
                "whnf_noredex_class.stuck".to_string(),
                "whnf_noredex_class.stuck_proj".to_string(),
                "consts_defined".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// X13a — the `consts_defined` predicate and the CONST CASE of full
    /// δ-progress as a kernel theorem. The remaining X13 glue is the
    /// `KExpr.rec` assembly of the full `delta_progress` (guide-validated
    /// foreign-side); this increment lands its load-bearing new case.
    fn add_consts_defined_progress(&mut self) -> Result<(), SpecError> {
        // opt_defined o : the named Type-valued option discriminator (Empty on
        // none, ConstFreeUnit on some). NAMED so every occurrence in motives
        // and binder domains is const-headed — the elaborator rejects a naked
        // beta-redex (fun _ => Type) o in a sort position.
        self.add_recursive_def(
            r"def opt_defined (o : OptionType KExpr) : Type := OptionType.rec KExpr (fun (_o : OptionType KExpr) => Type) Empty (fun (v : KExpr) => ConstFreeUnit) o",
            "opt_defined o is inhabited exactly when o is some (ConstFreeUnit) and empty              on none — the named option discriminator used by has_defval and the              scrutinee-generalized const-case progress proof. Part of the DeltaProgress              spec-port (X13a).",
        )?;

        // has_defval env n : inhabited iff the name is bound (Empty on a miss).
        self.add_recursive_def(
            r"def has_defval (env : DefEnv) (n : Name) : Type := opt_defined (defval_for env n)",
            "has_defval env n is inhabited exactly when the definition environment binds n              (ConstFreeUnit on some, Empty on none) — the const-node witness of the              consts_defined predicate. Part of the DeltaProgress spec-port (X13a).",
        )?;

        // consts_defined: const_free with the const arm swapped from Empty to
        // has_defval — every constant occurring in the term is bound.
        self.add_recursive_def(
            r"def consts_defined (env : DefEnv) (e : KExpr) : Type := KExpr.rec (fun (_ : KExpr) => Type) (fun (n : Level) => ConstFreeUnit) (fun (i : Nat) => ConstFreeUnit) (fun (f : KExpr) (a : KExpr) (cf : Type) (ca : Type) => AndType cf ca) (fun (ty : KExpr) (b : KExpr) (cty : Type) (cb : Type) => AndType cty cb) (fun (ty : KExpr) (b : KExpr) (cty : Type) (cb : Type) => AndType cty cb) (fun (n : Name) (us : ListType Level) => has_defval env n) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (cty : Type) (cv : Type) (cb : Type) => AndType cty (AndType cv cb)) (fun (s : Name) (i : Nat) (sub : KExpr) (csub : Type) => csub) (fun (v : Nat) => ConstFreeUnit) e",
            "consts_defined env e is inhabited iff every KExpr.const in e is bound in env:              the exact current KExpr recursion (including projection and literal) with the              const arm swapped from Empty to has_defval env n. The hypothesis of the              full δ-progress statement. Part of the DeltaProgress spec-port (X13a).",
        )?;

        // THE CONST CASE of full δ-progress: a constant with all (i.e. its own)
        // consts defined PROGRESSES — by scrutinee-generalized OptionType.rec
        // on the lookup with the equation threaded, closing the some-arm with
        // the X12 liveness theorem and refuting the none-arm by Empty.
        self.add_definition(SpecDefinition {
            name: "const_progress_env".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (n : Name) (us : ListType Level), ",
                "consts_defined env (KExpr.const n us) -> ",
                "whnf_progress_result_env env (KExpr.const n us)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (n : Name) (us : ListType Level) ",
                    "(hc : consts_defined env (KExpr.const n us)) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (defval_for env n) o -> ",
                    "opt_defined o -> ",
                    "whnf_progress_result_env env (KExpr.const n us)) ",
                    "(fun (_heq : Eq (OptionType KExpr) (defval_for env n) (OptionType.none KExpr)) (hd : Empty) => ",
                    "Empty.rec (fun (_e : Empty) => whnf_progress_result_env env (KExpr.const n us)) hd) ",
                    "(fun (v : KExpr) (heq : Eq (OptionType KExpr) (defval_for env n) (OptionType.some KExpr v)) (_hd : ConstFreeUnit) => ",
                    "whnf_progress_result_env.step env (KExpr.const n us) v (const_delta_fires env n us v heq)) ",
                    "(defval_for env n) ",
                    "(Eq.refl (OptionType KExpr) (defval_for env n)) ",
                    "hc"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "THE CONST CASE of full δ-progress (DeltaProgress spec-port X13a): a constant ",
                "whose name is defined PROGRESSES — scrutinee-generalized OptionType.rec on ",
                "defval_for with the lookup equation threaded through the motive (the applied ",
                "major instance is definitionally consts_defined at a const node); the some arm ",
                "closes by the X12 δ-liveness theorem const_delta_fires, the none arm is refuted ",
                "by Empty elimination. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "consts_defined".to_string(),
                "has_defval".to_string(),
                "opt_defined".to_string(),
                "defval_for".to_string(),
                "const_delta_fires".to_string(),
                "whnf_progress_result_env".to_string(),
                "whnf_progress_result_env.step".to_string(),
                "Empty.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// δ-AWARE PROGRESS SUBSTRATE (the first spec-port increment of the
    /// Aristotle-proved DeltaProgress guide): the env-aware weak-head step
    /// (β ∪ head-δ plus weak-head contextual closure over `DefEnv`), the
    /// env-aware progress result,
    /// the δ-LIVENESS theorem (a defined constant ALWAYS steps — ported from
    /// `const_always_steps`, now a Clean-kernel theorem), and the lift of the
    /// const-free progress theorem into the δ-aware result. The FULL
    /// δ-progress over `consts_defined` terms is the next rung; this one
    /// lands the relation, the liveness, and the bridge.
    fn add_whnf_env_progress(&mut self) -> Result<(), SpecError> {
        // The env-aware weak-head step: a β+ζ bd step, one deterministic
        // head-δ fire, or the weak-head contextual closure needed by the
        // current KExpr application/projection constructors.
        self.add_inductive(
            r"inductive whnf_env_step (env : DefEnv) : KExpr → KExpr → Type
| beta : forall (e : KExpr) (e2 : KExpr), beta_reduces_bd e e2 → whnf_env_step env e e2
| delta : forall (e : KExpr) (e2 : KExpr), Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e2) → whnf_env_step env e e2
| app_left : forall (f : KExpr) (f2 : KExpr) (a : KExpr), whnf_env_step env f f2 → whnf_env_step env (KExpr.app f a) (KExpr.app f2 a)
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr), whnf_env_step env sub sub2 → whnf_env_step env (KExpr.proj s i sub) (KExpr.proj s i sub2)",
            "The δ-AWARE weak-head step over a definition environment: either a              beta_reduces_bd step (the FULL 13-arm iota-free congruence closure —              under-binder arms included, so this relation ADMITS under-binder steps and              an executable weak-head fixpoint does NOT refute it; round-4 fidelity              audit), one deterministic head-δ fire (delta_reduct — which decomposes              applied const spines via kapp_fn/apply_spine, so a defined const under              application δ-steps as a whole), or the contextual weak-head lift through              an application head or projection scrutinee. app_left/proj are required              so δ progress of a child remains progress for the current KExpr app/proj              forms. Part of the DeltaProgress spec-port (Aristotle guide, round 1).",
        )?;

        // The env-aware exit witness. Keep both honest stuck residuals from
        // whnf_progress_result: an application with a stuck head and a
        // projection with a stuck scrutinee.
        self.add_inductive(
            r"inductive whnf_progress_result_env (env : DefEnv) : KExpr → Type
| done : forall (e : KExpr), is_whnf e → whnf_progress_result_env env e
| step : forall (e : KExpr) (e2 : KExpr), whnf_env_step env e e2 → whnf_progress_result_env env e
| stuck : forall (f : KExpr) (a : KExpr), whnf_stuck_head f → whnf_progress_result_env env (KExpr.app f a)
| stuck_proj : forall (s : Name) (i : Nat) (sub : KExpr), whnf_stuck_head sub → whnf_progress_result_env env (KExpr.proj s i sub)",
            "whnf_progress_result_env env e: the δ-aware exit witness for one weak-head              layer — a landed is_whnf value, a whnf_env_step (β/ζ, head-δ, or a              contextual app/proj lift), or one of the honest stuck application/projection              residuals. Part of the DeltaProgress spec-port.",
        )?;

        // δ-LIVENESS (ported from the proved guide's const_always_steps): a
        // constant with a defined value ALWAYS steps — by transporting the
        // lookup equation through opt_bind and closing with definitional
        // computation of delta_reduct on a const head.
        self.add_definition(SpecDefinition {
            name: "const_delta_fires".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (n : Name) (us : ListType Level) (v : KExpr), ",
                "Eq (OptionType KExpr) (defval_for env n) (OptionType.some KExpr v) -> ",
                "whnf_env_step env (KExpr.const n us) v"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (n : Name) (us : ListType Level) (v : KExpr) ",
                    "(h : Eq (OptionType KExpr) (defval_for env n) (OptionType.some KExpr v)) => ",
                    "whnf_env_step.delta env (KExpr.const n us) v ",
                    "(Eq.rec (OptionType KExpr) (defval_for env n) ",
                    "(fun (o : OptionType KExpr) (_h : Eq (OptionType KExpr) (defval_for env n) o) => ",
                    "Eq (OptionType KExpr) ",
                    "(opt_bind KExpr KExpr (defval_for env n) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.const n us)) val))) ",
                    "(opt_bind KExpr KExpr o (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.const n us)) val)))) ",
                    "(Eq.refl (OptionType KExpr) (opt_bind KExpr KExpr (defval_for env n) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.const n us)) val)))) ",
                    "(OptionType.some KExpr v) h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "δ-LIVENESS (DeltaProgress spec-port, ported from the Aristotle-proved ",
                "const_always_steps): a constant whose name is bound in the definition ",
                "environment ALWAYS takes a whnf_env_step — the head-δ fire. Proof: transport ",
                "the defval_for lookup equation through opt_bind via based Eq.rec; the base is ",
                "Eq.refl on the definitional computation of delta_reduct at a const head ",
                "(kapp_fn/kexpr_const_name/kapp_args all reduce), and the transported target ",
                "computes to the some-of-value shape (apply_spine nil v = v). NOTE (audit M6): ",
                "the model δ is name-keyed and LEVEL-BLIND — it fires to the raw definiens ",
                "with no universe-level instantiation, where the real kernel δ instantiates ",
                "the const levels (documented base deviation). DerivedProved, ",
                "zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_env_step".to_string(),
                "whnf_env_step.delta".to_string(),
                "delta_reduct".to_string(),
                "defval_for".to_string(),
                "opt_bind".to_string(),
                "apply_spine".to_string(),
                "kapp_args".to_string(),
                "Eq.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The bridge: const-free bvar-free progress lifts into the δ-aware
        // result over ANY environment (done/stuck carry over; steps embed via
        // the beta arm).
        self.add_definition(SpecDefinition {
            name: "whnf_progress_env_constfree".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (e : KExpr), ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> ",
                "whnf_progress_result_env env e"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (e : KExpr) (hb : Eq Nat (bvar_ceiling e) Nat.zero) ",
                    "(hc : const_free e) => ",
                    "whnf_progress_result.rec ",
                    "(fun (e1 : KExpr) (_r : whnf_progress_result e1) => whnf_progress_result_env env e1) ",
                    "(fun (e1 : KExpr) (hw : is_whnf e1) => whnf_progress_result_env.done env e1 hw) ",
                    "(fun (e1 : KExpr) (e2 : KExpr) (hs : beta_reduces_bd e1 e2) => ",
                    "whnf_progress_result_env.step env e1 e2 (whnf_env_step.beta env e1 e2 hs)) ",
                    "(fun (f : KExpr) (a : KExpr) (hs : whnf_stuck_head f) => ",
                    "whnf_progress_result_env.stuck env f a hs) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (hs : whnf_stuck_head sub) => ",
                    "whnf_progress_result_env.stuck_proj env s i sub hs) ",
                    "e (whnf_progress_bd e hb hc)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "BRIDGE (DeltaProgress spec-port): the landed const-free bvar-free progress ",
                "theorem whnf_progress_bd lifts into the δ-aware whnf_progress_result_env over ",
                "ANY definition environment — done/stuck/stuck_proj carry over unchanged and β/ζ steps ",
                "embed through whnf_env_step.beta, by whnf_progress_result.rec. With ",
                "const_delta_fires this pins both halves the FULL δ-progress rung will glue: ",
                "const-free subterms progress, defined consts fire. DerivedProved, zero ",
                "axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_progress_bd".to_string(),
                "whnf_progress_result".to_string(),
                "whnf_progress_result.rec".to_string(),
                "whnf_progress_result_env".to_string(),
                "whnf_progress_result_env.done".to_string(),
                "whnf_progress_result_env.step".to_string(),
                "whnf_progress_result_env.stuck".to_string(),
                "whnf_progress_result_env.stuck_proj".to_string(),
                "whnf_env_step".to_string(),
                "whnf_env_step.beta".to_string(),
                "const_free".to_string(),
                "bvar_ceiling".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The Prop→Type universe lift for the SINGLE reducer-universal composite
    /// statement. The kernel-computed reflection facts are Prop-sorted
    /// (`Eq Bool … Bool.true`) while the model universals (`whnf_progress_bd`,
    /// `whnf_normalizes_bd`, `step_fixpoint_classifies_bd`) are Type-sorted —
    /// `LiftP` lets ONE `AndType` chain conjoin all of them into a single
    /// kernel-checked statement (assembled programmatically on the
    /// trust-certify side; the graphs exceed the term parser's nesting limit).
    fn add_composite_lift(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive LiftP (P : Prop) : Type
| up : P → LiftP P",
            "LiftP P : Type is inhabited exactly when the Prop P is — the universe lift \
             that lets the Type-sorted AndType chain conjoin Prop-sorted kernel-computed \
             Eq facts with the Type-sorted model universals in the single \
             reducer-universal composite statement.",
        )?;

        // In-dialect smoke: LiftP composes with AndType across sorts — the
        // exact shape the programmatic composite statement uses.
        self.add_definition(SpecDefinition {
            name: "liftp_composite_smoke".to_string(),
            type_src: "AndType (LiftP (Eq Bool Bool.true Bool.true)) ConstFreeUnit".to_string(),
            value_src: Some(
                "AndType.intro (LiftP (Eq Bool Bool.true Bool.true)) ConstFreeUnit \
                 (LiftP.up (Eq Bool Bool.true Bool.true) (Eq.refl Bool Bool.true)) \
                 ConstFreeUnit.triv"
                    .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Cross-sort composition smoke: an AndType conjunct built from a LiftP-lifted ",
                "Prop-sorted Eq fact and a Type-sorted witness — the exact shape of the single ",
                "reducer-universal composite statement. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "LiftP".to_string(),
                "AndType".to_string(),
                "ConstFreeUnit".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// MIR CFG REACHABILITY — the kernel-side substrate for reflecting the
    /// CONTROL-FLOW L-witnesses (cached-reducer, fixpoint-exit). A graph is a
    /// list of nodes `(id, succs)`; reachability is a FUEL-BOUNDED visited-set
    /// iteration (fuel = node count, supplied by the encoder), entirely
    /// kernel-COMPUTABLE. An optional CUT EDGE (from, to) is removed kernel-side
    /// — the loop-analysis primitive (cutting a backedge separates "exits this
    /// iteration" from "re-loops") lives in the kernel, not Rust.
    ///
    /// The ENCODED GRAPHS are too large for the term parser (the 128-deep
    /// nesting limit — an 87-block adjacency list is a >87-deep cons chain), so
    /// the DATA is built programmatically as `Expr`s on the trust-certify side
    /// and kernel-checked there against these registered checkers; only the
    /// (small) model + checker functions are registered from source here.
    fn add_mir_cfg_reachability(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive MirNode : Type
| mk : Nat → ListType Nat → MirNode",
            "A reflected CFG node: its block id and successor ids. The kernel-side \
             substrate for control-flow L-witness reflection.",
        )?;

        let defs: Vec<(&str, &str, String)> = vec![
            // Is `x` a member of the id list?
            (
                "mir_mem",
                "Nat -> ListType Nat -> Bool",
                "fun (x : Nat) (l : ListType Nat) => ListType.rec Nat \
                 (fun (_ : ListType Nat) => Bool) Bool.false \
                 (fun (h : Nat) (t : ListType Nat) (ih : Bool) => \
                 Bool.rec (fun (_ : Bool) => Bool) ih Bool.true (mir_nat_eqb x h)) l"
                    .to_string(),
            ),
            // Successors of `id` in the graph, with the cut edge (cf, ct) removed:
            // if id = cf, filter ct out of the successor list.
            (
                "mir_succs",
                "ListType MirNode -> Nat -> Nat -> Nat -> ListType Nat",
                "fun (g : ListType MirNode) (cf : Nat) (ct : Nat) (id : Nat) => \
                 ListType.rec MirNode (fun (_ : ListType MirNode) => ListType Nat) \
                 (ListType.nil Nat) \
                 (fun (n : MirNode) (rest : ListType MirNode) (ih : ListType Nat) => \
                 MirNode.rec (fun (_ : MirNode) => ListType Nat) \
                 (fun (nid : Nat) (succs : ListType Nat) => \
                 Bool.rec (fun (_ : Bool) => ListType Nat) ih \
                 (Bool.rec (fun (_ : Bool) => ListType Nat) succs \
                 (ListType.rec Nat (fun (_ : ListType Nat) => ListType Nat) \
                 (ListType.nil Nat) \
                 (fun (s : Nat) (st : ListType Nat) (sih : ListType Nat) => \
                 Bool.rec (fun (_ : Bool) => ListType Nat) \
                 (ListType.cons Nat s sih) sih (mir_nat_eqb s ct)) succs) \
                 (mir_nat_eqb nid cf)) \
                 (mir_nat_eqb nid id)) n) g"
                    .to_string(),
            ),
            // One frontier expansion: fold the visited set, consing every successor
            // not already visited (dedup against the ACCUMULATED set).
            (
                "mir_expand",
                "ListType MirNode -> Nat -> Nat -> ListType Nat -> ListType Nat",
                "fun (g : ListType MirNode) (cf : Nat) (ct : Nat) (visited : ListType Nat) => \
                 ListType.rec Nat (fun (_ : ListType Nat) => ListType Nat) visited \
                 (fun (v : Nat) (rest : ListType Nat) (acc : ListType Nat) => \
                 ListType.rec Nat (fun (_ : ListType Nat) => ListType Nat) acc \
                 (fun (s : Nat) (st : ListType Nat) (acc2 : ListType Nat) => \
                 Bool.rec (fun (_ : Bool) => ListType Nat) \
                 (ListType.cons Nat s acc2) acc2 (mir_mem s acc2)) \
                 (mir_succs g cf ct v)) visited"
                    .to_string(),
            ),
            // Fuel-bounded reachability: iterate mir_expand `fuel` times from the
            // singleton {start}, then test membership of `target`.
            (
                "mir_reaches",
                "ListType MirNode -> Nat -> Nat -> Nat -> Nat -> Nat -> Bool",
                "fun (g : ListType MirNode) (cf : Nat) (ct : Nat) (fuel : Nat) \
                 (start : Nat) (target : Nat) => \
                 mir_mem target \
                 (Nat.rec (fun (_ : Nat) => ListType Nat) \
                 (ListType.cons Nat start (ListType.nil Nat)) \
                 (fun (k : Nat) (acc : ListType Nat) => mir_expand g cf ct acc) fuel)"
                    .to_string(),
            ),
        ];
        for (name, ty, value) in defs {
            self.add_definition_reducible(SpecDefinition {
                name: name.to_string(),
                type_src: ty.to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: format!(
                    "{name}: kernel-computable CFG reachability component (control-flow \
                     L-witness reflection substrate)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: None,
                axiom_deps: HashSet::new(),
            })?;
        }

        // SMOKE theorem (kernel-computed, parser-small): on the 3-node graph
        // 0→1→2 with the edge 1→2 CUT, node 2 is unreachable from 0 — and
        // WITHOUT the cut it IS reachable. Pins the checker's semantics (incl.
        // the cut) inside the kernel at registration time.
        let g = "(ListType.cons MirNode (MirNode.mk Nat.zero (ListType.cons Nat (Nat.succ Nat.zero) (ListType.nil Nat))) (ListType.cons MirNode (MirNode.mk (Nat.succ Nat.zero) (ListType.cons Nat (Nat.succ (Nat.succ Nat.zero)) (ListType.nil Nat))) (ListType.cons MirNode (MirNode.mk (Nat.succ (Nat.succ Nat.zero)) (ListType.nil Nat)) (ListType.nil MirNode))))";
        self.add_definition(SpecDefinition {
            name: "mir_reaches_smoke".to_string(),
            type_src: format!(
                "Eq Bool (mir_band \
                 (mir_reaches {g} (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ (Nat.succ Nat.zero))) Nat.zero (Nat.succ (Nat.succ Nat.zero))) \
                 (mir_bnot (mir_reaches {g} (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ (Nat.succ Nat.zero))) Nat.zero (Nat.succ (Nat.succ Nat.zero))))) Bool.true"
            ),
            value_src: Some("Eq.refl Bool Bool.true".to_string()),
            is_axiom: false,
            description: concat!(
                "SMOKE pin for the kernel-side CFG reachability: on 0->1->2, node 2 IS ",
                "reachable from 0 with a no-op cut (3,3), and is NOT reachable with the ",
                "edge (1,2) cut — both computed by the kernel (Eq.refl). Pins the checker ",
                "semantics (incl. the cut) at registration. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "mir_reaches".to_string(),
                "mir_band".to_string(),
                "mir_bnot".to_string(),
                "MirNode".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// MIR PAYLOAD REFLECTION — the first KERNEL-CHECKED L-witness. The
    /// trust-certify `whnf_stack_safe_payload_is_whnf_inner` witness (the real
    /// `whnf_impl::{closure#1}` is a pure `whnf_inner` passthrough) is re-stated
    /// here IN THE KERNEL'S LOGIC: the closure's MIR shape is ENCODED as kernel
    /// data (a tiny MIR model — statements classified as capture-unpacks vs other
    /// writes, terminators as opaque-call/ret, exactly-two-blocks by type), the
    /// witness PREDICATE is a Bool-valued spec function over that model, and the
    /// theorem `mir_payload_check <encoding> <whnf_inner> = true` is proved by
    /// KERNEL COMPUTATION (`Eq.refl` — the kernel evaluates the checker).
    ///
    /// The RESIDUAL trust is the ENCODER's fidelity (the trust-certify side
    /// re-derives the encoding from the committed real-MIR fixture and pins it
    /// byte-identically against this registration) — the same epistemic shape as
    /// the reflected kernel-env foundation core. The witness LOGIC itself (what
    /// the shape checks mean and that the encoding satisfies them) is now
    /// kernel-checked, not Rust.
    fn add_mir_payload_reflection(&mut self) -> Result<(), SpecError> {
        // Nat literal `Nat.succ^n Nat.zero`. Kept SMALL: the parser has a
        // nesting-depth limit (128), so raw byte values (e.g. 'w' = 119) are out
        // of range once wrapped in the surrounding term — the name encoding below
        // uses a compact per-character code instead.
        fn nat_src(n: usize) -> String {
            let mut s = "Nat.zero".to_string();
            for _ in 0..n {
                s = format!("(Nat.succ {s})");
            }
            s
        }
        // A Name from an identifier string: fold each character into `Name.str`
        // using the COMPACT INJECTIVE code `c - 94` over the domain `[_a-z]`
        // ('_' = 1, 'a' = 3 … 'z' = 28; max chain depth 28, far under the parser
        // limit). The trust-side encoder uses the SAME code, so a tampered callee
        // (any other identifier over the domain) encodes to a DIFFERENT Name and
        // the kernel's mir_name_eqb check fails. Characters outside the domain
        // would panic loudly at registration (never silently alias).
        fn name_src(text: &str) -> String {
            let mut s = "Name.anonymous".to_string();
            for c in text.chars() {
                assert!(
                    c == '_' || c.is_ascii_lowercase(),
                    "mir name encoding domain is [_a-z], got {c:?}"
                );
                let code = (c as usize) - 94;
                s = format!("(Name.str {s} {})", nat_src(code));
            }
            s
        }

        self.add_inductive(
            r"inductive MirStmt : Type
| unpack : Nat → MirStmt
| assign_other : Nat → MirStmt
| non_assign : MirStmt",
            "MIR statement classification for the payload reflection: a closure-capture \
             unpack `dst = copy (_1.<field>)` (recording the destination local), any \
             other assignment (recording its destination), or a non-assign statement.",
        )?;
        self.add_inductive(
            r"inductive MirTerm : Type
| opaque_call : Name → MirTerm
| ret : MirTerm
| other_term : MirTerm",
            "MIR terminator classification for the payload reflection: an opaque-encoded \
             call (recording the callee's final segment as a byte-folded Name), a plain \
             return, or anything else.",
        )?;
        self.add_inductive(
            r"inductive MirBlock : Type
| mk : ListType MirStmt → MirTerm → MirBlock",
            "A reflected MIR basic block: its classified statements and terminator.",
        )?;
        self.add_inductive(
            r"inductive PayloadBody : Type
| mk2 : MirBlock → MirBlock → PayloadBody",
            "An exactly-two-block MIR body (the stack_safe payload closure's shape); \
             the two-block arity is carried BY TYPE.",
        )?;

        // Boolean helpers over the model (Bool.rec minor order: false, true).
        // SELF-CONTAINED: the equality helpers are defined here (Nat.rec /
        // Name.rec) rather than borrowing nat_eqb/name_eqb, so every def in the
        // checker chain is REDUCIBLE (add_definition_reducible — the kernel must
        // COMPUTE the checker for the Eq.refl proof; a sealed def would hit the
        // same is_def_eq wall const_whnf did before Brick A).
        let defs: Vec<(&str, &str, String)> = vec![
            (
                "mir_band",
                "Bool -> Bool -> Bool",
                "fun (a : Bool) (b : Bool) => Bool.rec (fun (_ : Bool) => Bool) Bool.false b a"
                    .to_string(),
            ),
            (
                "mir_bnot",
                "Bool -> Bool",
                "fun (a : Bool) => Bool.rec (fun (_ : Bool) => Bool) Bool.true Bool.false a"
                    .to_string(),
            ),
            (
                "mir_nat_eqb",
                "Nat -> Nat -> Bool",
                "fun (a : Nat) => Nat.rec (fun (_ : Nat) => Nat -> Bool) \
                 (fun (b : Nat) => Nat.rec (fun (_ : Nat) => Bool) Bool.true \
                 (fun (b2 : Nat) (_ : Bool) => Bool.false) b) \
                 (fun (a2 : Nat) (ih : Nat -> Bool) => fun (b : Nat) => \
                 Nat.rec (fun (_ : Nat) => Bool) Bool.false \
                 (fun (b2 : Nat) (_ : Bool) => ih b2) b) a"
                    .to_string(),
            ),
            (
                "mir_name_eqb",
                "Name -> Name -> Bool",
                "fun (a : Name) => Name.rec (fun (_ : Name) => Name -> Bool) \
                 (fun (b : Name) => Name.rec (fun (_ : Name) => Bool) Bool.true \
                 (fun (pb : Name) (cb : Nat) (_ : Bool) => Bool.false) b) \
                 (fun (pa : Name) (ca : Nat) (ihpa : Name -> Bool) => fun (b : Name) => \
                 Name.rec (fun (_ : Name) => Bool) Bool.false \
                 (fun (pb : Name) (cb : Nat) (_ : Bool) => \
                 mir_band (ihpa pb) (mir_nat_eqb ca cb)) b) a"
                    .to_string(),
            ),
            (
                "mir_stmt_unpack_ok",
                "MirStmt -> Bool",
                "fun (s : MirStmt) => MirStmt.rec (fun (_ : MirStmt) => Bool) \
                 (fun (dst : Nat) => mir_bnot (mir_nat_eqb dst Nat.zero)) \
                 (fun (_ : Nat) => Bool.false) Bool.false s"
                    .to_string(),
            ),
            (
                "mir_stmts_all_unpack",
                "ListType MirStmt -> Bool",
                "fun (l : ListType MirStmt) => ListType.rec MirStmt \
                 (fun (_ : ListType MirStmt) => Bool) Bool.true \
                 (fun (s : MirStmt) (rest : ListType MirStmt) (ih : Bool) => \
                 mir_band (mir_stmt_unpack_ok s) ih) l"
                    .to_string(),
            ),
            (
                "mir_stmts_is_nil",
                "ListType MirStmt -> Bool",
                "fun (l : ListType MirStmt) => ListType.rec MirStmt \
                 (fun (_ : ListType MirStmt) => Bool) Bool.true \
                 (fun (s : MirStmt) (rest : ListType MirStmt) (ih : Bool) => Bool.false) l"
                    .to_string(),
            ),
            (
                "mir_term_calls",
                "MirTerm -> Name -> Bool",
                "fun (t : MirTerm) (callee : Name) => MirTerm.rec (fun (_ : MirTerm) => Bool) \
                 (fun (n : Name) => mir_name_eqb n callee) Bool.false Bool.false t"
                    .to_string(),
            ),
            (
                "mir_term_is_ret",
                "MirTerm -> Bool",
                "fun (t : MirTerm) => MirTerm.rec (fun (_ : MirTerm) => Bool) \
                 (fun (_ : Name) => Bool.false) Bool.true Bool.false t"
                    .to_string(),
            ),
            (
                "mir_block_call_ok",
                "MirBlock -> Name -> Bool",
                "fun (b : MirBlock) (callee : Name) => MirBlock.rec (fun (_ : MirBlock) => Bool) \
                 (fun (stmts : ListType MirStmt) (t : MirTerm) => \
                 mir_band (mir_stmts_all_unpack stmts) (mir_term_calls t callee)) b"
                    .to_string(),
            ),
            (
                "mir_block_ret_ok",
                "MirBlock -> Bool",
                "fun (b : MirBlock) => MirBlock.rec (fun (_ : MirBlock) => Bool) \
                 (fun (stmts : ListType MirStmt) (t : MirTerm) => \
                 mir_band (mir_stmts_is_nil stmts) (mir_term_is_ret t)) b"
                    .to_string(),
            ),
            (
                "mir_payload_check",
                "PayloadBody -> Name -> Bool",
                "fun (p : PayloadBody) (callee : Name) => PayloadBody.rec \
                 (fun (_ : PayloadBody) => Bool) \
                 (fun (b0 : MirBlock) (b1 : MirBlock) => \
                 mir_band (mir_block_call_ok b0 callee) (mir_block_ret_ok b1)) p"
                    .to_string(),
            ),
        ];
        for (name, ty, value) in defs {
            self.add_definition_reducible(SpecDefinition {
                name: name.to_string(),
                type_src: ty.to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: format!(
                    "{name}: Bool-valued checker component of the MIR payload reflection \
                     (kernel-computable; part of the first kernel-checked L-witness)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: None,
                axiom_deps: HashSet::new(),
            })?;
        }

        // The ENCODED real payload body (whnf_impl::{closure#1}, from the
        // provenance-pinned fixture): block 0 = two capture unpacks into locals
        // 2 and 3, then the opaque call to `whnf_inner`; block 1 = bare return.
        // The trust-certify side re-derives this encoding from the committed
        // fixture and pins it against this registration byte-identically.
        let callee = name_src("whnf_inner");
        let encoded = format!(
            "(PayloadBody.mk2 (MirBlock.mk (ListType.cons MirStmt (MirStmt.unpack {n2}) \
             (ListType.cons MirStmt (MirStmt.unpack {n3}) (ListType.nil MirStmt))) \
             (MirTerm.opaque_call {callee})) (MirBlock.mk (ListType.nil MirStmt) MirTerm.ret))",
            n2 = nat_src(2),
            n3 = nat_src(3),
        );
        self.add_definition(SpecDefinition {
            name: "mir_payload_reflection_whnf_inner".to_string(),
            type_src: format!("Eq Bool (mir_payload_check {encoded} {callee}) Bool.true"),
            value_src: Some("Eq.refl Bool Bool.true".to_string()),
            is_axiom: false,
            description: concat!(
                "THE FIRST KERNEL-CHECKED L-WITNESS: the encoded real stack_safe payload ",
                "closure (whnf_impl::{closure#1}, provenance-pinned fixture) SATISFIES the ",
                "payload predicate — two capture unpacks into non-return locals, an opaque ",
                "call whose callee is whnf_inner, and a bare-return second block — proved by ",
                "KERNEL COMPUTATION (Eq.refl: the kernel evaluates mir_payload_check on the ",
                "encoding to Bool.true). The encoder's fidelity to the committed fixture is ",
                "pinned on the trust-certify side; the witness LOGIC is kernel-checked here. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "mir_payload_check".to_string(),
                "PayloadBody".to_string(),
                "MirBlock".to_string(),
                "MirStmt".to_string(),
                "MirTerm".to_string(),
                "mir_name_eqb".to_string(),
                "mir_nat_eqb".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// MIR DISPATCH-ARM REFLECTION — the kernel-side half of the dispatch
    /// totality L-witness. The outer `whnf_impl` kind-switch's arms are encoded
    /// as `(variant, is_identity)` pairs; the KERNEL checks the structural
    /// partition facts over the encoding:
    ///
    ///   * every variant is `< 25` (the full ExprKind arity) and the arm values
    ///     are strictly increasing (hence unique);
    ///   * the identity flags sit EXACTLY on `{0, 2, 5, 6, 8}` (BVar/Sort/Lam/
    ///     Pi/Lit — the early-return identity variants);
    ///   * the single non-identity explicit arm is variant `1` (FVar);
    ///
    /// (the `otherwise` complement's ROUTING to the recursive core is the
    /// separate kernel-computed reachability fact, checked programmatically on
    /// the trust side over the encoded CFG). The ENCODER residual: deriving
    /// `(variant, is_identity)` from the real switch + the identity-clone
    /// copy-trace, pinned to the fixture on the trust side.
    fn add_mir_dispatch_reflection(&mut self) -> Result<(), SpecError> {
        fn nat_src(n: usize) -> String {
            let mut s = "Nat.zero".to_string();
            for _ in 0..n {
                s = format!("(Nat.succ {s})");
            }
            s
        }

        self.add_inductive(
            r"inductive MirArm : Type
| mk : Nat → Bool → MirArm",
            "A reflected dispatch arm: the ExprKind variant value and whether the arm is \
             the identity early-return shape.",
        )?;

        let defs: Vec<(&str, &str, String)> = vec![
            // Is `v` one of the identity variants {0, 2, 5, 6, 8}?
            (
                "mir_is_identity_variant",
                "Nat -> Bool",
                format!(
                    "fun (v : Nat) => Bool.rec (fun (_ : Bool) => Bool) \
                     (Bool.rec (fun (_ : Bool) => Bool) \
                     (Bool.rec (fun (_ : Bool) => Bool) \
                     (Bool.rec (fun (_ : Bool) => Bool) \
                     (mir_nat_eqb v {n8}) \
                     Bool.true (mir_nat_eqb v {n6})) \
                     Bool.true (mir_nat_eqb v {n5})) \
                     Bool.true (mir_nat_eqb v {n2})) \
                     Bool.true (mir_nat_eqb v Nat.zero)",
                    n2 = nat_src(2),
                    n5 = nat_src(5),
                    n6 = nat_src(6),
                    n8 = nat_src(8),
                ),
            ),
            // Nat strict less-than via double recursion (a < b).
            (
                "mir_nat_ltb",
                "Nat -> Nat -> Bool",
                "fun (a : Nat) => Nat.rec (fun (_ : Nat) => Nat -> Bool) \
                 (fun (b : Nat) => Nat.rec (fun (_ : Nat) => Bool) Bool.false \
                 (fun (b2 : Nat) (_ : Bool) => Bool.true) b) \
                 (fun (a2 : Nat) (ih : Nat -> Bool) => fun (b : Nat) => \
                 Nat.rec (fun (_ : Nat) => Bool) Bool.false \
                 (fun (b2 : Nat) (_ : Bool) => ih b2) b) a"
                    .to_string(),
            ),
            // One arm's local facts: variant < bound, and the identity flag agrees
            // with mir_is_identity_variant EXCEPT that variant 1 (FVar) must be
            // non-identity (mir_is_identity_variant 1 = false, so agreement covers it).
            (
                "mir_arm_ok",
                "Nat -> MirArm -> Bool",
                "fun (bound : Nat) (a : MirArm) => MirArm.rec (fun (_ : MirArm) => Bool) \
                 (fun (v : Nat) (ident : Bool) => mir_band (mir_nat_ltb v bound) \
                 (Bool.rec (fun (_ : Bool) => Bool) (mir_nat_eqb v (Nat.succ Nat.zero)) \
                 (mir_is_identity_variant v) ident)) a"
                    .to_string(),
            ),
            // The arm list: every arm ok, values strictly increasing (unique +
            // ordered), threaded as (previous-value+1 <= v) via ltb on prev.
            (
                "mir_arms_ok_from",
                "Nat -> Nat -> ListType MirArm -> Bool",
                "fun (bound : Nat) (lo : Nat) (l : ListType MirArm) => \
                 ListType.rec MirArm (fun (_ : ListType MirArm) => Nat -> Bool) \
                 (fun (_ : Nat) => Bool.true) \
                 (fun (a : MirArm) (rest : ListType MirArm) (ih : Nat -> Bool) => \
                 fun (lo2 : Nat) => MirArm.rec (fun (_ : MirArm) => Bool) \
                 (fun (v : Nat) (ident : Bool) => mir_band (mir_arm_ok bound (MirArm.mk v ident)) \
                 (mir_band (mir_nat_ltb lo2 (Nat.succ v)) \
                 (ih (Nat.succ v)))) a) l lo"
                    .to_string(),
            ),
            // A WILDCARD-terminated dispatch (whnf_core_inner) needs a different
            // predicate: its explicit arms are plain variants with no
            // identity/conditional distinction, so `mir_arm_ok`'s "non-identity
            // implies v = 1" rule — correct for whnf_impl — would wrongly reject
            // them. Same in-range + STRICTLY-INCREASING check over a bare
            // `ListType Nat`.
            (
                "mir_variants_ok_from",
                "Nat -> Nat -> ListType Nat -> Bool",
                "fun (bound : Nat) (lo : Nat) (l : ListType Nat) => \
                 ListType.rec Nat (fun (_ : ListType Nat) => Nat -> Bool) \
                 (fun (_ : Nat) => Bool.true) \
                 (fun (v : Nat) (rest : ListType Nat) (ih : Nat -> Bool) => \
                 fun (lo2 : Nat) => mir_band (mir_nat_ltb v bound) \
                 (mir_band (mir_nat_ltb lo2 (Nat.succ v)) (ih (Nat.succ v)))) l lo"
                    .to_string(),
            ),
            // Length, so a capstone can pin HOW MANY variants are handled
            // explicitly — and therefore how many the wildcard absorbs.
            (
                "mir_nat_len",
                "ListType Nat -> Nat",
                "fun (l : ListType Nat) => \
                 ListType.rec Nat (fun (_ : ListType Nat) => Nat) Nat.zero \
                 (fun (_ : Nat) (_ : ListType Nat) (ih : Nat) => Nat.succ ih) l"
                    .to_string(),
            ),
        ];
        for (name, ty, value) in defs {
            self.add_definition_reducible(SpecDefinition {
                name: name.to_string(),
                type_src: ty.to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: format!(
                    "{name}: kernel-computable dispatch-arm partition checker component."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: None,
                axiom_deps: HashSet::new(),
            })?;
        }

        // THE CAPSTONE. Until now this module registered the dispatch-arm
        // vocabulary but asserted NOTHING with it — the partition was
        // kernel-checkABLE and never kernel-CHECKED. This closes that gap for
        // `whnf_impl`'s identity pre-match (clean-kernel/src/tc/whnf.rs:145-165).
        //
        // The reflected arm list, in the real match's variant order:
        //   0 BVar  identity      2 Sort  identity      6 Pi   identity
        //   1 FVar  CONDITIONAL   5 Lam   identity      8 Lit  identity
        // `ExprKind` has 25 variants (expr/kind.rs), so bound = 25.
        //
        // FVar is the one non-identity arm, and `mir_arm_ok` enforces exactly
        // that: an arm with `ident = false` must have `v = 1`. That is faithful
        // to the source — FVar returns early only for NON-let FVars, because a
        // let-FVar still needs zeta reduction, so it cannot be an unconditional
        // identity. `mir_is_identity_variant` independently pins the identity set
        // to {0,2,5,6,8}, which is precisely the source's unconditional arm
        // `Sort | Pi | Lam | Lit | BVar => return e.clone()`.
        //
        // `mir_arms_ok_from` additionally forces the values to be STRICTLY
        // INCREASING, so this witnesses a genuine partition — no duplicated and
        // no out-of-range variant can satisfy it.
        //
        // Proved by KERNEL COMPUTATION: `Eq.refl` forces the kernel to evaluate
        // `mir_arms_ok_from` (hence `mir_arm_ok`, `mir_is_identity_variant`,
        // `mir_nat_ltb`, `mir_nat_eqb`) on the encoding down to `Bool.true`.
        //
        // SCOPE, stated honestly: this is a structural fact about a SWITCH — no
        // recursion, no cache, no heartbeat, no state. It does NOT certify
        // `whnf_impl`'s behaviour, and the encoder's fidelity to the real MIR is
        // pinned on the trust-certify side, exactly as for the payload witness
        // above. See docs/plans/PHASE2_CHECKER_SPINE_SCOPE_2026-07-25.md.
        let arms = {
            let mut acc = "(ListType.nil MirArm)".to_string();
            for (variant, ident) in [
                (8, true),
                (6, true),
                (5, true),
                (2, true),
                (1, false),
                (0, true),
            ] {
                acc = format!(
                    "(ListType.cons MirArm (MirArm.mk {v} {flag}) {acc})",
                    v = nat_src(variant),
                    flag = if ident { "Bool.true" } else { "Bool.false" },
                );
            }
            acc
        };
        self.add_definition(SpecDefinition {
            name: "mir_dispatch_reflection_whnf_impl".to_string(),
            type_src: format!(
                "Eq Bool (mir_arms_ok_from {bound} Nat.zero {arms}) Bool.true",
                bound = nat_src(25),
            ),
            value_src: Some("Eq.refl Bool Bool.true".to_string()),
            is_axiom: false,
            description: concat!(
                "THE FIRST KERNEL-CHECKED DISPATCH WITNESS ON THE SPINE: the encoded ",
                "identity pre-match of the real whnf_impl (tc/whnf.rs:145-165) SATISFIES the ",
                "dispatch-partition predicate — every arm's ExprKind variant is in range ",
                "(< 25), the identity flags agree with mir_is_identity_variant on {0,2,5,6,8} ",
                "= {BVar,Sort,Lam,Pi,Lit} (the source's unconditional early-return arm), FVar ",
                "(1) is the single CONDITIONAL arm (a let-FVar still needs zeta, so it cannot ",
                "be an unconditional identity), and the variant values are STRICTLY INCREASING ",
                "so the arm set is a genuine partition. Proved by KERNEL COMPUTATION (Eq.refl: ",
                "the kernel evaluates mir_arms_ok_from on the encoding to Bool.true). This is a ",
                "structural fact about a SWITCH — no recursion, cache, heartbeat or state — and ",
                "does NOT certify whnf_impl's behaviour; encoder fidelity to the real MIR is ",
                "pinned trust-certify-side. Phase-2 first step. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "mir_arms_ok_from".to_string(),
                "mir_arm_ok".to_string(),
                "mir_is_identity_variant".to_string(),
                "mir_nat_ltb".to_string(),
                "MirArm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // SECOND SPINE WITNESS: whnf_core_inner's dispatch (tc/whnf.rs:419-582).
        // Unlike whnf_impl's pre-match this one is WILDCARD-terminated, so the
        // checkable content is which variants get EXPLICIT arms and, by
        // complement, how many fall through.
        //
        // The 10 explicit arms, canonically sorted (the source's match order is
        // 4,7,3,1,9,10,18,21,20,19 — Rust match arms over distinct variants are
        // order-independent, so the SET is the invariant, not the listing order):
        //   1  FVar            9  Proj              19 CubicalHComp
        //   3  Const          10  MData             20 CubicalTransp
        //   4  App            18  CubicalPathApp    21 CubicalCoe
        //   7  Let
        // so the wildcard absorbs the other 15 of 25 variants:
        //   {0,2,5,6,8} u {11..17} u {22,23,24}
        // — note {0,2,5,6,8} is exactly whnf_impl's identity set above, which is
        // the consistency one would want between the two dispatches: what the
        // pre-match early-returns is what the core leaves Done.
        //
        // The conjunction pins the arm set EXACTLY: in-range + strictly
        // increasing (hence distinct) AND a length of 10. Dropping a real arm
        // still satisfies the ordering check but breaks the length, and adding a
        // spurious one breaks it the other way — so neither can slip through.
        let core_variants = {
            let mut acc = "(ListType.nil Nat)".to_string();
            for v in [21, 20, 19, 18, 10, 9, 7, 4, 3, 1] {
                acc = format!("(ListType.cons Nat {v} {acc})", v = nat_src(v));
            }
            acc
        };
        self.add_definition(SpecDefinition {
            name: "mir_dispatch_reflection_whnf_core_inner".to_string(),
            type_src: format!(
                "Eq Bool (mir_band (mir_variants_ok_from {bound} Nat.zero {core_variants}) \
                 (mir_nat_eqb (mir_nat_len {core_variants}) {ten})) Bool.true",
                bound = nat_src(25),
                ten = nat_src(10),
            ),
            value_src: Some("Eq.refl Bool Bool.true".to_string()),
            is_axiom: false,
            description: concat!(
                "SECOND KERNEL-CHECKED DISPATCH WITNESS ON THE SPINE: the encoded explicit-arm ",
                "set of the real whnf_core_inner (tc/whnf.rs:419-582) is exactly ",
                "{1 FVar, 3 Const, 4 App, 7 Let, 9 Proj, 10 MData, 18 CubicalPathApp, ",
                "19 CubicalHComp, 20 CubicalTransp, 21 CubicalCoe} — every variant in range ",
                "(< 25), strictly increasing (hence distinct), and EXACTLY 10 of them, so the ",
                "wildcard provably absorbs the remaining 15. The length conjunct is what makes ",
                "this pin the set rather than merely a sorted sublist: dropping a real arm keeps ",
                "the ordering valid but breaks the count. Proved by KERNEL COMPUTATION (Eq.refl ",
                "forces evaluation of mir_variants_ok_from / mir_nat_len / mir_nat_ltb / ",
                "mir_nat_eqb on the encoding). Structural fact about a SWITCH — no recursion, ",
                "cache, heartbeat or state; does NOT certify whnf_core_inner's behaviour, and ",
                "encoder fidelity to the real MIR stays pinned trust-certify-side. Phase-2 ",
                "second step. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "mir_variants_ok_from".to_string(),
                "mir_nat_len".to_string(),
                "mir_nat_ltb".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `whnf_progress_bd`. Structural `KExpr.rec` with motive
/// `fun e => bvar_ceiling e = 0 -> const_free e -> whnf_progress_result e`.
/// Arm order matches the `KExpr` constructor order: sort, bvar, app, lam, pi,
/// const, let_, proj, lit (fields then IHs for every recursive arm).
fn whnf_progress_bd_proof() -> String {
    concat!(
        "fun (e0 : KExpr) (hceil0 : Eq Nat (bvar_ceiling e0) Nat.zero) ",
        "(hcf0 : const_free e0) => ",
        "KExpr.rec ",
        "(fun (e : KExpr) => Eq Nat (bvar_ceiling e) Nat.zero -> const_free e -> ",
        "whnf_progress_result e) ",
        // sort n
        "(fun (n : Level) (_hceil : Eq Nat (bvar_ceiling (KExpr.sort n)) Nat.zero) ",
        "(_hcf : const_free (KExpr.sort n)) => ",
        "whnf_progress_result.done (KExpr.sort n) (is_whnf.sort n)) ",
        // bvar i — ceiling (bvar i) = succ i, refuted by nat_zero_ne_succ.
        "(fun (i : Nat) (hceil : Eq Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero) ",
        "(_hcf : const_free (KExpr.bvar i)) => ",
        "nat_zero_ne_succ i (whnf_progress_result (KExpr.bvar i)) ",
        "(Eq.symm Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero hceil)) ",
        // app f a — recurse on the head f, dispatch on its progress result.
        "(fun (f : KExpr) (a : KExpr) ",
        "(ihf : Eq Nat (bvar_ceiling f) Nat.zero -> const_free f -> whnf_progress_result f) ",
        "(_iha : Eq Nat (bvar_ceiling a) Nat.zero -> const_free a -> whnf_progress_result a) ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) ",
        "(hcf : const_free (KExpr.app f a)) => ",
        "whnf_progress_result.rec ",
        "(fun (e : KExpr) (_ : whnf_progress_result e) => ",
        "whnf_progress_result (KExpr.app e a)) ",
        // done arm: case on is_whnf of the head.
        "(fun (e : KExpr) (w : is_whnf e) => ",
        "is_whnf.rec ",
        "(fun (x : KExpr) (_ : is_whnf x) => whnf_progress_result (KExpr.app x a)) ",
        // is_whnf.sort n -> stuck (sort head)
        "(fun (n : Level) => ",
        "whnf_progress_result.stuck (KExpr.sort n) a (whnf_stuck_head.sort n)) ",
        // is_whnf.lam ty body -> step (beta redex fires)
        "(fun (ty : KExpr) (body : KExpr) => ",
        "whnf_progress_result.step (KExpr.app (KExpr.lam ty body) a) (instantiate body a) ",
        "(beta_reduces_bd.beta ty body a)) ",
        // is_whnf.pi ty body -> stuck (pi head)
        "(fun (ty : KExpr) (body : KExpr) => ",
        "whnf_progress_result.stuck (KExpr.pi ty body) a (whnf_stuck_head.pi ty body)) ",
        // is_whnf.neutral x hn -> done (neutral application spine)
        "(fun (x : KExpr) (hn : is_neutral x) => ",
        "whnf_progress_result.done (KExpr.app x a) ",
        "(is_whnf.neutral (KExpr.app x a) (is_neutral.app x a hn))) ",
        // is_whnf.proj ps pidx psub w -> stuck (a projection head is non-lambda whnf,
        // so the application is stuck: whnf_stuck_head.projw over the is_whnf scrutinee).
        "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (wsub : is_whnf psub) ",
        "(_ih : whnf_progress_result (KExpr.app psub a)) => ",
        "whnf_progress_result.stuck (KExpr.proj ps pidx psub) a ",
        "(whnf_stuck_head.projw ps pidx psub wsub)) ",
        // is_whnf.lit v -> stuck (a literal head is non-lambda whnf: whnf_stuck_head.lit).
        "(fun (v : Nat) => ",
        "whnf_progress_result.stuck (KExpr.lit v) a (whnf_stuck_head.lit v)) ",
        "e w) ",
        // step arm: head steps, lift through app_left congruence.
        "(fun (e : KExpr) (e' : KExpr) (hs : beta_reduces_bd e e') => ",
        "whnf_progress_result.step (KExpr.app e a) (KExpr.app e' a) ",
        "(beta_reduces_bd.app_left e e' a hs)) ",
        // stuck arm: head is itself a stuck application spine.
        "(fun (g : KExpr) (b : KExpr) (hg : whnf_stuck_head g) => ",
        "whnf_progress_result.stuck (KExpr.app g b) a (whnf_stuck_head.app g b hg)) ",
        // stuck_proj arm (proj/lit rung): head is a stuck projection, so the whole
        // application is stuck (whnf_stuck_head.proj lifts the stuck scrutinee-proj).
        "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (hsh : whnf_stuck_head psub) => ",
        "whnf_progress_result.stuck (KExpr.proj ps pidx psub) a ",
        "(whnf_stuck_head.proj ps pidx psub hsh)) ",
        // index + major: recurse on f with its ceiling/const-free projections.
        "f ",
        "(ihf (nat_add_eq_zero_left (bvar_ceiling f) (bvar_ceiling a) hceil) ",
        "(AndType.left (const_free f) (const_free a) hcf))) ",
        // lam ty body
        "(fun (ty : KExpr) (body : KExpr) ",
        "(_ihty : Eq Nat (bvar_ceiling ty) Nat.zero -> const_free ty -> ",
        "whnf_progress_result ty) ",
        "(_ihbody : Eq Nat (bvar_ceiling body) Nat.zero -> const_free body -> ",
        "whnf_progress_result body) ",
        "(_hceil : Eq Nat (bvar_ceiling (KExpr.lam ty body)) Nat.zero) ",
        "(_hcf : const_free (KExpr.lam ty body)) => ",
        "whnf_progress_result.done (KExpr.lam ty body) (is_whnf.lam ty body)) ",
        // pi ty body
        "(fun (ty : KExpr) (body : KExpr) ",
        "(_ihty : Eq Nat (bvar_ceiling ty) Nat.zero -> const_free ty -> ",
        "whnf_progress_result ty) ",
        "(_ihbody : Eq Nat (bvar_ceiling body) Nat.zero -> const_free body -> ",
        "whnf_progress_result body) ",
        "(_hceil : Eq Nat (bvar_ceiling (KExpr.pi ty body)) Nat.zero) ",
        "(_hcf : const_free (KExpr.pi ty body)) => ",
        "whnf_progress_result.done (KExpr.pi ty body) (is_whnf.pi ty body)) ",
        // const nm us — const_free (const nm us) reduces to Empty.
        "(fun (nm : Name) (us : ListType Level) ",
        "(_hceil : Eq Nat (bvar_ceiling (KExpr.const nm us)) Nat.zero) ",
        "(hcf : const_free (KExpr.const nm us)) => ",
        "Empty.rec (fun (_ : Empty) => whnf_progress_result (KExpr.const nm us)) hcf) ",
        // let_ ty val body — always a zeta redex: step via beta_reduces_bd.zeta
        // (a let_ is never a whnf/neutral; the IHs are unused).
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
        "(_ihty : Eq Nat (bvar_ceiling ty) Nat.zero -> const_free ty -> ",
        "whnf_progress_result ty) ",
        "(_ihval : Eq Nat (bvar_ceiling val) Nat.zero -> const_free val -> ",
        "whnf_progress_result val) ",
        "(_ihbody : Eq Nat (bvar_ceiling body) Nat.zero -> const_free body -> ",
        "whnf_progress_result body) ",
        "(_hceil : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) ",
        "(_hcf : const_free (KExpr.let_ ty val body)) => ",
        "whnf_progress_result.step (KExpr.let_ ty val body) (instantiate body val) ",
        "(beta_reduces_bd.zeta ty val body)) ",
        // proj s i sub (proj/lit rung): recurse on the scrutinee, dispatch its result.
        // bvar_ceiling/const_free reduce through proj (defeq), so hceil/hcf feed ihsub
        // directly. done -> is_whnf.proj; step -> beta_reduces_bd.proj; stuck (app or
        // proj head) -> stuck_proj (the projection over a stuck scrutinee is stuck).
        "(fun (s : Name) (i : Nat) (sub : KExpr) ",
        "(ihsub : Eq Nat (bvar_ceiling sub) Nat.zero -> const_free sub -> whnf_progress_result sub) ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.proj s i sub)) Nat.zero) ",
        "(hcf : const_free (KExpr.proj s i sub)) => ",
        "whnf_progress_result.rec ",
        "(fun (e : KExpr) (_ : whnf_progress_result e) => whnf_progress_result (KExpr.proj s i e)) ",
        "(fun (e : KExpr) (w : is_whnf e) => ",
        "whnf_progress_result.done (KExpr.proj s i e) (is_whnf.proj s i e w)) ",
        "(fun (e : KExpr) (e' : KExpr) (hs : beta_reduces_bd e e') => ",
        "whnf_progress_result.step (KExpr.proj s i e) (KExpr.proj s i e') ",
        "(beta_reduces_bd.proj s i e e' hs)) ",
        "(fun (g : KExpr) (b : KExpr) (hg : whnf_stuck_head g) => ",
        "whnf_progress_result.stuck_proj s i (KExpr.app g b) (whnf_stuck_head.app g b hg)) ",
        "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (hsh : whnf_stuck_head psub) => ",
        "whnf_progress_result.stuck_proj s i (KExpr.proj ps pidx psub) (whnf_stuck_head.proj ps pidx psub hsh)) ",
        "sub (ihsub hceil hcf)) ",
        // lit v (proj/lit rung): a literal is a WHNF leaf (is_whnf.lit).
        "(fun (v : Nat) ",
        "(_hceil : Eq Nat (bvar_ceiling (KExpr.lit v)) Nat.zero) ",
        "(_hcf : const_free (KExpr.lit v)) => ",
        "whnf_progress_result.done (KExpr.lit v) (is_whnf.lit v)) ",
        // motive indices + majors
        "e0 hceil0 hcf0"
    )
    .to_string()
}

const DELTA_LIFT_VALUE: &str = "fun (env : DefEnv) (f : KExpr) (a : KExpr) (f2 : KExpr) (hd : Eq (OptionType KExpr) (delta_reduct env f) (OptionType.some KExpr f2)) => OptionType.rec Name (fun (o1 : OptionType Name) => Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) o1 -> Eq (OptionType KExpr) (opt_bind Name KExpr o1 (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2)))) (OptionType.some KExpr f2) -> Eq (OptionType KExpr) (delta_reduct env (KExpr.app f a)) (OptionType.some KExpr (KExpr.app f2 a))) (fun (_h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.none Name)) (hd1 : Eq (OptionType KExpr) (opt_bind Name KExpr (OptionType.none Name) (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2)))) (OptionType.some KExpr f2)) => option_none_ne_some KExpr f2 (Eq (OptionType KExpr) (delta_reduct env (KExpr.app f a)) (OptionType.some KExpr (KExpr.app f2 a))) hd1) (fun (dn : Name) (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name dn)) (hd1 : Eq (OptionType KExpr) (opt_bind Name KExpr (OptionType.some Name dn) (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2)))) (OptionType.some KExpr f2)) => OptionType.rec KExpr (fun (o2 : OptionType KExpr) => Eq (OptionType KExpr) (defval_for env dn) o2 -> Eq (OptionType KExpr) (opt_bind KExpr KExpr o2 (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2))) (OptionType.some KExpr f2) -> Eq (OptionType KExpr) (delta_reduct env (KExpr.app f a)) (OptionType.some KExpr (KExpr.app f2 a))) (fun (_h2 : Eq (OptionType KExpr) (defval_for env dn) (OptionType.none KExpr)) (hd2 : Eq (OptionType KExpr) (opt_bind KExpr KExpr (OptionType.none KExpr) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2))) (OptionType.some KExpr f2)) => option_none_ne_some KExpr f2 (Eq (OptionType KExpr) (delta_reduct env (KExpr.app f a)) (OptionType.some KExpr (KExpr.app f2 a))) hd2) (fun (val : KExpr) (h2 : Eq (OptionType KExpr) (defval_for env dn) (OptionType.some KExpr val)) (hd2 : Eq (OptionType KExpr) (opt_bind KExpr KExpr (OptionType.some KExpr val) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2))) (OptionType.some KExpr f2)) => Eq.trans (OptionType KExpr) (delta_reduct env (KExpr.app f a)) (OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val)) (OptionType.some KExpr (KExpr.app f2 a)) (Eq.trans (OptionType KExpr) (delta_reduct env (KExpr.app f a)) (opt_bind KExpr KExpr (defval_for env dn) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val2))) (OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val)) (Eq.rec (OptionType Name) (kexpr_const_name (kapp_fn f)) (fun (o1b : OptionType Name) (_hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) o1b) => Eq (OptionType KExpr) (opt_bind Name KExpr (kexpr_const_name (kapp_fn f)) (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val2)))) (opt_bind Name KExpr o1b (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val2))))) (Eq.refl (OptionType KExpr) (opt_bind Name KExpr (kexpr_const_name (kapp_fn f)) (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val2))))) (OptionType.some Name dn) h1) (Eq.rec (OptionType KExpr) (defval_for env dn) (fun (o2b : OptionType KExpr) (_hh : Eq (OptionType KExpr) (defval_for env dn) o2b) => Eq (OptionType KExpr) (opt_bind KExpr KExpr (defval_for env dn) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val2))) (opt_bind KExpr KExpr o2b (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val2)))) (Eq.refl (OptionType KExpr) (opt_bind KExpr KExpr (defval_for env dn) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val2)))) (OptionType.some KExpr val) h2)) (Eq.rec KExpr (KExpr.app (apply_spine (kapp_args f) val) a) (fun (x : KExpr) (_hx : Eq KExpr (KExpr.app (apply_spine (kapp_args f) val) a) x) => Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val)) (OptionType.some KExpr x)) (Eq.rec KExpr (apply_spine (kapp_args (KExpr.app f a)) val) (fun (y : KExpr) (_hy : Eq KExpr (apply_spine (kapp_args (KExpr.app f a)) val) y) => Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val)) (OptionType.some KExpr y)) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args (KExpr.app f a)) val))) (KExpr.app (apply_spine (kapp_args f) val) a) (apply_spine_append_one (kapp_args f) a val)) (KExpr.app f2 a) (Eq.rec KExpr (apply_spine (kapp_args f) val) (fun (z : KExpr) (_hz : Eq KExpr (apply_spine (kapp_args f) val) z) => Eq KExpr (KExpr.app (apply_spine (kapp_args f) val) a) (KExpr.app z a)) (Eq.refl KExpr (KExpr.app (apply_spine (kapp_args f) val) a)) f2 (option_some_inj KExpr (apply_spine (kapp_args f) val) f2 hd2)))) (defval_for env dn) (Eq.refl (OptionType KExpr) (defval_for env dn)) hd1) (kexpr_const_name (kapp_fn f)) (Eq.refl (OptionType Name) (kexpr_const_name (kapp_fn f))) hd";

impl Specification {
    /// X13b — FULL δ-PROGRESS as a kernel theorem: the `KExpr.rec` assembly of
    /// `whnf_progress_env_bd` over `consts_defined` terms, gluing the landed
    /// const-free machinery (ceiling splits, is_whnf head analysis), the X13a
    /// const case, and the contextual app/proj lifts that carry any child
    /// β/δ step into the current nine-constructor KExpr surface.
    fn add_whnf_env_progress_full(&mut self) -> Result<(), SpecError> {
        // Independently useful Type-targeted option no-confusion: none ≠ some,
        // eliminating into ANY Type (the registered option_none_ne_some is
        // Prop-limited). Retained as X13b support for explicit delta_reduct
        // inversions even though the full theorem now uses contextual steps.
        self.add_recursive_def(
            r"def opt_none_discr (α : Type) (o : OptionType α) : Type := OptionType.rec α (fun (_o : OptionType α) => Type) ConstFreeUnit (fun (_x : α) => Empty) o",
            "opt_none_discr α o: ConstFreeUnit at none, Empty at some — the reversed              named discriminator behind the independently useful Type-targeted              none≠some support for explicit delta_reduct inversions (X13b).",
        )?;
        self.add_definition(SpecDefinition {
            name: "opt_none_ne_some_t".to_string(),
            type_src: concat!(
                "forall (α : Type) (r : α) (C : Type), ",
                "Eq (OptionType α) (OptionType.none α) (OptionType.some α r) -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (α : Type) (r : α) (C : Type) ",
                    "(h : Eq (OptionType α) (OptionType.none α) (OptionType.some α r)) => ",
                    "Empty.rec (fun (_e : Empty) => C) ",
                    "(Eq.rec (OptionType α) (OptionType.none α) ",
                    "(fun (o : OptionType α) (_h : Eq (OptionType α) (OptionType.none α) o) => opt_none_discr α o) ",
                    "ConstFreeUnit.triv (OptionType.some α r) h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Independent Type-targeted option no-confusion support (X13b): from none = some r conclude ",
                "anything in Type — transport ConstFreeUnit.triv through the reversed ",
                "discriminator to inhabit Empty, then eliminate. The Prop-limited ",
                "option_none_ne_some cannot serve Type-valued progress goals. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_none_discr".to_string(),
                "Empty.rec".to_string(),
                "Eq.rec".to_string(),
                "ConstFreeUnit.triv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // THE FULL δ-PROGRESS THEOREM.
        self.add_definition(SpecDefinition {
            name: "whnf_progress_env_bd".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (e : KExpr), ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> ",
                "whnf_progress_result_env env e"
            )
            .to_string(),
            value_src: Some(whnf_progress_env_bd_proof()),
            is_axiom: false,
            description: concat!(
                "FULL δ-PROGRESS (DeltaProgress spec-port X13b): the const/application core is ",
                "guide-validated foreign-side by the Aristotle delta_progress proof and locally ",
                "extended to the current projection/literal surface. Every bvar-free KExpr whose constants ",
                "are all defined is a weak-head value, takes a whnf_env_step (β/ζ or δ), ",
                "or is an honestly stuck application/projection — by the current nine-arm ",
                "KExpr.rec. The const case is X13a const_progress_env; the app and projection ",
                "cases dispatch on child progress and lift every β/δ step through the matching ",
                "whnf_env_step contextual constructor; literals are landed WHNF values. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "consts_defined".to_string(),
                "const_progress_env".to_string(),
                "KExpr".to_string(),
                "KExpr.rec".to_string(),
                "whnf_progress_result_env".to_string(),
                "whnf_progress_result_env.rec".to_string(),
                "whnf_progress_result_env.done".to_string(),
                "whnf_progress_result_env.step".to_string(),
                "whnf_progress_result_env.stuck".to_string(),
                "whnf_progress_result_env.stuck_proj".to_string(),
                "whnf_env_step".to_string(),
                "whnf_env_step.beta".to_string(),
                "whnf_env_step.app_left".to_string(),
                "whnf_env_step.proj".to_string(),
                "is_whnf".to_string(),
                "is_whnf.rec".to_string(),
                "is_whnf.sort".to_string(),
                "is_whnf.lam".to_string(),
                "is_whnf.pi".to_string(),
                "is_whnf.neutral".to_string(),
                "is_whnf.proj".to_string(),
                "is_whnf.lit".to_string(),
                "is_neutral".to_string(),
                "is_neutral.app".to_string(),
                "whnf_stuck_head".to_string(),
                "whnf_stuck_head.sort".to_string(),
                "whnf_stuck_head.pi".to_string(),
                "whnf_stuck_head.app".to_string(),
                "whnf_stuck_head.proj".to_string(),
                "whnf_stuck_head.projw".to_string(),
                "whnf_stuck_head.lit".to_string(),
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd.beta".to_string(),
                "beta_reduces_bd.zeta".to_string(),
                "instantiate".to_string(),
                "bvar_ceiling".to_string(),
                "nat_add_eq_zero_left".to_string(),
                "nat_zero_ne_succ".to_string(),
                "AndType".to_string(),
                "AndType.left".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// The X13b proof term: `whnf_progress_bd_proof` adapted to the δ-aware
/// result over `consts_defined`, including the current projection/literal
/// cases and contextual app/projection step lifts.
fn whnf_progress_env_bd_proof() -> String {
    concat!(
        "fun (env : DefEnv) (e0 : KExpr) ",
        "(hceil0 : Eq Nat (bvar_ceiling e0) Nat.zero) ",
        "(hcd0 : consts_defined env e0) => ",
        "KExpr.rec ",
        "(fun (e : KExpr) => Eq Nat (bvar_ceiling e) Nat.zero -> consts_defined env e -> ",
        "whnf_progress_result_env env e) ",
        // sort n
        "(fun (n : Level) (_hceil : Eq Nat (bvar_ceiling (KExpr.sort n)) Nat.zero) ",
        "(_hcd : consts_defined env (KExpr.sort n)) => ",
        "whnf_progress_result_env.done env (KExpr.sort n) (is_whnf.sort n)) ",
        // bvar i
        "(fun (i : Nat) (hceil : Eq Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero) ",
        "(_hcd : consts_defined env (KExpr.bvar i)) => ",
        "nat_zero_ne_succ i (whnf_progress_result_env env (KExpr.bvar i)) ",
        "(Eq.symm Nat (bvar_ceiling (KExpr.bvar i)) Nat.zero hceil)) ",
        // app f a
        "(fun (f : KExpr) (a : KExpr) ",
        "(ihf : Eq Nat (bvar_ceiling f) Nat.zero -> consts_defined env f -> ",
        "whnf_progress_result_env env f) ",
        "(_iha : Eq Nat (bvar_ceiling a) Nat.zero -> consts_defined env a -> ",
        "whnf_progress_result_env env a) ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) ",
        "(hcd : consts_defined env (KExpr.app f a)) => ",
        "whnf_progress_result_env.rec env ",
        "(fun (x : KExpr) (_r : whnf_progress_result_env env x) => ",
        "whnf_progress_result_env env (KExpr.app x a)) ",
        // done arm: is_whnf head analysis
        "(fun (x : KExpr) (w : is_whnf x) => ",
        "is_whnf.rec ",
        "(fun (y : KExpr) (_w : is_whnf y) => whnf_progress_result_env env (KExpr.app y a)) ",
        "(fun (n : Level) => ",
        "whnf_progress_result_env.stuck env (KExpr.sort n) a (whnf_stuck_head.sort n)) ",
        "(fun (ty : KExpr) (body : KExpr) => ",
        "whnf_progress_result_env.step env (KExpr.app (KExpr.lam ty body) a) (instantiate body a) ",
        "(whnf_env_step.beta env (KExpr.app (KExpr.lam ty body) a) (instantiate body a) ",
        "(beta_reduces_bd.beta ty body a))) ",
        "(fun (ty : KExpr) (body : KExpr) => ",
        "whnf_progress_result_env.stuck env (KExpr.pi ty body) a (whnf_stuck_head.pi ty body)) ",
        "(fun (y : KExpr) (hn : is_neutral y) => ",
        "whnf_progress_result_env.done env (KExpr.app y a) ",
        "(is_whnf.neutral (KExpr.app y a) (is_neutral.app y a hn))) ",
        // A projection head is a non-lambda WHNF, hence application is stuck.
        "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (wsub : is_whnf psub) ",
        "(_ih : whnf_progress_result_env env (KExpr.app psub a)) => ",
        "whnf_progress_result_env.stuck env (KExpr.proj ps pidx psub) a ",
        "(whnf_stuck_head.projw ps pidx psub wsub)) ",
        // A literal head is likewise a non-lambda WHNF.
        "(fun (v : Nat) => ",
        "whnf_progress_result_env.stuck env (KExpr.lit v) a (whnf_stuck_head.lit v)) ",
        "x w) ",
        // Any head step lifts through the application context, including a
        // projection-context step whose scrutinee took δ.
        "(fun (x : KExpr) (e2 : KExpr) (hs : whnf_env_step env x e2) => ",
        "whnf_progress_result_env.step env (KExpr.app x a) (KExpr.app e2 a) ",
        "(whnf_env_step.app_left env x e2 a hs)) ",
        // stuck arm
        "(fun (g : KExpr) (b : KExpr) (hg : whnf_stuck_head g) => ",
        "whnf_progress_result_env.stuck env (KExpr.app g b) a (whnf_stuck_head.app g b hg)) ",
        // A projection already classified as stuck remains a stuck head
        // when applied.
        "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (hsh : whnf_stuck_head psub) => ",
        "whnf_progress_result_env.stuck env (KExpr.proj ps pidx psub) a ",
        "(whnf_stuck_head.proj ps pidx psub hsh)) ",
        // major: recurse on f with projections
        "f ",
        "(ihf (nat_add_eq_zero_left (bvar_ceiling f) (bvar_ceiling a) hceil) ",
        "(AndType.left (consts_defined env f) (consts_defined env a) hcd))) ",
        // lam ty body
        "(fun (ty : KExpr) (body : KExpr) ",
        "(_ihty : Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> ",
        "whnf_progress_result_env env ty) ",
        "(_ihbody : Eq Nat (bvar_ceiling body) Nat.zero -> consts_defined env body -> ",
        "whnf_progress_result_env env body) ",
        "(_hceil : Eq Nat (bvar_ceiling (KExpr.lam ty body)) Nat.zero) ",
        "(_hcd : consts_defined env (KExpr.lam ty body)) => ",
        "whnf_progress_result_env.done env (KExpr.lam ty body) (is_whnf.lam ty body)) ",
        // pi ty body
        "(fun (ty : KExpr) (body : KExpr) ",
        "(_ihty : Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> ",
        "whnf_progress_result_env env ty) ",
        "(_ihbody : Eq Nat (bvar_ceiling body) Nat.zero -> consts_defined env body -> ",
        "whnf_progress_result_env env body) ",
        "(_hceil : Eq Nat (bvar_ceiling (KExpr.pi ty body)) Nat.zero) ",
        "(_hcd : consts_defined env (KExpr.pi ty body)) => ",
        "whnf_progress_result_env.done env (KExpr.pi ty body) (is_whnf.pi ty body)) ",
        // const nm us — THE X13a THEOREM
        "(fun (nm : Name) (us : ListType Level) ",
        "(_hceil : Eq Nat (bvar_ceiling (KExpr.const nm us)) Nat.zero) ",
        "(hcd : consts_defined env (KExpr.const nm us)) => ",
        "const_progress_env env nm us hcd) ",
        // let_ ty val body — zeta via the beta embedding
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
        "(_ihty : Eq Nat (bvar_ceiling ty) Nat.zero -> consts_defined env ty -> ",
        "whnf_progress_result_env env ty) ",
        "(_ihval : Eq Nat (bvar_ceiling val) Nat.zero -> consts_defined env val -> ",
        "whnf_progress_result_env env val) ",
        "(_ihbody : Eq Nat (bvar_ceiling body) Nat.zero -> consts_defined env body -> ",
        "whnf_progress_result_env env body) ",
        "(_hceil : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) ",
        "(_hcd : consts_defined env (KExpr.let_ ty val body)) => ",
        "whnf_progress_result_env.step env (KExpr.let_ ty val body) (instantiate body val) ",
        "(whnf_env_step.beta env (KExpr.let_ ty val body) (instantiate body val) ",
        "(beta_reduces_bd.zeta ty val body))) ",
        // proj s i sub: recurse on the scrutinee and preserve every
        // env-aware progress shape under the projection context.
        "(fun (s : Name) (i : Nat) (sub : KExpr) ",
        "(ihsub : Eq Nat (bvar_ceiling sub) Nat.zero -> consts_defined env sub -> ",
        "whnf_progress_result_env env sub) ",
        "(hceil : Eq Nat (bvar_ceiling (KExpr.proj s i sub)) Nat.zero) ",
        "(hcd : consts_defined env (KExpr.proj s i sub)) => ",
        "whnf_progress_result_env.rec env ",
        "(fun (x : KExpr) (_r : whnf_progress_result_env env x) => ",
        "whnf_progress_result_env env (KExpr.proj s i x)) ",
        "(fun (x : KExpr) (w : is_whnf x) => ",
        "whnf_progress_result_env.done env (KExpr.proj s i x) (is_whnf.proj s i x w)) ",
        "(fun (x : KExpr) (x2 : KExpr) (hs : whnf_env_step env x x2) => ",
        "whnf_progress_result_env.step env (KExpr.proj s i x) (KExpr.proj s i x2) ",
        "(whnf_env_step.proj env s i x x2 hs)) ",
        "(fun (g : KExpr) (b : KExpr) (hg : whnf_stuck_head g) => ",
        "whnf_progress_result_env.stuck_proj env s i (KExpr.app g b) ",
        "(whnf_stuck_head.app g b hg)) ",
        "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (hsh : whnf_stuck_head psub) => ",
        "whnf_progress_result_env.stuck_proj env s i (KExpr.proj ps pidx psub) ",
        "(whnf_stuck_head.proj ps pidx psub hsh)) ",
        "sub (ihsub hceil hcd)) ",
        // lit v is a WHNF leaf.
        "(fun (v : Nat) ",
        "(_hceil : Eq Nat (bvar_ceiling (KExpr.lit v)) Nat.zero) ",
        "(_hcd : consts_defined env (KExpr.lit v)) => ",
        "whnf_progress_result_env.done env (KExpr.lit v) (is_whnf.lit v)) ",
        "e0 hceil0 hcd0"
    )
    .to_string()
}

#[cfg(test)]
#[path = "whnf_progress_tests.rs"]
mod whnf_progress_tests;
