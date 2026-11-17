// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R0 of the candidate-model construction ladder: the candidate-SET interface
//! `IsCandSet` (Girard/Tait cr1/cr2/cr3 over an arbitrary term set
//! `S : KExpr -> Type`), its base instance `isCand_whnfAcc` (the whole-SN set),
//! the candidate-space floor `cand_var_mem` (every variable inhabits every
//! candidate set), and the two §6-mandated discriminating witnesses.
//!
//! Port of the corpus `Stratified/Cand.lean` `IsCand`/`isCand_SN`/
//! `IsCand.var_mem` (rung `stratified-sn`) to the spec's `KExpr` calculus,
//! per `designs/2026-08-23-spec-candmodel-port.md` §5 rung R0 / §7.
//!
//! ## Honesty notes (read before quoting)
//!
//! - **This is the candidate-SET interface, NOT a `CandModel` instance.**
//!   `IsCandSet` packages exactly the three per-set laws cr1/cr2/cr3; it has
//!   no `red_sort`, no `pi_elim`/`pi_intro`, no `redAbstraction`/`redLet`, no
//!   `redRec*`, no `redTypeStep`. In particular `isCand_whnfAcc` does NOT
//!   advance (let alone discharge) the `M : CandModel tenv` hypothesis of
//!   `whnf_terminates_well_typed_dependent`: the scoping note's §0.4 pincer is
//!   that the top set `Red := whnf_acc` REFUTES `pi_elim`, and `pi_elim` is
//!   deliberately not a face of `IsCandSet`. R0 is the model-independent
//!   toolbox layer the corpus keeps in `Cand.lean`, nothing more.
//! - **The step relation is the spec's FULL one-step reduction, env-fixed.**
//!   `whnf_step` = `beta_reduces` (top-level beta + zeta + iota via
//!   `iota_step (red_rec the_red_env)`, with congruence into every subterm
//!   slot) union `delta_reduces` at `red_def the_red_env` — pinned to the
//!   reflected kernel core env, NOT a parameter (scoping note verdict 3). So
//!   `whnf_acc` is genuine strong normalization for that fixed relation, and
//!   every `IsCandSet` face quantifies over it.
//! - **The laws quantify over UNTYPED terms.** `selfApp`/`omegaLoop` are
//!   well-formed `KExpr` syntax whether or not they are typable; typability is
//!   irrelevant to the candidate-set laws. `omegaLoop` beta-steps to ITSELF
//!   (`omega_step_self`, contractum pinned by `omega_inst_pin`), hence
//!   `omega_not_whnfAcc`, hence `cand_excludes_omega`: NO candidate set
//!   contains the loop — the cr1 face genuinely excludes (the §6.1 control:
//!   no automated gate checks a registration for degenerate content, so the
//!   discrimination is hand-registered here).
//! - **The positive witness goes THROUGH the interface.** `cand_var_witness`
//!   derives `whnf_acc (bvar 0)` by `cand_var_mem` at the base instance —
//!   exercising the cr3 face (which `Red := Empty`-style degenerates fail) at
//!   the irreducible neutral `bvar 0` (`no_whnf_step_bvar`), not by a direct
//!   `whnf_acc.intro`.
//! - **The cr3 FACE has its own witness, and it is not the projection.**
//!   `isCandSet_cr3` states the face expanded, so it concludes `S e` and not
//!   `candCr3 S`; before `candCr3_whnfAcc` nothing in the spec concluded
//!   `candCr3` at all, while `isCandSet_intro` assumes it. The
//!   premise-satisfiability gate found exactly that, and it is the same shape
//!   as the `hnf` capstone: an obligation no term is known to meet.
//! - **Interface encoding (R1 contract).** `IsCandSet S` is a REDUCIBLE plain
//!   def: `AndType (candCr1 S) (AndType (candCr2 S) (candCr3 S))` with the
//!   three faces themselves named Type-valued defs. Consume it with
//!   `isCandSet_cr1/cr2/cr3`, build it with `isCandSet_intro`. The faces
//!   mirror the corpus `IsCand` fields with `SN := whnf_acc`,
//!   `Step := whnf_step`, `Neutral :=` the spec's `Neutral`
//!   (`dependent_sn_richmodel.rs`: bvar/app/const/proj neutral; sort/lam/pi/
//!   let_/lit not).
//!
//! ## Census
//!
//! ZERO new axioms: every constant is value-bearing (plain defs via
//! `add_recursive_def`, theorems/witnesses via `add_definition` with kernel
//! `add_decl` checking). Census-neutral.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ================================================================
// Group A — the three candidate faces and the packaged interface.
// Corpus: Stratified/Cand.lean IsCand (:31-34).
// ================================================================

pub(super) const SRC_CAND_CR1: &str =
    "def candCr1 (S : KExpr -> Type) : Type := forall (e : KExpr), S e -> whnf_acc e";

pub(super) const SRC_CAND_CR2: &str = "def candCr2 (S : KExpr -> Type) : Type := forall (e : KExpr) (e2 : KExpr), S e -> whnf_step e e2 -> S e2";

pub(super) const SRC_CAND_CR3: &str = "def candCr3 (S : KExpr -> Type) : Type := forall (e : KExpr), Neutral e -> (forall (e2 : KExpr), whnf_step e e2 -> S e2) -> S e";

pub(super) const SRC_IS_CAND_SET: &str = "def IsCandSet (S : KExpr -> Type) : Type := AndType (candCr1 S) (AndType (candCr2 S) (candCr3 S))";

// ================================================================
// Group B — intro and the three projections (the R1 consumption API).
// ================================================================

pub(super) const TY_ISCANDSET_INTRO: &str =
    "forall (S : KExpr -> Type), candCr1 S -> candCr2 S -> candCr3 S -> IsCandSet S";
pub(super) const VAL_ISCANDSET_INTRO: &str = "fun (S : KExpr -> Type) (h1 : candCr1 S) (h2 : candCr2 S) (h3 : candCr3 S) => @AndType.intro (candCr1 S) (AndType (candCr2 S) (candCr3 S)) h1 (@AndType.intro (candCr2 S) (candCr3 S) h2 h3)";

pub(super) const TY_ISCANDSET_CR1: &str =
    "forall (S : KExpr -> Type), IsCandSet S -> forall (e : KExpr), S e -> whnf_acc e";
pub(super) const VAL_ISCANDSET_CR1: &str = "fun (S : KExpr -> Type) (hS : IsCandSet S) => AndType.left (candCr1 S) (AndType (candCr2 S) (candCr3 S)) hS";

pub(super) const TY_ISCANDSET_CR2: &str = "forall (S : KExpr -> Type), IsCandSet S -> forall (e : KExpr) (e2 : KExpr), S e -> whnf_step e e2 -> S e2";
pub(super) const VAL_ISCANDSET_CR2: &str = "fun (S : KExpr -> Type) (hS : IsCandSet S) => AndType.left (candCr2 S) (candCr3 S) (AndType.right (candCr1 S) (AndType (candCr2 S) (candCr3 S)) hS)";

pub(super) const TY_ISCANDSET_CR3: &str = "forall (S : KExpr -> Type), IsCandSet S -> forall (e : KExpr), Neutral e -> (forall (e2 : KExpr), whnf_step e e2 -> S e2) -> S e";
pub(super) const VAL_ISCANDSET_CR3: &str = "fun (S : KExpr -> Type) (hS : IsCandSet S) => AndType.right (candCr2 S) (candCr3 S) (AndType.right (candCr1 S) (AndType (candCr2 S) (candCr3 S)) hS)";

// ================================================================
// Group C — the base instance: the whole-SN set is a candidate set.
// Corpus: isCand_SN (Cand.lean:51-54).
// ================================================================

pub(super) const TY_WHNFACC_INV_STEP: &str =
    "forall (e : KExpr), whnf_acc e -> forall (e2 : KExpr), whnf_step e e2 -> whnf_acc e2";
pub(super) const VAL_WHNFACC_INV_STEP: &str = "fun (e : KExpr) (h : whnf_acc e) => @whnf_acc.rec (fun (e0 : KExpr) (_h : whnf_acc e0) => forall (e2 : KExpr), whnf_step e0 e2 -> whnf_acc e2) (fun (e0 : KExpr) (hsteps : forall (e1 : KExpr), whnf_step e0 e1 -> whnf_acc e1) (_ih : forall (e1 : KExpr), whnf_step e0 e1 -> forall (e2 : KExpr), whnf_step e1 e2 -> whnf_acc e2) => hsteps) e h";

pub(super) const TY_ISCAND_WHNFACC: &str = "IsCandSet (fun (e : KExpr) => whnf_acc e)";
pub(super) const VAL_ISCAND_WHNFACC: &str = "isCandSet_intro (fun (e : KExpr) => whnf_acc e) (fun (e : KExpr) (h : whnf_acc e) => h) (fun (e : KExpr) (e2 : KExpr) (h : whnf_acc e) (hs : whnf_step e e2) => whnfAcc_inv_step e h e2 hs) (fun (e : KExpr) (_hn : Neutral e) (hred : forall (e2 : KExpr), whnf_step e e2 -> whnf_acc e2) => whnf_acc.intro e hred)";

// The cr3 face at the base instance, kept in the FACE spelling rather than the
// expanded one. `isCandSet_cr3` concludes at `S e` (a bound variable applied),
// so nothing in the ladder concluded `candCr3` itself — the premise-
// satisfiability gate's finding, and its whole point: a face assumed by
// `isCandSet_intro` that no definition supplies is a face nothing is known to
// have. Projected out of `isCand_whnfAcc` with the package UNEXPANDED, so the
// conclusion IS `candCr3 <set>`.
pub(super) const TY_CANDCR3_WHNFACC: &str = "candCr3 (fun (e : KExpr) => whnf_acc e)";
pub(super) const VAL_CANDCR3_WHNFACC: &str = "AndType.right (candCr2 (fun (e : KExpr) => whnf_acc e)) (candCr3 (fun (e : KExpr) => whnf_acc e)) (AndType.right (candCr1 (fun (e : KExpr) => whnf_acc e)) (AndType (candCr2 (fun (e : KExpr) => whnf_acc e)) (candCr3 (fun (e : KExpr) => whnf_acc e))) isCand_whnfAcc)";

// The cr1 and cr2 faces at the same base instance, and for the same reason.
// `4b455add4` witnessed cr3 and stopped there, so `candCr1` and `candCr2` stayed
// assumed-by-`isCandSet_intro` and concluded by nothing — the premise gate's
// wave-4 finding. `isCandSet_cr1` states the face EXPANDED (its conclusion is
// `whnf_acc e`) and `isCandSet_cr2` concludes at `S e2`, so neither supplies the
// face itself. These are the SAME projections those two definitions already
// perform, with the package left unexpanded so the CONCLUSION is the face,
// applied to the proved base instance `isCand_whnfAcc`.
pub(super) const TY_CANDCR1_WHNFACC: &str = "candCr1 (fun (e : KExpr) => whnf_acc e)";
pub(super) const VAL_CANDCR1_WHNFACC: &str = "AndType.left (candCr1 (fun (e : KExpr) => whnf_acc e)) (AndType (candCr2 (fun (e : KExpr) => whnf_acc e)) (candCr3 (fun (e : KExpr) => whnf_acc e))) isCand_whnfAcc";

pub(super) const TY_CANDCR2_WHNFACC: &str = "candCr2 (fun (e : KExpr) => whnf_acc e)";
pub(super) const VAL_CANDCR2_WHNFACC: &str = "AndType.left (candCr2 (fun (e : KExpr) => whnf_acc e)) (candCr3 (fun (e : KExpr) => whnf_acc e)) (AndType.right (candCr1 (fun (e : KExpr) => whnf_acc e)) (AndType (candCr2 (fun (e : KExpr) => whnf_acc e)) (candCr3 (fun (e : KExpr) => whnf_acc e))) isCand_whnfAcc)";

// ================================================================
// Group D — the candidate-space floor: variables inhabit every candidate
// set. Corpus: IsCand.var_mem (Cand.lean:43-44).
// ================================================================

pub(super) const TY_CAND_VAR_MEM: &str =
    "forall (S : KExpr -> Type), IsCandSet S -> forall (i : Nat), S (KExpr.bvar i)";
pub(super) const VAL_CAND_VAR_MEM: &str = "fun (S : KExpr -> Type) (hS : IsCandSet S) (i : Nat) => isCandSet_cr3 S hS (KExpr.bvar i) ConstFreeUnit.triv (fun (e2 : KExpr) (hs : whnf_step (KExpr.bvar i) e2) => no_whnf_step_bvar i e2 (S e2) hs)";

// Positive discriminating witness (§6.1): a concrete term IN a concrete
// candidate set, derived THROUGH the interface (cr3 at the irreducible
// neutral bvar 0), not by direct whnf_acc.intro.
pub(super) const TY_CAND_VAR_WITNESS: &str = "whnf_acc (KExpr.bvar Nat.zero)";
pub(super) const VAL_CAND_VAR_WITNESS: &str =
    "cand_var_mem (fun (e : KExpr) => whnf_acc e) isCand_whnfAcc Nat.zero";

// ================================================================
// Group E — the refutation-shaped witness: the self-application loop is
// not whnf_acc, so cr1 genuinely excludes. The standard untyped
// Omega = (\x:*0. x x)(\x:*0. x x) over KExpr; no such object existed in
// core_spec before this module.
// ================================================================

pub(super) const SRC_SELF_APP: &str = "def selfApp : KExpr := KExpr.lam (KExpr.sort Level.zero) (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))";

pub(super) const SRC_OMEGA_LOOP: &str = "def omegaLoop : KExpr := KExpr.app selfApp selfApp";

pub(super) const TY_OMEGA_INST_PIN: &str = "@Eq KExpr (instantiate (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) selfApp) omegaLoop";
pub(super) const VAL_OMEGA_INST_PIN: &str = "@Eq.refl KExpr omegaLoop";

pub(super) const TY_OMEGA_STEP_SELF: &str = "whnf_step omegaLoop omegaLoop";
pub(super) const VAL_OMEGA_STEP_SELF: &str = "@whnf_step.beta omegaLoop omegaLoop (beta_reduces.beta (KExpr.sort Level.zero) (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) selfApp)";

pub(super) const TY_OMEGA_NOT_WHNFACC: &str = "whnf_acc omegaLoop -> Empty";
pub(super) const VAL_OMEGA_NOT_WHNFACC: &str = "fun (h : whnf_acc omegaLoop) => @whnf_acc.rec (fun (e : KExpr) (_h : whnf_acc e) => @Eq KExpr omegaLoop e -> Empty) (fun (e : KExpr) (_hsteps : forall (e1 : KExpr), whnf_step e e1 -> whnf_acc e1) (ih : forall (e1 : KExpr), whnf_step e e1 -> @Eq KExpr omegaLoop e1 -> Empty) (heq : @Eq KExpr omegaLoop e) => ih omegaLoop (@Eq.substType KExpr (fun (z : KExpr) => whnf_step z omegaLoop) omegaLoop e heq omega_step_self) (@Eq.refl KExpr omegaLoop)) omegaLoop h (@Eq.refl KExpr omegaLoop)";

pub(super) const TY_CAND_EXCLUDES_OMEGA: &str =
    "forall (S : KExpr -> Type), IsCandSet S -> S omegaLoop -> Empty";
pub(super) const VAL_CAND_EXCLUDES_OMEGA: &str = "fun (S : KExpr -> Type) (hS : IsCandSet S) (hmem : S omegaLoop) => omega_not_whnfAcc (isCandSet_cr1 S hS omegaLoop hmem)";

impl Specification {
    /// Register the R0 candidate-set interface, its base (whole-SN) instance,
    /// the variable-membership floor, and the two discriminating witnesses.
    ///
    /// MUST be registered AFTER `add_dependent_sn_richmodel` (`Neutral` /
    /// `no_whnf_step_bvar`), `add_whnf_reduction` (`whnf_step` / `whnf_acc` /
    /// `beta_reduces`), `add_expr_model` (`KExpr` / `Level` / `instantiate`),
    /// `add_whnf_progress` (`ConstFreeUnit`) and the foundation types
    /// (`Eq` / `Nat` / `Empty` / `AndType`).
    ///
    /// Port of `Stratified/Cand.lean` `IsCand`/`isCand_SN`/`IsCand.var_mem`
    /// per `designs/2026-08-23-spec-candmodel-port.md` §7 (rung R0); see the
    /// module docs for the not-a-CandModel-instance honesty note.
    pub(super) fn add_candmodel_construct_r0(&mut self) -> Result<(), SpecError> {
        // --- Group A: the faces + the packaged interface ---
        self.add_recursive_def(
            SRC_CAND_CR1,
            "candCr1 S — the CR1 face: every member of S is strongly normalizing for the \
             spec's FULL env-fixed one-step reduction (whnf_acc = Acc of whnf_step at \
             the_red_env). Corpus IsCand.cr1 (Stratified/Cand.lean:32) with SN := whnf_acc. \
             Type-valued plain def.",
        )?;
        self.add_recursive_def(
            SRC_CAND_CR2,
            "candCr2 S — the CR2 face: S is closed under whnf_step (one full beta/zeta/iota/\
             delta step at the fixed the_red_env, congruence included). Corpus IsCand.cr2 \
             (Stratified/Cand.lean:33). Type-valued plain def.",
        )?;
        self.add_recursive_def(
            SRC_CAND_CR3,
            "candCr3 S — the CR3 face: a Neutral term (spec Neutral: bvar/app/const/proj \
             heads; NOT sort/lam/pi/let_/lit) all of whose one-step reducts are in S is in \
             S. Corpus IsCand.cr3 (Stratified/Cand.lean:34). Type-valued plain def.",
        )?;
        self.add_recursive_def(
            SRC_IS_CAND_SET,
            "IsCandSet S — the Girard/Tait candidate-set interface over an arbitrary UNTYPED \
             term set S : KExpr -> Type: AndType (candCr1 S) (AndType (candCr2 S) (candCr3 S)). \
             Corpus IsCand (Stratified/Cand.lean:31) ported to KExpr/whnf_step at the fixed \
             the_red_env. Deliberately per-SET and model-independent: it has NO red_sort/\
             pi_elim/pi_intro/redAbstraction/redRec*/redTypeStep faces, so inhabiting it is \
             FAR weaker than inhabiting CandModel — no claim on the M hypothesis of \
             whnf_terminates_well_typed_dependent is made or implied. R1's generic \
             head-expansion engines take (S, IsCandSet S) as their parameter. Reducible \
             plain def.",
        )?;

        // --- Group B: intro + projections ---
        self.add_definition(SpecDefinition {
            name: "isCandSet_intro".to_string(),
            type_src: TY_ISCANDSET_INTRO.to_string(),
            value_src: Some(VAL_ISCANDSET_INTRO.to_string()),
            is_axiom: false,
            description: "Build an IsCandSet from its three faces (two nested AndType.intro). \
                          The constructor side of the R1 interface. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "candCr1".to_string(),
                "candCr2".to_string(),
                "candCr3".to_string(),
                "AndType.intro".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "isCandSet_cr1".to_string(),
            type_src: TY_ISCANDSET_CR1.to_string(),
            value_src: Some(VAL_ISCANDSET_CR1.to_string()),
            is_axiom: false,
            description: "CR1 projection, stated with the face EXPANDED (members of S are \
                          whnf_acc): AndType.left on the IsCandSet package. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "AndType.left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "isCandSet_cr2".to_string(),
            type_src: TY_ISCANDSET_CR2.to_string(),
            value_src: Some(VAL_ISCANDSET_CR2.to_string()),
            is_axiom: false,
            description: "CR2 projection, face expanded (S closed under whnf_step): \
                          AndType.left of the AndType.right of the package. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "AndType.left".to_string(),
                "AndType.right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "isCandSet_cr3".to_string(),
            type_src: TY_ISCANDSET_CR3.to_string(),
            value_src: Some(VAL_ISCANDSET_CR3.to_string()),
            is_axiom: false,
            description: "CR3 projection, face expanded (neutral with all reducts in S is in \
                          S): AndType.right twice on the package. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "AndType.right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group C: the base instance ---
        self.add_definition(SpecDefinition {
            name: "whnfAcc_inv_step".to_string(),
            type_src: TY_WHNFACC_INV_STEP.to_string(),
            value_src: Some(VAL_WHNFACC_INV_STEP.to_string()),
            is_axiom: false,
            description: "Acc inversion: whnf_acc e and whnf_step e e2 give whnf_acc e2 — one \
                          whnf_acc.rec projecting the intro field (the corpus SN.step, \
                          Cand.lean:53). The cr2 face of the base instance, and the inversion \
                          R1's head-expansion engines will re-use. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_acc".to_string(),
                "whnf_acc.rec".to_string(),
                "whnf_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "isCand_whnfAcc".to_string(),
            type_src: TY_ISCAND_WHNFACC.to_string(),
            value_src: Some(VAL_ISCAND_WHNFACC.to_string()),
            is_axiom: false,
            description: "THE BASE INSTANCE: the whole-SN set (fun e => whnf_acc e) is a \
                          candidate set — cr1 identity, cr2 whnfAcc_inv_step, cr3 \
                          whnf_acc.intro discarding neutrality. Corpus isCand_SN \
                          (Cand.lean:51). HONESTY: this is the TOP candidate set, not a \
                          CandModel Red — the scoping note's §0.4 pincer shows Red := \
                          whnf_acc refutes pi_elim, a law IsCandSet deliberately does not \
                          contain. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "isCandSet_intro".to_string(),
                "whnfAcc_inv_step".to_string(),
                "whnf_acc".to_string(),
                "whnf_acc.intro".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "candCr3_whnfAcc".to_string(),
            type_src: TY_CANDCR3_WHNFACC.to_string(),
            value_src: Some(VAL_CANDCR3_WHNFACC.to_string()),
            is_axiom: false,
            description: "PREMISE-SATISFIABILITY WITNESS for the cr3 face: candCr3 IS \
                          INHABITED, at the base instance's set (fun e => whnf_acc e). \
                          candCr3 is assumed as a hypothesis by isCandSet_intro and nothing \
                          in the ladder concluded it — isCandSet_cr3 states the face \
                          EXPANDED, so its conclusion is S e, not candCr3 S. A face nothing \
                          supplies would make every isCandSet_intro call conditional on an \
                          obligation no term is known to meet, which is exactly the shape the \
                          hnf capstone had. The witness is the same nested AndType.right the \
                          projection uses, with the package left unexpanded so the CONCLUSION \
                          is the face, applied to isCand_whnfAcc. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "candCr3".to_string(),
                "IsCandSet".to_string(),
                "isCand_whnfAcc".to_string(),
                "AndType.right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "candCr1_whnfAcc".to_string(),
            type_src: TY_CANDCR1_WHNFACC.to_string(),
            value_src: Some(VAL_CANDCR1_WHNFACC.to_string()),
            is_axiom: false,
            description: "PREMISE-SATISFIABILITY WITNESS for the cr1 face: candCr1 IS \
                          INHABITED, at the base instance's set (fun e => whnf_acc e). \
                          candCr1 is assumed as a hypothesis by isCandSet_intro and nothing \
                          in the ladder concluded it — isCandSet_cr1 states the face \
                          EXPANDED (its conclusion is whnf_acc e), so its conclusion is not candCr1 S. Companion to \
                          candCr3_whnfAcc, which witnessed the third face alone and left this \
                          one open; the projection is the one isCandSet_cr1 already \
                          performs, with the package unexpanded so the CONCLUSION is the face, \
                          applied to isCand_whnfAcc. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "candCr1".to_string(),
                "IsCandSet".to_string(),
                "isCand_whnfAcc".to_string(),
                "AndType.left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "candCr2_whnfAcc".to_string(),
            type_src: TY_CANDCR2_WHNFACC.to_string(),
            value_src: Some(VAL_CANDCR2_WHNFACC.to_string()),
            is_axiom: false,
            description: "PREMISE-SATISFIABILITY WITNESS for the cr2 face: candCr2 IS \
                          INHABITED, at the base instance's set (fun e => whnf_acc e). \
                          candCr2 is assumed as a hypothesis by isCandSet_intro and nothing \
                          in the ladder concluded it — isCandSet_cr2 states the face \
                          EXPANDED (its conclusion is S e2), so its conclusion is not candCr2 S. Companion to \
                          candCr3_whnfAcc, which witnessed the third face alone and left this \
                          one open; the projection is the one isCandSet_cr2 already \
                          performs, with the package unexpanded so the CONCLUSION is the face, \
                          applied to isCand_whnfAcc. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "candCr2".to_string(),
                "IsCandSet".to_string(),
                "isCand_whnfAcc".to_string(),
                "AndType.left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group D: the candidate-space floor ---
        self.add_definition(SpecDefinition {
            name: "cand_var_mem".to_string(),
            type_src: TY_CAND_VAR_MEM.to_string(),
            value_src: Some(VAL_CAND_VAR_MEM.to_string()),
            is_axiom: false,
            description: "Every candidate set contains every variable (corpus IsCand.var_mem, \
                          Cand.lean:43): bvar i is Neutral (ConstFreeUnit.triv computes) and \
                          admits no whnf_step (no_whnf_step_bvar), so cr3 applies vacuously. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "isCandSet_cr3".to_string(),
                "Neutral".to_string(),
                "ConstFreeUnit".to_string(),
                "no_whnf_step_bvar".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "cand_var_witness".to_string(),
            type_src: TY_CAND_VAR_WITNESS.to_string(),
            value_src: Some(VAL_CAND_VAR_WITNESS.to_string()),
            is_axiom: false,
            description: "Positive discriminating witness (§6.1 control): whnf_acc (bvar 0) \
                          derived THROUGH the interface — cand_var_mem at the base instance \
                          isCand_whnfAcc — exercising the cr3 face a degenerate Empty-style \
                          set would fail, at the concrete irreducible neutral bvar 0. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "cand_var_mem".to_string(),
                "isCand_whnfAcc".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group E: the refutation-shaped witness ---
        self.add_recursive_def(
            SRC_SELF_APP,
            "selfApp = lam (sort 0) (app (bvar 0) (bvar 0)) — the untyped self-applicator \
             (\\x:*0. x x) as a closed KExpr. Its annotation sort 0 is irrelevant: the \
             candidate laws quantify over untyped terms. Plain def.",
        )?;
        self.add_recursive_def(
            SRC_OMEGA_LOOP,
            "omegaLoop = app selfApp selfApp — the standard Omega loop over KExpr; \
             beta-steps to itself (omega_step_self), so it is NOT whnf_acc \
             (omega_not_whnfAcc). Plain def.",
        )?;
        self.add_definition(SpecDefinition {
            name: "omega_inst_pin".to_string(),
            type_src: TY_OMEGA_INST_PIN.to_string(),
            value_src: Some(VAL_OMEGA_INST_PIN.to_string()),
            is_axiom: false,
            description: "Computation pin: instantiate (app (bvar 0) (bvar 0)) selfApp \
                          reduces to omegaLoop by Eq.refl (the beta contractum of omegaLoop \
                          IS omegaLoop — selfApp is closed, so the substitution computes \
                          exactly). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate".to_string(),
                "selfApp".to_string(),
                "omegaLoop".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "omega_step_self".to_string(),
            type_src: TY_OMEGA_STEP_SELF.to_string(),
            value_src: Some(VAL_OMEGA_STEP_SELF.to_string()),
            is_axiom: false,
            description: "omegaLoop whnf_steps to ITSELF: the top-level beta step of \
                          app selfApp selfApp, whose contractum computes back to omegaLoop \
                          (omega_inst_pin). The one-step loop feeding omega_not_whnfAcc. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step".to_string(),
                "whnf_step.beta".to_string(),
                "beta_reduces.beta".to_string(),
                "selfApp".to_string(),
                "omegaLoop".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "omega_not_whnfAcc".to_string(),
            type_src: TY_OMEGA_NOT_WHNFACC.to_string(),
            value_src: Some(VAL_OMEGA_NOT_WHNFACC.to_string()),
            is_axiom: false,
            description: "omegaLoop is NOT strongly normalizing: whnf_acc.rec with the \
                          equality-generalized motive (Eq omegaLoop e -> Empty); at each \
                          node the self-step (transported along the equation via \
                          Eq.substType) feeds the IH at omegaLoop itself. The standard \
                          Acc-refutation of a one-step loop. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_acc".to_string(),
                "whnf_acc.rec".to_string(),
                "omega_step_self".to_string(),
                "omegaLoop".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "cand_excludes_omega".to_string(),
            type_src: TY_CAND_EXCLUDES_OMEGA.to_string(),
            value_src: Some(VAL_CAND_EXCLUDES_OMEGA.to_string()),
            is_axiom: false,
            description: "Refutation-shaped discriminating witness (§6.1 control): NO \
                          candidate set contains omegaLoop — cr1 sends a member to \
                          whnf_acc, which omega_not_whnfAcc refutes. This is the face the \
                          everything-degenerate 'top' relation would fail if IsCandSet's \
                          cr1 were vacuous, hand-registered because no automated gate \
                          checks registrations for degenerate content. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IsCandSet".to_string(),
                "isCandSet_cr1".to_string(),
                "omega_not_whnfAcc".to_string(),
                "omegaLoop".to_string(),
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

    /// Every plain-def source in registration order.
    const DEF_SOURCES: [&str; 6] = [
        SRC_CAND_CR1,
        SRC_CAND_CR2,
        SRC_CAND_CR3,
        SRC_IS_CAND_SET,
        SRC_SELF_APP,
        SRC_OMEGA_LOOP,
    ];

    /// Every (name, type, value) triple registered via `add_definition`, in
    /// registration order.
    const THEOREM_SOURCES: [(&str, &str, &str); 15] = [
        ("isCandSet_intro", TY_ISCANDSET_INTRO, VAL_ISCANDSET_INTRO),
        ("isCandSet_cr1", TY_ISCANDSET_CR1, VAL_ISCANDSET_CR1),
        ("isCandSet_cr2", TY_ISCANDSET_CR2, VAL_ISCANDSET_CR2),
        ("isCandSet_cr3", TY_ISCANDSET_CR3, VAL_ISCANDSET_CR3),
        (
            "whnfAcc_inv_step",
            TY_WHNFACC_INV_STEP,
            VAL_WHNFACC_INV_STEP,
        ),
        ("isCand_whnfAcc", TY_ISCAND_WHNFACC, VAL_ISCAND_WHNFACC),
        ("candCr3_whnfAcc", TY_CANDCR3_WHNFACC, VAL_CANDCR3_WHNFACC),
        ("candCr1_whnfAcc", TY_CANDCR1_WHNFACC, VAL_CANDCR1_WHNFACC),
        ("candCr2_whnfAcc", TY_CANDCR2_WHNFACC, VAL_CANDCR2_WHNFACC),
        ("cand_var_mem", TY_CAND_VAR_MEM, VAL_CAND_VAR_MEM),
        (
            "cand_var_witness",
            TY_CAND_VAR_WITNESS,
            VAL_CAND_VAR_WITNESS,
        ),
        ("omega_inst_pin", TY_OMEGA_INST_PIN, VAL_OMEGA_INST_PIN),
        ("omega_step_self", TY_OMEGA_STEP_SELF, VAL_OMEGA_STEP_SELF),
        (
            "omega_not_whnfAcc",
            TY_OMEGA_NOT_WHNFACC,
            VAL_OMEGA_NOT_WHNFACC,
        ),
        (
            "cand_excludes_omega",
            TY_CAND_EXCLUDES_OMEGA,
            VAL_CAND_EXCLUDES_OMEGA,
        ),
    ];

    /// Parse-check every generated source — the fast guard for the commonest
    /// failure class (syntax-level assembly mistakes invisible to cargo check).
    #[test]
    fn test_candmodel_r0_sources_parse() {
        for src in DEF_SOURCES {
            parse_check(src).unwrap_or_else(|e| panic!("def source should parse: {e}\n{src}"));
        }
        for (name, ty, val) in THEOREM_SOURCES {
            let assembled = format!("def {name} : {ty} := {val}");
            parse_check(&assembled)
                .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
        }
    }

    /// Paren balance on every source (a cheap structural guard for the long
    /// single-line proof terms).
    #[test]
    fn test_candmodel_r0_sources_paren_balanced() {
        let mut all: Vec<String> = DEF_SOURCES.iter().map(|s| (*s).to_string()).collect();
        for (_, ty, val) in THEOREM_SOURCES {
            all.push(ty.to_string());
            all.push(val.to_string());
        }
        for src in &all {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in: {src}");
            }
            assert_eq!(depth, 0, "unbalanced parens in: {src}");
        }
    }

    /// Interface-shape guard: the packaged IsCandSet nests exactly
    /// AndType (candCr1 S) (AndType (candCr2 S) (candCr3 S)), and every
    /// projection/intro spells the SAME package (a transposition would
    /// elaborate to a wrong projection, caught only at heavy-run time).
    #[test]
    fn test_candmodel_r0_package_shape_consistent() {
        let package = "AndType (candCr1 S) (AndType (candCr2 S) (candCr3 S))";
        assert!(
            SRC_IS_CAND_SET.contains(package),
            "IsCandSet body should be the canonical right-nested package"
        );
        for (name, val) in [
            ("isCandSet_intro", VAL_ISCANDSET_INTRO),
            ("isCandSet_cr1", VAL_ISCANDSET_CR1),
            ("isCandSet_cr2", VAL_ISCANDSET_CR2),
            ("isCandSet_cr3", VAL_ISCANDSET_CR3),
        ] {
            assert!(
                val.contains("(AndType (candCr2 S) (candCr3 S))"),
                "{name} should project against the canonical inner package"
            );
        }
    }

    /// Registration + kernel re-verification against the substitution bundle:
    /// the stage registers every constant, and the interface instance, floor,
    /// and both discriminating witnesses re-typecheck in the live kernel
    /// environment.
    #[test]
    fn test_candmodel_r0_registered_and_reverifies() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();
        for name in [
            "candCr1",
            "candCr2",
            "candCr3",
            "IsCandSet",
            "isCandSet_intro",
            "isCandSet_cr1",
            "isCandSet_cr2",
            "isCandSet_cr3",
            "whnfAcc_inv_step",
            "isCand_whnfAcc",
            "candCr3_whnfAcc",
            "candCr1_whnfAcc",
            "candCr2_whnfAcc",
            "cand_var_mem",
            "cand_var_witness",
            "selfApp",
            "omegaLoop",
            "omega_inst_pin",
            "omega_step_self",
            "omega_not_whnfAcc",
            "cand_excludes_omega",
        ] {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the candmodel_construct_r0 stage"
            );
        }
        for name in [
            "isCandSet_intro",
            "isCandSet_cr1",
            "isCandSet_cr2",
            "isCandSet_cr3",
            "whnfAcc_inv_step",
            "isCand_whnfAcc",
            "candCr3_whnfAcc",
            "candCr1_whnfAcc",
            "candCr2_whnfAcc",
            "cand_var_mem",
            "cand_var_witness",
            "omega_inst_pin",
            "omega_step_self",
            "omega_not_whnfAcc",
            "cand_excludes_omega",
        ] {
            spec.verify_definition(name).unwrap_or_else(|e| {
                panic!("{name} should re-typecheck in the spec environment: {e:?}")
            });
        }
    }
}
