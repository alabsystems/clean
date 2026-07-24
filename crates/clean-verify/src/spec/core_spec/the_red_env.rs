// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `the_red_env`: the single distinguished reduction environment the DefEq world
//! is implicitly relative to (church_rosser_whnf retirement track, design
//! `scratch/defeq-family-redefinition-design.md` §1/§2, deletion plan §3 choice 3c).
//!
//! The env-free `DefEq` / `iota_reduces` / `delta_reduces` must, when tightened to
//! carry an OPERATIONAL step, pin that step's environment to ONE fixed constant
//! (a `forall env` premise is the FALSE all-environments claim; an `∃ env` premise
//! cannot be re-pinned at the join site — design §1(β)/(3b)). That fixed constant
//! is `the_red_env`.
//!
//! ## Front #1 STAGE 3 — THE SWAP (this module's current state)
//!
//! `the_red_env` is no longer a toy: its value IS `kernel_core_red_env`, the
//! MECHANICALLY REFLECTED foundation core of the real kernel environment
//! (19 recursors / 36 real rules with real RecMeta counts and real rule RHSs,
//! 50 real definition values; `kernel_core_red_env.rs`), pinned 1:1 to the
//! live kernel env by the fidelity gate
//! (`tests/kernel_core_red_env_fidelity.rs`) under the three documented trust
//! edges (injective name interning / level erasure / coverage-with-skips
//! ledger). The metatheory's reduction environment is therefore a
//! fidelity-gated reflection of the environment the kernel itself computes
//! with. Registration order: the generated def script (`kcre_nat_*` /
//! `kcre_name_*` atoms + the env term) registers in the stage IMMEDIATELY
//! BEFORE this one (see bundles.rs).
//!
//! CRITICAL — why this is a value-ful DEFINITION, not the design doc's opaque
//! postulate (§2): a value-LESS `the_red_env : RedEnv` lowers to a
//! `Declaration::Axiom` which the axiom ratchet counts (Guard 2 violation). So
//! `the_red_env` is a concrete `def` with `value_src = Some(..)`, lowering to a
//! `Declaration::Definition` the ratchet does NOT count.
//!
//! ## Guard 3, restated for the post-swap world
//!
//! Value-COMPUTATION on `the_red_env` is permitted ONLY in the designated
//! discharge modules:
//!  - the two Guard-4 non-vacuity witnesses below (a real `Nat.rec` iota fire
//!    and a real delta unfold);
//!  - the checker-based one-rfl interface discharges
//!    (`env_closed_checkers.rs` / `env_closed_checkers_depth.rs` /
//!    `faithful_checkers.rs`, including the Stage-4
//!    `the_red_env_faithful` bundle) and the kernel_core_red_env payoff
//!    witnesses;
//!  - the fidelity-gate / refutation-gate measurement probes (tests).
//!
//! The ~79 carried-hypothesis metatheory decls remain PARAMETRIC in the env
//! value (the schematic discipline): no metatheory proof term pattern-matches
//! the value, so the metatheory stays general and survives regeneration of the
//! reflection. NO property OF `the_red_env` is postulated as an axiom — the
//! i1..i8 interfaces are either carried hypotheses or honestly DISCHARGED
//! `DerivedProved` checker witnesses (`the_red_env_faithful`).
//!
//! ## Guard 4 (non-vacuity)
//!
//! The reflected env is NON-EMPTY by construction; the two witnesses below
//! pin a REAL iota fire (`Nat.rec` applied through motive/minors to the
//! `Nat.zero` constructor reduces to the real rule rhs applied to the spine
//! prefix) and a REAL delta unfold (the outermost DefEnv entry,
//! `def_env_lift_closed_b`, unfolds to its reflected value), so the tightened
//! `iota_reduces` / `delta_reduces` families are inhabited, not vacuous.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// Interned-name atoms of the reflected env (generated/kernel_core_red_env.interning.tsv):
// real name -> `kcre_name_<tag>` (:= Name.str Name.anonymous <unary tag>).
const NAT_REC: &str = "kcre_name_25"; // Nat.rec
const NAT_ZERO: &str = "kcre_name_16"; // Nat.zero
const DELTA_HEAD: &str = "kcre_name_116"; // def_env_lift_closed_b (outermost DefEnv entry)

// The REAL reflected rule rhs of Nat.rec's Nat.zero rule (extracted verbatim
// from the generated env term; the fidelity gate pins it to the kernel):
// λ (motive : Nat -> Sort) (z : motive Nat.zero)
//   (s : ∀ n, motive n -> motive (Nat.succ n)) => z, level-erased.
const NAT_ZERO_RHS: &str = "(KExpr.lam (KExpr.pi (KExpr.const kcre_name_1 (ListType.nil Level)) (KExpr.sort Level.zero)) \
     (KExpr.lam (KExpr.app (KExpr.bvar kcre_nat_0) (KExpr.const kcre_name_16 (ListType.nil Level))) \
     (KExpr.lam (KExpr.pi (KExpr.const kcre_name_1 (ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar kcre_nat_2) (KExpr.bvar kcre_nat_0)) \
     (KExpr.app (KExpr.bvar kcre_nat_3) (KExpr.app (KExpr.const kcre_name_10 (ListType.nil Level)) (KExpr.bvar kcre_nat_1))))) \
     (KExpr.bvar kcre_nat_1))))";

// The REAL reflected value of the outermost DefEnv entry
// (`def_env_lift_closed_b := fun (env : DefEnv) => def_env_closed_b env`):
// kcre_name_12 = DefEnv, kcre_name_88 = def_env_closed_b.
const DELTA_VALUE: &str = "(KExpr.lam (KExpr.const kcre_name_12 (ListType.nil Level)) \
     (KExpr.app (KExpr.const kcre_name_88 (ListType.nil Level)) (KExpr.bvar kcre_nat_0)))";

impl Specification {
    pub(super) fn add_the_red_env(&mut self) -> Result<(), SpecError> {
        // the_red_env : RedEnv — the fixed distinguished env, SWAPPED (Front #1
        // Stage 3) to the fidelity-gated reflection of the real kernel
        // foundation core. value_src = Some(..) ⇒ Declaration::Definition ⇒
        // ratchet-clean (Guard 2). A value-level ALIAS: the generated
        // kernel_core_red_env def (previous stage) carries the literal.
        self.add_recursive_def(
            "def the_red_env : RedEnv := kernel_core_red_env",
            "The single distinguished reduction environment DefEq is relative to (deletion-plan \
             choice 3c) — SWAPPED (Front #1 Stage 3) to kernel_core_red_env, the mechanically \
             reflected, fidelity-gated foundation core of the REAL kernel environment (19 \
             recursors / 36 real rules / 50 real definition values; \
             tests/kernel_core_red_env_fidelity.rs pins it 1:1 to the live kernel env). A \
             value-ful Definition (NOT a postulated axiom: Guard 2), non-empty by construction \
             (Guard 4: a real Nat.rec iota fire + a real delta unfold — see the two witnesses). \
             Its value is never pattern-matched by the carried metatheory (schematic discipline, \
             Guard 3): value computation happens only in the designated discharge modules. Part \
             of the church_rosser_whnf retirement track.",
        )?;

        // Guard 4 witness (iota): the_red_env genuinely admits a REAL iota
        // step. Nat.rec (RecMeta 0/1/2/0, major at spine position 3) applied
        // to [motive, minor_zero, minor_succ, Nat.zero] reduces by iota_reduct
        // to the REAL Nat.zero rule rhs applied back to the spine prefix
        // (rhs motive minor_zero minor_succ). The three prefix arguments are
        // chosen as (sort 0) placeholders — iota_reduct is a name-keyed spine
        // surgery and never inspects them. Pure computation: ZERO axiom_deps.
        self.add_definition(SpecDefinition {
            name: "the_red_env_iota_nonvacuous".to_string(),
            type_src: format!(
                "iota_step (red_rec the_red_env) \
                 (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const {NAT_REC} (ListType.nil Level)) \
                 (KExpr.sort Level.zero)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero)) \
                 (KExpr.const {NAT_ZERO} (ListType.nil Level))) \
                 (KExpr.app (KExpr.app (KExpr.app {NAT_ZERO_RHS} \
                 (KExpr.sort Level.zero)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero))"
            ),
            value_src: Some(format!(
                "Eq.refl (OptionType KExpr) (OptionType.some KExpr \
                 (KExpr.app (KExpr.app (KExpr.app {NAT_ZERO_RHS} \
                 (KExpr.sort Level.zero)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero)))"
            )),
            is_axiom: false,
            description: "Non-vacuity witness (Guard 4, post-swap): the_red_env admits a REAL iota step — \
                          the reflected Nat.rec (real RecMeta 0 params/1 motive/2 minors/0 indices, major at \
                          spine position 3) applied to [motive, minor_zero, minor_succ, Nat.zero] reduces by \
                          the computational iota_reduct to the REAL Nat.zero rule rhs applied to the spine \
                          prefix. Proof by refl — the kernel whnf-evaluates iota_reduct over the reflected \
                          env. Zero axiom_deps. Confirms the tightened iota_reduces family is inhabited."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "the_red_env".to_string(),
                "iota_step".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Guard 4 witness (delta): the_red_env genuinely admits a REAL delta
        // step. The const `def_env_lift_closed_b` (the outermost DefEnv entry,
        // the first defval_for match) unfolds by delta_reduct to its REAL
        // reflected value (λ (env : DefEnv). def_env_closed_b env). Pure
        // computation: ZERO axiom_deps.
        self.add_definition(SpecDefinition {
            name: "the_red_env_delta_nonvacuous".to_string(),
            type_src: format!(
                "delta_step (red_def the_red_env) \
                 (KExpr.const {DELTA_HEAD} (ListType.nil Level)) \
                 {DELTA_VALUE}"
            ),
            value_src: Some(format!(
                "Eq.refl (OptionType KExpr) (OptionType.some KExpr {DELTA_VALUE})"
            )),
            is_axiom: false,
            description: "Non-vacuity witness (Guard 4, post-swap): the_red_env admits a REAL delta step — \
                          the reflected definition def_env_lift_closed_b (the outermost DefEnv entry) unfolds \
                          by the computational delta_reduct to its REAL reflected value (a lambda applying \
                          def_env_closed_b). Proof by refl — the kernel whnf-evaluates delta_reduct over the \
                          reflected env. Zero axiom_deps. Confirms the tightened delta_reduces family is \
                          inhabited."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "the_red_env".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
