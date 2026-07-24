// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Environment-preservation theorems for the kernel add_decl entry point (#461).
//!
//! This module bridges the production kernel's `Environment::add_decl` to the
//! specification's `DefinitionalExtension` soundness chain.  It adds:
//!
//! - `KernelAddDeclAccepts`: opaque predicate for successful `add_decl`
//! - `KernelAddDeclChain`: reflexive-transitive closure of successful `add_decl`
//! - `kernel_add_decl_extends_env`: successful `add_decl` is a definitional extension
//! - `kernel_add_decl_preserves_env_valid_raw`: raw env-validity projection (constructive)
//! - `kernel_add_decl_preserves_local_ctx_wf_raw`: raw local-context projection (constructive)
//! - `KernelAddDeclPreservesEnvValid`: state-indexed env-validity wrapper
//! - `kernel_add_decl_preserves_local_ctx_wf`: state-indexed local-context wrapper
//! - `KernelAddDeclPreservesEnvSound`: derived—`add_decl` preserves `EnvSound`
//! - `KernelAddDeclPreservesState`: derived—`add_decl` preserves `KernelStateMatchesSpec`
//! - `KernelAddDeclSound`: derived—combined end-to-end theorem (inductive step)
//! - `KernelAddDeclChainSound`: derived—fold the one-step theorem across any chain

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_env_preservation(
        &mut self,
    ) -> Result<(), SpecError> {
        // =========================================================
        // PART 21c: Environment preservation through add_decl (#461)
        // =========================================================
        //
        // The production kernel's `Environment::add_decl` is the sole entry
        // point for extending the environment with new constants/inductives.
        // This slice names that operation in the specification and states the
        // preservation properties needed to chain forward-simulation across
        // multiple declaration additions.

        // KernelAddDeclAccepts: was an opaque `KEnv -> KEnv -> Type` HelperAxiom
        // ("Environment::add_decl transformed env into env'"). It is now a FAITHFUL
        // inductive — the same Accepts-decomposition playbook as KernelDefEqAccepts /
        // KernelInferAccepts / KernelCheckAccepts. A successful add_decl performs
        // EITHER a constant extension OR an inductive extension, so the two
        // constructors carry exactly that evidence (ConstantExtension /
        // InductiveExtension — themselves inductives whose .mk already bundles the
        // freshness / well-typedness / positivity / well-formedness the real add_decl
        // verified). NO extra guard is needed: the validity lives inside
        // ConstantExtension / InductiveExtension. Draining the opaque axiom to this
        // inductive is a genuine census drop (no new axiom); the external Trust
        // producer must now supply the extension evidence — the faithful requirement
        // (add_decl success = a valid extension was performed).
        self.add_inductive(
            r"inductive KernelAddDeclAccepts : KEnv -> KEnv -> Type
| const_case : forall (env : KEnv) (env' : KEnv), ConstantExtension env env' -> KernelAddDeclAccepts env env'
| inductive_case : forall (env : KEnv) (env' : KEnv), InductiveExtension env env' -> KernelAddDeclAccepts env env'",
            "KernelAddDeclAccepts env env': the production kernel's add_decl transformed \
             env into env' — faithfully, EITHER a constant extension (const_case, carrying \
             ConstantExtension) or an inductive extension (inductive_case, carrying \
             InductiveExtension). Formerly an opaque HelperAxiom.",
        )?;

        // kernel_add_decl_extends_env: was the opaque bridge HelperAxiom; now a
        // DerivedProved term. Eliminating the KernelAddDeclAccepts inductive gives the
        // ConstantExtension / InductiveExtension evidence in each case, which
        // DefinitionalExtension.const_ / .inductive_ lift directly to the immediate
        // definitional-extension step. Zero axiom_deps (rests only on the
        // FoundationalRule DefinitionalExtension constructors + the new inductive's
        // recursor).
        self.add_definition(SpecDefinition {
            name: "kernel_add_decl_extends_env".to_string(),
            type_src: "forall (env : KEnv) (env' : KEnv), KernelAddDeclAccepts env env' -> DefinitionalExtension env env'".to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (h : KernelAddDeclAccepts env env') => ",
                    "KernelAddDeclAccepts.rec env env' ",
                    "(fun (_ : KernelAddDeclAccepts env env') => DefinitionalExtension env env') ",
                    "(fun (ce : ConstantExtension env env') => DefinitionalExtension.const_ env env' ce) ",
                    "(fun (ie : InductiveExtension env env') => DefinitionalExtension.inductive_ env env' ie) ",
                    "h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Bridge, now DERIVED: a successful add_decl corresponds to a valid \
                          definitional-extension step. Proof = case on KernelAddDeclAccepts \
                          (const_case -> DefinitionalExtension.const_; inductive_case -> \
                          DefinitionalExtension.inductive_). Formerly a HelperAxiom bridge; \
                          zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelAddDeclAccepts".to_string(),
                "DefinitionalExtension".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The raw implementation obligations live at the environment/local-context
        // layer. Both raw projections below are now derived CONSTRUCTIVELY: the
        // env-validity half via DefinitionalExtension.trans (Rank-1) and the
        // local-context half via KernelLocalCtxWellFormed.rec env-transport replay
        // (Rank-2). The consolidated `kernel_add_decl_raw_preservation` HelperAxiom
        // that previously packaged both as a ProdType has been ELIMINATED (a genuine
        // -1 admitted-axiom drain): there is no longer any preservation axiom to
        // project off; each half stands on its own constructive proof term. The
        // state-indexed versions further below are derived wrappers so the
        // summary-facing theorem can stay structural.

        self.add_definition(SpecDefinition {
            name: "kernel_add_decl_preserves_env_valid_raw".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv), ",
                "KernelEnvValid env -> ",
                "KernelAddDeclAccepts env env' -> ",
                "KernelEnvValid env'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) ",
                    "(henv : KernelEnvValid env) ",
                    "(hadd : KernelAddDeclAccepts env env') => ",
                    "DefinitionalExtension.trans KEnv.empty env env' henv ",
                    "(kernel_add_decl_extends_env env env' hadd)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Raw env-validity preservation, derived CONSTRUCTIVELY (not a projection ",
                "off any preservation axiom). With ",
                "KernelEnvValid env := EnvSound env := DefinitionalExtension KEnv.empty env ",
                "(both semireducible), the hypothesis henv : KernelEnvValid env unfolds to a ",
                "DefinitionalExtension KEnv.empty env reachability witness; ",
                "kernel_add_decl_extends_env env env' hadd supplies the immediate ",
                "DefinitionalExtension env env' step; and DefinitionalExtension.trans (a ",
                "FoundationalRule) composes them into DefinitionalExtension KEnv.empty env' = ",
                "KernelEnvValid env' (the goal). This mirrors constant_extension_preserves_soundness. ",
                "The remaining trust leaf is the kernel_add_decl_extends_env bridge HelperAxiom ",
                "(which itself rests on the KernelAddDeclAccepts HelperAxiom); the env-transport ",
                "step is FOUNDATIONAL."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelEnvValid".to_string(),
                "KernelAddDeclAccepts".to_string(),
                "kernel_add_decl_extends_env".to_string(),
                "DefinitionalExtension.trans".to_string(),
            ])),
            // True transitive non-foundational closure of the new constructive value:
            // kernel_add_decl_extends_env (HelperAxiom bridge) + KernelAddDeclAccepts
            // (HelperAxiom, in the type and in the bridge's own closure).
            // DefinitionalExtension.trans is a FoundationalRule, hence foundational base,
            // not residual debt.
            axiom_deps: HashSet::from([
                "kernel_add_decl_extends_env".to_string(),
                "KernelAddDeclAccepts".to_string(),
            ]),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelAddDeclPreservesEnvValid".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx), ",
                "KernelStateEnvValid (KernelState.mk env ctx) -> ",
                "KernelAddDeclAccepts env env' -> ",
                "KernelStateEnvValid (KernelState.mk env' ctx)"
            ).to_string(),
            value_src: Some(concat!(
                "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                "(henv : KernelStateEnvValid (KernelState.mk env ctx)) ",
                "(hadd : KernelAddDeclAccepts env env') => ",
                "kernel_add_decl_preserves_env_valid_raw env env' henv hadd"
            ).to_string()),
            is_axiom: false,
            description: "State-indexed env-validity preservation wrapper for add_decl. It factors through the constructive raw env-validity projection kernel_add_decl_preserves_env_valid_raw (DefinitionalExtension.trans) while keeping downstream proofs on KernelStateEnvValid.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateEnvValid".to_string(),
                "kernel_add_decl_preserves_env_valid_raw".to_string(),
                "KernelAddDeclAccepts".to_string(),
            ])),
            // True transitive non-foundational closure: the env half is constructive
            // (DerivedPending), so its closure surfaces here — the
            // kernel_add_decl_extends_env bridge HelperAxiom and its KernelAddDeclAccepts
            // leaf. The consolidated raw axiom is gone (Rank-2 drain).
            axiom_deps: HashSet::from([
                "kernel_add_decl_extends_env".to_string(),
                "KernelAddDeclAccepts".to_string(),
            ]),
        })?;

        self.add_definition(SpecDefinition {
            name: "kernel_add_decl_preserves_local_ctx_wf_raw".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx), ",
                "KernelLocalCtxWellFormed env ctx -> ",
                "KernelAddDeclAccepts env env' -> ",
                "KernelLocalCtxWellFormed env' ctx"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                    "(hctx : KernelLocalCtxWellFormed env ctx) ",
                    "(_hadd : KernelAddDeclAccepts env env') => ",
                    "KernelLocalCtxWellFormed.rec env ",
                    "(fun (c : KernelLocalCtx) (_h : KernelLocalCtxWellFormed env c) => ",
                    "KernelLocalCtxWellFormed env' c) ",
                    "(KernelLocalCtxWellFormed.nil env') ",
                    "(fun (id : Nat) (ty : KExpr) (u : Level) (rest : KernelLocalCtx) ",
                    "(hty : Typing ty (KExpr.sort u)) ",
                    "(_hrest : KernelLocalCtxWellFormed env rest) ",
                    "(ih : KernelLocalCtxWellFormed env' rest) => ",
                    "KernelLocalCtxWellFormed.cons env' id ty u rest hty ih) ",
                    "ctx hctx"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Raw local-context preservation, now derived CONSTRUCTIVELY by ",
                "KernelLocalCtxWellFormed.rec env-transport replay (no longer a ProdType ",
                "projection off any preservation axiom). KernelLocalCtxWellFormed is a ",
                "faithful nil/cons inductive whose env is a UNIFORM/phantom parameter and ",
                "whose cons premise Typing ty (KExpr.sort u) is ENV-FREE; the recursor ",
                "motive (fun c _ => KernelLocalCtxWellFormed env' c) admits the env re-index, ",
                "so every witness transports by rebuilding it under env': nil -> ",
                "KernelLocalCtxWellFormed.nil env', cons -> KernelLocalCtxWellFormed.cons env' ",
                "reusing the env-free Typing derivation and the recursively-transported tail. ",
                "The KernelAddDeclAccepts hypothesis (_hadd) is unused — env transport is ",
                "purely structural. The only trust leaf is the KernelAddDeclAccepts ",
                "HelperAxiom in the type signature; the transport step is FOUNDATIONAL."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelLocalCtxWellFormed".to_string(),
                "KernelLocalCtxWellFormed.rec".to_string(),
                "KernelLocalCtxWellFormed.nil".to_string(),
                "KernelLocalCtxWellFormed.cons".to_string(),
                "Typing".to_string(),
                "KernelAddDeclAccepts".to_string(),
            ])),
            // True transitive non-foundational closure of the constructive value: the
            // KernelAddDeclAccepts HelperAxiom (present only in the type signature; the
            // proof itself never uses _hadd). The KernelLocalCtxWellFormed inductive,
            // its recursor and constructors, and the env-free Typing judgment are
            // foundational base, not residual debt. The consolidated raw axiom is gone.
            axiom_deps: HashSet::from(["KernelAddDeclAccepts".to_string()]),
        })?;

        self.add_definition(SpecDefinition {
            name: "kernel_add_decl_preserves_local_ctx_wf".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx), ",
                "KernelStateLocalCtxWellFormed (KernelState.mk env ctx) -> ",
                "KernelAddDeclAccepts env env' -> ",
                "KernelStateLocalCtxWellFormed (KernelState.mk env' ctx)"
            ).to_string(),
            value_src: Some(concat!(
                "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                "(hctx : KernelStateLocalCtxWellFormed (KernelState.mk env ctx)) ",
                "(hadd : KernelAddDeclAccepts env env') => ",
                "kernel_add_decl_preserves_local_ctx_wf_raw env env' ctx hctx hadd"
            ).to_string()),
            is_axiom: false,
            description: "State-indexed local-context preservation wrapper for add_decl. It factors through the constructive raw local-context projection kernel_add_decl_preserves_local_ctx_wf_raw (KernelLocalCtxWellFormed.rec env-transport) while keeping downstream proofs on KernelStateLocalCtxWellFormed.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateLocalCtxWellFormed".to_string(),
                "kernel_add_decl_preserves_local_ctx_wf_raw".to_string(),
                "KernelAddDeclAccepts".to_string(),
            ])),
            // The raw local-context half is now constructive (DerivedPending); its only
            // leaf is the KernelAddDeclAccepts HelperAxiom. The consolidated raw axiom
            // is gone (Rank-2 drain).
            axiom_deps: HashSet::from(["KernelAddDeclAccepts".to_string()]),
        })?;

        // =========================================================
        // Derived corollary: add_decl preserves EnvSound (spec-level)
        // =========================================================

        self.add_definition(SpecDefinition {
            name: "KernelAddDeclPreservesEnvSound".to_string(),
            type_src: "forall (env : KEnv) (env' : KEnv), EnvSound env -> KernelAddDeclAccepts env env' -> EnvSound env'".to_string(),
            value_src: Some(concat!(
                "fun (env : KEnv) (env' : KEnv) ",
                "(hsound : EnvSound env) ",
                "(hadd : KernelAddDeclAccepts env env') => ",
                "definitional_extension_sound env env' ",
                "(kernel_add_decl_extends_env env env' hadd) ",
                "hsound"
            ).to_string()),
            is_axiom: false,
            description: "Derived corollary: add_decl preserves spec-level environment soundness by composing the implementation-to-spec bridge with definitional_extension_sound.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "EnvSound".to_string(),
                "KernelAddDeclAccepts".to_string(),
                "definitional_extension_sound".to_string(),
                "kernel_add_decl_extends_env".to_string(),
            ])),
            axiom_deps: HashSet::from([
                // From kernel_add_decl_extends_env:
                "KernelAddDeclAccepts".to_string(),
                // From definitional_extension_sound (transitive):
                "FreshDeclName".to_string(),
                "StrictlyPositiveCtorDecls".to_string(),
                "WellFormedCtorDecls".to_string(),
                "EnvSound".to_string(),
                "constant_extension_preserves_soundness".to_string(),
                "inductive_extension_preserves_soundness".to_string(),
            ]),
        })?;

        // =========================================================
        // Derived theorem: add_decl preserves KernelStateMatchesSpec
        // =========================================================
        //
        // This is the main environment-preservation theorem for #461.
        // It takes a valid kernel state, a successful add_decl on the
        // environment component, and returns a proof that the new state
        // (with extended env, same local context) also matches the spec.

        self.add_definition(SpecDefinition {
            name: "KernelAddDeclPreservesState".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx), ",
                "KernelStateMatchesSpec (KernelState.mk env ctx) -> ",
                "KernelAddDeclAccepts env env' -> ",
                "KernelStateMatchesSpec (KernelState.mk env' ctx)"
            ).to_string(),
            value_src: Some(concat!(
                "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                "(hmatch : KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                "(hadd : KernelAddDeclAccepts env env') => ",
                "KernelStateMatchesSpec.mk (KernelState.mk env' ctx) ",
                "(KernelAddDeclPreservesEnvValid env env' ctx ",
                "(KernelStateMatchesSpec.envValid (KernelState.mk env ctx) hmatch) ",
                "hadd) ",
                "(kernel_add_decl_preserves_local_ctx_wf env env' ctx ",
                "(KernelStateMatchesSpec.ctxWellFormed (KernelState.mk env ctx) hmatch) ",
                "hadd)"
            ).to_string()),
            is_axiom: false,
            description: "Main environment-preservation theorem: successful add_decl preserves KernelStateMatchesSpec. Decomposes the summary alias, applies the constructive env-validity and local-ctx-wf preservation projections, and rebuilds the summary.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateMatchesSpec".to_string(),
                "KernelAddDeclAccepts".to_string(),
                "KernelStateMatchesSpec.mk".to_string(),
                "KernelStateMatchesSpec.envValid".to_string(),
                "KernelStateMatchesSpec.ctxWellFormed".to_string(),
                "KernelAddDeclPreservesEnvValid".to_string(),
                "kernel_add_decl_preserves_local_ctx_wf".to_string(),
            ])),
            // Union of both constructive halves' closures: the env half contributes
            // kernel_add_decl_extends_env + KernelAddDeclAccepts; the ctx half contributes
            // KernelAddDeclAccepts. The consolidated raw axiom is gone (Rank-2 drain).
            axiom_deps: HashSet::from([
                "kernel_add_decl_extends_env".to_string(),
                "KernelAddDeclAccepts".to_string(),
            ]),
        })?;

        // =========================================================
        // Combined end-to-end add_decl soundness theorem
        // =========================================================
        //
        // This is the inductive step for the refinement chain:
        //   given a valid, sound kernel state, a successful add_decl
        //   produces a new state that is BOTH valid AND sound.
        // Together with KernelInitialStateValid (base case), this
        // enables reasoning about arbitrary sequences of add_decl.

        self.add_definition(SpecDefinition {
            name: "KernelAddDeclSound".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx), ",
                "KernelStateMatchesSpec (KernelState.mk env ctx) -> ",
                "EnvSound env -> ",
                "KernelAddDeclAccepts env env' -> ",
                "ProdType (KernelStateMatchesSpec (KernelState.mk env' ctx)) (EnvSound env')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                    "(hmatch : KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                    "(hsound : EnvSound env) ",
                    "(hadd : KernelAddDeclAccepts env env') => ",
                    "ProdType.mk ",
                    "(KernelStateMatchesSpec (KernelState.mk env' ctx)) ",
                    "(EnvSound env') ",
                    "(KernelAddDeclPreservesState env env' ctx hmatch hadd) ",
                    "(KernelAddDeclPreservesEnvSound env env' hsound hadd)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "End-to-end add_decl soundness theorem (inductive step): ",
                "a successful add_decl on a valid, sound kernel state produces ",
                "a new state that is both structurally valid (KernelStateMatchesSpec) ",
                "and semantically sound (EnvSound). Composes KernelAddDeclPreservesState ",
                "with KernelAddDeclPreservesEnvSound into a single ProdType pair. Together ",
                "with KernelInitialStateValid, this closes the inductive soundness ",
                "chain for arbitrary sequences of kernel declarations. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelAddDeclPreservesState".to_string(),
                "KernelAddDeclPreservesEnvSound".to_string(),
                "KernelStateMatchesSpec".to_string(),
                "KernelAddDeclAccepts".to_string(),
                "EnvSound".to_string(),
            ])),
            // Union of both components' axiom_deps:
            axiom_deps: HashSet::from([
                // From KernelAddDeclPreservesState (both halves now constructive):
                "kernel_add_decl_extends_env".to_string(),
                // From KernelAddDeclPreservesEnvSound:
                "KernelAddDeclAccepts".to_string(),
                "FreshDeclName".to_string(),
                "StrictlyPositiveCtorDecls".to_string(),
                "WellFormedCtorDecls".to_string(),
                "EnvSound".to_string(),
                "constant_extension_preserves_soundness".to_string(),
                "inductive_extension_preserves_soundness".to_string(),
            ]),
        })?;
        self.add_implementation_soundness_env_preservation_chain()?;
        self.add_implementation_soundness_env_chain_simulation()?;

        Ok(())
    }
}

#[path = "implementation_soundness_env_preservation_chain.rs"]
mod implementation_soundness_env_preservation_chain;

#[path = "implementation_soundness_env_chain_simulation.rs"]
mod implementation_soundness_env_chain_simulation;

#[cfg(test)]
#[path = "implementation_soundness_env_preservation_tests.rs"]
mod implementation_soundness_env_preservation_tests;

#[cfg(test)]
#[path = "implementation_soundness_env_preservation_chain_tests.rs"]
mod implementation_soundness_env_preservation_chain_tests;
