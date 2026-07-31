// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Chain-aware simulation wrappers for #461.
//!
//! These lemmas make `KernelAddDeclChainSound` usable from the forward
//! simulation surface without reopening the base simulation module. The
//! production kernel extends environments through declaration chains while
//! leaving the local context unchanged; these wrappers transport
//! `KernelStateMatchesSpec` across the chain and then delegate to the existing
//! summary theorems.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_env_chain_simulation(
        &mut self,
    ) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "KernelAddDeclChainPreservesState".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx), ",
                "KernelAddDeclChain env env' -> ",
                "KernelStateMatchesSpec (KernelState.mk env ctx) -> ",
                "EnvSound env -> ",
                "KernelStateMatchesSpec (KernelState.mk env' ctx)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                    "(hchain : KernelAddDeclChain env env') ",
                    "(hmatch : KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                    "(hsound : EnvSound env) => ",
                    "ProdType.fst ",
                    "(KernelStateMatchesSpec (KernelState.mk env' ctx)) ",
                    "(EnvSound env') ",
                    "(KernelAddDeclChainSound env env' ctx hchain hmatch hsound)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Projection of KernelAddDeclChainSound onto the structural side: ",
                "a successful declaration chain preserves KernelStateMatchesSpec ",
                "for an unchanged local context. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelAddDeclChain".to_string(),
                "KernelAddDeclChainSound".to_string(),
                "KernelStateMatchesSpec".to_string(),
                "EnvSound".to_string(),
                "ProdType.fst".to_string(),
            ])),
            axiom_deps: HashSet::from([
                "kernel_add_decl_extends_env".to_string(),
                "KernelAddDeclAccepts".to_string(),
                "FreshDeclName".to_string(),
                "StrictlyPositiveCtorDecls".to_string(),
                "WellFormedCtorDecls".to_string(),
                "EnvSound".to_string(),
                "constant_extension_preserves_soundness".to_string(),
                "inductive_extension_preserves_soundness".to_string(),
            ]),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelInferSound_chain".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                "(e : KExpr) (T : KExpr), ",
                "KernelAddDeclChain env env' -> ",
                "KernelStateMatchesSpec (KernelState.mk env ctx) -> ",
                "EnvSound env -> ",
                "KernelInputAdmissible (KernelState.mk env' ctx) e -> ",
                "KernelInferAccepts (KernelState.mk env' ctx) e T -> ",
                "has_type e T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                    "(e : KExpr) (T : KExpr) ",
                    "(hchain : KernelAddDeclChain env env') ",
                    "(hmatch : KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                    "(hsound : EnvSound env) ",
                    "(hin : KernelInputAdmissible (KernelState.mk env' ctx) e) ",
                    "(haccept : KernelInferAccepts (KernelState.mk env' ctx) e T) => ",
                    "KernelInferSound_summary (KernelState.mk env' ctx) e T ",
                    "(KernelAddDeclChainPreservesState env env' ctx hchain hmatch hsound) ",
                    "hin haccept"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Chain-aware forward simulation for infer_type: transport the ",
                "summary state relation across KernelAddDeclChain via ",
                "KernelAddDeclChainPreservesState, then delegate to ",
                "KernelInferSound_summary. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelAddDeclChain".to_string(),
                "KernelAddDeclChainPreservesState".to_string(),
                "KernelStateMatchesSpec".to_string(),
                "EnvSound".to_string(),
                "KernelInputAdmissible".to_string(),
                "KernelInferAccepts".to_string(),
                "KernelInferSound_summary".to_string(),
            ])),
            axiom_deps: HashSet::from([
                "kernel_add_decl_extends_env".to_string(),
                "KernelAddDeclAccepts".to_string(),
                "FreshDeclName".to_string(),
                "StrictlyPositiveCtorDecls".to_string(),
                "WellFormedCtorDecls".to_string(),
                "EnvSound".to_string(),
                "constant_extension_preserves_soundness".to_string(),
                "inductive_extension_preserves_soundness".to_string(),
                // The six per-case infer axioms are no longer axiom leaves
                // (derived from the faithful KernelInferAccepts inductive via
                // kernel_infer_inversion); the infer side's residual is the
                // master inversion's closure (10 infer-band skolems +
                // KernelCheckAccepts) plus the check/defeq band.
                "kernel_infer_returns_well_typed".to_string(),
            ]),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelCheckSound_chain".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                "(e : KExpr) (T : KExpr), ",
                "KernelAddDeclChain env env' -> ",
                "KernelStateMatchesSpec (KernelState.mk env ctx) -> ",
                "EnvSound env -> ",
                "KernelInputAdmissible (KernelState.mk env' ctx) e -> ",
                "KernelCheckAccepts (KernelState.mk env' ctx) e T -> ",
                "has_type e T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                    "(e : KExpr) (T : KExpr) ",
                    "(hchain : KernelAddDeclChain env env') ",
                    "(hmatch : KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                    "(hsound : EnvSound env) ",
                    "(hin : KernelInputAdmissible (KernelState.mk env' ctx) e) ",
                    "(haccept : KernelCheckAccepts (KernelState.mk env' ctx) e T) => ",
                    "KernelCheckSound_summary (KernelState.mk env' ctx) e T ",
                    "(KernelAddDeclChainPreservesState env env' ctx hchain hmatch hsound) ",
                    "hin haccept"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Chain-aware forward simulation for check_type. Transports ",
                "KernelStateMatchesSpec across KernelAddDeclChain and then reuses ",
                "KernelCheckSound_summary. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelAddDeclChain".to_string(),
                "KernelAddDeclChainPreservesState".to_string(),
                "KernelStateMatchesSpec".to_string(),
                "EnvSound".to_string(),
                "KernelInputAdmissible".to_string(),
                "KernelCheckAccepts".to_string(),
                "KernelCheckSound_summary".to_string(),
            ])),
            axiom_deps: HashSet::from([
                "kernel_add_decl_extends_env".to_string(),
                "KernelAddDeclAccepts".to_string(),
                "FreshDeclName".to_string(),
                "StrictlyPositiveCtorDecls".to_string(),
                "WellFormedCtorDecls".to_string(),
                "EnvSound".to_string(),
                "constant_extension_preserves_soundness".to_string(),
                "inductive_extension_preserves_soundness".to_string(),
                "kernel_infer_returns_well_typed".to_string(),
            ]),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelWhnfSound_chain".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                "(e : KExpr) (e'' : KExpr), ",
                "KernelAddDeclChain env env' -> ",
                "KernelStateMatchesSpec (KernelState.mk env ctx) -> ",
                "EnvSound env -> ",
                "KernelInputAdmissible (KernelState.mk env' ctx) e -> ",
                "KernelWhnfAccepts (KernelState.mk env' ctx) e e'' -> ",
                "is_def_eq e e''"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                    "(e : KExpr) (e'' : KExpr) ",
                    "(hchain : KernelAddDeclChain env env') ",
                    "(hmatch : KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                    "(hsound : EnvSound env) ",
                    "(hin : KernelInputAdmissible (KernelState.mk env' ctx) e) ",
                    "(haccept : KernelWhnfAccepts (KernelState.mk env' ctx) e e'') => ",
                    "KernelWhnfSound_summary (KernelState.mk env' ctx) e e'' ",
                    "(KernelAddDeclChainPreservesState env env' ctx hchain hmatch hsound) ",
                    "hin haccept"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Chain-aware forward simulation for whnf. Transports the state ",
                "summary through KernelAddDeclChain and then delegates to ",
                "KernelWhnfSound_summary. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelAddDeclChain".to_string(),
                "KernelAddDeclChainPreservesState".to_string(),
                "KernelStateMatchesSpec".to_string(),
                "EnvSound".to_string(),
                "KernelInputAdmissible".to_string(),
                "KernelWhnfAccepts".to_string(),
                "KernelWhnfSound_summary".to_string(),
            ])),
            axiom_deps: HashSet::from([
                "kernel_add_decl_extends_env".to_string(),
                "KernelAddDeclAccepts".to_string(),
                "FreshDeclName".to_string(),
                "StrictlyPositiveCtorDecls".to_string(),
                "WellFormedCtorDecls".to_string(),
                "EnvSound".to_string(),
                "constant_extension_preserves_soundness".to_string(),
                "inductive_extension_preserves_soundness".to_string(),
            ]),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelDefEqSound_chain".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                "(a : KExpr) (b : KExpr), ",
                "KernelAddDeclChain env env' -> ",
                "KernelStateMatchesSpec (KernelState.mk env ctx) -> ",
                "EnvSound env -> ",
                "KernelBinaryInputAdmissible (KernelState.mk env' ctx) a b -> ",
                "KernelDefEqAccepts (KernelState.mk env' ctx) a b -> ",
                "is_def_eq a b"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                    "(a : KExpr) (b : KExpr) ",
                    "(hchain : KernelAddDeclChain env env') ",
                    "(hmatch : KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                    "(hsound : EnvSound env) ",
                    "(hin : KernelBinaryInputAdmissible (KernelState.mk env' ctx) a b) ",
                    "(haccept : KernelDefEqAccepts (KernelState.mk env' ctx) a b) => ",
                    "KernelDefEqSound_summary (KernelState.mk env' ctx) a b ",
                    "(KernelAddDeclChainPreservesState env env' ctx hchain hmatch hsound) ",
                    "hin haccept"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Chain-aware forward simulation for is_def_eq. Transports the ",
                "summary state relation across KernelAddDeclChain and delegates ",
                "to KernelDefEqSound_summary. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelAddDeclChain".to_string(),
                "KernelAddDeclChainPreservesState".to_string(),
                "KernelStateMatchesSpec".to_string(),
                "EnvSound".to_string(),
                "KernelBinaryInputAdmissible".to_string(),
                "KernelDefEqAccepts".to_string(),
                "KernelDefEqSound_summary".to_string(),
            ])),
            axiom_deps: HashSet::from([
                "kernel_add_decl_extends_env".to_string(),
                "KernelAddDeclAccepts".to_string(),
                "FreshDeclName".to_string(),
                "StrictlyPositiveCtorDecls".to_string(),
                "WellFormedCtorDecls".to_string(),
                "EnvSound".to_string(),
                "constant_extension_preserves_soundness".to_string(),
                "inductive_extension_preserves_soundness".to_string(),
            ]),
        })?;

        Ok(())
    }
}
