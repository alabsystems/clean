// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Multi-step add_decl closure theorem for #461.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_env_preservation_chain(
        &mut self,
    ) -> Result<(), SpecError> {
        // KernelAddDeclChain was previously a HAND-AXIOMATIZED inductive: the
        // type, both constructors, AND the recursor were 4 separate
        // FoundationalRule axioms. It is now a GENUINE inductive: the ctor
        // types below transcribe the former axioms verbatim, and the kernel
        // GENERATES KernelAddDeclChain.rec (sound by construction) — the same
        // retirement applied to KernelWhnfAccepts / KernelLocalCtxWellFormed /
        // KernelDefEqAccepts. NOTE the generated recursor is NOT shaped like
        // the retired hand-written one: fixed-index promotion (the kernel's
        // `fixedIndicesToParams`) promotes the uniform first index `env` to a
        // parameter, so the motive ranges over the DESTINATION env and the
        // trace only (`P : forall (dst : KEnv), KernelAddDeclChain env dst ->
        // Sort u`), with `env` supplied once as the leading recursor argument.
        // KernelAddDeclChainSound below is written against that generated
        // eliminator shape.
        self.add_inductive(
            r"inductive KernelAddDeclChain : KEnv -> KEnv -> Type
| refl : forall (env : KEnv), KernelAddDeclChain env env
| step : forall (env : KEnv) (mid : KEnv) (env' : KEnv), KernelAddDeclChain env mid -> KernelAddDeclAccepts mid env' -> KernelAddDeclChain env env'",
            "Reflexive-transitive closure of successful production-kernel declaration \
             additions. Faithful inductive (formerly 4 hand axioms: type, refl, step, \
             and a hand-written recursor): refl is the empty chain, step extends a \
             chain with one more successful production add_decl.",
        )?;

        self.add_definition(SpecDefinition {
            name: "KernelAddDeclChainSound".to_string(),
            type_src: concat!(
                "forall (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx), ",
                "KernelAddDeclChain env env' -> ",
                "KernelStateMatchesSpec (KernelState.mk env ctx) -> ",
                "EnvSound env -> ",
                "ProdType (KernelStateMatchesSpec (KernelState.mk env' ctx)) (EnvSound env')"
            )
            .to_string(),
            // Proof by the kernel-GENERATED KernelAddDeclChain.rec. Its shape
            // (dumped from the live env):
            //   rec : (env : KEnv)
            //     -> (motive : (dst : KEnv) -> KernelAddDeclChain env dst -> Sort u)
            //     -> motive env (KernelAddDeclChain.refl env)
            //     -> ((mid : KEnv) -> (dst : KEnv)
            //         -> (hprefix : KernelAddDeclChain env mid)
            //         -> (hadd : KernelAddDeclAccepts mid dst)
            //         -> motive mid hprefix
            //         -> motive dst (KernelAddDeclChain.step env mid dst hprefix hadd))
            //     -> (dst : KEnv) -> (h : KernelAddDeclChain env dst) -> motive dst h
            // i.e. the SOURCE env is a promoted parameter (fixed-index
            // promotion), so the motive generalizes only the destination env;
            // ctx/hmatch/hsound are generalized inside the motive as before.
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                    "(hchain : KernelAddDeclChain env env') ",
                    "(hmatch : KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                    "(hsound : EnvSound env) => ",
                    "KernelAddDeclChain.rec env ",
                    "(fun (dst_env : KEnv) (_hstep : KernelAddDeclChain env dst_env) => ",
                    "forall (ctx : KernelLocalCtx), ",
                    "KernelStateMatchesSpec (KernelState.mk env ctx) -> ",
                    "EnvSound env -> ",
                    "ProdType (KernelStateMatchesSpec (KernelState.mk dst_env ctx)) (EnvSound dst_env)) ",
                    "(fun (ctx : KernelLocalCtx) ",
                    "(base_match : KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                    "(base_sound : EnvSound env) => ",
                    "ProdType.mk ",
                    "(KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                    "(EnvSound env) ",
                    "base_match base_sound) ",
                    "(fun (mid_env : KEnv) (dst_env : KEnv) ",
                    "(_hprefix : KernelAddDeclChain env mid_env) ",
                    "(hadd : KernelAddDeclAccepts mid_env dst_env) ",
                    "(ih : forall (ctx : KernelLocalCtx), ",
                    "KernelStateMatchesSpec (KernelState.mk env ctx) -> ",
                    "EnvSound env -> ",
                    "ProdType (KernelStateMatchesSpec (KernelState.mk mid_env ctx)) (EnvSound mid_env)) ",
                    "(ctx : KernelLocalCtx) ",
                    "(src_match : KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                    "(src_sound : EnvSound env) => ",
                    "KernelAddDeclSound mid_env dst_env ctx ",
                    "(ProdType.fst ",
                    "(KernelStateMatchesSpec (KernelState.mk mid_env ctx)) ",
                    "(EnvSound mid_env) ",
                    "(ih ctx src_match src_sound)) ",
                    "(ProdType.snd ",
                    "(KernelStateMatchesSpec (KernelState.mk mid_env ctx)) ",
                    "(EnvSound mid_env) ",
                    "(ih ctx src_match src_sound)) ",
                    "hadd) ",
                    "env' hchain ctx hmatch hsound"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Closure theorem for implementation declaration additions: any ",
                "KernelAddDeclChain preserves both KernelStateMatchesSpec and ",
                "EnvSound by structural recursion over the successful add_decl ",
                "trace and repeated application of KernelAddDeclSound. This ",
                "turns the one-step inductive theorem into an arbitrary-sequence ",
                "transport lemma without adding new trusted assumptions. Part of #461."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelAddDeclChain".to_string(),
                "KernelAddDeclChain.rec".to_string(),
                "KernelAddDeclSound".to_string(),
                "KernelStateMatchesSpec".to_string(),
                "KernelAddDeclAccepts".to_string(),
                "EnvSound".to_string(),
                "ProdType.mk".to_string(),
                "ProdType.fst".to_string(),
                "ProdType.snd".to_string(),
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
