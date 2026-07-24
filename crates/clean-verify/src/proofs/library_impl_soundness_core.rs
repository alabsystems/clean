// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Implementation soundness core proof terms for the kernel ProofLibrary.
//!
//! Part of #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_impl_soundness_core_proofs(&mut self) {
        // =============================================================
        // From implementation_soundness.rs (PART 21: state bridge defs)
        // =============================================================

        // KernelStateEnvValid: semireducible state-indexed env-validity
        self.proofs.insert(
            "KernelStateEnvValid".to_string(),
            ProofTerm::new(
                "KernelStateEnvValid",
                "fun (st : KernelState) => KernelState.rec (fun (_ : KernelState) => Type) (fun (env : KEnv) (_ctx : KernelLocalCtx) => KernelEnvValid env) st",
                "Semireducible state-indexed environment-validity predicate via KernelState.rec.",
            ),
        );

        // KernelStateLocalCtxWellFormed: semireducible state-indexed local-context wf
        self.proofs.insert(
            "KernelStateLocalCtxWellFormed".to_string(),
            ProofTerm::new(
                "KernelStateLocalCtxWellFormed",
                "fun (st : KernelState) => KernelState.rec (fun (_ : KernelState) => Type) (fun (env : KEnv) (ctx : KernelLocalCtx) => KernelLocalCtxWellFormed env ctx) st",
                "Semireducible state-indexed local-context well-formedness predicate via KernelState.rec.",
            ),
        );

        // KernelStateMatchesSpec: semireducible summary correspondence
        self.proofs.insert(
            "KernelStateMatchesSpec".to_string(),
            ProofTerm::new(
                "KernelStateMatchesSpec",
                "fun (st : KernelState) => AndType (KernelStateEnvValid st) (KernelStateLocalCtxWellFormed st)",
                "Semireducible summary correspondence relation packaging split env-validity and local-context invariants.",
            ),
        );

        // KernelStateMatchesSpec.mk: build summary from split predicates
        self.proofs.insert(
            "KernelStateMatchesSpec.mk".to_string(),
            ProofTerm::new(
                "KernelStateMatchesSpec.mk",
                "fun (st : KernelState) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) => AndType.intro (KernelStateEnvValid st) (KernelStateLocalCtxWellFormed st) henv hctx",
                "Build summary implementation/spec correspondence from split bridge predicates via AndType.intro.",
            ),
        );

        // KernelStateMatchesSpec.envValid: extract env-validity
        self.proofs.insert(
            "KernelStateMatchesSpec.envValid".to_string(),
            ProofTerm::new(
                "KernelStateMatchesSpec.envValid",
                "fun (st : KernelState) (h : KernelStateMatchesSpec st) => AndType.left (KernelStateEnvValid st) (KernelStateLocalCtxWellFormed st) h",
                "Extract environment-validity from summary correspondence via AndType.left.",
            ),
        );

        // KernelStateMatchesSpec.ctxWellFormed: extract local-context wf
        self.proofs.insert(
            "KernelStateMatchesSpec.ctxWellFormed".to_string(),
            ProofTerm::new(
                "KernelStateMatchesSpec.ctxWellFormed",
                "fun (st : KernelState) (h : KernelStateMatchesSpec st) => AndType.right (KernelStateEnvValid st) (KernelStateLocalCtxWellFormed st) h",
                "Extract local-context well-formedness from summary correspondence via AndType.right.",
            ),
        );

        // KernelInitialStateValid: base case of the inductive chain
        self.proofs.insert(
            "KernelInitialStateValid".to_string(),
            ProofTerm::new(
                "KernelInitialStateValid",
                concat!(
                    "KernelStateMatchesSpec.mk ",
                    "(KernelState.mk KEnv.empty KernelLocalCtx.nil) ",
                    "kernel_empty_env_valid ",
                    "kernel_empty_ctx_well_formed"
                ),
                "Initial kernel state (empty env, empty local ctx) satisfies KernelStateMatchesSpec. Base case of the inductive refinement chain.",
            ),
        );

        // ================================================================
        // From implementation_soundness_simulation.rs (forward simulation)
        // ================================================================

        // KernelInferSound: named forward-simulation for infer_type
        self.proofs.insert(
            "KernelInferSound".to_string(),
            ProofTerm::new(
                "KernelInferSound",
                "fun (st : KernelState) (e : KExpr) (T : KExpr) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelInputAdmissible st e) (haccept : KernelInferAccepts st e T) => kernel_infer_returns_well_typed st e T henv hctx hin haccept",
                "Named forward-simulation theorem for infer_type over the core specification fragment.",
            ),
        );

        // KernelCheckSound: named forward-simulation for check_type
        self.proofs.insert(
            "KernelCheckSound".to_string(),
            ProofTerm::new(
                "KernelCheckSound",
                "fun (st : KernelState) (e : KExpr) (T : KExpr) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelInputAdmissible st e) (haccept : KernelCheckAccepts st e T) => kernel_check_returns_well_typed st e T henv hctx hin haccept",
                "Named forward-simulation theorem for check_type over the core specification fragment.",
            ),
        );

        // KernelWhnfSound: named forward-simulation for whnf
        self.proofs.insert(
            "KernelWhnfSound".to_string(),
            ProofTerm::new(
                "KernelWhnfSound",
                "fun (st : KernelState) (e : KExpr) (e' : KExpr) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelInputAdmissible st e) (haccept : KernelWhnfAccepts st e e') => kernel_whnf_returns_def_eq st e e' henv hctx hin haccept",
                "Named forward-simulation theorem for whnf over the core specification fragment.",
            ),
        );

        // KernelDefEqSound: named forward-simulation for is_def_eq
        self.proofs.insert(
            "KernelDefEqSound".to_string(),
            ProofTerm::new(
                "KernelDefEqSound",
                "fun (st : KernelState) (a : KExpr) (b : KExpr) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelBinaryInputAdmissible st a b) (haccept : KernelDefEqAccepts st a b) => kernel_def_eq_reflects_spec st a b henv hctx hin haccept",
                "Named forward-simulation theorem for is_def_eq over the core specification fragment.",
            ),
        );

        // KernelWhnfPreservesTyping: derived corollary
        self.proofs.insert(
            "KernelWhnfPreservesTyping".to_string(),
            ProofTerm::new(
                "KernelWhnfPreservesTyping",
                "fun (hf : RedEnvFaithful the_red_env) (st : KernelState) (e : KExpr) (e' : KExpr) (T : KExpr) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) (hin : KernelInputAdmissible st e) (haccept : KernelWhnfAccepts st e e') (ht : has_type e T) => whnf_to_preserves_typing hf e e' T wd wr (kernel_whnf_reduces_to_spec_whnf st e e' henv hctx hin haccept) ht",
                "Derived corollary: kernel WHNF preserves typing via whnf_to_preserves_typing composed with kernel_whnf_reduces_to_spec_whnf (forward directed subject reduction; #2859 retired the symmetric raw bridge).",
            ),
        );

        // KernelInferSound_summary: summary-alias wrapper for infer
        self.proofs.insert(
            "KernelInferSound_summary".to_string(),
            ProofTerm::new(
                "KernelInferSound_summary",
                "fun (st : KernelState) (e : KExpr) (T : KExpr) (hmatch : KernelStateMatchesSpec st) (hin : KernelInputAdmissible st e) (haccept : KernelInferAccepts st e T) => KernelInferSound st e T (KernelStateMatchesSpec.envValid st hmatch) (KernelStateMatchesSpec.ctxWellFormed st hmatch) hin haccept",
                "Forward simulation for infer_type via summary alias: decomposes KernelStateMatchesSpec and delegates to KernelInferSound.",
            ),
        );

        // KernelCheckSound_summary: summary-alias wrapper for check
        self.proofs.insert(
            "KernelCheckSound_summary".to_string(),
            ProofTerm::new(
                "KernelCheckSound_summary",
                "fun (st : KernelState) (e : KExpr) (T : KExpr) (hmatch : KernelStateMatchesSpec st) (hin : KernelInputAdmissible st e) (haccept : KernelCheckAccepts st e T) => KernelCheckSound st e T (KernelStateMatchesSpec.envValid st hmatch) (KernelStateMatchesSpec.ctxWellFormed st hmatch) hin haccept",
                "Forward simulation for check_type via summary alias: decomposes KernelStateMatchesSpec and delegates to KernelCheckSound.",
            ),
        );

        // KernelWhnfSound_summary: summary-alias wrapper for whnf
        self.proofs.insert(
            "KernelWhnfSound_summary".to_string(),
            ProofTerm::new(
                "KernelWhnfSound_summary",
                "fun (st : KernelState) (e : KExpr) (e' : KExpr) (hmatch : KernelStateMatchesSpec st) (hin : KernelInputAdmissible st e) (haccept : KernelWhnfAccepts st e e') => KernelWhnfSound st e e' (KernelStateMatchesSpec.envValid st hmatch) (KernelStateMatchesSpec.ctxWellFormed st hmatch) hin haccept",
                "Forward simulation for whnf via summary alias: decomposes KernelStateMatchesSpec and delegates to KernelWhnfSound.",
            ),
        );

        // KernelDefEqSound_summary: summary-alias wrapper for def_eq
        self.proofs.insert(
            "KernelDefEqSound_summary".to_string(),
            ProofTerm::new(
                "KernelDefEqSound_summary",
                "fun (st : KernelState) (a : KExpr) (b : KExpr) (hmatch : KernelStateMatchesSpec st) (hin : KernelBinaryInputAdmissible st a b) (haccept : KernelDefEqAccepts st a b) => KernelDefEqSound st a b (KernelStateMatchesSpec.envValid st hmatch) (KernelStateMatchesSpec.ctxWellFormed st hmatch) hin haccept",
                "Forward simulation for is_def_eq via summary alias: decomposes KernelStateMatchesSpec and delegates to KernelDefEqSound.",
            ),
        );

        // ====================================================================
        // From implementation_soundness_env_preservation.rs (env preservation)
        // ====================================================================

        // kernel_add_decl_preserves_env_valid_raw: now derived CONSTRUCTIVELY by
        // composing the impl-to-spec bridge with the foundational extension-chain
        // transitivity (mirrors the spec value_src; no ProdType projection).
        self.proofs.insert(
            "kernel_add_decl_preserves_env_valid_raw".to_string(),
            ProofTerm::new(
                "kernel_add_decl_preserves_env_valid_raw",
                concat!(
                    "fun (env : KEnv) (env' : KEnv) ",
                    "(henv : KernelEnvValid env) ",
                    "(hadd : KernelAddDeclAccepts env env') => ",
                    "DefinitionalExtension.trans KEnv.empty env env' henv ",
                    "(kernel_add_decl_extends_env env env' hadd)"
                ),
                "Raw env-validity preservation: KernelEnvValid env unfolds (semireducibly) to DefinitionalExtension KEnv.empty env, kernel_add_decl_extends_env gives the immediate DefinitionalExtension env env' step, and DefinitionalExtension.trans composes them into KernelEnvValid env'.",
            ),
        );

        // KernelAddDeclPreservesEnvValid: state-indexed env-validity wrapper
        self.proofs.insert(
            "KernelAddDeclPreservesEnvValid".to_string(),
            ProofTerm::new(
                "KernelAddDeclPreservesEnvValid",
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                    "(henv : KernelStateEnvValid (KernelState.mk env ctx)) ",
                    "(hadd : KernelAddDeclAccepts env env') => ",
                    "kernel_add_decl_preserves_env_valid_raw env env' henv hadd"
                ),
                "State-indexed env-validity preservation wrapper for add_decl, factoring through raw projection.",
            ),
        );

        // kernel_add_decl_preserves_local_ctx_wf_raw: raw local-context preservation,
        // derived CONSTRUCTIVELY by KernelLocalCtxWellFormed.rec env-transport replay
        // (Rank-2). env is a uniform/phantom parameter and the cons premise
        // Typing ty (KExpr.sort u) is env-free, so the recursor motive admits the env
        // re-index and every witness rebuilds under env'.
        self.proofs.insert(
            "kernel_add_decl_preserves_local_ctx_wf_raw".to_string(),
            ProofTerm::new(
                "kernel_add_decl_preserves_local_ctx_wf_raw",
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
                ),
                "Raw local-context preservation via KernelLocalCtxWellFormed.rec env-transport replay: nil rebuilds as nil env', cons rebuilds as cons env' reusing the env-free Typing derivation and the transported tail. The KernelAddDeclAccepts hypothesis is unused; env transport is purely structural.",
            ),
        );

        // kernel_add_decl_preserves_local_ctx_wf: state-indexed local-context wrapper
        self.proofs.insert(
            "kernel_add_decl_preserves_local_ctx_wf".to_string(),
            ProofTerm::new(
                "kernel_add_decl_preserves_local_ctx_wf",
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                    "(hctx : KernelStateLocalCtxWellFormed (KernelState.mk env ctx)) ",
                    "(hadd : KernelAddDeclAccepts env env') => ",
                    "kernel_add_decl_preserves_local_ctx_wf_raw env env' ctx hctx hadd"
                ),
                "State-indexed local-context preservation wrapper for add_decl, factoring through raw projection.",
            ),
        );

        // KernelAddDeclPreservesEnvSound: add_decl preserves EnvSound
        self.proofs.insert(
            "KernelAddDeclPreservesEnvSound".to_string(),
            ProofTerm::new(
                "KernelAddDeclPreservesEnvSound",
                concat!(
                    "fun (env : KEnv) (env' : KEnv) ",
                    "(hsound : EnvSound env) ",
                    "(hadd : KernelAddDeclAccepts env env') => ",
                    "definitional_extension_sound env env' ",
                    "(kernel_add_decl_extends_env env env' hadd) ",
                    "hsound"
                ),
                "Derived corollary: add_decl preserves spec-level environment soundness via definitional_extension_sound.",
            ),
        );

        // KernelAddDeclPreservesState: main env-preservation theorem
        self.proofs.insert(
            "KernelAddDeclPreservesState".to_string(),
            ProofTerm::new(
                "KernelAddDeclPreservesState",
                concat!(
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
                ),
                "Main environment-preservation theorem: successful add_decl preserves KernelStateMatchesSpec.",
            ),
        );

        // KernelAddDeclSound: combined end-to-end theorem (inductive step)
        self.proofs.insert(
            "KernelAddDeclSound".to_string(),
            ProofTerm::new(
                "KernelAddDeclSound",
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
                ),
                "End-to-end add_decl soundness (inductive step): produces both KernelStateMatchesSpec and EnvSound for the new state.",
            ),
        );

        // =============================================================
        // From implementation_soundness_env_preservation_chain.rs
        // =============================================================

        // KernelAddDeclChainSound: closure theorem via structural recursion.
        // Written against the kernel-GENERATED KernelAddDeclChain.rec (the
        // chain is a genuine inductive; fixed-index promotion makes the source
        // env a recursor parameter, so the motive generalizes only the
        // destination env). Mirrors the spec value_src in
        // implementation_soundness_env_preservation_chain.rs.
        self.proofs.insert(
            "KernelAddDeclChainSound".to_string(),
            ProofTerm::new(
                "KernelAddDeclChainSound",
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
                ),
                "Closure theorem: any KernelAddDeclChain preserves both KernelStateMatchesSpec and EnvSound by structural recursion over the add_decl trace (kernel-generated recursor).",
            ),
        );

        // =============================================================
        // From implementation_soundness_env_chain_simulation.rs
        // =============================================================

        // KernelAddDeclChainPreservesState: structural projection of chain sound
        self.proofs.insert(
            "KernelAddDeclChainPreservesState".to_string(),
            ProofTerm::new(
                "KernelAddDeclChainPreservesState",
                concat!(
                    "fun (env : KEnv) (env' : KEnv) (ctx : KernelLocalCtx) ",
                    "(hchain : KernelAddDeclChain env env') ",
                    "(hmatch : KernelStateMatchesSpec (KernelState.mk env ctx)) ",
                    "(hsound : EnvSound env) => ",
                    "ProdType.fst ",
                    "(KernelStateMatchesSpec (KernelState.mk env' ctx)) ",
                    "(EnvSound env') ",
                    "(KernelAddDeclChainSound env env' ctx hchain hmatch hsound)"
                ),
                "Projection of KernelAddDeclChainSound onto structural side: declaration chain preserves KernelStateMatchesSpec.",
            ),
        );

        // KernelInferSound_chain: chain-aware forward simulation for infer
        self.proofs.insert(
            "KernelInferSound_chain".to_string(),
            ProofTerm::new(
                "KernelInferSound_chain",
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
                ),
                "Chain-aware forward simulation for infer_type: transport state via KernelAddDeclChainPreservesState then delegate to KernelInferSound_summary.",
            ),
        );

        // KernelCheckSound_chain: chain-aware forward simulation for check
        self.proofs.insert(
            "KernelCheckSound_chain".to_string(),
            ProofTerm::new(
                "KernelCheckSound_chain",
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
                ),
                "Chain-aware forward simulation for check_type: transport state via KernelAddDeclChainPreservesState then delegate to KernelCheckSound_summary.",
            ),
        );

        // KernelWhnfSound_chain: chain-aware forward simulation for whnf
        self.proofs.insert(
            "KernelWhnfSound_chain".to_string(),
            ProofTerm::new(
                "KernelWhnfSound_chain",
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
                ),
                "Chain-aware forward simulation for whnf: transport state via KernelAddDeclChainPreservesState then delegate to KernelWhnfSound_summary.",
            ),
        );

        // KernelDefEqSound_chain: chain-aware forward simulation for def_eq
        self.proofs.insert(
            "KernelDefEqSound_chain".to_string(),
            ProofTerm::new(
                "KernelDefEqSound_chain",
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
                ),
                "Chain-aware forward simulation for is_def_eq: transport state via KernelAddDeclChainPreservesState then delegate to KernelDefEqSound_summary.",
            ),
        );
    }
}
