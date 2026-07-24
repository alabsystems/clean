// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bootstrap trust chain specification registration.
//!
//! Registers bootstrap-related inductive types and proof obligations into the
//! clean specification system, following the pattern established by
//! `sat_verify/cdcl/spec_registration.rs`.

use std::collections::HashSet;

use crate::spec::Specification;
use crate::spec::{AxiomCategory, ProofStatus, SpecDefinition, SpecError};

impl Specification {
    /// Register bootstrap trust chain specifications.
    ///
    /// Adds inductive types and proof obligations for the bootstrap verification
    /// of the clean kernel: trust levels, verification stages, and the key
    /// theorem that the kernel model faithfully represents the implementation.
    pub(crate) fn add_bootstrap_trust_chain_spec(&mut self) -> Result<(), SpecError> {
        // ── Bootstrap trust level inductive ──────────────────────────────

        self.add_inductive(
            r"inductive BootstrapTrustLevel : Type
| unverified : BootstrapTrustLevel
| lean4_proved : BootstrapTrustLevel
| self_verified : BootstrapTrustLevel
| fully_verified : BootstrapTrustLevel",
            "Trust levels for the bootstrap verification chain. \
             Unverified is the initial state; lean4_proved means Lean 4 has \
             verified the kernel model; self_verified means clean has verified \
             itself; fully_verified means both external and self verification \
             are complete.",
        )?;

        // ── Bootstrap verification stage inductive ──────────────────────

        self.add_inductive(
            r"inductive BootstrapStage : Type
| model_definition : BootstrapStage
| lean4_encoding : BootstrapStage
| lean4_proof : BootstrapStage
| self_check : BootstrapStage
| trust_chain_complete : BootstrapStage",
            "Stages of the bootstrap verification pipeline. Each stage \
             must complete before the next can begin: define the formal model, \
             encode it in Lean 4, prove soundness in Lean 4, self-verify \
             in clean, complete the trust chain.",
        )?;

        // ── Opaque type-inference functions + model fidelity — DELETED ──────
        //   (opaque-constant RE-ARCH: the RELATIONAL RESTATEMENT, 2026-07-07)
        //
        // model_infer_type, kernel_infer_type (both opaque
        // `KExpr -> ListType KExpr -> KExpr`) and bootstrap_model_fidelity
        //   (`forall e ctx, Eq KExpr (model_infer_type e ctx) (kernel_infer_type e ctx)`)
        // were all DELETED — the same false-leaf / masquerade discipline as the
        // bootstrap_type_preservation_transfer deletion below.
        //
        // WHY: bootstrap_model_fidelity was a TOTAL EQUALITY between two TOTAL
        // functions `KExpr -> ListType KExpr -> KExpr`. But the real Rust `infer`
        // (bootstrap/kernel_model.rs `model_infer_type`) is PARTIAL — it ERRORS on
        // ill-typed input. Forcing a total equality therefore demands the model and
        // the kernel AGREE on ill-typed junk that neither actually accepts: a
        // masquerade (a total function pretending to model a partial algorithm).
        // Giving `model_infer_type` a total CIC body would only deepen the trap.
        //
        // REPLACEMENT (the relational restatement, all three names retired):
        //   * `KernelInfers` (core_spec/dependent_sn_richmodel.rs) — the inductive
        //     ALGORITHMIC inference RELATION, a faithful arm-for-arm reflection of
        //     the Rust `model_infer_type` (the app arm whnf-reduces the function
        //     type and def-eq-checks the argument — the algorithm's real
        //     operations, not the declarative shape). is_axiom:false, census-neutral.
        //   * `TypingCtxConv` (same file) — the declarative-with-conversion typing
        //     judgment (the soundness target). is_axiom:false, census-neutral.
        //   * `bootstrap_infer_sound` (registered just below) — the SOUNDNESS
        //     obligation `KernelInfers G e T -> TypingCtxConv G e T`. A PENDING
        //     theorem obligation (DerivedPending), NOT a permanent trust assumption:
        //     it is what the Aristotle strategy mirror
        //     (scratch/kernelinfers_soundness_mirror.lean) targets; on a proof it
        //     re-registers as a value-bearing add_definition and leaves the census.
        //
        // kernel_infer_type was DELETED rather than kept as an "opaque external-Rust
        // reference": it had ZERO consumers (no spec dependency, no prose reference
        // outside this block) and was itself the total-function-shaped opaque
        // constant the re-arch eliminates. The faithful spec-level representation of
        // the Rust inference is now the PARTIAL relation KernelInfers; the empirical
        // model↔kernel agreement evidence is the differential fidelity_gate.rs
        // (which runs the REAL kernel and never referenced these spec tokens). No
        // total-equality axiom remains. (These were opaque Trust-boundary axioms, so
        // no computable refutation witness exists; the unsoundness of the deleted
        // fidelity axiom is by its total-vs-partial quantifier structure, as above.)

        // ── bootstrap_infer_sound : algorithmic-soundness — NOW PROVED ──
        //
        // The relational replacement for bootstrap_model_fidelity: soundness of the
        // faithful algorithmic relation KernelInfers against the declarative-with-
        // conversion judgment TypingCtxConv. FORMERLY a PENDING axiom (is_axiom:true,
        // value_src:None); NOW a value-bearing DerivedProved THEOREM — the explicit
        // KernelInfers.rec proof term below, ported back from the completed Aristotle
        // strategy proof (scratch/kernelinfers_soundness_mirror.lean elaborated clean,
        // zero sorry). NO-MASQUERADE: the Lean tactic proof is a STRATEGY GUIDE ONLY;
        // this term is re-derived against the LIVE reflected inductives and
        // kernel-checks with ZERO domain axiom_deps (transitive closure ⊆
        // foundational — verified by the spec_axiom_closure honesty gate).
        //
        // The term is induction on KernelInfers via its generated recursor:
        //   * sort/bvar/pi/lam/const  → the matching TypingCtxConv rule applied to
        //     the recursor IHs (sort/const carry no IH; pi/lam thread ihA/ihB).
        //   * app (the load-bearing arm) — the recursor hands the app minor the
        //     fields (hf : KernelInfers f F, hwF : whnf_to F (pi A B),
        //     ha : KernelInfers a A', hAA : DefEq A' A) then the two IHs
        //     (ihf : TypingCtxConv f F, iha : TypingCtxConv a A'). It builds
        //       - TypingCtxConv.conv (ihf) (whnf_to_preserves_def_eq F (pi A B) hwF)
        //         : TypingCtxConv f (pi A B)   [whnf ⊆ def-eq / subject reduction],
        //       - TypingCtxConv.conv (iha) hAA : TypingCtxConv a A,
        //     then TypingCtxConv.app on the two, concluding
        //     TypingCtxConv (app f a) (instantiate B a) — exactly the arm's output.
        //   * let_ uses the same conversion bridges for the annotation and value,
        //     then threads the body IH through TypingCtxConv.let_.
        //   The conv rule is precisely what discharges KernelInfers' faithful
        //   whnf_to+DefEq app arm; whnf_to_preserves_def_eq
        //   (implementation_soundness_whnf_decomposition.rs, DerivedProved, empty
        //   closure) is the whnf-trace → DefEq bridge (the mirror's
        //   `whnfToImpliesDefEq`; the mirror's `stepImpliesDefEq` is the already-live
        //   whnf_step_preserves_def_eq that it composes).
        //
        // Deliberately does NOT register COMPLETENESS in any form: completeness of a
        // real kernel is a sound-but-not-complete hazard (could be concretely FALSE
        // against the deployed checker); it only ever ships CandModel-conditional
        // later, never here.
        self.add_definition(SpecDefinition {
            name: "bootstrap_infer_sound".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (e : KExpr) (T : KExpr), ",
                "KernelInfers tenv G e T -> TypingCtxConv tenv G e T",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (e : KExpr) (T : KExpr) ",
                    "(h : KernelInfers tenv G e T) => ",
                    "KernelInfers.rec tenv ",
                    // motive: fun G0 e0 T0 (_ : KernelInfers tenv G0 e0 T0) => TypingCtxConv tenv G0 e0 T0
                    "(fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) (h0 : KernelInfers tenv G0 e0 T0) => ",
                    "TypingCtxConv tenv G0 e0 T0) ",
                    // sort arm
                    "(fun (G0 : ListType KExpr) (n : Level) => TypingCtxConv.sort tenv G0 n) ",
                    // bvar arm
                    "(fun (G0 : ListType KExpr) (i : Nat) (A : KExpr) ",
                    "(hlk : Eq (OptionType KExpr) (ctx_lookup G0 i) (OptionType.some KExpr A)) => ",
                    "TypingCtxConv.var tenv G0 i A hlk) ",
                    // pi arm (fields hA hB, then IHs ihA ihB)
                    "(fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) ",
                    "(hA : KernelInfers tenv G0 A (KExpr.sort n)) ",
                    "(hB : KernelInfers tenv (ListType.cons KExpr A G0) B (KExpr.sort m)) ",
                    "(ihA : TypingCtxConv tenv G0 A (KExpr.sort n)) ",
                    "(ihB : TypingCtxConv tenv (ListType.cons KExpr A G0) B (KExpr.sort m)) => ",
                    "TypingCtxConv.pi tenv G0 A B n m ihA ihB) ",
                    // lam arm (fields hA hb, then IHs ihA ihb)
                    "(fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) ",
                    "(hA : KernelInfers tenv G0 A (KExpr.sort u)) ",
                    "(hb : KernelInfers tenv (ListType.cons KExpr A G0) b B) ",
                    "(ihA : TypingCtxConv tenv G0 A (KExpr.sort u)) ",
                    "(ihb : TypingCtxConv tenv (ListType.cons KExpr A G0) b B) => ",
                    "TypingCtxConv.lam tenv G0 A b B u ihA ihb) ",
                    // const arm
                    "(fun (G0 : ListType KExpr) (nm : Name) (us : ListType Level) (A : KExpr) ",
                    "(ht : Eq (OptionType KExpr) (tenv nm) (OptionType.some KExpr A)) => ",
                    "TypingCtxConv.const tenv G0 nm us A ht) ",
                    // app arm (fields hf hwF ha hAA, then IHs ihf iha) — the load-bearing conv step
                    "(fun (G0 : ListType KExpr) (ff : KExpr) (aa : KExpr) (F : KExpr) (A : KExpr) (B : KExpr) (Ap : KExpr) ",
                    "(hf : KernelInfers tenv G0 ff F) ",
                    "(hwF : whnf_to F (KExpr.pi A B)) ",
                    "(ha : KernelInfers tenv G0 aa Ap) ",
                    "(hAA : DefEq Ap A) ",
                    "(ihf : TypingCtxConv tenv G0 ff F) ",
                    "(iha : TypingCtxConv tenv G0 aa Ap) => ",
                    "TypingCtxConv.app tenv G0 ff aa A B ",
                    "(TypingCtxConv.conv tenv G0 ff F (KExpr.pi A B) ihf ",
                    "(whnf_to_preserves_def_eq F (KExpr.pi A B) hwF)) ",
                    "(TypingCtxConv.conv tenv G0 aa Ap A iha hAA)) ",
                    // let_ arm (fields hty hwTy hv hTv hb, then IHs ihty ihv ihb) — the
                    // 7-shape closure: same conv machinery as the app arm, twice —
                    // annotation's inferred type whnf's to a sort (conv along
                    // whnf_to_preserves_def_eq), value's inferred type def-eq the
                    // annotation (conv along hTv) — then TypingCtxConv.let_.
                    "(fun (G0 : ListType KExpr) (lty : KExpr) (lv : KExpr) (lb : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr) ",
                    "(hty : KernelInfers tenv G0 lty Ty) ",
                    "(hwTy : whnf_to Ty (KExpr.sort u)) ",
                    "(hv : KernelInfers tenv G0 lv Tv) ",
                    "(hTv : DefEq Tv lty) ",
                    "(hb : KernelInfers tenv (ListType.cons KExpr lty G0) lb B) ",
                    "(ihty : TypingCtxConv tenv G0 lty Ty) ",
                    "(ihv : TypingCtxConv tenv G0 lv Tv) ",
                    "(ihb : TypingCtxConv tenv (ListType.cons KExpr lty G0) lb B) => ",
                    "TypingCtxConv.let_ tenv G0 lty lv lb B u ",
                    "(TypingCtxConv.conv tenv G0 lty Ty (KExpr.sort u) ihty ",
                    "(whnf_to_preserves_def_eq Ty (KExpr.sort u) hwTy)) ",
                    "(TypingCtxConv.conv tenv G0 lv Tv lty ihv hTv) ",
                    "ihb) ",
                    // indices + major
                    "G e T h",
                )
                .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            description: "Algorithmic soundness (DerivedProved, relational replacement for the \
                          deleted total-equality bootstrap_model_fidelity): every type the faithful \
                          algorithmic relation KernelInfers infers is a valid type in the \
                          declarative-with-conversion judgment TypingCtxConv. NOW a value-bearing \
                          THEOREM — an explicit KernelInfers.rec proof term ported back from the \
                          completed Aristotle strategy proof (scratch/kernelinfers_soundness_mirror.lean); \
                          NO-MASQUERADE: re-derived against the live reflected inductives, kernel-checks \
                          with ZERO domain axiom_deps. Induction on KernelInfers: sort/bvar/pi/lam/const \
                          map to the matching TypingCtxConv rules; the app arm is discharged via \
                          whnf_to_preserves_def_eq (whnf F->pi => DefEq F (pi A B)) then \
                          TypingCtxConv.conv, and DefEq A' A then TypingCtxConv.conv, then \
                          TypingCtxConv.app. The let_ arm (7-shape closure of the former let-free \
                          gap) replays the same conv machinery twice — annotation's inferred type \
                          whnf'd to a sort, value's inferred type def-eq the annotation — then \
                          TypingCtxConv.let_. Soundness ONLY — completeness is a sound-but-not-complete \
                          hazard and is deliberately NOT registered."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers.rec".to_string(),
                "TypingCtxConv.sort".to_string(),
                "TypingCtxConv.var".to_string(),
                "TypingCtxConv.pi".to_string(),
                "TypingCtxConv.lam".to_string(),
                "TypingCtxConv.const".to_string(),
                "TypingCtxConv.app".to_string(),
                "TypingCtxConv.let_".to_string(),
                "TypingCtxConv.conv".to_string(),
                "whnf_to_preserves_def_eq".to_string(),
                "ctx_lookup".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Type preservation transfer — DELETED (false-as-stated, unused) ──
        //
        // bootstrap_type_preservation_transfer asserted
        //   forall e e' T ctx, model_infer_type e ctx = T -> model_infer_type e' ctx = T
        // — for an ARBITRARY e', which is FALSE (its own description admitted it
        // "lacks a reduction relation connecting e to e'"): counterexample
        // e = sort 0 (infers sort 1 = T), e' = sort 1 (infers sort 2 != sort 1).
        // It was a placeholder for a real type-preservation statement (with the
        // omitted reduction hypothesis) but had ZERO consumers (grep-verified),
        // and the genuine type-preservation content already lives in
        // TypePreservation. Deleted rather than left as a false axiom in the
        // census — the same discipline as the par_subst/par_strips false-leaf
        // deletions. (model_infer_type is an opaque Trust-boundary axiom, so no
        // computable refutation witness is possible; the falseness is by the
        // stated quantifier structure, documented here.)

        Ok(())
    }
}
