// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Implementation-state correspondence and forward soundness contracts for #461.
//!
//! This module mirrors the production kernel's REQUIRES/ENSURES contracts:
//! `TypeChecker` constructors assume a consistent environment and well-formed
//! local context, while `infer_type`, `check_type`, `whnf`, and `is_def_eq`
//! assume admissible inputs and promise typing/def-eq facts on success.
//! Phase 4 needs those assumptions named explicitly inside the specification so
//! the trusted theory base can track them as pending implementation proofs.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // PART 21: Kernel implementation/state correspondence (#461)
        // =========================================================
        //
        // The core KExpr fragment is environment-free. This slice adds an
        // abstract model of the kernel's runtime state and the admissibility
        // invariants required by the production `TypeChecker` entry points so
        // Phase 4 can state the implementation-soundness boundary directly.

        self.add_inductive(
            r"inductive KernelLocalDecl : Type
| mk : Nat -> KExpr -> KernelLocalDecl",
            "Abstract local context entry: implementation local identifier plus its type in the core KExpr fragment.",
        )?;

        self.add_inductive(
            r"inductive KernelLocalCtx : Type
| nil : KernelLocalCtx
| cons : KernelLocalDecl -> KernelLocalCtx -> KernelLocalCtx",
            "Abstract local context for implementation/spec correspondence.",
        )?;

        self.add_inductive(
            r"inductive KernelState : Type
| mk : KEnv -> KernelLocalCtx -> KernelState",
            "Abstract kernel state used by the implementation-soundness layer: specification environment plus local context.",
        )?;

        // KernelEnvValid: FAITHFUL reducible definition (was a bare KEnv -> Type
        // HelperAxiom). The TypeChecker constructor precondition "env is a
        // consistent kernel environment" is DEFINED as its spec twin EnvSound env,
        // which itself unfolds (one further layer) to the real reachability
        // witness DefinitionalExtension KEnv.empty env — carrying every
        // constant/inductive step's well-typedness side-conditions (FreshDeclName,
        // Typing, StrictlyPositiveCtorDecls, WellFormedCtorDecls) through the
        // ConstantExtension/InductiveExtension constructors. This is NOT a vacuous
        // stand-in and NOT a separate twin collapsed to identity: KernelEnvValid IS
        // the consumed precondition threaded (opaquely) through the forward-sim
        // chain, and it now reduces to the genuinely-inhabited soundness witness.
        // Registered semireducibly (add_definition_reducible) so it unfolds to
        // EnvSound env during declaration checking, exactly like KernelInputAdmissible
        // (:= is_closed) above. EnvSound (PART 20) is registered before this PART 21,
        // so the dependency points backward.
        self.add_definition_reducible(SpecDefinition {
            name: "KernelEnvValid".to_string(),
            type_src: "KEnv -> Type".to_string(),
            value_src: Some("fun (env : KEnv) => EnvSound env".to_string()),
            is_axiom: false,
            description:
                "KernelEnvValid env: the TypeChecker constructor precondition that env is a consistent kernel environment, DEFINED as its spec twin EnvSound env (reachability from the empty environment by a valid definitional-extension chain). Faithful: unfolds to the real DefinitionalExtension KEnv.empty env witness carrying every step's well-typedness side-conditions, not a vacuous always-true predicate."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["EnvSound".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // KernelLocalCtxWellFormed was previously an opaque HelperAxiom of type
        // `KEnv -> KernelLocalCtx -> Type`. It is now a FAITHFUL inductive that
        // mirrors the production kernel's per-binder local-context invariant: every
        // declaration's domain type must itself be a Sort. `env : KEnv` is a UNIFORM
        // PARAMETER (a phantom, since the spec `Typing` judgment is env-free) — this
        // keeps the recursor motive env-free, the st-uniform discipline used for
        // KernelWhnfAccepts above. The `nil` ctor witnesses the empty context; the
        // `cons` ctor demands a REAL `Typing ty (KExpr.sort u)` derivation (the
        // domain-is-a-Sort check infer.rs imposes on Lam/Pi before ctx_push) plus a
        // recursive well-formedness proof of the tail. This is NOT vacuity (cons
        // requires an inhabited Typing derivation) and NOT a thin-def. The signature
        // is unchanged (KEnv -> KernelLocalCtx -> Type), so every applied/hypothesis
        // position across the soundness chain still type-checks.
        self.add_inductive(
            r"inductive KernelLocalCtxWellFormed (env : KEnv) : KernelLocalCtx → Type
| nil : KernelLocalCtxWellFormed env KernelLocalCtx.nil
| cons : forall (id : Nat) (ty : KExpr) (u : Level) (rest : KernelLocalCtx), Typing ty (KExpr.sort u) → KernelLocalCtxWellFormed env rest → KernelLocalCtxWellFormed env (KernelLocalCtx.cons (KernelLocalDecl.mk id ty) rest)",
            "Implementation-side local-context well-formedness: KernelLocalCtxWellFormed \
             env ctx holds when every declaration's domain type is a Sort. Faithful \
             inductive with env as a uniform (phantom, since spec Typing is env-free) \
             parameter; nil on the empty context, cons demanding a real Typing ty \
             (KExpr.sort u) domain-is-a-Sort derivation plus tail well-formedness.",
        )?;

        self.add_definition_reducible(SpecDefinition {
            name: "KernelStateEnvValid".to_string(),
            type_src: "KernelState -> Type".to_string(),
            value_src: Some("fun (st : KernelState) => KernelState.rec (fun (_ : KernelState) => Type) (fun (env : KEnv) (_ctx : KernelLocalCtx) => KernelEnvValid env) st".to_string()),
            is_axiom: false,
            description: "Semireducible state-indexed environment-validity predicate. This pulls the environment side of the implementation/spec bridge out of the summary alias while still unfolding to KernelEnvValid env during declaration checking.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KernelEnvValid".to_string()])),
            // KernelEnvValid is now a DerivedProved DerivedLemma (:= EnvSound), so it
            // is no longer an axiom leaf; this alias's transitive axiom closure is now
            // empty. KernelStateEnvValid stays DerivedPending: it is still an abstract
            // state invariant surfaced as a pending implementation assumption.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_reducible(SpecDefinition {
            name: "KernelStateLocalCtxWellFormed".to_string(),
            type_src: "KernelState -> Type".to_string(),
            value_src: Some("fun (st : KernelState) => KernelState.rec (fun (_ : KernelState) => Type) (fun (env : KEnv) (ctx : KernelLocalCtx) => KernelLocalCtxWellFormed env ctx) st".to_string()),
            is_axiom: false,
            description: "Semireducible state-indexed local-context well-formedness predicate. This keeps the local-context side of the state bridge explicit while still unfolding to KernelLocalCtxWellFormed env ctx during declaration checking.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KernelLocalCtxWellFormed".to_string()])),
            // KernelLocalCtxWellFormed is now a faithful inductive (nil/cons), not a
            // HelperAxiom, so it is no longer an axiom leaf; this alias's transitive
            // axiom closure is now empty. KernelStateLocalCtxWellFormed stays
            // DerivedPending: it is still an abstract state invariant surfaced as a
            // pending implementation assumption.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_reducible(SpecDefinition {
            name: "KernelStateMatchesSpec".to_string(),
            type_src: "KernelState -> Type".to_string(),
            value_src: Some("fun (st : KernelState) => AndType (KernelStateEnvValid st) (KernelStateLocalCtxWellFormed st)".to_string()),
            is_axiom: false,
            description: "Semireducible summary correspondence relation between a production-kernel state and the specification environment/context it is supposed to implement. In the current core-fragment slice this packages the split environment-validity and local-context invariants while still unfolding to the underlying AndType during declaration checking.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateEnvValid".to_string(),
                "KernelStateLocalCtxWellFormed".to_string(),
            ])),
            // KernelEnvValid retired to a DerivedProved DerivedLemma (:= EnvSound) and
            // KernelLocalCtxWellFormed retired to a faithful nil/cons inductive, so
            // neither is an axiom leaf any longer; this summary's transitive axiom
            // closure is now empty.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelStateMatchesSpec.mk".to_string(),
            type_src: "forall (st : KernelState), KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> KernelStateMatchesSpec st".to_string(),
            value_src: Some("fun (st : KernelState) (henv : KernelStateEnvValid st) (hctx : KernelStateLocalCtxWellFormed st) => AndType.intro (KernelStateEnvValid st) (KernelStateLocalCtxWellFormed st) henv hctx".to_string()),
            is_axiom: false,
            description: "Build the summary implementation/spec correspondence from the split bridge predicates. DerivedPending because the bridge is constructive, but its state predicates still depend on implementation-side invariants.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateMatchesSpec".to_string(),
                "KernelStateEnvValid".to_string(),
                "KernelStateLocalCtxWellFormed".to_string(),
                "AndType.intro".to_string(),
            ])),
            // KernelEnvValid retired to a DerivedProved DerivedLemma (:= EnvSound) and
            // KernelLocalCtxWellFormed retired to a faithful nil/cons inductive, so
            // neither is an axiom leaf any longer; transitive axiom closure now empty.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelStateMatchesSpec.envValid".to_string(),
            type_src: "forall (st : KernelState), KernelStateMatchesSpec st -> KernelStateEnvValid st".to_string(),
            value_src: Some("fun (st : KernelState) (h : KernelStateMatchesSpec st) => AndType.left (KernelStateEnvValid st) (KernelStateLocalCtxWellFormed st) h".to_string()),
            is_axiom: false,
            description: "Extract environment-validity from the summary correspondence. DerivedPending because the projection is constructive, but the summary alias still packages pending implementation-side invariants.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateMatchesSpec".to_string(),
                "KernelStateEnvValid".to_string(),
                "KernelStateLocalCtxWellFormed".to_string(),
                "AndType.left".to_string(),
            ])),
            // KernelEnvValid retired to a DerivedProved DerivedLemma (:= EnvSound) and
            // KernelLocalCtxWellFormed retired to a faithful nil/cons inductive, so
            // neither is an axiom leaf any longer; transitive axiom closure now empty.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelStateMatchesSpec.ctxWellFormed".to_string(),
            type_src: "forall (st : KernelState), KernelStateMatchesSpec st -> KernelStateLocalCtxWellFormed st".to_string(),
            value_src: Some("fun (st : KernelState) (h : KernelStateMatchesSpec st) => AndType.right (KernelStateEnvValid st) (KernelStateLocalCtxWellFormed st) h".to_string()),
            is_axiom: false,
            description: "Extract local-context well-formedness from the summary correspondence. DerivedPending because the projection is constructive, but the summary alias still packages pending implementation-side invariants.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateMatchesSpec".to_string(),
                "KernelStateEnvValid".to_string(),
                "KernelStateLocalCtxWellFormed".to_string(),
                "AndType.right".to_string(),
            ])),
            // KernelEnvValid retired to a DerivedProved DerivedLemma (:= EnvSound) and
            // KernelLocalCtxWellFormed retired to a faithful nil/cons inductive, so
            // neither is an axiom leaf any longer; transitive axiom closure now empty.
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_reducible(SpecDefinition {
            name: "KernelInputAdmissible".to_string(),
            type_src: "KernelState -> KExpr -> Type".to_string(),
            value_src: Some("fun (st : KernelState) (e : KExpr) => is_closed e".to_string()),
            is_axiom: false,
            description: "KernelInputAdmissible st e is the core-fragment admissibility predicate for unary entry points. On the current KExpr slice, admissibility is exactly closedness: the expression has no dangling bound variables. Semireducible so proof terms can unfold it during declaration checking (needed for bvar case in kernel_infer_returns_well_typed).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["is_closed".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_reducible(SpecDefinition {
            name: "KernelBinaryInputAdmissible".to_string(),
            type_src: "KernelState -> KExpr -> KExpr -> Type".to_string(),
            value_src: Some("fun (st : KernelState) (a : KExpr) (b : KExpr) => AndType (KernelInputAdmissible st a) (KernelInputAdmissible st b)".to_string()),
            is_axiom: false,
            description: "KernelBinaryInputAdmissible st a b packages the unary admissibility proof for each argument of a binary kernel entry point. Semireducible (like KernelInputAdmissible) so proof terms can unfold it to AndType during declaration checking — needed to CONSTRUCT a binary-admissibility value (infer_result_self_admissible, the census-11 drain guard); the trivial non-recursive AndType alias makes unfolding O(1)-safe.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KernelInputAdmissible".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // KernelInferAccepts was here as an opaque HelperAxiom of type
        // `KernelState -> KExpr -> KExpr -> Type`. It is now a FAITHFUL
        // 5-constructor inductive (sort/const/app/lam/pi, no bvar) registered in
        // implementation_soundness_infer_accepts.rs (the next bundle stage),
        // together with the 10 infer-band Skolem witnesses its constructor
        // fields apply and the master inversion kernel_infer_inversion from
        // which the six formerly-assumed per-case infer axioms are now derived.

        // KernelCheckAccepts was here as an opaque HelperAxiom of type
        // `KernelState -> KExpr -> KExpr -> Type`. It is now a FAITHFUL
        // single-constructor inductive registered in
        // implementation_soundness_infer_accepts.rs (the next bundle stage,
        // Step 4), AFTER the faithful KernelInferAccepts inductive its mk
        // constructor's decomposition field references (check_type = infer_type
        // + is_def_eq, so the check acceptance witness carries an infer
        // acceptance at the KernelInferResult skolem). The declared signature
        // is unchanged.

        // KernelWhnfAccepts was previously an opaque HelperAxiom of type
        // `KernelState -> KExpr -> KExpr -> Type`. It is now a FAITHFUL inductive
        // that mirrors the production kernel's WHNF loop, structurally identical
        // to the spec `whnf_to` relation (whnf_reduction.rs): a refl ctor on a
        // term already in WHNF, and a step ctor over a single `whnf_step`
        // (beta/delta) followed by a tail reduction. `st : KernelState` is a
        // UNIFORM PARAMETER (not an index) — the ctor indices live only on the
        // KExpr arguments. Keeping `st` uniform makes the recursor motive
        // st-free, which is what lets the bridge `kernel_whnf_reduces_to_spec_whnf`
        // be a genuine structural recursion rather than an assumed axiom.
        // The signature is unchanged (KernelState -> KExpr -> KExpr -> Type), so
        // every applied/hypothesis position across the soundness chain still
        // type-checks. Modeled on `par_reduces_p` (par_reduces_p.rs), which
        // carries `env : RecEnv` as the analogous uniform parameter.
        self.add_inductive(
            r"inductive KernelWhnfAccepts (st : KernelState) : KExpr → KExpr → Type
| refl : forall (e : KExpr), is_whnf e → KernelWhnfAccepts st e e
| step : forall (e : KExpr) (e' : KExpr) (v : KExpr), whnf_step e e' → KernelWhnfAccepts st e' v → KernelWhnfAccepts st e v",
            "Successful production-kernel WHNF reduction: KernelWhnfAccepts st e e' \
             means the kernel's whnf loop reduced e to e' (e' in bounded WHNF for \
             the current const+delta fragment). Faithful inductive mirror of the \
             spec whnf_to relation with st as a uniform parameter; refl on a WHNF \
             term, step over a single whnf_step then a tail reduction.",
        )?;

        // DefEqJoinable a b: the PACKAGED EXISTENTIAL "a and b reduce to
        // definitionally-equal forms" — the joinability witness that RETIRES the two
        // KernelDefEqNormalLeft / KernelDefEqNormalRight Skolem FUNCTIONS. The single
        // `mk` constructor binds the two common reducts nl/nr INTERNALLY (as
        // existentially-quantified ctor arguments) instead of naming them by opaque
        // Skolem functions of (st, a, b); it packages exactly the old three-part
        // evidence (DefEq a nl, DefEq b nr, DefEq nl nr). This is a real
        // `add_inductive` (Declaration::Inductive, NOT a value-less axiom), so it
        // leaves the ConstantKind::Axiom census; its `.mk`/`.rec` are kernel-generated
        // and sound by construction. `def_eq_joinable_reflects`
        // (implementation_soundness_defeq_decomposition.rs) eliminates it to the
        // skolem-free `DefEq a b`. Registered BEFORE KernelDefEqAccepts because that
        // inductive's mk field concludes in DefEqJoinable a b.
        self.add_inductive(
            r"inductive DefEqJoinable : KExpr → KExpr → Type
| mk : forall (a : KExpr) (b : KExpr) (nl : KExpr) (nr : KExpr), DefEq a nl → DefEq b nr → DefEq nl nr → DefEqJoinable a b",
            "Joinability witness for definitional equality: DefEqJoinable a b holds when a and b \
             reduce to definitionally-equal forms. The single mk constructor binds the two common \
             reducts nl/nr internally (the packaged existential), carrying DefEq a nl, DefEq b nr, \
             and DefEq nl nr — exactly the content the production kernel's is_def_eq normalization \
             establishes, but WITHOUT naming the reducts by Skolem functions of the inputs. This \
             retires KernelDefEqNormalLeft/Right; it eliminates to the skolem-free DefEq a b via \
             def_eq_joinable_reflects.",
        )?;

        // KernelDefEqAccepts was previously an opaque HelperAxiom of type
        // `KernelState -> KExpr -> KExpr -> Type`. It is now a FAITHFUL inductive
        // mirroring the production kernel's is_def_eq success contract. The single
        // mk constructor's single field is the GUARDED implication
        //   KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st ->
        //   KernelBinaryInputAdmissible st a b -> DefEqJoinable a b
        // — i.e. EXACTLY what the opaque token plus the old kernel_defeq_decomposition
        // axiom jointly asserted about every accepted pair, guards included, now with
        // the def-eq evidence carried by the skolem-free DefEqJoinable packaged
        // existential instead of the ProdType-of-Skolem-normal-forms triple. An
        // UNGUARDED field would be strictly STRONGER than the old assumption
        // (it would let every producer axiom concluding an Accepts assert spec-DefEq
        // facts in arbitrary — including invalid — kernel states, which the old
        // KernelStateEnvValid guard deliberately excluded); an adversarial audit
        // caught exactly that overreach in the first draft of this conversion.
        // The DefEqJoinable field type (not whnf_to) is the honest reduction
        // vocabulary: is_def_eq interleaves no-delta whnf_core with one-step lazy
        // delta and congruence/eta/proof-irrelevance acceptance, so whnf_to fields
        // would be FALSE for acceptances that reduce nothing. Because the
        // constructor's conclusion is uniform in (a, b), the elaborator PROMOTES
        // st/a/b to inductive parameters — the generated recursor is the param-fixed
        // AndType.rec shape (motive over the major premise only), NOT
        // KernelWhnfAccepts' index-motive shape. The declared signature
        // KernelState -> KExpr -> KExpr -> Type is unchanged, so every
        // applied/hypothesis position across the soundness chain still
        // type-checks. kernel_def_eq_reflects_spec is now DERIVED from
        // KernelDefEqAccepts.rec (implementation_soundness_defeq_decomposition.rs)
        // by applying the constructor's guarded-implication field to the
        // reflection's own guard premises, then eliminating DefEqJoinable.
        self.add_inductive(
            r"inductive KernelDefEqAccepts (st : KernelState) : KExpr → KExpr → Type
| mk : forall (a : KExpr) (b : KExpr), (KernelStateEnvValid st → KernelStateLocalCtxWellFormed st → KernelBinaryInputAdmissible st a b → DefEqJoinable a b) → KernelDefEqAccepts st a b",
            "Successful production-kernel definitional equality: KernelDefEqAccepts st a b \
             means is_def_eq returned true for a and b. Faithful inductive in GUARDED form: \
             the constructor field is the implication from state validity, local-context \
             well-formedness, and binary input admissibility to DefEqJoinable a b (a and b \
             reduce to definitionally-equal forms) — exactly the content of the \
             formerly-assumed kernel_defeq_decomposition, guards included, with the def-eq \
             evidence carried by the skolem-free DefEqJoinable packaged existential.",
        )?;

        // kernel_infer_returns_well_typed was here as a HelperAxiom.
        // Now decomposed into per-case forward simulation axioms in
        // implementation_soundness_infer_refinement.rs (PART 21f) and
        // derived via KExpr.rec case dispatch. The BVar case is
        // discharged constructively from the closedness precondition.

        // kernel_whnf_returns_def_eq was here as a HelperAxiom.
        // Now decomposed into a narrower bridge axiom
        // (kernel_whnf_reduces_to_spec_whnf), the remaining
        // whnf_to->DefEq spec-closure helper, and the follow-on
        // beta_reduces decomposition leaf in
        // implementation_soundness_whnf_decomposition.rs (PART 21e).

        // kernel_def_eq_reflects_spec was here as a HelperAxiom.
        // Now decomposed into normalization + structural comparison in
        // implementation_soundness_defeq_decomposition.rs (PART 21d).

        // =========================================================
        // Initial state validity (base case for the inductive chain)
        // =========================================================
        //
        // The refinement proof has an inductive structure:
        //   Base: the initial kernel state is valid
        //   Step: each add_decl preserves validity + soundness
        // These axioms + derived theorem supply the base case.

        // kernel_empty_env_valid: now a PROVED term, not a HelperAxiom. With
        // KernelEnvValid env := EnvSound env := DefinitionalExtension KEnv.empty env,
        // the goal `KernelEnvValid KEnv.empty` reducibly unfolds to
        // `DefinitionalExtension KEnv.empty KEnv.empty`, which is inhabited by the
        // reflexive extension constructor. The empty environment is reachable from
        // itself by the empty (zero-step) chain — exactly the base case of the
        // inductive refinement chain. Closure ⊆ the DefinitionalExtension.refl
        // FoundationalRule leaf (no HelperAxiom); recorded with empty axiom_deps so
        // the dependency audit drains every list that named it as a leaf.
        self.add_definition(SpecDefinition {
            name: "kernel_empty_env_valid".to_string(),
            type_src: "KernelEnvValid KEnv.empty".to_string(),
            value_src: Some("DefinitionalExtension.refl KEnv.empty".to_string()),
            is_axiom: false,
            description: "The production kernel's empty environment (Environment::new()) satisfies KernelEnvValid. PROVED: KernelEnvValid KEnv.empty unfolds (via EnvSound) to DefinitionalExtension KEnv.empty KEnv.empty, inhabited by DefinitionalExtension.refl — the empty environment is reachable from itself by the zero-step extension chain. This is the base case for the inductive chain.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelEnvValid".to_string(),
                "EnvSound".to_string(),
                "DefinitionalExtension.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kernel_empty_ctx_well_formed: now a PROVED term, not a HelperAxiom. With
        // KernelLocalCtxWellFormed retired to a faithful inductive (env uniform
        // parameter, nil/cons), the goal `KernelLocalCtxWellFormed KEnv.empty
        // KernelLocalCtx.nil` is inhabited directly by the nil constructor applied to
        // the empty environment. The empty local context has no binder whose domain
        // could fail the per-binder Sort check — exactly the base case of the
        // inductive refinement chain. Closure ⊆ the KernelLocalCtxWellFormed.nil
        // FoundationalRule ctor leaf (no HelperAxiom); recorded with empty axiom_deps
        // so the dependency audit drains every list that named it as a leaf.
        self.add_definition(SpecDefinition {
            name: "kernel_empty_ctx_well_formed".to_string(),
            type_src: "KernelLocalCtxWellFormed KEnv.empty KernelLocalCtx.nil".to_string(),
            value_src: Some("KernelLocalCtxWellFormed.nil KEnv.empty".to_string()),
            is_axiom: false,
            description: "The empty local context is well-formed in the empty environment. PROVED: KernelLocalCtxWellFormed KEnv.empty KernelLocalCtx.nil is inhabited by the nil constructor applied to KEnv.empty — an empty context has no declaration whose domain type could fail the per-binder Sort check. This is the base case for the inductive chain.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelLocalCtxWellFormed".to_string(),
                "KernelLocalCtxWellFormed.nil".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "KernelInitialStateValid".to_string(),
            type_src: "KernelStateMatchesSpec (KernelState.mk KEnv.empty KernelLocalCtx.nil)".to_string(),
            value_src: Some(concat!(
                "KernelStateMatchesSpec.mk ",
                "(KernelState.mk KEnv.empty KernelLocalCtx.nil) ",
                "kernel_empty_env_valid ",
                "kernel_empty_ctx_well_formed"
            ).to_string()),
            is_axiom: false,
            description: "The initial kernel state (empty environment, empty local context) satisfies KernelStateMatchesSpec. This is the base case of the inductive refinement chain: starting from this state, each subsequent add_decl preserves validity via KernelAddDeclPreservesState.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelStateMatchesSpec.mk".to_string(),
                "kernel_empty_env_valid".to_string(),
                "kernel_empty_ctx_well_formed".to_string(),
            ])),
            // kernel_empty_env_valid is now a DerivedProved DerivedLemma (proved via
            // DefinitionalExtension.refl) and kernel_empty_ctx_well_formed is now a
            // DerivedProved DerivedLemma (proved via KernelLocalCtxWellFormed.nil), so
            // neither is an axiom leaf any longer; transitive axiom closure now empty.
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_tests.rs"]
mod implementation_soundness_tests;
