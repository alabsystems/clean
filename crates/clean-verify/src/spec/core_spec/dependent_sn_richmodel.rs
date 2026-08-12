// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rich-model (dependent, context-indexed) typing judgment — Brick 2 of the
//! fidelity re-architecture (`designs/2026-07-06-fidelity-rearchitecture.md`).
//!
//! FIRST PORTED PIECE of the dependent-SN metatheory strategy guide
//! `proofs/lean-aristotle/dependent_sn_modulo_candmodel.lean` (Lean, complete,
//! `#print axioms` = propext/Quot.sound MODULO a `CandModel`). The guide's
//! §8b `TypingCtx` is the intended dependent judgment: the context-indexed
//! generalization of the DEGENERATE env-free `Typing` (`typing_def_eq.rs`), WITH
//! the two rules the degenerate fragment omits — the de Bruijn `var` rule (which
//! re-opens genuine free variables, so β no longer degenerates) and the `const`
//! rule (typing a defined constant at its declared type, looked up in a
//! const-typing environment). It is over THIS judgment that SN genuinely needs
//! the Girard reducibility candidates (the isolated Gödel floor); see the guide's
//! Part 2 and the design doc's Brick 1/2.
//!
//! ## Reconciliation with clean-verify (established this port)
//!
//! - `KExpr` — the guide's transcription matches the live `KExpr`
//!   (`expr_model.rs`): sort/bvar/app/lam/pi/const PLUS the genuine 7th `let_`
//!   constructor (let promotion, task #28; SN guide
//!   `scratch/aristotle-harvest/aristotle-sn-let/aristotle-sn-let_aristotle/SnLet.lean`).
//!   Every full KExpr.rec in this file
//!   carries the trailing let_ minor; every beta_reduces case analysis carries
//!   the zeta + let_ty/let_val/let_body minors (old bundled let_body position,
//!   iota last); FVRel/TypingCtx/TypingCtxConv carry trailing let_ rules; the
//!   CandModel carries the redLet zeta weak-head-expansion closure field and the
//!   fundamental tower the fundamental_let adequacy case.
//! - `lift_at` / `instantiate` / `imax_nat` — already registered (expr_model.rs,
//!   typing_universe_levels.rs); reused verbatim in the constructor conclusions.
//! - Env parametrization: the guide's `WhnfStep denv renv` / `TypingCtx tenv` are
//!   env-PARAMETRIC; clean-verify's live `whnf_step` / `delta_reduces` /
//!   `iota_reduces` are env-FIXED to `the_red_env`. The FUTURE SN theorem must be
//!   pinned to that fixed env; the TypingCtx judgment itself only needs the
//!   const-typing env `tenv`, which we carry as an inductive PARAMETER (a total
//!   map `Name -> OptionType KExpr` sending each defined name to its declared
//!   TYPE — the type-level companion of `DefEnv`, which stores δ-bodies).
//! - Prop vs Type: the guide states `TypingCtx : ... -> Prop`; clean-verify's
//!   `add_inductive` elaborates families into `Type` (exactly as the live
//!   `Typing`/`DefEq` are `KExpr -> KExpr -> Type`). We follow the live idiom.
//!
//! ## Census impact (confirmed)
//!
//! `TypingCtx` is a positivity-checked `add_inductive`: it lowers to
//! `Declaration::Inductive` + `Declaration::Constructor` + `Declaration::Recursor`
//! — NONE of which are `ConstantKind::Axiom`. So this piece is census-NEUTRAL (the
//! live-env axiom census is unchanged). Census growth happens later, only when the
//! metatheory ASSERTS a `CandModel` exists (that single structure instance is the
//! Gödel-floor labeled assumption). Adding the judgment costs zero axioms.
//!
//! ## What is (and is NOT) done here
//!
//! This registers the dependent judgment + its lookup function + non-vacuity
//! witnesses, ALONGSIDE (not replacing) the degenerate `Typing`. The census-16
//! degenerate `whnf_terminates_well_typed` lane is untouched and stays green. The
//! Girard machinery (`CandModel`, `Neutral`, `psubst`, CR1-3, `fundamental*`,
//! `whnf_terminates_well_typed_dependent`) has SINCE LANDED in this same module.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the rich-model dependent typing judgment `TypingCtx`, its context
    /// lookup `ctx_lookup`, and two non-vacuity witnesses (a `sort` inhabitant and
    /// a `var` inhabitant — the latter exercising the NEW de Bruijn `var` rule and
    /// the `ctx_lookup` computation).
    ///
    /// MUST be registered AFTER `add_expr_model` (`KExpr`/`lift_at`/`instantiate`),
    /// `add_typing_universe_levels` (`imax_nat`) and the foundation types
    /// (`Eq`/`Nat`/`OptionType`/`ListType`/`Name`/`Level`). Placed right after
    /// `add_whnf_terminates_well_typed` in the Substitution bundle so it sits
    /// alongside the degenerate lane without perturbing it.
    ///
    /// Part of Brick 2 (`designs/2026-07-06-fidelity-rearchitecture.md`).
    pub(super) fn add_dependent_sn_richmodel(&mut self) -> Result<(), SpecError> {
        // ctx_lookup G i : the i-th entry of context G (Γ[i]?), the guide's
        // `ctx_get?` (`dependent_sn_modulo_candmodel.lean:878`). Recursion on the
        // LIST returning a function `Nat -> OptionType KExpr` (the proven-safe
        // Nat+ListType idiom used by `list_take`, iota_step.rs) — avoids nested
        // match. cons a rest at index 0 -> some a; at succ n -> ctx_lookup rest n.
        self.add_recursive_def(
            r"def ctx_lookup (g : ListType KExpr) : Nat -> OptionType KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => Nat -> OptionType KExpr) (fun (_ : Nat) => OptionType.none KExpr) (fun (a : KExpr) (rest : ListType KExpr) (ih : Nat -> OptionType KExpr) => fun (i : Nat) => Nat.rec (fun (_ : Nat) => OptionType KExpr) (OptionType.some KExpr a) (fun (n : Nat) (_ : OptionType KExpr) => ih n) i) g",
            "Context lookup Γ[i]? for the dependent judgment: the i-th declared type in \
             context g, or none. Mirrors the guide's ctx_get? \
             (dependent_sn_modulo_candmodel.lean:878). Total, structural on the list.",
        )?;

        // TypingCtx tenv G e T : the context-indexed dependent typing judgment
        // (guide §8b, dependent_sn_modulo_candmodel.lean:888-905). Parameter `tenv`
        // is the const-typing environment (Name -> declared TYPE). Indices G/e/T
        // are non-uniform (var/const use arbitrary G; pi/lam premise on cons A G),
        // so they stay genuine INDICES and the generated recursor keeps the 3-ary
        // index motive. Constructors var/sort/pi/lam/app/const: the two NEW rules
        // vs the degenerate `Typing` are `var` (de Bruijn free variables — β no
        // longer degenerates) and `const` (defined-constant typing at its declared
        // type). Positivity is identical in shape to the live `Typing` (recursive
        // occurrences are strictly-positive premises). ZERO new axioms
        // (Inductive/Constructor/Recursor, not Axiom).
        self.add_inductive(
            concat!(
                "inductive TypingCtx (tenv : Name -> OptionType KExpr) : ListType KExpr -> KExpr -> KExpr -> Type\n",
                "| var : forall (G : ListType KExpr) (i : Nat) (A : KExpr), Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> TypingCtx tenv G (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))\n",
                "| sort : forall (G : ListType KExpr) (n : Level), TypingCtx tenv G (KExpr.sort n) (KExpr.sort (Level.succ n))\n",
                "| pi : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level), TypingCtx tenv G A (KExpr.sort n) -> TypingCtx tenv (ListType.cons KExpr A G) B (KExpr.sort m) -> TypingCtx tenv G (KExpr.pi A B) (KExpr.sort (Level.imax n m))\n",
                "| lam : forall (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingCtx tenv G A (KExpr.sort u) -> TypingCtx tenv (ListType.cons KExpr A G) b B -> TypingCtx tenv G (KExpr.lam A b) (KExpr.pi A B)\n",
                "| app : forall (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr), TypingCtx tenv G f (KExpr.pi A B) -> TypingCtx tenv G a A -> TypingCtx tenv G (KExpr.app f a) (instantiate B a)\n",
                "| const : forall (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr), Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> TypingCtx tenv G (KExpr.const n us) A\n",
                "| let_ : forall (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingCtx tenv G ty (KExpr.sort u) -> TypingCtx tenv G v ty -> TypingCtx tenv (ListType.cons KExpr ty G) b B -> TypingCtx tenv G (KExpr.let_ ty v b) (instantiate B v)"
            ),
            "Context-indexed dependent typing judgment (Brick 2 rich model): TypingCtx tenv G e T means e has type T in context G under const-typing environment tenv. The context-indexed generalization of the degenerate env-free Typing, WITH the de Bruijn `var` rule (bvar i : the i+1-lifted declared type looked up in G) and the `const` rule (const n us : its declared type tenv n), the two rules the degenerate fragment omits. var re-opens genuine free variables so β no longer degenerates — it is over THIS judgment that SN needs the Girard reducibility candidates (the isolated Gödel floor; guide Part 2). Faithful transcription of the strategy guide's TypingCtx (dependent_sn_modulo_candmodel.lean:888-905). Kernel generates TypingCtx.rec, sound by construction. ZERO new axioms (Inductive/Constructor/Recursor, census-neutral). LET INCREMENT (task #28): the trailing let_ rule is the standard dependent let (ty : sort u, v : ty, body : B under cons ty G, let : instantiate B v — guide SnLet.lean:1004); TypingCtx.rec gains a trailing 7th minor (fundamental_general).",
        )?;

        // Non-vacuity witness #1 (sort): sort 0 : sort 1 in the empty context under
        // the empty const-env. Pure constructor application, no computation. Mirrors
        // the guide's §9 non-vacuity example. Confirms the inductive is inhabited
        // and constructor application type-checks.
        self.add_definition(SpecDefinition {
            name: "typingctx_sort_witness".to_string(),
            type_src: "TypingCtx (fun (nm : Name) => OptionType.none KExpr) (ListType.nil KExpr) (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))".to_string(),
            value_src: Some(
                "TypingCtx.sort (fun (nm : Name) => OptionType.none KExpr) (ListType.nil KExpr) Level.zero".to_string(),
            ),
            is_axiom: false,
            description: "Non-vacuity witness for the dependent judgment: (sort 0 : sort 1) in the \
                          empty context under the empty const-env. Pure constructor application \
                          (TypingCtx.sort), zero axiom_deps. Confirms TypingCtx is inhabited."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtx".to_string(),
                "OptionType".to_string(),
                "ListType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Non-vacuity witness #2 (var): bvar 0 : (lift_at (sort 0) 0 1) in context
        // [sort 0], exercising the NEW de Bruijn `var` rule and the ctx_lookup
        // computation (ctx_lookup [sort 0] 0 reduces to some (sort 0), discharged by
        // refl). This is the rule the degenerate `Typing` OMITS — the concrete proof
        // that the rich judgment genuinely fires on a free variable. The stated type
        // is the RAW constructor conclusion (uses lift_at, no reliance on defeq
        // reduction in the type).
        self.add_definition(SpecDefinition {
            name: "typingctx_var_witness".to_string(),
            type_src: "TypingCtx (fun (nm : Name) => OptionType.none KExpr) (ListType.cons KExpr (KExpr.sort Level.zero) (ListType.nil KExpr)) (KExpr.bvar Nat.zero) (lift_at (KExpr.sort Level.zero) Nat.zero (Nat.succ Nat.zero))".to_string(),
            value_src: Some(
                "TypingCtx.var (fun (nm : Name) => OptionType.none KExpr) (ListType.cons KExpr (KExpr.sort Level.zero) (ListType.nil KExpr)) Nat.zero (KExpr.sort Level.zero) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero)))".to_string(),
            ),
            is_axiom: false,
            description: "Non-vacuity witness exercising the NEW var rule: bvar 0 : lift_at (sort 0) 0 1 \
                          in context [sort 0]. The ctx_lookup [sort 0] 0 = some (sort 0) premise is \
                          discharged by refl (computational). Confirms the de Bruijn var rule the \
                          degenerate Typing omits genuinely fires. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtx".to_string(),
                "ctx_lookup".to_string(),
                "Eq.refl".to_string(),
                "lift_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // OPAQUE-CONSTANT RE-ARCH — the RELATIONAL RESTATEMENT.
        //
        // Replaces the DELETED total-equality axioms `model_infer_type` +
        // `bootstrap_model_fidelity` (bootstrap/spec_registration.rs). Those
        // asserted a TOTAL model function `KExpr -> ListType KExpr -> KExpr`
        // agreeing with the Rust kernel on ALL inputs, INCLUDING ill-typed junk —
        // a masquerade trap, because the real Rust `infer` is PARTIAL, so a total
        // equality forces agreement on garbage the algorithm never accepts.
        //
        // The restatement instead reflects the Rust algorithm as an inductive
        // INFERENCE RELATION `KernelInfers` (object-of-study, is_axiom:false) and
        // states its SOUNDNESS (`bootstrap_infer_sound`,
        // bootstrap/spec_registration.rs) against a declarative-with-conversion
        // judgment `TypingCtxConv`. Both inductives are census-NEUTRAL
        // (Inductive/Constructor/Recursor, never ConstantKind::Axiom).
        // ================================================================

        // KernelInfers tenv G e T : the ALGORITHMIC type-inference relation,
        // FAITHFUL (arm-for-arm) to the real Rust `model_infer_type`
        // (crates/clean-verify/src/bootstrap/kernel_model.rs:152). Each
        // constructor transcribes one `match` arm using the algorithm's ACTUAL
        // operations, NOT the declarative shape:
        //   - sort  : `Sort(n) => Sort(n+1)`.
        //   - bvar  : ctx lookup then de Bruijn lift by `i+1`
        //             (`lift(ctx[pos], depth-pos)`, cutoff 0).
        //   - pi    : infer domain `: Sort n`; infer codomain (ctx extended by A)
        //             `: Sort m`; result `Sort (imax n m)`.
        //   - lam   : infer domain `: Sort u` (the algorithm REQUIRES a sort but
        //             DISCARDS the level `u`); infer body (ctx extended) `: B`;
        //             result `Pi A B`.
        //   - const : `env.get_type(n)`  (`tenv n = some A`).
        //   - app   : infer f `: F`; **whnf-reduce F to `Pi A B`** (`model_whnf`
        //             + `expect_pi`); infer a `: A'`; **check `A'` def-eq `A`**
        //             (`model_is_def_eq`); result `instantiate B a`.  <<< the
        //             CRUCIAL faithful arm: it whnf-reduces the FUNCTION type and
        //             def-eq-checks the ARGUMENT — exactly the two operations the
        //             Rust `App` arm performs — NOT the declarative `f : Pi A B` /
        //             `a : A` shape (that would be an unfaithful masquerade). Uses
        //             the live `whnf_to` (whnf_reduction.rs) + `DefEq`
        //             (typing_def_eq.rs) inductives verbatim.
        //   - let_  : infer the annotation type and whnf it to a sort; infer the
        //             value and check its type def-eq the annotation; infer the
        //             body under the annotation binder; instantiate with the value.
        //             This is the genuine 7th algorithmic shape, and the matching
        //             KernelInfers.rec minor is consumed by bootstrap_infer_sound.
        // ZERO new axioms (Inductive/Constructor/Recursor, census-neutral).
        self.add_inductive(
            concat!(
                "inductive KernelInfers (tenv : Name -> OptionType KExpr) : ListType KExpr -> KExpr -> KExpr -> Type\n",
                "| sort : forall (G : ListType KExpr) (n : Level), KernelInfers tenv G (KExpr.sort n) (KExpr.sort (Level.succ n))\n",
                "| bvar : forall (G : ListType KExpr) (i : Nat) (A : KExpr), Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> KernelInfers tenv G (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))\n",
                "| pi : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (SA : KExpr) (n : Level) (SB : KExpr) (m : Level), KernelInfers tenv G A SA -> whnf_to SA (KExpr.sort n) -> KernelInfers tenv (ListType.cons KExpr A G) B SB -> whnf_to SB (KExpr.sort m) -> KernelInfers tenv G (KExpr.pi A B) (KExpr.sort (Level.imax n m))\n",
                "| lam : forall (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (SA : KExpr) (u : Level), KernelInfers tenv G A SA -> whnf_to SA (KExpr.sort u) -> KernelInfers tenv (ListType.cons KExpr A G) b B -> KernelInfers tenv G (KExpr.lam A b) (KExpr.pi A B)\n",
                "| const : forall (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr), Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> KernelInfers tenv G (KExpr.const n us) A\n",
                "| app : forall (G : ListType KExpr) (f : KExpr) (a : KExpr) (F : KExpr) (A : KExpr) (B : KExpr) (A' : KExpr), KernelInfers tenv G f F -> whnf_to F (KExpr.pi A B) -> KernelInfers tenv G a A' -> DefEq A' A -> KernelInfers tenv G (KExpr.app f a) (instantiate B a)\n",
                "| let_ : forall (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr), KernelInfers tenv G ty Ty -> whnf_to Ty (KExpr.sort u) -> KernelInfers tenv G v Tv -> DefEq Tv ty -> KernelInfers tenv (ListType.cons KExpr ty G) b B -> KernelInfers tenv G (KExpr.let_ ty v b) (instantiate B v)"
            ),
            "Algorithmic type-inference relation KernelInfers tenv G e T: a FAITHFUL arm-for-arm \
             reflection of the real Rust model_infer_type (bootstrap/kernel_model.rs). sort/bvar/pi/\
             lam/const transcribe the corresponding match arms; the CRUCIAL app arm uses the \
             algorithm's own operations — whnf-reduce the function type F to a Pi A B (whnf_to) and \
             check the argument type A' def-eq the domain A (DefEq) — NOT the declarative f:Pi A B / \
             a:A shape (which would be an unfaithful masquerade). The let_ arm (7th, closing the \
             let-free-surface gap) mirrors the CHECK-MODE kernel let path (tc/infer.rs Let arm, \
             infer_only=false) in the same idiom: infer the annotation's type Ty and whnf it to a \
             sort (whnf_to Ty (sort u)), infer the value's type Tv and check it def-eq the \
             annotation (DefEq Tv ty), infer the body under the binder, conclude instantiate B v \
             (the algorithm's subst_fvar zeta). This is the object-of-study of the \
             opaque-constant re-architecture (relational restatement of the deleted total-equality \
             model_infer_type / bootstrap_model_fidelity axioms). Kernel generates KernelInfers.rec, \
             sound by construction. ZERO new axioms (census-neutral).",
        )?;

        // Non-vacuity witness for KernelInfers: (sort 0 : sort 1) in the empty
        // context under the empty const-env. Pure constructor application
        // (KernelInfers.sort), zero axiom_deps; also an elaboration smoke test
        // confirming the inductive is well-formed and inhabited.
        self.add_definition(SpecDefinition {
            name: "kernelinfers_sort_witness".to_string(),
            type_src: "KernelInfers (fun (nm : Name) => OptionType.none KExpr) (ListType.nil KExpr) (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))".to_string(),
            value_src: Some(
                "KernelInfers.sort (fun (nm : Name) => OptionType.none KExpr) (ListType.nil KExpr) Level.zero".to_string(),
            ),
            is_axiom: false,
            description: "Non-vacuity witness for the algorithmic relation: (sort 0 : sort 1) in the \
                          empty context. Pure constructor application (KernelInfers.sort), zero \
                          axiom_deps. Confirms KernelInfers is inhabited."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers".to_string(),
                "OptionType".to_string(),
                "ListType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // TypingCtxConv tenv G e T : the DECLARATIVE-with-conversion typing
        // judgment — TypingCtx's base rules (var/sort/pi/lam/app/const), the
        // dependent let rule, and the standard CIC conversion rule `conv`, with
        // recursive premises taken over TypingCtxConv. This is the SOUNDNESS
        // TARGET for KernelInfers
        // (`bootstrap_infer_sound`: KernelInfers G e T -> TypingCtxConv G e T).
        //
        // WHY a SEPARATE judgment (not a `conv` ctor bolted onto TypingCtx): the
        // existing `TypingCtx.rec` has a LIVE consumer — `fundamental_general`
        // (this file, the Girard SN port) dispatches over exactly TypingCtx's six
        // minor premises. Adding a seventh (conv) minor would change the recursor
        // shape and break that proof term (spec would fail to build). TypingCtxConv
        // is the conversion-CLOSED superset judgment (TypingCtx ⊆ TypingCtxConv),
        // leaving the SN lane and its recursor untouched. It is the genuine
        // declarative CIC judgment (the degenerate env-free `Typing` likewise
        // carries a `conv` rule); its premises range over TypingCtxConv so the
        // soundness INDUCTION on KernelInfers composes (the pi/lam/app IHs are
        // already TypingCtxConv derivations).
        //
        // The `conv` rule is exactly what discharges KernelInfers' faithful app
        // arm in the soundness proof: from `f : F` + `whnf_to F (pi A B)` (=>
        // DefEq F (pi A B), whnf ⊆ def-eq / subject reduction) `conv` yields
        // `f : pi A B`; from `a : A'` + `DefEq A' A` `conv` yields `a : A`; then
        // the `app` rule concludes `app f a : instantiate B a`. ZERO new axioms.
        self.add_inductive(
            concat!(
                "inductive TypingCtxConv (tenv : Name -> OptionType KExpr) : ListType KExpr -> KExpr -> KExpr -> Type\n",
                "| var : forall (G : ListType KExpr) (i : Nat) (A : KExpr), Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> TypingCtxConv tenv G (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))\n",
                "| sort : forall (G : ListType KExpr) (n : Level), TypingCtxConv tenv G (KExpr.sort n) (KExpr.sort (Level.succ n))\n",
                "| pi : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level), TypingCtxConv tenv G A (KExpr.sort n) -> TypingCtxConv tenv (ListType.cons KExpr A G) B (KExpr.sort m) -> TypingCtxConv tenv G (KExpr.pi A B) (KExpr.sort (Level.imax n m))\n",
                "| lam : forall (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingCtxConv tenv G A (KExpr.sort u) -> TypingCtxConv tenv (ListType.cons KExpr A G) b B -> TypingCtxConv tenv G (KExpr.lam A b) (KExpr.pi A B)\n",
                "| app : forall (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr), TypingCtxConv tenv G f (KExpr.pi A B) -> TypingCtxConv tenv G a A -> TypingCtxConv tenv G (KExpr.app f a) (instantiate B a)\n",
                "| const : forall (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr), Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> TypingCtxConv tenv G (KExpr.const n us) A\n",
                "| conv : forall (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr), TypingCtxConv tenv G e A -> DefEq A B -> TypingCtxConv tenv G e B\n",
                "| let_ : forall (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingCtxConv tenv G ty (KExpr.sort u) -> TypingCtxConv tenv G v ty -> TypingCtxConv tenv (ListType.cons KExpr ty G) b B -> TypingCtxConv tenv G (KExpr.let_ ty v b) (instantiate B v)"
            ),
            "Declarative-with-conversion typing judgment TypingCtxConv tenv G e T: the standard \
             declarative CIC judgment (var/sort/pi/lam/app/const/let_) with recursive premises over \
             itself, PLUS the CIC conversion rule conv (TypingCtxConv G e A -> DefEq A B -> \
             TypingCtxConv G e B). It is the conversion-closed superset of the conv-free TypingCtx \
             (kept separate to leave TypingCtx.rec / the Girard fundamental_general consumer intact). \
             This is the soundness TARGET for the algorithmic KernelInfers: conv discharges the \
             faithful app arm (whnf F->pi gives DefEq F (pi A B) then conv; DefEq A' A then conv). \
             Kernel generates TypingCtxConv.rec, sound by construction. ZERO new axioms \
             (census-neutral). LET INCREMENT (task #28): the dependent let_ rule is appended \
             LAST (after conv — the B5a cross-lane convention: binders G ty v b B u, premises \
             ty : sort u / v : ty / cons ty G |- b : B, conclusion instantiate B v), so every \
             external TypingCtxConv.rec consumer (subject_reduction_bundle.rs) gains its let \
             minor as the TRAILING 8th minor.",
        )?;

        // Non-vacuity witness for TypingCtxConv: (sort 0 : sort 1) in the empty
        // context. Pure constructor application (TypingCtxConv.sort), elaboration
        // smoke test.
        self.add_definition(SpecDefinition {
            name: "typingctxconv_sort_witness".to_string(),
            type_src: "TypingCtxConv (fun (nm : Name) => OptionType.none KExpr) (ListType.nil KExpr) (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))".to_string(),
            value_src: Some(
                "TypingCtxConv.sort (fun (nm : Name) => OptionType.none KExpr) (ListType.nil KExpr) Level.zero".to_string(),
            ),
            is_axiom: false,
            description: "Non-vacuity witness for the declarative-with-conversion judgment: \
                          (sort 0 : sort 1) in the empty context. Pure constructor application \
                          (TypingCtxConv.sort), zero axiom_deps. Confirms TypingCtxConv is inhabited."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv".to_string(),
                "OptionType".to_string(),
                "ListType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // INFRASTRUCTURE BATCH (Brick 2): Neutral + psubst PRIMITIVES +
        // CandModel structure. The Girard reducibility-candidate interface.
        // These are the DEFINITIONS/STRUCTURE only — the psubst-tower LEMMAS
        // (psubst_comp, psubst_id, instantiate_eq_psubst, ...) and the
        // CR-accessors / red_var / fundamental adequacy are a SEPARATE later
        // batch. Every decl here is value-full (add_recursive_def /
        // add_definition / add_inductive) — ZERO new kernel axioms, census
        // stays 16.
        // ================================================================

        // Neutral e : e is not a canonical introduction (lam/pi/sort) — i.e.
        // its head is a variable, application, or constant. Guide's `Neutral`
        // (dependent_sn_modulo_candmodel.lean:728-734), a NEW def DISTINCT from
        // clean-verify's `is_neutral` (which is the const+delta whnf-head
        // inductive). Realized as the guide's Prop-valued def in the Type idiom:
        // ConstFreeUnit (trivially inhabited) at the neutral heads bvar/app/const,
        // Empty at the canonical intros sort/lam/pi. Same KExpr.rec large-
        // elimination shape as `const_free` (whnf_progress.rs), so it reduces on
        // constructors and its witnesses discharge by ConstFreeUnit.triv.
        self.add_recursive_def(
            r"def Neutral (e : KExpr) : Type := KExpr.rec (fun (_ : KExpr) => Type) (fun (n : Level) => Empty) (fun (i : Nat) => ConstFreeUnit) (fun (f : KExpr) (a : KExpr) (nf : Type) (na : Type) => ConstFreeUnit) (fun (ty : KExpr) (b : KExpr) (nty : Type) (nb : Type) => Empty) (fun (ty : KExpr) (b : KExpr) (nty : Type) (nb : Type) => Empty) (fun (n : Name) (us : ListType Level) => ConstFreeUnit) (fun (lty : KExpr) (lv : KExpr) (lb : KExpr) (nty : Type) (nv : Type) (nb : Type) => Empty) (fun (s : Name) (i : Nat) (sub : KExpr) (nsub : Type) => ConstFreeUnit) (fun (v : Nat) => Empty) e",
            "Neutral e is inhabited iff e is NOT a canonical introduction (lam/pi/sort): \
             ConstFreeUnit at the neutral heads bvar/app/const, Empty at sort/lam/pi. The \
             guide's Neutral (dependent_sn_modulo_candmodel.lean:728), the CR3 hypothesis of \
             the reducibility-candidate method. A NEW def, DISTINCT from is_neutral (the \
             const+delta whnf-head inductive). A let_ is NEVER neutral (Empty): it is a \
             zeta-redex former; its reducibility closure enters via the redLet candidate \
             field instead (let increment, task #28; guide SnLet.lean:818). Recursive \
             Type-valued KExpr.rec def (same shape as const_free), reduces on constructors.",
        )?;

        // Neutral witnesses: bvar/app/const are neutral (reduce to ConstFreeUnit,
        // discharged by ConstFreeUnit.triv). Confirm Neutral computes on each
        // neutral head under the kernel.
        self.add_definition(SpecDefinition {
            name: "neutral_bvar_witness".to_string(),
            type_src: "Neutral (KExpr.bvar Nat.zero)".to_string(),
            value_src: Some("ConstFreeUnit.triv".to_string()),
            is_axiom: false,
            description: "Neutral computes on a variable head: Neutral (bvar 0) reduces to \
                          ConstFreeUnit, inhabited by ConstFreeUnit.triv. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Neutral".to_string(),
                "ConstFreeUnit".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "neutral_app_witness".to_string(),
            type_src: "Neutral (KExpr.app (KExpr.sort Level.zero) (KExpr.sort Level.zero))".to_string(),
            value_src: Some("ConstFreeUnit.triv".to_string()),
            is_axiom: false,
            description: "Neutral computes on an application head: Neutral (app (sort 0) (sort 0)) \
                          reduces to ConstFreeUnit, inhabited by ConstFreeUnit.triv. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Neutral".to_string(),
                "ConstFreeUnit".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "neutral_const_witness".to_string(),
            type_src: "Neutral (KExpr.const Name.anonymous (ListType.nil Level))".to_string(),
            value_src: Some("ConstFreeUnit.triv".to_string()),
            is_axiom: false,
            description: "Neutral computes on a constant head: Neutral (const anonymous nil) \
                          reduces to ConstFreeUnit, inhabited by ConstFreeUnit.triv. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Neutral".to_string(),
                "ConstFreeUnit".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // de Bruijn PARALLEL-SUBSTITUTION primitives (guide §8-8b',
        // dependent_sn_modulo_candmodel.lean:743-766). DEFINITIONS ONLY — the
        // commutation-tower lemmas are a separate reuse-first batch. Written with
        // explicit Nat.rec / KExpr.rec (the proven-safe idiom), NOT nested match.

        // scons a s : "stream cons" — prepend a to a substitution s : Nat -> KExpr
        // (0 |-> a, succ i |-> s i). Recursion on the index via Nat.rec.
        self.add_recursive_def(
            r"def scons (a : KExpr) (s : Nat -> KExpr) : Nat -> KExpr := fun (i : Nat) => Nat.rec (fun (_ : Nat) => KExpr) a (fun (n : Nat) (_ : KExpr) => s n) i",
            "scons a s : prepend a to the substitution s (0 |-> a, succ i |-> s i). Guide's scons \
             (dependent_sn_modulo_candmodel.lean:743). Nat.rec on the index.",
        )?;

        // up s : shift a substitution under a binder (0 |-> bvar 0, succ i |->
        // lift (s i) by 1). scons (bvar 0) (lift . 1). Non-recursive composition.
        self.add_recursive_def(
            r"def up (s : Nat -> KExpr) : Nat -> KExpr := scons (KExpr.bvar Nat.zero) (fun (i : Nat) => lift_at (s i) Nat.zero (Nat.succ Nat.zero))",
            "up s : shift substitution s under one binder (0 |-> bvar 0, succ i |-> lift (s i) 1). \
             Guide's up (dependent_sn_modulo_candmodel.lean:748). scons (bvar 0) over the \
             1-lifted tail.",
        )?;

        // psubst s e : parallel substitution of s : Nat -> KExpr through e. The
        // motive is FUNCTION-valued (fun _ => (Nat -> KExpr) -> KExpr): the KExpr.rec
        // produces a function of the substitution, so under a binder the recursive
        // call is threaded with `up t` (the substitution changes going under lam/pi).
        // This is the standard "recurse on the term, abstract the substitution"
        // encoding. bvar i |-> t i; sort/const are inert; app/lam/pi recurse (lam/pi
        // shifting the substitution via up).
        self.add_recursive_def(
            r"def psubst (s : Nat -> KExpr) (e : KExpr) : KExpr := KExpr.rec (fun (_ : KExpr) => (Nat -> KExpr) -> KExpr) (fun (n : Level) => fun (t : Nat -> KExpr) => KExpr.sort n) (fun (i : Nat) => fun (t : Nat -> KExpr) => t i) (fun (f : KExpr) (a : KExpr) (ihf : (Nat -> KExpr) -> KExpr) (iha : (Nat -> KExpr) -> KExpr) => fun (t : Nat -> KExpr) => KExpr.app (ihf t) (iha t)) (fun (ty : KExpr) (b : KExpr) (ihty : (Nat -> KExpr) -> KExpr) (ihb : (Nat -> KExpr) -> KExpr) => fun (t : Nat -> KExpr) => KExpr.lam (ihty t) (ihb (up t))) (fun (ty : KExpr) (b : KExpr) (ihty : (Nat -> KExpr) -> KExpr) (ihb : (Nat -> KExpr) -> KExpr) => fun (t : Nat -> KExpr) => KExpr.pi (ihty t) (ihb (up t))) (fun (n : Name) (us : ListType Level) => fun (t : Nat -> KExpr) => KExpr.const n us) (fun (lty : KExpr) (lv : KExpr) (lb : KExpr) (ihty : (Nat -> KExpr) -> KExpr) (ihv : (Nat -> KExpr) -> KExpr) (ihb : (Nat -> KExpr) -> KExpr) => fun (t : Nat -> KExpr) => KExpr.let_ (ihty t) (ihv t) (ihb (up t))) (fun (ps : Name) (pidx : Nat) (sub : KExpr) (ihsub : (Nat -> KExpr) -> KExpr) => fun (t : Nat -> KExpr) => KExpr.proj ps pidx (ihsub t)) (fun (v : Nat) => fun (t : Nat -> KExpr) => KExpr.lit v) e s",
            "psubst s e : parallel substitution of s : Nat -> KExpr through e. Guide's psubst \
             (dependent_sn_modulo_candmodel.lean:752). KExpr.rec with a FUNCTION-valued motive \
             ((Nat -> KExpr) -> KExpr) so the substitution can be shifted (up) under binders: \
             bvar i |-> t i, sort/const inert, app congruent, lam/pi (and the let_ body — ty/val \
             at the current substitution) recurse under `up t` (let increment, task #28).",
        )?;

        // idsubst : the identity substitution i |-> bvar i.
        self.add_recursive_def(
            r"def idsubst : Nat -> KExpr := fun (i : Nat) => KExpr.bvar i",
            "idsubst : the identity substitution i |-> bvar i. Guide's idsubst \
             (dependent_sn_modulo_candmodel.lean:761).",
        )?;

        // upn c s : `up` iterated c times (Nat.rec on c, threading the
        // substitution). Used to state the general-depth commutation lemmas later.
        self.add_recursive_def(
            r"def upn (c : Nat) (s : Nat -> KExpr) : Nat -> KExpr := Nat.rec (fun (_ : Nat) => (Nat -> KExpr) -> (Nat -> KExpr)) (fun (t : Nat -> KExpr) => t) (fun (c2 : Nat) (ih : (Nat -> KExpr) -> (Nat -> KExpr)) => fun (t : Nat -> KExpr) => up (ih t)) c s",
            "upn c s : `up` iterated c times over the substitution s (upn 0 s = s, \
             upn (succ c) s = up (upn c s)). Guide's upn (dependent_sn_modulo_candmodel.lean:764). \
             Nat.rec on c with a substitution-transformer motive.",
        )?;

        // Computation witnesses (Eq.refl): confirm the primitives REDUCE under the
        // kernel (not merely parse). psubst on a concrete sort/bvar computes; upn 0
        // is the identity iteration.
        self.add_definition(SpecDefinition {
            name: "psubst_idsubst_sort_witness".to_string(),
            type_src: "Eq KExpr (psubst idsubst (KExpr.sort Level.zero)) (KExpr.sort Level.zero)"
                .to_string(),
            value_src: Some("Eq.refl KExpr (KExpr.sort Level.zero)".to_string()),
            is_axiom: false,
            description: "psubst computes on a sort: psubst idsubst (sort 0) reduces to (sort 0) \
                          (KExpr.rec iota on the sort constructor). Discharged by Eq.refl. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "psubst".to_string(),
                "idsubst".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "psubst_idsubst_bvar_witness".to_string(),
            type_src: "Eq KExpr (psubst idsubst (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)"
                .to_string(),
            value_src: Some("Eq.refl KExpr (KExpr.bvar Nat.zero)".to_string()),
            is_axiom: false,
            description: "psubst threads the substitution at a variable: psubst idsubst (bvar 0) \
                          reduces to idsubst 0 = (bvar 0). Discharged by Eq.refl. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "psubst".to_string(),
                "idsubst".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "upn_zero_idsubst_witness".to_string(),
            type_src: "Eq (Nat -> KExpr) (upn Nat.zero idsubst) idsubst".to_string(),
            value_src: Some("Eq.refl (Nat -> KExpr) idsubst".to_string()),
            is_axiom: false,
            description: "upn 0 is the identity iteration: upn 0 idsubst reduces to idsubst \
                          (Nat.rec base case). Discharged by Eq.refl at the substitution type. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "upn".to_string(),
                "idsubst".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // CandModel tenv : the Girard/Tait reducibility-candidate interface (guide
        // §8 CandModel, dependent_sn_modulo_candmodel.lean:781-822), packaged as a
        // single-constructor inductive `mk` (the Type-idiom analog of the guide's
        // `structure`). Bundles a reducibility family `Red : KExpr -> KExpr -> Type`
        // with the candidate laws CR1/CR2/CR3, the base `red_sort`, the dependent-Pi
        // `pi_elim`/`pi_intro`, the weak-head-expansion `redAbstraction`, and the
        // definition-reducibility `redConst`. Env-parametric in the guide collapse
        // to the FIXED the_red_env here (whnf_acc/whnf_step are env-fixed in
        // clean-verify), so only `tenv` (the const-typing env) survives as a
        // parameter. Lives in `Type 1` because it stores the Type-valued family Red.
        // The EXISTENCE of an inhabitant is the isolated Gödel-floor labeled
        // assumption — but the STRUCTURE itself is a positivity-checked add_inductive
        // (Inductive/Constructor/Recursor, NONE ConstantKind::Axiom), so registering
        // it is census-NEUTRAL (census stays 16). CandModel does NOT occur in any
        // field type, so positivity is trivially satisfied (it is a large sigma).
        self.add_inductive(
            concat!(
                "inductive CandModel (tenv : Name -> OptionType KExpr) : Type 1\n",
                "| mk : forall (Red : KExpr -> KExpr -> Type) ",
                "(cr1 : forall (T : KExpr) (e : KExpr), Red T e -> whnf_acc e) ",
                "(cr2 : forall (T : KExpr) (e : KExpr) (e2 : KExpr), Red T e -> whnf_step e e2 -> Red T e2) ",
                "(cr3 : forall (T : KExpr) (e : KExpr), Neutral e -> (forall (e2 : KExpr), whnf_step e e2 -> Red T e2) -> Red T e) ",
                "(red_sort : forall (n : Level) (e : KExpr), whnf_acc e -> Red (KExpr.sort n) e) ",
                "(pi_elim : forall (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr), Red (KExpr.pi A B) f -> Red A a -> Red (instantiate B a) (KExpr.app f a)) ",
                "(pi_intro : forall (A : KExpr) (B : KExpr) (f : KExpr), (forall (a : KExpr), Red A a -> Red (instantiate B a) (KExpr.app f a)) -> Red (KExpr.pi A B) f) ",
                "(redAbstraction : forall (A : KExpr) (b : KExpr) (B : KExpr), whnf_acc A -> (forall (a : KExpr), Red A a -> Red (instantiate B a) (instantiate b a)) -> forall (a : KExpr), Red A a -> Red (instantiate B a) (KExpr.app (KExpr.lam A b) a)) ",
                "(redConst : forall (n : Name) (us : ListType Level) (A : KExpr) (s : Nat -> KExpr), Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> Red (psubst s A) (KExpr.const n us)) ",
                "(redLet : forall (A : KExpr) (b : KExpr) (B : KExpr), whnf_acc A -> (forall (a : KExpr), Red A a -> Red (instantiate B a) (instantiate b a)) -> forall (a : KExpr), Red A a -> Red (instantiate B a) (KExpr.let_ A a b)) ",
                "(redRecGen : forall (fam : Name) (sig : ListType Nat) (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (ms : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), GenFresh fam sig denv -> GenRecEnvOK fam sig u renv -> GenRecContract fam sig u (genRecApp fam sig u m ms t) contractum -> whnf_acc m -> WhnfAccAll ms -> whnf_acc t -> Red T contractum -> Red T (genRecApp fam sig u m ms t)) ",
                "(redRecW : forall (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (mn : KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), WFresh denv -> WRecEnvOK u renv -> WRecContract u (wRecApp u m mn t) contractum -> whnf_acc m -> whnf_acc mn -> whnf_acc t -> Red T contractum -> Red T (wRecApp u m mn t)) (redRecMut : forall (msig : ListType FamSpec) (u : Level) (i : Nat) (denv : DefEnv) (renv : RecEnv) (cs : ListType KExpr) (ms : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), MutFresh msig denv -> MutRecEnvOK msig u renv -> MutRecContract msig u (mutRecApp msig u i cs ms t) contractum -> WhnfAccAll cs -> WhnfAccAll ms -> whnf_acc t -> Red T contractum -> Red T (mutRecApp msig u i cs ms t)) (redRecIdx : forall (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (ms : ListType KExpr) (ix : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), IGenFresh fam isig denv -> IGenRecEnvOK iFam fam nIdx isig u renv -> IGenRecContract fam nIdx isig u (iRecApp fam isig u m ms ix t) contractum -> whnf_acc m -> WhnfAccAll ms -> WhnfAccAll ix -> whnf_acc t -> Red T contractum -> Red T (iRecApp fam isig u m ms ix t)) (redTypeStep : forall (T : KExpr) (T2 : KExpr) (e : KExpr), whnf_step T T2 -> AndType (Red T e -> Red T2 e) (Red T2 e -> Red T e)), ",
                "CandModel tenv"
            ),
            "CandModel tenv (Brick 2 Girard reducibility-candidate interface, guide dependent_sn_modulo_candmodel.lean:781): a single-constructor inductive whose mk telescope binds Red plus FOURTEEN laws (15 binders total): cr1, cr2, cr3, red_sort, pi_elim, pi_intro, redAbstraction, redConst, redLet, redRecGen, redRecW, redRecMut, redRecIdx, redTypeStep. Each added law makes CandModel a STRICTLY STRONGER hypothesis, so every CandModel-conditional theorem assumes more without its statement changing. The laws are CR1 (reducible => SN), CR2 (closed under reduction), CR3 (neutral with all reducts reducible is reducible), red_sort (base: SN => reducible at a sort), pi_elim / pi_intro (the dependent-Pi elim/intro where instantiate B a enters and structural recursion breaks), redAbstraction (weak-head-expansion closure), redConst (defined constants inhabit their declared type at every substitution instance) and redLet — the NEW zeta weak-head-expansion closure (let increment, task #28; guide SnLet.lean:908-918): zeta enters the candidates EXACTLY the way beta does, in the same shape as redAbstraction with the redex app (lam A b) a replaced by let_ A a b. Env-parametric guide collapses to the FIXED env (whnf_acc/whnf_step env-fixed); only tenv survives. Lives in Type 1 (stores the Type-valued Red). Its INHABITANT is the isolated Gödel-floor assumption; the STRUCTURE is census-NEUTRAL (Inductive/Constructor/Recursor, zero axioms). Kernel generates CandModel.rec.",
        )?;

        // CandModel elaboration + field-projection witness. Given a CandModel, its
        // fields project via CandModel.rec: this composes the `red_sort` base clause
        // with the CR1 accessor to round-trip whnf_acc e -> whnf_acc e THROUGH the
        // model (red_sort n e h : Red (sort n) e, then cr1 (sort n) e that : whnf_acc e).
        // Confirms CandModel.rec is generated with the right arity and that the full
        // 11-field (redLet + Nat.rec redNatRec) constructor telescope (incl. the let-increment redLet) type-checks and is usable. The motive lands
        // in Type 0 (eliminating the Type-1 inductive into Type 0 — allowed, it is a
        // non-Prop inductive with unrestricted large elimination).
        self.add_definition(SpecDefinition {
            name: "candmodel_red_sort_cr1_witness".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (n : Level) (e : KExpr), whnf_acc e -> whnf_acc e".to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => ",
                    "CandModel.rec tenv ",
                    "(fun (M0 : CandModel tenv) => forall (n : Level) (e : KExpr), whnf_acc e -> whnf_acc e) ",
                    "(fun (Red : KExpr -> KExpr -> Type) ",
                    "(cr1 : forall (T : KExpr) (e : KExpr), Red T e -> whnf_acc e) ",
                    "(cr2 : forall (T : KExpr) (e : KExpr) (e2 : KExpr), Red T e -> whnf_step e e2 -> Red T e2) ",
                    "(cr3 : forall (T : KExpr) (e : KExpr), Neutral e -> (forall (e2 : KExpr), whnf_step e e2 -> Red T e2) -> Red T e) ",
                    "(red_sort : forall (n : Level) (e : KExpr), whnf_acc e -> Red (KExpr.sort n) e) ",
                    "(pi_elim : forall (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr), Red (KExpr.pi A B) f -> Red A a -> Red (instantiate B a) (KExpr.app f a)) ",
                    "(pi_intro : forall (A : KExpr) (B : KExpr) (f : KExpr), (forall (a : KExpr), Red A a -> Red (instantiate B a) (KExpr.app f a)) -> Red (KExpr.pi A B) f) ",
                    "(redAbstraction : forall (A : KExpr) (b : KExpr) (B : KExpr), whnf_acc A -> (forall (a : KExpr), Red A a -> Red (instantiate B a) (instantiate b a)) -> forall (a : KExpr), Red A a -> Red (instantiate B a) (KExpr.app (KExpr.lam A b) a)) ",
                    "(redConst : forall (n : Name) (us : ListType Level) (A : KExpr) (s : Nat -> KExpr), Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> Red (psubst s A) (KExpr.const n us)) ",
                    "(redLet : forall (A : KExpr) (b : KExpr) (B : KExpr), whnf_acc A -> (forall (a : KExpr), Red A a -> Red (instantiate B a) (instantiate b a)) -> forall (a : KExpr), Red A a -> Red (instantiate B a) (KExpr.let_ A a b)) ",
                    "(redRecGen : forall (fam : Name) (sig : ListType Nat) (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (ms : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), GenFresh fam sig denv -> GenRecEnvOK fam sig u renv -> GenRecContract fam sig u (genRecApp fam sig u m ms t) contractum -> whnf_acc m -> WhnfAccAll ms -> whnf_acc t -> Red T contractum -> Red T (genRecApp fam sig u m ms t)) ",
                    "(redRecW : forall (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (mn : KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), WFresh denv -> WRecEnvOK u renv -> WRecContract u (wRecApp u m mn t) contractum -> whnf_acc m -> whnf_acc mn -> whnf_acc t -> Red T contractum -> Red T (wRecApp u m mn t)) (redRecMut : forall (msig : ListType FamSpec) (u : Level) (i : Nat) (denv : DefEnv) (renv : RecEnv) (cs : ListType KExpr) (ms : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), MutFresh msig denv -> MutRecEnvOK msig u renv -> MutRecContract msig u (mutRecApp msig u i cs ms t) contractum -> WhnfAccAll cs -> WhnfAccAll ms -> whnf_acc t -> Red T contractum -> Red T (mutRecApp msig u i cs ms t)) (redRecIdx : forall (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (ms : ListType KExpr) (ix : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), IGenFresh fam isig denv -> IGenRecEnvOK iFam fam nIdx isig u renv -> IGenRecContract fam nIdx isig u (iRecApp fam isig u m ms ix t) contractum -> whnf_acc m -> WhnfAccAll ms -> WhnfAccAll ix -> whnf_acc t -> Red T contractum -> Red T (iRecApp fam isig u m ms ix t)) (redTypeStep : forall (T : KExpr) (T2 : KExpr) (e : KExpr), whnf_step T T2 -> AndType (Red T e -> Red T2 e) (Red T2 e -> Red T e)) => ",
                    "fun (n : Level) (e : KExpr) (h : whnf_acc e) => cr1 (KExpr.sort n) e (red_sort n e h)) ",
                    "M"
                ).to_string(),
            ),
            is_axiom: false,
            description: "CandModel elaboration + field-projection witness: via CandModel.rec, the \
                          model's fields project and compose — red_sort (base clause) then cr1 \
                          (CR1 accessor) round-trip whnf_acc e -> whnf_acc e through the candidate \
                          family. Confirms CandModel.rec exists at the right arity and the 11-field (redLet + Nat.rec redNatRec) \
                          telescope (incl. redLet) type-checks + is usable. Zero axiom_deps (census-neutral)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CandModel".to_string(),
                "whnf_acc".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // §8b' PSUBST TOWER — BATCH 3 (this port). Reuse-first: the pure
        // `lift_at` lemmas the guide re-derives (guide `lift_at_zero`,
        // `lift_same`, `lift_shift`, `lift_at_lift_at`, `instantiate_bvar_at_eq`)
        // ALREADY EXIST in clean-verify's explicit-substitution library
        // (`lift_at_amount_zero`, `lift_at_compose`, `lift_at_shift_succ_gen`,
        // `instantiate_bvar_at_eq`) and are REFERENCED, not re-ported. What is
        // genuinely NEW here is the `psubst` calculus, because `psubst`/`up`/
        // `scons`/`upn`/`idsubst` were introduced in Batches 1-2. clean-verify's
        // spec has NO `funext` in its reconstruction toolbox, so the guide's
        // funext-driven proofs (psubst_comp/psubst_id/up_comp) are re-derived
        // FUNEXT-FREE via a pointwise-congruence lemma (`psubst_pointwise`) that
        // stands in for every `funext` use.
        //
        // This batch lands the COMPUTATIONAL BASE + the congruence engine +
        // the identity law, all zero-axiom DerivedProved (census stays 16):
        //   psubst_sort/bvar/app/lam/pi/const  — the explicit form of the
        //     guide's `simp only [psubst]` (per-constructor iota unfolds), the
        //     analog of the library's lift_at_app/lam/pi. This is exactly the
        //     spot a prior attempt broke (KExpr.rec Discriminant(6) vs (3)); the
        //     fix is add_definition_structural + Eq.refl (same bypass the whole
        //     lift library uses).
        //   up_zero / up_succ                  — `up` unfolds at 0 / succ.
        //   up_pointwise / up_idsubst          — `up` respects pointwise-eq /
        //     fixes idsubst (guide `up_idsubst`, line 1130).
        //   psubst_pointwise                   — FUNEXT-FREE congruence (NEW,
        //     replaces the guide's funext).
        //   psubst_id                          — guide `psubst_id` (line 1134).
        // The arithmetic sub-tower (upn_apply, psubst_up_lift_gen, up_comp,
        // psubst_comp, instantiate_at_eq_psubst, instantiate_eq_psubst,
        // psubst_cancel_gen, psubst_cancel, psubst_instantiate,
        // psubst_scons_instantiate) is the NEXT batch — dense Nat.rec-convoy
        // arithmetic over the reused lift lemmas.
        // ================================================================

        // --- BATCH 3a: per-constructor psubst iota-unfold lemmas ---
        // Each is Eq.refl through the checked KExpr.rec iota reduction of psubst
        // (function-valued motive, applied to `s` after the major premise), the
        // psubst analog of lift_at_app/lift_at_lam. add_definition_structural
        // bypasses the KExpr.rec-motive iota false negative (Discriminant(6)
        // vs (3)). ZERO axioms.
        self.add_definition_structural(SpecDefinition {
            name: "psubst_sort".to_string(),
            type_src: "forall (s : Nat -> KExpr) (n : Level), Eq KExpr (psubst s (KExpr.sort n)) (KExpr.sort n)".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (n : Level) => Eq.refl KExpr (KExpr.sort n)".to_string()),
            is_axiom: false,
            description: "psubst on a sort is the sort (iota unfold of psubst's KExpr.rec sort branch). Explicit form of the guide's `simp only [psubst]` sort case. DerivedProved via Eq.refl + structural registration. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["psubst".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "psubst_bvar".to_string(),
            type_src: "forall (s : Nat -> KExpr) (i : Nat), Eq KExpr (psubst s (KExpr.bvar i)) (s i)".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (i : Nat) => Eq.refl KExpr (s i)".to_string()),
            is_axiom: false,
            description: "psubst threads the substitution at a variable: psubst s (bvar i) = s i (iota unfold of psubst's bvar branch). DerivedProved via Eq.refl + structural registration. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["psubst".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "psubst_app".to_string(),
            type_src: "forall (s : Nat -> KExpr) (f : KExpr) (a : KExpr), Eq KExpr (psubst s (KExpr.app f a)) (KExpr.app (psubst s f) (psubst s a))".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (f : KExpr) (a : KExpr) => Eq.refl KExpr (KExpr.app (psubst s f) (psubst s a))".to_string()),
            is_axiom: false,
            description: "psubst distributes over app (iota unfold of psubst's app branch). DerivedProved via Eq.refl + structural registration. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["psubst".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "psubst_lam".to_string(),
            type_src: "forall (s : Nat -> KExpr) (ty : KExpr) (b : KExpr), Eq KExpr (psubst s (KExpr.lam ty b)) (KExpr.lam (psubst s ty) (psubst (up s) b))".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (ty : KExpr) (b : KExpr) => Eq.refl KExpr (KExpr.lam (psubst s ty) (psubst (up s) b))".to_string()),
            is_axiom: false,
            description: "psubst under a lam shifts the substitution via `up` (iota unfold of psubst's lam branch): psubst s (lam ty b) = lam (psubst s ty) (psubst (up s) b). DerivedProved via Eq.refl + structural registration. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["psubst".to_string(), "up".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "psubst_pi".to_string(),
            type_src: "forall (s : Nat -> KExpr) (ty : KExpr) (b : KExpr), Eq KExpr (psubst s (KExpr.pi ty b)) (KExpr.pi (psubst s ty) (psubst (up s) b))".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (ty : KExpr) (b : KExpr) => Eq.refl KExpr (KExpr.pi (psubst s ty) (psubst (up s) b))".to_string()),
            is_axiom: false,
            description: "psubst under a pi shifts the substitution via `up` (iota unfold of psubst's pi branch): psubst s (pi ty b) = pi (psubst s ty) (psubst (up s) b). DerivedProved via Eq.refl + structural registration. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["psubst".to_string(), "up".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "psubst_const".to_string(),
            type_src: "forall (s : Nat -> KExpr) (n : Name) (us : ListType Level), Eq KExpr (psubst s (KExpr.const n us)) (KExpr.const n us)".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (n : Name) (us : ListType Level) => Eq.refl KExpr (KExpr.const n us)".to_string()),
            is_axiom: false,
            description: "psubst leaves a const unchanged (iota unfold of psubst's const branch). DerivedProved via Eq.refl + structural registration. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["psubst".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "psubst_let_".to_string(),
            type_src: "forall (s : Nat -> KExpr) (ty : KExpr) (v : KExpr) (b : KExpr), Eq KExpr (psubst s (KExpr.let_ ty v b)) (KExpr.let_ (psubst s ty) (psubst s v) (psubst (up s) b))".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) => Eq.refl KExpr (KExpr.let_ (psubst s ty) (psubst s v) (psubst (up s) b))".to_string()),
            is_axiom: false,
            description: "psubst under a let_ shifts the substitution via `up` in the BODY only (ty/val stay at the current substitution — iota unfold of psubst's let_ branch): psubst s (let_ ty v b) = let_ (psubst s ty) (psubst s v) (psubst (up s) b). Let-promotion increment (task #28), the let_ analogue of psubst_lam. DerivedProved via Eq.refl + structural registration. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["psubst".to_string(), "up".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "psubst_proj".to_string(),
            type_src: "forall (s : Nat -> KExpr) (nm : Name) (i : Nat) (sub : KExpr), Eq KExpr (psubst s (KExpr.proj nm i sub)) (KExpr.proj nm i (psubst s sub))".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (nm : Name) (i : Nat) (sub : KExpr) => Eq.refl KExpr (KExpr.proj nm i (psubst s sub))".to_string()),
            is_axiom: false,
            description: "psubst descends into a proj scrutinee unchanged (no binder — iota unfold of psubst's proj branch): psubst s (proj nm i sub) = proj nm i (psubst s sub). The proj analogue of psubst_app (single hole). DerivedProved via Eq.refl + structural registration. Zero axiom_deps. Part of the proj/lit fragment rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["psubst".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "psubst_lit".to_string(),
            type_src: "forall (s : Nat -> KExpr) (v : Nat), Eq KExpr (psubst s (KExpr.lit v)) (KExpr.lit v)".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (v : Nat) => Eq.refl KExpr (KExpr.lit v)".to_string()),
            is_axiom: false,
            description: "psubst leaves a literal unchanged (iota unfold of psubst's lit branch): psubst s (lit v) = lit v. The lit analogue of psubst_const (leaf). DerivedProved via Eq.refl + structural registration. Zero axiom_deps. Part of the proj/lit fragment rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["psubst".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // --- BATCH 3b: `up` iota-unfold at 0 / succ ---
        // up s = scons (bvar 0) (fun i => lift_at (s i) 0 1); scons is Nat.rec on
        // the index. Eq.refl through the checked Nat.rec iota.
        self.add_definition_structural(SpecDefinition {
            name: "up_zero".to_string(),
            type_src: "forall (s : Nat -> KExpr), Eq KExpr (up s Nat.zero) (KExpr.bvar Nat.zero)".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) => Eq.refl KExpr (KExpr.bvar Nat.zero)".to_string()),
            is_axiom: false,
            description: "up s at index 0 is bvar 0 (scons base case). DerivedProved via Eq.refl + structural registration. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["up".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "up_succ".to_string(),
            type_src: "forall (s : Nat -> KExpr) (k : Nat), Eq KExpr (up s (Nat.succ k)) (lift_at (s k) Nat.zero (Nat.succ Nat.zero))".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (k : Nat) => Eq.refl KExpr (lift_at (s k) Nat.zero (Nat.succ Nat.zero))".to_string()),
            is_axiom: false,
            description: "up s at index (succ k) lifts the tail: up s (succ k) = lift_at (s k) 0 1 (scons succ case). Guide's `up` succ clause (line 748). DerivedProved via Eq.refl + structural registration. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["up".to_string(), "lift_at".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // --- BATCH 3c: `up` congruence + idsubst fixpoint ---
        // up_pointwise: `up` respects pointwise equality of substitutions. This is
        // the FUNEXT-FREE engine — it lets an induction go under a binder without
        // needing `funext (up σ = up τ)`. Nat.rec on the index: 0 -> bvar 0 both
        // sides (up_zero); succ k -> lift_at (s k)/(t k) 0 1, bridged by Eq.cong
        // on the pointwise hypothesis (up_succ).
        self.add_definition_structural(SpecDefinition {
            name: "up_pointwise".to_string(),
            type_src: "forall (s : Nat -> KExpr) (t : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s i) (t i)) -> forall (i : Nat), Eq KExpr (up s i) (up t i)".to_string(),
            value_src: Some(concat!(
                "fun (s : Nat -> KExpr) (t : Nat -> KExpr) (h : forall (i : Nat), Eq KExpr (s i) (t i)) (i : Nat) => ",
                "Nat.rec (fun (j : Nat) => Eq KExpr (up s j) (up t j)) ",
                "(Eq.trans KExpr (up s Nat.zero) (KExpr.bvar Nat.zero) (up t Nat.zero) ",
                "(up_zero s) (Eq.symm KExpr (up t Nat.zero) (KExpr.bvar Nat.zero) (up_zero t))) ",
                "(fun (k : Nat) (ih : Eq KExpr (up s k) (up t k)) => ",
                "Eq.trans KExpr (up s (Nat.succ k)) (lift_at (s k) Nat.zero (Nat.succ Nat.zero)) (up t (Nat.succ k)) ",
                "(up_succ s k) ",
                "(Eq.trans KExpr (lift_at (s k) Nat.zero (Nat.succ Nat.zero)) (lift_at (t k) Nat.zero (Nat.succ Nat.zero)) (up t (Nat.succ k)) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x Nat.zero (Nat.succ Nat.zero)) (s k) (t k) (h k)) ",
                "(Eq.symm KExpr (up t (Nat.succ k)) (lift_at (t k) Nat.zero (Nat.succ Nat.zero)) (up_succ t k)))) ",
                "i",
            ).to_string()),
            is_axiom: false,
            description: "up respects pointwise substitution equality: (forall i, s i = t i) -> forall i, up s i = up t i. The funext-free tool that carries pointwise equalities under binders. DerivedProved via Nat.rec on the index (up_zero/up_succ). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "up_zero".to_string(), "up_succ".to_string(),
                "Eq.trans".to_string(), "Eq.symm".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // up_idsubst: `up` fixes the identity substitution (guide up_idsubst,
        // line 1130): up idsubst i = idsubst i. Nat.rec on i: 0 -> bvar 0 (up_zero,
        // idsubst 0 defeq bvar 0); succ k -> lift_at (idsubst k) 0 1 = bvar (k+1) =
        // idsubst (succ k) (up_succ + lift_at_bvar_geq via nat_sub_zero_left).
        self.add_definition_structural(SpecDefinition {
            name: "up_idsubst".to_string(),
            type_src: "forall (i : Nat), Eq KExpr (up idsubst i) (idsubst i)".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) => ",
                "Nat.rec (fun (j : Nat) => Eq KExpr (up idsubst j) (idsubst j)) ",
                "(up_zero idsubst) ",
                "(fun (k : Nat) (ih : Eq KExpr (up idsubst k) (idsubst k)) => ",
                "Eq.trans KExpr (up idsubst (Nat.succ k)) (lift_at (idsubst k) Nat.zero (Nat.succ Nat.zero)) (idsubst (Nat.succ k)) ",
                "(up_succ idsubst k) ",
                "(Eq.trans KExpr (lift_at (idsubst k) Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar (Nat.add k (Nat.succ Nat.zero))) (idsubst (Nat.succ k)) ",
                "(lift_at_bvar_geq k Nat.zero (Nat.succ Nat.zero) (nat_sub_zero_left k)) ",
                "(Eq.refl KExpr (KExpr.bvar (Nat.succ k))))) ",
                "i",
            ).to_string()),
            is_axiom: false,
            description: "up fixes the identity substitution: up idsubst i = idsubst i. Guide's up_idsubst (line 1130). DerivedProved via Nat.rec on i (up_zero/up_succ + lift_at_bvar_geq). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "idsubst".to_string(), "up_zero".to_string(),
                "up_succ".to_string(), "lift_at_bvar_geq".to_string(),
                "nat_sub_zero_left".to_string(), "Eq.trans".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- BATCH 3d: psubst congruence (funext-free) + identity law ---
        // psubst_pointwise: substitutions that agree pointwise yield equal psubst
        // results. This is the FUNEXT-FREE replacement for every place the guide
        // rewrites one substitution to another via `funext`. KExpr.rec on the term
        // with a substitution-universalized motive; the lam/pi cases carry the
        // pointwise hypothesis under the binder via up_pointwise (NOT funext).
        self.add_definition_structural(SpecDefinition {
            name: "psubst_pointwise".to_string(),
            type_src: "forall (e : KExpr) (s : Nat -> KExpr) (t : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s i) (t i)) -> Eq KExpr (psubst s e) (psubst t e)".to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) (s : Nat -> KExpr) (t : Nat -> KExpr) (h : forall (i : Nat), Eq KExpr (s i) (t i)) => ",
                "KExpr.rec ",
                "(fun (e0 : KExpr) => forall (s0 : Nat -> KExpr) (t0 : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s0 i) (t0 i)) -> Eq KExpr (psubst s0 e0) (psubst t0 e0)) ",
                // sort
                "(fun (n : Level) (s : Nat -> KExpr) (t : Nat -> KExpr) (h : forall (i : Nat), Eq KExpr (s i) (t i)) => ",
                "Eq.trans KExpr (psubst s (KExpr.sort n)) (KExpr.sort n) (psubst t (KExpr.sort n)) ",
                "(psubst_sort s n) (Eq.symm KExpr (psubst t (KExpr.sort n)) (KExpr.sort n) (psubst_sort t n))) ",
                // bvar
                "(fun (i : Nat) (s : Nat -> KExpr) (t : Nat -> KExpr) (h : forall (i : Nat), Eq KExpr (s i) (t i)) => ",
                "Eq.trans KExpr (psubst s (KExpr.bvar i)) (s i) (psubst t (KExpr.bvar i)) ",
                "(psubst_bvar s i) ",
                "(Eq.trans KExpr (s i) (t i) (psubst t (KExpr.bvar i)) (h i) ",
                "(Eq.symm KExpr (psubst t (KExpr.bvar i)) (t i) (psubst_bvar t i)))) ",
                // app
                "(fun (f : KExpr) (a : KExpr) ",
                "(ihf : forall (s0 : Nat -> KExpr) (t0 : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s0 i) (t0 i)) -> Eq KExpr (psubst s0 f) (psubst t0 f)) ",
                "(iha : forall (s0 : Nat -> KExpr) (t0 : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s0 i) (t0 i)) -> Eq KExpr (psubst s0 a) (psubst t0 a)) ",
                "(s : Nat -> KExpr) (t : Nat -> KExpr) (h : forall (i : Nat), Eq KExpr (s i) (t i)) => ",
                "Eq.trans KExpr (psubst s (KExpr.app f a)) (KExpr.app (psubst s f) (psubst s a)) (psubst t (KExpr.app f a)) ",
                "(psubst_app s f a) ",
                "(Eq.trans KExpr (KExpr.app (psubst s f) (psubst s a)) (KExpr.app (psubst t f) (psubst t a)) (psubst t (KExpr.app f a)) ",
                "(Eq.trans KExpr (KExpr.app (psubst s f) (psubst s a)) (KExpr.app (psubst t f) (psubst s a)) (KExpr.app (psubst t f) (psubst t a)) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x (psubst s a)) (psubst s f) (psubst t f) (ihf s t h)) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app (psubst t f) x) (psubst s a) (psubst t a) (iha s t h))) ",
                "(Eq.symm KExpr (psubst t (KExpr.app f a)) (KExpr.app (psubst t f) (psubst t a)) (psubst_app t f a)))) ",
                // lam
                "(fun (ty : KExpr) (b : KExpr) ",
                "(ihty : forall (s0 : Nat -> KExpr) (t0 : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s0 i) (t0 i)) -> Eq KExpr (psubst s0 ty) (psubst t0 ty)) ",
                "(ihb : forall (s0 : Nat -> KExpr) (t0 : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s0 i) (t0 i)) -> Eq KExpr (psubst s0 b) (psubst t0 b)) ",
                "(s : Nat -> KExpr) (t : Nat -> KExpr) (h : forall (i : Nat), Eq KExpr (s i) (t i)) => ",
                "Eq.trans KExpr (psubst s (KExpr.lam ty b)) (KExpr.lam (psubst s ty) (psubst (up s) b)) (psubst t (KExpr.lam ty b)) ",
                "(psubst_lam s ty b) ",
                "(Eq.trans KExpr (KExpr.lam (psubst s ty) (psubst (up s) b)) (KExpr.lam (psubst t ty) (psubst (up t) b)) (psubst t (KExpr.lam ty b)) ",
                "(Eq.trans KExpr (KExpr.lam (psubst s ty) (psubst (up s) b)) (KExpr.lam (psubst t ty) (psubst (up s) b)) (KExpr.lam (psubst t ty) (psubst (up t) b)) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.lam x (psubst (up s) b)) (psubst s ty) (psubst t ty) (ihty s t h)) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.lam (psubst t ty) x) (psubst (up s) b) (psubst (up t) b) (ihb (up s) (up t) (up_pointwise s t h)))) ",
                "(Eq.symm KExpr (psubst t (KExpr.lam ty b)) (KExpr.lam (psubst t ty) (psubst (up t) b)) (psubst_lam t ty b)))) ",
                // pi
                "(fun (ty : KExpr) (b : KExpr) ",
                "(ihty : forall (s0 : Nat -> KExpr) (t0 : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s0 i) (t0 i)) -> Eq KExpr (psubst s0 ty) (psubst t0 ty)) ",
                "(ihb : forall (s0 : Nat -> KExpr) (t0 : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s0 i) (t0 i)) -> Eq KExpr (psubst s0 b) (psubst t0 b)) ",
                "(s : Nat -> KExpr) (t : Nat -> KExpr) (h : forall (i : Nat), Eq KExpr (s i) (t i)) => ",
                "Eq.trans KExpr (psubst s (KExpr.pi ty b)) (KExpr.pi (psubst s ty) (psubst (up s) b)) (psubst t (KExpr.pi ty b)) ",
                "(psubst_pi s ty b) ",
                "(Eq.trans KExpr (KExpr.pi (psubst s ty) (psubst (up s) b)) (KExpr.pi (psubst t ty) (psubst (up t) b)) (psubst t (KExpr.pi ty b)) ",
                "(Eq.trans KExpr (KExpr.pi (psubst s ty) (psubst (up s) b)) (KExpr.pi (psubst t ty) (psubst (up s) b)) (KExpr.pi (psubst t ty) (psubst (up t) b)) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi x (psubst (up s) b)) (psubst s ty) (psubst t ty) (ihty s t h)) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi (psubst t ty) x) (psubst (up s) b) (psubst (up t) b) (ihb (up s) (up t) (up_pointwise s t h)))) ",
                "(Eq.symm KExpr (psubst t (KExpr.pi ty b)) (KExpr.pi (psubst t ty) (psubst (up t) b)) (psubst_pi t ty b)))) ",
                // const
                "(fun (n : Name) (us : ListType Level) (s : Nat -> KExpr) (t : Nat -> KExpr) (h : forall (i : Nat), Eq KExpr (s i) (t i)) => ",
                "Eq.trans KExpr (psubst s (KExpr.const n us)) (KExpr.const n us) (psubst t (KExpr.const n us)) ",
                "(psubst_const s n us) (Eq.symm KExpr (psubst t (KExpr.const n us)) (KExpr.const n us) (psubst_const t n us))) ",
                // let_
                "(fun (lty : KExpr) (lv : KExpr) (lb : KExpr) ",
                "(ihty : forall (s0 : Nat -> KExpr) (t0 : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s0 i) (t0 i)) -> Eq KExpr (psubst s0 lty) (psubst t0 lty)) ",
                "(ihv : forall (s0 : Nat -> KExpr) (t0 : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s0 i) (t0 i)) -> Eq KExpr (psubst s0 lv) (psubst t0 lv)) ",
                "(ihb : forall (s0 : Nat -> KExpr) (t0 : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s0 i) (t0 i)) -> Eq KExpr (psubst s0 lb) (psubst t0 lb)) ",
                "(s : Nat -> KExpr) (t : Nat -> KExpr) (h : forall (i : Nat), Eq KExpr (s i) (t i)) => ",
                "Eq.trans KExpr (psubst s (KExpr.let_ lty lv lb)) (KExpr.let_ (psubst s lty) (psubst s lv) (psubst (up s) lb)) (psubst t (KExpr.let_ lty lv lb)) ",
                "(psubst_let_ s lty lv lb) ",
                "(Eq.trans KExpr (KExpr.let_ (psubst s lty) (psubst s lv) (psubst (up s) lb)) (KExpr.let_ (psubst t lty) (psubst t lv) (psubst (up t) lb)) (psubst t (KExpr.let_ lty lv lb)) ",
                "(Eq.trans KExpr (KExpr.let_ (psubst s lty) (psubst s lv) (psubst (up s) lb)) (KExpr.let_ (psubst t lty) (psubst s lv) (psubst (up s) lb)) (KExpr.let_ (psubst t lty) (psubst t lv) (psubst (up t) lb)) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ x (psubst s lv) (psubst (up s) lb)) (psubst s lty) (psubst t lty) (ihty s t h)) ",
                "(Eq.trans KExpr (KExpr.let_ (psubst t lty) (psubst s lv) (psubst (up s) lb)) (KExpr.let_ (psubst t lty) (psubst t lv) (psubst (up s) lb)) (KExpr.let_ (psubst t lty) (psubst t lv) (psubst (up t) lb)) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ (psubst t lty) x (psubst (up s) lb)) (psubst s lv) (psubst t lv) (ihv s t h)) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ (psubst t lty) (psubst t lv) x) (psubst (up s) lb) (psubst (up t) lb) (ihb (up s) (up t) (up_pointwise s t h))))) ",
                "(Eq.symm KExpr (psubst t (KExpr.let_ lty lv lb)) (KExpr.let_ (psubst t lty) (psubst t lv) (psubst (up t) lb)) (psubst_let_ t lty lv lb)))) ",
                // proj — single hole, no binder shift (ihsub at the SAME s/t).
                "(fun (ps : Name) (pidx : Nat) (sub : KExpr) ",
                "(ihsub : forall (s0 : Nat -> KExpr) (t0 : Nat -> KExpr), (forall (i : Nat), Eq KExpr (s0 i) (t0 i)) -> Eq KExpr (psubst s0 sub) (psubst t0 sub)) ",
                "(s : Nat -> KExpr) (t : Nat -> KExpr) (h : forall (i : Nat), Eq KExpr (s i) (t i)) => ",
                "Eq.trans KExpr (psubst s (KExpr.proj ps pidx sub)) (KExpr.proj ps pidx (psubst s sub)) (psubst t (KExpr.proj ps pidx sub)) ",
                "(psubst_proj s ps pidx sub) ",
                "(Eq.trans KExpr (KExpr.proj ps pidx (psubst s sub)) (KExpr.proj ps pidx (psubst t sub)) (psubst t (KExpr.proj ps pidx sub)) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj ps pidx x) (psubst s sub) (psubst t sub) (ihsub s t h)) ",
                "(Eq.symm KExpr (psubst t (KExpr.proj ps pidx sub)) (KExpr.proj ps pidx (psubst t sub)) (psubst_proj t ps pidx sub)))) ",
                // lit — leaf, like const.
                "(fun (v : Nat) (s : Nat -> KExpr) (t : Nat -> KExpr) (h : forall (i : Nat), Eq KExpr (s i) (t i)) => ",
                "Eq.trans KExpr (psubst s (KExpr.lit v)) (KExpr.lit v) (psubst t (KExpr.lit v)) ",
                "(psubst_lit s v) (Eq.symm KExpr (psubst t (KExpr.lit v)) (KExpr.lit v) (psubst_lit t v))) ",
                "e s t h",
            ).to_string()),
            is_axiom: false,
            description: "psubst congruence: substitutions agreeing pointwise give equal results (forall i, s i = t i) -> psubst s e = psubst t e. The funext-free replacement for the guide's funext rewrites. DerivedProved via KExpr.rec with substitution-universalized motive (lam/pi carry the hypothesis under binders via up_pointwise). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(), "psubst".to_string(),
                "psubst_sort".to_string(), "psubst_bvar".to_string(), "psubst_app".to_string(),
                "psubst_lam".to_string(), "psubst_pi".to_string(), "psubst_const".to_string(), "psubst_let_".to_string(),
                "psubst_proj".to_string(), "psubst_lit".to_string(),
                "up_pointwise".to_string(),
                "Eq.trans".to_string(), "Eq.symm".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // psubst_id: the identity substitution acts as the identity (guide
        // psubst_id, line 1134): psubst idsubst e = e. KExpr.rec on e; the lam/pi
        // body case rewrites `up idsubst` back to `idsubst` via psubst_pointwise +
        // up_idsubst (the funext-free stand-in for the guide's `funext up_idsubst`),
        // then applies the IH.
        self.add_definition_structural(SpecDefinition {
            name: "psubst_id".to_string(),
            type_src: "forall (e : KExpr), Eq KExpr (psubst idsubst e) e".to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) => ",
                "KExpr.rec (fun (e0 : KExpr) => Eq KExpr (psubst idsubst e0) e0) ",
                "(fun (n : Level) => psubst_sort idsubst n) ",
                "(fun (i : Nat) => psubst_bvar idsubst i) ",
                // app
                "(fun (f : KExpr) (a : KExpr) (ihf : Eq KExpr (psubst idsubst f) f) (iha : Eq KExpr (psubst idsubst a) a) => ",
                "Eq.trans KExpr (psubst idsubst (KExpr.app f a)) (KExpr.app (psubst idsubst f) (psubst idsubst a)) (KExpr.app f a) ",
                "(psubst_app idsubst f a) ",
                "(Eq.trans KExpr (KExpr.app (psubst idsubst f) (psubst idsubst a)) (KExpr.app f (psubst idsubst a)) (KExpr.app f a) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x (psubst idsubst a)) (psubst idsubst f) f ihf) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app f x) (psubst idsubst a) a iha))) ",
                // lam
                "(fun (ty : KExpr) (b : KExpr) (ihty : Eq KExpr (psubst idsubst ty) ty) (ihb : Eq KExpr (psubst idsubst b) b) => ",
                "Eq.trans KExpr (psubst idsubst (KExpr.lam ty b)) (KExpr.lam (psubst idsubst ty) (psubst (up idsubst) b)) (KExpr.lam ty b) ",
                "(psubst_lam idsubst ty b) ",
                "(Eq.trans KExpr (KExpr.lam (psubst idsubst ty) (psubst (up idsubst) b)) (KExpr.lam ty (psubst (up idsubst) b)) (KExpr.lam ty b) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.lam x (psubst (up idsubst) b)) (psubst idsubst ty) ty ihty) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.lam ty x) (psubst (up idsubst) b) b ",
                "(Eq.trans KExpr (psubst (up idsubst) b) (psubst idsubst b) b ",
                "(psubst_pointwise b (up idsubst) idsubst up_idsubst) ihb)))) ",
                // pi
                "(fun (ty : KExpr) (b : KExpr) (ihty : Eq KExpr (psubst idsubst ty) ty) (ihb : Eq KExpr (psubst idsubst b) b) => ",
                "Eq.trans KExpr (psubst idsubst (KExpr.pi ty b)) (KExpr.pi (psubst idsubst ty) (psubst (up idsubst) b)) (KExpr.pi ty b) ",
                "(psubst_pi idsubst ty b) ",
                "(Eq.trans KExpr (KExpr.pi (psubst idsubst ty) (psubst (up idsubst) b)) (KExpr.pi ty (psubst (up idsubst) b)) (KExpr.pi ty b) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi x (psubst (up idsubst) b)) (psubst idsubst ty) ty ihty) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi ty x) (psubst (up idsubst) b) b ",
                "(Eq.trans KExpr (psubst (up idsubst) b) (psubst idsubst b) b ",
                "(psubst_pointwise b (up idsubst) idsubst up_idsubst) ihb)))) ",
                // const
                "(fun (n : Name) (us : ListType Level) => psubst_const idsubst n us) ",
                // let_
                "(fun (lty : KExpr) (lv : KExpr) (lb : KExpr) (ihty : Eq KExpr (psubst idsubst lty) lty) (ihv : Eq KExpr (psubst idsubst lv) lv) (ihb : Eq KExpr (psubst idsubst lb) lb) => ",
                "Eq.trans KExpr (psubst idsubst (KExpr.let_ lty lv lb)) (KExpr.let_ (psubst idsubst lty) (psubst idsubst lv) (psubst (up idsubst) lb)) (KExpr.let_ lty lv lb) ",
                "(psubst_let_ idsubst lty lv lb) ",
                "(Eq.trans KExpr (KExpr.let_ (psubst idsubst lty) (psubst idsubst lv) (psubst (up idsubst) lb)) (KExpr.let_ lty (psubst idsubst lv) (psubst (up idsubst) lb)) (KExpr.let_ lty lv lb) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ x (psubst idsubst lv) (psubst (up idsubst) lb)) (psubst idsubst lty) lty ihty) ",
                "(Eq.trans KExpr (KExpr.let_ lty (psubst idsubst lv) (psubst (up idsubst) lb)) (KExpr.let_ lty lv (psubst (up idsubst) lb)) (KExpr.let_ lty lv lb) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ lty x (psubst (up idsubst) lb)) (psubst idsubst lv) lv ihv) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.let_ lty lv x) (psubst (up idsubst) lb) lb ",
                "(Eq.trans KExpr (psubst (up idsubst) lb) (psubst idsubst lb) lb ",
                "(psubst_pointwise lb (up idsubst) idsubst up_idsubst) ihb))))) ",
                // proj — single hole, no binder (psubst_proj + ihsub cong).
                "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (ihsub : Eq KExpr (psubst idsubst sub) sub) => ",
                "Eq.trans KExpr (psubst idsubst (KExpr.proj ps pidx sub)) (KExpr.proj ps pidx (psubst idsubst sub)) (KExpr.proj ps pidx sub) ",
                "(psubst_proj idsubst ps pidx sub) ",
                "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj ps pidx x) (psubst idsubst sub) sub ihsub)) ",
                // lit — leaf, like const.
                "(fun (v : Nat) => psubst_lit idsubst v) ",
                "e",
            ).to_string()),
            is_axiom: false,
            description: "The identity substitution acts as identity: psubst idsubst e = e. Guide's psubst_id (line 1134). DerivedProved via KExpr.rec on e; lam/pi body rewrites up idsubst -> idsubst via psubst_pointwise + up_idsubst (funext-free), then the IH. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(), "psubst".to_string(), "idsubst".to_string(),
                "psubst_sort".to_string(), "psubst_bvar".to_string(), "psubst_app".to_string(),
                "psubst_lam".to_string(), "psubst_pi".to_string(), "psubst_const".to_string(), "psubst_let_".to_string(),
                "psubst_proj".to_string(), "psubst_lit".to_string(),
                "psubst_pointwise".to_string(), "up_idsubst".to_string(),
                "Eq.trans".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // §8b'''' FVRel FREE-VARIABLE BISIMULATION — BATCH 4 (this port).
        // The structural relation `FVRel k e e'` ("e and e' are equal up to a
        // renaming of variables with index >= k") and its list companion
        // `FVRelL`, plus the STRUCTURAL / PASS-THROUGH core of the framework
        // (guide §8b'''', dependent_sn_modulo_candmodel.lean:1302-1798). The
        // guide's `i < k` / `k <= i` constructor side-conditions are ported to
        // clean-verify's existing `Lt`/`Le` inductives (foundation_types.rs) —
        // faithful to the guide's `<`/`<=`. The bisimulation LEMMAS
        // (fvRel_delta_bisim / fvRel_iota_bisim / fvRel_beta_bisim / fvRel_bisim /
        // whnfAcc_of_fvRel / whnfAcc_of_instantiate_bvar0) and the ARITHMETIC
        // renaming lemmas (fvRel_refl / fvRel_mono / fvRel_lift /
        // fvRel_instantiate_bvar0 / fvRel_instantiate_at / fvRelL_head_some) are
        // the NEXT batch — they need a Nat `Lt`/`Le` dichotomy + a Sigma/CPS
        // existential encoding, absent from this structural core. Every decl here
        // is value-full (add_inductive / add_definition_structural) — ZERO new
        // kernel axioms, census stays 16.
        // ================================================================

        // FVRel k e e' : e and e' have the same shape and agree on all bound
        // variables (index < k, `bvar_bound` carrying `Lt i k`); free variables
        // (index >= k) may be renamed (`bvar_free` carrying `Le k i` / `Le k j`).
        // Guide's FVRel (dependent_sn_modulo_candmodel.lean:1319). Type-valued
        // (clean-verify idiom) indexed inductive; the Lt/Le premises are the
        // foundation ordering relations. Positivity identical in shape to the live
        // `beta_reduces` (recursive occurrences are strictly-positive premises).
        // ZERO new axioms (Inductive/Constructor/Recursor).
        self.add_inductive(
            concat!(
                "inductive FVRel : Nat -> KExpr -> KExpr -> Type\n",
                "| bvar_bound : forall (k : Nat) (i : Nat), Lt i k -> FVRel k (KExpr.bvar i) (KExpr.bvar i)\n",
                "| bvar_free : forall (k : Nat) (i : Nat) (j : Nat), Le k i -> Le k j -> FVRel k (KExpr.bvar i) (KExpr.bvar j)\n",
                "| sort : forall (k : Nat) (n : Level), FVRel k (KExpr.sort n) (KExpr.sort n)\n",
                "| const : forall (k : Nat) (n : Name) (us : ListType Level), FVRel k (KExpr.const n us) (KExpr.const n us)\n",
                "| app : forall (k : Nat) (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr), FVRel k f f2 -> FVRel k a a2 -> FVRel k (KExpr.app f a) (KExpr.app f2 a2)\n",
                "| lam : forall (k : Nat) (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr), FVRel k A A2 -> FVRel (Nat.succ k) b b2 -> FVRel k (KExpr.lam A b) (KExpr.lam A2 b2)\n",
                "| pi : forall (k : Nat) (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr), FVRel k A A2 -> FVRel (Nat.succ k) B B2 -> FVRel k (KExpr.pi A B) (KExpr.pi A2 B2)\n",
                "| let_ : forall (k : Nat) (ty : KExpr) (ty2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr), FVRel k ty ty2 -> FVRel k v v2 -> FVRel (Nat.succ k) b b2 -> FVRel k (KExpr.let_ ty v b) (KExpr.let_ ty2 v2 b2)\n",
                "| proj : forall (k : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr), FVRel k sub sub2 -> FVRel k (KExpr.proj s i sub) (KExpr.proj s i sub2)\n",
                "| lit : forall (k : Nat) (v : Nat), FVRel k (KExpr.lit v) (KExpr.lit v)"
            ),
            "FVRel k e e' (Brick 2 free-variable bisimulation, guide dependent_sn_modulo_candmodel.lean:1319): e and e' have the same shape and agree on all BOUND variables (index < k, bvar_bound carrying Lt i k); FREE variables (index >= k) may be renamed arbitrarily (bvar_free carrying Le k i / Le k j). The structural relation whose bisimulation for whnf_step reflects strong normalization along the pi-case instantiation (instantiate C (bvar 0) is a free-variable renaming of C). The guide's `<`/`<=` side-conditions are the foundation Lt/Le inductives. LET INCREMENT (task #28): the trailing let_ congruence (ty/v at k, body at succ k — guide SnLet.lean:1469) makes every FVRel.rec gain a trailing 8th minor. Kernel generates FVRel.rec, sound by construction. ZERO new axioms (Inductive/Constructor/Recursor, census-neutral).",
        )?;

        // FVRelL k xs ys : pointwise FVRel on argument lists. Guide's FVRelL
        // (dependent_sn_modulo_candmodel.lean:1523). Used by the spine machinery
        // (kapp_args / apply_spine / list_drop / list_take) of the delta/iota
        // bisimulation. ZERO new axioms.
        self.add_inductive(
            concat!(
                "inductive FVRelL : Nat -> ListType KExpr -> ListType KExpr -> Type\n",
                "| nil : forall (k : Nat), FVRelL k (ListType.nil KExpr) (ListType.nil KExpr)\n",
                "| cons : forall (k : Nat) (x : KExpr) (x2 : KExpr) (xs : ListType KExpr) (xs2 : ListType KExpr), FVRel k x x2 -> FVRelL k xs xs2 -> FVRelL k (ListType.cons KExpr x xs) (ListType.cons KExpr x2 xs2)"
            ),
            "FVRelL k xs ys (Brick 2): pointwise FVRel on argument lists — the list companion of FVRel used by the spine machinery of the delta/iota bisimulation. Guide's FVRelL (dependent_sn_modulo_candmodel.lean:1523). Kernel generates FVRelL.rec. ZERO new axioms (Inductive/Constructor/Recursor, census-neutral).",
        )?;

        // --- BATCH 4a: FVRel structural pass-through lemmas (FVRel.rec) ---
        // Each is FVRel.rec (0 params, 3 indices k/e/e', 7 arms) with a motive
        // over the 3 indices + major, then `k e e2 h`. Explicit-typed binders
        // throughout (proven le_trans/psubst_pointwise idiom). ZERO axioms.

        // fvRel_symm: FVRel is symmetric (guide fvRel_symm, line 1351). Pass-
        // through: each arm re-applies the constructor with the two related terms
        // swapped (bvar_free swaps i/j and hi/hj; app/lam/pi swap via the ihs).
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_symm".to_string(),
            type_src: "forall (k : Nat) (e : KExpr) (e2 : KExpr), FVRel k e e2 -> FVRel k e2 e".to_string(),
            value_src: Some(r"fun (k : Nat) (e : KExpr) (e2 : KExpr) (h : FVRel k e e2) => FVRel.rec (fun (k0 : Nat) (a : KExpr) (b : KExpr) (hh : FVRel k0 a b) => FVRel k0 b a) (fun (k0 : Nat) (i : Nat) (hlt : Lt i k0) => FVRel.bvar_bound k0 i hlt) (fun (k0 : Nat) (i : Nat) (j : Nat) (hi : Le k0 i) (hj : Le k0 j) => FVRel.bvar_free k0 j i hj hi) (fun (k0 : Nat) (n : Level) => FVRel.sort k0 n) (fun (k0 : Nat) (n : Name) (us : ListType Level) => FVRel.const k0 n us) (fun (k0 : Nat) (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : FVRel k0 f f2) (ha : FVRel k0 a a2) (ihf : FVRel k0 f2 f) (iha : FVRel k0 a2 a) => FVRel.app k0 f2 f a2 a ihf iha) (fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : FVRel k0 A A2) (hb : FVRel (Nat.succ k0) b b2) (ihA : FVRel k0 A2 A) (ihb : FVRel (Nat.succ k0) b2 b) => FVRel.lam k0 A2 A b2 b ihA ihb) (fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr) (hA : FVRel k0 A A2) (hB : FVRel (Nat.succ k0) B B2) (ihA : FVRel k0 A2 A) (ihB : FVRel (Nat.succ k0) B2 B) => FVRel.pi k0 A2 A B2 B ihA ihB) (fun (k0 : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (hty : FVRel k0 lty lty2) (hv : FVRel k0 lv lv2) (hb : FVRel (Nat.succ k0) lb lb2) (ihty : FVRel k0 lty2 lty) (ihv : FVRel k0 lv2 lv) (ihb : FVRel (Nat.succ k0) lb2 lb) => FVRel.let_ k0 lty2 lty lv2 lv lb2 lb ihty ihv ihb) (fun (k0 : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : FVRel k0 sub sub2) (ihsub : FVRel k0 sub2 sub) => FVRel.proj k0 s i sub2 sub ihsub) (fun (k0 : Nat) (v : Nat) => FVRel.lit k0 v) k e e2 h".to_string()),
            is_axiom: false,
            description: "FVRel is symmetric: FVRel k e e2 -> FVRel k e2 e. Guide's fvRel_symm (line 1351). Pass-through FVRel.rec (each arm re-applies the constructor with related terms swapped). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRel_const_name: the head const name is preserved by FVRel (guide
        // fvRel_const_name, line 1517). Every arm's two related terms have the
        // same kexpr_const_name (none, except const which agrees on n), so each
        // arm is Eq.refl at the shared normal form.
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_const_name".to_string(),
            type_src: "forall (k : Nat) (e : KExpr) (e2 : KExpr), FVRel k e e2 -> Eq (OptionType Name) (kexpr_const_name e) (kexpr_const_name e2)".to_string(),
            value_src: Some(r"fun (k : Nat) (e : KExpr) (e2 : KExpr) (h : FVRel k e e2) => FVRel.rec (fun (k0 : Nat) (a : KExpr) (b : KExpr) (hh : FVRel k0 a b) => Eq (OptionType Name) (kexpr_const_name a) (kexpr_const_name b)) (fun (k0 : Nat) (i : Nat) (hlt : Lt i k0) => Eq.refl (OptionType Name) (OptionType.none Name)) (fun (k0 : Nat) (i : Nat) (j : Nat) (hi : Le k0 i) (hj : Le k0 j) => Eq.refl (OptionType Name) (OptionType.none Name)) (fun (k0 : Nat) (n : Level) => Eq.refl (OptionType Name) (OptionType.none Name)) (fun (k0 : Nat) (n : Name) (us : ListType Level) => Eq.refl (OptionType Name) (OptionType.some Name n)) (fun (k0 : Nat) (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : FVRel k0 f f2) (ha : FVRel k0 a a2) (ihf : Eq (OptionType Name) (kexpr_const_name f) (kexpr_const_name f2)) (iha : Eq (OptionType Name) (kexpr_const_name a) (kexpr_const_name a2)) => Eq.refl (OptionType Name) (OptionType.none Name)) (fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : FVRel k0 A A2) (hb : FVRel (Nat.succ k0) b b2) (ihA : Eq (OptionType Name) (kexpr_const_name A) (kexpr_const_name A2)) (ihb : Eq (OptionType Name) (kexpr_const_name b) (kexpr_const_name b2)) => Eq.refl (OptionType Name) (OptionType.none Name)) (fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr) (hA : FVRel k0 A A2) (hB : FVRel (Nat.succ k0) B B2) (ihA : Eq (OptionType Name) (kexpr_const_name A) (kexpr_const_name A2)) (ihB : Eq (OptionType Name) (kexpr_const_name B) (kexpr_const_name B2)) => Eq.refl (OptionType Name) (OptionType.none Name)) (fun (k0 : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (hty : FVRel k0 lty lty2) (hv : FVRel k0 lv lv2) (hb : FVRel (Nat.succ k0) lb lb2) (ihty : Eq (OptionType Name) (kexpr_const_name lty) (kexpr_const_name lty2)) (ihv : Eq (OptionType Name) (kexpr_const_name lv) (kexpr_const_name lv2)) (ihb : Eq (OptionType Name) (kexpr_const_name lb) (kexpr_const_name lb2)) => Eq.refl (OptionType Name) (OptionType.none Name)) (fun (k0 : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : FVRel k0 sub sub2) (ihsub : Eq (OptionType Name) (kexpr_const_name sub) (kexpr_const_name sub2)) => Eq.refl (OptionType Name) (OptionType.none Name)) (fun (k0 : Nat) (v : Nat) => Eq.refl (OptionType Name) (OptionType.none Name)) k e e2 h".to_string()),
            is_axiom: false,
            description: "The head const name is preserved by FVRel: kexpr_const_name e = kexpr_const_name e2. Guide's fvRel_const_name (line 1517). FVRel.rec; each arm is Eq.refl at the shared normal form (none, or some n for const). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(), "kexpr_const_name".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRel_kapp_fn: kapp_fn respects FVRel (guide fvRel_kapp_fn, line 1502).
        // bvar/sort/const arms reconstruct the head; app arm returns ihf
        // (kapp_fn (app f a) = kapp_fn f); lam/pi reconstruct the intro.
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_kapp_fn".to_string(),
            type_src: "forall (k : Nat) (e : KExpr) (e2 : KExpr), FVRel k e e2 -> FVRel k (kapp_fn e) (kapp_fn e2)".to_string(),
            value_src: Some(r"fun (k : Nat) (e : KExpr) (e2 : KExpr) (h : FVRel k e e2) => FVRel.rec (fun (k0 : Nat) (a : KExpr) (b : KExpr) (hh : FVRel k0 a b) => FVRel k0 (kapp_fn a) (kapp_fn b)) (fun (k0 : Nat) (i : Nat) (hlt : Lt i k0) => FVRel.bvar_bound k0 i hlt) (fun (k0 : Nat) (i : Nat) (j : Nat) (hi : Le k0 i) (hj : Le k0 j) => FVRel.bvar_free k0 i j hi hj) (fun (k0 : Nat) (n : Level) => FVRel.sort k0 n) (fun (k0 : Nat) (n : Name) (us : ListType Level) => FVRel.const k0 n us) (fun (k0 : Nat) (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : FVRel k0 f f2) (ha : FVRel k0 a a2) (ihf : FVRel k0 (kapp_fn f) (kapp_fn f2)) (iha : FVRel k0 (kapp_fn a) (kapp_fn a2)) => ihf) (fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : FVRel k0 A A2) (hb : FVRel (Nat.succ k0) b b2) (ihA : FVRel k0 (kapp_fn A) (kapp_fn A2)) (ihb : FVRel (Nat.succ k0) (kapp_fn b) (kapp_fn b2)) => FVRel.lam k0 A A2 b b2 hA hb) (fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr) (hA : FVRel k0 A A2) (hB : FVRel (Nat.succ k0) B B2) (ihA : FVRel k0 (kapp_fn A) (kapp_fn A2)) (ihB : FVRel (Nat.succ k0) (kapp_fn B) (kapp_fn B2)) => FVRel.pi k0 A A2 B B2 hA hB) (fun (k0 : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (hty : FVRel k0 lty lty2) (hv : FVRel k0 lv lv2) (hb : FVRel (Nat.succ k0) lb lb2) (ihty : FVRel k0 (kapp_fn lty) (kapp_fn lty2)) (ihv : FVRel k0 (kapp_fn lv) (kapp_fn lv2)) (ihb : FVRel (Nat.succ k0) (kapp_fn lb) (kapp_fn lb2)) => FVRel.let_ k0 lty lty2 lv lv2 lb lb2 hty hv hb) (fun (k0 : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : FVRel k0 sub sub2) (ihsub : FVRel k0 (kapp_fn sub) (kapp_fn sub2)) => FVRel.proj k0 s i sub sub2 hsub) (fun (k0 : Nat) (v : Nat) => FVRel.lit k0 v) k e e2 h".to_string()),
            is_axiom: false,
            description: "kapp_fn respects FVRel: FVRel k e e2 -> FVRel k (kapp_fn e) (kapp_fn e2). Guide's fvRel_kapp_fn (line 1502). FVRel.rec; app arm returns the head ih (kapp_fn (app f a) = kapp_fn f), the other arms reconstruct. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(), "kapp_fn".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- BATCH 4b: FVRelL list lemmas + fvRel_kapp_args bridge ---

        // fvRelL_append: FVRelL is preserved by list_append (guide fvRelL_append,
        // line 1528). FVRelL.rec on the first proof, second generalized into the
        // motive (funext-free convoy).
        self.add_definition_structural(SpecDefinition {
            name: "fvRelL_append".to_string(),
            type_src: "forall (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr) (xs2 : ListType KExpr) (ys2 : ListType KExpr), FVRelL k xs ys -> FVRelL k xs2 ys2 -> FVRelL k (list_append xs xs2) (list_append ys ys2)".to_string(),
            value_src: Some(r"fun (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr) (xs2 : ListType KExpr) (ys2 : ListType KExpr) (h1 : FVRelL k xs ys) (h2 : FVRelL k xs2 ys2) => FVRelL.rec k (fun (p0 : ListType KExpr) (q0 : ListType KExpr) (hh : FVRelL k p0 q0) => forall (p : ListType KExpr) (q : ListType KExpr), FVRelL k p q -> FVRelL k (list_append p0 p) (list_append q0 q)) (fun (p : ListType KExpr) (q : ListType KExpr) (hpq : FVRelL k p q) => hpq) (fun (x : KExpr) (x2 : KExpr) (l : ListType KExpr) (l2 : ListType KExpr) (hx : FVRel k x x2) (hl : FVRelL k l l2) (ihl : forall (p : ListType KExpr) (q : ListType KExpr), FVRelL k p q -> FVRelL k (list_append l p) (list_append l2 q)) => fun (p : ListType KExpr) (q : ListType KExpr) (hpq : FVRelL k p q) => FVRelL.cons k x x2 (list_append l p) (list_append l2 q) hx (ihl p q hpq)) xs ys h1 xs2 ys2 h2".to_string()),
            is_axiom: false,
            description: "FVRelL is preserved by list_append. Guide's fvRelL_append (line 1528). FVRelL.rec on the first proof with the second generalized into the motive. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRelL".to_string(), "FVRelL.rec".to_string(), "FVRelL.cons".to_string(), "list_append".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRelL_tail: FVRelL is preserved by list_tail (guide fvRelL_tail, 1535).
        self.add_definition_structural(SpecDefinition {
            name: "fvRelL_tail".to_string(),
            type_src: "forall (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr), FVRelL k xs ys -> FVRelL k (list_tail xs) (list_tail ys)".to_string(),
            value_src: Some(r"fun (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr) (h : FVRelL k xs ys) => FVRelL.rec k (fun (p0 : ListType KExpr) (q0 : ListType KExpr) (hh : FVRelL k p0 q0) => FVRelL k (list_tail p0) (list_tail q0)) (FVRelL.nil k) (fun (x : KExpr) (x2 : KExpr) (l : ListType KExpr) (l2 : ListType KExpr) (hx : FVRel k x x2) (hl : FVRelL k l l2) (ihl : FVRelL k (list_tail l) (list_tail l2)) => hl) xs ys h".to_string()),
            is_axiom: false,
            description: "FVRelL is preserved by list_tail. Guide's fvRelL_tail (line 1535). FVRelL.rec; nil arm nil, cons arm returns the tail proof. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRelL".to_string(), "FVRelL.rec".to_string(), "FVRelL.nil".to_string(), "list_tail".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRelL_length: FVRelL-related lists have equal length (guide
        // fvRelL_length, line 1559). FVRelL.rec; cons arm congrArg Nat.succ.
        self.add_definition_structural(SpecDefinition {
            name: "fvRelL_length".to_string(),
            type_src: "forall (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr), FVRelL k xs ys -> Eq Nat (list_length xs) (list_length ys)".to_string(),
            value_src: Some(r"fun (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr) (h : FVRelL k xs ys) => FVRelL.rec k (fun (p0 : ListType KExpr) (q0 : ListType KExpr) (hh : FVRelL k p0 q0) => Eq Nat (list_length p0) (list_length q0)) (Eq.refl Nat Nat.zero) (fun (x : KExpr) (x2 : KExpr) (l : ListType KExpr) (l2 : ListType KExpr) (hx : FVRel k x x2) (hl : FVRelL k l l2) (ihl : Eq Nat (list_length l) (list_length l2)) => Eq.cong Nat Nat Nat.succ (list_length l) (list_length l2) ihl) xs ys h".to_string()),
            is_axiom: false,
            description: "FVRelL-related lists have equal length. Guide's fvRelL_length (line 1559). FVRelL.rec; nil refl 0, cons Eq.cong Nat.succ on the ih. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRelL".to_string(), "FVRelL.rec".to_string(), "list_length".to_string(), "Eq.refl".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRelL_drop: FVRelL is preserved by list_drop (guide fvRelL_drop, 1541).
        // Nat.rec on n; succ case peels a list_tail via fvRelL_tail.
        self.add_definition_structural(SpecDefinition {
            name: "fvRelL_drop".to_string(),
            type_src: "forall (n : Nat) (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr), FVRelL k xs ys -> FVRelL k (list_drop n xs) (list_drop n ys)".to_string(),
            value_src: Some(r"fun (n : Nat) (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr) (h : FVRelL k xs ys) => Nat.rec (fun (n0 : Nat) => forall (k0 : Nat) (p : ListType KExpr) (q : ListType KExpr), FVRelL k0 p q -> FVRelL k0 (list_drop n0 p) (list_drop n0 q)) (fun (k0 : Nat) (p : ListType KExpr) (q : ListType KExpr) (h0 : FVRelL k0 p q) => h0) (fun (m : Nat) (ih : forall (k0 : Nat) (p : ListType KExpr) (q : ListType KExpr), FVRelL k0 p q -> FVRelL k0 (list_drop m p) (list_drop m q)) (k0 : Nat) (p : ListType KExpr) (q : ListType KExpr) (h0 : FVRelL k0 p q) => ih k0 (list_tail p) (list_tail q) (fvRelL_tail k0 p q h0)) n k xs ys h".to_string()),
            is_axiom: false,
            description: "FVRelL is preserved by list_drop. Guide's fvRelL_drop (line 1541). Nat.rec on n; succ peels a list_tail via fvRelL_tail. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "FVRelL".to_string(), "list_drop".to_string(), "list_tail".to_string(), "fvRelL_tail".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRelL_take: FVRelL is preserved by list_take (guide fvRelL_take, 1548).
        // Nat.rec on n; succ case does an inner FVRelL.rec (list_take branches on
        // the list) rebuilding the cons via the outer Nat.rec ih.
        self.add_definition_structural(SpecDefinition {
            name: "fvRelL_take".to_string(),
            type_src: "forall (n : Nat) (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr), FVRelL k xs ys -> FVRelL k (list_take n xs) (list_take n ys)".to_string(),
            value_src: Some(r"fun (n : Nat) (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr) (h : FVRelL k xs ys) => Nat.rec (fun (n0 : Nat) => forall (k0 : Nat) (p : ListType KExpr) (q : ListType KExpr), FVRelL k0 p q -> FVRelL k0 (list_take n0 p) (list_take n0 q)) (fun (k0 : Nat) (p : ListType KExpr) (q : ListType KExpr) (h0 : FVRelL k0 p q) => FVRelL.nil k0) (fun (m : Nat) (ih : forall (k0 : Nat) (p : ListType KExpr) (q : ListType KExpr), FVRelL k0 p q -> FVRelL k0 (list_take m p) (list_take m q)) (k0 : Nat) (p : ListType KExpr) (q : ListType KExpr) (h0 : FVRelL k0 p q) => FVRelL.rec k0 (fun (p1 : ListType KExpr) (q1 : ListType KExpr) (hh : FVRelL k0 p1 q1) => FVRelL k0 (list_take (Nat.succ m) p1) (list_take (Nat.succ m) q1)) (FVRelL.nil k0) (fun (x : KExpr) (x2 : KExpr) (l : ListType KExpr) (l2 : ListType KExpr) (hx : FVRel k0 x x2) (hl : FVRelL k0 l l2) (ihl : FVRelL k0 (list_take (Nat.succ m) l) (list_take (Nat.succ m) l2)) => FVRelL.cons k0 x x2 (list_take m l) (list_take m l2) hx (ih k0 l l2 hl)) p q h0) n k xs ys h".to_string()),
            is_axiom: false,
            description: "FVRelL is preserved by list_take. Guide's fvRelL_take (line 1548). Nat.rec on n; succ case inner FVRelL.rec rebuilding the cons via the outer ih. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "FVRelL".to_string(), "FVRelL.rec".to_string(), "FVRelL.cons".to_string(), "FVRelL.nil".to_string(), "list_take".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRelL_apply_spine: FVRelL-related spines applied to FVRel-related heads
        // stay FVRel-related (guide fvRelL_apply_spine, line 1565). FVRelL.rec with
        // the (head,head') pair generalized into the motive.
        self.add_definition_structural(SpecDefinition {
            name: "fvRelL_apply_spine".to_string(),
            type_src: "forall (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr), FVRelL k xs ys -> forall (p : KExpr) (q : KExpr), FVRel k p q -> FVRel k (apply_spine xs p) (apply_spine ys q)".to_string(),
            value_src: Some(r"fun (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr) (hxs : FVRelL k xs ys) => FVRelL.rec k (fun (p0 : ListType KExpr) (q0 : ListType KExpr) (hh : FVRelL k p0 q0) => forall (p : KExpr) (q : KExpr), FVRel k p q -> FVRel k (apply_spine p0 p) (apply_spine q0 q)) (fun (p : KExpr) (q : KExpr) (hpq : FVRel k p q) => hpq) (fun (x : KExpr) (x2 : KExpr) (l : ListType KExpr) (l2 : ListType KExpr) (hx : FVRel k x x2) (hl : FVRelL k l l2) (ihl : forall (p : KExpr) (q : KExpr), FVRel k p q -> FVRel k (apply_spine l p) (apply_spine l2 q)) => fun (p : KExpr) (q : KExpr) (hpq : FVRel k p q) => ihl (KExpr.app p x) (KExpr.app q x2) (FVRel.app k p q x x2 hpq hx)) xs ys hxs".to_string()),
            is_axiom: false,
            description: "FVRelL-related spines applied to FVRel-related heads stay FVRel-related. Guide's fvRelL_apply_spine (line 1565). FVRelL.rec with the head pair generalized into the motive; cons arm pushes an app via FVRel.app. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRelL".to_string(), "FVRelL.rec".to_string(), "FVRel.app".to_string(), "apply_spine".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRel_kapp_args: FVRel-related terms have FVRelL-related argument spines
        // (guide fvRel_kapp_args, line 1573). FVRel.rec; app arm splits via
        // fvRelL_append (kapp_args (app f a) = list_append (kapp_args f) [a]).
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_kapp_args".to_string(),
            type_src: "forall (k : Nat) (e : KExpr) (e2 : KExpr), FVRel k e e2 -> FVRelL k (kapp_args e) (kapp_args e2)".to_string(),
            value_src: Some(r"fun (k : Nat) (e : KExpr) (e2 : KExpr) (h : FVRel k e e2) => FVRel.rec (fun (k0 : Nat) (a : KExpr) (b : KExpr) (hh : FVRel k0 a b) => FVRelL k0 (kapp_args a) (kapp_args b)) (fun (k0 : Nat) (i : Nat) (hlt : Lt i k0) => FVRelL.nil k0) (fun (k0 : Nat) (i : Nat) (j : Nat) (hi : Le k0 i) (hj : Le k0 j) => FVRelL.nil k0) (fun (k0 : Nat) (n : Level) => FVRelL.nil k0) (fun (k0 : Nat) (n : Name) (us : ListType Level) => FVRelL.nil k0) (fun (k0 : Nat) (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : FVRel k0 f f2) (ha : FVRel k0 a a2) (ihf : FVRelL k0 (kapp_args f) (kapp_args f2)) (iha : FVRelL k0 (kapp_args a) (kapp_args a2)) => fvRelL_append k0 (kapp_args f) (kapp_args f2) (ListType.cons KExpr a (ListType.nil KExpr)) (ListType.cons KExpr a2 (ListType.nil KExpr)) ihf (FVRelL.cons k0 a a2 (ListType.nil KExpr) (ListType.nil KExpr) ha (FVRelL.nil k0))) (fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : FVRel k0 A A2) (hb : FVRel (Nat.succ k0) b b2) (ihA : FVRelL k0 (kapp_args A) (kapp_args A2)) (ihb : FVRelL (Nat.succ k0) (kapp_args b) (kapp_args b2)) => FVRelL.nil k0) (fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr) (hA : FVRel k0 A A2) (hB : FVRel (Nat.succ k0) B B2) (ihA : FVRelL k0 (kapp_args A) (kapp_args A2)) (ihB : FVRelL (Nat.succ k0) (kapp_args B) (kapp_args B2)) => FVRelL.nil k0) (fun (k0 : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (hty : FVRel k0 lty lty2) (hv : FVRel k0 lv lv2) (hb : FVRel (Nat.succ k0) lb lb2) (ihty : FVRelL k0 (kapp_args lty) (kapp_args lty2)) (ihv : FVRelL k0 (kapp_args lv) (kapp_args lv2)) (ihb : FVRelL (Nat.succ k0) (kapp_args lb) (kapp_args lb2)) => FVRelL.nil k0) (fun (k0 : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : FVRel k0 sub sub2) (ihsub : FVRelL k0 (kapp_args sub) (kapp_args sub2)) => FVRelL.nil k0) (fun (k0 : Nat) (v : Nat) => FVRelL.nil k0) k e e2 h".to_string()),
            is_axiom: false,
            description: "FVRel-related terms have FVRelL-related argument spines: FVRelL k (kapp_args e) (kapp_args e2). Guide's fvRel_kapp_args (line 1573). FVRel.rec; app arm splits kapp_args via fvRelL_append. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(), "FVRelL".to_string(), "FVRelL.cons".to_string(), "FVRelL.nil".to_string(), "fvRelL_append".to_string(), "kapp_args".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // §8b'''' FVRel BISIMULATION — BATCH 5 (this port). The 12 lemmas
        // batch 4 skipped: (A) ARITHMETIC renaming lemmas (need a total Nat
        // Lt/Le dichotomy) and (B) EXISTENTIAL bisimulation lemmas (packaged
        // as WITNESS INDUCTIVES, the clean-verify Sigma/Exists-free idiom —
        // the exact pattern DefEqJoinable uses, commit a96af44b). Every decl
        // here is value-full (add_inductive / add_definition_structural) —
        // ZERO new kernel axioms, census stays 16.
        // ================================================================

        // NatLtLeDichotomy i k : the total Nat ordering decision collapsed to a
        // 2-way disjoint sum (Lt i k OR Le k i) — a census-neutral witness
        // inductive standing in for clean-verify's absent Or/Sum. The (A)
        // arithmetic lemmas case on `i < k` (bvar_bound) vs `k <= i`
        // (bvar_free); this packages that decision. Type-valued (it eliminates
        // into the Type-valued FVRel). ZERO new axioms.
        self.add_inductive(
            concat!(
                "inductive NatLtLeDichotomy : Nat -> Nat -> Type\n",
                "| inl : forall (i : Nat) (k : Nat), Lt i k -> NatLtLeDichotomy i k\n",
                "| inr : forall (i : Nat) (k : Nat), Le k i -> NatLtLeDichotomy i k"
            ),
            "NatLtLeDichotomy i k (Brick 2 batch 5): the disjoint sum Lt i k (+) Le k i — the total Nat ordering decision the (A) FVRel arithmetic lemmas case on (bound variable i < k vs free k <= i), packaged as a 2-constructor witness inductive since clean-verify has no Or/Sum. Type-valued (eliminates into Type-valued FVRel). Kernel generates NatLtLeDichotomy.rec. ZERO new axioms (Inductive/Constructor/Recursor, census-neutral).",
        )?;

        // nat_lt_le_dichotomy : forall i k, NatLtLeDichotomy i k. The totality
        // proof, by double Nat.rec: k=0 -> Le 0 i (inr); i=0, k=succ -> Lt 0
        // (succ) (inl); succ/succ lifts the sub-decision (ih i' k') via
        // Lt.succ_lt_succ / le_succ_succ, eliminated through NatLtLeDichotomy.rec.
        self.add_definition_structural(SpecDefinition {
            name: "nat_lt_le_dichotomy".to_string(),
            type_src: "forall (i : Nat) (k : Nat), NatLtLeDichotomy i k".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) => Nat.rec ",
                "(fun (i0 : Nat) => forall (k : Nat), NatLtLeDichotomy i0 k) ",
                "(fun (k : Nat) => Nat.rec ",
                "(fun (k0 : Nat) => NatLtLeDichotomy Nat.zero k0) ",
                "(NatLtLeDichotomy.inr Nat.zero Nat.zero (Le.refl Nat.zero)) ",
                "(fun (k2 : Nat) (_d : NatLtLeDichotomy Nat.zero k2) => NatLtLeDichotomy.inl Nat.zero (Nat.succ k2) (Lt.zero_lt_succ k2)) ",
                "k) ",
                "(fun (i2 : Nat) (ih : forall (k : Nat), NatLtLeDichotomy i2 k) => ",
                "fun (k : Nat) => Nat.rec ",
                "(fun (k0 : Nat) => NatLtLeDichotomy (Nat.succ i2) k0) ",
                "(NatLtLeDichotomy.inr (Nat.succ i2) Nat.zero (le_zero_n (Nat.succ i2))) ",
                "(fun (k2 : Nat) (_d : NatLtLeDichotomy (Nat.succ i2) k2) => ",
                "NatLtLeDichotomy.rec i2 k2 ",
                "(fun (_dd : NatLtLeDichotomy i2 k2) => NatLtLeDichotomy (Nat.succ i2) (Nat.succ k2)) ",
                "(fun (hlt : Lt i2 k2) => NatLtLeDichotomy.inl (Nat.succ i2) (Nat.succ k2) (Lt.succ_lt_succ i2 k2 hlt)) ",
                "(fun (hle : Le k2 i2) => NatLtLeDichotomy.inr (Nat.succ i2) (Nat.succ k2) (le_succ_succ k2 i2 hle)) ",
                "(ih k2)) ",
                "k) ",
                "i",
            ).to_string()),
            is_axiom: false,
            description: "Total Nat ordering dichotomy: forall i k, Lt i k (+) Le k i (as NatLtLeDichotomy). DerivedProved by double Nat.rec (k=0 -> inr Le 0 i; i=0,k=succ -> inl Lt 0 (succ); succ/succ lifts ih via Lt.succ_lt_succ / le_succ_succ through NatLtLeDichotomy.rec). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "NatLtLeDichotomy".to_string(), "Nat.rec".to_string(),
                "Lt.zero_lt_succ".to_string(), "Lt.succ_lt_succ".to_string(),
                "Le.refl".to_string(), "le_zero_n".to_string(), "le_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRel_refl (A1): FVRel is reflexive (guide fvRel_refl, line 1335).
        // KExpr.rec on e with a k-universalized motive; the bvar case decides
        // i < k (bvar_bound) vs k <= i (bvar_free) via nat_lt_le_dichotomy.
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_refl".to_string(),
            type_src: "forall (k : Nat) (e : KExpr), FVRel k e e".to_string(),
            value_src: Some(concat!(
                "fun (k : Nat) (e : KExpr) => ",
                "KExpr.rec (fun (e0 : KExpr) => forall (k0 : Nat), FVRel k0 e0 e0) ",
                "(fun (n : Level) (k0 : Nat) => FVRel.sort k0 n) ",
                "(fun (i : Nat) (k0 : Nat) => NatLtLeDichotomy.rec i k0 (fun (_d : NatLtLeDichotomy i k0) => FVRel k0 (KExpr.bvar i) (KExpr.bvar i)) (fun (hlt : Lt i k0) => FVRel.bvar_bound k0 i hlt) (fun (hle : Le k0 i) => FVRel.bvar_free k0 i i hle hle) (nat_lt_le_dichotomy i k0)) ",
                "(fun (f : KExpr) (a : KExpr) (ihf : forall (k0 : Nat), FVRel k0 f f) (iha : forall (k0 : Nat), FVRel k0 a a) (k0 : Nat) => FVRel.app k0 f f a a (ihf k0) (iha k0)) ",
                "(fun (ty : KExpr) (b : KExpr) (ihty : forall (k0 : Nat), FVRel k0 ty ty) (ihb : forall (k0 : Nat), FVRel k0 b b) (k0 : Nat) => FVRel.lam k0 ty ty b b (ihty k0) (ihb (Nat.succ k0))) ",
                "(fun (ty : KExpr) (b : KExpr) (ihty : forall (k0 : Nat), FVRel k0 ty ty) (ihb : forall (k0 : Nat), FVRel k0 b b) (k0 : Nat) => FVRel.pi k0 ty ty b b (ihty k0) (ihb (Nat.succ k0))) ",
                "(fun (n : Name) (us : ListType Level) (k0 : Nat) => FVRel.const k0 n us) ",
                "(fun (lty : KExpr) (lv : KExpr) (lb : KExpr) (ihty : forall (k0 : Nat), FVRel k0 lty lty) (ihv : forall (k0 : Nat), FVRel k0 lv lv) (ihb : forall (k0 : Nat), FVRel k0 lb lb) (k0 : Nat) => FVRel.let_ k0 lty lty lv lv lb lb (ihty k0) (ihv k0) (ihb (Nat.succ k0))) ",
                "(fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : forall (k0 : Nat), FVRel k0 sub sub) (k0 : Nat) => FVRel.proj k0 s i sub sub (ihsub k0)) ",
                "(fun (v : Nat) (k0 : Nat) => FVRel.lit k0 v) ",
                "e k",
            ).to_string()),
            is_axiom: false,
            description: "FVRel is reflexive: FVRel k e e. Guide's fvRel_refl (line 1335). DerivedProved via KExpr.rec on e (k-universalized motive); bvar decides i<k (bvar_bound) vs k<=i (bvar_free) via nat_lt_le_dichotomy. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(), "FVRel".to_string(),
                "NatLtLeDichotomy".to_string(), "nat_lt_le_dichotomy".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRel_mono (A2): decreasing the bound threshold weakens FVRel (guide
        // fvRel_mono, line 1366): Le k2 k -> FVRel k e e2 -> FVRel k2 e e2.
        // FVRel.rec with a (k2, Le)-universalized motive; bvar_bound re-derives
        // reflexivity at k2 via the dichotomy, bvar_free/lam/pi weaken the
        // bound via le_trans / le_succ_succ.
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_mono".to_string(),
            type_src: "forall (k : Nat) (k2 : Nat) (e : KExpr) (e2 : KExpr), Le k2 k -> FVRel k e e2 -> FVRel k2 e e2".to_string(),
            value_src: Some(concat!(
                "fun (k : Nat) (k2 : Nat) (e : KExpr) (e2 : KExpr) (hle0 : Le k2 k) (h : FVRel k e e2) => ",
                "FVRel.rec ",
                "(fun (k0 : Nat) (a : KExpr) (b : KExpr) (_hh : FVRel k0 a b) => forall (kp : Nat), Le kp k0 -> FVRel kp a b) ",
                "(fun (k0 : Nat) (i : Nat) (_hlt : Lt i k0) => fun (kp : Nat) (_hkp : Le kp k0) => NatLtLeDichotomy.rec i kp (fun (_d : NatLtLeDichotomy i kp) => FVRel kp (KExpr.bvar i) (KExpr.bvar i)) (fun (h1 : Lt i kp) => FVRel.bvar_bound kp i h1) (fun (h2 : Le kp i) => FVRel.bvar_free kp i i h2 h2) (nat_lt_le_dichotomy i kp)) ",
                "(fun (k0 : Nat) (i : Nat) (j : Nat) (hi : Le k0 i) (hj : Le k0 j) => fun (kp : Nat) (hkp : Le kp k0) => FVRel.bvar_free kp i j (le_trans kp k0 i hkp hi) (le_trans kp k0 j hkp hj)) ",
                "(fun (k0 : Nat) (n : Level) => fun (kp : Nat) (_hkp : Le kp k0) => FVRel.sort kp n) ",
                "(fun (k0 : Nat) (n : Name) (us : ListType Level) => fun (kp : Nat) (_hkp : Le kp k0) => FVRel.const kp n us) ",
                "(fun (k0 : Nat) (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (_hf : FVRel k0 f f2) (_ha : FVRel k0 a a2) (ihf : forall (kp : Nat), Le kp k0 -> FVRel kp f f2) (iha : forall (kp : Nat), Le kp k0 -> FVRel kp a a2) => fun (kp : Nat) (hkp : Le kp k0) => FVRel.app kp f f2 a a2 (ihf kp hkp) (iha kp hkp)) ",
                "(fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (_hA : FVRel k0 A A2) (_hb : FVRel (Nat.succ k0) b b2) (ihA : forall (kp : Nat), Le kp k0 -> FVRel kp A A2) (ihb : forall (kp : Nat), Le kp (Nat.succ k0) -> FVRel kp b b2) => fun (kp : Nat) (hkp : Le kp k0) => FVRel.lam kp A A2 b b2 (ihA kp hkp) (ihb (Nat.succ kp) (le_succ_succ kp k0 hkp))) ",
                "(fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr) (_hA : FVRel k0 A A2) (_hB : FVRel (Nat.succ k0) B B2) (ihA : forall (kp : Nat), Le kp k0 -> FVRel kp A A2) (ihB : forall (kp : Nat), Le kp (Nat.succ k0) -> FVRel kp B B2) => fun (kp : Nat) (hkp : Le kp k0) => FVRel.pi kp A A2 B B2 (ihA kp hkp) (ihB (Nat.succ kp) (le_succ_succ kp k0 hkp))) ",
                "(fun (k0 : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (_hty : FVRel k0 lty lty2) (_hv : FVRel k0 lv lv2) (_hb : FVRel (Nat.succ k0) lb lb2) (ihty : forall (kp : Nat), Le kp k0 -> FVRel kp lty lty2) (ihv : forall (kp : Nat), Le kp k0 -> FVRel kp lv lv2) (ihb : forall (kp : Nat), Le kp (Nat.succ k0) -> FVRel kp lb lb2) => fun (kp : Nat) (hkp : Le kp k0) => FVRel.let_ kp lty lty2 lv lv2 lb lb2 (ihty kp hkp) (ihv kp hkp) (ihb (Nat.succ kp) (le_succ_succ kp k0 hkp))) ",
                "(fun (k0 : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (_hsub : FVRel k0 sub sub2) (ihsub : forall (kp : Nat), Le kp k0 -> FVRel kp sub sub2) => fun (kp : Nat) (hkp : Le kp k0) => FVRel.proj kp s i sub sub2 (ihsub kp hkp)) ",
                "(fun (k0 : Nat) (v : Nat) => fun (kp : Nat) (_hkp : Le kp k0) => FVRel.lit kp v) ",
                "k e e2 h k2 hle0",
            ).to_string()),
            is_axiom: false,
            description: "Decreasing the bound threshold weakens FVRel: Le k2 k -> FVRel k e e2 -> FVRel k2 e e2. Guide's fvRel_mono (line 1366). DerivedProved via FVRel.rec ((k2,Le)-universalized motive): bvar_bound re-derives reflexivity at k2 via nat_lt_le_dichotomy, bvar_free/lam/pi weaken via le_trans/le_succ_succ. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(),
                "NatLtLeDichotomy".to_string(), "nat_lt_le_dichotomy".to_string(),
                "le_trans".to_string(), "le_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // FVRelHeadWitness k ys z : the packaged existential
        // `exists z2, list_head ys = some z2 AND FVRel k z z2` (guide
        // fvRelL_head_some, line 1585). clean-verify has no Sigma/Exists, so the
        // existential is a single-constructor witness inductive — the exact
        // DefEqJoinable idiom (commit a96af44b): `mk` binds z2 internally with
        // its list_head equation and the FVRel relation. Type-valued so consumers
        // project z2 into Type-land. ZERO new axioms.
        self.add_inductive(
            concat!(
                "inductive FVRelHeadWitness (k : Nat) (ys : ListType KExpr) (z : KExpr) : Type\n",
                "| mk : forall (z2 : KExpr), Eq (OptionType KExpr) (list_head ys) (OptionType.some KExpr z2) -> FVRel k z z2 -> FVRelHeadWitness k ys z"
            ),
            "FVRelHeadWitness k ys z (Brick 2 batch 5): the packaged existential `exists z2, list_head ys = some z2 and FVRel k z z2` (guide fvRelL_head_some, line 1585), a single-constructor witness inductive standing in for clean-verify's absent Sigma/Exists (the DefEqJoinable idiom, commit a96af44b). mk binds the head witness z2 internally with its list_head equation and the FVRel relation. Kernel generates FVRelHeadWitness.rec. ZERO new axioms (Inductive/Constructor/Recursor, census-neutral).",
        )?;

        // fvRelL_head_some (B6): if xs is FVRelL-related to ys and xs has head z,
        // then ys has a head z2 FVRel-related to z (guide fvRelL_head_some, line
        // 1585). FVRelL.rec (k param): the nil arm is impossible (list_head nil =
        // none contradicts some z) — discharged in Type-land via Eq.substType
        // through an OptionType discriminator (ConstFreeUnit at none, the goal at
        // some); the cons arm reads off the head via option_some_inj + Eq.substType.
        self.add_definition_structural(SpecDefinition {
            name: "fvRelL_head_some".to_string(),
            type_src: "forall (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr) (z : KExpr), FVRelL k xs ys -> Eq (OptionType KExpr) (list_head xs) (OptionType.some KExpr z) -> FVRelHeadWitness k ys z".to_string(),
            value_src: Some(concat!(
                "fun (k : Nat) (xs : ListType KExpr) (ys : ListType KExpr) (z : KExpr) (h : FVRelL k xs ys) => ",
                "FVRelL.rec k ",
                "(fun (p0 : ListType KExpr) (q0 : ListType KExpr) (_hh : FVRelL k p0 q0) => Eq (OptionType KExpr) (list_head p0) (OptionType.some KExpr z) -> FVRelHeadWitness k q0 z) ",
                "(fun (hz : Eq (OptionType KExpr) (list_head (ListType.nil KExpr)) (OptionType.some KExpr z)) => ",
                "Eq.substType (OptionType KExpr) (fun (o : OptionType KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Type) ConstFreeUnit (fun (_ : KExpr) => FVRelHeadWitness k (ListType.nil KExpr) z) o) (OptionType.none KExpr) (OptionType.some KExpr z) hz ConstFreeUnit.triv) ",
                "(fun (x : KExpr) (x2 : KExpr) (l : ListType KExpr) (l2 : ListType KExpr) (hx : FVRel k x x2) (_hl : FVRelL k l l2) (_ihl : Eq (OptionType KExpr) (list_head l) (OptionType.some KExpr z) -> FVRelHeadWitness k l2 z) => ",
                "fun (hz : Eq (OptionType KExpr) (list_head (ListType.cons KExpr x l)) (OptionType.some KExpr z)) => ",
                "FVRelHeadWitness.mk k (ListType.cons KExpr x2 l2) z x2 (Eq.refl (OptionType KExpr) (OptionType.some KExpr x2)) (Eq.substType KExpr (fun (w : KExpr) => FVRel k w x2) x z (option_some_inj KExpr x z hz) hx)) ",
                "xs ys h",
            ).to_string()),
            is_axiom: false,
            description: "FVRelL head reflection: FVRelL k xs ys and list_head xs = some z give a head z2 of ys with FVRel k z z2 (packaged as FVRelHeadWitness). Guide's fvRelL_head_some (line 1585). DerivedProved via FVRelL.rec: nil arm (impossible) discharged in Type via Eq.substType through an OptionType discriminator; cons arm via option_some_inj + Eq.substType. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRelL".to_string(), "FVRelL.rec".to_string(),
                "FVRelHeadWitness".to_string(), "FVRelHeadWitness.mk".to_string(),
                "Eq.substType".to_string(), "option_some_inj".to_string(),
                "OptionType.rec".to_string(), "ConstFreeUnit".to_string(),
                "list_head".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // (The Type-valued opt_bind CPS inverter `opt_bind_some_inv_type` — needed
        // to build the Type-valued bisimulation witnesses from the reduct equation
        // — ALREADY EXISTS in the spec (par_reduces_c.rs); it is reused verbatim
        // below, not re-declared.)

        // DeltaBisimWitness k f e2 : the packaged existential
        // `exists f2, delta_reduces f f2 AND FVRel k e2 f2` (guide fvRel_delta_bisim,
        // line 1599) — the DefEqJoinable witness-inductive idiom. mk binds the
        // reduct f2 with its delta_reduces step and the FVRel relation. ZERO axioms.
        self.add_inductive(
            concat!(
                "inductive DeltaBisimWitness (k : Nat) (f : KExpr) (e2 : KExpr) : Type\n",
                "| mk : forall (f2 : KExpr), delta_reduces f f2 -> FVRel k e2 f2 -> DeltaBisimWitness k f e2"
            ),
            "DeltaBisimWitness k f e2 (Brick 2 batch 5): the packaged existential `exists f2, delta_reduces f f2 and FVRel k e2 f2` (guide fvRel_delta_bisim, line 1599), a single-constructor witness inductive (DefEqJoinable idiom) binding the delta-reduct f2 with its step and the FVRel relation. Kernel generates DeltaBisimWitness.rec. ZERO new axioms.",
        )?;

        // fvRel_delta_bisim (B7): delta-reduction respects FVRel — the fixed
        // definition body is inserted identically into both related terms (guide
        // fvRel_delta_bisim, line 1599). From delta_reduces e e2 extract the
        // delta_step (delta_reduces_to_step), invert the two opt_binds
        // (opt_bind_some_inv_type) to expose (dname, val) with the const-head and
        // defval equations, then rebuild delta_reduct f = some (apply_spine
        // (kapp_args f) val) using the FVRel-preserved const head (fvRel_const_name
        // (fvRel_kapp_fn)), and relate the reducts via fvRelL_apply_spine on the
        // FVRel-related arg spines (fvRel_kapp_args) with the shared body val.
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_delta_bisim".to_string(),
            type_src: "forall (k : Nat) (e : KExpr) (f : KExpr) (e2 : KExpr), FVRel k e f -> delta_reduces e e2 -> DeltaBisimWitness k f e2".to_string(),
            value_src: Some(concat!(
                "fun (k : Nat) (e : KExpr) (f : KExpr) (e2 : KExpr) (hR : FVRel k e f) (hde : delta_reduces e e2) => ",
                "opt_bind_some_inv_type Name KExpr (kexpr_const_name (kapp_fn e)) ",
                "(fun (dname : Name) => opt_bind KExpr KExpr (defval_for (red_def the_red_env) dname) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val))) ",
                "e2 (DeltaBisimWitness k f e2) ",
                "(delta_reduces_to_step e e2 hde) ",
                "(fun (dname : Name) (hcn : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname)) (hrest : Eq (OptionType KExpr) (opt_bind KExpr KExpr (defval_for (red_def the_red_env) dname) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val))) (OptionType.some KExpr e2)) => ",
                "opt_bind_some_inv_type KExpr KExpr (defval_for (red_def the_red_env) dname) ",
                "(fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val)) ",
                "e2 (DeltaBisimWitness k f e2) ",
                "hrest ",
                "(fun (val : KExpr) (hv : Eq (OptionType KExpr) (defval_for (red_def the_red_env) dname) (OptionType.some KExpr val)) (hval : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) val)) (OptionType.some KExpr e2)) => ",
                "DeltaBisimWitness.mk k f e2 (apply_spine (kapp_args f) val) ",
                "(delta_reduces.mk f (apply_spine (kapp_args f) val) ",
                "(Eq.trans (OptionType KExpr) ",
                "(delta_reduct (red_def the_red_env) f) ",
                "(opt_bind KExpr KExpr (defval_for (red_def the_red_env) dname) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2))) ",
                "(OptionType.some KExpr (apply_spine (kapp_args f) val)) ",
                "(Eq.cong (OptionType Name) (OptionType KExpr) (fun (o : OptionType Name) => opt_bind Name KExpr o (fun (dname2 : Name) => opt_bind KExpr KExpr (defval_for (red_def the_red_env) dname2) (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2)))) (kexpr_const_name (kapp_fn f)) (OptionType.some Name dname) ",
                "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname) ",
                "(Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (kexpr_const_name (kapp_fn f)) (fvRel_const_name k (kapp_fn e) (kapp_fn f) (fvRel_kapp_fn k e f hR))) ",
                "hcn)) ",
                "(Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (o : OptionType KExpr) => opt_bind KExpr KExpr o (fun (val2 : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val2))) (defval_for (red_def the_red_env) dname) (OptionType.some KExpr val) hv))) ",
                "(Eq.substType KExpr (fun (w : KExpr) => FVRel k w (apply_spine (kapp_args f) val)) (apply_spine (kapp_args e) val) e2 (option_some_inj KExpr (apply_spine (kapp_args e) val) e2 hval) (fvRelL_apply_spine k (kapp_args e) (kapp_args f) (fvRel_kapp_args k e f hR) val val (fvRel_refl k val)))))",
            ).to_string()),
            is_axiom: false,
            description: "delta-reduction respects FVRel: FVRel k e f and delta_reduces e e2 give a delta-reduct f2 of f with FVRel k e2 f2 (packaged as DeltaBisimWitness). Guide's fvRel_delta_bisim (line 1599). The fixed definition body val is inserted identically into both related terms. DerivedProved via opt_bind_some_inv_type (twice) + const-head/spine FVRel helpers. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DeltaBisimWitness".to_string(), "DeltaBisimWitness.mk".to_string(),
                "delta_reduces".to_string(), "delta_reduces.mk".to_string(),
                "delta_reduces_to_step".to_string(), "opt_bind_some_inv_type".to_string(),
                "delta_reduct".to_string(), "opt_bind".to_string(), "defval_for".to_string(),
                "fvRel_const_name".to_string(), "fvRel_kapp_fn".to_string(),
                "fvRel_kapp_args".to_string(), "fvRelL_apply_spine".to_string(), "fvRel_refl".to_string(),
                "option_some_inj".to_string(), "Eq.cong".to_string(), "Eq.trans".to_string(),
                "Eq.symm".to_string(), "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // §8b'''' FVRel BISIMULATION — BATCH 6 (this port): the iota/beta/union
        // bisimulation arms + FVRel arithmetic + SN transport. Mirrors the
        // landed fvRel_delta_bisim witness-inductive shape. Every decl is
        // value-full (add_inductive / add_definition_structural) — ZERO new
        // kernel axioms, census stays 16.
        // ================================================================

        // IotaBisimWitness k f e2 : the packaged existential
        // `exists f2, iota_reduces f f2 AND FVRel k e2 f2` (guide fvRel_iota_bisim,
        // line 1625) — the DeltaBisimWitness idiom. mk binds the iota-reduct f2
        // with its iota_reduces step and the FVRel relation. ZERO axioms.
        self.add_inductive(
            concat!(
                "inductive IotaBisimWitness (k : Nat) (f : KExpr) (e2 : KExpr) : Type\n",
                "| mk : forall (f2 : KExpr), iota_reduces f f2 -> FVRel k e2 f2 -> IotaBisimWitness k f e2"
            ),
            "IotaBisimWitness k f e2 (Brick 2 batch 6): the packaged existential `exists f2, iota_reduces f f2 and FVRel k e2 f2` (guide fvRel_iota_bisim, line 1625), a single-constructor witness inductive (DeltaBisimWitness idiom) binding the iota-reduct f2 with its step and the FVRel relation. Kernel generates IotaBisimWitness.rec. ZERO new axioms.",
        )?;

        // fvRel_iota_bisim (B8): iota-reduction respects FVRel — the fixed
        // recursor-rule body is inserted identically into both related terms
        // (guide fvRel_iota_bisim, line 1625). Invert the five nested opt_binds
        // (opt_bind_some_inv_type x5), pick f's FVRel-related major' via
        // fvRelL_head_some, rebuild iota_reduct f = some (...) via
        // opt_bind_some_intro x5 (reusing hm/hrule; recname/cname FVRel-preserved),
        // then relate the reducts through the three nested apply_spines
        // (fvRelL_apply_spine), transporting the middle spine length along
        // fvRelL_length (major vs major').
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_iota_bisim".to_string(),
            type_src: "forall (k : Nat) (e : KExpr) (f : KExpr) (e2 : KExpr), FVRel k e f -> iota_reduces e e2 -> IotaBisimWitness k f e2".to_string(),
            value_src: Some(r"fun (k : Nat) (e : KExpr) (f : KExpr) (e2 : KExpr) (hR : FVRel k e f) (hie : iota_reduces e e2) => opt_bind_some_inv_type Name KExpr (kexpr_const_name (kapp_fn e)) (fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for (red_rec the_red_env) recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))))))))) e2 (IotaBisimWitness k f e2) (iota_reduces_to_step e e2 hie) (fun (recname : Name) (hcn : (Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname))) (hrest1 : (Eq (OptionType KExpr) (opt_bind RecMeta KExpr (recmeta_for (red_rec the_red_env) recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))))))))) (OptionType.some KExpr e2))) => (opt_bind_some_inv_type RecMeta KExpr (recmeta_for (red_rec the_red_env) recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))))))) e2 (IotaBisimWitness k f e2) hrest1 (fun (meta : RecMeta) (hm : (Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) recname) (OptionType.some RecMeta meta))) (hrest2 : (Eq (OptionType KExpr) (opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))))))) (OptionType.some KExpr e2))) => (opt_bind_some_inv_type KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))))))) e2 (IotaBisimWitness k f e2) hrest2 (fun (major : KExpr) (hmaj : (Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (OptionType.some KExpr major))) (hrest3 : (Eq (OptionType KExpr) (opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))))))) (OptionType.some KExpr e2))) => (opt_bind_some_inv_type Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))))) e2 (IotaBisimWitness k f e2) hrest3 (fun (cname : Name) (hcm : (Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname))) (hrest4 : (Eq (OptionType KExpr) (opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))))) (OptionType.some KExpr e2))) => (opt_bind_some_inv_type RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))))) e2 (IotaBisimWitness k f e2) hrest4 (fun (rule : RecRule) (hrule : (Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) recname cname) (OptionType.some RecRule rule))) (hfin : (Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))) (OptionType.some KExpr e2))) => FVRelHeadWitness.rec k (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args f)) major (fun (_w : FVRelHeadWitness k (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args f)) major) => IotaBisimWitness k f e2) (fun (major2 : KExpr) (hmaj_f : (Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args f))) (OptionType.some KExpr major2))) (hmajR : FVRel k major major2) => (IotaBisimWitness.mk k f e2 (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) (iota_reduces.mk f (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) (opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn f)) (fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for (red_rec the_red_env) recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args f))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))))))))) recname (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (kexpr_const_name (kapp_fn f)) (fvRel_const_name k (kapp_fn e) (kapp_fn f) (fvRel_kapp_fn k e f hR))) hcn) (opt_bind_some_intro RecMeta KExpr (recmeta_for (red_rec the_red_env) recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args f))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule))))))))) meta (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) hm (opt_bind_some_intro KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args f))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))))))) major2 (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) hmaj_f (opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn major2)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule))))))) cname (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn major2)) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn major)) (kexpr_const_name (kapp_fn major2)) (fvRel_const_name k (kapp_fn major) (kapp_fn major2) (fvRel_kapp_fn k major major2 hmajR))) hcm) (opt_bind_some_intro RecRule KExpr (recrule_for (red_rec the_red_env) recname cname) (fun (rule : RecRule) => (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))))) rule (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) hrule (Eq.refl (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))))))))))) (Eq.substType KExpr (fun (w : KExpr) => FVRel k w (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule))))) (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))) e2 (option_some_inj KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))) e2 hfin) (Eq.substType Nat (fun (n : Nat) => FVRel k (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub n (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)))) (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule))))) (list_length (kapp_args major2)) (list_length (kapp_args major)) (Eq.symm Nat (list_length (kapp_args major)) (list_length (kapp_args major2)) (fvRelL_length k (kapp_args major) (kapp_args major2) (fvRel_kapp_args k major major2 hmajR))) (fvRelL_apply_spine k (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (fvRelL_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) k (kapp_args e) (kapp_args f) (fvRel_kapp_args k e f hR)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule))) (fvRelL_apply_spine k (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major)) (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (fvRelL_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) k (kapp_args major) (kapp_args major2) (fvRel_kapp_args k major major2 hmajR)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)) (fvRelL_apply_spine k (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (fvRelL_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) k (kapp_args e) (kapp_args f) (fvRel_kapp_args k e f hR)) (recrule_rhs rule) (recrule_rhs rule) (fvRel_refl k (recrule_rhs rule))))))))) (fvRelL_head_some k (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e)) (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args f)) major (fvRelL_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) k (kapp_args e) (kapp_args f) (fvRel_kapp_args k e f hR)) hmaj))))))))))".to_string()),
            is_axiom: false,
            description: "iota-reduction respects FVRel: FVRel k e f and iota_reduces e e2 give an iota-reduct f2 of f with FVRel k e2 f2 (packaged as IotaBisimWitness). Guide's fvRel_iota_bisim (line 1625). The fixed recursor-rule body is inserted identically into both related terms; the major spine length is transported along fvRelL_length. DerivedProved via opt_bind_some_inv_type (5x) + opt_bind_some_intro (5x) + FVRelHeadWitness destruct + spine FVRel helpers. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "IotaBisimWitness".to_string(), "IotaBisimWitness.mk".to_string(),
                "iota_reduces".to_string(), "iota_reduces.mk".to_string(),
                "iota_reduces_to_step".to_string(), "opt_bind_some_inv_type".to_string(),
                "opt_bind_some_intro".to_string(), "iota_reduct".to_string(),
                "opt_bind".to_string(), "recmeta_for".to_string(), "recrule_for".to_string(),
                "recrule_rhs".to_string(), "recrule_num_fields".to_string(),
                "recmeta_num_params".to_string(), "recmeta_num_motives".to_string(),
                "recmeta_num_minors".to_string(), "recmeta_num_indices".to_string(),
                "list_head".to_string(), "list_drop".to_string(), "list_take".to_string(),
                "list_length".to_string(), "kapp_args".to_string(), "kapp_fn".to_string(),
                "apply_spine".to_string(), "kexpr_const_name".to_string(),
                "red_rec".to_string(), "the_red_env".to_string(),
                "FVRelHeadWitness".to_string(), "FVRelHeadWitness.rec".to_string(),
                "fvRelL_head_some".to_string(), "fvRelL_drop".to_string(), "fvRelL_take".to_string(),
                "fvRelL_apply_spine".to_string(), "fvRelL_length".to_string(),
                "fvRel_const_name".to_string(), "fvRel_kapp_fn".to_string(),
                "fvRel_kapp_args".to_string(), "fvRel_refl".to_string(),
                "option_some_inj".to_string(), "Eq.cong".to_string(), "Eq.trans".to_string(),
                "Eq.symm".to_string(), "Eq.substType".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- BATCH 6a: FVRel arithmetic bridges (Le/Lt <-> Nat.sub, add-mono) ---

        // le_sub_zero: Le c i -> Nat.sub c i = 0. Le.rec (Prop motive, since Le is
        // subsingleton) generalizing the second index; refl = nat_sub_self, step
        // peels a Nat.pred (Nat.sub recurses on the right arg). Guide's `Nat.sub_eq_zero_of_le`.
        self.add_definition_structural(SpecDefinition {
            name: "le_sub_zero".to_string(),
            type_src: "forall (c : Nat) (i : Nat), Le c i -> Eq Nat (Nat.sub c i) Nat.zero".to_string(),
            value_src: Some(concat!(
                "fun (c : Nat) (i : Nat) (h : Le c i) => ",
                "Le.rec c ",
                "(fun (j : Nat) (_ : Le c j) => Eq Nat (Nat.sub c j) Nat.zero) ",
                "(nat_sub_self c) ",
                "(fun (m : Nat) (_hm : Le c m) (ihm : Eq Nat (Nat.sub c m) Nat.zero) => ",
                "Eq.trans Nat (Nat.sub c (Nat.succ m)) (Nat.pred (Nat.sub c m)) Nat.zero ",
                "(Eq.refl Nat (Nat.pred (Nat.sub c m))) ",
                "(Eq.trans Nat (Nat.pred (Nat.sub c m)) (Nat.pred Nat.zero) Nat.zero ",
                "(Eq.cong Nat Nat Nat.pred (Nat.sub c m) Nat.zero ihm) (Eq.refl Nat Nat.zero))) ",
                "i h",
            ).to_string()),
            is_axiom: false,
            description: "Le c i -> Nat.sub c i = 0. DerivedProved via Le.rec (Prop motive): refl = nat_sub_self, step peels Nat.pred. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(), "Le.rec".to_string(), "nat_sub_self".to_string(),
                "Nat.pred".to_string(), "Nat.sub".to_string(),
                "Eq.cong".to_string(), "Eq.trans".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_sub_succ: Lt i c -> Nat.sub c i = succ (Nat.sub (Nat.sub c i) 1)
        // (Nat.sub c i is in succ-normal form when positive). Lt.rec (Type ok);
        // zero_lt_succ base is Eq.refl (sub (succ m) 0 reduces both sides to succ m),
        // succ_lt_succ transports the ih along nat_sub_succ_succ.
        self.add_definition_structural(SpecDefinition {
            name: "lt_sub_succ".to_string(),
            type_src: "forall (i : Nat) (c : Nat), Lt i c -> Eq Nat (Nat.sub c i) (Nat.succ (Nat.sub (Nat.sub c i) (Nat.succ Nat.zero)))".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (c : Nat) (h : Lt i c) => ",
                "Lt.rec ",
                "(fun (x : Nat) (y : Nat) (_ : Lt x y) => Eq Nat (Nat.sub y x) (Nat.succ (Nat.sub (Nat.sub y x) (Nat.succ Nat.zero)))) ",
                "(fun (m : Nat) => Eq.refl Nat (Nat.succ m)) ",
                "(fun (n : Nat) (m : Nat) (_hnm : Lt n m) (ih : Eq Nat (Nat.sub m n) (Nat.succ (Nat.sub (Nat.sub m n) (Nat.succ Nat.zero)))) => ",
                "Eq.substType Nat (fun (s : Nat) => Eq Nat s (Nat.succ (Nat.sub s (Nat.succ Nat.zero)))) (Nat.sub m n) (Nat.sub (Nat.succ m) (Nat.succ n)) ",
                "(Eq.symm Nat (Nat.sub (Nat.succ m) (Nat.succ n)) (Nat.sub m n) (nat_sub_succ_succ m n)) ih) ",
                "i c h",
            ).to_string()),
            is_axiom: false,
            description: "Lt i c -> Nat.sub c i = succ (Nat.sub (Nat.sub c i) 1). DerivedProved via Lt.rec: zero_lt_succ base = Eq.refl, succ_lt_succ transports ih along nat_sub_succ_succ. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(), "Lt.rec".to_string(), "Nat.sub".to_string(),
                "nat_sub_succ_succ".to_string(),
                "Eq.substType".to_string(), "Eq.symm".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_add_weaken_right: Lt i k -> Lt i (Nat.add k a). Nat.rec on a
        // (add recurses on the right); base is h, succ weakens via lt_succ_weaken.
        self.add_definition_structural(SpecDefinition {
            name: "lt_add_weaken_right".to_string(),
            type_src: "forall (i : Nat) (k : Nat) (a : Nat), Lt i k -> Lt i (Nat.add k a)".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (k : Nat) (a : Nat) (h : Lt i k) => ",
                "Nat.rec (fun (a0 : Nat) => Lt i (Nat.add k a0)) h ",
                "(fun (a1 : Nat) (ih : Lt i (Nat.add k a1)) => lt_succ_weaken i (Nat.add k a1) ih) a",
            ).to_string()),
            is_axiom: false,
            description: "Lt i k -> Lt i (Nat.add k a). DerivedProved via Nat.rec on a; base h, succ via lt_succ_weaken. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "Lt".to_string(), "lt_succ_weaken".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // le_add_right_mono: Le x y -> Le (Nat.add x a) (Nat.add y a). Nat.rec on a;
        // base is h, succ via le_succ_succ.
        self.add_definition_structural(SpecDefinition {
            name: "le_add_right_mono".to_string(),
            type_src: "forall (x : Nat) (y : Nat) (a : Nat), Le x y -> Le (Nat.add x a) (Nat.add y a)".to_string(),
            value_src: Some(concat!(
                "fun (x : Nat) (y : Nat) (a : Nat) (h : Le x y) => ",
                "Nat.rec (fun (a0 : Nat) => Le (Nat.add x a0) (Nat.add y a0)) h ",
                "(fun (a1 : Nat) (ih : Le (Nat.add x a1) (Nat.add y a1)) => le_succ_succ (Nat.add x a1) (Nat.add y a1) ih) a",
            ).to_string()),
            is_axiom: false,
            description: "Le x y -> Le (Nat.add x a) (Nat.add y a). DerivedProved via Nat.rec on a; base h, succ via le_succ_succ. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "Le".to_string(), "le_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRel_lift (A3): lifting preserves FVRel when the cutoff is within the
        // bound region (Le c k): shifting free variables keeps them free (guide
        // fvRel_lift, line 1387). FVRel.rec (c-universalized motive carrying Le c0 k0);
        // bvar arms case on NatLtLeDichotomy i c0 and compute lift via
        // lift_at_bvar_below/geq (le_sub_zero / lt_sub_succ), rebuilding the bvar
        // constructor with the shifted index (lt_add_right_mono / lt_add_weaken_right
        // / le_add_right_mono); lam/pi transport the body threshold add(succ k0)a ->
        // succ(add k0 a) via nat_succ_add.
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_lift".to_string(),
            type_src: "forall (k : Nat) (c : Nat) (a : Nat) (e : KExpr) (e2 : KExpr), Le c k -> FVRel k e e2 -> FVRel (Nat.add k a) (lift_at e c a) (lift_at e2 c a)".to_string(),
            value_src: Some(r"fun (k : Nat) (c : Nat) (a : Nat) (e : KExpr) (e2 : KExpr) (hck : Le c k) (h : FVRel k e e2) => FVRel.rec (fun (k0 : Nat) (x : KExpr) (y : KExpr) (_hh : FVRel k0 x y) => forall (c0 : Nat), Le c0 k0 -> FVRel (Nat.add k0 a) (lift_at x c0 a) (lift_at y c0 a)) (fun (k0 : Nat) (i : Nat) (hlt : Lt i k0) => fun (c0 : Nat) (hc0 : Le c0 k0) => NatLtLeDichotomy.rec i c0 (fun (_d : NatLtLeDichotomy i c0) => FVRel (Nat.add k0 a) (lift_at (KExpr.bvar i) c0 a) (lift_at (KExpr.bvar i) c0 a)) (fun (hic : Lt i c0) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k0 a) w w) (KExpr.bvar i) (lift_at (KExpr.bvar i) c0 a) (Eq.symm KExpr (lift_at (KExpr.bvar i) c0 a) (KExpr.bvar i) (lift_at_bvar_below i c0 a (lt_sub_succ i c0 hic))) (FVRel.bvar_bound (Nat.add k0 a) i (lt_add_weaken_right i k0 a hlt)))) (fun (hci : Le c0 i) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k0 a) w w) (KExpr.bvar (Nat.add i a)) (lift_at (KExpr.bvar i) c0 a) (Eq.symm KExpr (lift_at (KExpr.bvar i) c0 a) (KExpr.bvar (Nat.add i a)) (lift_at_bvar_geq i c0 a (le_sub_zero c0 i hci))) (FVRel.bvar_bound (Nat.add k0 a) (Nat.add i a) (lt_add_right_mono i k0 a hlt)))) (nat_lt_le_dichotomy i c0)) (fun (k0 : Nat) (i : Nat) (j : Nat) (hi : Le k0 i) (hj : Le k0 j) => fun (c0 : Nat) (hc0 : Le c0 k0) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k0 a) w (lift_at (KExpr.bvar j) c0 a)) (KExpr.bvar (Nat.add i a)) (lift_at (KExpr.bvar i) c0 a) (Eq.symm KExpr (lift_at (KExpr.bvar i) c0 a) (KExpr.bvar (Nat.add i a)) (lift_at_bvar_geq i c0 a (le_sub_zero c0 i (le_trans c0 k0 i hc0 hi)))) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k0 a) (KExpr.bvar (Nat.add i a)) w) (KExpr.bvar (Nat.add j a)) (lift_at (KExpr.bvar j) c0 a) (Eq.symm KExpr (lift_at (KExpr.bvar j) c0 a) (KExpr.bvar (Nat.add j a)) (lift_at_bvar_geq j c0 a (le_sub_zero c0 j (le_trans c0 k0 j hc0 hj)))) (FVRel.bvar_free (Nat.add k0 a) (Nat.add i a) (Nat.add j a) (le_add_right_mono k0 i a hi) (le_add_right_mono k0 j a hj))))) (fun (k0 : Nat) (n : Level) => fun (c0 : Nat) (_hc0 : Le c0 k0) => FVRel.sort (Nat.add k0 a) n) (fun (k0 : Nat) (n : Name) (us : ListType Level) => fun (c0 : Nat) (_hc0 : Le c0 k0) => FVRel.const (Nat.add k0 a) n us) (fun (k0 : Nat) (f : KExpr) (f2 : KExpr) (aa : KExpr) (aa2 : KExpr) (hf : FVRel k0 f f2) (ha : FVRel k0 aa aa2) (ihf : forall (c1 : Nat), Le c1 k0 -> FVRel (Nat.add k0 a) (lift_at f c1 a) (lift_at f2 c1 a)) (iha : forall (c1 : Nat), Le c1 k0 -> FVRel (Nat.add k0 a) (lift_at aa c1 a) (lift_at aa2 c1 a)) => fun (c0 : Nat) (hc0 : Le c0 k0) => FVRel.app (Nat.add k0 a) (lift_at f c0 a) (lift_at f2 c0 a) (lift_at aa c0 a) (lift_at aa2 c0 a) (ihf c0 hc0) (iha c0 hc0)) (fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : FVRel k0 A A2) (hb : FVRel (Nat.succ k0) b b2) (ihA : forall (c1 : Nat), Le c1 k0 -> FVRel (Nat.add k0 a) (lift_at A c1 a) (lift_at A2 c1 a)) (ihb : forall (c1 : Nat), Le c1 (Nat.succ k0) -> FVRel (Nat.add (Nat.succ k0) a) (lift_at b c1 a) (lift_at b2 c1 a)) => fun (c0 : Nat) (hc0 : Le c0 k0) => FVRel.lam (Nat.add k0 a) (lift_at A c0 a) (lift_at A2 c0 a) (lift_at b (Nat.succ c0) a) (lift_at b2 (Nat.succ c0) a) (ihA c0 hc0) (Eq.substType Nat (fun (t : Nat) => FVRel t (lift_at b (Nat.succ c0) a) (lift_at b2 (Nat.succ c0) a)) (Nat.add (Nat.succ k0) a) (Nat.succ (Nat.add k0 a)) (nat_succ_add k0 a) (ihb (Nat.succ c0) (le_succ_succ c0 k0 hc0)))) (fun (k0 : Nat) (A : KExpr) (A2 : KExpr) (B : KExpr) (B2 : KExpr) (hA : FVRel k0 A A2) (hB : FVRel (Nat.succ k0) B B2) (ihA : forall (c1 : Nat), Le c1 k0 -> FVRel (Nat.add k0 a) (lift_at A c1 a) (lift_at A2 c1 a)) (ihB : forall (c1 : Nat), Le c1 (Nat.succ k0) -> FVRel (Nat.add (Nat.succ k0) a) (lift_at B c1 a) (lift_at B2 c1 a)) => fun (c0 : Nat) (hc0 : Le c0 k0) => FVRel.pi (Nat.add k0 a) (lift_at A c0 a) (lift_at A2 c0 a) (lift_at B (Nat.succ c0) a) (lift_at B2 (Nat.succ c0) a) (ihA c0 hc0) (Eq.substType Nat (fun (t : Nat) => FVRel t (lift_at B (Nat.succ c0) a) (lift_at B2 (Nat.succ c0) a)) (Nat.add (Nat.succ k0) a) (Nat.succ (Nat.add k0 a)) (nat_succ_add k0 a) (ihB (Nat.succ c0) (le_succ_succ c0 k0 hc0)))) (fun (k0 : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (hty : FVRel k0 lty lty2) (hv : FVRel k0 lv lv2) (hb : FVRel (Nat.succ k0) lb lb2) (ihty : forall (c1 : Nat), Le c1 k0 -> FVRel (Nat.add k0 a) (lift_at lty c1 a) (lift_at lty2 c1 a)) (ihv : forall (c1 : Nat), Le c1 k0 -> FVRel (Nat.add k0 a) (lift_at lv c1 a) (lift_at lv2 c1 a)) (ihb : forall (c1 : Nat), Le c1 (Nat.succ k0) -> FVRel (Nat.add (Nat.succ k0) a) (lift_at lb c1 a) (lift_at lb2 c1 a)) => fun (c0 : Nat) (hc0 : Le c0 k0) => FVRel.let_ (Nat.add k0 a) (lift_at lty c0 a) (lift_at lty2 c0 a) (lift_at lv c0 a) (lift_at lv2 c0 a) (lift_at lb (Nat.succ c0) a) (lift_at lb2 (Nat.succ c0) a) (ihty c0 hc0) (ihv c0 hc0) (Eq.substType Nat (fun (t : Nat) => FVRel t (lift_at lb (Nat.succ c0) a) (lift_at lb2 (Nat.succ c0) a)) (Nat.add (Nat.succ k0) a) (Nat.succ (Nat.add k0 a)) (nat_succ_add k0 a) (ihb (Nat.succ c0) (le_succ_succ c0 k0 hc0)))) (fun (k0 : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : FVRel k0 sub sub2) (ihsub : forall (c1 : Nat), Le c1 k0 -> FVRel (Nat.add k0 a) (lift_at sub c1 a) (lift_at sub2 c1 a)) => fun (c0 : Nat) (hc0 : Le c0 k0) => FVRel.proj (Nat.add k0 a) s i (lift_at sub c0 a) (lift_at sub2 c0 a) (ihsub c0 hc0)) (fun (k0 : Nat) (v : Nat) => fun (c0 : Nat) (_hc0 : Le c0 k0) => FVRel.lit (Nat.add k0 a) v) k e e2 h c hck".to_string()),
            is_axiom: false,
            description: "Lifting preserves FVRel when the cutoff is bound (Le c k): FVRel (k+a) (lift_at e c a) (lift_at e2 c a). Guide's fvRel_lift (line 1387). DerivedProved via FVRel.rec (c-universalized motive); bvar arms case on nat_lt_le_dichotomy computing lift via lift_at_bvar_below/geq (le_sub_zero/lt_sub_succ) + add-mono; lam/pi transport the threshold via nat_succ_add. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(), "lift_at".to_string(),
                "NatLtLeDichotomy".to_string(), "NatLtLeDichotomy.rec".to_string(),
                "nat_lt_le_dichotomy".to_string(),
                "lift_at_bvar_below".to_string(), "lift_at_bvar_geq".to_string(),
                "le_sub_zero".to_string(), "lt_sub_succ".to_string(),
                "lt_add_right_mono".to_string(), "lt_add_weaken_right".to_string(),
                "le_add_right_mono".to_string(), "le_trans".to_string(),
                "le_succ_succ".to_string(), "nat_succ_add".to_string(),
                "Eq.substType".to_string(), "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- BATCH 6b: Nat trichotomy + Lt->Le bridges + fvRel_instantiate_bvar0 ---

        // NatTrichotomy i d : the total 3-way ordering decision Lt i d (+) Eq i d (+)
        // Lt d i, a Type-valued witness inductive (clean-verify has no Or/Sum). The
        // instantiate arithmetic lemmas case on i<d / i=d / i>d; this packages that.
        self.add_inductive(
            concat!(
                "inductive NatTrichotomy : Nat -> Nat -> Type\n",
                "| lt : forall (i : Nat) (d : Nat), Lt i d -> NatTrichotomy i d\n",
                "| eq : forall (i : Nat) (d : Nat), Eq Nat i d -> NatTrichotomy i d\n",
                "| gt : forall (i : Nat) (d : Nat), Lt d i -> NatTrichotomy i d"
            ),
            "NatTrichotomy i d (Brick 2 batch 6b): the total 3-way ordering Lt i d (+) Eq i d (+) Lt d i, packaged as a 3-constructor witness inductive (clean-verify has no Or/Sum). Type-valued (eliminates into Type-valued FVRel). Kernel generates NatTrichotomy.rec. ZERO new axioms (Inductive/Constructor/Recursor, census-neutral).",
        )?;

        // nat_trichotomy : forall i d, NatTrichotomy i d. Double Nat.rec (mirrors the
        // landed nat_lt_le_dichotomy): base rows via zero_lt_succ/eq, succ/succ lifts
        // the sub-decision through NatTrichotomy.rec + Lt.succ_lt_succ / Eq.cong succ.
        self.add_definition_structural(SpecDefinition {
            name: "nat_trichotomy".to_string(),
            type_src: "forall (i : Nat) (d : Nat), NatTrichotomy i d".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) => Nat.rec (fun (i0 : Nat) => forall (d : Nat), NatTrichotomy i0 d) ",
                "(fun (d : Nat) => Nat.rec (fun (d0 : Nat) => NatTrichotomy Nat.zero d0) ",
                "(NatTrichotomy.eq Nat.zero Nat.zero (Eq.refl Nat Nat.zero)) ",
                "(fun (d2 : Nat) (_ : NatTrichotomy Nat.zero d2) => NatTrichotomy.lt Nat.zero (Nat.succ d2) (Lt.zero_lt_succ d2)) ",
                "d) ",
                "(fun (i2 : Nat) (ih : forall (d : Nat), NatTrichotomy i2 d) => ",
                "fun (d : Nat) => Nat.rec (fun (d0 : Nat) => NatTrichotomy (Nat.succ i2) d0) ",
                "(NatTrichotomy.gt (Nat.succ i2) Nat.zero (Lt.zero_lt_succ i2)) ",
                "(fun (d2 : Nat) (_ : NatTrichotomy (Nat.succ i2) d2) => ",
                "NatTrichotomy.rec i2 d2 (fun (_dd : NatTrichotomy i2 d2) => NatTrichotomy (Nat.succ i2) (Nat.succ d2)) ",
                "(fun (hlt : Lt i2 d2) => NatTrichotomy.lt (Nat.succ i2) (Nat.succ d2) (Lt.succ_lt_succ i2 d2 hlt)) ",
                "(fun (heq : Eq Nat i2 d2) => NatTrichotomy.eq (Nat.succ i2) (Nat.succ d2) (Eq.cong Nat Nat Nat.succ i2 d2 heq)) ",
                "(fun (hgt : Lt d2 i2) => NatTrichotomy.gt (Nat.succ i2) (Nat.succ d2) (Lt.succ_lt_succ d2 i2 hgt)) ",
                "(ih d2)) ",
                "d) ",
                "i",
            ).to_string()),
            is_axiom: false,
            description: "Total 3-way Nat ordering: forall i d, Lt i d (+) Eq i d (+) Lt d i (as NatTrichotomy). DerivedProved by double Nat.rec (mirrors nat_lt_le_dichotomy). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "NatTrichotomy".to_string(), "Nat.rec".to_string(),
                "Lt.zero_lt_succ".to_string(), "Lt.succ_lt_succ".to_string(),
                "Eq.refl".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_implies_le: Lt a b -> Le a b. Lt.rec; zero_lt_succ = le_zero_n,
        // succ_lt_succ = le_succ_succ on the ih.
        self.add_definition_structural(SpecDefinition {
            name: "lt_implies_le".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Lt a b -> Le a b".to_string(),
            value_src: Some(concat!(
                "fun (a : Nat) (b : Nat) (h : Lt a b) => ",
                "Lt.rec (fun (x : Nat) (y : Nat) (_ : Lt x y) => Le x y) ",
                "(fun (n : Nat) => le_zero_n (Nat.succ n)) ",
                "(fun (n : Nat) (m : Nat) (_hnm : Lt n m) (ih : Le n m) => le_succ_succ n m ih) ",
                "a b h",
            ).to_string()),
            is_axiom: false,
            description: "Lt a b -> Le a b. DerivedProved via Lt.rec (zero_lt_succ = le_zero_n, succ = le_succ_succ). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(), "Lt.rec".to_string(), "Le".to_string(),
                "le_zero_n".to_string(), "le_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_to_le_succ: Lt a b -> Le (succ a) b. Lt.rec; zero_lt_succ =
        // le_succ_succ 0 n (le_zero_n n), succ_lt_succ = le_succ_succ (succ n) m ih.
        self.add_definition_structural(SpecDefinition {
            name: "lt_to_le_succ".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Lt a b -> Le (Nat.succ a) b".to_string(),
            value_src: Some(concat!(
                "fun (a : Nat) (b : Nat) (h : Lt a b) => ",
                "Lt.rec (fun (x : Nat) (y : Nat) (_ : Lt x y) => Le (Nat.succ x) y) ",
                "(fun (n : Nat) => le_succ_succ Nat.zero n (le_zero_n n)) ",
                "(fun (n : Nat) (m : Nat) (_hnm : Lt n m) (ih : Le (Nat.succ n) m) => le_succ_succ (Nat.succ n) m ih) ",
                "a b h",
            ).to_string()),
            is_axiom: false,
            description: "Lt a b -> Le (succ a) b. DerivedProved via Lt.rec (zero_lt_succ = le_succ_succ 0 n (le_zero_n n), succ = le_succ_succ). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(), "Lt.rec".to_string(), "Le".to_string(),
                "le_zero_n".to_string(), "le_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRel_instantiate_bvar0 (A4): a term is FVRel-related to its bvar-0
        // instantiation (a free-variable renaming) — instantiate_at fixes bound
        // variables and moves free ones (guide fvRel_instantiate_bvar0, line 1420).
        // KExpr.rec on C (k-universalized motive); the bvar arm cases on
        // NatTrichotomy i k0 (i<k0 = bvar_bound below; i=k0 = free rename to bvar(0+k0)
        // via instantiate_bvar_at_eq + lift_at_bvar_geq; i>k0 = bvar_free to bvar(i-1)
        // via instantiate_bvar_at_above + le_succ_le_pred); structural arms transport
        // via instantiate_at_{sort,app,lam,pi,const}.
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_instantiate_bvar0".to_string(),
            type_src: "forall (k : Nat) (C : KExpr), FVRel k C (instantiate_at C (KExpr.bvar Nat.zero) k)".to_string(),
            value_src: Some(r"fun (k : Nat) (C : KExpr) => KExpr.rec (fun (C0 : KExpr) => forall (k0 : Nat), FVRel k0 C0 (instantiate_at C0 (KExpr.bvar Nat.zero) k0)) (fun (n : Level) (k0 : Nat) => (Eq.substType KExpr (fun (w : KExpr) => FVRel k0 (KExpr.sort n) w) (KExpr.sort n) (instantiate_at (KExpr.sort n) (KExpr.bvar Nat.zero) k0) (Eq.symm KExpr (instantiate_at (KExpr.sort n) (KExpr.bvar Nat.zero) k0) (KExpr.sort n) (instantiate_at_sort n (KExpr.bvar Nat.zero) k0)) (FVRel.sort k0 n))) (fun (i : Nat) (k0 : Nat) => NatTrichotomy.rec i k0 (fun (_t : NatTrichotomy i k0) => FVRel k0 (KExpr.bvar i) (instantiate_at (KExpr.bvar i) (KExpr.bvar Nat.zero) k0)) (fun (hlt : Lt i k0) => (Eq.substType KExpr (fun (w : KExpr) => FVRel k0 (KExpr.bvar i) w) (KExpr.bvar i) (instantiate_at (KExpr.bvar i) (KExpr.bvar Nat.zero) k0) (Eq.symm KExpr (instantiate_at (KExpr.bvar i) (KExpr.bvar Nat.zero) k0) (KExpr.bvar i) (Eq.trans KExpr (instantiate_at (KExpr.bvar i) (KExpr.bvar Nat.zero) k0) (instantiate_bvar_at i k0 (KExpr.bvar Nat.zero)) (KExpr.bvar i) (instantiate_at_bvar i (KExpr.bvar Nat.zero) k0) (instantiate_bvar_at_below i k0 (KExpr.bvar Nat.zero) (lt_sub_succ i k0 hlt)))) (FVRel.bvar_bound k0 i hlt))) (fun (heq : Eq Nat i k0) => (Eq.substType Nat (fun (z : Nat) => FVRel k0 (KExpr.bvar z) (instantiate_at (KExpr.bvar z) (KExpr.bvar Nat.zero) k0)) k0 i (Eq.symm Nat i k0 heq) (Eq.substType KExpr (fun (w : KExpr) => FVRel k0 (KExpr.bvar k0) w) (KExpr.bvar (Nat.add Nat.zero k0)) (instantiate_at (KExpr.bvar k0) (KExpr.bvar Nat.zero) k0) (Eq.symm KExpr (instantiate_at (KExpr.bvar k0) (KExpr.bvar Nat.zero) k0) (KExpr.bvar (Nat.add Nat.zero k0)) (Eq.trans KExpr (instantiate_at (KExpr.bvar k0) (KExpr.bvar Nat.zero) k0) (instantiate_bvar_at k0 k0 (KExpr.bvar Nat.zero)) (KExpr.bvar (Nat.add Nat.zero k0)) (instantiate_at_bvar k0 (KExpr.bvar Nat.zero) k0) (Eq.trans KExpr (instantiate_bvar_at k0 k0 (KExpr.bvar Nat.zero)) (lift_at (KExpr.bvar Nat.zero) Nat.zero k0) (KExpr.bvar (Nat.add Nat.zero k0)) (instantiate_bvar_at_eq k0 (KExpr.bvar Nat.zero)) (lift_at_bvar_geq Nat.zero Nat.zero k0 (nat_sub_self Nat.zero))))) (FVRel.bvar_free k0 k0 (Nat.add Nat.zero k0) (Le.refl k0) (le_add_self_right Nat.zero k0))))) (fun (hgt : Lt k0 i) => (Eq.substType KExpr (fun (w : KExpr) => FVRel k0 (KExpr.bvar i) w) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (instantiate_at (KExpr.bvar i) (KExpr.bvar Nat.zero) k0) (Eq.symm KExpr (instantiate_at (KExpr.bvar i) (KExpr.bvar Nat.zero) k0) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Eq.trans KExpr (instantiate_at (KExpr.bvar i) (KExpr.bvar Nat.zero) k0) (instantiate_bvar_at i k0 (KExpr.bvar Nat.zero)) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (instantiate_at_bvar i (KExpr.bvar Nat.zero) k0) (instantiate_bvar_at_above i k0 (KExpr.bvar Nat.zero) (le_sub_zero k0 i (lt_implies_le k0 i hgt)) (lt_sub_succ k0 i hgt)))) (FVRel.bvar_free k0 i (Nat.sub i (Nat.succ Nat.zero)) (lt_implies_le k0 i hgt) (le_succ_le_pred k0 i (lt_to_le_succ k0 i hgt))))) (nat_trichotomy i k0)) (fun (f : KExpr) (aa : KExpr) (ihf : forall (k0 : Nat), FVRel k0 f (instantiate_at f (KExpr.bvar Nat.zero) k0)) (iha : forall (k0 : Nat), FVRel k0 aa (instantiate_at aa (KExpr.bvar Nat.zero) k0)) (k0 : Nat) => (Eq.substType KExpr (fun (w : KExpr) => FVRel k0 (KExpr.app f aa) w) (KExpr.app (instantiate_at f (KExpr.bvar Nat.zero) k0) (instantiate_at aa (KExpr.bvar Nat.zero) k0)) (instantiate_at (KExpr.app f aa) (KExpr.bvar Nat.zero) k0) (Eq.symm KExpr (instantiate_at (KExpr.app f aa) (KExpr.bvar Nat.zero) k0) (KExpr.app (instantiate_at f (KExpr.bvar Nat.zero) k0) (instantiate_at aa (KExpr.bvar Nat.zero) k0)) (instantiate_at_app f aa (KExpr.bvar Nat.zero) k0)) (FVRel.app k0 f (instantiate_at f (KExpr.bvar Nat.zero) k0) aa (instantiate_at aa (KExpr.bvar Nat.zero) k0) (ihf k0) (iha k0)))) (fun (ty : KExpr) (b : KExpr) (ihty : forall (k0 : Nat), FVRel k0 ty (instantiate_at ty (KExpr.bvar Nat.zero) k0)) (ihb : forall (k0 : Nat), FVRel k0 b (instantiate_at b (KExpr.bvar Nat.zero) k0)) (k0 : Nat) => (Eq.substType KExpr (fun (w : KExpr) => FVRel k0 (KExpr.lam ty b) w) (KExpr.lam (instantiate_at ty (KExpr.bvar Nat.zero) k0) (instantiate_at b (KExpr.bvar Nat.zero) (Nat.succ k0))) (instantiate_at (KExpr.lam ty b) (KExpr.bvar Nat.zero) k0) (Eq.symm KExpr (instantiate_at (KExpr.lam ty b) (KExpr.bvar Nat.zero) k0) (KExpr.lam (instantiate_at ty (KExpr.bvar Nat.zero) k0) (instantiate_at b (KExpr.bvar Nat.zero) (Nat.succ k0))) (instantiate_at_lam ty b (KExpr.bvar Nat.zero) k0)) (FVRel.lam k0 ty (instantiate_at ty (KExpr.bvar Nat.zero) k0) b (instantiate_at b (KExpr.bvar Nat.zero) (Nat.succ k0)) (ihty k0) (ihb (Nat.succ k0))))) (fun (ty : KExpr) (b : KExpr) (ihty : forall (k0 : Nat), FVRel k0 ty (instantiate_at ty (KExpr.bvar Nat.zero) k0)) (ihb : forall (k0 : Nat), FVRel k0 b (instantiate_at b (KExpr.bvar Nat.zero) k0)) (k0 : Nat) => (Eq.substType KExpr (fun (w : KExpr) => FVRel k0 (KExpr.pi ty b) w) (KExpr.pi (instantiate_at ty (KExpr.bvar Nat.zero) k0) (instantiate_at b (KExpr.bvar Nat.zero) (Nat.succ k0))) (instantiate_at (KExpr.pi ty b) (KExpr.bvar Nat.zero) k0) (Eq.symm KExpr (instantiate_at (KExpr.pi ty b) (KExpr.bvar Nat.zero) k0) (KExpr.pi (instantiate_at ty (KExpr.bvar Nat.zero) k0) (instantiate_at b (KExpr.bvar Nat.zero) (Nat.succ k0))) (instantiate_at_pi ty b (KExpr.bvar Nat.zero) k0)) (FVRel.pi k0 ty (instantiate_at ty (KExpr.bvar Nat.zero) k0) b (instantiate_at b (KExpr.bvar Nat.zero) (Nat.succ k0)) (ihty k0) (ihb (Nat.succ k0))))) (fun (n : Name) (us : ListType Level) (k0 : Nat) => (Eq.substType KExpr (fun (w : KExpr) => FVRel k0 (KExpr.const n us) w) (KExpr.const n us) (instantiate_at (KExpr.const n us) (KExpr.bvar Nat.zero) k0) (Eq.symm KExpr (instantiate_at (KExpr.const n us) (KExpr.bvar Nat.zero) k0) (KExpr.const n us) (instantiate_at_const n us (KExpr.bvar Nat.zero) k0)) (FVRel.const k0 n us))) (fun (lty : KExpr) (lv : KExpr) (lb : KExpr) (ihty : forall (k0 : Nat), FVRel k0 lty (instantiate_at lty (KExpr.bvar Nat.zero) k0)) (ihv : forall (k0 : Nat), FVRel k0 lv (instantiate_at lv (KExpr.bvar Nat.zero) k0)) (ihb : forall (k0 : Nat), FVRel k0 lb (instantiate_at lb (KExpr.bvar Nat.zero) k0)) (k0 : Nat) => (Eq.substType KExpr (fun (w : KExpr) => FVRel k0 (KExpr.let_ lty lv lb) w) (KExpr.let_ (instantiate_at lty (KExpr.bvar Nat.zero) k0) (instantiate_at lv (KExpr.bvar Nat.zero) k0) (instantiate_at lb (KExpr.bvar Nat.zero) (Nat.succ k0))) (instantiate_at (KExpr.let_ lty lv lb) (KExpr.bvar Nat.zero) k0) (Eq.symm KExpr (instantiate_at (KExpr.let_ lty lv lb) (KExpr.bvar Nat.zero) k0) (KExpr.let_ (instantiate_at lty (KExpr.bvar Nat.zero) k0) (instantiate_at lv (KExpr.bvar Nat.zero) k0) (instantiate_at lb (KExpr.bvar Nat.zero) (Nat.succ k0))) (instantiate_at_let_ lty lv lb (KExpr.bvar Nat.zero) k0)) (FVRel.let_ k0 lty (instantiate_at lty (KExpr.bvar Nat.zero) k0) lv (instantiate_at lv (KExpr.bvar Nat.zero) k0) lb (instantiate_at lb (KExpr.bvar Nat.zero) (Nat.succ k0)) (ihty k0) (ihv k0) (ihb (Nat.succ k0))))) (fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : forall (k0 : Nat), FVRel k0 sub (instantiate_at sub (KExpr.bvar Nat.zero) k0)) (k0 : Nat) => (Eq.substType KExpr (fun (w : KExpr) => FVRel k0 (KExpr.proj s i sub) w) (KExpr.proj s i (instantiate_at sub (KExpr.bvar Nat.zero) k0)) (instantiate_at (KExpr.proj s i sub) (KExpr.bvar Nat.zero) k0) (Eq.symm KExpr (instantiate_at (KExpr.proj s i sub) (KExpr.bvar Nat.zero) k0) (KExpr.proj s i (instantiate_at sub (KExpr.bvar Nat.zero) k0)) (instantiate_at_proj s i sub (KExpr.bvar Nat.zero) k0)) (FVRel.proj k0 s i sub (instantiate_at sub (KExpr.bvar Nat.zero) k0) (ihsub k0)))) (fun (v : Nat) (k0 : Nat) => (Eq.substType KExpr (fun (w : KExpr) => FVRel k0 (KExpr.lit v) w) (KExpr.lit v) (instantiate_at (KExpr.lit v) (KExpr.bvar Nat.zero) k0) (Eq.symm KExpr (instantiate_at (KExpr.lit v) (KExpr.bvar Nat.zero) k0) (KExpr.lit v) (instantiate_at_lit v (KExpr.bvar Nat.zero) k0)) (FVRel.lit k0 v))) C k".to_string()),
            is_axiom: false,
            description: "A term is FVRel-related to its bvar-0 instantiation (a free-variable renaming): FVRel k C (instantiate_at C (bvar 0) k). Guide's fvRel_instantiate_bvar0 (line 1420). DerivedProved via KExpr.rec; bvar arm cases on nat_trichotomy (below/rename/above via instantiate_bvar_at_{below,eq,above} + lift_at_bvar_geq + le_succ_le_pred); structural arms transport via instantiate_at_{sort,app,lam,pi,const}. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(), "FVRel".to_string(), "instantiate_at".to_string(),
                "NatTrichotomy".to_string(), "NatTrichotomy.rec".to_string(), "nat_trichotomy".to_string(),
                "instantiate_at_bvar".to_string(), "instantiate_at_sort".to_string(),
                "instantiate_at_app".to_string(), "instantiate_at_lam".to_string(),
                "instantiate_at_pi".to_string(), "instantiate_at_const".to_string(), "instantiate_at_let_".to_string(),
                "instantiate_at_proj".to_string(), "instantiate_at_lit".to_string(),
                "instantiate_bvar_at_below".to_string(), "instantiate_bvar_at_above".to_string(),
                "instantiate_bvar_at_eq".to_string(), "lift_at_bvar_geq".to_string(),
                "lt_sub_succ".to_string(), "le_sub_zero".to_string(), "nat_sub_self".to_string(),
                "lt_implies_le".to_string(), "lt_to_le_succ".to_string(), "le_succ_le_pred".to_string(),
                "le_add_self_right".to_string(), "Le.refl".to_string(),
                "Eq.substType".to_string(), "Eq.symm".to_string(), "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- BATCH 6c: lt_of_lt_of_le + lt_succ_to_le + fvRel_instantiate_at ---

        // lt_of_lt_of_le: Lt a b -> Le b c -> Lt a c. Recurse on the Lt (Type) so
        // the conclusion stays Type-valued (Le is Prop, cannot eliminate to Type);
        // the base cases decide c via Nat.rec using le_succ_zero_empty (c=0 absurd)
        // and le_pred_pred (succ/succ peel).
        self.add_definition_structural(SpecDefinition {
            name: "lt_of_lt_of_le".to_string(),
            type_src: "forall (a : Nat) (b : Nat) (c : Nat), Lt a b -> Le b c -> Lt a c".to_string(),
            value_src: Some(concat!(
                "fun (a : Nat) (b : Nat) (c : Nat) (hab : Lt a b) => ",
                "Lt.rec (fun (x : Nat) (y : Nat) (_ : Lt x y) => forall (z : Nat), Le y z -> Lt x z) ",
                "(fun (n : Nat) => fun (z : Nat) (hbz : Le (Nat.succ n) z) => ",
                "Nat.rec (fun (z0 : Nat) => Le (Nat.succ n) z0 -> Lt Nat.zero z0) ",
                "(fun (h0 : Le (Nat.succ n) Nat.zero) => Empty.rec (fun (_ : Empty) => Lt Nat.zero Nat.zero) (le_succ_zero_empty n h0)) ",
                "(fun (z2 : Nat) (_ih : Le (Nat.succ n) z2 -> Lt Nat.zero z2) (_hz : Le (Nat.succ n) (Nat.succ z2)) => Lt.zero_lt_succ z2) ",
                "z hbz) ",
                "(fun (n : Nat) (m : Nat) (_hnm : Lt n m) (ih : forall (z : Nat), Le m z -> Lt n z) => ",
                "fun (z : Nat) (hbz : Le (Nat.succ m) z) => ",
                "Nat.rec (fun (z0 : Nat) => Le (Nat.succ m) z0 -> Lt (Nat.succ n) z0) ",
                "(fun (h0 : Le (Nat.succ m) Nat.zero) => Empty.rec (fun (_ : Empty) => Lt (Nat.succ n) Nat.zero) (le_succ_zero_empty m h0)) ",
                "(fun (z2 : Nat) (_ih2 : Le (Nat.succ m) z2 -> Lt (Nat.succ n) z2) (hz : Le (Nat.succ m) (Nat.succ z2)) => Lt.succ_lt_succ n z2 (ih z2 (le_pred_pred m z2 hz))) ",
                "z hbz) ",
                "a b hab c",
            ).to_string()),
            is_axiom: false,
            description: "Lt a b -> Le b c -> Lt a c. DerivedProved by Lt.rec (Type-preserving), deciding c via Nat.rec with le_succ_zero_empty (c=0 absurd) + le_pred_pred. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(), "Lt.rec".to_string(), "Le".to_string(), "Nat.rec".to_string(),
                "Empty".to_string(), "le_succ_zero_empty".to_string(), "le_pred_pred".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_succ_to_le: Lt a (succ b) -> Le a b. Compose lt_to_le_succ (Le (succ a)
        // (succ b)) with le_pred_pred.
        self.add_definition_structural(SpecDefinition {
            name: "lt_succ_to_le".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Lt a (Nat.succ b) -> Le a b".to_string(),
            value_src: Some(concat!(
                "fun (a : Nat) (b : Nat) (h : Lt a (Nat.succ b)) => ",
                "le_pred_pred a b (lt_to_le_succ a (Nat.succ b) h)",
            ).to_string()),
            is_axiom: false,
            description: "Lt a (succ b) -> Le a b. DerivedProved via le_pred_pred (lt_to_le_succ ...). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(), "Le".to_string(), "le_pred_pred".to_string(), "lt_to_le_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_succ_sub1_of_lt: Lt d i -> succ (sub i 1) = i (i is a successor).
        // Lt.rec; both arms are Eq.refl (in both Lt constructors the upper index is
        // a successor, and sub (succ x) 1 reduces to x).
        self.add_definition_structural(SpecDefinition {
            name: "nat_succ_sub1_of_lt".to_string(),
            type_src: "forall (d : Nat) (i : Nat), Lt d i -> Eq Nat (Nat.succ (Nat.sub i (Nat.succ Nat.zero))) i".to_string(),
            value_src: Some(concat!(
                "fun (d : Nat) (i : Nat) (h : Lt d i) => ",
                "Lt.rec (fun (x : Nat) (y : Nat) (_ : Lt x y) => Eq Nat (Nat.succ (Nat.sub y (Nat.succ Nat.zero))) y) ",
                "(fun (n : Nat) => Eq.refl Nat (Nat.succ n)) ",
                "(fun (n : Nat) (m : Nat) (_hnm : Lt n m) (_ih : Eq Nat (Nat.succ (Nat.sub m (Nat.succ Nat.zero))) m) => Eq.refl Nat (Nat.succ m)) ",
                "d i h",
            ).to_string()),
            is_axiom: false,
            description: "Lt d i -> succ (sub i 1) = i. DerivedProved via Lt.rec; both arms Eq.refl (upper index is a successor, sub (succ x) 1 = x). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(), "Lt.rec".to_string(), "Nat.sub".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fvRel_instantiate_at (A5): the substitution lemma for FVRel —
        // instantiating (at depth 0) FVRel-related bodies with FVRel-related
        // arguments yields FVRel-related results (the beta-contractum form used by
        // the bisimulation) (guide fvRel_instantiate_at, line 1448). FVRel.rec on
        // the body hypothesis with an Eq-threaded depth d (motive carries
        // Eq kk (succ(k+d))): bvar_bound cases on nat_trichotomy i d (below /
        // free-shift via fvRel_lift / above), bvar_free is above on both sides,
        // structural arms transport via instantiate_at_{sort,app,lam,pi,const} with
        // the lam/pi body depth+threshold advanced through nat_succ_add-style
        // Eq.cong on heq.
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_instantiate_at".to_string(),
            type_src: "forall (k : Nat) (b : KExpr) (b2 : KExpr) (a : KExpr) (a2 : KExpr), FVRel (Nat.succ k) b b2 -> FVRel k a a2 -> FVRel k (instantiate_at b a Nat.zero) (instantiate_at b2 a2 Nat.zero)".to_string(),
            value_src: Some(r"fun (k : Nat) (b : KExpr) (b2 : KExpr) (a : KExpr) (a2 : KExpr) (hb : FVRel (Nat.succ k) b b2) (ha : FVRel k a a2) => FVRel.rec (fun (kk : Nat) (x : KExpr) (y : KExpr) (_h : FVRel kk x y) => forall (d : Nat), Eq Nat kk (Nat.succ (Nat.add k d)) -> FVRel (Nat.add k d) (instantiate_at x a d) (instantiate_at y a2 d)) (fun (kk : Nat) (i : Nat) (hlt : Lt i kk) => fun (d : Nat) (heq : Eq Nat kk (Nat.succ (Nat.add k d))) => NatTrichotomy.rec i d (fun (_t : NatTrichotomy i d) => FVRel (Nat.add k d) (instantiate_at (KExpr.bvar i) a d) (instantiate_at (KExpr.bvar i) a2 d)) (fun (hid : Lt i d) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.bvar i) a2 d)) (KExpr.bvar i) (instantiate_at (KExpr.bvar i) a d) (Eq.symm KExpr (instantiate_at (KExpr.bvar i) a d) (KExpr.bvar i) (Eq.trans KExpr (instantiate_at (KExpr.bvar i) a d) (instantiate_bvar_at i d a) (KExpr.bvar i) (instantiate_at_bvar i a d) (instantiate_bvar_at_below i d a (lt_sub_succ i d hid)))) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (KExpr.bvar i) w) (KExpr.bvar i) (instantiate_at (KExpr.bvar i) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.bvar i) a2 d) (KExpr.bvar i) (Eq.trans KExpr (instantiate_at (KExpr.bvar i) a2 d) (instantiate_bvar_at i d a2) (KExpr.bvar i) (instantiate_at_bvar i a2 d) (instantiate_bvar_at_below i d a2 (lt_sub_succ i d hid)))) (FVRel.bvar_bound (Nat.add k d) i (lt_of_lt_of_le i d (Nat.add k d) hid (le_add_self_right k d)))))) (fun (hid : Eq Nat i d) => (Eq.substType Nat (fun (z : Nat) => FVRel (Nat.add k d) (instantiate_at (KExpr.bvar z) a d) (instantiate_at (KExpr.bvar z) a2 d)) d i (Eq.symm Nat i d hid) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.bvar d) a2 d)) (lift_at a Nat.zero d) (instantiate_at (KExpr.bvar d) a d) (Eq.symm KExpr (instantiate_at (KExpr.bvar d) a d) (lift_at a Nat.zero d) (Eq.trans KExpr (instantiate_at (KExpr.bvar d) a d) (instantiate_bvar_at d d a) (lift_at a Nat.zero d) (instantiate_at_bvar d a d) (instantiate_bvar_at_eq d a))) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (lift_at a Nat.zero d) w) (lift_at a2 Nat.zero d) (instantiate_at (KExpr.bvar d) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.bvar d) a2 d) (lift_at a2 Nat.zero d) (Eq.trans KExpr (instantiate_at (KExpr.bvar d) a2 d) (instantiate_bvar_at d d a2) (lift_at a2 Nat.zero d) (instantiate_at_bvar d a2 d) (instantiate_bvar_at_eq d a2))) (fvRel_lift k Nat.zero d a a2 (le_zero_n k) ha))))) (fun (hid : Lt d i) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.bvar i) a2 d)) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (instantiate_at (KExpr.bvar i) a d) (Eq.symm KExpr (instantiate_at (KExpr.bvar i) a d) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Eq.trans KExpr (instantiate_at (KExpr.bvar i) a d) (instantiate_bvar_at i d a) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (instantiate_at_bvar i a d) (instantiate_bvar_at_above i d a (le_sub_zero d i (lt_implies_le d i hid)) (lt_sub_succ d i hid)))) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) w) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (instantiate_at (KExpr.bvar i) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.bvar i) a2 d) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Eq.trans KExpr (instantiate_at (KExpr.bvar i) a2 d) (instantiate_bvar_at i d a2) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (instantiate_at_bvar i a2 d) (instantiate_bvar_at_above i d a2 (le_sub_zero d i (lt_implies_le d i hid)) (lt_sub_succ d i hid)))) (FVRel.bvar_bound (Nat.add k d) (Nat.sub i (Nat.succ Nat.zero)) (lt_of_lt_of_le (Nat.sub i (Nat.succ Nat.zero)) i (Nat.add k d) (Eq.substType Nat (fun (t : Nat) => Lt (Nat.sub i (Nat.succ Nat.zero)) t) (Nat.succ (Nat.sub i (Nat.succ Nat.zero))) i (nat_succ_sub1_of_lt d i hid) (lt_succ_self (Nat.sub i (Nat.succ Nat.zero)))) (lt_succ_to_le i (Nat.add k d) (Eq.substType Nat (fun (t : Nat) => Lt i t) kk (Nat.succ (Nat.add k d)) heq hlt))))))) (nat_trichotomy i d)) (fun (kk : Nat) (i : Nat) (j : Nat) (hi : Le kk i) (hj : Le kk j) => fun (d : Nat) (heq : Eq Nat kk (Nat.succ (Nat.add k d))) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.bvar j) a2 d)) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (instantiate_at (KExpr.bvar i) a d) (Eq.symm KExpr (instantiate_at (KExpr.bvar i) a d) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (Eq.trans KExpr (instantiate_at (KExpr.bvar i) a d) (instantiate_bvar_at i d a) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (instantiate_at_bvar i a d) (instantiate_bvar_at_above i d a (le_sub_zero d i (lt_implies_le d i (lt_of_lt_of_le d (Nat.succ (Nat.add k d)) i (lt_add_succ_right k d) (Eq.substType Nat (fun (t : Nat) => Le t i) kk (Nat.succ (Nat.add k d)) heq hi)))) (lt_sub_succ d i (lt_of_lt_of_le d (Nat.succ (Nat.add k d)) i (lt_add_succ_right k d) (Eq.substType Nat (fun (t : Nat) => Le t i) kk (Nat.succ (Nat.add k d)) heq hi)))))) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) w) (KExpr.bvar (Nat.sub j (Nat.succ Nat.zero))) (instantiate_at (KExpr.bvar j) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.bvar j) a2 d) (KExpr.bvar (Nat.sub j (Nat.succ Nat.zero))) (Eq.trans KExpr (instantiate_at (KExpr.bvar j) a2 d) (instantiate_bvar_at j d a2) (KExpr.bvar (Nat.sub j (Nat.succ Nat.zero))) (instantiate_at_bvar j a2 d) (instantiate_bvar_at_above j d a2 (le_sub_zero d j (lt_implies_le d j (lt_of_lt_of_le d (Nat.succ (Nat.add k d)) j (lt_add_succ_right k d) (Eq.substType Nat (fun (t : Nat) => Le t j) kk (Nat.succ (Nat.add k d)) heq hj)))) (lt_sub_succ d j (lt_of_lt_of_le d (Nat.succ (Nat.add k d)) j (lt_add_succ_right k d) (Eq.substType Nat (fun (t : Nat) => Le t j) kk (Nat.succ (Nat.add k d)) heq hj)))))) (FVRel.bvar_free (Nat.add k d) (Nat.sub i (Nat.succ Nat.zero)) (Nat.sub j (Nat.succ Nat.zero)) (le_succ_le_pred (Nat.add k d) i (Eq.substType Nat (fun (t : Nat) => Le t i) kk (Nat.succ (Nat.add k d)) heq hi)) (le_succ_le_pred (Nat.add k d) j (Eq.substType Nat (fun (t : Nat) => Le t j) kk (Nat.succ (Nat.add k d)) heq hj)))))) (fun (kk : Nat) (n : Level) => fun (d : Nat) (_heq : Eq Nat kk (Nat.succ (Nat.add k d))) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.sort n) a2 d)) (KExpr.sort n) (instantiate_at (KExpr.sort n) a d) (Eq.symm KExpr (instantiate_at (KExpr.sort n) a d) (KExpr.sort n) (instantiate_at_sort n a d)) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (KExpr.sort n) w) (KExpr.sort n) (instantiate_at (KExpr.sort n) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.sort n) a2 d) (KExpr.sort n) (instantiate_at_sort n a2 d)) (FVRel.sort (Nat.add k d) n)))) (fun (kk : Nat) (n : Name) (us : ListType Level) => fun (d : Nat) (_heq : Eq Nat kk (Nat.succ (Nat.add k d))) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.const n us) a2 d)) (KExpr.const n us) (instantiate_at (KExpr.const n us) a d) (Eq.symm KExpr (instantiate_at (KExpr.const n us) a d) (KExpr.const n us) (instantiate_at_const n us a d)) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (KExpr.const n us) w) (KExpr.const n us) (instantiate_at (KExpr.const n us) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.const n us) a2 d) (KExpr.const n us) (instantiate_at_const n us a2 d)) (FVRel.const (Nat.add k d) n us)))) (fun (kk : Nat) (f : KExpr) (f2 : KExpr) (aa : KExpr) (aa2 : KExpr) (hf : FVRel kk f f2) (haa : FVRel kk aa aa2) (ihf : forall (d : Nat), Eq Nat kk (Nat.succ (Nat.add k d)) -> FVRel (Nat.add k d) (instantiate_at f a d) (instantiate_at f2 a2 d)) (iha : forall (d : Nat), Eq Nat kk (Nat.succ (Nat.add k d)) -> FVRel (Nat.add k d) (instantiate_at aa a d) (instantiate_at aa2 a2 d)) => fun (d : Nat) (heq : Eq Nat kk (Nat.succ (Nat.add k d))) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.app f2 aa2) a2 d)) (KExpr.app (instantiate_at f a d) (instantiate_at aa a d)) (instantiate_at (KExpr.app f aa) a d) (Eq.symm KExpr (instantiate_at (KExpr.app f aa) a d) (KExpr.app (instantiate_at f a d) (instantiate_at aa a d)) (instantiate_at_app f aa a d)) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (KExpr.app (instantiate_at f a d) (instantiate_at aa a d)) w) (KExpr.app (instantiate_at f2 a2 d) (instantiate_at aa2 a2 d)) (instantiate_at (KExpr.app f2 aa2) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.app f2 aa2) a2 d) (KExpr.app (instantiate_at f2 a2 d) (instantiate_at aa2 a2 d)) (instantiate_at_app f2 aa2 a2 d)) (FVRel.app (Nat.add k d) (instantiate_at f a d) (instantiate_at f2 a2 d) (instantiate_at aa a d) (instantiate_at aa2 a2 d) (ihf d heq) (iha d heq))))) (fun (kk : Nat) (A : KExpr) (A2 : KExpr) (bb : KExpr) (bb2 : KExpr) (hA : FVRel kk A A2) (hbb : FVRel (Nat.succ kk) bb bb2) (ihA : forall (d : Nat), Eq Nat kk (Nat.succ (Nat.add k d)) -> FVRel (Nat.add k d) (instantiate_at A a d) (instantiate_at A2 a2 d)) (ihbb : forall (d : Nat), Eq Nat (Nat.succ kk) (Nat.succ (Nat.add k d)) -> FVRel (Nat.add k d) (instantiate_at bb a d) (instantiate_at bb2 a2 d)) => fun (d : Nat) (heq : Eq Nat kk (Nat.succ (Nat.add k d))) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.lam A2 bb2) a2 d)) (KExpr.lam (instantiate_at A a d) (instantiate_at bb a (Nat.succ d))) (instantiate_at (KExpr.lam A bb) a d) (Eq.symm KExpr (instantiate_at (KExpr.lam A bb) a d) (KExpr.lam (instantiate_at A a d) (instantiate_at bb a (Nat.succ d))) (instantiate_at_lam A bb a d)) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (KExpr.lam (instantiate_at A a d) (instantiate_at bb a (Nat.succ d))) w) (KExpr.lam (instantiate_at A2 a2 d) (instantiate_at bb2 a2 (Nat.succ d))) (instantiate_at (KExpr.lam A2 bb2) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.lam A2 bb2) a2 d) (KExpr.lam (instantiate_at A2 a2 d) (instantiate_at bb2 a2 (Nat.succ d))) (instantiate_at_lam A2 bb2 a2 d)) (FVRel.lam (Nat.add k d) (instantiate_at A a d) (instantiate_at A2 a2 d) (instantiate_at bb a (Nat.succ d)) (instantiate_at bb2 a2 (Nat.succ d)) (ihA d heq) (ihbb (Nat.succ d) (Eq.cong Nat Nat Nat.succ kk (Nat.succ (Nat.add k d)) heq)))))) (fun (kk : Nat) (A : KExpr) (A2 : KExpr) (bb : KExpr) (bb2 : KExpr) (hA : FVRel kk A A2) (hbb : FVRel (Nat.succ kk) bb bb2) (ihA : forall (d : Nat), Eq Nat kk (Nat.succ (Nat.add k d)) -> FVRel (Nat.add k d) (instantiate_at A a d) (instantiate_at A2 a2 d)) (ihbb : forall (d : Nat), Eq Nat (Nat.succ kk) (Nat.succ (Nat.add k d)) -> FVRel (Nat.add k d) (instantiate_at bb a d) (instantiate_at bb2 a2 d)) => fun (d : Nat) (heq : Eq Nat kk (Nat.succ (Nat.add k d))) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.pi A2 bb2) a2 d)) (KExpr.pi (instantiate_at A a d) (instantiate_at bb a (Nat.succ d))) (instantiate_at (KExpr.pi A bb) a d) (Eq.symm KExpr (instantiate_at (KExpr.pi A bb) a d) (KExpr.pi (instantiate_at A a d) (instantiate_at bb a (Nat.succ d))) (instantiate_at_pi A bb a d)) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (KExpr.pi (instantiate_at A a d) (instantiate_at bb a (Nat.succ d))) w) (KExpr.pi (instantiate_at A2 a2 d) (instantiate_at bb2 a2 (Nat.succ d))) (instantiate_at (KExpr.pi A2 bb2) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.pi A2 bb2) a2 d) (KExpr.pi (instantiate_at A2 a2 d) (instantiate_at bb2 a2 (Nat.succ d))) (instantiate_at_pi A2 bb2 a2 d)) (FVRel.pi (Nat.add k d) (instantiate_at A a d) (instantiate_at A2 a2 d) (instantiate_at bb a (Nat.succ d)) (instantiate_at bb2 a2 (Nat.succ d)) (ihA d heq) (ihbb (Nat.succ d) (Eq.cong Nat Nat Nat.succ kk (Nat.succ (Nat.add k d)) heq)))))) (fun (kk : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (hlty : FVRel kk lty lty2) (hlv : FVRel kk lv lv2) (hlb : FVRel (Nat.succ kk) lb lb2) (ihty : forall (d : Nat), Eq Nat kk (Nat.succ (Nat.add k d)) -> FVRel (Nat.add k d) (instantiate_at lty a d) (instantiate_at lty2 a2 d)) (ihv : forall (d : Nat), Eq Nat kk (Nat.succ (Nat.add k d)) -> FVRel (Nat.add k d) (instantiate_at lv a d) (instantiate_at lv2 a2 d)) (ihb : forall (d : Nat), Eq Nat (Nat.succ kk) (Nat.succ (Nat.add k d)) -> FVRel (Nat.add k d) (instantiate_at lb a d) (instantiate_at lb2 a2 d)) => fun (d : Nat) (heq : Eq Nat kk (Nat.succ (Nat.add k d))) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.let_ lty2 lv2 lb2) a2 d)) (KExpr.let_ (instantiate_at lty a d) (instantiate_at lv a d) (instantiate_at lb a (Nat.succ d))) (instantiate_at (KExpr.let_ lty lv lb) a d) (Eq.symm KExpr (instantiate_at (KExpr.let_ lty lv lb) a d) (KExpr.let_ (instantiate_at lty a d) (instantiate_at lv a d) (instantiate_at lb a (Nat.succ d))) (instantiate_at_let_ lty lv lb a d)) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (KExpr.let_ (instantiate_at lty a d) (instantiate_at lv a d) (instantiate_at lb a (Nat.succ d))) w) (KExpr.let_ (instantiate_at lty2 a2 d) (instantiate_at lv2 a2 d) (instantiate_at lb2 a2 (Nat.succ d))) (instantiate_at (KExpr.let_ lty2 lv2 lb2) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.let_ lty2 lv2 lb2) a2 d) (KExpr.let_ (instantiate_at lty2 a2 d) (instantiate_at lv2 a2 d) (instantiate_at lb2 a2 (Nat.succ d))) (instantiate_at_let_ lty2 lv2 lb2 a2 d)) (FVRel.let_ (Nat.add k d) (instantiate_at lty a d) (instantiate_at lty2 a2 d) (instantiate_at lv a d) (instantiate_at lv2 a2 d) (instantiate_at lb a (Nat.succ d)) (instantiate_at lb2 a2 (Nat.succ d)) (ihty d heq) (ihv d heq) (ihb (Nat.succ d) (Eq.cong Nat Nat Nat.succ kk (Nat.succ (Nat.add k d)) heq)))))) (fun (kk : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : FVRel kk sub sub2) (ihsub : forall (d : Nat), Eq Nat kk (Nat.succ (Nat.add k d)) -> FVRel (Nat.add k d) (instantiate_at sub a d) (instantiate_at sub2 a2 d)) => fun (d : Nat) (heq : Eq Nat kk (Nat.succ (Nat.add k d))) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.proj s i sub2) a2 d)) (KExpr.proj s i (instantiate_at sub a d)) (instantiate_at (KExpr.proj s i sub) a d) (Eq.symm KExpr (instantiate_at (KExpr.proj s i sub) a d) (KExpr.proj s i (instantiate_at sub a d)) (instantiate_at_proj s i sub a d)) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (KExpr.proj s i (instantiate_at sub a d)) w) (KExpr.proj s i (instantiate_at sub2 a2 d)) (instantiate_at (KExpr.proj s i sub2) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.proj s i sub2) a2 d) (KExpr.proj s i (instantiate_at sub2 a2 d)) (instantiate_at_proj s i sub2 a2 d)) (FVRel.proj (Nat.add k d) s i (instantiate_at sub a d) (instantiate_at sub2 a2 d) (ihsub d heq))))) (fun (kk : Nat) (v : Nat) => fun (d : Nat) (_heq : Eq Nat kk (Nat.succ (Nat.add k d))) => (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) w (instantiate_at (KExpr.lit v) a2 d)) (KExpr.lit v) (instantiate_at (KExpr.lit v) a d) (Eq.symm KExpr (instantiate_at (KExpr.lit v) a d) (KExpr.lit v) (instantiate_at_lit v a d)) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.add k d) (KExpr.lit v) w) (KExpr.lit v) (instantiate_at (KExpr.lit v) a2 d) (Eq.symm KExpr (instantiate_at (KExpr.lit v) a2 d) (KExpr.lit v) (instantiate_at_lit v a2 d)) (FVRel.lit (Nat.add k d) v)))) (Nat.succ k) b b2 hb Nat.zero (Eq.refl Nat (Nat.succ k))".to_string()),
            is_axiom: false,
            description: "FVRel substitution lemma: FVRel (succ k) b b2 and FVRel k a a2 give FVRel k (instantiate_at b a 0) (instantiate_at b2 a2 0). Guide's fvRel_instantiate_at (line 1448). DerivedProved via FVRel.rec on the body hypothesis with Eq-threaded depth; bvar arms case on nat_trichotomy (below/free-shift via fvRel_lift/above), structural arms transport via instantiate_at_{sort,app,lam,pi,const}. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(), "instantiate_at".to_string(),
                "NatTrichotomy".to_string(), "NatTrichotomy.rec".to_string(), "nat_trichotomy".to_string(),
                "instantiate_at_bvar".to_string(), "instantiate_at_sort".to_string(),
                "instantiate_at_app".to_string(), "instantiate_at_lam".to_string(),
                "instantiate_at_pi".to_string(), "instantiate_at_const".to_string(), "instantiate_at_let_".to_string(),
                "instantiate_at_proj".to_string(), "instantiate_at_lit".to_string(),
                "instantiate_bvar_at_below".to_string(), "instantiate_bvar_at_above".to_string(),
                "instantiate_bvar_at_eq".to_string(),
                "lt_sub_succ".to_string(), "le_sub_zero".to_string(),
                "lt_implies_le".to_string(), "lt_to_le_succ".to_string(), "lt_succ_to_le".to_string(),
                "le_succ_le_pred".to_string(), "lt_of_lt_of_le".to_string(),
                "le_add_self_right".to_string(), "lt_add_succ_right".to_string(),
                "nat_succ_sub1_of_lt".to_string(), "lt_succ_self".to_string(),
                "fvRel_lift".to_string(), "le_zero_n".to_string(),
                "Eq.substType".to_string(), "Eq.symm".to_string(), "Eq.trans".to_string(),
                "Eq.cong".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- BATCH 6d: FVRel inversion (app/lam/pi) for the beta bisimulation ---
        // The beta-bisimulation inducts on beta_reduces, so in each arm it must
        // invert the FVRel hypothesis on a KNOWN head shape. These witness inductives
        // + inversion lemmas do that via FVRel.rec with inline KExpr discriminators
        // (no-confusion, non-matching arms -> Empty) and inline projections
        // (injectivity, the matching arm). ZERO new axioms.

        self.add_inductive(
            concat!(
                "inductive FVRelAppInv (k : Nat) (ff : KExpr) (aa : KExpr) (g : KExpr) : Type\n",
                "| mk : forall (g1 : KExpr) (g2 : KExpr), Eq KExpr g (KExpr.app g1 g2) -> FVRel k ff g1 -> FVRel k aa g2 -> FVRelAppInv k ff aa g"
            ),
            "FVRelAppInv k ff aa g (Brick 2 batch 6d): the inversion of FVRel k (app ff aa) g — g is an app g1 g2 with FVRel k ff g1 and FVRel k aa g2. Kernel generates FVRelAppInv.rec. ZERO new axioms.",
        )?;
        self.add_inductive(
            concat!(
                "inductive FVRelLamInv (k : Nat) (A : KExpr) (b : KExpr) (g : KExpr) : Type\n",
                "| mk : forall (g1 : KExpr) (g2 : KExpr), Eq KExpr g (KExpr.lam g1 g2) -> FVRel k A g1 -> FVRel (Nat.succ k) b g2 -> FVRelLamInv k A b g"
            ),
            "FVRelLamInv k A b g (Brick 2 batch 6d): the inversion of FVRel k (lam A b) g — g is a lam g1 g2 with FVRel k A g1 and FVRel (succ k) b g2. Kernel generates FVRelLamInv.rec. ZERO new axioms.",
        )?;
        self.add_inductive(
            concat!(
                "inductive FVRelPiInv (k : Nat) (dom : KExpr) (body : KExpr) (g : KExpr) : Type\n",
                "| mk : forall (g1 : KExpr) (g2 : KExpr), Eq KExpr g (KExpr.pi g1 g2) -> FVRel k dom g1 -> FVRel (Nat.succ k) body g2 -> FVRelPiInv k dom body g"
            ),
            "FVRelPiInv k dom body g (Brick 2 batch 6d): the inversion of FVRel k (pi dom body) g — g is a pi g1 g2 with FVRel k dom g1 and FVRel (succ k) body g2. Kernel generates FVRelPiInv.rec. ZERO new axioms.",
        )?;

        self.add_definition_structural(SpecDefinition {
            name: "fvRel_app_inv".to_string(),
            type_src: "forall (k : Nat) (p1 : KExpr) (p2 : KExpr) (g : KExpr), FVRel k (KExpr.app p1 p2) g -> FVRelAppInv k p1 p2 g".to_string(),
            value_src: Some(r"fun (k : Nat) (p1 : KExpr) (p2 : KExpr) (g : KExpr) (h : FVRel k (KExpr.app p1 p2) g) => FVRel.rec (fun (kk : Nat) (x : KExpr) (y : KExpr) (_h : FVRel kk x y) => forall (r1 : KExpr) (r2 : KExpr), Eq KExpr x (KExpr.app r1 r2) -> FVRelAppInv kk r1 r2 y) (fun (kk : Nat) (i : Nat) (_hlt : Lt i kk) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.app r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelAppInv kk r1 r2 (KExpr.bvar i)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.bvar i) (KExpr.app r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (i : Nat) (j : Nat) (_hi : Le kk i) (_hj : Le kk j) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.app r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelAppInv kk r1 r2 (KExpr.bvar j)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.bvar i) (KExpr.app r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (n : Level) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.sort n) (KExpr.app r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelAppInv kk r1 r2 (KExpr.sort n)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.sort n) (KExpr.app r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (n : Name) (us : ListType Level) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.const n us) (KExpr.app r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelAppInv kk r1 r2 (KExpr.const n us)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.const n us) (KExpr.app r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel kk s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr p (KExpr.app r1 r2) -> FVRelAppInv kk r1 r2 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr s (KExpr.app r1 r2) -> FVRelAppInv kk r1 r2 s2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.app p s) (KExpr.app r1 r2)) => (FVRelAppInv.mk kk r1 r2 (KExpr.app p2 s2) p2 s2 (Eq.refl KExpr (KExpr.app p2 s2)) (Eq.substType KExpr (fun (w : KExpr) => FVRel kk w p2) p r1 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => u0) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.lam u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.pi u0 u1) (fun (n : Name) (us : ListType Level) => KExpr.const n us) (fun (u0 : KExpr) (u1 : KExpr) (u2 : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.let_ u0 u1 u2) (fun (ps : Name) (pidx : Nat) (psub : KExpr) (_ : KExpr) => KExpr.proj ps pidx psub) (fun (v : Nat) => KExpr.lit v) x) (KExpr.app p s) (KExpr.app r1 r2) heq) h1) (Eq.substType KExpr (fun (w : KExpr) => FVRel kk w s2) s r2 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.lam u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.pi u0 u1) (fun (n : Name) (us : ListType Level) => KExpr.const n us) (fun (u0 : KExpr) (u1 : KExpr) (u2 : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.let_ u0 u1 u2) (fun (ps : Name) (pidx : Nat) (psub : KExpr) (_ : KExpr) => KExpr.proj ps pidx psub) (fun (v : Nat) => KExpr.lit v) x) (KExpr.app p s) (KExpr.app r1 r2) heq) h2))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel (Nat.succ kk) s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr p (KExpr.app r1 r2) -> FVRelAppInv kk r1 r2 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr s (KExpr.app r1 r2) -> FVRelAppInv (Nat.succ kk) r1 r2 s2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.lam p s) (KExpr.app r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelAppInv kk r1 r2 (KExpr.lam p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.lam p s) (KExpr.app r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel (Nat.succ kk) s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr p (KExpr.app r1 r2) -> FVRelAppInv kk r1 r2 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr s (KExpr.app r1 r2) -> FVRelAppInv (Nat.succ kk) r1 r2 s2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.pi p s) (KExpr.app r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelAppInv kk r1 r2 (KExpr.pi p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.pi p s) (KExpr.app r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (h1 : FVRel kk lty lty2) (h2 : FVRel kk lv lv2) (h3 : FVRel (Nat.succ kk) lb lb2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr lty (KExpr.app r1 r2) -> FVRelAppInv kk r1 r2 lty2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr lv (KExpr.app r1 r2) -> FVRelAppInv kk r1 r2 lv2) (_ih3 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr lb (KExpr.app r1 r2) -> FVRelAppInv (Nat.succ kk) r1 r2 lb2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.let_ lty lv lb) (KExpr.app r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelAppInv kk r1 r2 (KExpr.let_ lty2 lv2 lb2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.let_ lty lv lb) (KExpr.app r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (_hsub : FVRel kk sub sub2) (_ihsub : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr sub (KExpr.app r1 r2) -> FVRelAppInv kk r1 r2 sub2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.proj s i sub) (KExpr.app r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelAppInv kk r1 r2 (KExpr.proj s i sub2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.proj s i sub) (KExpr.app r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (v : Nat) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.lit v) (KExpr.app r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelAppInv kk r1 r2 (KExpr.lit v)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.lit v) (KExpr.app r1 r2) heq ConstFreeUnit.triv))) k (KExpr.app p1 p2) g h p1 p2 (Eq.refl KExpr (KExpr.app p1 p2))".to_string()),
            is_axiom: false,
            description: "Inversion of FVRel on an app head. Guide's `cases hR` (app). DerivedProved via FVRel.rec with inline KExpr discriminator (no-confusion) + inline projections (injectivity). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(), "FVRelAppInv".to_string(), "FVRelAppInv.mk".to_string(),
                "KExpr.rec".to_string(), "Empty".to_string(), "Empty.rec".to_string(),
                "ConstFreeUnit".to_string(), "Eq.substType".to_string(), "Eq.cong".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_lam_inv".to_string(),
            type_src: "forall (k : Nat) (p1 : KExpr) (p2 : KExpr) (g : KExpr), FVRel k (KExpr.lam p1 p2) g -> FVRelLamInv k p1 p2 g".to_string(),
            value_src: Some(r"fun (k : Nat) (p1 : KExpr) (p2 : KExpr) (g : KExpr) (h : FVRel k (KExpr.lam p1 p2) g) => FVRel.rec (fun (kk : Nat) (x : KExpr) (y : KExpr) (_h : FVRel kk x y) => forall (r1 : KExpr) (r2 : KExpr), Eq KExpr x (KExpr.lam r1 r2) -> FVRelLamInv kk r1 r2 y) (fun (kk : Nat) (i : Nat) (_hlt : Lt i kk) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.lam r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelLamInv kk r1 r2 (KExpr.bvar i)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.bvar i) (KExpr.lam r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (i : Nat) (j : Nat) (_hi : Le kk i) (_hj : Le kk j) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.lam r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelLamInv kk r1 r2 (KExpr.bvar j)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.bvar i) (KExpr.lam r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (n : Level) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.sort n) (KExpr.lam r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelLamInv kk r1 r2 (KExpr.sort n)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.sort n) (KExpr.lam r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (n : Name) (us : ListType Level) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.const n us) (KExpr.lam r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelLamInv kk r1 r2 (KExpr.const n us)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.const n us) (KExpr.lam r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel kk s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr p (KExpr.lam r1 r2) -> FVRelLamInv kk r1 r2 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr s (KExpr.lam r1 r2) -> FVRelLamInv kk r1 r2 s2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.app p s) (KExpr.lam r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelLamInv kk r1 r2 (KExpr.app p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.app p s) (KExpr.lam r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel (Nat.succ kk) s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr p (KExpr.lam r1 r2) -> FVRelLamInv kk r1 r2 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr s (KExpr.lam r1 r2) -> FVRelLamInv (Nat.succ kk) r1 r2 s2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.lam p s) (KExpr.lam r1 r2)) => (FVRelLamInv.mk kk r1 r2 (KExpr.lam p2 s2) p2 s2 (Eq.refl KExpr (KExpr.lam p2 s2)) (Eq.substType KExpr (fun (w : KExpr) => FVRel kk w p2) p r1 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.app u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => u0) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.pi u0 u1) (fun (n : Name) (us : ListType Level) => KExpr.const n us) (fun (u0 : KExpr) (u1 : KExpr) (u2 : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.let_ u0 u1 u2) (fun (ps : Name) (pidx : Nat) (psub : KExpr) (_ : KExpr) => KExpr.proj ps pidx psub) (fun (v : Nat) => KExpr.lit v) x) (KExpr.lam p s) (KExpr.lam r1 r2) heq) h1) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.succ kk) w s2) s r2 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.app u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.pi u0 u1) (fun (n : Name) (us : ListType Level) => KExpr.const n us) (fun (u0 : KExpr) (u1 : KExpr) (u2 : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.let_ u0 u1 u2) (fun (ps : Name) (pidx : Nat) (psub : KExpr) (_ : KExpr) => KExpr.proj ps pidx psub) (fun (v : Nat) => KExpr.lit v) x) (KExpr.lam p s) (KExpr.lam r1 r2) heq) h2))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel (Nat.succ kk) s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr p (KExpr.lam r1 r2) -> FVRelLamInv kk r1 r2 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr s (KExpr.lam r1 r2) -> FVRelLamInv (Nat.succ kk) r1 r2 s2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.pi p s) (KExpr.lam r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelLamInv kk r1 r2 (KExpr.pi p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.pi p s) (KExpr.lam r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (h1 : FVRel kk lty lty2) (h2 : FVRel kk lv lv2) (h3 : FVRel (Nat.succ kk) lb lb2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr lty (KExpr.lam r1 r2) -> FVRelLamInv kk r1 r2 lty2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr lv (KExpr.lam r1 r2) -> FVRelLamInv kk r1 r2 lv2) (_ih3 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr lb (KExpr.lam r1 r2) -> FVRelLamInv (Nat.succ kk) r1 r2 lb2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.let_ lty lv lb) (KExpr.lam r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelLamInv kk r1 r2 (KExpr.let_ lty2 lv2 lb2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.let_ lty lv lb) (KExpr.lam r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (_hsub : FVRel kk sub sub2) (_ihsub : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr sub (KExpr.lam r1 r2) -> FVRelLamInv kk r1 r2 sub2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.proj s i sub) (KExpr.lam r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelLamInv kk r1 r2 (KExpr.proj s i sub2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.proj s i sub) (KExpr.lam r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (v : Nat) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.lit v) (KExpr.lam r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelLamInv kk r1 r2 (KExpr.lit v)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.lit v) (KExpr.lam r1 r2) heq ConstFreeUnit.triv))) k (KExpr.lam p1 p2) g h p1 p2 (Eq.refl KExpr (KExpr.lam p1 p2))".to_string()),
            is_axiom: false,
            description: "Inversion of FVRel on a lam head. Guide's `cases hR` (lam). DerivedProved via FVRel.rec with inline KExpr discriminator + projections. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(), "FVRelLamInv".to_string(), "FVRelLamInv.mk".to_string(),
                "KExpr.rec".to_string(), "Empty".to_string(), "Empty.rec".to_string(),
                "ConstFreeUnit".to_string(), "Eq.substType".to_string(), "Eq.cong".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_pi_inv".to_string(),
            type_src: "forall (k : Nat) (p1 : KExpr) (p2 : KExpr) (g : KExpr), FVRel k (KExpr.pi p1 p2) g -> FVRelPiInv k p1 p2 g".to_string(),
            value_src: Some(r"fun (k : Nat) (p1 : KExpr) (p2 : KExpr) (g : KExpr) (h : FVRel k (KExpr.pi p1 p2) g) => FVRel.rec (fun (kk : Nat) (x : KExpr) (y : KExpr) (_h : FVRel kk x y) => forall (r1 : KExpr) (r2 : KExpr), Eq KExpr x (KExpr.pi r1 r2) -> FVRelPiInv kk r1 r2 y) (fun (kk : Nat) (i : Nat) (_hlt : Lt i kk) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.pi r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelPiInv kk r1 r2 (KExpr.bvar i)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.bvar i) (KExpr.pi r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (i : Nat) (j : Nat) (_hi : Le kk i) (_hj : Le kk j) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.pi r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelPiInv kk r1 r2 (KExpr.bvar j)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.bvar i) (KExpr.pi r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (n : Level) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.sort n) (KExpr.pi r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelPiInv kk r1 r2 (KExpr.sort n)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.sort n) (KExpr.pi r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (n : Name) (us : ListType Level) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.const n us) (KExpr.pi r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelPiInv kk r1 r2 (KExpr.const n us)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.const n us) (KExpr.pi r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel kk s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr p (KExpr.pi r1 r2) -> FVRelPiInv kk r1 r2 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr s (KExpr.pi r1 r2) -> FVRelPiInv kk r1 r2 s2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.app p s) (KExpr.pi r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelPiInv kk r1 r2 (KExpr.app p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.app p s) (KExpr.pi r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel (Nat.succ kk) s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr p (KExpr.pi r1 r2) -> FVRelPiInv kk r1 r2 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr s (KExpr.pi r1 r2) -> FVRelPiInv (Nat.succ kk) r1 r2 s2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.lam p s) (KExpr.pi r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelPiInv kk r1 r2 (KExpr.lam p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.lam p s) (KExpr.pi r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel (Nat.succ kk) s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr p (KExpr.pi r1 r2) -> FVRelPiInv kk r1 r2 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr s (KExpr.pi r1 r2) -> FVRelPiInv (Nat.succ kk) r1 r2 s2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.pi p s) (KExpr.pi r1 r2)) => (FVRelPiInv.mk kk r1 r2 (KExpr.pi p2 s2) p2 s2 (Eq.refl KExpr (KExpr.pi p2 s2)) (Eq.substType KExpr (fun (w : KExpr) => FVRel kk w p2) p r1 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.app u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.lam u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => u0) (fun (n : Name) (us : ListType Level) => KExpr.const n us) (fun (u0 : KExpr) (u1 : KExpr) (u2 : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.let_ u0 u1 u2) (fun (ps : Name) (pidx : Nat) (psub : KExpr) (_ : KExpr) => KExpr.proj ps pidx psub) (fun (v : Nat) => KExpr.lit v) x) (KExpr.pi p s) (KExpr.pi r1 r2) heq) h1) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.succ kk) w s2) s r2 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.app u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.lam u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => u1) (fun (n : Name) (us : ListType Level) => KExpr.const n us) (fun (u0 : KExpr) (u1 : KExpr) (u2 : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.let_ u0 u1 u2) (fun (ps : Name) (pidx : Nat) (psub : KExpr) (_ : KExpr) => KExpr.proj ps pidx psub) (fun (v : Nat) => KExpr.lit v) x) (KExpr.pi p s) (KExpr.pi r1 r2) heq) h2))) (fun (kk : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (h1 : FVRel kk lty lty2) (h2 : FVRel kk lv lv2) (h3 : FVRel (Nat.succ kk) lb lb2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr lty (KExpr.pi r1 r2) -> FVRelPiInv kk r1 r2 lty2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr lv (KExpr.pi r1 r2) -> FVRelPiInv kk r1 r2 lv2) (_ih3 : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr lb (KExpr.pi r1 r2) -> FVRelPiInv (Nat.succ kk) r1 r2 lb2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.let_ lty lv lb) (KExpr.pi r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelPiInv kk r1 r2 (KExpr.let_ lty2 lv2 lb2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.let_ lty lv lb) (KExpr.pi r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (_hsub : FVRel kk sub sub2) (_ihsub : forall (r1 : KExpr) (r2 : KExpr), Eq KExpr sub (KExpr.pi r1 r2) -> FVRelPiInv kk r1 r2 sub2) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.proj s i sub) (KExpr.pi r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelPiInv kk r1 r2 (KExpr.proj s i sub2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.proj s i sub) (KExpr.pi r1 r2) heq ConstFreeUnit.triv))) (fun (kk : Nat) (v : Nat) => fun (r1 : KExpr) (r2 : KExpr) (heq : Eq KExpr (KExpr.lit v) (KExpr.pi r1 r2)) => (Empty.rec (fun (_ : Empty) => FVRelPiInv kk r1 r2 (KExpr.lit v)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => Empty) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.lit v) (KExpr.pi r1 r2) heq ConstFreeUnit.triv))) k (KExpr.pi p1 p2) g h p1 p2 (Eq.refl KExpr (KExpr.pi p1 p2))".to_string()),
            is_axiom: false,
            description: "Inversion of FVRel on a pi head. Guide's `cases hR` (pi). DerivedProved via FVRel.rec with inline KExpr discriminator + projections. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(), "FVRelPiInv".to_string(), "FVRelPiInv.mk".to_string(),
                "KExpr.rec".to_string(), "Empty".to_string(), "Empty.rec".to_string(),
                "ConstFreeUnit".to_string(), "Eq.substType".to_string(), "Eq.cong".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // LET INCREMENT (task #28): the let_ inversion the zeta/let congruence
        // arms of the beta bisimulation need — FVRel k (let_ ty v b) g forces g
        // to be a let_ with FVRel-related components (ty/v at k, body at succ k).
        self.add_inductive(
            concat!(
                "inductive FVRelLetInv (k : Nat) (ty : KExpr) (v : KExpr) (b : KExpr) (g : KExpr) : Type\n",
                "| mk : forall (g1 : KExpr) (g2 : KExpr) (g3 : KExpr), Eq KExpr g (KExpr.let_ g1 g2 g3) -> FVRel k ty g1 -> FVRel k v g2 -> FVRel (Nat.succ k) b g3 -> FVRelLetInv k ty v b g"
            ),
            "FVRelLetInv k ty v b g (let increment, task #28): the inversion of FVRel k (let_ ty v b) g — g is a let_ g1 g2 g3 with FVRel k ty g1, FVRel k v g2 and FVRel (succ k) b g3. Kernel generates FVRelLetInv.rec. ZERO new axioms.",
        )?;

        self.add_definition_structural(SpecDefinition {
            name: "fvRel_let_inv".to_string(),
            type_src: "forall (k : Nat) (p1 : KExpr) (p2 : KExpr) (p3 : KExpr) (g : KExpr), FVRel k (KExpr.let_ p1 p2 p3) g -> FVRelLetInv k p1 p2 p3 g".to_string(),
            value_src: Some(r"fun (k : Nat) (p1 : KExpr) (p2 : KExpr) (p3 : KExpr) (g : KExpr) (h : FVRel k (KExpr.let_ p1 p2 p3) g) => FVRel.rec (fun (kk : Nat) (x : KExpr) (y : KExpr) (_h : FVRel kk x y) => forall (r1 : KExpr) (r2 : KExpr) (r3 : KExpr), Eq KExpr x (KExpr.let_ r1 r2 r3) -> FVRelLetInv kk r1 r2 r3 y) (fun (kk : Nat) (i : Nat) (_hlt : Lt i kk) => fun (r1 : KExpr) (r2 : KExpr) (r3 : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.let_ r1 r2 r3)) => (Empty.rec (fun (_ : Empty) => FVRelLetInv kk r1 r2 r3 (KExpr.bvar i)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.bvar i) (KExpr.let_ r1 r2 r3) heq ConstFreeUnit.triv))) (fun (kk : Nat) (i : Nat) (j : Nat) (_hi : Le kk i) (_hj : Le kk j) => fun (r1 : KExpr) (r2 : KExpr) (r3 : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.let_ r1 r2 r3)) => (Empty.rec (fun (_ : Empty) => FVRelLetInv kk r1 r2 r3 (KExpr.bvar j)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.bvar i) (KExpr.let_ r1 r2 r3) heq ConstFreeUnit.triv))) (fun (kk : Nat) (n : Level) => fun (r1 : KExpr) (r2 : KExpr) (r3 : KExpr) (heq : Eq KExpr (KExpr.sort n) (KExpr.let_ r1 r2 r3)) => (Empty.rec (fun (_ : Empty) => FVRelLetInv kk r1 r2 r3 (KExpr.sort n)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.sort n) (KExpr.let_ r1 r2 r3) heq ConstFreeUnit.triv))) (fun (kk : Nat) (n : Name) (us : ListType Level) => fun (r1 : KExpr) (r2 : KExpr) (r3 : KExpr) (heq : Eq KExpr (KExpr.const n us) (KExpr.let_ r1 r2 r3)) => (Empty.rec (fun (_ : Empty) => FVRelLetInv kk r1 r2 r3 (KExpr.const n us)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.const n us) (KExpr.let_ r1 r2 r3) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel kk s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr) (r3 : KExpr), Eq KExpr p (KExpr.let_ r1 r2 r3) -> FVRelLetInv kk r1 r2 r3 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr) (r3 : KExpr), Eq KExpr s (KExpr.let_ r1 r2 r3) -> FVRelLetInv kk r1 r2 r3 s2) => fun (r1 : KExpr) (r2 : KExpr) (r3 : KExpr) (heq : Eq KExpr (KExpr.app p s) (KExpr.let_ r1 r2 r3)) => (Empty.rec (fun (_ : Empty) => FVRelLetInv kk r1 r2 r3 (KExpr.app p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.app p s) (KExpr.let_ r1 r2 r3) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel (Nat.succ kk) s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr) (r3 : KExpr), Eq KExpr p (KExpr.let_ r1 r2 r3) -> FVRelLetInv kk r1 r2 r3 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr) (r3 : KExpr), Eq KExpr s (KExpr.let_ r1 r2 r3) -> FVRelLetInv (Nat.succ kk) r1 r2 r3 s2) => fun (r1 : KExpr) (r2 : KExpr) (r3 : KExpr) (heq : Eq KExpr (KExpr.lam p s) (KExpr.let_ r1 r2 r3)) => (Empty.rec (fun (_ : Empty) => FVRelLetInv kk r1 r2 r3 (KExpr.lam p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.lam p s) (KExpr.let_ r1 r2 r3) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (h1 : FVRel kk p p2) (h2 : FVRel (Nat.succ kk) s s2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr) (r3 : KExpr), Eq KExpr p (KExpr.let_ r1 r2 r3) -> FVRelLetInv kk r1 r2 r3 p2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr) (r3 : KExpr), Eq KExpr s (KExpr.let_ r1 r2 r3) -> FVRelLetInv (Nat.succ kk) r1 r2 r3 s2) => fun (r1 : KExpr) (r2 : KExpr) (r3 : KExpr) (heq : Eq KExpr (KExpr.pi p s) (KExpr.let_ r1 r2 r3)) => (Empty.rec (fun (_ : Empty) => FVRelLetInv kk r1 r2 r3 (KExpr.pi p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.pi p s) (KExpr.let_ r1 r2 r3) heq ConstFreeUnit.triv))) (fun (kk : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (h1 : FVRel kk lty lty2) (h2 : FVRel kk lv lv2) (h3 : FVRel (Nat.succ kk) lb lb2) (_ih1 : forall (r1 : KExpr) (r2 : KExpr) (r3 : KExpr), Eq KExpr lty (KExpr.let_ r1 r2 r3) -> FVRelLetInv kk r1 r2 r3 lty2) (_ih2 : forall (r1 : KExpr) (r2 : KExpr) (r3 : KExpr), Eq KExpr lv (KExpr.let_ r1 r2 r3) -> FVRelLetInv kk r1 r2 r3 lv2) (_ih3 : forall (r1 : KExpr) (r2 : KExpr) (r3 : KExpr), Eq KExpr lb (KExpr.let_ r1 r2 r3) -> FVRelLetInv (Nat.succ kk) r1 r2 r3 lb2) => fun (r1 : KExpr) (r2 : KExpr) (r3 : KExpr) (heq : Eq KExpr (KExpr.let_ lty lv lb) (KExpr.let_ r1 r2 r3)) => (FVRelLetInv.mk kk r1 r2 r3 (KExpr.let_ lty2 lv2 lb2) lty2 lv2 lb2 (Eq.refl KExpr (KExpr.let_ lty2 lv2 lb2)) (Eq.substType KExpr (fun (w : KExpr) => FVRel kk w lty2) lty r1 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.app u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.lam u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.pi u0 u1) (fun (n : Name) (us : ListType Level) => KExpr.const n us) (fun (u0 : KExpr) (u1 : KExpr) (u2 : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => u0) (fun (ps : Name) (pidx : Nat) (psub : KExpr) (_ : KExpr) => KExpr.proj ps pidx psub) (fun (v : Nat) => KExpr.lit v) x) (KExpr.let_ lty lv lb) (KExpr.let_ r1 r2 r3) heq) h1) (Eq.substType KExpr (fun (w : KExpr) => FVRel kk w lv2) lv r2 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.app u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.lam u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.pi u0 u1) (fun (n : Name) (us : ListType Level) => KExpr.const n us) (fun (u0 : KExpr) (u1 : KExpr) (u2 : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => u1) (fun (ps : Name) (pidx : Nat) (psub : KExpr) (_ : KExpr) => KExpr.proj ps pidx psub) (fun (v : Nat) => KExpr.lit v) x) (KExpr.let_ lty lv lb) (KExpr.let_ r1 r2 r3) heq) h2) (Eq.substType KExpr (fun (w : KExpr) => FVRel (Nat.succ kk) w lb2) lb r3 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.app u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.lam u0 u1) (fun (u0 : KExpr) (u1 : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.pi u0 u1) (fun (n : Name) (us : ListType Level) => KExpr.const n us) (fun (u0 : KExpr) (u1 : KExpr) (u2 : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => u2) (fun (ps : Name) (pidx : Nat) (psub : KExpr) (_ : KExpr) => KExpr.proj ps pidx psub) (fun (v : Nat) => KExpr.lit v) x) (KExpr.let_ lty lv lb) (KExpr.let_ r1 r2 r3) heq) h3))) (fun (kk : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (_hsub : FVRel kk sub sub2) (_ihsub : forall (r1 : KExpr) (r2 : KExpr) (r3 : KExpr), Eq KExpr sub (KExpr.let_ r1 r2 r3) -> FVRelLetInv kk r1 r2 r3 sub2) => fun (r1 : KExpr) (r2 : KExpr) (r3 : KExpr) (heq : Eq KExpr (KExpr.proj s i sub) (KExpr.let_ r1 r2 r3)) => (Empty.rec (fun (_ : Empty) => FVRelLetInv kk r1 r2 r3 (KExpr.proj s i sub2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.proj s i sub) (KExpr.let_ r1 r2 r3) heq ConstFreeUnit.triv))) (fun (kk : Nat) (v : Nat) => fun (r1 : KExpr) (r2 : KExpr) (r3 : KExpr) (heq : Eq KExpr (KExpr.lit v) (KExpr.let_ r1 r2 r3)) => (Empty.rec (fun (_ : Empty) => FVRelLetInv kk r1 r2 r3 (KExpr.lit v)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => ConstFreeUnit) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.lit v) (KExpr.let_ r1 r2 r3) heq ConstFreeUnit.triv))) k (KExpr.let_ p1 p2 p3) g h p1 p2 p3 (Eq.refl KExpr (KExpr.let_ p1 p2 p3))".to_string()),
            is_axiom: false,
            description: "Inversion of FVRel on a let_ head (let increment, task #28). Guide's `cases hR` (let_). DerivedProved via FVRel.rec with inline KExpr discriminator (no-confusion, let_ -> Empty) + inline projections (injectivity, fst/snd/thd). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(), "FVRelLetInv".to_string(), "FVRelLetInv.mk".to_string(),
                "KExpr.rec".to_string(), "Empty".to_string(), "Empty.rec".to_string(),
                "ConstFreeUnit".to_string(), "Eq.substType".to_string(), "Eq.cong".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // FVRelProjInv + fvRel_proj_inv (proj/lit rung): inversion of FVRel on a proj head.
        // Mirror of FVRelAppInv/fvRel_app_inv; the proj_s arm is the LIVE recovery (proj
        // injectivity via proj_inj_{name,idx,sub}), all other arms off-shape discharges.
        self.add_inductive(
            concat!(
                "inductive FVRelProjInv (k : Nat) (s : Name) (i : Nat) (sub : KExpr) (g : KExpr) : Type\n",
                "| mk : forall (gsub : KExpr), Eq KExpr g (KExpr.proj s i gsub) -> FVRel k sub gsub -> FVRelProjInv k s i sub g"
            ),
            "FVRelProjInv k s i sub g: the inversion of FVRel k (proj s i sub) g — g is a proj s i gsub with FVRel k sub gsub. Kernel generates FVRelProjInv.rec. ZERO new axioms. Part of the proj/lit fragment rung.",
        )?;

        self.add_definition_structural(SpecDefinition {
            name: "fvRel_proj_inv".to_string(),
            type_src: "forall (k : Nat) (ps : Name) (pidx : Nat) (psub : KExpr) (g : KExpr), FVRel k (KExpr.proj ps pidx psub) g -> FVRelProjInv k ps pidx psub g".to_string(),
            value_src: Some(r"fun (k : Nat) (ps : Name) (pidx : Nat) (psub : KExpr) (g : KExpr) (h : FVRel k (KExpr.proj ps pidx psub) g) => FVRel.rec (fun (kk : Nat) (x : KExpr) (y : KExpr) (_h : FVRel kk x y) => forall (rs : Name) (ri : Nat) (rsub : KExpr), Eq KExpr x (KExpr.proj rs ri rsub) -> FVRelProjInv kk rs ri rsub y) (fun (kk : Nat) (i : Nat) (_hlt : Lt i kk) => fun (rs : Name) (ri : Nat) (rsub : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.proj rs ri rsub)) => (Empty.rec (fun (_ : Empty) => FVRelProjInv kk rs ri rsub (KExpr.bvar i)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => Empty) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.bvar i) (KExpr.proj rs ri rsub) heq ConstFreeUnit.triv))) (fun (kk : Nat) (i : Nat) (j : Nat) (_hi : Le kk i) (_hj : Le kk j) => fun (rs : Name) (ri : Nat) (rsub : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.proj rs ri rsub)) => (Empty.rec (fun (_ : Empty) => FVRelProjInv kk rs ri rsub (KExpr.bvar j)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => Empty) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.bvar i) (KExpr.proj rs ri rsub) heq ConstFreeUnit.triv))) (fun (kk : Nat) (n : Level) => fun (rs : Name) (ri : Nat) (rsub : KExpr) (heq : Eq KExpr (KExpr.sort n) (KExpr.proj rs ri rsub)) => (Empty.rec (fun (_ : Empty) => FVRelProjInv kk rs ri rsub (KExpr.sort n)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => Empty) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.sort n) (KExpr.proj rs ri rsub) heq ConstFreeUnit.triv))) (fun (kk : Nat) (n : Name) (us : ListType Level) => fun (rs : Name) (ri : Nat) (rsub : KExpr) (heq : Eq KExpr (KExpr.const n us) (KExpr.proj rs ri rsub)) => (Empty.rec (fun (_ : Empty) => FVRelProjInv kk rs ri rsub (KExpr.const n us)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => Empty) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.const n us) (KExpr.proj rs ri rsub) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (_h1 : FVRel kk p p2) (_h2 : FVRel kk s s2) (_ih1 : forall (rs : Name) (ri : Nat) (rsub : KExpr), Eq KExpr p (KExpr.proj rs ri rsub) -> FVRelProjInv kk rs ri rsub p2) (_ih2 : forall (rs : Name) (ri : Nat) (rsub : KExpr), Eq KExpr s (KExpr.proj rs ri rsub) -> FVRelProjInv kk rs ri rsub s2) => fun (rs : Name) (ri : Nat) (rsub : KExpr) (heq : Eq KExpr (KExpr.app p s) (KExpr.proj rs ri rsub)) => (Empty.rec (fun (_ : Empty) => FVRelProjInv kk rs ri rsub (KExpr.app p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => Empty) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.app p s) (KExpr.proj rs ri rsub) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (_h1 : FVRel kk p p2) (_h2 : FVRel (Nat.succ kk) s s2) (_ih1 : forall (rs : Name) (ri : Nat) (rsub : KExpr), Eq KExpr p (KExpr.proj rs ri rsub) -> FVRelProjInv kk rs ri rsub p2) (_ih2 : forall (rs : Name) (ri : Nat) (rsub : KExpr), Eq KExpr s (KExpr.proj rs ri rsub) -> FVRelProjInv (Nat.succ kk) rs ri rsub s2) => fun (rs : Name) (ri : Nat) (rsub : KExpr) (heq : Eq KExpr (KExpr.lam p s) (KExpr.proj rs ri rsub)) => (Empty.rec (fun (_ : Empty) => FVRelProjInv kk rs ri rsub (KExpr.lam p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => Empty) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.lam p s) (KExpr.proj rs ri rsub) heq ConstFreeUnit.triv))) (fun (kk : Nat) (p : KExpr) (p2 : KExpr) (s : KExpr) (s2 : KExpr) (_h1 : FVRel kk p p2) (_h2 : FVRel (Nat.succ kk) s s2) (_ih1 : forall (rs : Name) (ri : Nat) (rsub : KExpr), Eq KExpr p (KExpr.proj rs ri rsub) -> FVRelProjInv kk rs ri rsub p2) (_ih2 : forall (rs : Name) (ri : Nat) (rsub : KExpr), Eq KExpr s (KExpr.proj rs ri rsub) -> FVRelProjInv (Nat.succ kk) rs ri rsub s2) => fun (rs : Name) (ri : Nat) (rsub : KExpr) (heq : Eq KExpr (KExpr.pi p s) (KExpr.proj rs ri rsub)) => (Empty.rec (fun (_ : Empty) => FVRelProjInv kk rs ri rsub (KExpr.pi p2 s2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => Empty) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.pi p s) (KExpr.proj rs ri rsub) heq ConstFreeUnit.triv))) (fun (kk : Nat) (lty : KExpr) (lty2 : KExpr) (lv : KExpr) (lv2 : KExpr) (lb : KExpr) (lb2 : KExpr) (_h1 : FVRel kk lty lty2) (_h2 : FVRel kk lv lv2) (_h3 : FVRel (Nat.succ kk) lb lb2) (_ih1 : forall (rs : Name) (ri : Nat) (rsub : KExpr), Eq KExpr lty (KExpr.proj rs ri rsub) -> FVRelProjInv kk rs ri rsub lty2) (_ih2 : forall (rs : Name) (ri : Nat) (rsub : KExpr), Eq KExpr lv (KExpr.proj rs ri rsub) -> FVRelProjInv kk rs ri rsub lv2) (_ih3 : forall (rs : Name) (ri : Nat) (rsub : KExpr), Eq KExpr lb (KExpr.proj rs ri rsub) -> FVRelProjInv (Nat.succ kk) rs ri rsub lb2) => fun (rs : Name) (ri : Nat) (rsub : KExpr) (heq : Eq KExpr (KExpr.let_ lty lv lb) (KExpr.proj rs ri rsub)) => (Empty.rec (fun (_ : Empty) => FVRelProjInv kk rs ri rsub (KExpr.let_ lty2 lv2 lb2)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => Empty) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.let_ lty lv lb) (KExpr.proj rs ri rsub) heq ConstFreeUnit.triv))) (fun (kk : Nat) (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : FVRel kk sub sub2) (_ihsub : forall (rs : Name) (ri : Nat) (rsub : KExpr), Eq KExpr sub (KExpr.proj rs ri rsub) -> FVRelProjInv kk rs ri rsub sub2) => fun (rs : Name) (ri : Nat) (rsub : KExpr) (heq : Eq KExpr (KExpr.proj s i sub) (KExpr.proj rs ri rsub)) => FVRelProjInv.mk kk rs ri rsub (KExpr.proj s i sub2) sub2 (Eq.trans KExpr (KExpr.proj s i sub2) (KExpr.proj rs i sub2) (KExpr.proj rs ri sub2) (Eq.cong Name KExpr (fun (z : Name) => KExpr.proj z i sub2) s rs (proj_inj_name s i sub rs ri rsub heq)) (Eq.cong Nat KExpr (fun (z : Nat) => KExpr.proj rs z sub2) i ri (proj_inj_idx s i sub rs ri rsub heq))) (Eq.substType KExpr (fun (w : KExpr) => FVRel kk w sub2) sub rsub (proj_inj_sub s i sub rs ri rsub heq) hsub)) (fun (kk : Nat) (v : Nat) => fun (rs : Name) (ri : Nat) (rsub : KExpr) (heq : Eq KExpr (KExpr.lit v) (KExpr.proj rs ri rsub)) => (Empty.rec (fun (_ : Empty) => FVRelProjInv kk rs ri rsub (KExpr.lit v)) (Eq.substType KExpr (fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (_n : Level) => ConstFreeUnit) (fun (_i : Nat) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_n : Name) (_us : ListType Level) => ConstFreeUnit) (fun (_u0 : KExpr) (_u1 : KExpr) (_u2 : KExpr) (_ : Type) (_ : Type) (_ : Type) => ConstFreeUnit) (fun (_ps : Name) (_pi : Nat) (_psub : KExpr) (_ : Type) => Empty) (fun (_v : Nat) => ConstFreeUnit) x) (KExpr.lit v) (KExpr.proj rs ri rsub) heq ConstFreeUnit.triv))) k (KExpr.proj ps pidx psub) g h ps pidx psub (Eq.refl KExpr (KExpr.proj ps pidx psub))".to_string()),
            is_axiom: false,
            description: "Inversion of FVRel on a proj head (proj/lit rung). FVRel.rec with a source-equation motive; the proj_s arm recovers g via proj_inj_{name,idx,sub} (live), off-shape arms discharge by KExpr no-confusion. DerivedProved, zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "FVRel".to_string(), "FVRel.rec".to_string(), "FVRelProjInv".to_string(), "FVRelProjInv.mk".to_string(),
                "KExpr.rec".to_string(), "Empty".to_string(), "Empty.rec".to_string(), "ConstFreeUnit".to_string(), "ConstFreeUnit.triv".to_string(),
                "proj_inj_name".to_string(), "proj_inj_idx".to_string(), "proj_inj_sub".to_string(),
                "Eq.substType".to_string(), "Eq.cong".to_string(), "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- BATCH 6e: fvRel_beta_bisim (beta+congruence+iota bisimulation arm) ---

        // BetaBisimWitness k f e2 : the packaged existential
        // `exists f2, beta_reduces f f2 AND FVRel k e2 f2`.
        self.add_inductive(
            concat!(
                "inductive BetaBisimWitness (k : Nat) (f : KExpr) (e2 : KExpr) : Type\n",
                "| mk : forall (f2 : KExpr), beta_reduces f f2 -> FVRel k e2 f2 -> BetaBisimWitness k f e2"
            ),
            "BetaBisimWitness k f e2 (Brick 2 batch 6e): the packaged existential `exists f2, beta_reduces f f2 and FVRel k e2 f2`. Kernel generates BetaBisimWitness.rec. ZERO new axioms.",
        )?;

        // fvRel_beta_bisim: beta_reduces (beta + zeta + all congruences + iota) is
        // simulated along FVRel at every level (guide fvRel_beta_bisim, line 1689).
        // Induction on beta_reduces (14 arms — let increment adds zeta and the three
        // positional let congruences in the old bundled let_body position, iota still
        // last); each congruence arm inverts the FVRel hypothesis on the known head
        // (fvRel_app/lam/pi/let_inv), recurses via the IH, and rebuilds the step +
        // FVRel; the beta/zeta arms use fvRel_instantiate_at on the contractum; the
        // iota arm delegates to fvRel_iota_bisim.
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_beta_bisim".to_string(),
            type_src: "forall (e : KExpr) (e2 : KExpr), beta_reduces e e2 -> forall (k : Nat) (f : KExpr), FVRel k e f -> BetaBisimWitness k f e2".to_string(),
            value_src: Some(r"fun (e : KExpr) (e2 : KExpr) (hbeta : beta_reduces e e2) => beta_reduces.rec (fun (e0 : KExpr) (e0p : KExpr) (_hb : beta_reduces e0 e0p) => forall (k : Nat) (f : KExpr), FVRel k e0 f -> BetaBisimWitness k f e0p) (fun (A : KExpr) (bd : KExpr) (arg : KExpr) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.app (KExpr.lam A bd) arg) f) => (FVRelAppInv.rec k (KExpr.lam A bd) arg f (fun (_w : FVRelAppInv k (KExpr.lam A bd) arg f) => BetaBisimWitness k f (instantiate_at bd arg Nat.zero)) (fun (g1 : KExpr) (g2 : KExpr) (heqf : Eq KExpr f (KExpr.app g1 g2)) (hlam : FVRel k (KExpr.lam A bd) g1) (harg : FVRel k arg g2) => (FVRelLamInv.rec k A bd g1 (fun (_w : FVRelLamInv k A bd g1) => BetaBisimWitness k f (instantiate_at bd arg Nat.zero)) (fun (l1 : KExpr) (l2 : KExpr) (heqg1 : Eq KExpr g1 (KExpr.lam l1 l2)) (hA : FVRel k A l1) (hbd : FVRel (Nat.succ k) bd l2) => (BetaBisimWitness.mk k f (instantiate_at bd arg Nat.zero) (instantiate_at l2 g2 Nat.zero) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (instantiate_at l2 g2 Nat.zero)) (KExpr.app (KExpr.lam l1 l2) g2) f (Eq.symm KExpr f (KExpr.app (KExpr.lam l1 l2) g2) (Eq.trans KExpr f (KExpr.app g1 g2) (KExpr.app (KExpr.lam l1 l2) g2) heqf (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w g2) g1 (KExpr.lam l1 l2) heqg1))) (beta_reduces.beta l1 l2 g2)) (fvRel_instantiate_at k bd l2 arg g2 hbd harg))) (fvRel_lam_inv k A bd g1 hlam))) (fvRel_app_inv k (KExpr.lam A bd) arg f hR))) (fun (f0 : KExpr) (f0p : KExpr) (aa : KExpr) (hstep : beta_reduces f0 f0p) (ih : forall (k : Nat) (f : KExpr), FVRel k f0 f -> BetaBisimWitness k f f0p) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.app f0 aa) f) => (FVRelAppInv.rec k f0 aa f (fun (_w : FVRelAppInv k f0 aa f) => BetaBisimWitness k f (KExpr.app f0p aa)) (fun (g1 : KExpr) (g2 : KExpr) (heqf : Eq KExpr f (KExpr.app g1 g2)) (hf0 : FVRel k f0 g1) (haa : FVRel k aa g2) => (BetaBisimWitness.rec k g1 f0p (fun (_w : BetaBisimWitness k g1 f0p) => BetaBisimWitness k f (KExpr.app f0p aa)) (fun (g1p : KExpr) (st : beta_reduces g1 g1p) (hRp : FVRel k f0p g1p) => (BetaBisimWitness.mk k f (KExpr.app f0p aa) (KExpr.app g1p g2) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.app g1p g2)) (KExpr.app g1 g2) f (Eq.symm KExpr f (KExpr.app g1 g2) heqf) (beta_reduces.app_left g1 g1p g2 st)) (FVRel.app k f0p g1p aa g2 hRp haa))) (ih k g1 hf0))) (fvRel_app_inv k f0 aa f hR))) (fun (f0 : KExpr) (aa : KExpr) (aap : KExpr) (hstep : beta_reduces aa aap) (ih : forall (k : Nat) (f : KExpr), FVRel k aa f -> BetaBisimWitness k f aap) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.app f0 aa) f) => (FVRelAppInv.rec k f0 aa f (fun (_w : FVRelAppInv k f0 aa f) => BetaBisimWitness k f (KExpr.app f0 aap)) (fun (g1 : KExpr) (g2 : KExpr) (heqf : Eq KExpr f (KExpr.app g1 g2)) (hf0 : FVRel k f0 g1) (haa : FVRel k aa g2) => (BetaBisimWitness.rec k g2 aap (fun (_w : BetaBisimWitness k g2 aap) => BetaBisimWitness k f (KExpr.app f0 aap)) (fun (g2p : KExpr) (st : beta_reduces g2 g2p) (hRp : FVRel k aap g2p) => (BetaBisimWitness.mk k f (KExpr.app f0 aap) (KExpr.app g1 g2p) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.app g1 g2p)) (KExpr.app g1 g2) f (Eq.symm KExpr f (KExpr.app g1 g2) heqf) (beta_reduces.app_right g1 g2 g2p st)) (FVRel.app k f0 g1 aap g2p hf0 hRp))) (ih k g2 haa))) (fvRel_app_inv k f0 aa f hR))) (fun (ty : KExpr) (typ : KExpr) (bd : KExpr) (hstep : beta_reduces ty typ) (ih : forall (k : Nat) (f : KExpr), FVRel k ty f -> BetaBisimWitness k f typ) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.lam ty bd) f) => (FVRelLamInv.rec k ty bd f (fun (_w : FVRelLamInv k ty bd f) => BetaBisimWitness k f (KExpr.lam typ bd)) (fun (g1 : KExpr) (g2 : KExpr) (heqf : Eq KExpr f (KExpr.lam g1 g2)) (hty : FVRel k ty g1) (hbd : FVRel (Nat.succ k) bd g2) => (BetaBisimWitness.rec k g1 typ (fun (_w : BetaBisimWitness k g1 typ) => BetaBisimWitness k f (KExpr.lam typ bd)) (fun (g1p : KExpr) (st : beta_reduces g1 g1p) (hRp : FVRel k typ g1p) => (BetaBisimWitness.mk k f (KExpr.lam typ bd) (KExpr.lam g1p g2) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.lam g1p g2)) (KExpr.lam g1 g2) f (Eq.symm KExpr f (KExpr.lam g1 g2) heqf) (beta_reduces.lam_ty g1 g1p g2 st)) (FVRel.lam k typ g1p bd g2 hRp hbd))) (ih k g1 hty))) (fvRel_lam_inv k ty bd f hR))) (fun (ty : KExpr) (bd : KExpr) (bdp : KExpr) (hstep : beta_reduces bd bdp) (ih : forall (k : Nat) (f : KExpr), FVRel k bd f -> BetaBisimWitness k f bdp) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.lam ty bd) f) => (FVRelLamInv.rec k ty bd f (fun (_w : FVRelLamInv k ty bd f) => BetaBisimWitness k f (KExpr.lam ty bdp)) (fun (g1 : KExpr) (g2 : KExpr) (heqf : Eq KExpr f (KExpr.lam g1 g2)) (hty : FVRel k ty g1) (hbd : FVRel (Nat.succ k) bd g2) => (BetaBisimWitness.rec (Nat.succ k) g2 bdp (fun (_w : BetaBisimWitness (Nat.succ k) g2 bdp) => BetaBisimWitness k f (KExpr.lam ty bdp)) (fun (g2p : KExpr) (st : beta_reduces g2 g2p) (hRp : FVRel (Nat.succ k) bdp g2p) => (BetaBisimWitness.mk k f (KExpr.lam ty bdp) (KExpr.lam g1 g2p) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.lam g1 g2p)) (KExpr.lam g1 g2) f (Eq.symm KExpr f (KExpr.lam g1 g2) heqf) (beta_reduces.lam_body g1 g2 g2p st)) (FVRel.lam k ty g1 bdp g2p hty hRp))) (ih (Nat.succ k) g2 hbd))) (fvRel_lam_inv k ty bd f hR))) (fun (dm : KExpr) (dmp : KExpr) (bd : KExpr) (hstep : beta_reduces dm dmp) (ih : forall (k : Nat) (f : KExpr), FVRel k dm f -> BetaBisimWitness k f dmp) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.pi dm bd) f) => (FVRelPiInv.rec k dm bd f (fun (_w : FVRelPiInv k dm bd f) => BetaBisimWitness k f (KExpr.pi dmp bd)) (fun (g1 : KExpr) (g2 : KExpr) (heqf : Eq KExpr f (KExpr.pi g1 g2)) (hdm : FVRel k dm g1) (hbd : FVRel (Nat.succ k) bd g2) => (BetaBisimWitness.rec k g1 dmp (fun (_w : BetaBisimWitness k g1 dmp) => BetaBisimWitness k f (KExpr.pi dmp bd)) (fun (g1p : KExpr) (st : beta_reduces g1 g1p) (hRp : FVRel k dmp g1p) => (BetaBisimWitness.mk k f (KExpr.pi dmp bd) (KExpr.pi g1p g2) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.pi g1p g2)) (KExpr.pi g1 g2) f (Eq.symm KExpr f (KExpr.pi g1 g2) heqf) (beta_reduces.pi_dom g1 g1p g2 st)) (FVRel.pi k dmp g1p bd g2 hRp hbd))) (ih k g1 hdm))) (fvRel_pi_inv k dm bd f hR))) (fun (dm : KExpr) (bd : KExpr) (bdp : KExpr) (hstep : beta_reduces bd bdp) (ih : forall (k : Nat) (f : KExpr), FVRel k bd f -> BetaBisimWitness k f bdp) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.pi dm bd) f) => (FVRelPiInv.rec k dm bd f (fun (_w : FVRelPiInv k dm bd f) => BetaBisimWitness k f (KExpr.pi dm bdp)) (fun (g1 : KExpr) (g2 : KExpr) (heqf : Eq KExpr f (KExpr.pi g1 g2)) (hdm : FVRel k dm g1) (hbd : FVRel (Nat.succ k) bd g2) => (BetaBisimWitness.rec (Nat.succ k) g2 bdp (fun (_w : BetaBisimWitness (Nat.succ k) g2 bdp) => BetaBisimWitness k f (KExpr.pi dm bdp)) (fun (g2p : KExpr) (st : beta_reduces g2 g2p) (hRp : FVRel (Nat.succ k) bdp g2p) => (BetaBisimWitness.mk k f (KExpr.pi dm bdp) (KExpr.pi g1 g2p) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.pi g1 g2p)) (KExpr.pi g1 g2) f (Eq.symm KExpr f (KExpr.pi g1 g2) heqf) (beta_reduces.pi_cod g1 g2 g2p st)) (FVRel.pi k dm g1 bdp g2p hdm hRp))) (ih (Nat.succ k) g2 hbd))) (fvRel_pi_inv k dm bd f hR))) (fun (dm : KExpr) (dmp : KExpr) (bd : KExpr) (hstep : beta_reduces dm dmp) (ih : forall (k : Nat) (f : KExpr), FVRel k dm f -> BetaBisimWitness k f dmp) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.pi dm bd) f) => (FVRelPiInv.rec k dm bd f (fun (_w : FVRelPiInv k dm bd f) => BetaBisimWitness k f (KExpr.pi dmp bd)) (fun (g1 : KExpr) (g2 : KExpr) (heqf : Eq KExpr f (KExpr.pi g1 g2)) (hdm : FVRel k dm g1) (hbd : FVRel (Nat.succ k) bd g2) => (BetaBisimWitness.rec k g1 dmp (fun (_w : BetaBisimWitness k g1 dmp) => BetaBisimWitness k f (KExpr.pi dmp bd)) (fun (g1p : KExpr) (st : beta_reduces g1 g1p) (hRp : FVRel k dmp g1p) => (BetaBisimWitness.mk k f (KExpr.pi dmp bd) (KExpr.pi g1p g2) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.pi g1p g2)) (KExpr.pi g1 g2) f (Eq.symm KExpr f (KExpr.pi g1 g2) heqf) (beta_reduces.pi_dom g1 g1p g2 st)) (FVRel.pi k dmp g1p bd g2 hRp hbd))) (ih k g1 hdm))) (fvRel_pi_inv k dm bd f hR))) (fun (dm : KExpr) (bd : KExpr) (bdp : KExpr) (hstep : beta_reduces bd bdp) (ih : forall (k : Nat) (f : KExpr), FVRel k bd f -> BetaBisimWitness k f bdp) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.pi dm bd) f) => (FVRelPiInv.rec k dm bd f (fun (_w : FVRelPiInv k dm bd f) => BetaBisimWitness k f (KExpr.pi dm bdp)) (fun (g1 : KExpr) (g2 : KExpr) (heqf : Eq KExpr f (KExpr.pi g1 g2)) (hdm : FVRel k dm g1) (hbd : FVRel (Nat.succ k) bd g2) => (BetaBisimWitness.rec (Nat.succ k) g2 bdp (fun (_w : BetaBisimWitness (Nat.succ k) g2 bdp) => BetaBisimWitness k f (KExpr.pi dm bdp)) (fun (g2p : KExpr) (st : beta_reduces g2 g2p) (hRp : FVRel (Nat.succ k) bdp g2p) => (BetaBisimWitness.mk k f (KExpr.pi dm bdp) (KExpr.pi g1 g2p) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.pi g1 g2p)) (KExpr.pi g1 g2) f (Eq.symm KExpr f (KExpr.pi g1 g2) heqf) (beta_reduces.pi_cod g1 g2 g2p st)) (FVRel.pi k dm g1 bdp g2p hdm hRp))) (ih (Nat.succ k) g2 hbd))) (fvRel_pi_inv k dm bd f hR))) (fun (lty : KExpr) (lval : KExpr) (lbd : KExpr) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.let_ lty lval lbd) f) => (FVRelLetInv.rec k lty lval lbd f (fun (_w : FVRelLetInv k lty lval lbd f) => BetaBisimWitness k f (instantiate_at lbd lval Nat.zero)) (fun (g1 : KExpr) (g2 : KExpr) (g3 : KExpr) (heqf : Eq KExpr f (KExpr.let_ g1 g2 g3)) (hty : FVRel k lty g1) (hval : FVRel k lval g2) (hbd : FVRel (Nat.succ k) lbd g3) => (BetaBisimWitness.mk k f (instantiate_at lbd lval Nat.zero) (instantiate_at g3 g2 Nat.zero) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (instantiate_at g3 g2 Nat.zero)) (KExpr.let_ g1 g2 g3) f (Eq.symm KExpr f (KExpr.let_ g1 g2 g3) heqf) (beta_reduces.zeta g1 g2 g3)) (fvRel_instantiate_at k lbd g3 lval g2 hbd hval))) (fvRel_let_inv k lty lval lbd f hR))) (fun (lty : KExpr) (ltyp : KExpr) (lval : KExpr) (lbd : KExpr) (hstep : beta_reduces lty ltyp) (ih : forall (k : Nat) (f : KExpr), FVRel k lty f -> BetaBisimWitness k f ltyp) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.let_ lty lval lbd) f) => (FVRelLetInv.rec k lty lval lbd f (fun (_w : FVRelLetInv k lty lval lbd f) => BetaBisimWitness k f (KExpr.let_ ltyp lval lbd)) (fun (g1 : KExpr) (g2 : KExpr) (g3 : KExpr) (heqf : Eq KExpr f (KExpr.let_ g1 g2 g3)) (hty : FVRel k lty g1) (hval : FVRel k lval g2) (hbd : FVRel (Nat.succ k) lbd g3) => (BetaBisimWitness.rec k g1 ltyp (fun (_w : BetaBisimWitness k g1 ltyp) => BetaBisimWitness k f (KExpr.let_ ltyp lval lbd)) (fun (g1p : KExpr) (st : beta_reduces g1 g1p) (hRp : FVRel k ltyp g1p) => (BetaBisimWitness.mk k f (KExpr.let_ ltyp lval lbd) (KExpr.let_ g1p g2 g3) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.let_ g1p g2 g3)) (KExpr.let_ g1 g2 g3) f (Eq.symm KExpr f (KExpr.let_ g1 g2 g3) heqf) (beta_reduces.let_ty g1 g1p g2 g3 st)) (FVRel.let_ k ltyp g1p lval g2 lbd g3 hRp hval hbd))) (ih k g1 hty))) (fvRel_let_inv k lty lval lbd f hR))) (fun (lty : KExpr) (lval : KExpr) (lvalp : KExpr) (lbd : KExpr) (hstep : beta_reduces lval lvalp) (ih : forall (k : Nat) (f : KExpr), FVRel k lval f -> BetaBisimWitness k f lvalp) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.let_ lty lval lbd) f) => (FVRelLetInv.rec k lty lval lbd f (fun (_w : FVRelLetInv k lty lval lbd f) => BetaBisimWitness k f (KExpr.let_ lty lvalp lbd)) (fun (g1 : KExpr) (g2 : KExpr) (g3 : KExpr) (heqf : Eq KExpr f (KExpr.let_ g1 g2 g3)) (hty : FVRel k lty g1) (hval : FVRel k lval g2) (hbd : FVRel (Nat.succ k) lbd g3) => (BetaBisimWitness.rec k g2 lvalp (fun (_w : BetaBisimWitness k g2 lvalp) => BetaBisimWitness k f (KExpr.let_ lty lvalp lbd)) (fun (g2p : KExpr) (st : beta_reduces g2 g2p) (hRp : FVRel k lvalp g2p) => (BetaBisimWitness.mk k f (KExpr.let_ lty lvalp lbd) (KExpr.let_ g1 g2p g3) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.let_ g1 g2p g3)) (KExpr.let_ g1 g2 g3) f (Eq.symm KExpr f (KExpr.let_ g1 g2 g3) heqf) (beta_reduces.let_val g1 g2 g2p g3 st)) (FVRel.let_ k lty g1 lvalp g2p lbd g3 hty hRp hbd))) (ih k g2 hval))) (fvRel_let_inv k lty lval lbd f hR))) (fun (lty : KExpr) (lval : KExpr) (lbd : KExpr) (lbdp : KExpr) (hstep : beta_reduces lbd lbdp) (ih : forall (k : Nat) (f : KExpr), FVRel k lbd f -> BetaBisimWitness k f lbdp) => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.let_ lty lval lbd) f) => (FVRelLetInv.rec k lty lval lbd f (fun (_w : FVRelLetInv k lty lval lbd f) => BetaBisimWitness k f (KExpr.let_ lty lval lbdp)) (fun (g1 : KExpr) (g2 : KExpr) (g3 : KExpr) (heqf : Eq KExpr f (KExpr.let_ g1 g2 g3)) (hty : FVRel k lty g1) (hval : FVRel k lval g2) (hbd : FVRel (Nat.succ k) lbd g3) => (BetaBisimWitness.rec (Nat.succ k) g3 lbdp (fun (_w : BetaBisimWitness (Nat.succ k) g3 lbdp) => BetaBisimWitness k f (KExpr.let_ lty lval lbdp)) (fun (g3p : KExpr) (st : beta_reduces g3 g3p) (hRp : FVRel (Nat.succ k) lbdp g3p) => (BetaBisimWitness.mk k f (KExpr.let_ lty lval lbdp) (KExpr.let_ g1 g2 g3p) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.let_ g1 g2 g3p)) (KExpr.let_ g1 g2 g3) f (Eq.symm KExpr f (KExpr.let_ g1 g2 g3) heqf) (beta_reduces.let_body g1 g2 g3 g3p st)) (FVRel.let_ k lty g1 lval g2 lbdp g3p hty hval hRp))) (ih (Nat.succ k) g3 hbd))) (fvRel_let_inv k lty lval lbd f hR))) (fun (ee : KExpr) (eep : KExpr) (hiota : iota_reduces ee eep) => fun (k : Nat) (f : KExpr) (hR : FVRel k ee f) => (IotaBisimWitness.rec k f eep (fun (_w : IotaBisimWitness k f eep) => BetaBisimWitness k f eep) (fun (f2 : KExpr) (st : iota_reduces f f2) (hRp : FVRel k eep f2) => (BetaBisimWitness.mk k f eep f2 (beta_reduces.iota f f2 st) hRp)) (fvRel_iota_bisim k ee f eep hR hiota))) (fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub' : KExpr) (hstep : beta_reduces sub sub') (ih : forall (k : Nat) (f : KExpr), FVRel k sub f -> BetaBisimWitness k f sub') => fun (k : Nat) (f : KExpr) (hR : FVRel k (KExpr.proj ps pidx sub) f) => (FVRelProjInv.rec k ps pidx sub f (fun (_w : FVRelProjInv k ps pidx sub f) => BetaBisimWitness k f (KExpr.proj ps pidx sub')) (fun (fsub : KExpr) (heqf : Eq KExpr f (KExpr.proj ps pidx fsub)) (hfv1 : FVRel k sub fsub) => (BetaBisimWitness.rec k fsub sub' (fun (_w : BetaBisimWitness k fsub sub') => BetaBisimWitness k f (KExpr.proj ps pidx sub')) (fun (fsub2 : KExpr) (st : beta_reduces fsub fsub2) (hRp : FVRel k sub' fsub2) => (BetaBisimWitness.mk k f (KExpr.proj ps pidx sub') (KExpr.proj ps pidx fsub2) (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w (KExpr.proj ps pidx fsub2)) (KExpr.proj ps pidx fsub) f (Eq.symm KExpr f (KExpr.proj ps pidx fsub) heqf) (beta_reduces.proj ps pidx fsub fsub2 st)) (FVRel.proj k ps pidx sub' fsub2 hRp))) (ih k fsub hfv1))) (fvRel_proj_inv k ps pidx sub f hR))) e e2 hbeta".to_string()),
            is_axiom: false,
            description: "beta_reduces is simulated along FVRel: FVRel k e f and beta_reduces e e2 give a beta-reduct f2 of f with FVRel k e2 f2 (packaged as BetaBisimWitness). Guide's fvRel_beta_bisim (line 1689). DerivedProved by induction on beta_reduces (14 arms; let increment: zeta + let_ty/let_val/let_body) using FVRel inversion (app/lam/pi/let), fvRel_instantiate_at (beta/zeta contractum), and fvRel_iota_bisim (iota). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "BetaBisimWitness".to_string(), "BetaBisimWitness.mk".to_string(), "BetaBisimWitness.rec".to_string(),
                "beta_reduces".to_string(), "beta_reduces.rec".to_string(),
                "beta_reduces.beta".to_string(), "beta_reduces.app_left".to_string(), "beta_reduces.app_right".to_string(),
                "beta_reduces.lam_ty".to_string(), "beta_reduces.lam_body".to_string(),
                "beta_reduces.pi_dom".to_string(), "beta_reduces.pi_cod".to_string(),
                "beta_reduces.zeta".to_string(), "beta_reduces.let_ty".to_string(),
                "beta_reduces.let_val".to_string(), "beta_reduces.let_body".to_string(),
                "beta_reduces.iota".to_string(),
                "fvRel_app_inv".to_string(), "fvRel_proj_inv".to_string(), "FVRelProjInv".to_string(), "FVRelProjInv.rec".to_string(), "beta_reduces.proj".to_string(), "FVRel.proj".to_string(), "fvRel_lam_inv".to_string(), "fvRel_pi_inv".to_string(), "fvRel_let_inv".to_string(),
                "FVRelAppInv.rec".to_string(), "FVRelLamInv.rec".to_string(), "FVRelPiInv.rec".to_string(), "FVRelLetInv.rec".to_string(),
                "fvRel_instantiate_at".to_string(), "fvRel_iota_bisim".to_string(), "IotaBisimWitness.rec".to_string(),
                "FVRel.app".to_string(), "FVRel.lam".to_string(), "FVRel.pi".to_string(), "FVRel.let_".to_string(),
                "KExpr.let_".to_string(), "instantiate_at".to_string(),
                "Eq.substType".to_string(), "Eq.symm".to_string(), "Eq.trans".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- BATCH 6f: fvRel_bisim (union) + SN transport (whnfAcc_of_fvRel) ---

        // WhnfBisimWitness k f e2 : `exists f2, whnf_step f f2 AND FVRel k e2 f2`.
        self.add_inductive(
            concat!(
                "inductive WhnfBisimWitness (k : Nat) (f : KExpr) (e2 : KExpr) : Type\n",
                "| mk : forall (f2 : KExpr), whnf_step f f2 -> FVRel k e2 f2 -> WhnfBisimWitness k f e2"
            ),
            "WhnfBisimWitness k f e2 (Brick 2 batch 6f): the packaged existential `exists f2, whnf_step f f2 and FVRel k e2 f2`. Kernel generates WhnfBisimWitness.rec. ZERO new axioms.",
        )?;

        // fvRel_bisim: FVRel is a bisimulation for whnf_step — dispatch over the two
        // whnf_step arms (beta -> fvRel_beta_bisim, delta -> fvRel_delta_bisim) and
        // repackage as a whnf_step (guide fvRel_bisim, line 1775).
        self.add_definition_structural(SpecDefinition {
            name: "fvRel_bisim".to_string(),
            type_src: "forall (e : KExpr) (e2 : KExpr), whnf_step e e2 -> forall (k : Nat) (f : KExpr), FVRel k e f -> WhnfBisimWitness k f e2".to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) (e2 : KExpr) (hs : whnf_step e e2) => ",
                "whnf_step.rec e e2 (fun (_h : whnf_step e e2) => forall (k : Nat) (f : KExpr), FVRel k e f -> WhnfBisimWitness k f e2) ",
                "(fun (hbr : beta_reduces e e2) => fun (k : Nat) (f : KExpr) (hR : FVRel k e f) => ",
                "BetaBisimWitness.rec k f e2 (fun (_w : BetaBisimWitness k f e2) => WhnfBisimWitness k f e2) ",
                "(fun (f2 : KExpr) (st : beta_reduces f f2) (hRp : FVRel k e2 f2) => WhnfBisimWitness.mk k f e2 f2 (whnf_step.beta f f2 st) hRp) ",
                "(fvRel_beta_bisim e e2 hbr k f hR)) ",
                "(fun (hdr : delta_reduces e e2) => fun (k : Nat) (f : KExpr) (hR : FVRel k e f) => ",
                "DeltaBisimWitness.rec k f e2 (fun (_w : DeltaBisimWitness k f e2) => WhnfBisimWitness k f e2) ",
                "(fun (f2 : KExpr) (st : delta_reduces f f2) (hRp : FVRel k e2 f2) => WhnfBisimWitness.mk k f e2 f2 (whnf_step.delta f f2 st) hRp) ",
                "(fvRel_delta_bisim k e f e2 hR hdr)) ",
                "hs",
            ).to_string()),
            is_axiom: false,
            description: "FVRel is a bisimulation for whnf_step: FVRel k e f and whnf_step e e2 give a whnf_step f f2 with FVRel k e2 f2 (packaged as WhnfBisimWitness). Guide's fvRel_bisim (line 1775). DerivedProved by whnf_step.rec dispatch to fvRel_beta_bisim / fvRel_delta_bisim. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "WhnfBisimWitness".to_string(), "WhnfBisimWitness.mk".to_string(),
                "whnf_step".to_string(), "whnf_step.rec".to_string(), "whnf_step.beta".to_string(), "whnf_step.delta".to_string(),
                "beta_reduces".to_string(), "delta_reduces".to_string(),
                "BetaBisimWitness.rec".to_string(), "DeltaBisimWitness.rec".to_string(),
                "fvRel_beta_bisim".to_string(), "fvRel_delta_bisim".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnfAcc_of_fvRel: strong normalization transports along FVRel — if f is
        // whnf_acc and FVRel 0 e f, then e is whnf_acc (guide whnfAcc_of_fvRel, line
        // 1788). Acc induction on whnf_acc f (generalizing e): every step of e
        // corresponds, via fvRel_bisim, to a step of f whose reduct the IH handles.
        self.add_definition_structural(SpecDefinition {
            name: "whnfAcc_of_fvRel".to_string(),
            type_src: "forall (e : KExpr) (f : KExpr), FVRel Nat.zero e f -> whnf_acc f -> whnf_acc e".to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) (f : KExpr) (hR : FVRel Nat.zero e f) (hf : whnf_acc f) => ",
                "whnf_acc.rec (fun (f0 : KExpr) (_h : whnf_acc f0) => forall (e0 : KExpr), FVRel Nat.zero e0 f0 -> whnf_acc e0) ",
                "(fun (f0 : KExpr) (hstepfn : forall (ep : KExpr), whnf_step f0 ep -> whnf_acc ep) (ih : forall (ep : KExpr), whnf_step f0 ep -> forall (e0 : KExpr), FVRel Nat.zero e0 ep -> whnf_acc e0) => ",
                "fun (e1 : KExpr) (hR1 : FVRel Nat.zero e1 f0) => ",
                "whnf_acc.intro e1 (fun (ep : KExpr) (hstep : whnf_step e1 ep) => ",
                "WhnfBisimWitness.rec Nat.zero f0 ep (fun (_w : WhnfBisimWitness Nat.zero f0 ep) => whnf_acc ep) ",
                "(fun (fp : KExpr) (hfstep : whnf_step f0 fp) (hRp : FVRel Nat.zero ep fp) => ih fp hfstep ep hRp) ",
                "(fvRel_bisim e1 ep hstep Nat.zero f0 hR1))) ",
                "f hf e hR",
            ).to_string()),
            is_axiom: false,
            description: "SN transports along FVRel: FVRel 0 e f and whnf_acc f give whnf_acc e. Guide's whnfAcc_of_fvRel (line 1788). DerivedProved by whnf_acc.rec (Acc induction) generalizing e, using fvRel_bisim to match each step. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_acc".to_string(), "whnf_acc.rec".to_string(), "whnf_acc.intro".to_string(),
                "whnf_step".to_string(), "WhnfBisimWitness.rec".to_string(), "fvRel_bisim".to_string(),
                "FVRel".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnfAcc_of_instantiate_bvar0: the SN reflection the dependent pi case needs
        // — whnf_acc (instantiate C (bvar 0)) -> whnf_acc C (guide
        // whnfAcc_of_instantiate_bvar0, line 1420 region), via whnfAcc_of_fvRel +
        // fvRel_instantiate_bvar0.
        self.add_definition_structural(SpecDefinition {
            name: "whnfAcc_of_instantiate_bvar0".to_string(),
            type_src: "forall (C : KExpr), whnf_acc (instantiate_at C (KExpr.bvar Nat.zero) Nat.zero) -> whnf_acc C".to_string(),
            value_src: Some(concat!(
                "fun (C : KExpr) (h : whnf_acc (instantiate_at C (KExpr.bvar Nat.zero) Nat.zero)) => ",
                "whnfAcc_of_fvRel C (instantiate_at C (KExpr.bvar Nat.zero) Nat.zero) (fvRel_instantiate_bvar0 Nat.zero C) h",
            ).to_string()),
            is_axiom: false,
            description: "SN reflection along the bvar-0 instantiation: whnf_acc (instantiate_at C (bvar 0) 0) -> whnf_acc C. The dependent pi case's SN reflection. DerivedProved via whnfAcc_of_fvRel + fvRel_instantiate_bvar0. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_acc".to_string(), "instantiate_at".to_string(),
                "whnfAcc_of_fvRel".to_string(), "fvRel_instantiate_bvar0".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // §8/§8a PRIORITY BATCH (this port): CandModel field projections
        // (cm_Red / CR1-3 / RedAbstraction+redAbstraction_holds and, per the let
        // increment, RedLet+redLet_holds), red_var,
        // whnfAcc_sort, and the pi SN-closure whnfAcc_pi. These gate the
        // fundamental adequacy cases (next batch). Every decl is value-full
        // (add_recursive_def / add_inductive / add_definition_structural) —
        // ZERO new kernel axioms, census stays 16.
        // ================================================================

        // Large-elimination discriminator: bvar -> Empty, every other head ->
        // Nat (the analog of KEXPR_NOT_PI_INLINE). Collapses `Eq (app/lam/pi ..)
        // (bvar i)` to Empty, the inversion primitive the bvar-source arms of
        // no_whnf_step_bvar need.
        let kexpr_not_bvar = concat!(
            "(KExpr.rec (fun (_ : KExpr) => Type) ",
            "(fun (_ : Level) => Nat) ",
            "(fun (_ : Nat) => Empty) ",
            "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
            "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
            "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
            "(fun (_ : Name) (_ : ListType Level) => Nat) ",
            "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
            "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
            "(fun (_ : Nat) => Nat))"
        );

        self.add_definition_structural(SpecDefinition {
            name: "app_ne_bvar".to_string(),
            type_src: "forall (f : KExpr) (a : KExpr) (i : Nat) (C : Type), Eq KExpr (KExpr.app f a) (KExpr.bvar i) -> C".to_string(),
            value_src: Some(format!(
                "fun (f : KExpr) (a : KExpr) (i : Nat) (C : Type) (h : Eq KExpr (KExpr.app f a) (KExpr.bvar i)) => Empty.rec (fun (_ : Empty) => C) (Eq.substType KExpr {d} (KExpr.app f a) (KExpr.bvar i) h Nat.zero)",
                d = kexpr_not_bvar,
            )),
            is_axiom: false,
            description: "App f a != bvar i discrimination (produces any C). DerivedProved via the bvar-Empty discriminator + Eq.substType + Empty.rec. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string(), "Eq.substType".to_string(), "Empty.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "lam_ne_bvar".to_string(),
            type_src: "forall (ty : KExpr) (b : KExpr) (i : Nat) (C : Type), Eq KExpr (KExpr.lam ty b) (KExpr.bvar i) -> C".to_string(),
            value_src: Some(format!(
                "fun (ty : KExpr) (b : KExpr) (i : Nat) (C : Type) (h : Eq KExpr (KExpr.lam ty b) (KExpr.bvar i)) => Empty.rec (fun (_ : Empty) => C) (Eq.substType KExpr {d} (KExpr.lam ty b) (KExpr.bvar i) h Nat.zero)",
                d = kexpr_not_bvar,
            )),
            is_axiom: false,
            description: "Lam ty b != bvar i discrimination (produces any C). DerivedProved via the bvar-Empty discriminator + Eq.substType + Empty.rec. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string(), "Eq.substType".to_string(), "Empty.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "pi_ne_bvar".to_string(),
            type_src: "forall (dom : KExpr) (b : KExpr) (i : Nat) (C : Type), Eq KExpr (KExpr.pi dom b) (KExpr.bvar i) -> C".to_string(),
            value_src: Some(format!(
                "fun (dom : KExpr) (b : KExpr) (i : Nat) (C : Type) (h : Eq KExpr (KExpr.pi dom b) (KExpr.bvar i)) => Empty.rec (fun (_ : Empty) => C) (Eq.substType KExpr {d} (KExpr.pi dom b) (KExpr.bvar i) h Nat.zero)",
                d = kexpr_not_bvar,
            )),
            is_axiom: false,
            description: "Pi dom b != bvar i discrimination (produces any C). DerivedProved via the bvar-Empty discriminator + Eq.substType + Empty.rec. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string(), "Eq.substType".to_string(), "Empty.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "let_ne_bvar".to_string(),
            type_src: "forall (ty : KExpr) (v : KExpr) (b : KExpr) (i : Nat) (C : Type), Eq KExpr (KExpr.let_ ty v b) (KExpr.bvar i) -> C".to_string(),
            value_src: Some(format!(
                "fun (ty : KExpr) (v : KExpr) (b : KExpr) (i : Nat) (C : Type) (h : Eq KExpr (KExpr.let_ ty v b) (KExpr.bvar i)) => Empty.rec (fun (_ : Empty) => C) (Eq.substType KExpr {d} (KExpr.let_ ty v b) (KExpr.bvar i) h Nat.zero)",
                d = kexpr_not_bvar,
            )),
            is_axiom: false,
            description: "Let_ ty v b != bvar i discrimination (produces any C). Let-promotion increment (task #28). DerivedProved via the bvar-Empty discriminator + Eq.substType + Empty.rec. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string(), "Eq.substType".to_string(), "Empty.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "proj_ne_bvar".to_string(),
            type_src: "forall (s : Name) (i : Nat) (sub : KExpr) (j : Nat) (C : Type), Eq KExpr (KExpr.proj s i sub) (KExpr.bvar j) -> C".to_string(),
            value_src: Some(format!(
                "fun (s : Name) (i : Nat) (sub : KExpr) (j : Nat) (C : Type) (h : Eq KExpr (KExpr.proj s i sub) (KExpr.bvar j)) => Empty.rec (fun (_ : Empty) => C) (Eq.substType KExpr {d} (KExpr.proj s i sub) (KExpr.bvar j) h Nat.zero)",
                d = kexpr_not_bvar,
            )),
            is_axiom: false,
            description: "Proj s i sub != bvar j discrimination (produces any C). Proj/lit fragment rung. DerivedProved via the bvar-Empty discriminator + Eq.substType + Empty.rec. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["KExpr.rec".to_string(), "Eq.substType".to_string(), "Empty.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // The CandModel mk-case binder (the 11-field (redLet + Nat.rec redNatRec) telescope, incl. the
        // let-increment redLet), shared by every
        // field projection via CandModel.rec. Its field types reference the bound
        // `Red`, so on the `mk` constructor cm_Red reduces to `Red` and every
        // projection's motive-goal reduces to that field's type. Guide's `M.Red`
        // / CR1 / CR2 / CR3 / redAbstraction accessors (§8/§8a).
        let cm_tel = |body: &str| {
            format!(concat!(
            "(fun (Red : KExpr -> KExpr -> Type) ",
            "(cr1 : forall (T : KExpr) (e : KExpr), Red T e -> whnf_acc e) ",
            "(cr2 : forall (T : KExpr) (e : KExpr) (e2 : KExpr), Red T e -> whnf_step e e2 -> Red T e2) ",
            "(cr3 : forall (T : KExpr) (e : KExpr), Neutral e -> (forall (e2 : KExpr), whnf_step e e2 -> Red T e2) -> Red T e) ",
            "(red_sort : forall (n : Level) (e : KExpr), whnf_acc e -> Red (KExpr.sort n) e) ",
            "(pi_elim : forall (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr), Red (KExpr.pi A B) f -> Red A a -> Red (instantiate B a) (KExpr.app f a)) ",
            "(pi_intro : forall (A : KExpr) (B : KExpr) (f : KExpr), (forall (a : KExpr), Red A a -> Red (instantiate B a) (KExpr.app f a)) -> Red (KExpr.pi A B) f) ",
            "(redAbstraction : forall (A : KExpr) (b : KExpr) (B : KExpr), whnf_acc A -> (forall (a : KExpr), Red A a -> Red (instantiate B a) (instantiate b a)) -> forall (a : KExpr), Red A a -> Red (instantiate B a) (KExpr.app (KExpr.lam A b) a)) ",
            "(redConst : forall (n : Name) (us : ListType Level) (A : KExpr) (s : Nat -> KExpr), Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> Red (psubst s A) (KExpr.const n us)) ",
            "(redLet : forall (A : KExpr) (b : KExpr) (B : KExpr), whnf_acc A -> (forall (a : KExpr), Red A a -> Red (instantiate B a) (instantiate b a)) -> forall (a : KExpr), Red A a -> Red (instantiate B a) (KExpr.let_ A a b)) ",
            "(redRecGen : forall (fam : Name) (sig : ListType Nat) (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (ms : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), GenFresh fam sig denv -> GenRecEnvOK fam sig u renv -> GenRecContract fam sig u (genRecApp fam sig u m ms t) contractum -> whnf_acc m -> WhnfAccAll ms -> whnf_acc t -> Red T contractum -> Red T (genRecApp fam sig u m ms t)) ",
            "(redRecW : forall (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (mn : KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), WFresh denv -> WRecEnvOK u renv -> WRecContract u (wRecApp u m mn t) contractum -> whnf_acc m -> whnf_acc mn -> whnf_acc t -> Red T contractum -> Red T (wRecApp u m mn t)) (redRecMut : forall (msig : ListType FamSpec) (u : Level) (i : Nat) (denv : DefEnv) (renv : RecEnv) (cs : ListType KExpr) (ms : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), MutFresh msig denv -> MutRecEnvOK msig u renv -> MutRecContract msig u (mutRecApp msig u i cs ms t) contractum -> WhnfAccAll cs -> WhnfAccAll ms -> whnf_acc t -> Red T contractum -> Red T (mutRecApp msig u i cs ms t)) (redRecIdx : forall (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (ms : ListType KExpr) (ix : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), IGenFresh fam isig denv -> IGenRecEnvOK iFam fam nIdx isig u renv -> IGenRecContract fam nIdx isig u (iRecApp fam isig u m ms ix t) contractum -> whnf_acc m -> WhnfAccAll ms -> WhnfAccAll ix -> whnf_acc t -> Red T contractum -> Red T (iRecApp fam isig u m ms ix t)) (redTypeStep : forall (T : KExpr) (T2 : KExpr) (e : KExpr), whnf_step T T2 -> AndType (Red T e -> Red T2 e) (Red T2 e -> Red T e)) => {body})"
        ), body = body)
        };

        // cm_Red tenv M : the reducibility family Red of a CandModel (the guide's
        // `M.Red`). CandModel.rec projection with a constant Type-1 motive; on `mk`
        // it iota-reduces to the stored Red. Registered via add_recursive_def so it
        // is a SEMIREDUCIBLE `def` (NOT Opaque) — the field accessors CR1-3 /
        // redAbstraction_holds and red_var must UNFOLD cm_Red to reduce
        // `cm_Red (mk ..) = Red` during their CandModel.rec minor-premise check.
        // All downstream (red_var, Models, fundamental) phrase reducibility via cm_Red.
        self.add_recursive_def(
            &format!(
                "def cm_Red (tenv : Name -> OptionType KExpr) (M : CandModel tenv) : KExpr -> KExpr -> Type := CandModel.rec tenv (fun (M0 : CandModel tenv) => KExpr -> KExpr -> Type) {tel} M",
                tel = cm_tel("Red"),
            ),
            "cm_Red tenv M : the reducibility family Red of a CandModel (guide's M.Red). CandModel.rec projection (constant Type-1 motive); reduces to the stored Red on mk. Semireducible def so the field accessors + red_var/Models can unfold it. Zero axiom_deps.",
        )?;

        // CR1 : reducible => strongly normalizing (guide CR1 accessor). Projects
        // the cr1 field; on mk the goal reduces (cm_Red (mk ..) = Red) to cr1's type.
        self.add_definition_structural(SpecDefinition {
            name: "CR1".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (T : KExpr) (e : KExpr), cm_Red tenv M T e -> whnf_acc e".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => forall (T : KExpr) (e : KExpr), cm_Red tenv M0 T e -> whnf_acc e) {tel} M",
                tel = cm_tel("cr1"),
            )),
            is_axiom: false,
            description: "CR1 accessor: cm_Red tenv M T e -> whnf_acc e (reducible => SN). CandModel.rec projection of the cr1 field. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["CandModel.rec".to_string(), "cm_Red".to_string(), "whnf_acc".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // CR2 : reducibility is preserved by reduction (guide CR2 accessor).
        self.add_definition_structural(SpecDefinition {
            name: "CR2".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (T : KExpr) (e : KExpr) (e2 : KExpr), cm_Red tenv M T e -> whnf_step e e2 -> cm_Red tenv M T e2".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => forall (T : KExpr) (e : KExpr) (e2 : KExpr), cm_Red tenv M0 T e -> whnf_step e e2 -> cm_Red tenv M0 T e2) {tel} M",
                tel = cm_tel("cr2"),
            )),
            is_axiom: false,
            description: "CR2 accessor: cm_Red T e -> whnf_step e e2 -> cm_Red T e2 (closed under reduction). CandModel.rec projection of the cr2 field. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["CandModel.rec".to_string(), "cm_Red".to_string(), "whnf_step".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // CR3 : a neutral term all of whose reducts are reducible is reducible
        // (guide CR3 accessor). The vacuous-neutral engine behind red_var.
        self.add_definition_structural(SpecDefinition {
            name: "CR3".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (T : KExpr) (e : KExpr), Neutral e -> (forall (e2 : KExpr), whnf_step e e2 -> cm_Red tenv M T e2) -> cm_Red tenv M T e".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => forall (T : KExpr) (e : KExpr), Neutral e -> (forall (e2 : KExpr), whnf_step e e2 -> cm_Red tenv M0 T e2) -> cm_Red tenv M0 T e) {tel} M",
                tel = cm_tel("cr3"),
            )),
            is_axiom: false,
            description: "CR3 accessor: Neutral e -> (forall e2, whnf_step e e2 -> cm_Red T e2) -> cm_Red T e. CandModel.rec projection of the cr3 field. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["CandModel.rec".to_string(), "cm_Red".to_string(), "Neutral".to_string(), "whnf_step".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // RedAbstraction tenv M : the Tait weak-head-expansion (abstraction) law as
        // a named proposition over cm_Red (guide RedAbstraction, line 1844). A plain
        // reducible def so redAbstraction_holds : RedAbstraction and the fundamental
        // lam case can apply it directly.
        self.add_recursive_def(
            "def RedAbstraction (tenv : Name -> OptionType KExpr) (M : CandModel tenv) : Type := forall (A : KExpr) (b : KExpr) (B : KExpr), whnf_acc A -> (forall (a : KExpr), cm_Red tenv M A a -> cm_Red tenv M (instantiate B a) (instantiate b a)) -> forall (a : KExpr), cm_Red tenv M A a -> cm_Red tenv M (instantiate B a) (KExpr.app (KExpr.lam A b) a)",
            "RedAbstraction tenv M : the Tait/Girard weak-head-expansion (abstraction) closure law over cm_Red. Guide's RedAbstraction (line 1844). Reducible def; the sole candidate-model input to the fundamental lam case.",
        )?;

        // redAbstraction_holds M : RedAbstraction M := M.redAbstraction — the trivial
        // projection of the CandModel redAbstraction field (guide line 1886). On mk
        // the goal RedAbstraction (mk ..) unfolds + reduces (cm_Red (mk ..) = Red) to
        // exactly the redAbstraction field's type.
        self.add_definition_structural(SpecDefinition {
            name: "redAbstraction_holds".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv), RedAbstraction tenv M".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => RedAbstraction tenv M0) {tel} M",
                tel = cm_tel("redAbstraction"),
            )),
            is_axiom: false,
            description: "redAbstraction_holds M : RedAbstraction M := M.redAbstraction. Trivial CandModel.rec projection of the redAbstraction field (guide line 1886). The sole candidate-model input to the fundamental lam case. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["CandModel.rec".to_string(), "RedAbstraction".to_string(), "cm_Red".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // RedLet tenv M : the zeta weak-head-expansion closure law over cm_Red —
        // the let_ analogue of RedAbstraction, in EXACTLY the same shape (zeta
        // enters the candidates exactly the way beta does). Guide's RedLet
        // (SnLet.lean:2077). Let-promotion increment (task #28).
        self.add_recursive_def(
            "def RedLet (tenv : Name -> OptionType KExpr) (M : CandModel tenv) : Type := forall (A : KExpr) (b : KExpr) (B : KExpr), whnf_acc A -> (forall (a : KExpr), cm_Red tenv M A a -> cm_Red tenv M (instantiate B a) (instantiate b a)) -> forall (a : KExpr), cm_Red tenv M A a -> cm_Red tenv M (instantiate B a) (KExpr.let_ A a b)",
            "RedLet tenv M : the zeta weak-head-expansion closure law over cm_Red — the let_ analogue of RedAbstraction (zeta enters the candidates exactly the way beta does). Guide's RedLet (SnLet.lean:2077). Reducible def; the sole candidate-model input to the fundamental let case. Let-promotion increment (task #28).",
        )?;

        // redLet_holds M : RedLet M := M.redLet — the trivial CandModel.rec
        // projection of the redLet field (guide redLet_holds, SnLet.lean:2084).
        // On mk the goal RedLet (mk ..) unfolds + reduces (cm_Red (mk ..) = Red)
        // to exactly the redLet field's type.
        self.add_definition_structural(SpecDefinition {
            name: "redLet_holds".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv), RedLet tenv M".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => RedLet tenv M0) {tel} M",
                tel = cm_tel("redLet"),
            )),
            is_axiom: false,
            description: "redLet_holds M : RedLet M := M.redLet. Trivial CandModel.rec projection of the redLet field (guide SnLet.lean:2084). The sole candidate-model input to the fundamental let case. Let-promotion increment (task #28). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["CandModel.rec".to_string(), "RedLet".to_string(), "cm_Red".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // ── N3/B5 (recursor projection): RedNatRec (the Nat field type over cm_Red,
        // KEPT as the consumer-facing statement) + RedRecGen (the NEW generic field
        // type) + redRecGen_holds (projects the generic redRecGen field) +
        // redNatRec_holds (RE-BODIED: same name+type as before, but now DERIVES the
        // Nat.rec adequacy from the generic field via redRecGen_holds at
        // (natName, sigNat) — natFresh_to_genFresh / natRecEnvOK_to_gen /
        // natContract_to_gen bridges + whnfAccAll_cons2 for ms=[z,s]; the conclusion
        // Red T (genRecApp natName sigNat u m [z,s] t) is defeq to
        // Red T (natRecApp u m z s t) via genRecApp_nat/rfl). The 2 consumers in
        // natRec_adequacy_numeral are unchanged (they only apply redNatRec_holds and
        // depend on its TYPE). Zero domain axioms; census-neutral.
        self.add_recursive_def(
            "def RedNatRec (tenv : Name -> OptionType KExpr) (M : CandModel tenv) : Type := forall (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (z : KExpr) (s : KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), NatFresh denv -> NatRecEnvOK u renv -> NatRecContract u (natRecApp u m z s t) contractum -> whnf_acc m -> whnf_acc z -> whnf_acc s -> whnf_acc t -> cm_Red tenv M T contractum -> cm_Red tenv M T (natRecApp u m z s t)",
            "RedNatRec tenv M: the object-level-iota weak-head-expansion closure law over cm_Red — the Nat.rec analogue of RedLet. Now a DERIVED consequence of RedRecGen (redNatRec_holds re-body). Nat.rec port N3.",
        )?;
        self.add_recursive_def(
            "def RedRecGen (tenv : Name -> OptionType KExpr) (M : CandModel tenv) : Type := forall (fam : Name) (sig : ListType Nat) (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (ms : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), GenFresh fam sig denv -> GenRecEnvOK fam sig u renv -> GenRecContract fam sig u (genRecApp fam sig u m ms t) contractum -> whnf_acc m -> WhnfAccAll ms -> whnf_acc t -> cm_Red tenv M T contractum -> cm_Red tenv M T (genRecApp fam sig u m ms t)",
            "RedRecGen tenv M: the GENERIC object-level-iota weak-head-expansion closure over cm_Red for the whole signature schema (fam, sig) — the single candidate-model recursor-adequacy field, generalizing RedNatRec. SnSchema B5.",
        )?;
        // redRecGen_holds: trivial CandModel.rec projection of the generic redRecGen
        // field (on mk, cm_Red (mk ..) = Red reduces the goal to the field's type).
        self.add_definition_structural(SpecDefinition {
            name: "redRecGen_holds".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv), RedRecGen tenv M".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => RedRecGen tenv M0) {tel} M",
                tel = cm_tel("redRecGen"),
            )),
            is_axiom: false,
            description: "redRecGen_holds M : RedRecGen M := M.redRecGen. Trivial CandModel.rec projection of the generic redRecGen field — the single candidate-model recursor-adequacy input for the whole signature schema. SnSchema B5. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CandModel.rec".to_string(),
                "RedRecGen".to_string(),
                "cm_Red".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        // W-type (higher-order fields) recursor adequacy. NOT derivable from
        // RedRecGen: wContractum embeds the recursor-built IH FUNCTION wIhFun
        // (a minor applied under a binder), which the first-order GenRecContract
        // cannot express — mutual_schema.rs's mutRecApp_deg/mutContractum_deg_succ
        // show the degeneracy arrow points from the general shape TO the generic
        // one, so the generic field is the special case and cannot imply this.
        // Hence a genuinely NEW CandModel field alongside redRecGen (same as
        // redLet and redRecGen themselves were): census-NEUTRAL, since it is a
        // constructor-telescope entry, not an axiom. It does STRENGTHEN the
        // CandModel hypothesis, which is the honest cost and is already the
        // labeled Gödel-floor assumption. Guide: AccWTypeSN.lean:1128-1132
        // (redRecW field) and :1169-1176 (redRecW_holds).
        self.add_recursive_def(
            "def RedRecW (tenv : Name -> OptionType KExpr) (M : CandModel tenv) : Type := forall (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (mn : KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), WFresh denv -> WRecEnvOK u renv -> WRecContract u (wRecApp u m mn t) contractum -> whnf_acc m -> whnf_acc mn -> whnf_acc t -> cm_Red tenv M T contractum -> cm_Red tenv M T (wRecApp u m mn t)",
            "RedRecW tenv M: the W-shaped (higher-order-field) object-level-iota weak-head-expansion closure over cm_Red — the wRec analogue of RedRecGen, gated on WFresh/WRecEnvOK so it is vacuous off-target. Not an instance of RedRecGen: the W contractum carries an IH function under a binder. AccWType adequacy Phase 1.",
        )?;
        // RedRecMut / redRecMut_holds — the MUTUAL-block analogue of
        // RedRecW/redRecW_holds. Uses the spec's WhnfAccAll idiom for the
        // ctor/minor lists, NOT the guide's `forall x, MemL x cs -> ...`:
        // MemL is registered in the LATE add_snschema (stage 132), so a literal
        // transcription into a stage-78 telescope fails with "Unknown
        // identifier: MemL". redRecGen already uses WhnfAccAll for the same
        // reason (schema.rs documents them as equivalent).
        self.add_recursive_def(
            "def RedRecMut (tenv : Name -> OptionType KExpr) (M : CandModel tenv) : Type := forall (msig : ListType FamSpec) (u : Level) (i : Nat) (denv : DefEnv) (renv : RecEnv) (cs : ListType KExpr) (ms : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), MutFresh msig denv -> MutRecEnvOK msig u renv -> MutRecContract msig u (mutRecApp msig u i cs ms t) contractum -> WhnfAccAll cs -> WhnfAccAll ms -> whnf_acc t -> cm_Red tenv M T contractum -> cm_Red tenv M T (mutRecApp msig u i cs ms t)",
            "RedRecMut tenv M: the mutual-block object-level-iota weak-head-expansion closure over cm_Red, carrying MutFresh/MutRecEnvOK premises. NOTE: denv/renv are quantified INSIDE the field and occur only in those premises, never in the conclusion, so they do NOT restrict which candidate models satisfy it (an instantiator may take denv := DefEnv.empty). Do not describe this as vacuous off-target. Not an instance of RedRecGen: mutRecApp/mutContractum are the K-family generalization of which genRecApp/genContractum are the degenerate single-family case (mutual_schema.rs proves that direction), so the arrow points the wrong way to derive it. MutSchema adequacy Phase 1.",
        )?;
        // RedRecIdx / redRecIdx_holds — the INDEXED-family analogue, third and
        // last of the recursor-adequacy fields (redRecGen first-order,
        // redRecW higher-order, redRecMut mutual, redRecIdx indexed).
        // Statable only because the indexed object layer landed in
        // add_snschema_objects; before that its type had no referents.
        self.add_recursive_def(
            "def RedRecIdx (tenv : Name -> OptionType KExpr) (M : CandModel tenv) : Type := forall (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (ms : ListType KExpr) (ix : ListType KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr), IGenFresh fam isig denv -> IGenRecEnvOK iFam fam nIdx isig u renv -> IGenRecContract fam nIdx isig u (iRecApp fam isig u m ms ix t) contractum -> whnf_acc m -> WhnfAccAll ms -> WhnfAccAll ix -> whnf_acc t -> cm_Red tenv M T contractum -> cm_Red tenv M T (iRecApp fam isig u m ms ix t)",
            "RedRecIdx tenv M: the indexed-family object-level-iota weak-head-expansion closure over cm_Red, carrying IGenFresh/IGenRecEnvOK premises. NOTE: denv/renv are quantified INSIDE the field and occur only in those premises, never in the conclusion, so they do NOT restrict which candidate models satisfy it. Do not describe this as vacuous off-target. Uses WhnfAccAll for the minor/index list SN hypotheses (the guide's MemL phrasing is not in scope at this stage). Indexed adequacy Phase 1.",
        )?;

        // RedTypeStep / redTypeStep_holds — the conversion-transport law
        // (guide AccWTypeSN.lean:1136). Candidates respect ONE whnf step of the
        // TYPE index, in BOTH directions; the guide states it as an Iff and uses
        // .mp and .mpr in different places, so here it is an AndType of the two
        // implications (the spec has no Iff).
        //
        // TRUST NOTE: this ADDS a clause to CandModel, which is the labeled
        // Godel-floor hypothesis. CandModel therefore becomes a STRICTLY
        // STRONGER assumption, and every CandModel-conditional theorem in the
        // spec now assumes marginally more than it did before, without its
        // printed statement changing. That is a real (if small) trust cost, paid
        // deliberately: the law is standard for reducibility candidates
        // (a whnf-class-indexed model validates it), it is of a piece with the
        // ten closure fields CandModel already carries (cr1-3, pi_intro/elim,
        // redAbstraction, redConst, redLet, redRecGen, redRecW), and the guide
        // carries it as a field for the same reason.
        self.add_recursive_def(
            "def RedTypeStep (tenv : Name -> OptionType KExpr) (M : CandModel tenv) : Type := forall (T : KExpr) (T2 : KExpr) (e : KExpr), whnf_step T T2 -> AndType (cm_Red tenv M T e -> cm_Red tenv M T2 e) (cm_Red tenv M T2 e -> cm_Red tenv M T e)",
            "RedTypeStep tenv M: the type of the CandModel FIELD redTypeStep (adding it made CandModel a strictly stronger hypothesis for every CandModel-conditional theorem in the spec) -- the candidates-respect-conversion law over cm_Red — reducibility transports along ONE whnf step of the TYPE index, in both directions. Guide AccWTypeSN.lean:1136 states it as an Iff; encoded here as an AndType of the two implications. Consumed by minorUseW_motive_step and w_adequacy_stuck.",
        )?;

        // redTypeStep_holds: trivial CandModel.rec projection of the
        // redTypeStep field, exactly as redRecW_holds projects redRecW.
        self.add_definition_structural(SpecDefinition {
            name: "redTypeStep_holds".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv), RedTypeStep tenv M".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => RedTypeStep tenv M0) {tel} M",
                tel = cm_tel("redTypeStep"),
            )),
            is_axiom: false,
            description: "redTypeStep_holds M : RedTypeStep M := M.redTypeStep. Trivial CandModel.rec projection of the conversion-transport field. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CandModel.rec".to_string(),
                "RedTypeStep".to_string(),
                "cm_Red".to_string(),
                "AndType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // redRecW_holds: trivial CandModel.rec projection of the redRecW field,
        // exactly as redRecGen_holds projects redRecGen.
        self.add_definition_structural(SpecDefinition {
            name: "redRecW_holds".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv), RedRecW tenv M".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => RedRecW tenv M0) {tel} M",
                tel = cm_tel("redRecW"),
            )),
            is_axiom: false,
            description: "redRecW_holds M : RedRecW M := M.redRecW. Trivial CandModel.rec projection of the W-type recursor-adequacy field — the candidate-model input for higher-order (W/Acc) iota adequacy. AccWType adequacy Phase 1. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CandModel.rec".to_string(),
                "RedRecW".to_string(),
                "cm_Red".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        // redRecMut_holds: trivial CandModel.rec projection of the redRecMut
        // field, exactly as redRecW_holds projects redRecW. Kept GENERIC over
        // denv/renv (the spec idiom) rather than specialized to mutREnv like the
        // guide's version — the concrete env-witness discharge belongs in the
        // adequacy consumer, which is also where the still-unported mutREnv_ok
        // will be needed.
        self.add_definition_structural(SpecDefinition {
            name: "redRecMut_holds".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv), RedRecMut tenv M".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => RedRecMut tenv M0) {tel} M",
                tel = cm_tel("redRecMut"),
            )),
            is_axiom: false,
            description: "redRecMut_holds M : RedRecMut M := M.redRecMut. Trivial CandModel.rec projection of the mutual-block recursor-adequacy field. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CandModel.rec".to_string(),
                "RedRecMut".to_string(),
                "cm_Red".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        // redRecIdx_holds: CandModel.rec projection of the redRecIdx field,
        // mirroring redRecW_holds / redRecMut_holds. Generic over denv/renv.
        self.add_definition_structural(SpecDefinition {
            name: "redRecIdx_holds".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv), RedRecIdx tenv M".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => RedRecIdx tenv M0) {tel} M",
                tel = cm_tel("redRecIdx"),
            )),
            is_axiom: false,
            description: "redRecIdx_holds M : RedRecIdx M := M.redRecIdx. Trivial CandModel.rec projection of the indexed recursor-adequacy field. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CandModel.rec".to_string(),
                "RedRecIdx".to_string(),
                "cm_Red".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // redNatRec_holds: RE-BODIED. Same name+type (RedNatRec), but derives the Nat
        // adequacy from the generic redRecGen field at (natName, sigNat, ms=[z,s]).
        self.add_definition_structural(SpecDefinition {
            name: "redNatRec_holds".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv), RedNatRec tenv M".to_string(),
            value_src: Some(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => fun (u : Level) (denv : DefEnv) (renv : RecEnv) (m : KExpr) (z : KExpr) (s : KExpr) (t : KExpr) (contractum : KExpr) (T : KExpr) (hf : NatFresh denv) (hok : NatRecEnvOK u renv) (hc : NatRecContract u (natRecApp u m z s t) contractum) (hm : whnf_acc m) (hz : whnf_acc z) (hs : whnf_acc s) (ht : whnf_acc t) (hred : cm_Red tenv M T contractum) => redRecGen_holds tenv M natName sigNat u denv renv m (ListType.cons KExpr z (ListType.cons KExpr s (ListType.nil KExpr))) t contractum T (natFresh_to_genFresh denv hf) (natRecEnvOK_to_gen u renv hok) (natContract_to_gen u (natRecApp u m z s t) contractum hc) hm (whnfAccAll_cons2 z s hz hs) ht hred".to_string(),
            ),
            is_axiom: false,
            description: "redNatRec_holds M : RedNatRec M. DERIVED from the generic redRecGen field (redRecGen_holds at natName/sigNat/ms=[z,s]) — natFresh_to_genFresh/natRecEnvOK_to_gen/natContract_to_gen bridges + whnfAccAll_cons2; genRecApp natName sigNat u m [z,s] t ≡ natRecApp u m z s t by rfl. The sole candidate-model input to natRec_adequacy_numeral (consumers unchanged). SnSchema B5. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "redRecGen_holds".to_string(),
                "RedNatRec".to_string(),
                "RedRecGen".to_string(),
                "cm_Red".to_string(),
                "natFresh_to_genFresh".to_string(),
                "natRecEnvOK_to_gen".to_string(),
                "natContract_to_gen".to_string(),
                "whnfAccAll_cons2".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // no_whnf_step_bvar : a bound variable admits NO whnf_step (guide line 848),
        // producing any C. whnf_step.rec dispatch: the delta arm is const-head-none
        // absurd; the beta arm inverts beta_reduces on a bvar source (beta_reduces.rec
        // with a source-eq motive) — every canonical arm is app/lam/pi != bvar absurd,
        // and the lone iota arm (arbitrary source) is const-head-none absurd after
        // substituting the source = bvar i.
        self.add_definition_structural(SpecDefinition {
            name: "no_whnf_step_bvar".to_string(),
            type_src: "forall (i : Nat) (e2 : KExpr) (C : Type), whnf_step (KExpr.bvar i) e2 -> C".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (e2 : KExpr) (C : Type) (hs : whnf_step (KExpr.bvar i) e2) => ",
                "whnf_step.rec (KExpr.bvar i) e2 (fun (_ : whnf_step (KExpr.bvar i) e2) => C) ",
                "(fun (hbr : beta_reduces (KExpr.bvar i) e2) => ",
                "beta_reduces.rec (fun (s : KExpr) (t : KExpr) (_hbr : beta_reduces s t) => Eq KExpr s (KExpr.bvar i) -> C) ",
                // beta
                "(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) (KExpr.bvar i)) => app_ne_bvar (KExpr.lam A0 body) arg i C heq) ",
                // app_left
                "(fun (f : KExpr) (f2 : KExpr) (a : KExpr) (_hstep : beta_reduces f f2) (_ih : Eq KExpr f (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.app f a) (KExpr.bvar i)) => app_ne_bvar f a i C heq) ",
                // app_right
                "(fun (f : KExpr) (a : KExpr) (a2 : KExpr) (_hstep : beta_reduces a a2) (_ih : Eq KExpr a (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.app f a) (KExpr.bvar i)) => app_ne_bvar f a i C heq) ",
                // lam_ty
                "(fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.bvar i)) => lam_ne_bvar ty body i C heq) ",
                // lam_body
                "(fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.bvar i)) => lam_ne_bvar ty body i C heq) ",
                // pi_dom
                "(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.pi dom body) (KExpr.bvar i)) => pi_ne_bvar dom body i C heq) ",
                // pi_cod
                "(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.pi dom body) (KExpr.bvar i)) => pi_ne_bvar dom body i C heq) ",
                // forall_congr_dom
                "(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.forall_ dom body) (KExpr.bvar i)) => pi_ne_bvar dom body i C heq) ",
                // forall_congr_cod
                "(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.forall_ dom body) (KExpr.bvar i)) => pi_ne_bvar dom body i C heq) ",
                // zeta (let increment: source let_ != bvar)
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.bvar i)) => let_ne_bvar ty val body i C heq) ",
                // let_ty
                "(fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.bvar i)) => let_ne_bvar ty val body i C heq) ",
                // let_val
                "(fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hstep : beta_reduces val val2) (_ih : Eq KExpr val (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.bvar i)) => let_ne_bvar ty val body i C heq) ",
                // let_body
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.bvar i)) => let_ne_bvar ty val body i C heq) ",
                // iota
                "(fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : Eq KExpr e0 (KExpr.bvar i)) => iota_step_head_none_absurd_type (red_rec the_red_env) (KExpr.bvar i) e02 C (Eq.refl (OptionType Name) (OptionType.none Name)) (iota_reduces_to_step (KExpr.bvar i) e02 (Eq.substType KExpr (fun (w : KExpr) => iota_reduces w e02) e0 (KExpr.bvar i) heq hiota))) ",
                // proj (proj/lit rung: source proj != bvar)
                "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub2 : KExpr) (_hstep : beta_reduces sub sub2) (_ih : Eq KExpr sub (KExpr.bvar i) -> C) (heq : Eq KExpr (KExpr.proj ps pidx sub) (KExpr.bvar i)) => proj_ne_bvar ps pidx sub i C heq) ",
                "(KExpr.bvar i) e2 hbr (Eq.refl KExpr (KExpr.bvar i))) ",
                "(fun (hdr : delta_reduces (KExpr.bvar i) e2) => ",
                "delta_step_head_none_absurd_type (red_def the_red_env) (KExpr.bvar i) e2 C (Eq.refl (OptionType Name) (OptionType.none Name)) (delta_reduces_to_step (KExpr.bvar i) e2 hdr)) ",
                "hs",
            ).to_string()),
            is_axiom: false,
            description: "A bound variable admits no whnf_step (guide line 848), producing any C. DerivedProved via whnf_step.rec: delta arm const-head-none absurd; beta arm inverts beta_reduces on a bvar source (all canonical/congruence arms app/lam/pi/let != bvar absurd — zeta + the three let congruences via let_ne_bvar — iota arm const-head-none absurd). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step.rec".to_string(), "beta_reduces.rec".to_string(),
                "app_ne_bvar".to_string(), "lam_ne_bvar".to_string(), "pi_ne_bvar".to_string(), "let_ne_bvar".to_string(), "proj_ne_bvar".to_string(),
                "iota_step_head_none_absurd_type".to_string(), "delta_step_head_none_absurd_type".to_string(),
                "iota_reduces_to_step".to_string(), "delta_reduces_to_step".to_string(),
                "red_rec".to_string(), "red_def".to_string(), "the_red_env".to_string(),
                "Eq.substType".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // red_var M T i : every variable is reducible at every type (guide red_var,
        // line 861). bvar i is Neutral (ConstFreeUnit.triv) and irreducible
        // (no_whnf_step_bvar), so CR3 applies vacuously.
        self.add_definition_structural(SpecDefinition {
            name: "red_var".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (T : KExpr) (i : Nat), cm_Red tenv M T (KExpr.bvar i)".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (T : KExpr) (i : Nat) => ",
                "CR3 tenv M T (KExpr.bvar i) ConstFreeUnit.triv ",
                "(fun (e2 : KExpr) (hstep : whnf_step (KExpr.bvar i) e2) => no_whnf_step_bvar i e2 (cm_Red tenv M T e2) hstep)",
            ).to_string()),
            is_axiom: false,
            description: "red_var M T i : every variable is reducible at every type (guide line 861). bvar i is Neutral (ConstFreeUnit.triv) and irreducible (no_whnf_step_bvar), so CR3 applies vacuously. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CR3".to_string(), "cm_Red".to_string(), "Neutral".to_string(),
                "ConstFreeUnit".to_string(), "no_whnf_step_bvar".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnfAcc_sort n : sorts are strongly normalizing (guide whnfAcc_sort, line
        // 869). Reuses the ALREADY-PROVEN degenerate theorem: sort n : sort (succ n)
        // is typable (Typing.sort n : has_type), so whnf_terminates_well_typed
        // delivers its whnf_acc directly (terminates_whnf = whnf_acc, reducible alias).
        self.add_definition_structural(SpecDefinition {
            name: "whnfAcc_sort".to_string(),
            type_src: "forall (n : Level), whnf_acc (KExpr.sort n)".to_string(),
            value_src: Some(
                "fun (n : Level) => whnf_terminates_well_typed (KExpr.sort n) (KExpr.sort (Level.succ n)) (Typing.sort n)".to_string(),
            ),
            is_axiom: false,
            description: "whnfAcc_sort n : whnf_acc (sort n) (guide line 869). Reuses the proven degenerate whnf_terminates_well_typed on the typable sort n : sort (succ n) (Typing.sort n); terminates_whnf = whnf_acc reducible alias. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_terminates_well_typed".to_string(), "Typing.sort".to_string(),
                "whnf_acc".to_string(), "terminates_whnf".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // WhnfStepPiInv A B e2 : the inversion witness for a whnf_step out of a
        // pi (guide whnfStep_pi_inv, line 1273) — either the domain stepped
        // (e2 = pi A2 B) or the codomain stepped (e2 = pi A B2). Two constructors.
        self.add_inductive(
            concat!(
                "inductive WhnfStepPiInv (A : KExpr) (B : KExpr) (e2 : KExpr) : Type\n",
                "| dom : forall (A2 : KExpr), whnf_step A A2 -> Eq KExpr e2 (KExpr.pi A2 B) -> WhnfStepPiInv A B e2\n",
                "| cod : forall (B2 : KExpr), whnf_step B B2 -> Eq KExpr e2 (KExpr.pi A B2) -> WhnfStepPiInv A B e2"
            ),
            "WhnfStepPiInv A B e2 (Brick 2 priority batch): the inversion witness for whnf_step (pi A B) e2 — dom (domain stepped, e2 = pi A2 B) or cod (codomain stepped, e2 = pi A B2). Guide's whnfStep_pi_inv disjunction (line 1273). Kernel generates WhnfStepPiInv.rec. ZERO new axioms.",
        )?;

        // whnfStep_pi_inv : inversion of a whnf_step out of a pi (guide line 1273).
        // whnf_step.rec dispatch: delta arm const-head-none absurd; beta arm inverts
        // beta_reduces on a pi source — pi_dom/pi_cod (and the forall_ aliases) give
        // the dom/cod witnesses via pi injectivity; the canonical redex arms
        // (beta/app/lam plus zeta + the three let congruences) are app/lam/let != pi
        // absurd (let arms via let_ne_pi); the iota arm is const-head-none absurd
        // after substituting the source = pi A B.
        self.add_definition_structural(SpecDefinition {
            name: "whnfStep_pi_inv".to_string(),
            type_src: "forall (A : KExpr) (B : KExpr) (e2 : KExpr), whnf_step (KExpr.pi A B) e2 -> WhnfStepPiInv A B e2".to_string(),
            value_src: Some(concat!(
                "fun (A : KExpr) (B : KExpr) (e2 : KExpr) (hs : whnf_step (KExpr.pi A B) e2) => ",
                "whnf_step.rec (KExpr.pi A B) e2 (fun (_ : whnf_step (KExpr.pi A B) e2) => WhnfStepPiInv A B e2) ",
                "(fun (hbr : beta_reduces (KExpr.pi A B) e2) => ",
                "beta_reduces.rec (fun (s : KExpr) (t : KExpr) (_hbr : beta_reduces s t) => Eq KExpr s (KExpr.pi A B) -> WhnfStepPiInv A B t) ",
                // beta A0 body arg -> instantiate body arg
                "(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) (KExpr.pi A B)) => app_ne_pi (KExpr.lam A0 body) arg A B (WhnfStepPiInv A B (instantiate body arg)) heq) ",
                // app_left f f2 a
                "(fun (f : KExpr) (f2 : KExpr) (a : KExpr) (_hstep : beta_reduces f f2) (_ih : Eq KExpr f (KExpr.pi A B) -> WhnfStepPiInv A B f2) (heq : Eq KExpr (KExpr.app f a) (KExpr.pi A B)) => app_ne_pi f a A B (WhnfStepPiInv A B (KExpr.app f2 a)) heq) ",
                // app_right f a a2
                "(fun (f : KExpr) (a : KExpr) (a2 : KExpr) (_hstep : beta_reduces a a2) (_ih : Eq KExpr a (KExpr.pi A B) -> WhnfStepPiInv A B a2) (heq : Eq KExpr (KExpr.app f a) (KExpr.pi A B)) => app_ne_pi f a A B (WhnfStepPiInv A B (KExpr.app f a2)) heq) ",
                // lam_ty ty ty2 body
                "(fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty (KExpr.pi A B) -> WhnfStepPiInv A B ty2) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.pi A B)) => lam_ne_pi ty body A B (WhnfStepPiInv A B (KExpr.lam ty2 body)) heq) ",
                // lam_body ty body body2
                "(fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.pi A B) -> WhnfStepPiInv A B body2) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.pi A B)) => lam_ne_pi ty body A B (WhnfStepPiInv A B (KExpr.lam ty body2)) heq) ",
                // pi_dom dom dom2 body  (REAL)
                "(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom (KExpr.pi A B) -> WhnfStepPiInv A B dom2) (heq : Eq KExpr (KExpr.pi dom body) (KExpr.pi A B)) => WhnfStepPiInv.dom A B (KExpr.pi dom2 body) dom2 (Eq.substType KExpr (fun (w : KExpr) => whnf_step w dom2) dom A (pi_inj_fst dom body A B heq) (whnf_step.beta dom dom2 hstep)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi dom2 w) body B (pi_inj_snd dom body A B heq))) ",
                // pi_cod dom body body2  (REAL)
                "(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.pi A B) -> WhnfStepPiInv A B body2) (heq : Eq KExpr (KExpr.pi dom body) (KExpr.pi A B)) => WhnfStepPiInv.cod A B (KExpr.pi dom body2) body2 (Eq.substType KExpr (fun (w : KExpr) => whnf_step w body2) body B (pi_inj_snd dom body A B heq) (whnf_step.beta body body2 hstep)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w body2) dom A (pi_inj_fst dom body A B heq))) ",
                // forall_congr_dom dom dom2 body  (REAL, forall_ source reduces to pi)
                "(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom (KExpr.pi A B) -> WhnfStepPiInv A B dom2) (heq : Eq KExpr (KExpr.forall_ dom body) (KExpr.pi A B)) => WhnfStepPiInv.dom A B (KExpr.pi dom2 body) dom2 (Eq.substType KExpr (fun (w : KExpr) => whnf_step w dom2) dom A (pi_inj_fst dom body A B heq) (whnf_step.beta dom dom2 hstep)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi dom2 w) body B (pi_inj_snd dom body A B heq))) ",
                // forall_congr_cod dom body body2  (REAL)
                "(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.pi A B) -> WhnfStepPiInv A B body2) (heq : Eq KExpr (KExpr.forall_ dom body) (KExpr.pi A B)) => WhnfStepPiInv.cod A B (KExpr.pi dom body2) body2 (Eq.substType KExpr (fun (w : KExpr) => whnf_step w body2) body B (pi_inj_snd dom body A B heq) (whnf_step.beta body body2 hstep)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w body2) dom A (pi_inj_fst dom body A B heq))) ",
                // zeta (let increment: source let_ != pi)
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.pi A B)) => let_ne_pi ty val body A B (WhnfStepPiInv A B (instantiate body val)) heq) ",
                // let_ty
                "(fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty (KExpr.pi A B) -> WhnfStepPiInv A B ty2) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.pi A B)) => let_ne_pi ty val body A B (WhnfStepPiInv A B (KExpr.let_ ty2 val body)) heq) ",
                // let_val
                "(fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hstep : beta_reduces val val2) (_ih : Eq KExpr val (KExpr.pi A B) -> WhnfStepPiInv A B val2) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.pi A B)) => let_ne_pi ty val body A B (WhnfStepPiInv A B (KExpr.let_ ty val2 body)) heq) ",
                // let_body
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.pi A B) -> WhnfStepPiInv A B body2) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.pi A B)) => let_ne_pi ty val body A B (WhnfStepPiInv A B (KExpr.let_ ty val body2)) heq) ",
                // iota e0 e02
                "(fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : Eq KExpr e0 (KExpr.pi A B)) => iota_step_head_none_absurd_type (red_rec the_red_env) (KExpr.pi A B) e02 (WhnfStepPiInv A B e02) (Eq.refl (OptionType Name) (OptionType.none Name)) (iota_reduces_to_step (KExpr.pi A B) e02 (Eq.substType KExpr (fun (w : KExpr) => iota_reduces w e02) e0 (KExpr.pi A B) heq hiota))) ",
                // proj (proj/lit rung: source proj != pi)
                "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub2 : KExpr) (_hstep : beta_reduces sub sub2) (_ih : Eq KExpr sub (KExpr.pi A B) -> WhnfStepPiInv A B sub2) (heq : Eq KExpr (KExpr.proj ps pidx sub) (KExpr.pi A B)) => proj_ne_pi ps pidx sub A B (WhnfStepPiInv A B (KExpr.proj ps pidx sub2)) heq) ",
                "(KExpr.pi A B) e2 hbr (Eq.refl KExpr (KExpr.pi A B))) ",
                "(fun (hdr : delta_reduces (KExpr.pi A B) e2) => delta_step_head_none_absurd_type (red_def the_red_env) (KExpr.pi A B) e2 (WhnfStepPiInv A B e2) (Eq.refl (OptionType Name) (OptionType.none Name)) (delta_reduces_to_step (KExpr.pi A B) e2 hdr)) ",
                "hs",
            ).to_string()),
            is_axiom: false,
            description: "Inversion of a whnf_step out of a pi (guide line 1273): whnf_step (pi A B) e2 -> WhnfStepPiInv A B e2. DerivedProved via whnf_step.rec (delta absurd) + beta_reduces.rec inversion (pi_dom/pi_cod/forall_ arms give dom/cod via pi injectivity; canonical redex arms app/lam/let != pi absurd, the let/zeta arms via let_ne_pi; iota arm const-head-none absurd). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "WhnfStepPiInv".to_string(), "WhnfStepPiInv.dom".to_string(), "WhnfStepPiInv.cod".to_string(),
                "whnf_step.rec".to_string(), "whnf_step.beta".to_string(), "beta_reduces.rec".to_string(),
                "app_ne_pi".to_string(), "proj_ne_pi".to_string(), "lam_ne_pi".to_string(), "let_ne_pi".to_string(), "pi_inj_fst".to_string(), "pi_inj_snd".to_string(),
                "iota_step_head_none_absurd_type".to_string(), "delta_step_head_none_absurd_type".to_string(),
                "iota_reduces_to_step".to_string(), "delta_reduces_to_step".to_string(),
                "red_rec".to_string(), "red_def".to_string(), "the_red_env".to_string(),
                "Eq.substType".to_string(), "Eq.cong".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnfAcc_pi : strong normalization is closed under pi (guide line 1288).
        // Double Acc induction (whnf_acc.rec on A generalizing B, then on B); at each
        // node every whnf_step out of pi A0 B1 is, by whnfStep_pi_inv, a domain step
        // (outer IH ihA, rebuilding whnf_acc B1 from the inner accessor) or a codomain
        // step (inner IH ihB), transported to the reduct via Eq.substType.
        self.add_definition_structural(SpecDefinition {
            name: "whnfAcc_pi".to_string(),
            type_src: "forall (A : KExpr) (B : KExpr), whnf_acc A -> whnf_acc B -> whnf_acc (KExpr.pi A B)".to_string(),
            value_src: Some(concat!(
                "fun (A : KExpr) (B : KExpr) (hA : whnf_acc A) (hB : whnf_acc B) => ",
                "whnf_acc.rec (fun (A0 : KExpr) (_ : whnf_acc A0) => forall (B0 : KExpr), whnf_acc B0 -> whnf_acc (KExpr.pi A0 B0)) ",
                "(fun (A0 : KExpr) (hAacc : forall (A2 : KExpr), whnf_step A0 A2 -> whnf_acc A2) (ihA : forall (A2 : KExpr), whnf_step A0 A2 -> forall (B0 : KExpr), whnf_acc B0 -> whnf_acc (KExpr.pi A2 B0)) => ",
                "fun (B0 : KExpr) (hB0 : whnf_acc B0) => ",
                "whnf_acc.rec (fun (B1 : KExpr) (_ : whnf_acc B1) => whnf_acc (KExpr.pi A0 B1)) ",
                "(fun (B1 : KExpr) (hBacc : forall (B2 : KExpr), whnf_step B1 B2 -> whnf_acc B2) (ihB : forall (B2 : KExpr), whnf_step B1 B2 -> whnf_acc (KExpr.pi A0 B2)) => ",
                "whnf_acc.intro (KExpr.pi A0 B1) (fun (e2 : KExpr) (hstep : whnf_step (KExpr.pi A0 B1) e2) => ",
                "WhnfStepPiInv.rec A0 B1 e2 (fun (_ : WhnfStepPiInv A0 B1 e2) => whnf_acc e2) ",
                "(fun (A2 : KExpr) (st : whnf_step A0 A2) (heq : Eq KExpr e2 (KExpr.pi A2 B1)) => Eq.substType KExpr (fun (w : KExpr) => whnf_acc w) (KExpr.pi A2 B1) e2 (Eq.symm KExpr e2 (KExpr.pi A2 B1) heq) (ihA A2 st B1 (whnf_acc.intro B1 hBacc))) ",
                "(fun (B2 : KExpr) (st : whnf_step B1 B2) (heq : Eq KExpr e2 (KExpr.pi A0 B2)) => Eq.substType KExpr (fun (w : KExpr) => whnf_acc w) (KExpr.pi A0 B2) e2 (Eq.symm KExpr e2 (KExpr.pi A0 B2) heq) (ihB B2 st)) ",
                "(whnfStep_pi_inv A0 B1 e2 hstep))) ",
                "B0 hB0) ",
                "A hA B hB",
            ).to_string()),
            is_axiom: false,
            description: "Strong normalization is closed under pi (guide line 1288): whnf_acc A -> whnf_acc B -> whnf_acc (pi A B). DerivedProved via double whnf_acc.rec (Acc induction on A generalizing B, then B); each step inverted by whnfStep_pi_inv into a domain step (outer IH) or codomain step (inner IH), transported by Eq.substType. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_acc".to_string(), "whnf_acc.rec".to_string(), "whnf_acc.intro".to_string(),
                "whnf_step".to_string(), "WhnfStepPiInv".to_string(), "WhnfStepPiInv.rec".to_string(),
                "whnfStep_pi_inv".to_string(), "Eq.substType".to_string(), "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // §8b' PSUBST ARITHMETIC SUB-TOWER (this port): the `upn` closed-form
        // primitives. These feed the psubst_cancel / psubst_up_lift_gen chain
        // (the guide's upn_apply, line 963) that the fundamental adequacy cases
        // (next batch) need via Models/models_extend. Value-full, ZERO axioms.
        // ================================================================

        // upn_zero_apply / upn_succ_apply : the iota unfolds of upn at a point
        // (upn 0 s j = s j ; upn (succ c) s j = up (upn c s) j). Eq.refl through
        // the Nat.rec convoy of upn.
        self.add_definition_structural(SpecDefinition {
            name: "upn_zero_apply".to_string(),
            type_src: "forall (s : Nat -> KExpr) (j : Nat), Eq KExpr (upn Nat.zero s j) (s j)"
                .to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (j : Nat) => Eq.refl KExpr (s j)".to_string()),
            is_axiom: false,
            description:
                "upn 0 s j = s j (Nat.rec zero convoy). DerivedProved via Eq.refl. Zero axiom_deps."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["upn".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "upn_succ_apply".to_string(),
            type_src: "forall (c : Nat) (s : Nat -> KExpr) (j : Nat), Eq KExpr (upn (Nat.succ c) s j) (up (upn c s) j)".to_string(),
            value_src: Some("fun (c : Nat) (s : Nat -> KExpr) (j : Nat) => Eq.refl KExpr (up (upn c s) j)".to_string()),
            is_axiom: false,
            description: "upn (succ c) s j = up (upn c s) j (Nat.rec succ convoy). DerivedProved via Eq.refl. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["upn".to_string(), "up".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // upn_apply_lt : below the binder depth, upn is the identity on variables
        // (guide upn_apply `if i < c` branch, line 964). Nat.rec on c; the succ case
        // cases i (0 -> up_zero; succ k -> up_succ + IH + lift_at_bvar_geq).
        self.add_definition_structural(SpecDefinition {
            name: "upn_apply_lt".to_string(),
            type_src: "forall (c : Nat) (s : Nat -> KExpr) (i : Nat), Lt i c -> Eq KExpr (upn c s i) (KExpr.bvar i)".to_string(),
            value_src: Some(concat!(
                "fun (c : Nat) (s : Nat -> KExpr) (i : Nat) (hlt : Lt i c) => ",
                "Nat.rec (fun (c0 : Nat) => forall (s0 : Nat -> KExpr) (i0 : Nat), Lt i0 c0 -> Eq KExpr (upn c0 s0 i0) (KExpr.bvar i0)) ",
                "(fun (s0 : Nat -> KExpr) (i0 : Nat) (h0 : Lt i0 Nat.zero) => Empty.rec (fun (_ : Empty) => Eq KExpr (upn Nat.zero s0 i0) (KExpr.bvar i0)) (lt_zero_absurd i0 Empty h0)) ",
                "(fun (c2 : Nat) (ih : forall (s0 : Nat -> KExpr) (i0 : Nat), Lt i0 c2 -> Eq KExpr (upn c2 s0 i0) (KExpr.bvar i0)) => ",
                "fun (s0 : Nat -> KExpr) (i0 : Nat) (_h0 : Lt i0 (Nat.succ c2)) => ",
                "Nat.rec (fun (i1 : Nat) => Lt i1 (Nat.succ c2) -> Eq KExpr (upn (Nat.succ c2) s0 i1) (KExpr.bvar i1)) ",
                "(fun (_hz : Lt Nat.zero (Nat.succ c2)) => Eq.trans KExpr (upn (Nat.succ c2) s0 Nat.zero) (up (upn c2 s0) Nat.zero) (KExpr.bvar Nat.zero) (upn_succ_apply c2 s0 Nat.zero) (up_zero (upn c2 s0))) ",
                "(fun (k : Nat) (_ihk : Lt k (Nat.succ c2) -> Eq KExpr (upn (Nat.succ c2) s0 k) (KExpr.bvar k)) (hk : Lt (Nat.succ k) (Nat.succ c2)) => ",
                "Eq.trans KExpr (upn (Nat.succ c2) s0 (Nat.succ k)) (lift_at (upn c2 s0 k) Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar (Nat.succ k)) ",
                "(Eq.trans KExpr (upn (Nat.succ c2) s0 (Nat.succ k)) (up (upn c2 s0) (Nat.succ k)) (lift_at (upn c2 s0 k) Nat.zero (Nat.succ Nat.zero)) (upn_succ_apply c2 s0 (Nat.succ k)) (up_succ (upn c2 s0) k)) ",
                "(Eq.trans KExpr (lift_at (upn c2 s0 k) Nat.zero (Nat.succ Nat.zero)) (lift_at (KExpr.bvar k) Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar (Nat.succ k)) ",
                "(Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w Nat.zero (Nat.succ Nat.zero)) (upn c2 s0 k) (KExpr.bvar k) (ih s0 k (lt_succ_succ_to_lt k c2 hk))) ",
                "(lift_at_bvar_geq k Nat.zero (Nat.succ Nat.zero) (nat_sub_zero_left k)))) ",
                "i0 _h0) ",
                "c s i hlt",
            ).to_string()),
            is_axiom: false,
            description: "upn_apply_lt: i < c -> upn c s i = bvar i (guide upn_apply, line 964). DerivedProved via Nat.rec on c (succ case cases i: up_zero / up_succ + IH + lift_at_bvar_geq). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "upn".to_string(), "up".to_string(),
                "upn_succ_apply".to_string(), "up_zero".to_string(), "up_succ".to_string(),
                "lift_at_bvar_geq".to_string(), "nat_sub_zero_left".to_string(),
                "lt_succ_succ_to_lt".to_string(), "lt_zero_absurd".to_string(),
                "Empty.rec".to_string(), "Eq.trans".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // upn_apply_ge : at or above the binder depth, upn lifts the shifted
        // substitution value (guide upn_apply `else` branch, line 964). Nat.rec on
        // c; the succ case cases i (0 -> le_succ_zero_empty absurd; succ k -> up_succ
        // + IH + lift_at_compose + nat_sub_succ_succ).
        self.add_definition_structural(SpecDefinition {
            name: "upn_apply_ge".to_string(),
            type_src: "forall (c : Nat) (s : Nat -> KExpr) (i : Nat), Le c i -> Eq KExpr (upn c s i) (lift_at (s (Nat.sub i c)) Nat.zero c)".to_string(),
            value_src: Some(concat!(
                "fun (c : Nat) (s : Nat -> KExpr) (i : Nat) (hle : Le c i) => ",
                "Nat.rec (fun (c0 : Nat) => forall (s0 : Nat -> KExpr) (i0 : Nat), Le c0 i0 -> Eq KExpr (upn c0 s0 i0) (lift_at (s0 (Nat.sub i0 c0)) Nat.zero c0)) ",
                "(fun (s0 : Nat -> KExpr) (i0 : Nat) (_h0 : Le Nat.zero i0) => Eq.trans KExpr (upn Nat.zero s0 i0) (s0 (Nat.sub i0 Nat.zero)) (lift_at (s0 (Nat.sub i0 Nat.zero)) Nat.zero Nat.zero) (upn_zero_apply s0 i0) (Eq.symm KExpr (lift_at (s0 (Nat.sub i0 Nat.zero)) Nat.zero Nat.zero) (s0 (Nat.sub i0 Nat.zero)) (lift_at_amount_zero (s0 (Nat.sub i0 Nat.zero)) Nat.zero))) ",
                "(fun (c2 : Nat) (ih : forall (s0 : Nat -> KExpr) (i0 : Nat), Le c2 i0 -> Eq KExpr (upn c2 s0 i0) (lift_at (s0 (Nat.sub i0 c2)) Nat.zero c2)) => ",
                "fun (s0 : Nat -> KExpr) (i0 : Nat) (h0 : Le (Nat.succ c2) i0) => ",
                "Nat.rec (fun (i1 : Nat) => Le (Nat.succ c2) i1 -> Eq KExpr (upn (Nat.succ c2) s0 i1) (lift_at (s0 (Nat.sub i1 (Nat.succ c2))) Nat.zero (Nat.succ c2))) ",
                "(fun (hz : Le (Nat.succ c2) Nat.zero) => Empty.rec (fun (_ : Empty) => Eq KExpr (upn (Nat.succ c2) s0 Nat.zero) (lift_at (s0 (Nat.sub Nat.zero (Nat.succ c2))) Nat.zero (Nat.succ c2))) (le_succ_zero_empty c2 hz)) ",
                "(fun (k : Nat) (_ihk : Le (Nat.succ c2) k -> Eq KExpr (upn (Nat.succ c2) s0 k) (lift_at (s0 (Nat.sub k (Nat.succ c2))) Nat.zero (Nat.succ c2))) (hk : Le (Nat.succ c2) (Nat.succ k)) => ",
                "Eq.trans KExpr (upn (Nat.succ c2) s0 (Nat.succ k)) (lift_at (upn c2 s0 k) Nat.zero (Nat.succ Nat.zero)) (lift_at (s0 (Nat.sub (Nat.succ k) (Nat.succ c2))) Nat.zero (Nat.succ c2)) ",
                "(Eq.trans KExpr (upn (Nat.succ c2) s0 (Nat.succ k)) (up (upn c2 s0) (Nat.succ k)) (lift_at (upn c2 s0 k) Nat.zero (Nat.succ Nat.zero)) (upn_succ_apply c2 s0 (Nat.succ k)) (up_succ (upn c2 s0) k)) ",
                "(Eq.trans KExpr (lift_at (upn c2 s0 k) Nat.zero (Nat.succ Nat.zero)) (lift_at (lift_at (s0 (Nat.sub k c2)) Nat.zero c2) Nat.zero (Nat.succ Nat.zero)) (lift_at (s0 (Nat.sub (Nat.succ k) (Nat.succ c2))) Nat.zero (Nat.succ c2)) ",
                "(Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w Nat.zero (Nat.succ Nat.zero)) (upn c2 s0 k) (lift_at (s0 (Nat.sub k c2)) Nat.zero c2) (ih s0 k (le_pred_pred c2 k hk))) ",
                "(Eq.trans KExpr (lift_at (lift_at (s0 (Nat.sub k c2)) Nat.zero c2) Nat.zero (Nat.succ Nat.zero)) (lift_at (s0 (Nat.sub k c2)) Nat.zero (Nat.succ c2)) (lift_at (s0 (Nat.sub (Nat.succ k) (Nat.succ c2))) Nat.zero (Nat.succ c2)) ",
                "(lift_at_compose (s0 (Nat.sub k c2)) Nat.zero c2 (Nat.succ Nat.zero)) ",
                "(Eq.cong Nat KExpr (fun (m : Nat) => lift_at (s0 m) Nat.zero (Nat.succ c2)) (Nat.sub k c2) (Nat.sub (Nat.succ k) (Nat.succ c2)) (Eq.symm Nat (Nat.sub (Nat.succ k) (Nat.succ c2)) (Nat.sub k c2) (nat_sub_succ_succ k c2)))))) ",
                "i0 h0) ",
                "c s i hle",
            ).to_string()),
            is_axiom: false,
            description: "upn_apply_ge: c <= i -> upn c s i = lift_at (s (i-c)) 0 c (guide upn_apply, line 964). DerivedProved via Nat.rec on c (succ case cases i: le_succ_zero_empty absurd / up_succ + IH + lift_at_compose + nat_sub_succ_succ). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "upn".to_string(), "up".to_string(),
                "upn_zero_apply".to_string(), "upn_succ_apply".to_string(), "up_succ".to_string(),
                "lift_at_amount_zero".to_string(), "lift_at_compose".to_string(),
                "nat_sub_succ_succ".to_string(), "le_pred_pred".to_string(), "le_succ_zero_empty".to_string(),
                "Empty.rec".to_string(), "Eq.trans".to_string(), "Eq.symm".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_bvar_lt : below the cutoff, lift_at fixes a variable (the `< `
        // companion of lift_at_bvar_geq). Same Eq.cong-through-Nat.rec shape as
        // lift_at_bvar_geq but hitting the succ branch via lt_sub_succ.
        self.add_definition_structural(SpecDefinition {
            name: "lift_at_bvar_lt".to_string(),
            type_src: "forall (i : Nat) (cutoff : Nat) (amount : Nat), Lt i cutoff -> Eq KExpr (lift_at (KExpr.bvar i) cutoff amount) (KExpr.bvar i)".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (cutoff : Nat) (amount : Nat) (hlt : Lt i cutoff) => ",
                "Eq.cong Nat KExpr (fun (n : Nat) => Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i amount)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) n) ",
                "(Nat.sub cutoff i) (Nat.succ (Nat.sub (Nat.sub cutoff i) (Nat.succ Nat.zero))) (lt_sub_succ i cutoff hlt)",
            ).to_string()),
            is_axiom: false,
            description: "lift_at_bvar_lt: i < cutoff -> lift_at (bvar i) cutoff amount = bvar i (the < companion of lift_at_bvar_geq). DerivedProved via Eq.cong through lift_bvar_at's Nat.rec + lt_sub_succ (succ branch). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "lift_at".to_string(), "lt_sub_succ".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_succ_sub_of_le : d <= i -> (i+1) - d = (i - d) + 1 (the guide's
        // `(i+1) - d = succ (i - d)` omega step, psubst_cancel_gen bvar ge-case).
        // Nat.rec on d; succ case cases i (le_succ_zero_empty absurd / nat_sub_succ_succ + IH).
        self.add_definition_structural(SpecDefinition {
            name: "nat_succ_sub_of_le".to_string(),
            type_src: "forall (d : Nat) (i : Nat), Le d i -> Eq Nat (Nat.sub (Nat.succ i) d) (Nat.succ (Nat.sub i d))".to_string(),
            value_src: Some(concat!(
                "fun (d : Nat) (i : Nat) (hle : Le d i) => ",
                "Nat.rec (fun (d0 : Nat) => forall (i0 : Nat), Le d0 i0 -> Eq Nat (Nat.sub (Nat.succ i0) d0) (Nat.succ (Nat.sub i0 d0))) ",
                "(fun (i0 : Nat) (_h : Le Nat.zero i0) => Eq.refl Nat (Nat.succ i0)) ",
                "(fun (d2 : Nat) (ih : forall (i0 : Nat), Le d2 i0 -> Eq Nat (Nat.sub (Nat.succ i0) d2) (Nat.succ (Nat.sub i0 d2))) => ",
                "fun (i0 : Nat) (h0 : Le (Nat.succ d2) i0) => ",
                "Nat.rec (fun (i1 : Nat) => Le (Nat.succ d2) i1 -> Eq Nat (Nat.sub (Nat.succ i1) (Nat.succ d2)) (Nat.succ (Nat.sub i1 (Nat.succ d2)))) ",
                "(fun (hz : Le (Nat.succ d2) Nat.zero) => Empty.rec (fun (_ : Empty) => Eq Nat (Nat.sub (Nat.succ Nat.zero) (Nat.succ d2)) (Nat.succ (Nat.sub Nat.zero (Nat.succ d2)))) (le_succ_zero_empty d2 hz)) ",
                "(fun (i3 : Nat) (_ihi : Le (Nat.succ d2) i3 -> Eq Nat (Nat.sub (Nat.succ i3) (Nat.succ d2)) (Nat.succ (Nat.sub i3 (Nat.succ d2)))) (hk : Le (Nat.succ d2) (Nat.succ i3)) => ",
                "Eq.trans Nat (Nat.sub (Nat.succ (Nat.succ i3)) (Nat.succ d2)) (Nat.sub (Nat.succ i3) d2) (Nat.succ (Nat.sub (Nat.succ i3) (Nat.succ d2))) ",
                "(nat_sub_succ_succ (Nat.succ i3) d2) ",
                "(Eq.trans Nat (Nat.sub (Nat.succ i3) d2) (Nat.succ (Nat.sub i3 d2)) (Nat.succ (Nat.sub (Nat.succ i3) (Nat.succ d2))) ",
                "(ih i3 (le_pred_pred d2 i3 hk)) ",
                "(Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.sub i3 d2) (Nat.sub (Nat.succ i3) (Nat.succ d2)) (Eq.symm Nat (Nat.sub (Nat.succ i3) (Nat.succ d2)) (Nat.sub i3 d2) (nat_sub_succ_succ i3 d2))))) ",
                "i0 h0) ",
                "d i hle",
            ).to_string()),
            is_axiom: false,
            description: "nat_succ_sub_of_le: d <= i -> (succ i) - d = succ (i - d) (the guide's omega step for the psubst_cancel_gen bvar ge-case). DerivedProved via Nat.rec on d (succ case cases i: le_succ_zero_empty absurd / nat_sub_succ_succ + IH). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "nat_sub_succ_succ".to_string(), "le_pred_pred".to_string(),
                "le_succ_zero_empty".to_string(), "Empty.rec".to_string(),
                "Eq.trans".to_string(), "Eq.symm".to_string(), "Eq.cong".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Models tenv M s G : the semantic environment of the Tait fundamental
        // theorem (guide Models, line 1808) — s sends each context variable i:A to a
        // term reducible at the (s-substituted, i+1-lifted) type A. Reducible def
        // over cm_Red + ctx_lookup so models_idsubst / models_extend and the
        // fundamental cases can unfold it.
        self.add_recursive_def(
            "def Models (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (s : Nat -> KExpr) (G : ListType KExpr) : Type := forall (i : Nat) (A : KExpr), Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> cm_Red tenv M (psubst s (lift_at A Nat.zero (Nat.succ i))) (s i)",
            "Models tenv M s G : s models the context G for M (guide Models, line 1808) — every ctx var i:A maps to a term reducible at psubst s (lift_at A 0 (i+1)). The semantic environment of the fundamental theorem. Reducible def over cm_Red / ctx_lookup.",
        )?;

        // models_idsubst : the identity substitution models every context (its
        // variables are reducible by red_var). Guide line 1813.
        self.add_definition_structural(SpecDefinition {
            name: "models_idsubst".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr), Models tenv M idsubst G".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) ",
                "(i : Nat) (A : KExpr) (_hget : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) => ",
                "red_var tenv M (psubst idsubst (lift_at A Nat.zero (Nat.succ i))) i",
            ).to_string()),
            is_axiom: false,
            description: "models_idsubst: idsubst models every context (guide line 1813) — each variable is reducible via red_var (idsubst i = bvar i). DerivedProved. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Models".to_string(), "idsubst".to_string(), "red_var".to_string(),
                "cm_Red".to_string(), "ctx_lookup".to_string(), "psubst".to_string(), "lift_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // psubst_cancel_gen : substituting under a fresh binder cancels a lift, at
        // any depth d (guide psubst_cancel_gen, line 1188). KExpr.rec on e
        // generalizing d; sort/const trivial, app/lam/pi congruence (lam/pi carrying
        // the substitution under the binder via up ~ upn succ), and the bvar case the
        // NatLtLeDichotomy split feeding upn_apply_lt / upn_apply_ge + lift_at_bvar_lt
        // / lift_at_bvar_geq + nat_succ_sub_of_le.
        self.add_definition_structural(SpecDefinition {
            name: "psubst_cancel_gen".to_string(),
            type_src: "forall (a : KExpr) (s : Nat -> KExpr) (e : KExpr) (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at e d (Nat.succ Nat.zero))) (psubst (upn d s) e)".to_string(),
            value_src: Some(concat!(
                "fun (a : KExpr) (s : Nat -> KExpr) (e : KExpr) => ",
                "KExpr.rec (fun (e0 : KExpr) => forall (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at e0 d (Nat.succ Nat.zero))) (psubst (upn d s) e0)) ",
                "(fun (n : Level) (d : Nat) => Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.sort n) d (Nat.succ Nat.zero))) (KExpr.sort n) (psubst (upn d s) (KExpr.sort n)) (psubst_sort (upn d (scons a s)) n) (Eq.symm KExpr (psubst (upn d s) (KExpr.sort n)) (KExpr.sort n) (psubst_sort (upn d s) n))) ",
                "(fun (i : Nat) (d : Nat) => NatLtLeDichotomy.rec i d (fun (_w : NatLtLeDichotomy i d) => Eq KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.bvar i) d (Nat.succ Nat.zero))) (psubst (upn d s) (KExpr.bvar i))) ",
                "(fun (hlt : Lt i d) => Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.bvar i) d (Nat.succ Nat.zero))) (KExpr.bvar i) (psubst (upn d s) (KExpr.bvar i)) (Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.bvar i) d (Nat.succ Nat.zero))) (psubst (upn d (scons a s)) (KExpr.bvar i)) (KExpr.bvar i) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst (upn d (scons a s)) w) (lift_at (KExpr.bvar i) d (Nat.succ Nat.zero)) (KExpr.bvar i) (lift_at_bvar_lt i d (Nat.succ Nat.zero) hlt)) (Eq.trans KExpr (psubst (upn d (scons a s)) (KExpr.bvar i)) (upn d (scons a s) i) (KExpr.bvar i) (psubst_bvar (upn d (scons a s)) i) (upn_apply_lt d (scons a s) i hlt))) (Eq.symm KExpr (psubst (upn d s) (KExpr.bvar i)) (KExpr.bvar i) (Eq.trans KExpr (psubst (upn d s) (KExpr.bvar i)) (upn d s i) (KExpr.bvar i) (psubst_bvar (upn d s) i) (upn_apply_lt d s i hlt)))) ",
                "(fun (hle : Le d i) => Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.bvar i) d (Nat.succ Nat.zero))) (lift_at (s (Nat.sub i d)) Nat.zero d) (psubst (upn d s) (KExpr.bvar i)) (Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.bvar i) d (Nat.succ Nat.zero))) (psubst (upn d (scons a s)) (KExpr.bvar (Nat.add i (Nat.succ Nat.zero)))) (lift_at (s (Nat.sub i d)) Nat.zero d) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst (upn d (scons a s)) w) (lift_at (KExpr.bvar i) d (Nat.succ Nat.zero)) (KExpr.bvar (Nat.add i (Nat.succ Nat.zero))) (lift_at_bvar_geq i d (Nat.succ Nat.zero) (le_sub_zero d i hle))) (Eq.trans KExpr (psubst (upn d (scons a s)) (KExpr.bvar (Nat.add i (Nat.succ Nat.zero)))) (lift_at (scons a s (Nat.sub (Nat.add i (Nat.succ Nat.zero)) d)) Nat.zero d) (lift_at (s (Nat.sub i d)) Nat.zero d) (Eq.trans KExpr (psubst (upn d (scons a s)) (KExpr.bvar (Nat.add i (Nat.succ Nat.zero)))) (upn d (scons a s) (Nat.add i (Nat.succ Nat.zero))) (lift_at (scons a s (Nat.sub (Nat.add i (Nat.succ Nat.zero)) d)) Nat.zero d) (psubst_bvar (upn d (scons a s)) (Nat.add i (Nat.succ Nat.zero))) (upn_apply_ge d (scons a s) (Nat.add i (Nat.succ Nat.zero)) (Le.step d i hle))) (Eq.cong Nat KExpr (fun (m : Nat) => lift_at (scons a s m) Nat.zero d) (Nat.sub (Nat.add i (Nat.succ Nat.zero)) d) (Nat.succ (Nat.sub i d)) (nat_succ_sub_of_le d i hle)))) (Eq.symm KExpr (psubst (upn d s) (KExpr.bvar i)) (lift_at (s (Nat.sub i d)) Nat.zero d) (Eq.trans KExpr (psubst (upn d s) (KExpr.bvar i)) (upn d s i) (lift_at (s (Nat.sub i d)) Nat.zero d) (psubst_bvar (upn d s) i) (upn_apply_ge d s i hle)))) ",
                "(nat_lt_le_dichotomy i d)) ",
                "(fun (f : KExpr) (x : KExpr) (ihf : forall (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at f d (Nat.succ Nat.zero))) (psubst (upn d s) f)) (ihx : forall (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at x d (Nat.succ Nat.zero))) (psubst (upn d s) x)) (d : Nat) => Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.app f x) d (Nat.succ Nat.zero))) (KExpr.app (psubst (upn d (scons a s)) (lift_at f d (Nat.succ Nat.zero))) (psubst (upn d (scons a s)) (lift_at x d (Nat.succ Nat.zero)))) (psubst (upn d s) (KExpr.app f x)) (psubst_app (upn d (scons a s)) (lift_at f d (Nat.succ Nat.zero)) (lift_at x d (Nat.succ Nat.zero))) (Eq.trans KExpr (KExpr.app (psubst (upn d (scons a s)) (lift_at f d (Nat.succ Nat.zero))) (psubst (upn d (scons a s)) (lift_at x d (Nat.succ Nat.zero)))) (KExpr.app (psubst (upn d s) f) (psubst (upn d s) x)) (psubst (upn d s) (KExpr.app f x)) (Eq.trans KExpr (KExpr.app (psubst (upn d (scons a s)) (lift_at f d (Nat.succ Nat.zero))) (psubst (upn d (scons a s)) (lift_at x d (Nat.succ Nat.zero)))) (KExpr.app (psubst (upn d s) f) (psubst (upn d (scons a s)) (lift_at x d (Nat.succ Nat.zero)))) (KExpr.app (psubst (upn d s) f) (psubst (upn d s) x)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w (psubst (upn d (scons a s)) (lift_at x d (Nat.succ Nat.zero)))) (psubst (upn d (scons a s)) (lift_at f d (Nat.succ Nat.zero))) (psubst (upn d s) f) (ihf d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app (psubst (upn d s) f) w) (psubst (upn d (scons a s)) (lift_at x d (Nat.succ Nat.zero))) (psubst (upn d s) x) (ihx d))) (Eq.symm KExpr (psubst (upn d s) (KExpr.app f x)) (KExpr.app (psubst (upn d s) f) (psubst (upn d s) x)) (psubst_app (upn d s) f x)))) ",
                "(fun (ty : KExpr) (bd : KExpr) (ihty : forall (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero))) (psubst (upn d s) ty)) (ihbd : forall (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at bd d (Nat.succ Nat.zero))) (psubst (upn d s) bd)) (d : Nat) => Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.lam ty bd) d (Nat.succ Nat.zero))) (KExpr.lam (psubst (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero)))) (psubst (upn d s) (KExpr.lam ty bd)) (psubst_lam (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero)) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero))) (Eq.trans KExpr (KExpr.lam (psubst (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero)))) (KExpr.lam (psubst (upn d s) ty) (psubst (up (upn d s)) bd)) (psubst (upn d s) (KExpr.lam ty bd)) (Eq.trans KExpr (KExpr.lam (psubst (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero)))) (KExpr.lam (psubst (upn d s) ty) (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero)))) (KExpr.lam (psubst (upn d s) ty) (psubst (up (upn d s)) bd)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero)))) (psubst (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero))) (psubst (upn d s) ty) (ihty d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam (psubst (upn d s) ty) w) (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero))) (psubst (up (upn d s)) bd) (ihbd (Nat.succ d)))) (Eq.symm KExpr (psubst (upn d s) (KExpr.lam ty bd)) (KExpr.lam (psubst (upn d s) ty) (psubst (up (upn d s)) bd)) (psubst_lam (upn d s) ty bd)))) ",
                "(fun (ty : KExpr) (bd : KExpr) (ihty : forall (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero))) (psubst (upn d s) ty)) (ihbd : forall (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at bd d (Nat.succ Nat.zero))) (psubst (upn d s) bd)) (d : Nat) => Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.pi ty bd) d (Nat.succ Nat.zero))) (KExpr.pi (psubst (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero)))) (psubst (upn d s) (KExpr.pi ty bd)) (psubst_pi (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero)) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero))) (Eq.trans KExpr (KExpr.pi (psubst (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero)))) (KExpr.pi (psubst (upn d s) ty) (psubst (up (upn d s)) bd)) (psubst (upn d s) (KExpr.pi ty bd)) (Eq.trans KExpr (KExpr.pi (psubst (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero)))) (KExpr.pi (psubst (upn d s) ty) (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero)))) (KExpr.pi (psubst (upn d s) ty) (psubst (up (upn d s)) bd)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero)))) (psubst (upn d (scons a s)) (lift_at ty d (Nat.succ Nat.zero))) (psubst (upn d s) ty) (ihty d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi (psubst (upn d s) ty) w) (psubst (up (upn d (scons a s))) (lift_at bd (Nat.succ d) (Nat.succ Nat.zero))) (psubst (up (upn d s)) bd) (ihbd (Nat.succ d)))) (Eq.symm KExpr (psubst (upn d s) (KExpr.pi ty bd)) (KExpr.pi (psubst (upn d s) ty) (psubst (up (upn d s)) bd)) (psubst_pi (upn d s) ty bd)))) ",
                "(fun (nm : Name) (us : ListType Level) (d : Nat) => Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.const nm us) d (Nat.succ Nat.zero))) (KExpr.const nm us) (psubst (upn d s) (KExpr.const nm us)) (psubst_const (upn d (scons a s)) nm us) (Eq.symm KExpr (psubst (upn d s) (KExpr.const nm us)) (KExpr.const nm us) (psubst_const (upn d s) nm us))) ",
                "(fun (lty : KExpr) (lv : KExpr) (lb : KExpr) (ihty : forall (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at lty d (Nat.succ Nat.zero))) (psubst (upn d s) lty)) (ihv : forall (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at lv d (Nat.succ Nat.zero))) (psubst (upn d s) lv)) (ihb : forall (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at lb d (Nat.succ Nat.zero))) (psubst (upn d s) lb)) (d : Nat) => Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.let_ lty lv lb) d (Nat.succ Nat.zero))) (KExpr.let_ (psubst (upn d (scons a s)) (lift_at lty d (Nat.succ Nat.zero))) (psubst (upn d (scons a s)) (lift_at lv d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at lb (Nat.succ d) (Nat.succ Nat.zero)))) (psubst (upn d s) (KExpr.let_ lty lv lb)) (psubst_let_ (upn d (scons a s)) (lift_at lty d (Nat.succ Nat.zero)) (lift_at lv d (Nat.succ Nat.zero)) (lift_at lb (Nat.succ d) (Nat.succ Nat.zero))) (Eq.trans KExpr (KExpr.let_ (psubst (upn d (scons a s)) (lift_at lty d (Nat.succ Nat.zero))) (psubst (upn d (scons a s)) (lift_at lv d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at lb (Nat.succ d) (Nat.succ Nat.zero)))) (KExpr.let_ (psubst (upn d s) lty) (psubst (upn d s) lv) (psubst (up (upn d s)) lb)) (psubst (upn d s) (KExpr.let_ lty lv lb)) (Eq.trans KExpr (KExpr.let_ (psubst (upn d (scons a s)) (lift_at lty d (Nat.succ Nat.zero))) (psubst (upn d (scons a s)) (lift_at lv d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at lb (Nat.succ d) (Nat.succ Nat.zero)))) (KExpr.let_ (psubst (upn d s) lty) (psubst (upn d (scons a s)) (lift_at lv d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at lb (Nat.succ d) (Nat.succ Nat.zero)))) (KExpr.let_ (psubst (upn d s) lty) (psubst (upn d s) lv) (psubst (up (upn d s)) lb)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w (psubst (upn d (scons a s)) (lift_at lv d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at lb (Nat.succ d) (Nat.succ Nat.zero)))) (psubst (upn d (scons a s)) (lift_at lty d (Nat.succ Nat.zero))) (psubst (upn d s) lty) (ihty d)) (Eq.trans KExpr (KExpr.let_ (psubst (upn d s) lty) (psubst (upn d (scons a s)) (lift_at lv d (Nat.succ Nat.zero))) (psubst (up (upn d (scons a s))) (lift_at lb (Nat.succ d) (Nat.succ Nat.zero)))) (KExpr.let_ (psubst (upn d s) lty) (psubst (upn d s) lv) (psubst (up (upn d (scons a s))) (lift_at lb (Nat.succ d) (Nat.succ Nat.zero)))) (KExpr.let_ (psubst (upn d s) lty) (psubst (upn d s) lv) (psubst (up (upn d s)) lb)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (psubst (upn d s) lty) w (psubst (up (upn d (scons a s))) (lift_at lb (Nat.succ d) (Nat.succ Nat.zero)))) (psubst (upn d (scons a s)) (lift_at lv d (Nat.succ Nat.zero))) (psubst (upn d s) lv) (ihv d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (psubst (upn d s) lty) (psubst (upn d s) lv) w) (psubst (up (upn d (scons a s))) (lift_at lb (Nat.succ d) (Nat.succ Nat.zero))) (psubst (up (upn d s)) lb) (ihb (Nat.succ d))))) (Eq.symm KExpr (psubst (upn d s) (KExpr.let_ lty lv lb)) (KExpr.let_ (psubst (upn d s) lty) (psubst (upn d s) lv) (psubst (up (upn d s)) lb)) (psubst_let_ (upn d s) lty lv lb)))) ",
                // proj (proj/lit rung): single hole, same cutoff (lift_at/psubst descend through proj by defeq).
                "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (ihsub : forall (d : Nat), Eq KExpr (psubst (upn d (scons a s)) (lift_at sub d (Nat.succ Nat.zero))) (psubst (upn d s) sub)) (d : Nat) => Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.proj ps pidx sub) d (Nat.succ Nat.zero))) (KExpr.proj ps pidx (psubst (upn d (scons a s)) (lift_at sub d (Nat.succ Nat.zero)))) (psubst (upn d s) (KExpr.proj ps pidx sub)) (psubst_proj (upn d (scons a s)) ps pidx (lift_at sub d (Nat.succ Nat.zero))) (Eq.trans KExpr (KExpr.proj ps pidx (psubst (upn d (scons a s)) (lift_at sub d (Nat.succ Nat.zero)))) (KExpr.proj ps pidx (psubst (upn d s) sub)) (psubst (upn d s) (KExpr.proj ps pidx sub)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.proj ps pidx w) (psubst (upn d (scons a s)) (lift_at sub d (Nat.succ Nat.zero))) (psubst (upn d s) sub) (ihsub d)) (Eq.symm KExpr (psubst (upn d s) (KExpr.proj ps pidx sub)) (KExpr.proj ps pidx (psubst (upn d s) sub)) (psubst_proj (upn d s) ps pidx sub)))) ",
                // lit (proj/lit rung): leaf, like const (lift_at/psubst identity).
                "(fun (v : Nat) (d : Nat) => Eq.trans KExpr (psubst (upn d (scons a s)) (lift_at (KExpr.lit v) d (Nat.succ Nat.zero))) (KExpr.lit v) (psubst (upn d s) (KExpr.lit v)) (psubst_lit (upn d (scons a s)) v) (Eq.symm KExpr (psubst (upn d s) (KExpr.lit v)) (KExpr.lit v) (psubst_lit (upn d s) v))) ",
                "e",
            ).to_string()),
            is_axiom: false,
            description: "psubst_cancel_gen: psubst (upn d (scons a s)) (lift_at e d 1) = psubst (upn d s) e (guide line 1188). DerivedProved via KExpr.rec on e generalizing d; bvar case NatLtLeDichotomy split feeding upn_apply_lt/ge + lift_at_bvar_lt/geq + nat_succ_sub_of_le; app/lam/pi congruence. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(), "NatLtLeDichotomy.rec".to_string(), "nat_lt_le_dichotomy".to_string(),
                "psubst".to_string(), "upn".to_string(), "up".to_string(), "scons".to_string(), "lift_at".to_string(),
                "psubst_sort".to_string(), "psubst_bvar".to_string(), "psubst_app".to_string(),
                "psubst_lam".to_string(), "psubst_pi".to_string(), "psubst_const".to_string(), "psubst_let_".to_string(), "psubst_proj".to_string(), "psubst_lit".to_string(),
                "upn_apply_lt".to_string(), "upn_apply_ge".to_string(),
                "lift_at_bvar_lt".to_string(), "lift_at_bvar_geq".to_string(),
                "le_sub_zero".to_string(), "nat_succ_sub_of_le".to_string(), "Le.step".to_string(),
                "Eq.trans".to_string(), "Eq.symm".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // psubst_cancel : depth-0 specialization (guide psubst_cancel, line 1214).
        self.add_definition_structural(SpecDefinition {
            name: "psubst_cancel".to_string(),
            type_src: "forall (e : KExpr) (a : KExpr) (s : Nat -> KExpr), Eq KExpr (psubst (scons a s) (lift_at e Nat.zero (Nat.succ Nat.zero))) (psubst s e)".to_string(),
            value_src: Some("fun (e : KExpr) (a : KExpr) (s : Nat -> KExpr) => psubst_cancel_gen a s e Nat.zero".to_string()),
            is_axiom: false,
            description: "psubst_cancel: psubst (scons a s) (lift_at e 0 1) = psubst s e (guide line 1214). DerivedProved as psubst_cancel_gen at depth 0 (upn 0 = id). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["psubst_cancel_gen".to_string(), "psubst".to_string(), "scons".to_string(), "lift_at".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // models_extend : extending a modelling substitution by a reducible term
        // models the extended context (guide models_extend, line 1820). Nat.rec on
        // the looked-up index: the zero entry is the new binding (transport ha along
        // psubst_cancel + the some-injection A = A2); the succ entries fall back to
        // the tail model hs (transport along psubst_cancel + lift_at_compose).
        self.add_definition_structural(SpecDefinition {
            name: "models_extend".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (s : Nat -> KExpr) (G : ListType KExpr) (A : KExpr) (a : KExpr), cm_Red tenv M (psubst s A) a -> Models tenv M s G -> Models tenv M (scons a s) (ListType.cons KExpr A G)".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (s : Nat -> KExpr) (G : ListType KExpr) (A : KExpr) (a : KExpr) (ha : cm_Red tenv M (psubst s A) a) (hs : Models tenv M s G) => ",
                "fun (i : Nat) (A2 : KExpr) (hget : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) i) (OptionType.some KExpr A2)) => ",
                "Nat.rec (fun (i0 : Nat) => Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) i0) (OptionType.some KExpr A2) -> cm_Red tenv M (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ i0))) (scons a s i0)) ",
                "(fun (h0 : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) Nat.zero) (OptionType.some KExpr A2)) => ",
                "Eq.substType KExpr (fun (w : KExpr) => cm_Red tenv M w a) (psubst s A2) (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ Nat.zero))) (Eq.symm KExpr (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ Nat.zero))) (psubst s A2) (psubst_cancel A2 a s)) (Eq.substType KExpr (fun (w : KExpr) => cm_Red tenv M (psubst s w) a) A A2 (option_some_inj KExpr A A2 h0) ha)) ",
                "(fun (k : Nat) (_ihk : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) k) (OptionType.some KExpr A2) -> cm_Red tenv M (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ k))) (scons a s k)) (hk : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) (Nat.succ k)) (OptionType.some KExpr A2)) => ",
                "Eq.substType KExpr (fun (w : KExpr) => cm_Red tenv M w (s k)) (psubst s (lift_at A2 Nat.zero (Nat.succ k))) (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ (Nat.succ k)))) (Eq.symm KExpr (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ (Nat.succ k)))) (psubst s (lift_at A2 Nat.zero (Nat.succ k))) (Eq.trans KExpr (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ (Nat.succ k)))) (psubst (scons a s) (lift_at (lift_at A2 Nat.zero (Nat.succ k)) Nat.zero (Nat.succ Nat.zero))) (psubst s (lift_at A2 Nat.zero (Nat.succ k))) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst (scons a s) w) (lift_at A2 Nat.zero (Nat.succ (Nat.succ k))) (lift_at (lift_at A2 Nat.zero (Nat.succ k)) Nat.zero (Nat.succ Nat.zero)) (Eq.symm KExpr (lift_at (lift_at A2 Nat.zero (Nat.succ k)) Nat.zero (Nat.succ Nat.zero)) (lift_at A2 Nat.zero (Nat.succ (Nat.succ k))) (lift_at_compose A2 Nat.zero (Nat.succ k) (Nat.succ Nat.zero)))) (psubst_cancel (lift_at A2 Nat.zero (Nat.succ k)) a s))) (hs k A2 hk)) ",
                "i hget",
            ).to_string()),
            is_axiom: false,
            description: "models_extend: cm_Red (psubst s A) a and Models s G give Models (scons a s) (cons A G) (guide line 1820). DerivedProved via Nat.rec on the index: zero entry transports ha (psubst_cancel + option_some_inj A=A2); succ entries transport the tail model hs (psubst_cancel + lift_at_compose). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "Models".to_string(), "cm_Red".to_string(),
                "ctx_lookup".to_string(), "scons".to_string(), "psubst".to_string(), "lift_at".to_string(),
                "psubst_cancel".to_string(), "lift_at_compose".to_string(), "option_some_inj".to_string(),
                "Eq.substType".to_string(), "Eq.symm".to_string(), "Eq.trans".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // §8b' PSUBST COMPOSITION + INSTANTIATION SUB-TOWER (this port).
        // psubst_up_lift_gen / psubst_up_lift / up_comp / psubst_comp then
        // instantiate_at_eq_psubst / instantiate_eq_psubst / psubst_instantiate /
        // psubst_scons_instantiate — the guide's §8b' comp/instantiate lemmas
        // (dependent_sn_modulo_candmodel.lean:1059-1242) that fundamental_app /
        // fundamental_lam / fundamental_pi need. Funext-free (psubst_pointwise +
        // up_comp). REUSE: lift_at_compose (= guide lift_same) + lift_at_shift_succ
        // (= guide lift_shift) + instantiate_bvar_at_eq from the base spec. ZERO
        // new kernel axioms, census stays 16.
        // ================================================================

        // psubst_up_lift_gen : lifting commutes with a substitution shifted under
        // `c` binders (guide psubst_up_lift_gen, line 1059). KExpr.rec on e
        // generalizing c/s; bvar case NatLtLeDichotomy split feeding upn_apply_lt/ge
        // + lift_at_bvar_lt/geq + lift_at_compose + lift_at_shift_succ + the
        // 1+c = succ c arithmetic; app/lam/pi congruence (upn (succ c) reduces to
        // up (upn c) definitionally). Zero axiom_deps.
        self.add_definition_structural(SpecDefinition {
            name: "psubst_up_lift_gen".to_string(),
            type_src: "forall (e : KExpr) (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at e c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) e) c (Nat.succ Nat.zero))".to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) => ",
                "KExpr.rec ",
                "(fun (e0 : KExpr) => forall (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at e0 c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) e0) c (Nat.succ Nat.zero))) ",
                "(fun (n : Level) (c : Nat) (s : Nat -> KExpr) => Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.sort n) c (Nat.succ Nat.zero))) (KExpr.sort n) (lift_at (psubst (upn c s) (KExpr.sort n)) c (Nat.succ Nat.zero)) (psubst_sort (upn c (up s)) n) (Eq.symm KExpr (lift_at (psubst (upn c s) (KExpr.sort n)) c (Nat.succ Nat.zero)) (KExpr.sort n) (Eq.trans KExpr (lift_at (psubst (upn c s) (KExpr.sort n)) c (Nat.succ Nat.zero)) (lift_at (KExpr.sort n) c (Nat.succ Nat.zero)) (KExpr.sort n) (Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w c (Nat.succ Nat.zero)) (psubst (upn c s) (KExpr.sort n)) (KExpr.sort n) (psubst_sort (upn c s) n)) (lift_at_sort n c (Nat.succ Nat.zero))))) ",
                "(fun (i : Nat) (c : Nat) (s : Nat -> KExpr) => NatLtLeDichotomy.rec i c (fun (_w : NatLtLeDichotomy i c) => Eq KExpr (psubst (upn c (up s)) (lift_at (KExpr.bvar i) c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) (KExpr.bvar i)) c (Nat.succ Nat.zero))) ",
                "(fun (hlt : Lt i c) => Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.bvar i) c (Nat.succ Nat.zero))) (KExpr.bvar i) (lift_at (psubst (upn c s) (KExpr.bvar i)) c (Nat.succ Nat.zero)) (Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.bvar i) c (Nat.succ Nat.zero))) (psubst (upn c (up s)) (KExpr.bvar i)) (KExpr.bvar i) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst (upn c (up s)) w) (lift_at (KExpr.bvar i) c (Nat.succ Nat.zero)) (KExpr.bvar i) (lift_at_bvar_lt i c (Nat.succ Nat.zero) hlt)) (Eq.trans KExpr (psubst (upn c (up s)) (KExpr.bvar i)) (upn c (up s) i) (KExpr.bvar i) (psubst_bvar (upn c (up s)) i) (upn_apply_lt c (up s) i hlt))) (Eq.symm KExpr (lift_at (psubst (upn c s) (KExpr.bvar i)) c (Nat.succ Nat.zero)) (KExpr.bvar i) (Eq.trans KExpr (lift_at (psubst (upn c s) (KExpr.bvar i)) c (Nat.succ Nat.zero)) (lift_at (KExpr.bvar i) c (Nat.succ Nat.zero)) (KExpr.bvar i) (Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w c (Nat.succ Nat.zero)) (psubst (upn c s) (KExpr.bvar i)) (KExpr.bvar i) (Eq.trans KExpr (psubst (upn c s) (KExpr.bvar i)) (upn c s i) (KExpr.bvar i) (psubst_bvar (upn c s) i) (upn_apply_lt c s i hlt))) (lift_at_bvar_lt i c (Nat.succ Nat.zero) hlt)))) ",
                "(fun (hle : Le c i) => Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.bvar i) c (Nat.succ Nat.zero))) (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ c)) (lift_at (psubst (upn c s) (KExpr.bvar i)) c (Nat.succ Nat.zero)) (Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.bvar i) c (Nat.succ Nat.zero))) (psubst (upn c (up s)) (KExpr.bvar (Nat.add i (Nat.succ Nat.zero)))) (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ c)) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst (upn c (up s)) w) (lift_at (KExpr.bvar i) c (Nat.succ Nat.zero)) (KExpr.bvar (Nat.add i (Nat.succ Nat.zero))) (lift_at_bvar_geq i c (Nat.succ Nat.zero) (le_sub_zero c i hle))) (Eq.trans KExpr (psubst (upn c (up s)) (KExpr.bvar (Nat.add i (Nat.succ Nat.zero)))) (upn c (up s) (Nat.add i (Nat.succ Nat.zero))) (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ c)) (psubst_bvar (upn c (up s)) (Nat.add i (Nat.succ Nat.zero))) (Eq.trans KExpr (upn c (up s) (Nat.add i (Nat.succ Nat.zero))) (lift_at (up s (Nat.sub (Nat.add i (Nat.succ Nat.zero)) c)) Nat.zero c) (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ c)) (upn_apply_ge c (up s) (Nat.add i (Nat.succ Nat.zero)) (Le.step c i hle)) (Eq.trans KExpr (lift_at (up s (Nat.sub (Nat.add i (Nat.succ Nat.zero)) c)) Nat.zero c) (lift_at (up s (Nat.succ (Nat.sub i c))) Nat.zero c) (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ c)) (Eq.cong Nat KExpr (fun (m : Nat) => lift_at (up s m) Nat.zero c) (Nat.sub (Nat.add i (Nat.succ Nat.zero)) c) (Nat.succ (Nat.sub i c)) (nat_succ_sub_of_le c i hle)) (Eq.trans KExpr (lift_at (up s (Nat.succ (Nat.sub i c))) Nat.zero c) (lift_at (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ Nat.zero)) Nat.zero c) (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ c)) (Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w Nat.zero c) (up s (Nat.succ (Nat.sub i c))) (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ Nat.zero)) (up_succ s (Nat.sub i c))) (Eq.trans KExpr (lift_at (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ Nat.zero)) Nat.zero c) (lift_at (s (Nat.sub i c)) Nat.zero (Nat.add (Nat.succ Nat.zero) c)) (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ c)) (lift_at_compose (s (Nat.sub i c)) Nat.zero (Nat.succ Nat.zero) c) (Eq.cong Nat KExpr (fun (m : Nat) => lift_at (s (Nat.sub i c)) Nat.zero m) (Nat.add (Nat.succ Nat.zero) c) (Nat.succ c) (Eq.trans Nat (Nat.add (Nat.succ Nat.zero) c) (Nat.succ (Nat.add Nat.zero c)) (Nat.succ c) (nat_succ_add Nat.zero c) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add Nat.zero c) c (nat_zero_add c)))))))))) (Eq.symm KExpr (lift_at (psubst (upn c s) (KExpr.bvar i)) c (Nat.succ Nat.zero)) (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ c)) (Eq.trans KExpr (lift_at (psubst (upn c s) (KExpr.bvar i)) c (Nat.succ Nat.zero)) (lift_at (lift_at (s (Nat.sub i c)) Nat.zero c) c (Nat.succ Nat.zero)) (lift_at (s (Nat.sub i c)) Nat.zero (Nat.succ c)) (Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w c (Nat.succ Nat.zero)) (psubst (upn c s) (KExpr.bvar i)) (lift_at (s (Nat.sub i c)) Nat.zero c) (Eq.trans KExpr (psubst (upn c s) (KExpr.bvar i)) (upn c s i) (lift_at (s (Nat.sub i c)) Nat.zero c) (psubst_bvar (upn c s) i) (upn_apply_ge c s i hle))) (lift_at_shift_succ (s (Nat.sub i c)) c c (nat_sub_self c))))) ",
                "(nat_lt_le_dichotomy i c)) ",
                "(fun (f : KExpr) (x : KExpr) (ihf : forall (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at f c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) f) c (Nat.succ Nat.zero))) (ihx : forall (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at x c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) x) c (Nat.succ Nat.zero))) (c : Nat) (s : Nat -> KExpr) => Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.app f x) c (Nat.succ Nat.zero))) (KExpr.app (psubst (upn c (up s)) (lift_at f c (Nat.succ Nat.zero))) (psubst (upn c (up s)) (lift_at x c (Nat.succ Nat.zero)))) (lift_at (psubst (upn c s) (KExpr.app f x)) c (Nat.succ Nat.zero)) (psubst_app (upn c (up s)) (lift_at f c (Nat.succ Nat.zero)) (lift_at x c (Nat.succ Nat.zero))) (Eq.trans KExpr (KExpr.app (psubst (upn c (up s)) (lift_at f c (Nat.succ Nat.zero))) (psubst (upn c (up s)) (lift_at x c (Nat.succ Nat.zero)))) (KExpr.app (lift_at (psubst (upn c s) f) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) x) c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) (KExpr.app f x)) c (Nat.succ Nat.zero)) (Eq.trans KExpr (KExpr.app (psubst (upn c (up s)) (lift_at f c (Nat.succ Nat.zero))) (psubst (upn c (up s)) (lift_at x c (Nat.succ Nat.zero)))) (KExpr.app (lift_at (psubst (upn c s) f) c (Nat.succ Nat.zero)) (psubst (upn c (up s)) (lift_at x c (Nat.succ Nat.zero)))) (KExpr.app (lift_at (psubst (upn c s) f) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) x) c (Nat.succ Nat.zero))) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w (psubst (upn c (up s)) (lift_at x c (Nat.succ Nat.zero)))) (psubst (upn c (up s)) (lift_at f c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) f) c (Nat.succ Nat.zero)) (ihf c s)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app (lift_at (psubst (upn c s) f) c (Nat.succ Nat.zero)) w) (psubst (upn c (up s)) (lift_at x c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) x) c (Nat.succ Nat.zero)) (ihx c s))) (Eq.symm KExpr (lift_at (psubst (upn c s) (KExpr.app f x)) c (Nat.succ Nat.zero)) (KExpr.app (lift_at (psubst (upn c s) f) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) x) c (Nat.succ Nat.zero))) (Eq.trans KExpr (lift_at (psubst (upn c s) (KExpr.app f x)) c (Nat.succ Nat.zero)) (lift_at (KExpr.app (psubst (upn c s) f) (psubst (upn c s) x)) c (Nat.succ Nat.zero)) (KExpr.app (lift_at (psubst (upn c s) f) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) x) c (Nat.succ Nat.zero))) (Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w c (Nat.succ Nat.zero)) (psubst (upn c s) (KExpr.app f x)) (KExpr.app (psubst (upn c s) f) (psubst (upn c s) x)) (psubst_app (upn c s) f x)) (lift_at_app (psubst (upn c s) f) (psubst (upn c s) x) c (Nat.succ Nat.zero)))))) ",
                "(fun (ty : KExpr) (bd : KExpr) (ihty : forall (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero))) (ihbd : forall (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at bd c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) bd) c (Nat.succ Nat.zero))) (c : Nat) (s : Nat -> KExpr) => Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.lam ty bd) c (Nat.succ Nat.zero))) (KExpr.lam (psubst (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero)))) (lift_at (psubst (upn c s) (KExpr.lam ty bd)) c (Nat.succ Nat.zero)) (psubst_lam (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero)) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero))) (Eq.trans KExpr (KExpr.lam (psubst (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero)))) (KExpr.lam (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) bd) (Nat.succ c) (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) (KExpr.lam ty bd)) c (Nat.succ Nat.zero)) (Eq.trans KExpr (KExpr.lam (psubst (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero)))) (KExpr.lam (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero)))) (KExpr.lam (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) bd) (Nat.succ c) (Nat.succ Nat.zero))) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero)))) (psubst (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (ihty c s)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) w) (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero))) (lift_at (psubst (up (upn c s)) bd) (Nat.succ c) (Nat.succ Nat.zero)) (ihbd (Nat.succ c) s))) (Eq.symm KExpr (lift_at (psubst (upn c s) (KExpr.lam ty bd)) c (Nat.succ Nat.zero)) (KExpr.lam (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) bd) (Nat.succ c) (Nat.succ Nat.zero))) (Eq.trans KExpr (lift_at (psubst (upn c s) (KExpr.lam ty bd)) c (Nat.succ Nat.zero)) (lift_at (KExpr.lam (psubst (upn c s) ty) (psubst (up (upn c s)) bd)) c (Nat.succ Nat.zero)) (KExpr.lam (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) bd) (Nat.succ c) (Nat.succ Nat.zero))) (Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w c (Nat.succ Nat.zero)) (psubst (upn c s) (KExpr.lam ty bd)) (KExpr.lam (psubst (upn c s) ty) (psubst (up (upn c s)) bd)) (psubst_lam (upn c s) ty bd)) (lift_at_lam (psubst (upn c s) ty) (psubst (up (upn c s)) bd) c (Nat.succ Nat.zero)))))) ",
                "(fun (ty : KExpr) (bd : KExpr) (ihty : forall (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero))) (ihbd : forall (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at bd c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) bd) c (Nat.succ Nat.zero))) (c : Nat) (s : Nat -> KExpr) => Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.pi ty bd) c (Nat.succ Nat.zero))) (KExpr.pi (psubst (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero)))) (lift_at (psubst (upn c s) (KExpr.pi ty bd)) c (Nat.succ Nat.zero)) (psubst_pi (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero)) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero))) (Eq.trans KExpr (KExpr.pi (psubst (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero)))) (KExpr.pi (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) bd) (Nat.succ c) (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) (KExpr.pi ty bd)) c (Nat.succ Nat.zero)) (Eq.trans KExpr (KExpr.pi (psubst (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero)))) (KExpr.pi (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero)))) (KExpr.pi (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) bd) (Nat.succ c) (Nat.succ Nat.zero))) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero)))) (psubst (upn c (up s)) (lift_at ty c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (ihty c s)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) w) (psubst (up (upn c (up s))) (lift_at bd (Nat.succ c) (Nat.succ Nat.zero))) (lift_at (psubst (up (upn c s)) bd) (Nat.succ c) (Nat.succ Nat.zero)) (ihbd (Nat.succ c) s))) (Eq.symm KExpr (lift_at (psubst (upn c s) (KExpr.pi ty bd)) c (Nat.succ Nat.zero)) (KExpr.pi (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) bd) (Nat.succ c) (Nat.succ Nat.zero))) (Eq.trans KExpr (lift_at (psubst (upn c s) (KExpr.pi ty bd)) c (Nat.succ Nat.zero)) (lift_at (KExpr.pi (psubst (upn c s) ty) (psubst (up (upn c s)) bd)) c (Nat.succ Nat.zero)) (KExpr.pi (lift_at (psubst (upn c s) ty) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) bd) (Nat.succ c) (Nat.succ Nat.zero))) (Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w c (Nat.succ Nat.zero)) (psubst (upn c s) (KExpr.pi ty bd)) (KExpr.pi (psubst (upn c s) ty) (psubst (up (upn c s)) bd)) (psubst_pi (upn c s) ty bd)) (lift_at_pi (psubst (upn c s) ty) (psubst (up (upn c s)) bd) c (Nat.succ Nat.zero)))))) ",
                "(fun (nm : Name) (us : ListType Level) (c : Nat) (s : Nat -> KExpr) => Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.const nm us) c (Nat.succ Nat.zero))) (KExpr.const nm us) (lift_at (psubst (upn c s) (KExpr.const nm us)) c (Nat.succ Nat.zero)) (psubst_const (upn c (up s)) nm us) (Eq.symm KExpr (lift_at (psubst (upn c s) (KExpr.const nm us)) c (Nat.succ Nat.zero)) (KExpr.const nm us) (Eq.trans KExpr (lift_at (psubst (upn c s) (KExpr.const nm us)) c (Nat.succ Nat.zero)) (lift_at (KExpr.const nm us) c (Nat.succ Nat.zero)) (KExpr.const nm us) (Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w c (Nat.succ Nat.zero)) (psubst (upn c s) (KExpr.const nm us)) (KExpr.const nm us) (psubst_const (upn c s) nm us)) (lift_at_const nm us c (Nat.succ Nat.zero))))) ",
                "(fun (lty : KExpr) (lv : KExpr) (lb : KExpr) (ihty : forall (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at lty c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero))) (ihv : forall (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at lv c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) lv) c (Nat.succ Nat.zero))) (ihb : forall (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at lb c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) lb) c (Nat.succ Nat.zero))) (c : Nat) (s : Nat -> KExpr) => Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.let_ lty lv lb) c (Nat.succ Nat.zero))) (KExpr.let_ (psubst (upn c (up s)) (lift_at lty c (Nat.succ Nat.zero))) (psubst (upn c (up s)) (lift_at lv c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at lb (Nat.succ c) (Nat.succ Nat.zero)))) (lift_at (psubst (upn c s) (KExpr.let_ lty lv lb)) c (Nat.succ Nat.zero)) (psubst_let_ (upn c (up s)) (lift_at lty c (Nat.succ Nat.zero)) (lift_at lv c (Nat.succ Nat.zero)) (lift_at lb (Nat.succ c) (Nat.succ Nat.zero))) (Eq.trans KExpr (KExpr.let_ (psubst (upn c (up s)) (lift_at lty c (Nat.succ Nat.zero))) (psubst (upn c (up s)) (lift_at lv c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at lb (Nat.succ c) (Nat.succ Nat.zero)))) (KExpr.let_ (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) lv) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) lb) (Nat.succ c) (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) (KExpr.let_ lty lv lb)) c (Nat.succ Nat.zero)) (Eq.trans KExpr (KExpr.let_ (psubst (upn c (up s)) (lift_at lty c (Nat.succ Nat.zero))) (psubst (upn c (up s)) (lift_at lv c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at lb (Nat.succ c) (Nat.succ Nat.zero)))) (KExpr.let_ (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero)) (psubst (upn c (up s)) (lift_at lv c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at lb (Nat.succ c) (Nat.succ Nat.zero)))) (KExpr.let_ (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) lv) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) lb) (Nat.succ c) (Nat.succ Nat.zero))) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w (psubst (upn c (up s)) (lift_at lv c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at lb (Nat.succ c) (Nat.succ Nat.zero)))) (psubst (upn c (up s)) (lift_at lty c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero)) (ihty c s)) (Eq.trans KExpr (KExpr.let_ (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero)) (psubst (upn c (up s)) (lift_at lv c (Nat.succ Nat.zero))) (psubst (up (upn c (up s))) (lift_at lb (Nat.succ c) (Nat.succ Nat.zero)))) (KExpr.let_ (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) lv) c (Nat.succ Nat.zero)) (psubst (up (upn c (up s))) (lift_at lb (Nat.succ c) (Nat.succ Nat.zero)))) (KExpr.let_ (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) lv) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) lb) (Nat.succ c) (Nat.succ Nat.zero))) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero)) w (psubst (up (upn c (up s))) (lift_at lb (Nat.succ c) (Nat.succ Nat.zero)))) (psubst (upn c (up s)) (lift_at lv c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) lv) c (Nat.succ Nat.zero)) (ihv c s)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) lv) c (Nat.succ Nat.zero)) w) (psubst (up (upn c (up s))) (lift_at lb (Nat.succ c) (Nat.succ Nat.zero))) (lift_at (psubst (up (upn c s)) lb) (Nat.succ c) (Nat.succ Nat.zero)) (ihb (Nat.succ c) s)))) (Eq.symm KExpr (lift_at (psubst (upn c s) (KExpr.let_ lty lv lb)) c (Nat.succ Nat.zero)) (KExpr.let_ (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) lv) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) lb) (Nat.succ c) (Nat.succ Nat.zero))) (Eq.trans KExpr (lift_at (psubst (upn c s) (KExpr.let_ lty lv lb)) c (Nat.succ Nat.zero)) (lift_at (KExpr.let_ (psubst (upn c s) lty) (psubst (upn c s) lv) (psubst (up (upn c s)) lb)) c (Nat.succ Nat.zero)) (KExpr.let_ (lift_at (psubst (upn c s) lty) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) lv) c (Nat.succ Nat.zero)) (lift_at (psubst (up (upn c s)) lb) (Nat.succ c) (Nat.succ Nat.zero))) (Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w c (Nat.succ Nat.zero)) (psubst (upn c s) (KExpr.let_ lty lv lb)) (KExpr.let_ (psubst (upn c s) lty) (psubst (upn c s) lv) (psubst (up (upn c s)) lb)) (psubst_let_ (upn c s) lty lv lb)) (lift_at_let_ (psubst (upn c s) lty) (psubst (upn c s) lv) (psubst (up (upn c s)) lb) c (Nat.succ Nat.zero)))))) ",
                "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (ihsub : forall (c : Nat) (s : Nat -> KExpr), Eq KExpr (psubst (upn c (up s)) (lift_at sub c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) sub) c (Nat.succ Nat.zero))) (c : Nat) (s : Nat -> KExpr) => Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.proj ps pidx sub) c (Nat.succ Nat.zero))) (psubst (upn c (up s)) (KExpr.proj ps pidx (lift_at sub c (Nat.succ Nat.zero)))) (lift_at (psubst (upn c s) (KExpr.proj ps pidx sub)) c (Nat.succ Nat.zero)) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst (upn c (up s)) w) (lift_at (KExpr.proj ps pidx sub) c (Nat.succ Nat.zero)) (KExpr.proj ps pidx (lift_at sub c (Nat.succ Nat.zero))) (lift_at_proj ps pidx sub c (Nat.succ Nat.zero))) (Eq.trans KExpr (psubst (upn c (up s)) (KExpr.proj ps pidx (lift_at sub c (Nat.succ Nat.zero)))) (KExpr.proj ps pidx (psubst (upn c (up s)) (lift_at sub c (Nat.succ Nat.zero)))) (lift_at (psubst (upn c s) (KExpr.proj ps pidx sub)) c (Nat.succ Nat.zero)) (psubst_proj (upn c (up s)) ps pidx (lift_at sub c (Nat.succ Nat.zero))) (Eq.trans KExpr (KExpr.proj ps pidx (psubst (upn c (up s)) (lift_at sub c (Nat.succ Nat.zero)))) (KExpr.proj ps pidx (lift_at (psubst (upn c s) sub) c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) (KExpr.proj ps pidx sub)) c (Nat.succ Nat.zero)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.proj ps pidx w) (psubst (upn c (up s)) (lift_at sub c (Nat.succ Nat.zero))) (lift_at (psubst (upn c s) sub) c (Nat.succ Nat.zero)) (ihsub c s)) (Eq.trans KExpr (KExpr.proj ps pidx (lift_at (psubst (upn c s) sub) c (Nat.succ Nat.zero))) (lift_at (KExpr.proj ps pidx (psubst (upn c s) sub)) c (Nat.succ Nat.zero)) (lift_at (psubst (upn c s) (KExpr.proj ps pidx sub)) c (Nat.succ Nat.zero)) (Eq.symm KExpr (lift_at (KExpr.proj ps pidx (psubst (upn c s) sub)) c (Nat.succ Nat.zero)) (KExpr.proj ps pidx (lift_at (psubst (upn c s) sub) c (Nat.succ Nat.zero))) (lift_at_proj ps pidx (psubst (upn c s) sub) c (Nat.succ Nat.zero))) (Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w c (Nat.succ Nat.zero)) (KExpr.proj ps pidx (psubst (upn c s) sub)) (psubst (upn c s) (KExpr.proj ps pidx sub)) (Eq.symm KExpr (psubst (upn c s) (KExpr.proj ps pidx sub)) (KExpr.proj ps pidx (psubst (upn c s) sub)) (psubst_proj (upn c s) ps pidx sub))))))) ",
                "(fun (v : Nat) (c : Nat) (s : Nat -> KExpr) => Eq.trans KExpr (psubst (upn c (up s)) (lift_at (KExpr.lit v) c (Nat.succ Nat.zero))) (KExpr.lit v) (lift_at (psubst (upn c s) (KExpr.lit v)) c (Nat.succ Nat.zero)) (psubst_lit (upn c (up s)) v) (Eq.symm KExpr (lift_at (psubst (upn c s) (KExpr.lit v)) c (Nat.succ Nat.zero)) (KExpr.lit v) (Eq.trans KExpr (lift_at (psubst (upn c s) (KExpr.lit v)) c (Nat.succ Nat.zero)) (lift_at (KExpr.lit v) c (Nat.succ Nat.zero)) (KExpr.lit v) (Eq.cong KExpr KExpr (fun (w : KExpr) => lift_at w c (Nat.succ Nat.zero)) (psubst (upn c s) (KExpr.lit v)) (KExpr.lit v) (psubst_lit (upn c s) v)) (lift_at_lit v c (Nat.succ Nat.zero))))) ",
                "e ",
            ).to_string()),
            is_axiom: false,
            description: "psubst_up_lift_gen: psubst (upn c (up s)) (lift_at e c 1) = lift_at (psubst (upn c s) e) c 1 (guide line 1059). DerivedProved via KExpr.rec on e generalizing c/s; bvar NatLtLeDichotomy split + lift_at_compose/lift_at_shift_succ; app/lam/pi congruence. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(), "NatLtLeDichotomy.rec".to_string(), "nat_lt_le_dichotomy".to_string(),
                "psubst".to_string(), "upn".to_string(), "up".to_string(), "lift_at".to_string(),
                "psubst_sort".to_string(), "psubst_bvar".to_string(), "psubst_app".to_string(),
                "psubst_lam".to_string(), "psubst_pi".to_string(), "psubst_const".to_string(), "psubst_let_".to_string(), "psubst_proj".to_string(), "psubst_lit".to_string(),
                "lift_at_sort".to_string(), "lift_at_app".to_string(), "lift_at_lam".to_string(), "lift_at_proj".to_string(), "lift_at_lit".to_string(),
                "lift_at_pi".to_string(), "lift_at_const".to_string(), "lift_at_let_".to_string(),
                "upn_apply_lt".to_string(), "upn_apply_ge".to_string(),
                "lift_at_bvar_lt".to_string(), "lift_at_bvar_geq".to_string(),
                "lift_at_compose".to_string(), "lift_at_shift_succ".to_string(),
                "le_sub_zero".to_string(), "nat_succ_sub_of_le".to_string(), "nat_sub_self".to_string(),
                "nat_succ_add".to_string(), "nat_zero_add".to_string(), "up_succ".to_string(), "Le.step".to_string(),
                "Eq.trans".to_string(), "Eq.symm".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // psubst_up_lift : depth-0 specialization (guide psubst_up_lift, line 1098).
        self.add_definition_structural(SpecDefinition {
            name: "psubst_up_lift".to_string(),
            type_src: "forall (e : KExpr) (s : Nat -> KExpr), Eq KExpr (psubst (up s) (lift_at e Nat.zero (Nat.succ Nat.zero))) (lift_at (psubst s e) Nat.zero (Nat.succ Nat.zero))".to_string(),
            value_src: Some("fun (e : KExpr) (s : Nat -> KExpr) => psubst_up_lift_gen e Nat.zero s".to_string()),
            is_axiom: false,
            description: "psubst_up_lift: psubst (up s) (lift_at e 0 1) = lift_at (psubst s e) 0 1 (guide line 1098). DerivedProved as psubst_up_lift_gen at depth 0 (upn 0 = id). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["psubst_up_lift_gen".to_string(), "psubst".to_string(), "up".to_string(), "lift_at".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // up_comp : `up` respects composition of substitutions (guide up_comp, line
        // 1104). Nat.rec on the index: zero -> bvar 0 (psubst_bvar); succ k ->
        // psubst_up_lift (t k) s. Zero axiom_deps.
        self.add_definition_structural(SpecDefinition {
            name: "up_comp".to_string(),
            type_src: "forall (s : Nat -> KExpr) (t : Nat -> KExpr) (i : Nat), Eq KExpr (psubst (up s) (up t i)) (up (fun (k : Nat) => psubst s (t k)) i)".to_string(),
            value_src: Some("fun (s : Nat -> KExpr) (t : Nat -> KExpr) (i : Nat) => Nat.rec (fun (j : Nat) => Eq KExpr (psubst (up s) (up t j)) (up (fun (k : Nat) => psubst s (t k)) j)) (Eq.trans KExpr (psubst (up s) (up t Nat.zero)) (up s Nat.zero) (up (fun (k : Nat) => psubst s (t k)) Nat.zero) (psubst_bvar (up s) Nat.zero) (Eq.refl KExpr (KExpr.bvar Nat.zero))) (fun (k : Nat) (_ih : Eq KExpr (psubst (up s) (up t k)) (up (fun (j : Nat) => psubst s (t j)) k)) => psubst_up_lift (t k) s) i".to_string()),
            is_axiom: false,
            description: "up_comp: psubst (up s) (up t i) = up (fun k => psubst s (t k)) i (guide line 1104). DerivedProved via Nat.rec on i (zero: psubst_bvar; succ: psubst_up_lift). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(), "psubst".to_string(), "up".to_string(),
                "psubst_bvar".to_string(), "psubst_up_lift".to_string(),
                "Eq.trans".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // psubst_comp : composition law for parallel substitution (guide psubst_comp,
        // line 1111). KExpr.rec on e; lam/pi carry the substitution under the binder
        // funext-free via psubst_pointwise + up_comp. Zero axiom_deps.
        self.add_definition_structural(SpecDefinition {
            name: "psubst_comp".to_string(),
            type_src: "forall (e : KExpr) (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t e)) (psubst (fun (i : Nat) => psubst s (t i)) e)".to_string(),
            value_src: Some("fun (e : KExpr) => KExpr.rec (fun (e0 : KExpr) => forall (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t e0)) (psubst (fun (i : Nat) => psubst s (t i)) e0)) (fun (n : Level) (s : Nat -> KExpr) (t : Nat -> KExpr) => Eq.trans KExpr (psubst s (psubst t (KExpr.sort n))) (KExpr.sort n) (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.sort n)) (Eq.trans KExpr (psubst s (psubst t (KExpr.sort n))) (psubst s (KExpr.sort n)) (KExpr.sort n) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst s w) (psubst t (KExpr.sort n)) (KExpr.sort n) (psubst_sort t n)) (psubst_sort s n)) (Eq.symm KExpr (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.sort n)) (KExpr.sort n) (psubst_sort (fun (i : Nat) => psubst s (t i)) n))) (fun (i : Nat) (s : Nat -> KExpr) (t : Nat -> KExpr) => Eq.trans KExpr (psubst s (psubst t (KExpr.bvar i))) (psubst s (t i)) (psubst (fun (j : Nat) => psubst s (t j)) (KExpr.bvar i)) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst s w) (psubst t (KExpr.bvar i)) (t i) (psubst_bvar t i)) (Eq.symm KExpr (psubst (fun (j : Nat) => psubst s (t j)) (KExpr.bvar i)) (psubst s (t i)) (psubst_bvar (fun (j : Nat) => psubst s (t j)) i))) (fun (f : KExpr) (x : KExpr) (ihf : forall (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t f)) (psubst (fun (i : Nat) => psubst s (t i)) f)) (ihx : forall (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t x)) (psubst (fun (i : Nat) => psubst s (t i)) x)) (s : Nat -> KExpr) (t : Nat -> KExpr) => Eq.trans KExpr (psubst s (psubst t (KExpr.app f x))) (KExpr.app (psubst (fun (i : Nat) => psubst s (t i)) f) (psubst (fun (i : Nat) => psubst s (t i)) x)) (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.app f x)) (Eq.trans KExpr (psubst s (psubst t (KExpr.app f x))) (psubst s (KExpr.app (psubst t f) (psubst t x))) (KExpr.app (psubst (fun (i : Nat) => psubst s (t i)) f) (psubst (fun (i : Nat) => psubst s (t i)) x)) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst s w) (psubst t (KExpr.app f x)) (KExpr.app (psubst t f) (psubst t x)) (psubst_app t f x)) (Eq.trans KExpr (psubst s (KExpr.app (psubst t f) (psubst t x))) (KExpr.app (psubst s (psubst t f)) (psubst s (psubst t x))) (KExpr.app (psubst (fun (i : Nat) => psubst s (t i)) f) (psubst (fun (i : Nat) => psubst s (t i)) x)) (psubst_app s (psubst t f) (psubst t x)) (Eq.trans KExpr (KExpr.app (psubst s (psubst t f)) (psubst s (psubst t x))) (KExpr.app (psubst (fun (i : Nat) => psubst s (t i)) f) (psubst s (psubst t x))) (KExpr.app (psubst (fun (i : Nat) => psubst s (t i)) f) (psubst (fun (i : Nat) => psubst s (t i)) x)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w (psubst s (psubst t x))) (psubst s (psubst t f)) (psubst (fun (i : Nat) => psubst s (t i)) f) (ihf s t)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app (psubst (fun (i : Nat) => psubst s (t i)) f) w) (psubst s (psubst t x)) (psubst (fun (i : Nat) => psubst s (t i)) x) (ihx s t))))) (Eq.symm KExpr (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.app f x)) (KExpr.app (psubst (fun (i : Nat) => psubst s (t i)) f) (psubst (fun (i : Nat) => psubst s (t i)) x)) (psubst_app (fun (i : Nat) => psubst s (t i)) f x))) (fun (A : KExpr) (b : KExpr) (ihA : forall (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t A)) (psubst (fun (i : Nat) => psubst s (t i)) A)) (ihb : forall (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t b)) (psubst (fun (i : Nat) => psubst s (t i)) b)) (s : Nat -> KExpr) (t : Nat -> KExpr) => Eq.trans KExpr (psubst s (psubst t (KExpr.lam A b))) (KExpr.lam (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.lam A b)) (Eq.trans KExpr (psubst s (psubst t (KExpr.lam A b))) (psubst s (KExpr.lam (psubst t A) (psubst (up t) b))) (KExpr.lam (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst s w) (psubst t (KExpr.lam A b)) (KExpr.lam (psubst t A) (psubst (up t) b)) (psubst_lam t A b)) (Eq.trans KExpr (psubst s (KExpr.lam (psubst t A) (psubst (up t) b))) (KExpr.lam (psubst s (psubst t A)) (psubst (up s) (psubst (up t) b))) (KExpr.lam (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (psubst_lam s (psubst t A) (psubst (up t) b)) (Eq.trans KExpr (KExpr.lam (psubst s (psubst t A)) (psubst (up s) (psubst (up t) b))) (KExpr.lam (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up s) (psubst (up t) b))) (KExpr.lam (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w (psubst (up s) (psubst (up t) b))) (psubst s (psubst t A)) (psubst (fun (i : Nat) => psubst s (t i)) A) (ihA s t)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam (psubst (fun (i : Nat) => psubst s (t i)) A) w) (psubst (up s) (psubst (up t) b)) (psubst (up (fun (i : Nat) => psubst s (t i))) b) (Eq.trans KExpr (psubst (up s) (psubst (up t) b)) (psubst (fun (j : Nat) => psubst (up s) (up t j)) b) (psubst (up (fun (i : Nat) => psubst s (t i))) b) (ihb (up s) (up t)) (psubst_pointwise b (fun (j : Nat) => psubst (up s) (up t j)) (up (fun (i : Nat) => psubst s (t i))) (up_comp s t))))))) (Eq.symm KExpr (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.lam A b)) (KExpr.lam (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (psubst_lam (fun (i : Nat) => psubst s (t i)) A b))) (fun (A : KExpr) (b : KExpr) (ihA : forall (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t A)) (psubst (fun (i : Nat) => psubst s (t i)) A)) (ihb : forall (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t b)) (psubst (fun (i : Nat) => psubst s (t i)) b)) (s : Nat -> KExpr) (t : Nat -> KExpr) => Eq.trans KExpr (psubst s (psubst t (KExpr.pi A b))) (KExpr.pi (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.pi A b)) (Eq.trans KExpr (psubst s (psubst t (KExpr.pi A b))) (psubst s (KExpr.pi (psubst t A) (psubst (up t) b))) (KExpr.pi (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst s w) (psubst t (KExpr.pi A b)) (KExpr.pi (psubst t A) (psubst (up t) b)) (psubst_pi t A b)) (Eq.trans KExpr (psubst s (KExpr.pi (psubst t A) (psubst (up t) b))) (KExpr.pi (psubst s (psubst t A)) (psubst (up s) (psubst (up t) b))) (KExpr.pi (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (psubst_pi s (psubst t A) (psubst (up t) b)) (Eq.trans KExpr (KExpr.pi (psubst s (psubst t A)) (psubst (up s) (psubst (up t) b))) (KExpr.pi (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up s) (psubst (up t) b))) (KExpr.pi (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w (psubst (up s) (psubst (up t) b))) (psubst s (psubst t A)) (psubst (fun (i : Nat) => psubst s (t i)) A) (ihA s t)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi (psubst (fun (i : Nat) => psubst s (t i)) A) w) (psubst (up s) (psubst (up t) b)) (psubst (up (fun (i : Nat) => psubst s (t i))) b) (Eq.trans KExpr (psubst (up s) (psubst (up t) b)) (psubst (fun (j : Nat) => psubst (up s) (up t j)) b) (psubst (up (fun (i : Nat) => psubst s (t i))) b) (ihb (up s) (up t)) (psubst_pointwise b (fun (j : Nat) => psubst (up s) (up t j)) (up (fun (i : Nat) => psubst s (t i))) (up_comp s t))))))) (Eq.symm KExpr (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.pi A b)) (KExpr.pi (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (psubst_pi (fun (i : Nat) => psubst s (t i)) A b))) (fun (nm : Name) (us : ListType Level) (s : Nat -> KExpr) (t : Nat -> KExpr) => Eq.trans KExpr (psubst s (psubst t (KExpr.const nm us))) (KExpr.const nm us) (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.const nm us)) (Eq.trans KExpr (psubst s (psubst t (KExpr.const nm us))) (psubst s (KExpr.const nm us)) (KExpr.const nm us) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst s w) (psubst t (KExpr.const nm us)) (KExpr.const nm us) (psubst_const t nm us)) (psubst_const s nm us)) (Eq.symm KExpr (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.const nm us)) (KExpr.const nm us) (psubst_const (fun (i : Nat) => psubst s (t i)) nm us))) (fun (A : KExpr) (lv : KExpr) (b : KExpr) (ihA : forall (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t A)) (psubst (fun (i : Nat) => psubst s (t i)) A)) (ihv : forall (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t lv)) (psubst (fun (i : Nat) => psubst s (t i)) lv)) (ihb : forall (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t b)) (psubst (fun (i : Nat) => psubst s (t i)) b)) (s : Nat -> KExpr) (t : Nat -> KExpr) => Eq.trans KExpr (psubst s (psubst t (KExpr.let_ A lv b))) (KExpr.let_ (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (fun (i : Nat) => psubst s (t i)) lv) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.let_ A lv b)) (Eq.trans KExpr (psubst s (psubst t (KExpr.let_ A lv b))) (psubst s (KExpr.let_ (psubst t A) (psubst t lv) (psubst (up t) b))) (KExpr.let_ (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (fun (i : Nat) => psubst s (t i)) lv) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst s w) (psubst t (KExpr.let_ A lv b)) (KExpr.let_ (psubst t A) (psubst t lv) (psubst (up t) b)) (psubst_let_ t A lv b)) (Eq.trans KExpr (psubst s (KExpr.let_ (psubst t A) (psubst t lv) (psubst (up t) b))) (KExpr.let_ (psubst s (psubst t A)) (psubst s (psubst t lv)) (psubst (up s) (psubst (up t) b))) (KExpr.let_ (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (fun (i : Nat) => psubst s (t i)) lv) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (psubst_let_ s (psubst t A) (psubst t lv) (psubst (up t) b)) (Eq.trans KExpr (KExpr.let_ (psubst s (psubst t A)) (psubst s (psubst t lv)) (psubst (up s) (psubst (up t) b))) (KExpr.let_ (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst s (psubst t lv)) (psubst (up s) (psubst (up t) b))) (KExpr.let_ (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (fun (i : Nat) => psubst s (t i)) lv) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w (psubst s (psubst t lv)) (psubst (up s) (psubst (up t) b))) (psubst s (psubst t A)) (psubst (fun (i : Nat) => psubst s (t i)) A) (ihA s t)) (Eq.trans KExpr (KExpr.let_ (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst s (psubst t lv)) (psubst (up s) (psubst (up t) b))) (KExpr.let_ (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (fun (i : Nat) => psubst s (t i)) lv) (psubst (up s) (psubst (up t) b))) (KExpr.let_ (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (fun (i : Nat) => psubst s (t i)) lv) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (psubst (fun (i : Nat) => psubst s (t i)) A) w (psubst (up s) (psubst (up t) b))) (psubst s (psubst t lv)) (psubst (fun (i : Nat) => psubst s (t i)) lv) (ihv s t)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (fun (i : Nat) => psubst s (t i)) lv) w) (psubst (up s) (psubst (up t) b)) (psubst (up (fun (i : Nat) => psubst s (t i))) b) (Eq.trans KExpr (psubst (up s) (psubst (up t) b)) (psubst (fun (j : Nat) => psubst (up s) (up t j)) b) (psubst (up (fun (i : Nat) => psubst s (t i))) b) (ihb (up s) (up t)) (psubst_pointwise b (fun (j : Nat) => psubst (up s) (up t j)) (up (fun (i : Nat) => psubst s (t i))) (up_comp s t)))))))) (Eq.symm KExpr (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.let_ A lv b)) (KExpr.let_ (psubst (fun (i : Nat) => psubst s (t i)) A) (psubst (fun (i : Nat) => psubst s (t i)) lv) (psubst (up (fun (i : Nat) => psubst s (t i))) b)) (psubst_let_ (fun (i : Nat) => psubst s (t i)) A lv b))) (fun (ps : Name) (pidx : Nat) (sub : KExpr) (ihsub : forall (s : Nat -> KExpr) (t : Nat -> KExpr), Eq KExpr (psubst s (psubst t sub)) (psubst (fun (i : Nat) => psubst s (t i)) sub)) (s : Nat -> KExpr) (t : Nat -> KExpr) => Eq.trans KExpr (psubst s (psubst t (KExpr.proj ps pidx sub))) (psubst s (KExpr.proj ps pidx (psubst t sub))) (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.proj ps pidx sub)) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst s w) (psubst t (KExpr.proj ps pidx sub)) (KExpr.proj ps pidx (psubst t sub)) (psubst_proj t ps pidx sub)) (Eq.trans KExpr (psubst s (KExpr.proj ps pidx (psubst t sub))) (KExpr.proj ps pidx (psubst s (psubst t sub))) (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.proj ps pidx sub)) (psubst_proj s ps pidx (psubst t sub)) (Eq.trans KExpr (KExpr.proj ps pidx (psubst s (psubst t sub))) (KExpr.proj ps pidx (psubst (fun (i : Nat) => psubst s (t i)) sub)) (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.proj ps pidx sub)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.proj ps pidx w) (psubst s (psubst t sub)) (psubst (fun (i : Nat) => psubst s (t i)) sub) (ihsub s t)) (Eq.symm KExpr (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.proj ps pidx sub)) (KExpr.proj ps pidx (psubst (fun (i : Nat) => psubst s (t i)) sub)) (psubst_proj (fun (i : Nat) => psubst s (t i)) ps pidx sub))))) (fun (v : Nat) (s : Nat -> KExpr) (t : Nat -> KExpr) => Eq.trans KExpr (psubst s (psubst t (KExpr.lit v))) (KExpr.lit v) (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.lit v)) (Eq.trans KExpr (psubst s (psubst t (KExpr.lit v))) (psubst s (KExpr.lit v)) (KExpr.lit v) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst s w) (psubst t (KExpr.lit v)) (KExpr.lit v) (psubst_lit t v)) (psubst_lit s v)) (Eq.symm KExpr (psubst (fun (i : Nat) => psubst s (t i)) (KExpr.lit v)) (KExpr.lit v) (psubst_lit (fun (i : Nat) => psubst s (t i)) v)))  e".to_string()),
            is_axiom: false,
            description: "psubst_comp: psubst s (psubst t e) = psubst (fun i => psubst s (t i)) e (guide line 1111). DerivedProved via KExpr.rec on e; lam/pi use psubst_pointwise + up_comp (funext-free). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(), "psubst".to_string(), "up".to_string(),
                "psubst_sort".to_string(), "psubst_bvar".to_string(), "psubst_app".to_string(),
                "psubst_lam".to_string(), "psubst_pi".to_string(), "psubst_const".to_string(), "psubst_let_".to_string(), "psubst_proj".to_string(), "psubst_lit".to_string(),
                "psubst_pointwise".to_string(), "up_comp".to_string(),
                "Eq.trans".to_string(), "Eq.symm".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // §8b' INSTANTIATE-AS-PSUBST SUB-TOWER (Brick 2 KEYSTONE STEP 1). The
        // three instantiate lemmas the Tait fundamental cases need
        // (instantiate_eq_psubst, psubst_instantiate [app case],
        // psubst_scons_instantiate [lam head-expansion]) + the general-depth
        // instantiate_at_eq_psubst they factor through + two pure-Nat arithmetic
        // bridges the bvar `>` case needs. Guide §8b'
        // (dependent_sn_modulo_candmodel.lean:1145-1242). REUSE: instantiate_at_*
        // unfolds, instantiate_bvar_at_{below,eq,above}, upn_apply_{lt,ge},
        // lift_at_bvar_geq, nat_sub_self, nat_sub_zero_left, lt_sub_succ,
        // le_sub_zero, lt_implies_le, nat_succ_sub_of_le, nat_succ_add,
        // nat_add_zero, psubst_comp/pointwise/cancel/id from the landed tower.
        // ZERO new kernel axioms, census stays 16.
        // ================================================================

        // nat_sub_add_cancel : (i - d) + d = i for d <= i. Le.rec on the Le d i
        // derivation (mirrors le_sub_zero): refl = nat_sub_self + nat_add_zero,
        // step peels succ via nat_succ_sub_of_le + nat_succ_add + the IH.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_add_cancel".to_string(),
            type_src: "forall (d : Nat) (i : Nat), Le d i -> Eq Nat (Nat.add (Nat.sub i d) d) i".to_string(),
            value_src: Some(concat!(
                "fun (d : Nat) (i : Nat) (h : Le d i) => ",
                "Le.rec d (fun (j : Nat) (_ : Le d j) => Eq Nat (Nat.add (Nat.sub j d) d) j) ",
                "(Eq.trans Nat (Nat.add (Nat.sub d d) d) (Nat.add Nat.zero d) d (Eq.cong Nat Nat (fun (w : Nat) => Nat.add w d) (Nat.sub d d) Nat.zero (nat_sub_self d)) (nat_add_zero d)) ",
                "(fun (m : Nat) (_hm : Le d m) (ihm : Eq Nat (Nat.add (Nat.sub m d) d) m) => ",
                "Eq.trans Nat (Nat.add (Nat.sub (Nat.succ m) d) d) (Nat.add (Nat.succ (Nat.sub m d)) d) (Nat.succ m) ",
                "(Eq.cong Nat Nat (fun (w : Nat) => Nat.add w d) (Nat.sub (Nat.succ m) d) (Nat.succ (Nat.sub m d)) (nat_succ_sub_of_le d m _hm)) ",
                "(Eq.trans Nat (Nat.add (Nat.succ (Nat.sub m d)) d) (Nat.succ (Nat.add (Nat.sub m d) d)) (Nat.succ m) (nat_succ_add (Nat.sub m d) d) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add (Nat.sub m d) d) m ihm))) ",
                "i h",
            ).to_string()),
            is_axiom: false,
            description: "nat_sub_add_cancel: (i - d) + d = i for Le d i. DerivedProved via Le.rec (Prop motive): refl = nat_sub_self + nat_add_zero, step peels succ via nat_succ_sub_of_le + nat_succ_add + IH. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le.rec".to_string(), "nat_sub_self".to_string(), "nat_add_zero".to_string(),
                "nat_succ_sub_of_le".to_string(), "nat_succ_add".to_string(),
                "Eq.trans".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_gt_sub_bridge : ((i - d) - 1) + d = i - 1 for d < i. The bvar `>`
        // arithmetic: derived from nat_sub_add_cancel + lt_sub_succ + nat_succ_add
        // (rewrite i - d = succ K in the cancel, peel a pred). Nat.sub i 1 and
        // Nat.pred i are definitionally equal.
        self.add_definition_structural(SpecDefinition {
            name: "nat_gt_sub_bridge".to_string(),
            type_src: "forall (d : Nat) (i : Nat), Lt d i -> Eq Nat (Nat.add (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero)) d) (Nat.sub i (Nat.succ Nat.zero))".to_string(),
            value_src: Some(concat!(
                "fun (d : Nat) (i : Nat) (hlt : Lt d i) => ",
                "Eq.cong Nat Nat (fun (w : Nat) => Nat.pred w) (Nat.succ (Nat.add (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero)) d)) i ",
                "(Eq.trans Nat (Nat.succ (Nat.add (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero)) d)) (Nat.add (Nat.succ (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) d) i ",
                "(Eq.symm Nat (Nat.add (Nat.succ (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) d) (Nat.succ (Nat.add (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero)) d)) (nat_succ_add (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero)) d)) ",
                "(Eq.trans Nat (Nat.add (Nat.succ (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) d) (Nat.add (Nat.sub i d) d) i ",
                "(Eq.symm Nat (Nat.add (Nat.sub i d) d) (Nat.add (Nat.succ (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) d) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add w d) (Nat.sub i d) (Nat.succ (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) (lt_sub_succ d i hlt))) ",
                "(nat_sub_add_cancel d i (lt_implies_le d i hlt))))",
            ).to_string()),
            is_axiom: false,
            description: "nat_gt_sub_bridge: ((i-d)-1)+d = i-1 for Lt d i. DerivedProved from nat_sub_add_cancel + lt_sub_succ + nat_succ_add, then Nat.pred cong (Nat.sub i 1 defeq Nat.pred i). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "nat_sub_add_cancel".to_string(), "lt_sub_succ".to_string(), "lt_implies_le".to_string(),
                "nat_succ_add".to_string(), "Eq.trans".to_string(), "Eq.symm".to_string(), "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_at_eq_psubst : instantiate_at e a d = psubst (upn d (scons a
        // idsubst)) e (guide instantiate_at_eq_psubst, line 1158). KExpr.rec on e
        // generalizing d; sort/const trivial (instantiate_at_* + psubst_*),
        // app/lam/pi congruence (lam/pi recurse at succ d, up (upn d ..) defeq
        // upn (succ d) ..), bvar case NatTrichotomy split:
        //   i<d  -> both bvar i (instantiate_bvar_at_below + upn_apply_lt);
        //   i=d  -> both lift_at a 0 d (instantiate_bvar_at_eq + upn_apply_ge + Le.refl
        //           + nat_sub_self + scons-zero defeq), transported along i=d;
        //   i>d  -> bvar (i-1): LHS instantiate_bvar_at_above, RHS upn_apply_ge +
        //           lt_sub_succ (scons-succ defeq bvar) + lift_at_bvar_geq + nat_gt_sub_bridge.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_eq_psubst".to_string(),
            type_src: "forall (e : KExpr) (a : KExpr) (d : Nat), Eq KExpr (instantiate_at e a d) (psubst (upn d (scons a idsubst)) e)".to_string(),
            value_src: Some(concat!(
                "fun (e : KExpr) (a : KExpr) => KExpr.rec (fun (e0 : KExpr) => forall (d : Nat), Eq KExpr (instantiate_at e0 a d) (psubst (upn d (scons a idsubst)) e0)) ",
                // sort
                "(fun (n : Level) (d : Nat) => Eq.trans KExpr (instantiate_at (KExpr.sort n) a d) (KExpr.sort n) (psubst (upn d (scons a idsubst)) (KExpr.sort n)) (instantiate_at_sort n a d) (Eq.symm KExpr (psubst (upn d (scons a idsubst)) (KExpr.sort n)) (KExpr.sort n) (psubst_sort (upn d (scons a idsubst)) n))) ",
                // bvar
                "(fun (i : Nat) (d : Nat) => Eq.trans KExpr (instantiate_at (KExpr.bvar i) a d) (instantiate_bvar_at i d a) (psubst (upn d (scons a idsubst)) (KExpr.bvar i)) (instantiate_at_bvar i a d) ",
                "(Eq.trans KExpr (instantiate_bvar_at i d a) (upn d (scons a idsubst) i) (psubst (upn d (scons a idsubst)) (KExpr.bvar i)) ",
                "(NatTrichotomy.rec i d (fun (_w : NatTrichotomy i d) => Eq KExpr (instantiate_bvar_at i d a) (upn d (scons a idsubst) i)) ",
                // lt branch
                "(fun (hlt : Lt i d) => Eq.trans KExpr (instantiate_bvar_at i d a) (KExpr.bvar i) (upn d (scons a idsubst) i) (instantiate_bvar_at_below i d a (lt_sub_succ i d hlt)) (Eq.symm KExpr (upn d (scons a idsubst) i) (KExpr.bvar i) (upn_apply_lt d (scons a idsubst) i hlt))) ",
                // eq branch
                "(fun (heq : Eq Nat i d) => Eq.substType Nat (fun (w : Nat) => Eq KExpr (instantiate_bvar_at w d a) (upn d (scons a idsubst) w)) d i (Eq.symm Nat i d heq) (Eq.trans KExpr (instantiate_bvar_at d d a) (lift_at a Nat.zero d) (upn d (scons a idsubst) d) (instantiate_bvar_at_eq d a) (Eq.symm KExpr (upn d (scons a idsubst) d) (lift_at a Nat.zero d) (Eq.trans KExpr (upn d (scons a idsubst) d) (lift_at (scons a idsubst (Nat.sub d d)) Nat.zero d) (lift_at a Nat.zero d) (upn_apply_ge d (scons a idsubst) d (Le.refl d)) (Eq.cong Nat KExpr (fun (m : Nat) => lift_at (scons a idsubst m) Nat.zero d) (Nat.sub d d) Nat.zero (nat_sub_self d)))))) ",
                // gt branch
                "(fun (hgt : Lt d i) => Eq.trans KExpr (instantiate_bvar_at i d a) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (upn d (scons a idsubst) i) (instantiate_bvar_at_above i d a (le_sub_zero d i (lt_implies_le d i hgt)) (lt_sub_succ d i hgt)) (Eq.symm KExpr (upn d (scons a idsubst) i) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
                "(Eq.trans KExpr (upn d (scons a idsubst) i) (lift_at (KExpr.bvar (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) Nat.zero d) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
                "(Eq.trans KExpr (upn d (scons a idsubst) i) (lift_at (scons a idsubst (Nat.sub i d)) Nat.zero d) (lift_at (KExpr.bvar (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) Nat.zero d) (upn_apply_ge d (scons a idsubst) i (lt_implies_le d i hgt)) (Eq.cong Nat KExpr (fun (m : Nat) => lift_at (scons a idsubst m) Nat.zero d) (Nat.sub i d) (Nat.succ (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) (lt_sub_succ d i hgt))) ",
                "(Eq.trans KExpr (lift_at (KExpr.bvar (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero))) Nat.zero d) (KExpr.bvar (Nat.add (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero)) d)) (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) (lift_at_bvar_geq (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero)) Nat.zero d (nat_sub_zero_left (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero)))) (Eq.cong Nat KExpr (fun (w : Nat) => KExpr.bvar w) (Nat.add (Nat.sub (Nat.sub i d) (Nat.succ Nat.zero)) d) (Nat.sub i (Nat.succ Nat.zero)) (nat_gt_sub_bridge d i hgt)))))) ",
                "(nat_trichotomy i d)) ",
                "(Eq.symm KExpr (psubst (upn d (scons a idsubst)) (KExpr.bvar i)) (upn d (scons a idsubst) i) (psubst_bvar (upn d (scons a idsubst)) i)))) ",
                // app
                "(fun (f : KExpr) (x : KExpr) (ihf : forall (d : Nat), Eq KExpr (instantiate_at f a d) (psubst (upn d (scons a idsubst)) f)) (ihx : forall (d : Nat), Eq KExpr (instantiate_at x a d) (psubst (upn d (scons a idsubst)) x)) (d : Nat) => Eq.trans KExpr (instantiate_at (KExpr.app f x) a d) (KExpr.app (psubst (upn d (scons a idsubst)) f) (psubst (upn d (scons a idsubst)) x)) (psubst (upn d (scons a idsubst)) (KExpr.app f x)) (Eq.trans KExpr (instantiate_at (KExpr.app f x) a d) (KExpr.app (instantiate_at f a d) (instantiate_at x a d)) (KExpr.app (psubst (upn d (scons a idsubst)) f) (psubst (upn d (scons a idsubst)) x)) (instantiate_at_app f x a d) (Eq.trans KExpr (KExpr.app (instantiate_at f a d) (instantiate_at x a d)) (KExpr.app (psubst (upn d (scons a idsubst)) f) (instantiate_at x a d)) (KExpr.app (psubst (upn d (scons a idsubst)) f) (psubst (upn d (scons a idsubst)) x)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w (instantiate_at x a d)) (instantiate_at f a d) (psubst (upn d (scons a idsubst)) f) (ihf d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app (psubst (upn d (scons a idsubst)) f) w) (instantiate_at x a d) (psubst (upn d (scons a idsubst)) x) (ihx d)))) (Eq.symm KExpr (psubst (upn d (scons a idsubst)) (KExpr.app f x)) (KExpr.app (psubst (upn d (scons a idsubst)) f) (psubst (upn d (scons a idsubst)) x)) (psubst_app (upn d (scons a idsubst)) f x))) ",
                // lam
                "(fun (ty : KExpr) (bd : KExpr) (ihty : forall (d : Nat), Eq KExpr (instantiate_at ty a d) (psubst (upn d (scons a idsubst)) ty)) (ihbd : forall (d : Nat), Eq KExpr (instantiate_at bd a d) (psubst (upn d (scons a idsubst)) bd)) (d : Nat) => Eq.trans KExpr (instantiate_at (KExpr.lam ty bd) a d) (KExpr.lam (psubst (upn d (scons a idsubst)) ty) (psubst (up (upn d (scons a idsubst))) bd)) (psubst (upn d (scons a idsubst)) (KExpr.lam ty bd)) (Eq.trans KExpr (instantiate_at (KExpr.lam ty bd) a d) (KExpr.lam (instantiate_at ty a d) (instantiate_at bd a (Nat.succ d))) (KExpr.lam (psubst (upn d (scons a idsubst)) ty) (psubst (up (upn d (scons a idsubst))) bd)) (instantiate_at_lam ty bd a d) (Eq.trans KExpr (KExpr.lam (instantiate_at ty a d) (instantiate_at bd a (Nat.succ d))) (KExpr.lam (psubst (upn d (scons a idsubst)) ty) (instantiate_at bd a (Nat.succ d))) (KExpr.lam (psubst (upn d (scons a idsubst)) ty) (psubst (up (upn d (scons a idsubst))) bd)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w (instantiate_at bd a (Nat.succ d))) (instantiate_at ty a d) (psubst (upn d (scons a idsubst)) ty) (ihty d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam (psubst (upn d (scons a idsubst)) ty) w) (instantiate_at bd a (Nat.succ d)) (psubst (up (upn d (scons a idsubst))) bd) (ihbd (Nat.succ d))))) (Eq.symm KExpr (psubst (upn d (scons a idsubst)) (KExpr.lam ty bd)) (KExpr.lam (psubst (upn d (scons a idsubst)) ty) (psubst (up (upn d (scons a idsubst))) bd)) (psubst_lam (upn d (scons a idsubst)) ty bd))) ",
                // pi
                "(fun (ty : KExpr) (bd : KExpr) (ihty : forall (d : Nat), Eq KExpr (instantiate_at ty a d) (psubst (upn d (scons a idsubst)) ty)) (ihbd : forall (d : Nat), Eq KExpr (instantiate_at bd a d) (psubst (upn d (scons a idsubst)) bd)) (d : Nat) => Eq.trans KExpr (instantiate_at (KExpr.pi ty bd) a d) (KExpr.pi (psubst (upn d (scons a idsubst)) ty) (psubst (up (upn d (scons a idsubst))) bd)) (psubst (upn d (scons a idsubst)) (KExpr.pi ty bd)) (Eq.trans KExpr (instantiate_at (KExpr.pi ty bd) a d) (KExpr.pi (instantiate_at ty a d) (instantiate_at bd a (Nat.succ d))) (KExpr.pi (psubst (upn d (scons a idsubst)) ty) (psubst (up (upn d (scons a idsubst))) bd)) (instantiate_at_pi ty bd a d) (Eq.trans KExpr (KExpr.pi (instantiate_at ty a d) (instantiate_at bd a (Nat.succ d))) (KExpr.pi (psubst (upn d (scons a idsubst)) ty) (instantiate_at bd a (Nat.succ d))) (KExpr.pi (psubst (upn d (scons a idsubst)) ty) (psubst (up (upn d (scons a idsubst))) bd)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w (instantiate_at bd a (Nat.succ d))) (instantiate_at ty a d) (psubst (upn d (scons a idsubst)) ty) (ihty d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi (psubst (upn d (scons a idsubst)) ty) w) (instantiate_at bd a (Nat.succ d)) (psubst (up (upn d (scons a idsubst))) bd) (ihbd (Nat.succ d))))) (Eq.symm KExpr (psubst (upn d (scons a idsubst)) (KExpr.pi ty bd)) (KExpr.pi (psubst (upn d (scons a idsubst)) ty) (psubst (up (upn d (scons a idsubst))) bd)) (psubst_pi (upn d (scons a idsubst)) ty bd))) ",
                // const
                "(fun (nm : Name) (us : ListType Level) (d : Nat) => Eq.trans KExpr (instantiate_at (KExpr.const nm us) a d) (KExpr.const nm us) (psubst (upn d (scons a idsubst)) (KExpr.const nm us)) (instantiate_at_const nm us a d) (Eq.symm KExpr (psubst (upn d (scons a idsubst)) (KExpr.const nm us)) (KExpr.const nm us) (psubst_const (upn d (scons a idsubst)) nm us))) ",
                // let_
                "(fun (lty : KExpr) (lv : KExpr) (lb : KExpr) (ihty : forall (d : Nat), Eq KExpr (instantiate_at lty a d) (psubst (upn d (scons a idsubst)) lty)) (ihv : forall (d : Nat), Eq KExpr (instantiate_at lv a d) (psubst (upn d (scons a idsubst)) lv)) (ihb : forall (d : Nat), Eq KExpr (instantiate_at lb a d) (psubst (upn d (scons a idsubst)) lb)) (d : Nat) => Eq.trans KExpr (instantiate_at (KExpr.let_ lty lv lb) a d) (KExpr.let_ (psubst (upn d (scons a idsubst)) lty) (psubst (upn d (scons a idsubst)) lv) (psubst (up (upn d (scons a idsubst))) lb)) (psubst (upn d (scons a idsubst)) (KExpr.let_ lty lv lb)) (Eq.trans KExpr (instantiate_at (KExpr.let_ lty lv lb) a d) (KExpr.let_ (instantiate_at lty a d) (instantiate_at lv a d) (instantiate_at lb a (Nat.succ d))) (KExpr.let_ (psubst (upn d (scons a idsubst)) lty) (psubst (upn d (scons a idsubst)) lv) (psubst (up (upn d (scons a idsubst))) lb)) (instantiate_at_let_ lty lv lb a d) (Eq.trans KExpr (KExpr.let_ (instantiate_at lty a d) (instantiate_at lv a d) (instantiate_at lb a (Nat.succ d))) (KExpr.let_ (psubst (upn d (scons a idsubst)) lty) (instantiate_at lv a d) (instantiate_at lb a (Nat.succ d))) (KExpr.let_ (psubst (upn d (scons a idsubst)) lty) (psubst (upn d (scons a idsubst)) lv) (psubst (up (upn d (scons a idsubst))) lb)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w (instantiate_at lv a d) (instantiate_at lb a (Nat.succ d))) (instantiate_at lty a d) (psubst (upn d (scons a idsubst)) lty) (ihty d)) (Eq.trans KExpr (KExpr.let_ (psubst (upn d (scons a idsubst)) lty) (instantiate_at lv a d) (instantiate_at lb a (Nat.succ d))) (KExpr.let_ (psubst (upn d (scons a idsubst)) lty) (psubst (upn d (scons a idsubst)) lv) (instantiate_at lb a (Nat.succ d))) (KExpr.let_ (psubst (upn d (scons a idsubst)) lty) (psubst (upn d (scons a idsubst)) lv) (psubst (up (upn d (scons a idsubst))) lb)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (psubst (upn d (scons a idsubst)) lty) w (instantiate_at lb a (Nat.succ d))) (instantiate_at lv a d) (psubst (upn d (scons a idsubst)) lv) (ihv d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (psubst (upn d (scons a idsubst)) lty) (psubst (upn d (scons a idsubst)) lv) w) (instantiate_at lb a (Nat.succ d)) (psubst (up (upn d (scons a idsubst))) lb) (ihb (Nat.succ d)))))) (Eq.symm KExpr (psubst (upn d (scons a idsubst)) (KExpr.let_ lty lv lb)) (KExpr.let_ (psubst (upn d (scons a idsubst)) lty) (psubst (upn d (scons a idsubst)) lv) (psubst (up (upn d (scons a idsubst))) lb)) (psubst_let_ (upn d (scons a idsubst)) lty lv lb))) ",
                "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (ihsub : forall (d : Nat), Eq KExpr (instantiate_at sub a d) (psubst (upn d (scons a idsubst)) sub)) (d : Nat) => Eq.trans KExpr (instantiate_at (KExpr.proj ps pidx sub) a d) (KExpr.proj ps pidx (instantiate_at sub a d)) (psubst (upn d (scons a idsubst)) (KExpr.proj ps pidx sub)) (instantiate_at_proj ps pidx sub a d) (Eq.trans KExpr (KExpr.proj ps pidx (instantiate_at sub a d)) (KExpr.proj ps pidx (psubst (upn d (scons a idsubst)) sub)) (psubst (upn d (scons a idsubst)) (KExpr.proj ps pidx sub)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.proj ps pidx w) (instantiate_at sub a d) (psubst (upn d (scons a idsubst)) sub) (ihsub d)) (Eq.symm KExpr (psubst (upn d (scons a idsubst)) (KExpr.proj ps pidx sub)) (KExpr.proj ps pidx (psubst (upn d (scons a idsubst)) sub)) (psubst_proj (upn d (scons a idsubst)) ps pidx sub)))) ",
                "(fun (v : Nat) (d : Nat) => Eq.trans KExpr (instantiate_at (KExpr.lit v) a d) (KExpr.lit v) (psubst (upn d (scons a idsubst)) (KExpr.lit v)) (instantiate_at_lit v a d) (Eq.symm KExpr (psubst (upn d (scons a idsubst)) (KExpr.lit v)) (KExpr.lit v) (psubst_lit (upn d (scons a idsubst)) v))) ",
                "e",
            ).to_string()),
            is_axiom: false,
            description: "instantiate_at_eq_psubst: instantiate_at e a d = psubst (upn d (scons a idsubst)) e (guide line 1158). DerivedProved via KExpr.rec on e generalizing d; bvar case NatTrichotomy 3-way split (instantiate_bvar_at_{below,eq,above} vs upn_apply_{lt,ge} + lift_at_bvar_geq + nat_gt_sub_bridge). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(), "NatTrichotomy.rec".to_string(), "nat_trichotomy".to_string(),
                "instantiate_at".to_string(), "instantiate_bvar_at".to_string(), "psubst".to_string(),
                "upn".to_string(), "up".to_string(), "scons".to_string(), "idsubst".to_string(), "lift_at".to_string(),
                "instantiate_at_sort".to_string(), "instantiate_at_bvar".to_string(), "instantiate_at_app".to_string(),
                "instantiate_at_lam".to_string(), "instantiate_at_pi".to_string(), "instantiate_at_const".to_string(), "instantiate_at_let_".to_string(),
                "instantiate_bvar_at_below".to_string(), "instantiate_bvar_at_eq".to_string(), "instantiate_bvar_at_above".to_string(),
                "psubst_sort".to_string(), "psubst_bvar".to_string(), "psubst_app".to_string(),
                "psubst_lam".to_string(), "psubst_pi".to_string(), "psubst_const".to_string(), "psubst_let_".to_string(),
                "upn_apply_lt".to_string(), "upn_apply_ge".to_string(), "lift_at_bvar_geq".to_string(),
                "lt_sub_succ".to_string(), "le_sub_zero".to_string(), "lt_implies_le".to_string(),
                "nat_sub_self".to_string(), "nat_sub_zero_left".to_string(), "nat_gt_sub_bridge".to_string(),
                "Le.refl".to_string(), "Eq.trans".to_string(), "Eq.symm".to_string(), "Eq.cong".to_string(), "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_eq_psubst : instantiate e a = psubst (scons a idsubst) e
        // (guide line 1181). Depth-0 specialization of instantiate_at_eq_psubst
        // (instantiate e a defeq instantiate_at e a 0; upn 0 X defeq X).
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_eq_psubst".to_string(),
            type_src: "forall (e : KExpr) (a : KExpr), Eq KExpr (instantiate e a) (psubst (scons a idsubst) e)".to_string(),
            value_src: Some("fun (e : KExpr) (a : KExpr) => instantiate_at_eq_psubst e a Nat.zero".to_string()),
            is_axiom: false,
            description: "instantiate_eq_psubst: instantiate e a = psubst (scons a idsubst) e (guide line 1181). DerivedProved as instantiate_at_eq_psubst at depth 0 (instantiate defeq instantiate_at ..0, upn 0 defeq id). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate_at_eq_psubst".to_string(), "instantiate".to_string(), "psubst".to_string(),
                "scons".to_string(), "idsubst".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // psubst_instantiate : psubst s (instantiate B a) = instantiate (psubst
        // (up s) B) (psubst s a) — the fundamental app-case lemma (guide line 1220).
        // instantiate_eq_psubst + psubst_comp on both sides, then psubst_pointwise
        // over a Nat.rec index split (0 refl; succ via psubst_cancel + psubst_id).
        self.add_definition_structural(SpecDefinition {
            name: "psubst_instantiate".to_string(),
            type_src: "forall (B : KExpr) (a : KExpr) (s : Nat -> KExpr), Eq KExpr (psubst s (instantiate B a)) (instantiate (psubst (up s) B) (psubst s a))".to_string(),
            value_src: Some(concat!(
                "fun (B : KExpr) (a : KExpr) (s : Nat -> KExpr) => ",
                "Eq.trans KExpr (psubst s (instantiate B a)) (psubst (fun (i : Nat) => psubst s (scons a idsubst i)) B) (instantiate (psubst (up s) B) (psubst s a)) ",
                // LHS chain: psubst s (instantiate B a) = psubst (fun i => psubst s (scons a idsubst i)) B
                "(Eq.trans KExpr (psubst s (instantiate B a)) (psubst s (psubst (scons a idsubst) B)) (psubst (fun (i : Nat) => psubst s (scons a idsubst i)) B) (Eq.cong KExpr KExpr (fun (w : KExpr) => psubst s w) (instantiate B a) (psubst (scons a idsubst) B) (instantiate_eq_psubst B a)) (psubst_comp B s (scons a idsubst))) ",
                // REST: psubst (fun i => psubst s (scons a idsubst i)) B = instantiate (psubst (up s) B) (psubst s a)
                "(Eq.trans KExpr (psubst (fun (i : Nat) => psubst s (scons a idsubst i)) B) (psubst (fun (i : Nat) => psubst (scons (psubst s a) idsubst) (up s i)) B) (instantiate (psubst (up s) B) (psubst s a)) ",
                "(psubst_pointwise B (fun (i : Nat) => psubst s (scons a idsubst i)) (fun (i : Nat) => psubst (scons (psubst s a) idsubst) (up s i)) ",
                // pointwise: forall i, psubst s (scons a idsubst i) = psubst (scons (psubst s a) idsubst) (up s i)
                "(fun (i : Nat) => Nat.rec (fun (i0 : Nat) => Eq KExpr (psubst s (scons a idsubst i0)) (psubst (scons (psubst s a) idsubst) (up s i0))) (Eq.refl KExpr (psubst s a)) (fun (k : Nat) (_ih : Eq KExpr (psubst s (scons a idsubst k)) (psubst (scons (psubst s a) idsubst) (up s k))) => Eq.symm KExpr (psubst (scons (psubst s a) idsubst) (up s (Nat.succ k))) (psubst s (scons a idsubst (Nat.succ k))) (Eq.trans KExpr (psubst (scons (psubst s a) idsubst) (lift_at (s k) Nat.zero (Nat.succ Nat.zero))) (psubst idsubst (s k)) (s k) (psubst_cancel (s k) (psubst s a) idsubst) (psubst_id (s k)))) i)) ",
                // RHS chain (symm): instantiate (psubst (up s) B) (psubst s a) = psubst (fun i => psubst (scons (psubst s a) idsubst) (up s i)) B
                "(Eq.symm KExpr (instantiate (psubst (up s) B) (psubst s a)) (psubst (fun (i : Nat) => psubst (scons (psubst s a) idsubst) (up s i)) B) (Eq.trans KExpr (instantiate (psubst (up s) B) (psubst s a)) (psubst (scons (psubst s a) idsubst) (psubst (up s) B)) (psubst (fun (i : Nat) => psubst (scons (psubst s a) idsubst) (up s i)) B) (instantiate_eq_psubst (psubst (up s) B) (psubst s a)) (psubst_comp B (scons (psubst s a) idsubst) (up s)))))",
            ).to_string()),
            is_axiom: false,
            description: "psubst_instantiate: psubst s (instantiate B a) = instantiate (psubst (up s) B) (psubst s a), the fundamental app-case lemma (guide line 1220). DerivedProved via instantiate_eq_psubst + psubst_comp (both sides) + psubst_pointwise over a Nat.rec index split (succ: psubst_cancel + psubst_id). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate_eq_psubst".to_string(), "psubst_comp".to_string(), "psubst_pointwise".to_string(),
                "psubst_cancel".to_string(), "psubst_id".to_string(), "Nat.rec".to_string(),
                "psubst".to_string(), "up".to_string(), "scons".to_string(), "idsubst".to_string(), "instantiate".to_string(), "lift_at".to_string(),
                "Eq.trans".to_string(), "Eq.symm".to_string(), "Eq.cong".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // psubst_scons_instantiate : psubst (scons a s) b = instantiate (psubst
        // (up s) b) a — the fundamental lam head-expansion lemma (guide line 1233).
        // instantiate_eq_psubst + psubst_comp on the RHS, then psubst_pointwise over
        // a Nat.rec index split (0 refl; succ via psubst_cancel + psubst_id).
        self.add_definition_structural(SpecDefinition {
            name: "psubst_scons_instantiate".to_string(),
            type_src: "forall (b : KExpr) (a : KExpr) (s : Nat -> KExpr), Eq KExpr (psubst (scons a s) b) (instantiate (psubst (up s) b) a)".to_string(),
            value_src: Some(concat!(
                "fun (b : KExpr) (a : KExpr) (s : Nat -> KExpr) => ",
                "Eq.trans KExpr (psubst (scons a s) b) (psubst (fun (i : Nat) => psubst (scons a idsubst) (up s i)) b) (instantiate (psubst (up s) b) a) ",
                "(psubst_pointwise b (scons a s) (fun (i : Nat) => psubst (scons a idsubst) (up s i)) ",
                // pointwise: forall i, scons a s i = psubst (scons a idsubst) (up s i)
                "(fun (i : Nat) => Nat.rec (fun (i0 : Nat) => Eq KExpr (scons a s i0) (psubst (scons a idsubst) (up s i0))) (Eq.refl KExpr a) (fun (k : Nat) (_ih : Eq KExpr (scons a s k) (psubst (scons a idsubst) (up s k))) => Eq.symm KExpr (psubst (scons a idsubst) (up s (Nat.succ k))) (scons a s (Nat.succ k)) (Eq.trans KExpr (psubst (scons a idsubst) (lift_at (s k) Nat.zero (Nat.succ Nat.zero))) (psubst idsubst (s k)) (s k) (psubst_cancel (s k) a idsubst) (psubst_id (s k)))) i)) ",
                // RHS (symm): instantiate (psubst (up s) b) a = psubst (fun i => psubst (scons a idsubst) (up s i)) b
                "(Eq.symm KExpr (instantiate (psubst (up s) b) a) (psubst (fun (i : Nat) => psubst (scons a idsubst) (up s i)) b) (Eq.trans KExpr (instantiate (psubst (up s) b) a) (psubst (scons a idsubst) (psubst (up s) b)) (psubst (fun (i : Nat) => psubst (scons a idsubst) (up s i)) b) (instantiate_eq_psubst (psubst (up s) b) a) (psubst_comp b (scons a idsubst) (up s))))",
            ).to_string()),
            is_axiom: false,
            description: "psubst_scons_instantiate: psubst (scons a s) b = instantiate (psubst (up s) b) a, the fundamental lam head-expansion lemma (guide line 1233). DerivedProved via instantiate_eq_psubst + psubst_comp (RHS) + psubst_pointwise over a Nat.rec index split (succ: psubst_cancel + psubst_id). Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate_eq_psubst".to_string(), "psubst_comp".to_string(), "psubst_pointwise".to_string(),
                "psubst_cancel".to_string(), "psubst_id".to_string(), "Nat.rec".to_string(),
                "psubst".to_string(), "up".to_string(), "scons".to_string(), "idsubst".to_string(), "instantiate".to_string(), "lift_at".to_string(),
                "Eq.trans".to_string(), "Eq.symm".to_string(), "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // BRICK 2 — Tait adequacy (this batch): the 4 remaining CandModel
        // field accessors (red_sort / pi_elim / pi_intro / redConst), the 7
        // fundamental_* adequacy cases (incl. the let increment's fundamental_let),
        // fundamental_general (TypingCtx.rec
        // dispatch), and the top theorem whnf_terminates_well_typed_dependent.
        // Every decl is value-full (add_definition_structural) — ZERO new
        // kernel axioms, census stays 16 (M : CandModel is a hypothesis param).
        // ================================================================

        // red_sort accessor: whnf_acc e -> cm_Red tenv M (sort n) e (guide's
        // M.red_sort). CandModel.rec projection of the red_sort field.
        self.add_definition_structural(SpecDefinition {
            name: "red_sort".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (n : Level) (e : KExpr), whnf_acc e -> cm_Red tenv M (KExpr.sort n) e".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => forall (n : Level) (e : KExpr), whnf_acc e -> cm_Red tenv M0 (KExpr.sort n) e) {tel} M",
                tel = cm_tel("red_sort"),
            )),
            is_axiom: false,
            description: "red_sort accessor: whnf_acc e -> cm_Red tenv M (sort n) e (guide's M.red_sort). CandModel.rec projection of the red_sort field. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["CandModel.rec".to_string(), "cm_Red".to_string(), "whnf_acc".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // pi_elim accessor: the dependent Pi elimination clause (guide's M.pi_elim).
        self.add_definition_structural(SpecDefinition {
            name: "pi_elim".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr), cm_Red tenv M (KExpr.pi A B) f -> cm_Red tenv M A a -> cm_Red tenv M (instantiate B a) (KExpr.app f a)".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => forall (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr), cm_Red tenv M0 (KExpr.pi A B) f -> cm_Red tenv M0 A a -> cm_Red tenv M0 (instantiate B a) (KExpr.app f a)) {tel} M",
                tel = cm_tel("pi_elim"),
            )),
            is_axiom: false,
            description: "pi_elim accessor: cm_Red (pi A B) f -> cm_Red A a -> cm_Red (instantiate B a) (app f a) (guide's M.pi_elim). CandModel.rec projection of the pi_elim field. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["CandModel.rec".to_string(), "cm_Red".to_string(), "instantiate".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // pi_intro accessor: the dependent Pi introduction clause (guide's M.pi_intro).
        self.add_definition_structural(SpecDefinition {
            name: "pi_intro".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (A : KExpr) (B : KExpr) (f : KExpr), (forall (a : KExpr), cm_Red tenv M A a -> cm_Red tenv M (instantiate B a) (KExpr.app f a)) -> cm_Red tenv M (KExpr.pi A B) f".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => forall (A : KExpr) (B : KExpr) (f : KExpr), (forall (a : KExpr), cm_Red tenv M0 A a -> cm_Red tenv M0 (instantiate B a) (KExpr.app f a)) -> cm_Red tenv M0 (KExpr.pi A B) f) {tel} M",
                tel = cm_tel("pi_intro"),
            )),
            is_axiom: false,
            description: "pi_intro accessor: (forall a, cm_Red A a -> cm_Red (instantiate B a) (app f a)) -> cm_Red (pi A B) f (guide's M.pi_intro). CandModel.rec projection of the pi_intro field. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["CandModel.rec".to_string(), "cm_Red".to_string(), "instantiate".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // redConst accessor: defined constants are reducible at every substitution
        // instance of their declared type (guide's M.redConst).
        self.add_definition_structural(SpecDefinition {
            name: "redConst".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (n : Name) (us : ListType Level) (A : KExpr) (s : Nat -> KExpr), Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> cm_Red tenv M (psubst s A) (KExpr.const n us)".to_string(),
            value_src: Some(format!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) => CandModel.rec tenv (fun (M0 : CandModel tenv) => forall (n : Name) (us : ListType Level) (A : KExpr) (s : Nat -> KExpr), Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> cm_Red tenv M0 (psubst s A) (KExpr.const n us)) {tel} M",
                tel = cm_tel("redConst"),
            )),
            is_axiom: false,
            description: "redConst accessor: tenv n = some A -> cm_Red (psubst s A) (const n us) (guide's M.redConst). CandModel.rec projection of the redConst field. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["CandModel.rec".to_string(), "cm_Red".to_string(), "psubst".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // fundamental_var: a modelling substitution sends each context variable to a
        // term reducible at the (psubst, lifted) declared type. Guide fundamental_var
        // (line 1898): the Models lookup itself (psubst s (bvar i) defeq s i).
        self.add_definition_structural(SpecDefinition {
            name: "fundamental_var".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (i : Nat) (A : KExpr), Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (lift_at A Nat.zero (Nat.succ i))) (psubst s (KExpr.bvar i))".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (i : Nat) (A : KExpr) (hget : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) (s : Nat -> KExpr) (hs : Models tenv M s G) => ",
                "hs i A hget",
            ).to_string()),
            is_axiom: false,
            description: "fundamental_var (guide line 1898): the Models lookup gives cm_Red at the lifted type (psubst s (bvar i) defeq s i). DerivedProved. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Models".to_string(), "cm_Red".to_string(), "ctx_lookup".to_string(),
                "psubst".to_string(), "lift_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fundamental_sort (guide line 1905): sorts are reducible at the next sort via
        // red_sort + whnfAcc_sort. psubst on sort reduces definitionally.
        self.add_definition_structural(SpecDefinition {
            name: "fundamental_sort".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (n : Level), forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (KExpr.sort (Level.succ n))) (psubst s (KExpr.sort n))".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (n : Level) (s : Nat -> KExpr) (_hs : Models tenv M s G) => ",
                "red_sort tenv M (Level.succ n) (KExpr.sort n) (whnfAcc_sort n)",
            ).to_string()),
            is_axiom: false,
            description: "fundamental_sort (guide line 1905): red_sort at the next sort with whnfAcc_sort (psubst on sort reduces). DerivedProved. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_sort".to_string(), "whnfAcc_sort".to_string(), "cm_Red".to_string(),
                "Models".to_string(), "psubst".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fundamental_pi (guide line 1911): red_sort at the imax universe, using
        // whnfAcc_pi (SN-closure under pi) and whnfAcc_of_instantiate_bvar0 for the
        // codomain SN (the codomain reducibility comes from the extended-context IH at
        // the fresh variable bvar 0, reshaped by psubst_scons_instantiate).
        self.add_definition_structural(SpecDefinition {
            name: "fundamental_pi".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level), (forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (KExpr.sort n)) (psubst s A)) -> (forall (s : Nat -> KExpr), Models tenv M s (ListType.cons KExpr A G) -> cm_Red tenv M (psubst s (KExpr.sort m)) (psubst s B)) -> forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (KExpr.sort (Level.imax n m))) (psubst s (KExpr.pi A B))".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) ",
                "(ihA : forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (KExpr.sort n)) (psubst s A)) ",
                "(ihB : forall (s : Nat -> KExpr), Models tenv M s (ListType.cons KExpr A G) -> cm_Red tenv M (psubst s (KExpr.sort m)) (psubst s B)) ",
                "(s : Nat -> KExpr) (hs : Models tenv M s G) => ",
                "red_sort tenv M (Level.imax n m) (KExpr.pi (psubst s A) (psubst (up s) B)) ",
                "(whnfAcc_pi (psubst s A) (psubst (up s) B) ",
                "(CR1 tenv M (psubst s (KExpr.sort n)) (psubst s A) (ihA s hs)) ",
                "(whnfAcc_of_instantiate_bvar0 (psubst (up s) B) ",
                "(Eq.substType KExpr (fun (w : KExpr) => whnf_acc w) (psubst (scons (KExpr.bvar Nat.zero) s) B) (instantiate (psubst (up s) B) (KExpr.bvar Nat.zero)) ",
                "(psubst_scons_instantiate B (KExpr.bvar Nat.zero) s) ",
                "(CR1 tenv M (psubst (scons (KExpr.bvar Nat.zero) s) (KExpr.sort m)) (psubst (scons (KExpr.bvar Nat.zero) s) B) ",
                "(ihB (scons (KExpr.bvar Nat.zero) s) (models_extend tenv M s G A (KExpr.bvar Nat.zero) (red_var tenv M (psubst s A) Nat.zero) hs))))))",
            ).to_string()),
            is_axiom: false,
            description: "fundamental_pi (guide line 1911): red_sort at the imax universe via whnfAcc_pi + whnfAcc_of_instantiate_bvar0; codomain SN from the extended-context IH at bvar 0 reshaped by psubst_scons_instantiate. DerivedProved. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "red_sort".to_string(), "whnfAcc_pi".to_string(), "whnfAcc_of_instantiate_bvar0".to_string(),
                "CR1".to_string(), "cm_Red".to_string(), "Models".to_string(), "models_extend".to_string(),
                "red_var".to_string(), "psubst_scons_instantiate".to_string(), "psubst".to_string(),
                "up".to_string(), "scons".to_string(), "instantiate".to_string(), "imax_nat".to_string(),
                "Eq.substType".to_string(), "whnf_acc".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fundamental_lam (guide line 1929, THE substantive case): pi_intro +
        // redAbstraction_holds (Tait weak-head-expansion), lifting the body IH under the
        // extended substitution via psubst_scons_instantiate (twice: type + term).
        self.add_definition_structural(SpecDefinition {
            name: "fundamental_lam".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level), (forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (KExpr.sort u)) (psubst s A)) -> (forall (s : Nat -> KExpr), Models tenv M s (ListType.cons KExpr A G) -> cm_Red tenv M (psubst s B) (psubst s b)) -> forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (KExpr.pi A B)) (psubst s (KExpr.lam A b))".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) ",
                "(ihA : forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (KExpr.sort u)) (psubst s A)) ",
                "(ihb : forall (s : Nat -> KExpr), Models tenv M s (ListType.cons KExpr A G) -> cm_Red tenv M (psubst s B) (psubst s b)) ",
                "(s : Nat -> KExpr) (hs : Models tenv M s G) => ",
                "pi_intro tenv M (psubst s A) (psubst (up s) B) (KExpr.lam (psubst s A) (psubst (up s) b)) ",
                "(redAbstraction_holds tenv M (psubst s A) (psubst (up s) b) (psubst (up s) B) ",
                "(CR1 tenv M (psubst s (KExpr.sort u)) (psubst s A) (ihA s hs)) ",
                "(fun (a : KExpr) (ha : cm_Red tenv M (psubst s A) a) => ",
                "Eq.substType KExpr (fun (w : KExpr) => cm_Red tenv M w (instantiate (psubst (up s) b) a)) (psubst (scons a s) B) (instantiate (psubst (up s) B) a) (psubst_scons_instantiate B a s) ",
                "(Eq.substType KExpr (fun (w : KExpr) => cm_Red tenv M (psubst (scons a s) B) w) (psubst (scons a s) b) (instantiate (psubst (up s) b) a) (psubst_scons_instantiate b a s) ",
                "(ihb (scons a s) (models_extend tenv M s G A a ha hs)))))",
            ).to_string()),
            is_axiom: false,
            description: "fundamental_lam (guide line 1929, substantive case): pi_intro + redAbstraction_holds head-expansion, lifting the body IH under the extended substitution via psubst_scons_instantiate (type + term). DerivedProved. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "pi_intro".to_string(), "redAbstraction_holds".to_string(), "CR1".to_string(),
                "cm_Red".to_string(), "Models".to_string(), "models_extend".to_string(),
                "psubst_scons_instantiate".to_string(), "psubst".to_string(), "up".to_string(),
                "scons".to_string(), "instantiate".to_string(), "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fundamental_app (guide line 1947): pi_elim on the two IHs, then reshape the
        // codomain instantiation back through the substitution via psubst_instantiate.
        self.add_definition_structural(SpecDefinition {
            name: "fundamental_app".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr), (forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (KExpr.pi A B)) (psubst s f)) -> (forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s A) (psubst s a)) -> forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (instantiate B a)) (psubst s (KExpr.app f a))".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) ",
                "(ihf : forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (KExpr.pi A B)) (psubst s f)) ",
                "(iha : forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s A) (psubst s a)) ",
                "(s : Nat -> KExpr) (hs : Models tenv M s G) => ",
                "Eq.substType KExpr (fun (w : KExpr) => cm_Red tenv M w (KExpr.app (psubst s f) (psubst s a))) (instantiate (psubst (up s) B) (psubst s a)) (psubst s (instantiate B a)) ",
                "(Eq.symm KExpr (psubst s (instantiate B a)) (instantiate (psubst (up s) B) (psubst s a)) (psubst_instantiate B a s)) ",
                "(pi_elim tenv M (psubst s A) (psubst (up s) B) (psubst s f) (psubst s a) (ihf s hs) (iha s hs))",
            ).to_string()),
            is_axiom: false,
            description: "fundamental_app (guide line 1947): pi_elim on the two IHs, then reshape the codomain via psubst_instantiate (psubst s (app f a) defeq app (psubst s f) (psubst s a)). DerivedProved. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "pi_elim".to_string(), "cm_Red".to_string(), "Models".to_string(),
                "psubst_instantiate".to_string(), "psubst".to_string(), "up".to_string(),
                "instantiate".to_string(), "Eq.substType".to_string(), "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fundamental_const (guide line 1963): a defined constant is reducible at every
        // substitution instance of its declared type via redConst (psubst s (const n us)
        // defeq const n us).
        self.add_definition_structural(SpecDefinition {
            name: "fundamental_const".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr), Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s A) (psubst s (KExpr.const n us))".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) (hget : Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A)) (s : Nat -> KExpr) (_hs : Models tenv M s G) => ",
                "redConst tenv M n us A s hget",
            ).to_string()),
            is_axiom: false,
            description: "fundamental_const (guide line 1963): redConst gives cm_Red at every substitution instance of the declared type (psubst s (const n us) defeq const n us). DerivedProved. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "redConst".to_string(), "cm_Red".to_string(), "Models".to_string(), "psubst".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fundamental_let (LET INCREMENT, task #28; guide SnLet.lean:2181): the
        // Tait adequacy case for the dependent let — fundamental_lam and
        // fundamental_app fused. Rewrite the type through psubst_instantiate
        // (psubst s (instantiate B v) = instantiate (psubst (up s) B) (psubst s v)),
        // then redLet_holds with A := psubst s ty, b := psubst (up s) b,
        // B := psubst (up s) B, a := psubst s v: the annotation SN from CR1 on the
        // ty IH; the body premise from the ihb at the extended substitution
        // (models_extend), reshaped through psubst_scons_instantiate twice (exactly
        // fundamental_lam's inner step); the bound-value reducibility is ihv s hs.
        // psubst s (let_ ty v b) reduces definitionally to
        // let_ (psubst s ty) (psubst s v) (psubst (up s) b).
        self.add_definition_structural(SpecDefinition {
            name: "fundamental_let".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level), (forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (KExpr.sort u)) (psubst s ty)) -> (forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s ty) (psubst s v)) -> (forall (s : Nat -> KExpr), Models tenv M s (ListType.cons KExpr ty G) -> cm_Red tenv M (psubst s B) (psubst s b)) -> forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (instantiate B v)) (psubst s (KExpr.let_ ty v b))".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level) ",
                "(ihty : forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s (KExpr.sort u)) (psubst s ty)) ",
                "(ihv : forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s ty) (psubst s v)) ",
                "(ihb : forall (s : Nat -> KExpr), Models tenv M s (ListType.cons KExpr ty G) -> cm_Red tenv M (psubst s B) (psubst s b)) ",
                "(s : Nat -> KExpr) (hs : Models tenv M s G) => ",
                "Eq.substType KExpr (fun (w : KExpr) => cm_Red tenv M w (KExpr.let_ (psubst s ty) (psubst s v) (psubst (up s) b))) (instantiate (psubst (up s) B) (psubst s v)) (psubst s (instantiate B v)) ",
                "(Eq.symm KExpr (psubst s (instantiate B v)) (instantiate (psubst (up s) B) (psubst s v)) (psubst_instantiate B v s)) ",
                "(redLet_holds tenv M (psubst s ty) (psubst (up s) b) (psubst (up s) B) ",
                "(CR1 tenv M (psubst s (KExpr.sort u)) (psubst s ty) (ihty s hs)) ",
                "(fun (a : KExpr) (ha : cm_Red tenv M (psubst s ty) a) => ",
                "Eq.substType KExpr (fun (w : KExpr) => cm_Red tenv M w (instantiate (psubst (up s) b) a)) (psubst (scons a s) B) (instantiate (psubst (up s) B) a) (psubst_scons_instantiate B a s) ",
                "(Eq.substType KExpr (fun (w : KExpr) => cm_Red tenv M (psubst (scons a s) B) w) (psubst (scons a s) b) (instantiate (psubst (up s) b) a) (psubst_scons_instantiate b a s) ",
                "(ihb (scons a s) (models_extend tenv M s G ty a ha hs)))) ",
                "(psubst s v) (ihv s hs))",
            ).to_string()),
            is_axiom: false,
            description: "fundamental_let (guide SnLet.lean:2181, LET INCREMENT task #28): the Tait adequacy case for the dependent let — redLet_holds (zeta weak-head-expansion) with the codomain reshaped via psubst_instantiate and the body IH lifted under the extended substitution via psubst_scons_instantiate (type + term, exactly fundamental_lam's inner step); the bound value's reducibility is the ihv. DerivedProved. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "redLet_holds".to_string(), "CR1".to_string(), "cm_Red".to_string(),
                "Models".to_string(), "models_extend".to_string(),
                "psubst_instantiate".to_string(), "psubst_scons_instantiate".to_string(),
                "psubst".to_string(), "up".to_string(), "scons".to_string(), "instantiate".to_string(),
                "Eq.substType".to_string(), "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // fundamental_general (guide line 1974): the parallel-substitution-general
        // Tait fundamental theorem, by TypingCtx.rec dispatch to the 7 cases (incl.
        // the let increment's trailing fundamental_let minor). Motive
        // fun G e T _h => forall s, Models tenv M s G -> cm_Red tenv M (psubst s T) (psubst s e).
        self.add_definition_structural(SpecDefinition {
            name: "fundamental_general".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (e : KExpr) (T : KExpr), TypingCtx tenv G e T -> forall (s : Nat -> KExpr), Models tenv M s G -> cm_Red tenv M (psubst s T) (psubst s e)".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : TypingCtx tenv G e T) => ",
                "TypingCtx.rec tenv ",
                "(fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) (_h : TypingCtx tenv G0 e0 T0) => forall (s : Nat -> KExpr), Models tenv M s G0 -> cm_Red tenv M (psubst s T0) (psubst s e0)) ",
                "(fun (G0 : ListType KExpr) (i : Nat) (A : KExpr) (hget : Eq (OptionType KExpr) (ctx_lookup G0 i) (OptionType.some KExpr A)) => fundamental_var tenv M G0 i A hget) ",
                "(fun (G0 : ListType KExpr) (n : Level) => fundamental_sort tenv M G0 n) ",
                "(fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) (hA : TypingCtx tenv G0 A (KExpr.sort n)) (hB : TypingCtx tenv (ListType.cons KExpr A G0) B (KExpr.sort m)) (ihA : forall (s : Nat -> KExpr), Models tenv M s G0 -> cm_Red tenv M (psubst s (KExpr.sort n)) (psubst s A)) (ihB : forall (s : Nat -> KExpr), Models tenv M s (ListType.cons KExpr A G0) -> cm_Red tenv M (psubst s (KExpr.sort m)) (psubst s B)) => fundamental_pi tenv M G0 A B n m ihA ihB) ",
                "(fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) (hA : TypingCtx tenv G0 A (KExpr.sort u)) (hb : TypingCtx tenv (ListType.cons KExpr A G0) b B) (ihA : forall (s : Nat -> KExpr), Models tenv M s G0 -> cm_Red tenv M (psubst s (KExpr.sort u)) (psubst s A)) (ihb : forall (s : Nat -> KExpr), Models tenv M s (ListType.cons KExpr A G0) -> cm_Red tenv M (psubst s B) (psubst s b)) => fundamental_lam tenv M G0 A b B u ihA ihb) ",
                "(fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) (hf : TypingCtx tenv G0 f (KExpr.pi A B)) (ha : TypingCtx tenv G0 a A) (ihf : forall (s : Nat -> KExpr), Models tenv M s G0 -> cm_Red tenv M (psubst s (KExpr.pi A B)) (psubst s f)) (iha : forall (s : Nat -> KExpr), Models tenv M s G0 -> cm_Red tenv M (psubst s A) (psubst s a)) => fundamental_app tenv M G0 f a A B ihf iha) ",
                "(fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) (hget : Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A)) => fundamental_const tenv M G0 n us A hget) ",
                "(fun (G0 : ListType KExpr) (lty : KExpr) (lv : KExpr) (lb : KExpr) (B : KExpr) (u : Level) (hty : TypingCtx tenv G0 lty (KExpr.sort u)) (hv : TypingCtx tenv G0 lv lty) (hb : TypingCtx tenv (ListType.cons KExpr lty G0) lb B) (ihty : forall (s : Nat -> KExpr), Models tenv M s G0 -> cm_Red tenv M (psubst s (KExpr.sort u)) (psubst s lty)) (ihv : forall (s : Nat -> KExpr), Models tenv M s G0 -> cm_Red tenv M (psubst s lty) (psubst s lv)) (ihb : forall (s : Nat -> KExpr), Models tenv M s (ListType.cons KExpr lty G0) -> cm_Red tenv M (psubst s B) (psubst s lb)) => fundamental_let tenv M G0 lty lv lb B u ihty ihv ihb) ",
                "G e T h",
            ).to_string()),
            is_axiom: false,
            description: "fundamental_general (guide line 1974): the parallel-substitution Tait fundamental theorem by TypingCtx.rec dispatch to the 7 fundamental_* cases (incl. fundamental_let, the let increment). DerivedProved. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtx.rec".to_string(), "cm_Red".to_string(), "Models".to_string(), "psubst".to_string(),
                "ctx_lookup".to_string(), "imax_nat".to_string(),
                "fundamental_var".to_string(), "fundamental_sort".to_string(), "fundamental_pi".to_string(),
                "fundamental_lam".to_string(), "fundamental_app".to_string(), "fundamental_const".to_string(), "fundamental_let".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // whnf_terminates_well_typed_dependent (guide line 2058): every CLOSED
        // well-typed term of the dependent judgment is strongly normalizing —
        // specialize fundamental_general to idsubst (models the empty context),
        // collapse psubst idsubst _ = _ via psubst_id (both sides), then CR1.
        // BRICK 2 COMPLETE: the dependent SN theorem, modulo the M : CandModel hypothesis.
        self.add_definition_structural(SpecDefinition {
            name: "whnf_terminates_well_typed_dependent".to_string(),
            type_src: "forall (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (e : KExpr) (T : KExpr), TypingCtx tenv (ListType.nil KExpr) e T -> whnf_acc e".to_string(),
            value_src: Some(concat!(
                "fun (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (e : KExpr) (T : KExpr) (h : TypingCtx tenv (ListType.nil KExpr) e T) => ",
                "CR1 tenv M T e ",
                "(Eq.substType KExpr (fun (w : KExpr) => cm_Red tenv M T w) (psubst idsubst e) e (psubst_id e) ",
                "(Eq.substType KExpr (fun (w : KExpr) => cm_Red tenv M w (psubst idsubst e)) (psubst idsubst T) T (psubst_id T) ",
                "(fundamental_general tenv M (ListType.nil KExpr) e T h idsubst (models_idsubst tenv M (ListType.nil KExpr)))))",
            ).to_string()),
            is_axiom: false,
            description: "whnf_terminates_well_typed_dependent (guide line 2058, BRICK 2 top theorem): every closed well-typed dependent term is whnf_acc, modulo M : CandModel. fundamental_general at idsubst + psubst_id collapse + CR1. DerivedProved. Zero axiom_deps.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CR1".to_string(), "fundamental_general".to_string(), "models_idsubst".to_string(),
                "psubst_id".to_string(), "cm_Red".to_string(), "psubst".to_string(), "idsubst".to_string(),
                "Eq.substType".to_string(), "whnf_acc".to_string(), "TypingCtx".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "dependent_sn_richmodel_tests.rs"]
mod dependent_sn_richmodel_tests;
