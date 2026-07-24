// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Faithful KernelInferAccepts + KernelCheckAccepts inductives + master
//! inversion (#461, Steps 3 + 4).
//!
//! KernelInferAccepts was previously an opaque HelperAxiom of type
//! `KernelState -> KExpr -> KExpr -> Type` (implementation_soundness.rs), with
//! six per-case HelperAxioms asserting what a successful inference implies for
//! each `KExpr` arm. This module replaces the opaque token with a faithful
//! 5-constructor inductive (sort/const/app/lam/pi, NO bvar) and derives all six
//! per-case axioms from ONE master inversion (`kernel_infer_inversion`) over a
//! semireducible index-family motive (`InferInversionAt`).
//!
//! Step 4 additionally replaces the opaque KernelCheckAccepts token with a
//! faithful single-constructor inductive (check_type = infer_type + is_def_eq,
//! registered here because its mk constructor references KernelInferAccepts /
//! KernelInferResult); the app constructor of KernelInferAccepts inlines the
//! token's exact content (the check/infer mutual recursion has no
//! mutual-inductive registration path), and the master inversion's app minor
//! rebuilds the token via KernelCheckAccepts.mk so every downstream statement
//! stays byte-identical. kernel_check_decomposition and
//! kernel_check_types_admissible flip to KernelCheckAccepts.rec projections in
//! implementation_soundness_check_decomposition.rs.
//!
//! Contents, in registration order (the order is load-bearing — the inductives'
//! constructor fields bind at the skolem applications, so the skolems must
//! precede them; same rule as Step 2's KernelDefEqNormalLeft/Right move):
//! - the 9 infer-band Skolem witnesses (moved from
//!   implementation_soundness_check_decomposition.rs /
//!   implementation_soundness_infer_refinement_app.rs /
//!   implementation_soundness_infer_refinement_binder.rs) — still opaque
//!   HelperAxioms, the residual named trust content of the infer model
//! - the faithful `KernelInferAccepts` inductive
//! - the faithful `KernelCheckAccepts` inductive (Step 4; after
//!   KernelInferAccepts, whose acceptance its mk field packages)
//! - `InferInversionAt`: semireducible per-shape payload family (KExpr.rec)
//! - `kernel_infer_inversion`: the single eliminator every flip projects from
//! - `kernel_infer_bvar_empty`: bvar acceptance is uninhabited (free corollary)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    pub(super) fn add_implementation_soundness_infer_accepts(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // Infer-band Skolem witnesses (moved here; must precede the
        // inductive whose constructor fields apply them)
        // =========================================================

        // ── KernelInferResult — DELETED (census 13->12) ──────────────────
        // Was: opaque Skolem `KernelState -> KExpr -> KExpr` = "the unique type
        // infer_type returns", the determinism anchor threaded (as a named term)
        // through KernelInferAccepts.app's recursive index + BOTH halves of
        // KernelCheckAccepts.mk's pair + tc_check_completeness's conclusion.
        // RETIRED by the existential reframe (Stage 1): every consumer now BINDS
        // the inferred sub-result as an existential constructor argument (Rf/Ra
        // on KernelInferAccepts.app + AppInferWitness; one R on
        // KernelCheckAccepts.mk shared across both pair halves) — the shipped
        // DefEqJoinable packaged-existential pattern (same as the six infer-band
        // skolems retired below). No name, no determinism lemma needed; the
        // shared value is preserved by the BINDING. Hypothesis-position
        // WEAKENING (larger accept set: "exists R inferable-and-defeq" vs "at the
        // skolem") — SAFE, since KernelInferAccepts/KernelCheckAccepts are
        // hypothesis-position in the *_returns_well_typed soundness bridges, so
        // the model stays a faithful OVER-approximation (real infer(e) is always
        // a witness R). Zero new axioms; only hypotheses weaken, no soundness
        // conclusion. Determinism was OFF-PATH (a masquerade risk — infer is not
        // zero-axiom deterministic over the faithful existential inductives).

        // KernelLamBodyAdmissible / KernelPiBodyAdmissible RETIRED (census
        // 18->16): these two opaque binder-admissibility guards sat in the .fst
        // slot of the lam/pi constructor's ProdType (guard) (witness) field but
        // were VESTIGIAL — every soundness consumer (kernel_infer_lam_sound /
        // kernel_infer_pi_sound) projected ProdType.snd (the witness) and
        // discarded the guard; the only .fst projections
        // (kernel_infer_lam_body_step / kernel_infer_pi_body_step) were
        // dead-ends consumed by nothing. The lam/pi ctor fields now conclude in
        // the Lam/PiInferWitness existentials DIRECTLY (no ProdType wrapper).
        // Hypothesis-weakening retirement: KernelInferAccepts is
        // hypothesis-position in the *_sound bridges, so dropping a premise
        // makes accept->has_type hold for MORE inputs (the safe direction). Only
        // KernelInferResult survives as an infer-band skolem.

        // =========================================================
        // Packaged-existential witness inductives (retire 6 skolems)
        // =========================================================
        //
        // AppInferWitness / LamInferWitness / PiInferWitness are the app/lam/pi
        // analogues of Step 2's DefEqJoinable: single-constructor inductives whose
        // `mk` binds the formerly-Skolem sub-results INTERNALLY (as
        // existentially-quantified ctor arguments) instead of naming them by
        // opaque Skolem FUNCTIONS of (st, e). They RETIRE the six infer-band
        // Skolems — KernelInferAppPiDomain / KernelInferAppPiCodomain (app pi
        // domain/codomain), KernelLamBodyType / KernelLamDomainLevel (lam body
        // type / domain level), KernelPiDomainLevel / KernelPiCodomainLevel (pi
        // domain/codomain levels) — leaving the ConstantKind::Axiom census (each
        // is a real `add_inductive`, NOT a value-less axiom; its `.mk`/`.rec` are
        // kernel-generated and sound by construction).
        //
        // Each packages EXACTLY the old skolem-named tuple's typing content, but
        // with the reducts/levels bound as existentials rather than pinned by
        // Skolem functions of the inputs — the honest reduction vocabulary. The
        // typing fields PIN those existentials: LamInferWitness carries
        // `Typing A (sort dl)` (dl is A's actual sort level) and `Typing body bt`
        // (bt is body's actual type); PiInferWitness carries `Typing A (sort dom)`
        // and `Typing B (sort cod)` so `sort (imax_nat dom cod)` is the genuine
        // Pi type, not a free level; AppInferWitness carries the WHNF-to-Pi of the
        // (kept) KernelInferResult st f, the arg-defeq to the bound domain, the
        // instantiated-codomain result, and the check-step admissibility guard
        // (which references the bound domain, so it lives INSIDE the witness).
        // Single-ctor uniform conclusions, so the elaborator promotes the leading
        // binders to inductive parameters — the AndType.rec (param-fixed, motive
        // over the major only) shape of DefEqJoinable, verified by the recursor
        // diagnostic. The `*_sound` bridges eliminate each witness to the
        // skolem-free `has_type (…) T` (motive not mentioning the bound
        // sub-results — the def_eq_joinable_reflects precedent). Registered BEFORE
        // KernelInferAccepts because its app/lam/pi constructor fields conclude in
        // these witnesses. AppInferWitness follows KernelInferResult (its fields
        // reference KernelInferResult st f / st a).
        self.add_inductive(
            r"inductive AppInferWitness : KernelState → KExpr → KExpr → KExpr → KExpr → Type
| mk : forall (st : KernelState) (Rf : KExpr) (Ra : KExpr) (a : KExpr) (T : KExpr) (dom : KExpr) (cod : KExpr), KernelWhnfAccepts st Rf (KExpr.pi dom cod) → KernelDefEqAccepts st Ra dom → Eq KExpr (instantiate cod a) T → (KernelStateEnvValid st → KernelStateLocalCtxWellFormed st → KernelInputAdmissible st a → KernelBinaryInputAdmissible st Ra dom) → AppInferWitness st Rf Ra a T",
            "App-case inference witness: AppInferWitness st Rf Ra a T packages the app branch's \
             pi-decomposition of the EXISTENTIALLY-BOUND inferred function type Rf and argument \
             type Ra (the un-Skolemization retiring KernelInferResult: Rf/Ra are now explicit \
             indices, formerly KernelInferResult st f / st a). The single mk constructor binds the \
             Pi domain/codomain dom/cod INTERNALLY (the packaged existential retiring \
             KernelInferAppPiDomain/Codomain), carrying: WHNF of Rf to Pi(dom, cod); def-eq of Ra \
             to dom; the instantiated-codomain result tied by syntactic Eq to T; and the guarded check-step \
             admissibility at (Ra, dom). Eliminated to the skolem-free has_type via \
             kernel_infer_app_sound.",
        )?;

        self.add_inductive(
            r"inductive LamInferWitness : KExpr → KExpr → KExpr → KExpr → Type
| mk : forall (A : KExpr) (body : KExpr) (bt : KExpr) (T : KExpr) (dl : Level), Typing A (KExpr.sort dl) → Typing body bt → Eq KExpr (KExpr.pi A bt) T → LamInferWitness A body bt T",
            "Lam-case inference witness: LamInferWitness A body bt T packages the lam branch's typing \
             content, with the body type bt now an EXPLICIT INDEX (exposed at the constructor level so \
             the KernelInferAccepts.lam recursive body-infer premise can share it — the AppInferWitness \
             Rf/Ra un-Skolemization pattern applied to the lam body). The single mk constructor binds \
             the domain level dl INTERNALLY (the packaged existential retiring KernelLamDomainLevel), \
             carrying: Typing A (sort dl) (dl is A's actual sort level); Typing body bt (bt is the \
             body's actual type); and syntactic Eq of Pi(A, bt) to the returned T. Eliminated to the \
             skolem-free has_type via kernel_infer_lam_sound (through LamInferDecomp).",
        )?;

        self.add_inductive(
            r"inductive PiInferWitness : KExpr → KExpr → KExpr → Type
| mk : forall (A : KExpr) (B : KExpr) (T : KExpr) (dom : Level) (cod : Level), Typing A (KExpr.sort dom) → Typing B (KExpr.sort cod) → Eq KExpr (KExpr.sort (Level.imax dom cod)) T → PiInferWitness A B T",
            "Pi-case inference witness: PiInferWitness A B T packages the pi branch's typing \
             content. The single mk constructor binds the domain/codomain levels dom/cod INTERNALLY \
             (the packaged existential retiring KernelPiDomainLevel/KernelPiCodomainLevel), \
             carrying: Typing A (sort dom) and Typing B (sort cod) (dom/cod are A's/B's actual sort \
             levels, so sort (imax_nat dom cod) is the genuine Pi type — not a free level); and \
             syntactic Eq of that imax sort to the returned T. Eliminated to the skolem-free has_type via \
             kernel_infer_pi_sound.",
        )?;

        // =========================================================
        // The faithful KernelInferAccepts inductive
        // =========================================================
        //
        // KernelInferAccepts was previously an opaque HelperAxiom of type
        // `KernelState -> KExpr -> KExpr -> Type`. It is now a FAITHFUL
        // 5-constructor inductive: one constructor per KExpr arm with a success
        // path in the production kernel's infer_type (check-mode/infer_only=false
        // path — the one check_type and add_decl run). Each constructor's fields
        // are byte-level copies of what the formerly-assumed per-case axiom for
        // that arm asserted — THAT AXIOM'S OWN GUARD STRUCTURE INCLUDED:
        //  - sort: unguarded `Eq KExpr (sort (succ l)) T` (= kernel_infer_sort_result,
        //    which was unguarded — the return value is a state-independent fact);
        //  - const: the GUARDED implication EnvValid -> CtxWF -> InputAdmissible ->
        //    has_type (= kernel_infer_const_sound verbatim; state-dependent);
        //  - app: field1 = the recursive premise KernelInferAccepts st f
        //    (KernelInferResult st f); field2 = the recursive argument-infer
        //    premise KernelInferAccepts st a (KernelInferResult st a) (the
        //    check step's infer half — see the Step-4 note below); field3 =
        //    the whnf-to-Pi x arg-defeq x defeq-result tuple (the middle
        //    component is the check step's defeq half); field4 = the check
        //    step's GUARDED admissibility implication at (a, Pi-domain);
        //    field5 = the GUARDED fun-type admissibility implication
        //    (= kernel_infer_app_fun_type_admissible verbatim). Fields 1+3
        //    with the check token rebuilt from fields 2+3+4 (via
        //    KernelCheckAccepts.mk in the master inversion's app minor)
        //    repackage kernel_infer_app_decomposition's unguarded 4-tuple
        //    verbatim. Recursive fields are split OUT of the ProdType tuple
        //    because a KernelInferAccepts occurrence nested inside ProdType
        //    would be a nested-inductive occurrence — as direct fields they
        //    are standard strictly-positive recursive arguments, precedent
        //    KernelWhnfAccepts.step;
        //  - lam/pi: the exact unguarded 4-/5-tuples of
        //    kernel_infer_lam_decomposition / kernel_infer_pi_decomposition.
        //    DELIBERATE exact-strength preservation: those axioms assert spec-level
        //    Typing facts unguarded (the FVar-model gap jump). Guarding them here
        //    would CHANGE the registered assumption's strength; the known overreach
        //    (spec Typing asserted in arbitrary states) is pre-existing registered
        //    trust content, unchanged in strength — the next honesty target.
        //
        // Per-axiom guard preservation is the Step-2 rule instantiated per-case:
        // an unguarded field where the old axiom was guarded would silently
        // STRENGTHEN every producer axiom concluding an Accepts (the Step-2
        // adversarial audit caught exactly that); a guarded field where the old
        // axiom was unguarded would WEAKEN the assumed content. Both are
        // masquerades; neither is done here.
        //
        // STEP-4 NOTE (the forced app-constructor edit): the app constructor
        // originally carried the argument check step as the opaque token
        // `KernelCheckAccepts st a (KernelInferAppPiDomain st f a)` nested in
        // its tuple field. Step 4 converts KernelCheckAccepts itself into a
        // faithful inductive whose mk constructor references KernelInferAccepts
        // (check_type = infer_type + is_def_eq), so the two acceptance families
        // are MUTUALLY recursive in the real kernel. The registration pipeline
        // has no mutual-inductive path (Specification::add_inductive handles
        // ElabResult::Inductive only), and even a mutual block would reject the
        // token occurrence nested inside ProdType (sibling-in-ProdType is a
        // nested-inductive occurrence) — so the cycle is broken by INLINING the
        // token's exact registered content into the app constructor: field2 =
        // the check pair's infer half (recursive, hoisted for strict
        // positivity), the tuple's middle component = the check pair's defeq
        // half, field4 = the check acceptance's guarded admissibility field.
        // This is strength-preserving in both directions: the old token field,
        // by the (then-)axioms kernel_check_decomposition and
        // kernel_check_types_admissible, implied exactly these components; and
        // the components rebuild the token via KernelCheckAccepts.mk. The
        // master inversion's app minor performs that rebuild, so
        // kernel_infer_app_decomposition and every downstream projection keep
        // BYTE-IDENTICAL statements (and values).
        //
        // WITNESS RETIREMENT (current): the app/lam/pi constructor fields now
        // conclude in the App/Lam/PiInferWitness packaged-existential inductives
        // instead of ProdType tuples of Skolem functions. AppInferWitness binds
        // the pi domain/codomain (dom, cod) and carries the WHNF-to-Pi, arg-defeq,
        // instantiated-codomain result, and check-step admissibility guard;
        // LamInferWitness binds the body type + domain level; PiInferWitness binds
        // the domain/codomain levels. This RETIRES the six KernelInferAppPiDomain /
        // KernelInferAppPiCodomain / KernelLamBodyType / KernelLamDomainLevel /
        // KernelPiDomainLevel / KernelPiCodomainLevel Skolems from the census (the
        // DefEqJoinable un-Skolemization pattern, per case). The app minor no
        // longer rebuilds the check token — kernel_infer_app_sound reconstructs
        // KernelCheckAccepts internally when eliminating AppInferWitness. Because
        // the witnesses only weaken the acceptance content (existential reducts vs
        // named Skolems) and KernelInferAccepts is hypothesis-position in the
        // *_sound bridges, no unsound inference becomes derivable — the safe
        // direction (the Step-2 argument).
        //
        // No bvar constructor: the real kernel unconditionally errors on BVar
        // (tc/infer.rs BVar arm returns Err(UnboundVariable); cert/infer_core.rs
        // mirrors), so bvar acceptance is uninhabited. New derivable facts audit:
        //  - `KernelInferAccepts st (bvar n) T -> Empty` becomes provable
        //    (kernel_infer_bvar_empty below). Composed with the unchanged producer
        //    kernel_check_decomposition this yields KernelCheckAccepts st (bvar n) T
        //    -> Empty — TRUE of the real kernel: check_type runs infer, which
        //    errors unconditionally on BVar.
        //  - Constructibility: the ctors make acceptance constructible from their
        //    premises (e.g. KernelInferAccepts st (sort l) (sort (succ l)) via
        //    Eq.refl). This over-approximates the real accept set only toward
        //    inputs the kernel WOULD accept absent resource aborts (heartbeat) —
        //    the standard soundness-safe direction, same as KernelWhnfAccepts
        //    (any spec whnf chain) in Step 1. Nothing false becomes derivable:
        //    every consumer of acceptance concludes typing facts that the ctor
        //    premises themselves already contain or imply.
        //  - Skolem pinning: via tc_infer_soundness + kernel_check_decomposition +
        //    sort inversion one can now derive Eq (sort (succ l))
        //    (KernelInferResult st (sort l)) — pins the KernelInferResult skolem
        //    at sorts, exactly the real kernel's deterministic result. Faithful.
        //  - Producer strength: the producers (kernel_check_decomposition, and the
        //    app ctor replacing kernel_infer_app_decomposition's first component)
        //    now assert, per accepted shape, exactly what the old consumer axioms
        //    already asserted about that shape — guards included where the old
        //    axioms had them. No producer gained strength.
        //
        // FVar/Let/Lit/Proj/MData arms exist in the real kernel but are outside
        // the core KExpr fragment (sort/bvar/app/lam/pi/const only) — the
        // inductive is scoped to KExpr.
        //
        // `st : KernelState` is a UNIFORM PARAMETER; (e, T) remain TRUE indices —
        // the five ctor conclusions differ in the e position, so e cannot be
        // uniform, and T (sitting after the non-uniform e) is structurally
        // unpromotable. Verified against the kernel-generated recursor type
        // (test_kernel_infer_accepts_recursor_is_index_shaped): the recursor is
        // the KernelWhnfAccepts.rec index-motive shape, NOT the param-promoted
        // AndType.rec shape of Step 2's single-ctor KernelDefEqAccepts.
        //
        // The declared signature KernelState -> KExpr -> KExpr -> Type is
        // unchanged, so every applied/hypothesis position across the soundness
        // chain still type-checks unmodified.
        self.add_inductive(
            r"inductive KernelInferAccepts (st : KernelState) : KExpr → KExpr → Type
| sort : forall (l : Level) (T : KExpr), Eq KExpr (KExpr.sort (Level.succ l)) T → KernelInferAccepts st (KExpr.sort l) T
| const : forall (n : Name) (us : ListType Level) (T : KExpr), (KernelStateEnvValid st → KernelStateLocalCtxWellFormed st → KernelInputAdmissible st (KExpr.const n us) → has_type (KExpr.const n us) T) → KernelInferAccepts st (KExpr.const n us) T
| app : forall (f : KExpr) (a : KExpr) (T : KExpr) (Rf : KExpr) (Ra : KExpr), KernelInferAccepts st f Rf → KernelInferAccepts st a Ra → AppInferWitness st Rf Ra a T → (KernelStateEnvValid st → KernelStateLocalCtxWellFormed st → KernelInputAdmissible st (KExpr.app f a) → KernelInputAdmissible st Rf) → KernelInferAccepts st (KExpr.app f a) T
| lam : forall (A : KExpr) (body : KExpr) (T : KExpr) (bt : KExpr), KernelInferAccepts st body bt → LamInferWitness A body bt T → KernelInferAccepts st (KExpr.lam A body) T
| pi : forall (A : KExpr) (B : KExpr) (T : KExpr), PiInferWitness A B T → KernelInferAccepts st (KExpr.pi A B) T",
            "Successful production-kernel type inference: KernelInferAccepts st e T means \
             infer_type (in the check-mode/infer_only=false path that check_type and \
             add_decl run) accepted e with type T. Faithful multi-ctor inductive: one \
             constructor per KExpr arm with a success path, each carrying EXACTLY the \
             content of the formerly-assumed per-case axiom for that arm, that axiom's \
             own guard structure included (the app arm carries the argument check step \
             as the check token's exact registered content — infer half, defeq half, \
             guarded admissibility — inlined to break the check/infer mutual-recursion \
             cycle; interderivable with the token via KernelCheckAccepts.mk and its \
             recursor, Step 4). No bvar constructor: the real kernel \
             unconditionally errors on BVar (tc/infer.rs BVar arm, cert/infer_core.rs), \
             so bvar acceptance is uninhabited.",
        )?;

        // =========================================================
        // AppInferDecomp: app-case inversion existential (un-Skolemization)
        // =========================================================
        //
        // The app inversion payload. Since KernelInferAccepts.app now binds the
        // inferred subtypes Rf/Ra EXISTENTIALLY (formerly KernelInferResult st f /
        // st a), the master-inversion app payload can no longer NAME them — it must
        // existentially re-bind them. This single-constructor witness inductive is
        // the clean-verify Sigma/Exists-free idiom (the DefEqJoinable pattern): its
        // mk binds Rf/Ra INTERNALLY and packages exactly the app constructor's four
        // fields (fun-infer at Rf, arg-infer at Ra, the AppInferWitness at Rf/Ra,
        // and the guarded fun-type admissibility at Rf). kernel_infer_app_sound
        // eliminates it via AppInferDecomp.rec, recovering Rf/Ra as bound variables
        // (no determinism, no Skolem). Registered AFTER KernelInferAccepts and
        // AppInferWitness (its fields reference both); it is the InferInversionAt
        // app arm and the result of kernel_infer_app_decomposition.
        self.add_inductive(
            r"inductive AppInferDecomp : KernelState → KExpr → KExpr → KExpr → Type
| mk : forall (st : KernelState) (f : KExpr) (a : KExpr) (T : KExpr) (Rf : KExpr) (Ra : KExpr), KernelInferAccepts st f Rf → KernelInferAccepts st a Ra → AppInferWitness st Rf Ra a T → (KernelStateEnvValid st → KernelStateLocalCtxWellFormed st → KernelInputAdmissible st (KExpr.app f a) → KernelInputAdmissible st Rf) → AppInferDecomp st f a T",
            "App-case inference decomposition existential: AppInferDecomp st f a T packages the app \
             branch's decomposition with the inferred subtypes Rf (of f) and Ra (of a) bound \
             INTERNALLY as existential constructor arguments (the un-Skolemization retiring \
             KernelInferResult). The single mk constructor carries: the recursive fun-infer \
             acceptance at Rf, the recursive arg-infer acceptance at Ra, the AppInferWitness at \
             (Rf, Ra), and the guarded fun-type admissibility at Rf. Recovered from a successful \
             app inference by kernel_infer_app_decomposition (via the master inversion), and \
             eliminated to the skolem-free has_type by kernel_infer_app_sound.",
        )?;

        // =========================================================
        // LamInferDecomp: lam-case inversion existential (body routed through infer)
        // =========================================================
        //
        // The lam analogue of AppInferDecomp (commit 0067f1e5), strictly simpler:
        // ONE recursive body-infer premise, no whnf/defeq witness. Since
        // KernelInferAccepts.lam now carries a RECURSIVE KernelInferAccepts st body
        // bt premise (the lam body's TYPE routed through inference, mirroring the
        // app arm's fun/arg premises) with bt bound EXISTENTIALLY, the master
        // inversion's lam payload existentially re-binds bt. mk packages exactly the
        // lam constructor's two fields: the recursive body-infer acceptance at bt and
        // the LamInferWitness at (A, body, bt). kernel_infer_lam_sound eliminates it
        // via LamInferDecomp.rec, recovering bt as a bound variable. Registered AFTER
        // KernelInferAccepts and LamInferWitness (its fields reference both); it is the
        // InferInversionAt lam arm and the result of kernel_infer_lam_decomposition.
        //
        // STAGE-1 NOTE (build-preserving): the recursive body-infer premise is CARRIED
        // but not yet consumed — kernel_infer_lam_sound still recovers the body typing
        // from LamInferWitness's retained `Typing body bt` field (the pre-existing
        // FVar-model-gap jump), because routing it through infer-soundness needs the
        // lam body's binder-crossing admissibility (is_closed_at body 1, not 0), which
        // is a Stage-2 dependency on infer_preserves_closed. The premise restructures
        // the RELATION now (enabling the Stage-2 recursion) while keeping the soundness
        // conclusion byte-identical; infer_sound_at_lam is unchanged.
        self.add_inductive(
            r"inductive LamInferDecomp : KernelState → KExpr → KExpr → KExpr → Type
| mk : forall (st : KernelState) (A : KExpr) (body : KExpr) (T : KExpr) (bt : KExpr), KernelInferAccepts st body bt → LamInferWitness A body bt T → LamInferDecomp st A body T",
            "Lam-case inference decomposition existential: LamInferDecomp st A body T packages the lam \
             branch's decomposition with the inferred body type bt bound INTERNALLY as an existential \
             constructor argument. The single mk constructor carries the recursive body-infer \
             acceptance at bt and the LamInferWitness at (A, body, bt). Mirrors AppInferDecomp (one \
             recursive body premise, no whnf/defeq witness — strictly simpler). Recovered from a \
             successful lam inference by kernel_infer_lam_decomposition (via the master inversion), \
             and eliminated to the skolem-free has_type by kernel_infer_lam_sound. Part of #461.",
        )?;

        // =========================================================
        // The faithful KernelCheckAccepts inductive (Step 4)
        // =========================================================
        //
        // KernelCheckAccepts was previously an opaque HelperAxiom of type
        // `KernelState -> KExpr -> KExpr -> Type` (implementation_soundness.rs).
        // It is now a FAITHFUL single-constructor inductive mirroring the
        // production kernel's check_type success contract:
        //
        //   let inferred = infer_type(e)?;            // infer half
        //   if !is_def_eq(&inferred, expected) { Err } // defeq half
        //
        // The mk constructor carries EXACTLY the joint content the opaque token
        // plus its two (formerly-assumed) eliminating axioms asserted of every
        // acceptance — each field preserving ITS OWN old axiom's guard
        // structure (the Step-2/3 per-axiom exact-strength rule):
        //
        //  - field1 (UNGUARDED, = kernel_check_decomposition's conclusion
        //    verbatim): the ProdType pair of the infer acceptance at the
        //    KernelInferResult skolem and the defeq acceptance between that
        //    inferred type and the expected T. The old axiom had no guards, so
        //    the field has none — an added guard would WEAKEN the assumed
        //    decomposition content.
        //  - field2 (GUARDED, = kernel_check_types_admissible with its token
        //    premise discharged, its guards verbatim): state validity + ctx
        //    well-formedness + input admissibility of e imply binary input
        //    admissibility of (KernelInferResult st e, T).
        //
        // FOLD-BOTH DECISION (the Step-2 producer audit rule: a ctor is the
        // conjunction of everything producers must supply; fold a field iff
        // every producer's old opaque-token assertion already implied it).
        // Producer inventory for KernelCheckAccepts (conclusion position):
        //   (1) tc_infer_soundness (type_checker_spec.rs, HelperAxiom, stays);
        //   (2) the app arm of KernelInferAccepts (formerly the token as a
        //       constructor field; the token is rebuilt from the inlined
        //       fields by the master inversion below).
        // Under the OLD regime both eliminating axioms were universally
        // quantified over ALL acceptances, so both producers' old assertions
        // implied BOTH fields — folding both is exact-strength for every
        // producer. Folding ONLY the decomposition field while RETAINING
        // kernel_check_types_admissible as an axiom would be a silent
        // WIDENING of the retained axiom: mk would make the token freely
        // constructible from the bare pair, and the retained axiom would then
        // assert closedness of ANY defeq-accepted T (the real kernel's
        // is_def_eq can accept an open T whose whnf is closed — a
        // countermodel shape the old system could not reach because the token
        // was not constructible). Folding it as a guarded mk field keeps that
        // consequence underivable, exactly as before.
        //
        // Both old axioms flip to DerivedProved KernelCheckAccepts.rec
        // projections in implementation_soundness_check_decomposition.rs.
        // tc_infer_soundness remains an axiom: deriving it would need the
        // pair AT KernelInferResult st e from an acceptance at an arbitrary
        // (defeq-equal) T — the skolem is opaque, so neither the infer half
        // nor the defeq half is constructible from KernelInferAccepts st e T.
        //
        // Positivity: KernelCheckAccepts does not occur in either field (the
        // nested occurrences are KernelInferAccepts / KernelDefEqAccepts —
        // previously-registered constants, not the family being defined), so
        // the single ProdType field needs no hoisting. Because the mk
        // conclusion is uniform in (e, T), the elaborator PROMOTES st/e/T to
        // inductive parameters — the generated recursor is the param-fixed
        // AndType.rec shape (motive over the major premise only, one minor
        // over the two fields), the Step-2 KernelDefEqAccepts.rec shape, NOT
        // the index-motive shape of KernelInferAccepts.rec. Verified against
        // the kernel-generated recursor type
        // (test_kernel_check_accepts_recursor_is_param_promoted). The declared
        // signature KernelState -> KExpr -> KExpr -> Type is unchanged, so
        // every applied/hypothesis position across the soundness chain still
        // type-checks unmodified.
        self.add_inductive(
            r"inductive KernelCheckAccepts (st : KernelState) : KExpr → KExpr → Type
| mk : forall (e : KExpr) (T : KExpr) (R : KExpr), ProdType (KernelInferAccepts st e R) (KernelDefEqAccepts st R T) → (KernelStateEnvValid st → KernelStateLocalCtxWellFormed st → KernelInputAdmissible st e → KernelBinaryInputAdmissible st R T) → KernelCheckAccepts st e T",
            "Successful production-kernel type checking: KernelCheckAccepts st e T means \
             check_type accepted e against T. Faithful single-constructor inductive in \
             EXISTENTIAL decomposition form: the mk constructor binds the inferred type \
             R INTERNALLY (the un-Skolemization retiring KernelInferResult st e — R is \
             now an existential constructor argument shared BY BINDING between the two \
             fields). The first field is the UNGUARDED ProdType pair of the infer \
             acceptance at R and the defeq acceptance between R and T (exactly the \
             formerly-assumed kernel_check_decomposition, which was unguarded); its \
             second field is the GUARDED implication from state validity, local-context \
             well-formedness, and input admissibility of e to binary input admissibility \
             of the inferred/expected pair (R, T) (exactly the formerly-assumed \
             kernel_check_types_admissible, guards included). Directly reflects the \
             production implementation: let inferred = infer_type(e)?; \
             is_def_eq(&inferred, T)?. Part of #461, Step 4.",
        )?;

        // =========================================================
        // CheckDecomp: check-case decomposition existential
        // =========================================================
        //
        // The existential form of the (retired) kernel_check_decomposition: from a
        // successful check_type, there EXISTS a shared inferred type R with an infer
        // acceptance at R and a defeq acceptance between R and T. Since KernelInferResult
        // is retired, this shared R can only be exposed as a bound existential — the
        // clean-verify Sigma/Exists-free idiom. tc_check_completeness eliminates
        // KernelCheckAccepts.rec and repackages the (R, ProdType-pair) into CheckDecomp.mk.
        self.add_inductive(
            r"inductive CheckDecomp : KernelState → KExpr → KExpr → Type
| mk : forall (st : KernelState) (e : KExpr) (T : KExpr) (R : KExpr), ProdType (KernelInferAccepts st e R) (KernelDefEqAccepts st R T) → CheckDecomp st e T",
            "Check-case decomposition existential: CheckDecomp st e T witnesses that a successful \
             check_type of e against T decomposes into a shared inferred type R (bound INTERNALLY \
             as an existential constructor argument — the un-Skolemization retiring \
             KernelInferResult st e) with a ProdType pair of the infer acceptance at R and the \
             defeq acceptance between R and T. The existential form of the former \
             kernel_check_decomposition; produced by tc_check_completeness via KernelCheckAccepts.rec.",
        )?;

        // =========================================================
        // KExprEqT: Type-valued KExpr equality witness
        // =========================================================
        //
        // The spec's Eq is Prop-valued (inductive Eq (α : Sort u) : α → α →
        // Prop), but the InferInversionAt payload family below must live
        // uniformly in Type (its app/lam/pi/const/bvar arms are ProdType /
        // implication / Empty payloads, all : Type, and a KExpr.rec motive
        // returns ONE sort for every arm — no per-arm universes). So the sort
        // arm's exact-result equation is carried by this Type-valued witness
        // instead. It is INTERDERIVABLE with Eq KExpr in both directions with
        // zero axioms (Eq.substType builds it from an Eq proof; KExprEqT.rec +
        // Eq.refl recovers the Eq proof), so no strength is added or lost —
        // the flipped kernel_infer_sort_result still concludes the byte-
        // identical Prop equation. Kernel-checked inductive: NOT an axiom.
        self.add_inductive(
            r"inductive KExprEqT (a : KExpr) : KExpr → Type
| refl : KExprEqT a a",
            "Type-valued KExpr equality witness: KExprEqT a b is inhabited exactly \
             when a = b (single refl constructor). Universe adapter for the \
             InferInversionAt payload family, whose KExpr.rec motive must return \
             Type in every arm while the spec's Eq is Prop-valued. Interderivable \
             with Eq KExpr in both directions with zero axioms.",
        )?;

        // =========================================================
        // InferInversionAt: semireducible index-family motive
        // =========================================================
        //
        // Per-shape inversion payload: InferInversionAt st x T computes (by
        // KExpr.rec on x) the exact content the corresponding KernelInferAccepts
        // constructor carries at (x, T) — and Empty at bvar, which has no
        // constructor. Registered via add_definition_reducible (MUST be the
        // reducible path: plain add_definition registers non-Prop valued defs as
        // Declaration::Opaque, which would block the iota unfolding the master
        // inversion rides on — the not_lt_zero_goal precedent). With this named
        // semireducible family as the recursor motive, index unification in the
        // inversion happens by REDUCTION (unfold + KExpr.rec iota at the literal
        // constructor pattern) instead of injectivity/discriminator plumbing.
        //
        // KExpr.rec minor order: sort, bvar, app, lam, pi, const, let_ (the
        // KEXPR_NOT_BVAR_INLINE order, let_ appended last). The app payload pairs the old
        // kernel_infer_app_decomposition 4-tuple with the old
        // kernel_infer_app_fun_type_admissible guarded implication, so both old
        // app axioms project out byte-identically.
        self.add_definition_reducible(SpecDefinition {
            name: "InferInversionAt".to_string(),
            type_src: "KernelState -> KExpr -> KExpr -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (x : KExpr) (T : KExpr) => ",
                    "KExpr.rec (fun (_ : KExpr) => Type) ",
                    "(fun (l : Level) => KExprEqT (KExpr.sort (Level.succ l)) T) ",
                    "(fun (_ : Nat) => Empty) ",
                    "(fun (f : KExpr) (a : KExpr) (_ : Type) (_ : Type) => ",
                    "AppInferDecomp st f a T) ",
                    "(fun (A : KExpr) (body : KExpr) (_ : Type) (_ : Type) => ",
                    "LamInferDecomp st A body T) ",
                    "(fun (A : KExpr) (B : KExpr) (_ : Type) (_ : Type) => ",
                    "PiInferWitness A B T) ",
                    "(fun (n : Name) (us : ListType Level) => ",
                    "KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                    "KernelInputAdmissible st (KExpr.const n us) -> ",
                    "has_type (KExpr.const n us) T) ",
                    // let_ minor: like bvar, KernelInferAccepts has NO let_
                    // constructor (Let is outside the core KExpr fragment the
                    // infer model covers), so the inversion payload at a let is
                    // Empty. Three recursive fields (ty, val, body) + three IHs.
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => ",
                    "Empty) ",
                    // proj/lit: outside the core KExpr fragment the infer model
                    // covers (like bvar/let_), so the inversion payload is Empty.
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) ",
                    "(fun (_ : Nat) => Empty) ",
                    "x"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Semireducible per-shape inversion payload family for KernelInferAccepts: ",
                "InferInversionAt st x T reduces (KExpr.rec on x) to exactly the content ",
                "the matching constructor carries at (x, T) — the old per-case axiom's ",
                "conclusion, guard structure included — and to Empty at bvar/let_ (no ",
                "matching KernelInferAccepts constructor). Motive of kernel_infer_inversion; index unification by ",
                "iota-reduction, no injectivity lemmas. Part of #461, Step 3."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "KExprEqT".to_string(),
                "KernelInferAccepts".to_string(),
                "AppInferDecomp".to_string(),
                "AppInferWitness".to_string(),
                "LamInferDecomp".to_string(),
                "LamInferWitness".to_string(),
                "PiInferWitness".to_string(),
                "Empty".to_string(),
            ])),
            // Honest residual closure: EMPTY. The KernelInferResult un-Skolemization
            // retired the last infer-band skolem — the inferred subtypes Rf/Ra are
            // bound internally by AppInferDecomp (the app payload), the pi
            // domain/codomain / lam-body-type / levels by the App/Lam/PiInferWitness
            // packaged existentials, all kernel-generated inductives. Tracked in
            // data/clean_verify_derivedproved_debt.json (the KernelInferResult debt
            // entry drains).
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // kernel_infer_inversion: the single master inversion
        // =========================================================
        //
        // ONE eliminator via KernelInferAccepts.rec with the semireducible
        // InferInversionAt motive. Every minor's expected type
        // `InferInversionAt st <literal ctor pattern> T'` iota-reduces through
        // the semireducible KExpr.rec to the payload, so four of the five minors
        // are literally the identity on the constructor field; only the app
        // minor does any work: it REBUILDS the check token
        // KernelCheckAccepts st a (KernelInferAppPiDomain st f a) from the
        // inlined check-content fields (KernelCheckAccepts.mk over the
        // argument-infer field, the tuple's defeq component, and the guarded
        // admissibility field) and repackages everything with ProdType.mk so
        // the old 4-tuple payload projects out byte-identically (Step 4).
        //
        // Recursor shape (kernel-generated, verified by the diagnostic and
        // pinned in test_kernel_infer_accepts_recursor_is_index_shaped):
        //   KernelInferAccepts.rec st
        //     (motive : forall (x y : KExpr), KernelInferAccepts st x y -> Sort u)
        //     m_sort m_const m_app m_lam m_pi e T h
        // Minor order = declaration order (sort, const, app, lam, pi); the app
        // minor binds (f a T' hf ha htail hchkadm hguard) and receives the IHs
        // for its TWO recursive fields LAST (after all fields), in field order,
        // typed motive f (KernelInferResult st f) hf and
        // motive a (KernelInferResult st a) ha.
        self.add_definition(SpecDefinition {
            name: "kernel_infer_inversion".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (e : KExpr) (T : KExpr), ",
                "KernelInferAccepts st e T -> InferInversionAt st e T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (e : KExpr) (T : KExpr) ",
                    "(h : KernelInferAccepts st e T) => ",
                    "KernelInferAccepts.rec st ",
                    "(fun (x : KExpr) (y : KExpr) (_h : KernelInferAccepts st x y) => ",
                    "InferInversionAt st x y) ",
                    // sort minor: transport the Prop-valued exact-result field
                    // into the Type-valued KExprEqT payload (universe adapter)
                    "(fun (l : Level) (T2 : KExpr) ",
                    "(hfield : Eq KExpr (KExpr.sort (Level.succ l)) T2) => ",
                    "Eq.substType KExpr ",
                    "(fun (X : KExpr) => KExprEqT (KExpr.sort (Level.succ l)) X) ",
                    "(KExpr.sort (Level.succ l)) T2 hfield ",
                    "(KExprEqT.refl (KExpr.sort (Level.succ l)))) ",
                    // const minor: identity on the guarded has_type implication
                    "(fun (n : Name) (us : ListType Level) (T2 : KExpr) ",
                    "(hfield : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                    "KernelInputAdmissible st (KExpr.const n us) -> ",
                    "has_type (KExpr.const n us) T2) => hfield) ",
                    // app minor: repackage the four constructor fields
                    // (fun-infer, arg-infer, AppInferWitness, guarded fun-type
                    // admissibility) as the 4-part ProdType InferInversionAt app
                    // payload. The KernelCheckAccepts token is NO LONGER rebuilt
                    // here — kernel_infer_app_sound reconstructs it internally from
                    // the arg-infer field and the witness's def-eq/admissibility.
                    "(fun (f : KExpr) (a : KExpr) (T2 : KExpr) (Rf : KExpr) (Ra : KExpr) ",
                    "(hf : KernelInferAccepts st f Rf) ",
                    "(ha : KernelInferAccepts st a Ra) ",
                    "(hwit : AppInferWitness st Rf Ra a T2) ",
                    "(hguard : KernelStateEnvValid st -> KernelStateLocalCtxWellFormed st -> ",
                    "KernelInputAdmissible st (KExpr.app f a) -> ",
                    "KernelInputAdmissible st Rf) ",
                    "(_ihf : InferInversionAt st f Rf) ",
                    "(_iha : InferInversionAt st a Ra) => ",
                    "AppInferDecomp.mk st f a T2 Rf Ra hf ha hwit hguard) ",
                    // lam minor: repackage the recursive body-infer field + the
                    // LamInferWitness into the LamInferDecomp existential (binding
                    // the inferred body type bt), mirroring the app minor. The IH
                    // for the recursive body-infer field comes LAST.
                    "(fun (A : KExpr) (body : KExpr) (T2 : KExpr) (bt : KExpr) ",
                    "(hbody : KernelInferAccepts st body bt) ",
                    "(hwit : LamInferWitness A body bt T2) ",
                    "(_ihbody : InferInversionAt st body bt) => ",
                    "LamInferDecomp.mk st A body T2 bt hbody hwit) ",
                    // pi minor: identity on PiInferWitness
                    "(fun (A : KExpr) (B : KExpr) (T2 : KExpr) ",
                    "(hfield : PiInferWitness A B T2) => hfield) ",
                    "e T h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Master inversion for the faithful KernelInferAccepts inductive: from an ",
                "acceptance witness, recover exactly the content its constructor carries — ",
                "the formerly-assumed per-case axiom for that shape, guard structure ",
                "included. Proved by KernelInferAccepts.rec over the semireducible ",
                "InferInversionAt motive; each minor's goal iota-reduces to the payload, so ",
                "index unification needs no injectivity or discriminator plumbing. All six ",
                "flipped per-case infer lemmas project from this single eliminator. ",
                "Part of #461, Step 3."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInferAccepts".to_string(),
                "KernelInferAccepts.rec".to_string(),
                "AppInferDecomp".to_string(),
                "AppInferDecomp.mk".to_string(),
                "AppInferWitness".to_string(),
                "LamInferDecomp".to_string(),
                "LamInferDecomp.mk".to_string(),
                "LamInferWitness".to_string(),
                "PiInferWitness".to_string(),
                "InferInversionAt".to_string(),
                "KExprEqT".to_string(),
                "KExprEqT.refl".to_string(),
                "Eq.substType".to_string(),
            ])),
            // Same honest residual as InferInversionAt: EMPTY. The KernelInferResult
            // un-Skolemization retired the last skolem; the app minor now builds the
            // AppInferDecomp existential (binding Rf/Ra) and the reduct/level Skolems
            // are inside the App/Lam/PiInferWitness inductives (all kernel-generated).
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // kernel_infer_bvar_empty: bvar acceptance is uninhabited
        // =========================================================
        //
        // Free corollary of the missing bvar constructor: InferInversionAt at a
        // bvar reduces to Empty. TRUE of the real kernel (infer_type errors
        // unconditionally on BVar), and composable with the unchanged producer
        // kernel_check_decomposition into KernelCheckAccepts st (bvar n) T ->
        // Empty — also true (check_type runs infer first). This does NOT rewire
        // infer_sound_at_bvar: its admissibility-based discharge stays.
        self.add_definition(SpecDefinition {
            name: "kernel_infer_bvar_empty".to_string(),
            type_src: concat!(
                "forall (st : KernelState) (n : Nat) (T : KExpr), ",
                "KernelInferAccepts st (KExpr.bvar n) T -> Empty"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (st : KernelState) (n : Nat) (T : KExpr) ",
                    "(h : KernelInferAccepts st (KExpr.bvar n) T) => ",
                    "kernel_infer_inversion st (KExpr.bvar n) T h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The production kernel never accepts a bound variable: infer_type errors ",
                "unconditionally on BVar, so KernelInferAccepts st (bvar n) T is ",
                "uninhabited. Proved by the master inversion — InferInversionAt at a bvar ",
                "iota-reduces to Empty (the inductive has no bvar constructor). ",
                "Part of #461, Step 3."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kernel_infer_inversion".to_string(),
                "InferInversionAt".to_string(),
                "KernelInferAccepts".to_string(),
                "Empty".to_string(),
            ])),
            // Inherits the master inversion's residual closure (reached through
            // kernel_infer_inversion's type/value): EMPTY after the KernelInferResult
            // un-Skolemization.
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_infer_accepts_tests.rs"]
mod implementation_soundness_infer_accepts_tests;
