// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R7 of the candidate-model construction ladder — the TEXTBOOK rung: the
//! judgment `SynTyT : ListType KExpr -> KExpr -> KExpr -> Type` whose `lam`
//! rule is the ordinary one, `SimpleTy A -> SynTyT (cons A G) b B -> SynTyT G
//! (lam A b) (pi A B)`, with NO development-closure side condition; its Tait
//! fundamental theorem; the still-UNCONDITIONAL capstones `synTyT_sn_subst` /
//! `synTyT_sn` / `synTyT_sn_closed`; and the bridge `synTy_to_synTyT` that
//! subsumes R6.
//!
//! ## What R6 left open, and how R7 closes it
//!
//! R6 landed `synTy_sn : SynTy G e T -> whnf_acc e` with no carried premise,
//! but paid for it in the RULE: `SynTy.lam` carries the hoisted syntactic
//! premise
//!
//! ```text
//! forall (s : Nat -> KExpr) (b2 : KExpr),
//!   betaStar (psubst (up s) b) b2 -> SynTy (ListType.cons KExpr A G) b2 B
//! ```
//!
//! R6's module docs state the obstruction exactly, and it was a STAGE-POSITION
//! obstruction, not a mathematical one: R5's `candInterp_lam` (R1's Tait engine
//! `candExpHF_beta`) demands the development family at the SUBSTITUTED body,
//! deriving it needs the substitution transport `beta_reduces b' b2 ->
//! beta_reduces (instantiate b' a) (instantiate b2 a)`, and the only spec-side
//! transport — R2's `betaRed_inst_transport` / `betaStar_inst_transport` —
//! CARRIES `RecEnvClosed (red_rec the_red_env)` (its iota arm goes through
//! `iota_subst_commutes`). The discharge of that premise,
//! `the_red_env_rec_closed_via_checker_b2`, registers in
//! `add_the_red_env_faithful_discharge` — **STAGES index 95**, nine stages
//! AFTER the ladder's index 86.
//!
//! R7 is registered at index 96, immediately after that discharge, and
//! therefore may simply APPLY it. Route (a) of the brief, taken as written:
//!
//! - `betaRed_inst_transport_env` and `betaStar_inst_transport_env` are R2's
//!   transports with the `RecEnvClosed` argument SUPPLIED, so they carry no
//!   premise at all;
//! - `candInterp_betaStar_closed` lifts R5's `isCandHF_cr2` along a
//!   `betaStar` chain;
//! - the two together turn R6's hoisted premise into the THEOREM
//!   `r7_dev_family_derived`, and the `lam` arm of `synTyT_fundamental`
//!   builds `candInterp_lam`'s development family from the ORDINARY
//!   single-body induction hypothesis.
//!
//! **The `RecEnvLiftClosed` half was not needed.** R6 named it as the blocker
//! for the second route (renaming/lifting `SubstOK` into the extended
//! context). R7 never lifts: the body's SN premise comes from the IH at
//! `scons (bvar 0) s` — a closing substitution built by R6's own
//! `substOK_extend` from `candInterp_var` — reshaped by
//! `psubst_scons_instantiate` and unwound by `whnfAcc_of_instantiate_bvar0`,
//! which is the landed idiom of `fundamental_pi`
//! (`dependent_sn_richmodel.rs:3888`). So only ONE of the two discharges is
//! consumed, and `RecEnvLiftClosed` stays untouched.
//!
//! ## Premise freedom is unchanged, and is guarded the same way
//!
//! ```text
//! synTyT_fundamental : SynTyT G e T -> forall s, SubstOK s G -> candInterp T (psubst s e)
//! synTyT_sn_subst    : SynTyT G e T -> forall s, SubstOK s G -> whnf_acc (psubst s e)
//! synTyT_sn          : SynTyT G e T -> whnf_acc e
//! synTyT_sn_closed   : SynTyT nil e T -> whnf_acc e
//! ```
//!
//! carry NO premise of any kind — no `CandModel`, no `RecEnvClosed`, no
//! `RecEnvLiftClosed`, no `DefEnvClosed`, no `EnvAcyclic`. The shape guard
//! refuses any of those names in the STATEMENT of the capstone chain, of
//! `SynTyT` itself and of the two transport unlocks. It deliberately does NOT
//! refuse them in proof VALUES: consuming
//! `the_red_env_rec_closed_via_checker_b2` inside a proof is the whole point of
//! the rung, and a separate guard REQUIRES that consumption so the unlock
//! cannot silently regress to a carried hypothesis.
//!
//! The discharge is honest: `the_red_env_rec_closed_via_checker_b2` is
//! `rec_env_closed_of_b2 (red_rec the_red_env) (Eq.refl Bool Bool.true)` —
//! `DerivedProved`, zero `axiom_deps`, the kernel whnf-evaluating the depth-aware
//! Bool fold `rec_env_closed_b2` over every real rule RHS of the reflected
//! kernel core env down to `Bool.true`. Nothing is assumed; a computation is
//! run.
//!
//! ## The bridge, and its direction
//!
//! `synTy_to_synTyT : SynTy G e T -> SynTyT G e T`. R6's judgment is SUBSUMED,
//! not orphaned: its `lam` rule's development premise, instantiated at
//! `s := idsubst` and the reflexive development, hands over exactly the
//! textbook rule's single sub-derivation once `psubst (up idsubst) b` is
//! collapsed to `b` (`psubst_up_idsubst`, from the landed `psubst_pointwise` +
//! `up_idsubst` + `psubst_id`). `synTy_sn_via_synTyT` re-derives R6's own
//! capstone through R7's, so R6's tower is a corollary of this one.
//!
//! **The converse is NOT claimed and is not provable here.** `SynTyT G e T ->
//! SynTy G e T` would require typing every beta-development of every
//! substitution instance of the body — i.e. SUBJECT REDUCTION for `SynTyT`
//! plus substitution stability, neither of which is landed. R7 states the
//! direction it proves and nothing more; `SynTyT` is a strictly WIDER judgment
//! (see `synTyT_lam_redex_witness`), which is why this is the useful
//! direction.
//!
//! ## The witness that the textbook rule genuinely buys something
//!
//! `synTyT_lam_redex_witness` types `lam (sort 0) (app (lam (sort 0) (bvar 0))
//! (bvar 0))` — a lambda whose BODY IS A LIVE BETA REDEX — in the empty
//! context, by one `SynTyT.lam` over one `SynTyT.app`. Under R6's rule the same
//! term demands `SynTy (cons (sort 0) nil) b2 (sort 0)` for EVERY `b2` with
//! `betaStar (psubst (up s) (app (lam (sort 0) (bvar 0)) (bvar 0))) b2` at
//! EVERY `s` — an inversion over the developments of a body that actually
//! fires, with no `betaStar_bvar_collapse` to close it (that lemma is why
//! R6's `synTy_id` was provable at all: its body `bvar 0` takes no step).
//! `r7_redex_body_fires` pins that the body really does beta-step, and
//! `r7_textbook_admits_redex_body` pairs the derivation with it, so the
//! difference between the two rules is recorded as a fact rather than as
//! prose. `synTyT_sn_witness` then obtains `whnf_acc` of that term THROUGH the
//! capstone — SN of a redex UNDER A BINDER, which is a strictly larger claim
//! than R6's `synTy_sn_witness` (a bare redex).
//!
//! ## Honesty notes (read before quoting)
//!
//! - **Nothing here discharges `M : CandModel tenv`.** `synTyT_sn` is SN for
//!   `SynTyT`, NOT for `TypingCtx`, and must never be described as advancing
//!   `whnf_terminates_well_typed_dependent` (design §6.2). `SynTyT` remains
//!   strictly narrower than `TypingCtx`: no `const` rule, no `let_` rule, no
//!   `pi` formation rule, and `SimpleTy` domains only. What R7 removes is one
//!   of R6's TWO lam side conditions — the development closure. `SimpleTy A`
//!   stays, and it stays for the reason R6 recorded: R5's `candInterp` has a
//!   NON-DEPENDENT Pi clause, whose exactness needs a substitution-inert
//!   domain, and the dependent clause is PROVED non-portable
//!   (`r6_dependent_pi_self_reachable`).
//! - **The judgment is not total.** `synTyT_not_total`: `r5_omegaLam` — a
//!   strongly normalizing term — is not `SynTyT`-derivable at `pi (sort 0)
//!   (sort 0)` in ANY context, because the fundamental theorem would place it
//!   in the interpretation R5's `candInterp_pi_not_total` excludes. This is
//!   the `micro_has_type` total-predicate trap guard; no automated gate
//!   performs the discrimination.
//! - **Every predicate R7 introduces in hypothesis position is WITNESSED in
//!   this module.** `SynTyT` is assumed by `synTyT_fundamental`, the three
//!   capstones, `r7_dev_family_derived` and the bridge; it is CONCLUDED by
//!   `synTyT_id`, `synTyT_sort_witness`, `synTyT_app_witness` and
//!   `synTyT_lam_redex_witness`. Constructors do not count on the supply side
//!   (`premise_witness.rs`), which is why those four are registered
//!   definitions and why the ladder guard
//!   `test_candmodel_ladder_premises_are_witnessed` names `SynTyT`.
//! - **Recursor conventions are taken from landed consumers, not guessed.**
//!   `SynTyT.app` has TWO recursive premises and `SynTyT.lam` one; the minors
//!   bind ALL FIELDS FIRST, THEN ALL IHs, in constructor order — the
//!   convention of `fundamental_general` (`dependent_sn_richmodel.rs:4052`)
//!   and of R6's own `synTy_fundamental`. Pinned by the shape guard.
//! - **No `fixedIndicesToParams` promotion.** The leading `(G : ListType
//!   KExpr)` is uniform across the four conclusions, but `SynTyT.lam`'s
//!   recursive premise concludes at `ListType.cons KExpr A G`, so the first
//!   index is not fixed and no promotion fires — the same reason `TypingCtx`
//!   and R6's `SynTy` keep their 3-ary index motives. Pinned by the shape
//!   guard.
//! - **Prop/Type discipline.** `Eq` is Prop; `candInterp T`, `SynTyT`,
//!   `SimpleTy`, `SubstOK`, `betaStar`, `beta_reduces` and `whnf_acc` are
//!   Type. `AndType (A : Type) (B : Type)` is `Type 0`-in and the kernel is
//!   NON-CUMULATIVE, so an `AndType` slot may hold neither an `Eq` nor a
//!   `Type 1` term — R6 paid a cycle for that lesson and the guard is carried
//!   forward here unchanged.
//!
//! ## Census
//!
//! ZERO new axioms: one genuine inductive via `add_inductive`, everything else
//! a value-bearing theorem via `add_definition` with kernel `add_decl`
//! checking. Census-neutral.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ==== R7 SOURCES BEGIN (pure string builders; every source in this region is ====
// ==== pre-validated through the stable-toolchain clean-parser harness).      ====

/// `bvar 0` — the canonical irreducible neutral.
const V0: &str = "(KExpr.bvar Nat.zero)";
/// `sort 0`, the fragment's base simple type.
const S0: &str = "(KExpr.sort Level.zero)";
/// The non-dependent function type `pi (sort 0) (sort 0)`.
const PI00: &str = "(KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))";
/// The fragment's identity function, annotated at the base type.
const IDLAM0: &str = "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))";
/// The one-entry context `[sort 0]`.
const CTX1: &str = "(@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr))";
/// The witness redex `app (lam (sort 0) (bvar 0)) (bvar 0)`.
const REDEX: &str =
    "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))";
/// `lam (sort 0) REDEX` — a lambda whose BODY IS A LIVE BETA REDEX. This is
/// the term the textbook rule admits in one step and the hoisted rule made
/// awkward.
const LAM_REDEX: &str = "(KExpr.lam (KExpr.sort Level.zero) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)))";
/// The empty context.
const NILCTX: &str = "(@ListType.nil KExpr)";

// ================================================================
// Group A — THE UNLOCK: R2's substitution transports with the RecEnvClosed
// premise DISCHARGED at the real reflected env, plus betaStar-closure of the
// interpretation.
// ================================================================

pub(super) const TY_BETARED_INST_TRANSPORT_ENV: &str = "forall (e : KExpr) (e2 : KExpr), beta_reduces e e2 -> forall (w : KExpr) (dd : Nat), beta_reduces (instantiate_at e w dd) (instantiate_at e2 w dd)";

pub(super) const VAL_BETARED_INST_TRANSPORT_ENV: &str = "fun (e : KExpr) (e2 : KExpr) (h : beta_reduces e e2) (w : KExpr) (dd : Nat) => betaRed_inst_transport e e2 h the_red_env_rec_closed_via_checker_b2 w dd";

pub(super) const TY_BETASTAR_INST_TRANSPORT_ENV: &str = "forall (b : KExpr) (b2 : KExpr), betaStar b b2 -> forall (a : KExpr), betaStar (instantiate b a) (instantiate b2 a)";

pub(super) const VAL_BETASTAR_INST_TRANSPORT_ENV: &str = "fun (b : KExpr) (b2 : KExpr) (hstar : betaStar b b2) (a : KExpr) => betaStar_inst_transport b b2 hstar the_red_env_rec_closed_via_checker_b2 a";

pub(super) const TY_CANDINTERP_BETASTAR_CLOSED: &str = "forall (T : KExpr) (e : KExpr) (e2 : KExpr), betaStar e e2 -> candInterp T e -> candInterp T e2";

pub(super) const VAL_CANDINTERP_BETASTAR_CLOSED: &str = "fun (T : KExpr) (e : KExpr) (e2 : KExpr) (hstar : betaStar e e2) => @betaStar.rec (fun (qx : KExpr) (qy : KExpr) (_ : betaStar qx qy) => candInterp T qx -> candInterp T qy) (fun (qe : KExpr) (qhx : candInterp T qe) => qhx) (fun (qe : KExpr) (qe2 : KExpr) (qe3 : KExpr) (qhb : beta_reduces qe qe2) (_qrest : betaStar qe2 qe3) (qih : candInterp T qe2 -> candInterp T qe3) (qhx : candInterp T qe) => qih (isCandHF_cr2 (candInterp T) (candInterp_isCandHF T) qe qe2 qhx (@whnf_step.beta qe qe2 qhb))) e e2 hstar";

// ================================================================
// Group B — the TEXTBOOK judgment.
// ================================================================

/// The textbook lam rule, spelled once so the inductive source, the recursor
/// minor and the shape guard cannot drift apart. Note what is NOT here: no
/// `betaStar`, no `psubst`, no quantification over substitutions.
const LAM_RULE_TEXTBOOK: &str = "| lam : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (b : KExpr), SimpleTy A -> SynTyT (@ListType.cons KExpr A G) b B -> SynTyT G (KExpr.lam A b) (KExpr.pi A B)";

pub(super) fn src_syn_ty_t() -> String {
    format!(
        "inductive SynTyT : ListType KExpr -> KExpr -> KExpr -> Type\n\
         | var : forall (G : ListType KExpr) (i : Nat) (T : KExpr), @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr T) -> SynTyT G (KExpr.bvar i) T\n\
         | sort : forall (G : ListType KExpr) (n : Level), SynTyT G (KExpr.sort n) (KExpr.sort (Level.succ n))\n\
         | app : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr), SynTyT G f (KExpr.pi A B) -> SynTyT G a A -> SynTyT G (KExpr.app f a) B\n\
         {LAM_RULE_TEXTBOOK}"
    )
}

// ================================================================
// Group C — the fundamental theorem and the capstones.
// ================================================================

pub(super) const TY_SYNTYT_FUNDAMENTAL: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyT G e T -> forall (s : Nat -> KExpr), SubstOK s G -> candInterp T (psubst s e)";

pub(super) fn val_syntyt_fundamental() -> String {
    let motive = "(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTyT qG qe qT) => forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp qT (psubst qs qe))";
    // var: the SubstOK lookup IS the goal (psubst qs (bvar qi) reduces to qs qi).
    let m_var = "(fun (qG : ListType KExpr) (qi : Nat) (qT : KExpr) (qhget : @Eq (OptionType KExpr) (ctx_lookup qG qi) (@OptionType.some KExpr qT)) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => qhs qi qT qhget)";
    // sort: red_sort at the interpretation, with the landed SN of sorts.
    let m_sort = "(fun (qG : ListType KExpr) (qn : Level) (qs : Nat -> KExpr) (_qhs : SubstOK qs qG) => candInterp_sort_mem (Level.succ qn) (KExpr.sort qn) (whnfAcc_sort qn))";
    // app: pi_elim at the interpretation on the two IHs.
    let m_app = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTyT qG qf (KExpr.pi qA qB)) (_qha : SynTyT qG qa qA) (qihf : forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp (KExpr.pi qA qB) (psubst qs qf)) (qiha : forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp qA (psubst qs qa)) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_app qA qB (psubst qs qf) (psubst qs qa) (qihf qs qhs) (qiha qs qhs))";
    // lam: the substantive case, and the one R6 could not state this way.
    let ih_ty = "forall (qs2 : Nat -> KExpr), SubstOK qs2 (@ListType.cons KExpr qA qG) -> candInterp qB (psubst qs2 qb)";
    // whnf_acc of the substituted annotation, through SimpleTy.
    let hty = "(@Eq.substType KExpr (fun (qw : KExpr) => whnf_acc qw) qA (psubst qs qA) (@Eq.symm KExpr (psubst qs qA) qA (simpleTy_psubst qA qhA qs)) (simpleTy_whnfAcc qA qhA))";
    // whnf_acc of the substituted BODY: the IH at the fresh variable, reshaped
    // by psubst_scons_instantiate and unwound by whnfAcc_of_instantiate_bvar0.
    // This is the landed fundamental_pi idiom, and it is what makes the
    // RecEnvLiftClosed route unnecessary.
    let hb = "(whnfAcc_of_instantiate_bvar0 (psubst (up qs) qb) (@Eq.substType KExpr (fun (qw : KExpr) => whnf_acc qw) (psubst (scons (KExpr.bvar Nat.zero) qs) qb) (instantiate (psubst (up qs) qb) (KExpr.bvar Nat.zero)) (psubst_scons_instantiate qb (KExpr.bvar Nat.zero) qs) (candInterp_cr1 qB (psubst (scons (KExpr.bvar Nat.zero) qs) qb) (qih (scons (KExpr.bvar Nat.zero) qs) (substOK_extend qs qG qA (KExpr.bvar Nat.zero) (candInterp_var qA Nat.zero) qhs)))))";
    // The Tait engine's development family, DERIVED (this is R6's hoisted
    // premise): the IH at scons a qs gives membership at the un-developed
    // body, psubst_scons_instantiate reshapes it to the instantiation, the
    // DISCHARGED transport carries the development through instantiate, and
    // betaStar-closure of the candidate lands it at b2.
    let hfam = "(fun (qb2 : KExpr) (qstar : betaStar (psubst (up qs) qb) qb2) (qa : KExpr) (qha : candInterp qA qa) => candInterp_betaStar_closed qB (instantiate (psubst (up qs) qb) qa) (instantiate qb2 qa) (betaStar_inst_transport_env (psubst (up qs) qb) qb2 qstar qa) (@Eq.substType KExpr (fun (qw : KExpr) => candInterp qB qw) (psubst (scons qa qs) qb) (instantiate (psubst (up qs) qb) qa) (psubst_scons_instantiate qb qa qs) (qih (scons qa qs) (substOK_extend qs qG qA qa qha qhs))))";
    let m_lam = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (qhA : SimpleTy qA) (_qhb : SynTyT (@ListType.cons KExpr qA qG) qb qB) (qih : {ih_ty}) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_lam qA qB (psubst qs qA) (psubst (up qs) qb) {hty} {hb} {hfam})"
    );
    format!(
        "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyT G e T) => @SynTyT.rec {motive} {m_var} {m_sort} {m_app} {m_lam} G e T h"
    )
}

pub(super) const TY_SYNTYT_SN_SUBST: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyT G e T -> forall (s : Nat -> KExpr), SubstOK s G -> whnf_acc (psubst s e)";

pub(super) const VAL_SYNTYT_SN_SUBST: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyT G e T) (s : Nat -> KExpr) (hs : SubstOK s G) => candInterp_cr1 T (psubst s e) (synTyT_fundamental G e T h s hs)";

pub(super) const TY_SYNTYT_SN: &str =
    "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyT G e T -> whnf_acc e";

pub(super) const VAL_SYNTYT_SN: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyT G e T) => @Eq.substType KExpr (fun (qw : KExpr) => whnf_acc qw) (psubst idsubst e) e (psubst_id e) (synTyT_sn_subst G e T h idsubst (substOK_idsubst G))";

pub(super) const TY_SYNTYT_SN_CLOSED: &str =
    "forall (e : KExpr) (T : KExpr), SynTyT (@ListType.nil KExpr) e T -> whnf_acc e";

pub(super) const VAL_SYNTYT_SN_CLOSED: &str = "fun (e : KExpr) (T : KExpr) (h : SynTyT (@ListType.nil KExpr) e T) => synTyT_sn (@ListType.nil KExpr) e T h";

pub(super) const TY_SYNTYT_FUNDAMENTAL_TYPESUBST: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTyT G e T -> SimpleTy T -> forall (s : Nat -> KExpr), SubstOK s G -> candInterp (psubst s T) (psubst s e)";

pub(super) const VAL_SYNTYT_FUNDAMENTAL_TYPESUBST: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTyT G e T) (hT : SimpleTy T) (s : Nat -> KExpr) (hs : SubstOK s G) => @Eq.substType KExpr (fun (qw : KExpr) => candInterp qw (psubst s e)) T (psubst s T) (@Eq.symm KExpr (psubst s T) T (simpleTy_psubst T hT s)) (synTyT_fundamental G e T h s hs)";

/// R6's HOISTED PREMISE, now a THEOREM: from the ordinary single-body typing
/// derivation, the whole development family the Tait engine demands.
pub(super) const TY_R7_DEV_FAMILY_DERIVED: &str = "forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (b : KExpr), SynTyT (@ListType.cons KExpr A G) b B -> forall (s : Nat -> KExpr), SubstOK s G -> forall (b2 : KExpr), betaStar (psubst (up s) b) b2 -> forall (a : KExpr), candInterp A a -> candInterp B (instantiate b2 a)";

pub(super) const VAL_R7_DEV_FAMILY_DERIVED: &str = "fun (G : ListType KExpr) (A : KExpr) (B : KExpr) (b : KExpr) (hb : SynTyT (@ListType.cons KExpr A G) b B) (s : Nat -> KExpr) (hs : SubstOK s G) (b2 : KExpr) (hstar : betaStar (psubst (up s) b) b2) (a : KExpr) (ha : candInterp A a) => candInterp_betaStar_closed B (instantiate (psubst (up s) b) a) (instantiate b2 a) (betaStar_inst_transport_env (psubst (up s) b) b2 hstar a) (@Eq.substType KExpr (fun (qw : KExpr) => candInterp B qw) (psubst (scons a s) b) (instantiate (psubst (up s) b) a) (psubst_scons_instantiate b a s) (synTyT_fundamental (@ListType.cons KExpr A G) b B hb (scons a s) (substOK_extend s G A a ha hs)))";

// ================================================================
// Group D — the bridge from R6.
// ================================================================

pub(super) const TY_PSUBST_UP_IDSUBST: &str =
    "forall (b : KExpr), @Eq KExpr (psubst (up idsubst) b) b";

pub(super) const VAL_PSUBST_UP_IDSUBST: &str = "fun (b : KExpr) => @Eq.trans KExpr (psubst (up idsubst) b) (psubst idsubst b) b (psubst_pointwise b (up idsubst) idsubst up_idsubst) (psubst_id b)";

pub(super) const TY_SYNTY_TO_SYNTYT: &str =
    "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTy G e T -> SynTyT G e T";

pub(super) fn val_synty_to_syntyt() -> String {
    let motive = "(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTy qG qe qT) => SynTyT qG qe qT)";
    let m_var = "(fun (qG : ListType KExpr) (qi : Nat) (qT : KExpr) (qhget : @Eq (OptionType KExpr) (ctx_lookup qG qi) (@OptionType.some KExpr qT)) => SynTyT.var qG qi qT qhget)";
    let m_sort = "(fun (qG : ListType KExpr) (qn : Level) => SynTyT.sort qG qn)";
    let m_app = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTy qG qf (KExpr.pi qA qB)) (_qha : SynTy qG qa qA) (qihf : SynTyT qG qf (KExpr.pi qA qB)) (qiha : SynTyT qG qa qA) => SynTyT.app qG qA qB qf qa qihf qiha)";
    let dev_ty = "forall (qs0 : Nat -> KExpr) (qb2 : KExpr), betaStar (psubst (up qs0) qb) qb2 -> SynTy (@ListType.cons KExpr qA qG) qb2 qB";
    let ih_ty = "forall (qs0 : Nat -> KExpr) (qb2 : KExpr), betaStar (psubst (up qs0) qb) qb2 -> SynTyT (@ListType.cons KExpr qA qG) qb2 qB";
    let body = "(@Eq.substType KExpr (fun (qw : KExpr) => SynTyT (@ListType.cons KExpr qA qG) qw qB) (psubst (up idsubst) qb) qb (psubst_up_idsubst qb) (qih idsubst (psubst (up idsubst) qb) (betaStar.refl (psubst (up idsubst) qb))))";
    let m_lam = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (qhA : SimpleTy qA) (_qhdev : {dev_ty}) (qih : {ih_ty}) => SynTyT.lam qG qA qB qb qhA {body})"
    );
    format!(
        "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTy G e T) => @SynTy.rec {motive} {m_var} {m_sort} {m_app} {m_lam} G e T h"
    )
}

pub(super) const TY_SYNTY_SN_VIA_SYNTYT: &str =
    "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTy G e T -> whnf_acc e";

pub(super) const VAL_SYNTY_SN_VIA_SYNTYT: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTy G e T) => synTyT_sn G e T (synTy_to_synTyT G e T h)";

// ================================================================
// Group E — witnesses and the non-degeneracy guard.
// ================================================================

pub(super) fn ty_syntyt_id() -> String {
    format!("forall (G : ListType KExpr), SynTyT G {IDLAM0} {PI00}")
}

pub(super) fn val_syntyt_id() -> String {
    format!(
        "fun (G : ListType KExpr) => SynTyT.lam G {S0} {S0} {V0} (SimpleTy.base Level.zero) (SynTyT.var (@ListType.cons KExpr {S0} G) Nat.zero {S0} (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {S0})))"
    )
}

pub(super) fn ty_syntyt_sort_witness() -> String {
    format!("SynTyT {NILCTX} {S0} (KExpr.sort (Level.succ Level.zero))")
}

pub(super) fn val_syntyt_sort_witness() -> String {
    format!("SynTyT.sort {NILCTX} Level.zero")
}

pub(super) fn ty_syntyt_app_witness() -> String {
    format!("SynTyT {CTX1} {REDEX} {S0}")
}

pub(super) fn val_syntyt_app_witness() -> String {
    format!(
        "SynTyT.app {CTX1} {S0} {S0} {IDLAM0} {V0} (synTyT_id {CTX1}) (SynTyT.var {CTX1} Nat.zero {S0} (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {S0})))"
    )
}

pub(super) fn ty_syntyt_lam_redex_witness() -> String {
    format!("SynTyT {NILCTX} {LAM_REDEX} {PI00}")
}

pub(super) fn val_syntyt_lam_redex_witness() -> String {
    format!("SynTyT.lam {NILCTX} {S0} {S0} {REDEX} (SimpleTy.base Level.zero) synTyT_app_witness")
}

pub(super) fn ty_r7_redex_body_fires() -> String {
    format!("beta_reduces {REDEX} (instantiate {V0} {V0})")
}

pub(super) fn val_r7_redex_body_fires() -> String {
    format!("beta_reduces.beta {S0} {V0} {V0}")
}

pub(super) fn ty_r7_textbook_admits_redex_body() -> String {
    let derivable = format!("(SynTyT {NILCTX} {LAM_REDEX} {PI00})");
    let fires = format!("(beta_reduces {REDEX} (instantiate {V0} {V0}))");
    format!("AndType {derivable} {fires}")
}

pub(super) fn val_r7_textbook_admits_redex_body() -> String {
    let derivable = format!("(SynTyT {NILCTX} {LAM_REDEX} {PI00})");
    let fires = format!("(beta_reduces {REDEX} (instantiate {V0} {V0}))");
    format!("@AndType.intro {derivable} {fires} synTyT_lam_redex_witness r7_redex_body_fires")
}

pub(super) fn ty_syntyt_sn_witness() -> String {
    format!("whnf_acc {LAM_REDEX}")
}

pub(super) fn val_syntyt_sn_witness() -> String {
    format!("synTyT_sn {NILCTX} {LAM_REDEX} {PI00} synTyT_lam_redex_witness")
}

pub(super) fn ty_syntyt_not_total() -> String {
    format!("forall (G : ListType KExpr), SynTyT G r5_omegaLam {PI00} -> Empty")
}

pub(super) fn val_syntyt_not_total() -> String {
    format!(
        "fun (G : ListType KExpr) (h : SynTyT G r5_omegaLam {PI00}) => candInterp_pi_not_total (@Eq.substType KExpr (fun (qw : KExpr) => candInterp {PI00} qw) (psubst idsubst r5_omegaLam) r5_omegaLam (psubst_id r5_omegaLam) (synTyT_fundamental G r5_omegaLam {PI00} h idsubst (substOK_idsubst G)))"
    )
}

// ==== R7 SOURCES END ====

/// Register one value-bearing theorem (R6's helper, verbatim).
fn add_thm(
    spec: &mut Specification,
    name: &str,
    ty: String,
    val: String,
    deps: &[&str],
    desc: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: ty,
        value_src: Some(val),
        is_axiom: false,
        description: desc.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: Some(
            deps.iter()
                .map(|d| (*d).to_string())
                .collect::<HashSet<_>>(),
        ),
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    /// Register the R7 transport unlock, the TEXTBOOK typing judgment
    /// `SynTyT`, its fundamental theorem, the unconditional SN capstones, the
    /// bridge subsuming R6's `SynTy`, and the discriminating witnesses.
    ///
    /// MUST be registered AFTER `add_the_red_env_faithful_discharge` — that is
    /// the whole point of the rung. It consumes
    /// `the_red_env_rec_closed_via_checker_b2 : RecEnvClosed (red_rec
    /// the_red_env)` to discharge the premise of R2's
    /// `betaRed_inst_transport` / `betaStar_inst_transport`, which is what
    /// turns R6's hoisted development-closure side condition into the theorem
    /// `r7_dev_family_derived` and lets `SynTyT.lam` be the textbook rule.
    ///
    /// Also requires `add_candmodel_construct_r0..r6` (`betaStar`,
    /// `isCandHF_cr2`, the whole `candInterp` layer, `SimpleTy` + its two
    /// lemmas, `SubstOK` + `substOK_idsubst`/`substOK_extend`, `SynTy`,
    /// `r5_omegaLam`, `candInterp_pi_not_total`),
    /// `add_dependent_sn_richmodel` (`ctx_lookup`, the psubst calculus,
    /// `psubst_pointwise`, `up_idsubst`, `psubst_id`,
    /// `psubst_scons_instantiate`, `whnfAcc_of_instantiate_bvar0`,
    /// `whnfAcc_sort`), `add_whnf_reduction` (`beta_reduces`, `whnf_step`,
    /// `whnf_acc`) and `add_expr_model` (`KExpr`, `Level`, `instantiate`).
    pub(super) fn add_candmodel_construct_r7(&mut self) -> Result<(), SpecError> {
        // --- Group A: the unlock ---
        add_thm(
            self,
            "betaRed_inst_transport_env",
            TY_BETARED_INST_TRANSPORT_ENV.to_string(),
            VAL_BETARED_INST_TRANSPORT_ENV.to_string(),
            &[
                "betaRed_inst_transport",
                "the_red_env_rec_closed_via_checker_b2",
            ],
            "THE R7 UNLOCK, one-step face: R2's beta substitution transport with its carried \
             RecEnvClosed (red_rec the_red_env) premise DISCHARGED, so it carries NOTHING. R2 \
             proved beta_reduces e e2 -> RecEnvClosed (red_rec the_red_env) -> beta_reduces \
             (instantiate_at e w dd) (instantiate_at e2 w dd) by a 15-arm induction whose iota arm \
             needs iota_subst_commutes; R7 supplies the argument from \
             the_red_env_rec_closed_via_checker_b2 = rec_env_closed_of_b2 (red_rec the_red_env) \
             (Eq.refl Bool Bool.true), the single-rfl checker route in \
             add_the_red_env_faithful_discharge, which is DerivedProved with zero axiom_deps — the \
             kernel whnf-evaluates the depth-aware Bool fold over every real rule RHS of the \
             reflected kernel core env to Bool.true. This is the EXACT fact R6's module docs named \
             as blocked at the ladder's stage position (index 86); it is available here because R7 \
             registers at index 96. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "betaStar_inst_transport_env",
            TY_BETASTAR_INST_TRANSPORT_ENV.to_string(),
            VAL_BETASTAR_INST_TRANSPORT_ENV.to_string(),
            &[
                "betaStar_inst_transport",
                "the_red_env_rec_closed_via_checker_b2",
            ],
            "THE R7 UNLOCK, development face: betaStar b b2 -> betaStar (instantiate b a) \
             (instantiate b2 a), with no carried premise. R2's betaStar_inst_transport with the \
             discharged witness supplied. This is the form the Tait engine actually consumes: \
             candInterp_lam's development family quantifies over betaStar developments of the \
             SUBSTITUTED body, and transporting each one through instantiate is precisely what R6 \
             could not do and therefore hoisted into SynTy.lam's rule. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "candInterp_betaStar_closed",
            TY_CANDINTERP_BETASTAR_CLOSED.to_string(),
            VAL_CANDINTERP_BETASTAR_CLOSED.to_string(),
            &[
                "betaStar.rec",
                "isCandHF_cr2",
                "candInterp_isCandHF",
                "whnf_step.beta",
            ],
            "Every candidate candInterp T is closed under beta DEVELOPMENT, not just under one \
             step: betaStar.rec over the chain, each link discharged by R5's cr2 projection \
             isCandHF_cr2 at the whnf_step obtained from whnf_step.beta. The motive is the \
             ARROW candInterp T x -> candInterp T y, so the refl arm is the identity and the step \
             arm composes cr2 with the IH. Together with betaStar_inst_transport_env this is the \
             complete replacement for R6's hoisted premise. Zero axiom_deps.",
        )?;

        // --- Group B: the textbook judgment ---
        self.add_inductive(
            &src_syn_ty_t(),
            "SynTyT G e T — THE TEXTBOOK TYPING JUDGMENT of the R7 fragment. Four rules, every one \
             of them the ordinary shape: var by ctx_lookup, sort at the successor universe, app by \
             pi-elimination, and lam by pi-introduction in the extended context with a SINGLE \
             sub-derivation `SynTyT (cons A G) b B`. Compare R6's SynTy.lam, which additionally \
             carried the DEVELOPMENT-CLOSURE premise `forall s b2, betaStar (psubst (up s) b) b2 \
             -> SynTy (cons A G) b2 B`: that premise is GONE here, and the shape guard refuses \
             both `betaStar` and `psubst` anywhere in this inductive's source. It could go because \
             R7 registers after add_the_red_env_faithful_discharge and may therefore DISCHARGE the \
             RecEnvClosed premise of R2's substitution transport (betaStar_inst_transport_env), \
             which is the fact the Tait engine needed and R6 lacked; r7_dev_family_derived states \
             the hoisted premise as the theorem it now is. Like SynTy, this judgment still mentions \
             NO candInterp anywhere and still keeps the SimpleTy A side condition, which is NOT a \
             stage-position artifact: R5's candInterp has a NON-DEPENDENT Pi clause whose \
             exactness needs a substitution-inert domain, and the dependent clause is PROVED \
             non-portable (r6_dependent_pi_self_reachable). Strict positivity is immediate (the \
             recursive premise is a bare SynTyT). No fixedIndicesToParams promotion: the leading \
             (G : ListType KExpr) is uniform across the four conclusions but the lam premise \
             concludes at ListType.cons KExpr A G, so the first index is not fixed — the same \
             reason TypingCtx and SynTy keep their 3-ary index motives. SCOPE: strictly narrower \
             than TypingCtx (no const, no let_, no pi formation, SimpleTy domains only); nothing \
             about it advances M : CandModel tenv. Not total: synTyT_not_total. ZERO new axioms.",
        )?;

        // --- Group C: the fundamental theorem and the capstones ---
        add_thm(
            self,
            "synTyT_fundamental",
            TY_SYNTYT_FUNDAMENTAL.to_string(),
            val_syntyt_fundamental(),
            &[
                "SynTyT.rec",
                "SubstOK",
                "candInterp_sort_mem",
                "candInterp_app",
                "candInterp_lam",
                "candInterp_cr1",
                "candInterp_var",
                "candInterp_betaStar_closed",
                "betaStar_inst_transport_env",
                "simpleTy_psubst",
                "simpleTy_whnfAcc",
                "substOK_extend",
                "psubst_scons_instantiate",
                "whnfAcc_of_instantiate_bvar0",
                "whnfAcc_sort",
                "Eq.substType",
            ],
            "THE FUNDAMENTAL THEOREM for the TEXTBOOK judgment: every SynTyT-derivable term \
             inhabits its type's interpretation at every closing substitution. One SynTyT.rec with \
             a full four-binder motive. Three arms are R6's verbatim (var is the SubstOK lookup, \
             sort is candInterp_sort_mem on whnfAcc_sort, app is candInterp_app on the two IHs). \
             The lam arm is the rung: from the ORDINARY single-body IH `forall s2, SubstOK s2 \
             (cons A G) -> candInterp B (psubst s2 b)` it builds all three candInterp_lam \
             premises. (1) The annotation's SN is simpleTy_whnfAcc transported along \
             simpleTy_psubst. (2) The BODY's SN is the IH at the fresh variable — scons (bvar 0) s \
             closes the extended context by substOK_extend on candInterp_var — reshaped by \
             psubst_scons_instantiate and unwound by whnfAcc_of_instantiate_bvar0; that is the \
             landed fundamental_pi idiom (dependent_sn_richmodel.rs:3888) and it is why the \
             RecEnvLiftClosed discharge R6 named is NOT needed: R7 never lifts. (3) The \
             DEVELOPMENT FAMILY — the premise R6 had to hoist into SynTy.lam's rule — is the IH at \
             scons a s reshaped by psubst_scons_instantiate, transported through the development by \
             the DISCHARGED betaStar_inst_transport_env, and landed by candInterp_betaStar_closed. \
             Carries NO premise: no CandModel, no RecEnvClosed, no RecEnvLiftClosed, no \
             DefEnvClosed. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_sn_subst",
            TY_SYNTYT_SN_SUBST.to_string(),
            VAL_SYNTYT_SN_SUBST.to_string(),
            &["synTyT_fundamental", "candInterp_cr1"],
            "SN OF EVERY CLOSING INSTANCE for the textbook judgment: SynTyT G e T implies whnf_acc \
             (psubst s e) for every s that closes G — the fundamental theorem composed with R5's \
             cr1 projection. UNCONDITIONAL. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_sn",
            TY_SYNTYT_SN.to_string(),
            VAL_SYNTYT_SN.to_string(),
            &["synTyT_sn_subst", "substOK_idsubst", "psubst_id"],
            "THE R7 CAPSTONE — UNCONDITIONAL strong normalization for the TEXTBOOK judgment: \
             SynTyT G e T implies whnf_acc e, at an ARBITRARY context, for the spec's FULL \
             env-fixed one-step reduction (beta, zeta, iota at red_rec the_red_env with full \
             congruence, and delta at red_def the_red_env). Instantiate synTyT_sn_subst at idsubst \
             — which closes every context by substOK_idsubst — and cancel with psubst_id. NO \
             carried premise of any kind (pinned by the premise-freedom shape guard); the \
             RecEnvClosed discharge is CONSUMED INSIDE the proof, which is exactly the difference \
             between R7 and R6 and is pinned by its own guard. HONESTY: this is SN for SynTyT, NOT \
             for TypingCtx — it neither discharges nor advances the M : CandModel tenv hypothesis \
             of whnf_terminates_well_typed_dependent, and must never be described as doing so \
             (design section 6.2). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_sn_closed",
            TY_SYNTYT_SN_CLOSED.to_string(),
            VAL_SYNTYT_SN_CLOSED.to_string(),
            &["synTyT_sn"],
            "The closed-term corollary: SynTyT nil e T implies whnf_acc e. A one-line \
             specialization of synTyT_sn, which already holds at every context. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_fundamental_typesubst",
            TY_SYNTYT_FUNDAMENTAL_TYPESUBST.to_string(),
            VAL_SYNTYT_FUNDAMENTAL_TYPESUBST.to_string(),
            &["synTyT_fundamental", "simpleTy_psubst", "Eq.substType"],
            "The fundamental theorem in the SUBSTITUTED-TYPE spelling candInterp (psubst s T) \
             (psubst s e), under a SimpleTy T premise, obtained by transporting along \
             simpleTy_psubst. Registered because that is the shape the guide's tower uses \
             (fundamental_general concludes at cm_Red (psubst s T) (psubst s e)). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r7_dev_family_derived",
            TY_R7_DEV_FAMILY_DERIVED.to_string(),
            VAL_R7_DEV_FAMILY_DERIVED.to_string(),
            &[
                "synTyT_fundamental",
                "candInterp_betaStar_closed",
                "betaStar_inst_transport_env",
                "psubst_scons_instantiate",
                "substOK_extend",
                "Eq.substType",
            ],
            "R6'S HOISTED PREMISE, NOW A THEOREM — the constant that makes the R7 claim checkable \
             rather than narrative. From the ORDINARY typing derivation of the body in the \
             extended context, SynTyT (cons A G) b B, it produces the whole family the Tait engine \
             demands: for every closing s, every beta-DEVELOPMENT b2 of the substituted body, and \
             every member a of the domain interpretation, candInterp B (instantiate b2 a). R6 \
             could not derive this and therefore hoisted its syntactic shadow into SynTy.lam's \
             RULE; the three ingredients that were missing at stage 86 and are present at stage 96 \
             are betaStar_inst_transport_env (R2's transport with RecEnvClosed DISCHARGED), \
             candInterp_betaStar_closed, and psubst_scons_instantiate. Proved as a corollary of \
             synTyT_fundamental (not used to prove it — that would be circular; the fundamental \
             theorem's lam arm inlines the same three steps against its IH). Zero axiom_deps.",
        )?;

        // --- Group D: the bridge from R6 ---
        add_thm(
            self,
            "psubst_up_idsubst",
            TY_PSUBST_UP_IDSUBST.to_string(),
            VAL_PSUBST_UP_IDSUBST.to_string(),
            &["psubst_pointwise", "up_idsubst", "psubst_id", "Eq.trans"],
            "psubst (up idsubst) b = b: `up` fixes the identity substitution POINTWISE \
             (up_idsubst), the landed funext-free psubst_pointwise turns that into equality of the \
             two substitution actions, and psubst_id finishes. Small, but it is the exact hinge of \
             the bridge below — R6's development premise is stated at psubst (up s) b, and \
             collapsing it at s := idsubst is what recovers the textbook rule's single \
             sub-derivation. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTy_to_synTyT",
            TY_SYNTY_TO_SYNTYT.to_string(),
            val_synty_to_syntyt(),
            &[
                "SynTy.rec",
                "SynTyT.var",
                "SynTyT.sort",
                "SynTyT.app",
                "SynTyT.lam",
                "psubst_up_idsubst",
                "betaStar.refl",
                "Eq.substType",
            ],
            "THE BRIDGE: every R6 derivation is an R7 derivation. SynTy.rec with the motive SynTyT \
             qG qe qT; var/sort/app map constructor-for-constructor, and the lam arm consumes R6's \
             development-closure IH at s := idsubst and the REFLEXIVE development, yielding SynTyT \
             (cons A G) (psubst (up idsubst) b) B, which psubst_up_idsubst collapses to the \
             textbook premise SynTyT (cons A G) b B. So R6's work is SUBSUMED, not orphaned, and \
             synTy_sn_via_synTyT below re-derives its capstone. DIRECTION MATTERS AND IS THE ONLY \
             ONE CLAIMED: the converse SynTyT G e T -> SynTy G e T would need SUBJECT REDUCTION \
             for SynTyT plus substitution stability (to type every development of every \
             substitution instance of a body), neither of which is landed — and SynTyT is \
             genuinely WIDER, as synTyT_lam_redex_witness exhibits. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTy_sn_via_synTyT",
            TY_SYNTY_SN_VIA_SYNTYT.to_string(),
            VAL_SYNTY_SN_VIA_SYNTYT.to_string(),
            &["synTyT_sn", "synTy_to_synTyT"],
            "R6's CAPSTONE, RE-DERIVED THROUGH R7's: SynTy G e T implies whnf_acc e, obtained as \
             synTyT_sn after the bridge instead of through synTy_fundamental. Same statement as \
             the landed synTy_sn, different proof — registered so that the subsumption is a \
             kernel-checked fact and not a claim about two developments that merely look alike. \
             Zero axiom_deps.",
        )?;

        // --- Group E: witnesses and the non-degeneracy guard ---
        add_thm(
            self,
            "synTyT_id",
            ty_syntyt_id(),
            val_syntyt_id(),
            &["SynTyT.lam", "SynTyT.var", "SimpleTy.base"],
            "The fragment's identity function is typed by the TEXTBOOK rule, in every context: lam \
             (sort 0) (bvar 0) : pi (sort 0) (sort 0), by SynTyT.lam over one SynTyT.var with \
             ctx_lookup (cons (sort 0) G) 0 = some (sort 0) by Eq.refl. Read against R6's \
             synTy_id, which needed the development premise discharged for EVERY substitution and \
             therefore an Eq.substType through betaStar_bvar_collapse: the textbook rule removes \
             that entirely even in the easiest case. Also a PREMISE-SATISFIABILITY WITNESS for \
             SynTyT (constructors do not count on the supply side). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_sort_witness",
            ty_syntyt_sort_witness(),
            val_syntyt_sort_witness(),
            &["SynTyT.sort"],
            "sort 0 : sort 1 in the empty context — the judgment's non-vacuity at its simplest \
             rule, a pure constructor application with no computation, and a closed-conclusion \
             premise-satisfiability witness for SynTyT. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_app_witness",
            ty_syntyt_app_witness(),
            val_syntyt_app_witness(),
            &["SynTyT.app", "SynTyT.var", "synTyT_id"],
            "A genuine BETA REDEX inside the textbook judgment: app (lam (sort 0) (bvar 0)) (bvar \
             0) : sort 0 in the one-entry context [sort 0], by pi-elim at the identity function \
             and the context variable. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_lam_redex_witness",
            ty_syntyt_lam_redex_witness(),
            val_syntyt_lam_redex_witness(),
            &["SynTyT.lam", "SimpleTy.base", "synTyT_app_witness"],
            "THE WITNESS THAT THE TEXTBOOK RULE BUYS SOMETHING REAL: lam (sort 0) (app (lam (sort \
             0) (bvar 0)) (bvar 0)) : pi (sort 0) (sort 0) in the EMPTY context — a lambda whose \
             BODY IS A LIVE BETA REDEX — derived by ONE SynTyT.lam over the app witness. Under \
             R6's SynTy.lam the same term demands SynTy (cons (sort 0) nil) b2 (sort 0) for EVERY \
             b2 with betaStar (psubst (up s) (app (lam (sort 0) (bvar 0)) (bvar 0))) b2 at EVERY \
             s: an inversion over the developments of a body that actually fires \
             (r7_redex_body_fires), with no betaStar_bvar_collapse available to close it — that \
             lemma is precisely why R6's synTy_id was provable, and it applies only because ITS \
             body takes no step at all. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r7_redex_body_fires",
            ty_r7_redex_body_fires(),
            val_r7_redex_body_fires(),
            &["beta_reduces.beta"],
            "The body of synTyT_lam_redex_witness genuinely BETA-STEPS: app (lam (sort 0) (bvar \
             0)) (bvar 0) beta-reduces to instantiate (bvar 0) (bvar 0), by the head beta \
             constructor. This is what makes the previous constant a real difference between the \
             two rules rather than a rhetorical one — R6's hoisted premise would have had genuine \
             work to do on this body, where on the identity's body (bvar 0) it has none. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "r7_textbook_admits_redex_body",
            ty_r7_textbook_admits_redex_body(),
            val_r7_textbook_admits_redex_body(),
            &[
                "AndType.intro",
                "synTyT_lam_redex_witness",
                "r7_redex_body_fires",
            ],
            "THE TWO HALVES PAIRED, so the R7-versus-R6 difference is one kernel-checked constant: \
             lam (sort 0) (app (lam (sort 0) (bvar 0)) (bvar 0)) IS derivable at pi (sort 0) (sort \
             0) by the textbook rule, AND its body is a live beta redex. Both slots are Type — \
             SynTyT is Type-valued and so is beta_reduces — which is what an AndType slot requires \
             (the kernel is non-cumulative; neither an Eq nor a Type-1 term may sit there, the \
             trap R6 measured). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_sn_witness",
            ty_syntyt_sn_witness(),
            val_syntyt_sn_witness(),
            &["synTyT_sn", "synTyT_lam_redex_witness"],
            "THE POSITIVE WITNESS, obtained THROUGH the capstone: whnf_acc of a beta redex UNDER A \
             BINDER, derived as synTyT_sn applied to synTyT_lam_redex_witness — i.e. through \
             SynTyT.lam, SynTyT.app, the fundamental theorem, the DISCHARGED substitution \
             transport inside the development family, the Tait engine candExpHF_beta inside \
             candInterp_lam, and the cr1 projection. Not by a direct whnf_acc.intro. A strictly \
             larger claim than R6's synTy_sn_witness, which is SN of a bare redex; the lam_body \
             congruence of whnf_step means a lambda is SN only if its body is (see R6's \
             r6_lam_body_acc_necessary, where a lam over a looping body self-steps). Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyT_not_total",
            ty_syntyt_not_total(),
            val_syntyt_not_total(),
            &[
                "synTyT_fundamental",
                "substOK_idsubst",
                "psubst_id",
                "candInterp_pi_not_total",
            ],
            "THE NON-DEGENERACY GUARD (design section 6.1; the micro_has_type total-predicate \
             trap): r5_omegaLam — a STRONGLY NORMALIZING term — is NOT SynTyT-derivable at pi \
             (sort 0) (sort 0), in ANY context. The fundamental theorem at idsubst would place it \
             in candInterp (pi (sort 0) (sort 0)), which R5's candInterp_pi_not_total refutes. So \
             widening SynTy's lam rule to the textbook one did NOT widen it to the total relation, \
             and since the excluded term IS whnf_acc the judgment is not a disguised restatement \
             of strong normalization either. No automated gate performs this discrimination: the \
             axiom census counts axioms and a judgment is value-full. Zero axiom_deps.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r7_tests.rs"]
mod tests;
