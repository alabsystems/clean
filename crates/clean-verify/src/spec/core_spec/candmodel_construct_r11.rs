// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R11 of the candidate-model construction ladder — the rung that WIRES R10's
//! semantic const-at-a-Pi-type into the judgment, and that SETTLES the
//! conversion rule: `candInterp` is **not** conversion-invariant, and the
//! refutation is one β step at the type level.
//!
//! ## A — the deliverable: `SynTyP`, and the const rule at ANY type
//!
//! R10 closed with: *"the ladder now reaches a const at a Pi type SEMANTICALLY
//! (`r10_interp_const_pi_witness`), but only for δ-dead non-recursor names, and
//! no `SynTyC`-style rule consumes it yet — wiring it into the judgment is
//! R11's job, not a wall."* It is not a wall, and it is not narrow either.
//! `SynTyP` is R9's `SynTyC` — all eight rules, textually, so they cannot drift
//! — plus
//!
//! ```text
//! | konstInert : forall G (c : Name) (us : ListType Level) (A : KExpr),
//!      defval_for  (red_def the_red_env) c = none
//!   -> recmeta_for (red_rec the_red_env) c = none
//!   -> SynTyP G (const c us) A
//! ```
//!
//! at **every untyped `A`**, Pi types included. That is `TypingCtx.const`'s
//! shape minus the `tenv` lookup, and it is sound for exactly R10's reason:
//! such a constant is `HeadInert`, hence in EVERY `IsCandHI` candidate
//! (`r10_deadConst_cand_mem`), and `candInterp A` is one at every `A`
//! (`candInterp_isCandHI`). The fundamental-theorem arm is one application —
//! `psubst` is definitionally inert on a `const`, so the goal IS the membership
//! R10 proved. R9's `konstDead` is this rule restricted to `A = sort m`; it is
//! KEPT rather than replaced, because dropping it would break the bridge.
//!
//! `synTyP_fundamental` / `synTyP_sn_subst` / `synTyP_sn` / `synTyP_sn_closed`
//! carry **ZERO premises** — no `CandModel`, no `RecEnvClosed`, no
//! `RecEnvLiftClosed`, no `DefEnvClosed`, no `EnvAcyclic` — guarded exactly as
//! R6–R10 guard theirs. `synTyP_konst_pi_witness` types the REAL reflected
//! `DefEnv` constant at `pi (sort 0) (sort 0)` and
//! `synTyP_sn_konst_pi_witness` obtains its SN **through** the capstone.
//!
//! ## B — the conversion rule: SETTLED, and the answer is REFUTED
//!
//! `TypingCtxConv` adds `conv : TypingCtxConv G e A -> DefEq A B ->
//! TypingCtxConv G e B`, item 4 on R10's list. Wiring it in needs
//!
//! ```text
//! DefEq A B -> candInterp A e -> candInterp B e
//! ```
//!
//! (or R8's equality form, `Eq (KExpr -> Type) (candInterp A) (candInterp B)`,
//! which is the shape a lifting lemma has to take because `PiSet` is
//! contravariant in its domain). **It is false, and the counterexample is three
//! symbols long.** `candInterp` is defined by `KExpr.rec` **on the type**: every
//! non-Pi former goes to the top candidate `whnf_acc` and only `pi` produces a
//! `PiSet`. So take the type-level β redex
//!
//! ```text
//! A := app (lam (sort 0) (bvar 0)) (pi (sort 0) (sort 0))     -- APP-headed
//! B := pi (sort 0) (sort 0)                                    -- its contractum
//! ```
//!
//! `DefEq A B` is `DefEq.beta` (`r11_conv_type_defeq`); `candInterp A` is the
//! top candidate, so R5's `r5_omegaLam` is in it; and `candInterp B` is a
//! PROPER subset that excludes exactly that term (`candInterp_pi_not_total`,
//! R5). Hence `r11_candInterp_conv_refuted`, its equality form
//! `r11_candInterp_conv_eq_refuted`, and the sharpest form
//! `r11_candInterp_step_conv_refuted` — not even ONE `whnf_step` of the type
//! may be transported. The obstruction is the type-level redex itself, not the
//! size of the conversion relation.
//!
//! **Scope of the claim, stated precisely because two different claims are in
//! play.** What is refuted here is conversion-invariance of **`candInterp`** —
//! this ladder's interpretation, and the one every rung from R5 on uses. It is
//! NOT the general impossibility. The general one is the Lean corpus's
//! `no_conv_invariant_substitutive_interpretation`
//! (`proofs/aristotle-whnf-model-guides/stratified-sn/solution/Stratified/SubstConvWall.lean`,
//! axioms: `propext` alone): no interpretation `Int : CEnv -> Tm -> (Tm -> Prop)`
//! can satisfy the variable clause `Int ρ (var i) = ρ i`, λ-body uniformity,
//! conversion invariance and the substitution law `Int ρ (B[a]) = Int (Int ρ a
//! :: ρ) B` together, because substitutivity makes `Int ρ (B[a])` depend on `a`
//! only through the candidate `Int ρ a` while conversion invariance makes it
//! depend on `a`'s whole β-behaviour. Those hypotheses are **not** `candInterp`'s:
//! `candInterp` takes no environment and satisfies no substitution law at all,
//! so the corpus theorem does not apply to it and this refutation is not an
//! instance of it. The two results are independent, and this one is cheaper and
//! narrower — one β step, no environment, no substitution lemma.
//!
//! What IS landed at intermediate generality is
//! `r11_conv_top_proper_incompatible`: for an ARBITRARY `I : KExpr -> KExpr ->
//! Type`, conversion-invariance, top-at-every-app-headed-type and
//! properness-at-`pi (sort 0) (sort 0)` are jointly contradictory. That says the
//! wall is not an artefact of `candInterp`'s particular arms — any interpretation
//! that discriminates at `pi` and does not at `app` meets it — and the specific
//! refutation is registered as its INSTANCE (`r11_candInterp_top_at_app` +
//! `candInterp_pi_not_total`), never re-proved.
//!
//! ### The act on the refutation: the conversion rule that IS sound
//!
//! A refutation is not a reason to have no conversion rule; it is a reason to
//! have the right premise. `SynTyP.convI` converts along equality of the two
//! types' INTERPRETATIONS:
//!
//! ```text
//! | convI : forall G e A B, SynTyP G e A
//!        -> Eq (KExpr -> Type) (candInterp A) (candInterp B) -> SynTyP G e B
//! ```
//!
//! sound by one `Eq.substType` at the pointwise motive (`r11_interpEq_conv` is
//! the same fact standalone). It is **strictly weaker than `TypingCtxConv.conv`
//! and that gap is exactly what is refuted above** — no honest rung can close
//! it. It is also **not** `Eq.refl` decoration: R8's `candInterp_lift_eq` holds
//! at an ARBITRARY type, so `r11_synTyP_unlift_type` /
//! `r11_synTyP_lift_type` make the judgment closed under lifting the TYPE in
//! both directions — the conversion `TypingCtx.var` needs and `SynTyC` could not
//! perform. `synTyP_convI_witness` types the identity lambda at
//! `pi (sort 0) (bvar 0)`, a Pi type with a VARIABLE codomain, and
//! `synTyP_sn_convI_witness` takes its SN through the capstone.
//!
//! ## The bridge, and its direction
//!
//! `synTyC_to_synTyP : SynTyC G e T -> SynTyP G e T`, with NO hypothesis (R11
//! changes no rule of R9's — it only adds two). The CONVERSE is **FALSE and
//! proved so**: `synTyC_no_const_at_pi` shows no `SynTyC` derivation concludes at
//! a `const` EXPRESSION with a `pi` TYPE, in any context at any `A B` — a
//! `SynTyC.rec` over the eight rules with a `Bool` discriminator on the subject
//! and `r11_pi_discr` on the type, where the two const rules are the only arms
//! that are not refutations and both conclude at a SORT — while
//! `synTyP_konst_pi_witness` is exactly such a derivation.
//! `synTyC_sn_via_synTyP` re-derives R9's capstone through R11's; R9's own
//! `synTyC_sn` is NOT superseded.
//!
//! ## Honesty notes (read before quoting)
//!
//! - **Nothing here discharges `M : CandModel tenv`.** `synTyP_sn` is SN for
//!   `SynTyP`, NOT for `TypingCtx`, and must never be described as advancing
//!   `whnf_terminates_well_typed_dependent` (design §6.2). R10 made that more
//!   final, not less, and R11 does not move it: `CandModel.redTypeStep` demands
//!   the model transport ONE step of the type in BOTH directions at every
//!   untyped `T`, and §B refutes that for `candInterp` in the forward direction
//!   at a concrete `T`.
//! - **The refutation is about `candInterp`, not about term-set interpretations
//!   in general.** See §B: the corpus's general theorem has different
//!   hypotheses (environment-indexed, substitutive) that `candInterp` does not
//!   satisfy. Do not cite one for the other.
//! - **`konstInert`'s two side conditions are REAL.** Drop the recmeta one and
//!   the rule types a recursor spine's head at a Pi type, which is R10's
//!   counterexample class; drop the defval one and the constant is a live δ
//!   redex (R9's `r9_konstDead_premise_necessary`). Both are discharged
//!   per-constant by `Eq.refl`, so they cost the capstone nothing.
//! - **Non-degeneracy.** `synTyP_not_total` — `r5_omegaLam`, a strongly
//!   normalizing term, is not `SynTyP`-derivable at `pi (sort 0) (sort 0)` in
//!   ANY context — and `r11_const_pi_rule_proper` pairs it with the const
//!   witness, so the new rule did not turn the judgment into the total relation.
//!   No automated gate performs this check.
//! - **Every predicate R11 introduces in hypothesis position is WITNESSED
//!   here.** `SynTyP` is concluded by `synTyP_id`, `synTyP_sort_witness`,
//!   `synTyP_konst_pi_witness`, `synTyP_convI_witness`, `synTyC_to_synTyP` and
//!   `r11_synTyP_unlift_type`; constructors do not count on the supply side,
//!   which is why those are registered definitions and why the ladder guard
//!   `test_candmodel_ladder_premises_are_witnessed` names `SynTyP`. The two new
//!   `Bool`/`Type` discriminators enter hypothesis position only as
//!   `Eq Bool _ Bool.true`, whose head is `Eq`.
//! - **Recursor conventions are taken from landed consumers, not guessed.** ALL
//!   FIELDS FIRST, THEN ALL IHs, in constructor order. `SynTyP.pi`,
//!   `SynTyP.app` and `SynTyP.letTy` have TWO recursive premises,
//!   `SynTyP.lam`, `SynTyP.konstDelta` and `SynTyP.convI` one, `SynTyP.var`,
//!   `SynTyP.sort`, `SynTyP.konstDead` and `SynTyP.konstInert` none. `convI`'s
//!   IH lands AFTER its non-recursive `Eq` field, which is what the
//!   fields-then-IHs convention says and what the shape guard pins. The
//!   fundamental theorem is R9's term with the judgment renamed and the two new
//!   minors spliced in front of the indices — the splice point is the trailing
//!   ` G e T h` and the guard refuses if R9's term stops ending there.
//! - **No `fixedIndicesToParams` promotion.** The leading `(G : ListType KExpr)`
//!   is uniform across the ten conclusions, but the `pi`, `lam` and `letTy`
//!   recursive premises conclude at `ListType.cons KExpr _ G`, so the first
//!   index is not fixed — unchanged from R9.
//! - **Prop/Type discipline.** `Eq`, `delta_step` and `HeadFree` are Prop;
//!   `candInterp T`, `SynTyC`, `SynTyP`, `DefEq`, `SimpleTy`, `SubstOK`,
//!   `whnf_acc` and `Empty` are Type. `SynTyP.convI`'s `Eq (KExpr -> Type) _ _`
//!   is `Eq` at `Sort 2` and therefore still a **Prop** field of a `Type`-valued
//!   inductive — inside `Eq (α : Sort u)`'s stated polymorphism, not a widening
//!   of it, and the same place R8 put `candInterp_lift_eq`. `AndType (A : Type)
//!   (B : Type)` is `Type 0` and the kernel is NON-CUMULATIVE, so
//!   `r11_conv_gap_is_real` pairs `DefEq` (Type) rather than the `Eq` form.
//! - **`r11_pi_discr` is a registered def with a declared `Type` result**, not
//!   an inline `KExpr.rec`, for R9's measured reason: the converse proof's
//!   motive needs it as the CODOMAIN of an arrow.
//!
//! ## What still separates the judgment from `TypingCtx`, after this rung
//!
//! R10's list, with item 1 CLOSED (up to the `tenv`), item 4 SETTLED as an
//! impossibility, and item 5 unchanged:
//!
//! 1. **CLOSED at the semantics, OPEN at the `tenv`.** `SynTyP.konstInert`
//!    reaches a const at ANY type including a Pi, which is what item 1 asked
//!    for. What remains is that `TypingCtx.const` reads the type off a `tenv`
//!    and imposes NO side condition on the constant, where `konstInert` demands
//!    δ-deadness and non-recursor-hood. Those two are not a shortfall of effort
//!    but the residue of §5 below: a `tenv` may declare a live recursor at a Pi
//!    type, and cr3 provably cannot introduce it;
//! 2. `app` is NON-DEPENDENT and `lam` carries `SimpleTy A` (R5/R6, unchanged);
//! 3. the `let_` rule is the sort-annotated fragment only (R8, unchanged);
//! 4. **SETTLED, and negatively.** `SynTyP` now HAS a conversion rule, but its
//!    premise is interpretation equality, not `DefEq`. The `DefEq` version is
//!    REFUTED (§B) — the second impossibility result of this ladder at a
//!    `TypingCtx` rule, after R10's. A future rung that wants
//!    `TypingCtxConv.conv` needs a DIFFERENT interpretation (one that does not
//!    recurse on the type's syntax — the corpus's kind-indexed semantic values
//!    are the known shape), not more effort on this one. `lam` still has no
//!    `TypingCtx G A (sort u)` premise;
//! 5. the remaining const-at-Pi cases are the ones with a live recursor head or
//!    a live δ value. The δ half is R9's `konstDelta` and is vacuous over this
//!    env; the recursor half is R10's counterexample class and is UNREACHABLE by
//!    cr3 in principle. Anything that wants it must supply ι-contractum
//!    membership from an ι-EXPANSION engine (R2/R3's
//!    `candExp_iota_natrec_zero` shape), never from cr3.
//!
//! ## Census
//!
//! ZERO new axioms: one genuine inductive via `add_inductive`, three plain defs
//! via `add_recursive_def`, everything else a value-bearing theorem via
//! `add_definition` with kernel `add_decl` checking. Census-neutral.

use std::collections::HashSet;

use super::candmodel_construct_r11_src::*;
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Register one value-bearing theorem (R6-R10's helper, verbatim).
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
    /// Register R11: the judgment `SynTyP` (R9's `SynTyC` plus the const rule at
    /// ANY type and the semantic conversion rule), its unconditional SN
    /// capstones, the bridge from R9 with its converse PROVED false, and the
    /// SETTLEMENT that `candInterp` is not conversion-invariant.
    ///
    /// MUST be registered AFTER `add_candmodel_construct_r10`
    /// (`r10_deadConst_cand_mem`, `candInterp_isCandHI`) and therefore after
    /// R0-R9. Also requires `add_typing_def_eq` (`DefEq`, `DefEq.beta`),
    /// `add_delta_step` (`defval_for`), `add_iota_step` (`recmeta_for`,
    /// `RecMeta`) and the generated `kernel_core_red_env` atoms
    /// (`fixture_def_env_name`).
    pub(super) fn add_candmodel_construct_r11(&mut self) -> Result<(), SpecError> {
        // --- Group A: the judgment and its capstones ---
        self.add_inductive(
            &src_syn_ty_p(),
            "SynTyP G e T — THE CONST-AT-A-PI-TYPE JUDGMENT: R9's SynTyC with all eight rules \
             textually unchanged, plus konstInert (a constant that the REAL reflected environment \
             gives neither a definitional value nor recursor metadata is typed at ANY A, Pi types \
             included — TypingCtx.const's shape minus the tenv lookup) and convI (conversion along \
             equality of the two types' INTERPRETATIONS, which is the strongest conversion premise \
             candInterp supports; the DefEq version is REFUTED by \
             r11_candInterp_conv_eq_refuted). Positivity is immediate (every recursive premise is \
             a bare SynTyP). konstInert is sound because such a constant is HeadInert, hence in \
             every IsCandHI candidate (r10_deadConst_cand_mem), and candInterp A is one at every A \
             (candInterp_isCandHI). R9's konstDead is kept rather than replaced so the bridge \
             stays hypothesis-free. Not total: synTyP_not_total. Nothing about it advances \
             M : CandModel tenv.",
        )?;
        add_thm(
            self,
            "synTyP_fundamental",
            ty_syntyp_fundamental(),
            val_syntyp_fundamental(),
            &[
                "SynTyP",
                "SynTyP.rec",
                "candInterp",
                "SubstOK",
                "r10_deadConst_cand_mem",
                "candInterp_isCandHI",
                "Eq.substType",
            ],
            "THE FUNDAMENTAL THEOREM for the const-at-a-Pi rung: every SynTyP-derivable term \
             inhabits its type's interpretation at every closing substitution. One SynTyP.rec with \
             a full four-binder motive and TEN minors. Eight of them are R9's synTyC_fundamental \
             arms with the judgment renamed — spliced textually, never retyped, so the shared \
             rules cannot drift. The konstInert arm is ONE application: psubst is definitionally \
             inert on a const, so the goal IS r10_deadConst_cand_mem's conclusion at candInterp A. \
             The convI arm is one Eq.substType at the pointwise motive fun F => F (psubst s e), \
             R8's candInterp_lift transport in shape. ZERO carried premises — no CandModel, no \
             RecEnvClosed, no RecEnvLiftClosed, no DefEnvClosed, no EnvAcyclic. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyP_sn_subst",
            ty_syntyp_sn_subst(),
            val_syntyp_sn_subst(),
            &["synTyP_fundamental", "candInterp_cr1"],
            "SN OF EVERY CLOSING INSTANCE for the const-at-a-Pi rung: SynTyP G e T implies \
             whnf_acc (psubst s e) at every SubstOK s G. cr1 of the interpretation applied to the \
             fundamental theorem. Zero carried premises, zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyP_sn",
            ty_syntyp_sn(),
            val_syntyp_sn(),
            &["synTyP_sn_subst", "substOK_idsubst", "psubst_id"],
            "THE CAPSTONE — UNCONDITIONAL strong normalization for the judgment that reaches a \
             constant at a PI type: SynTyP G e T implies whnf_acc e, at an ARBITRARY context, for \
             the spec's FULL beta+zeta+iota+delta step relation over the REAL reflected kernel \
             environment. Obtained from synTyP_sn_subst at the identity substitution. HONESTY: \
             this is SN for SynTyP, NOT for TypingCtx, and it does not advance \
             whnf_terminates_well_typed_dependent. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTyP_sn_closed",
            ty_syntyp_sn_closed(),
            val_syntyp_sn_closed(),
            &["synTyP_sn"],
            "The closed-term corollary: SynTyP nil e T implies whnf_acc e. A one-line \
             specialization of synTyP_sn, which already holds at every context. Zero axiom_deps.",
        )?;

        // --- Group B: the bridge, and the proof that its converse is false ---
        add_thm(
            self,
            "synTyC_to_synTyP",
            TY_SYNTYC_TO_SYNTYP.to_string(),
            val_syntyc_to_syntyp(),
            &["SynTyC", "SynTyP", "SynTyC.rec"],
            "THE BRIDGE, with NO hypothesis: every R9 derivation is an R11 derivation. R11 changes \
             no rule of R9's, it only adds two, so each of the eight minors rebuilds its own \
             constructor at the new judgment. Contrast R8's bridge, which needed CtxSimple G \
             because it CHANGED the var rule.",
        )?;
        add_thm(
            self,
            "synTyC_sn_via_synTyP",
            TY_SYNTYC_SN_VIA_SYNTYP.to_string(),
            VAL_SYNTYC_SN_VIA_SYNTYP.to_string(),
            &["synTyC_to_synTyP", "synTyP_sn"],
            "R9's capstone re-derived through R11's. R9's own synTyC_sn is NOT superseded — it is \
             the same statement proved without the two new rules in scope.",
        )?;
        self.add_recursive_def(
            SRC_KEXPR_IS_CONST_B,
            "kexpr_is_const_b e — Bool-valued `is this a const?', R9's kexpr_is_lam_b at the const \
             former. The demand-side discriminator of the bridge's converse proof: a SynTyC.rec \
             motive cannot case on the SUBJECT directly, so the subject enters as an \
             Eq Bool (kexpr_is_const_b qe) Bool.true hypothesis that seven of the eight arms \
             refute by computation.",
        )?;
        self.add_recursive_def(
            SRC_R11_PI_DISCR,
            "r11_pi_discr T — the TYPE-side discriminator: Empty at a pi, Nat everywhere else. A \
             REGISTERED def with a declared Type result rather than an inline KExpr.rec, for R9's \
             measured 2026-08-26 reason: synTyC_no_const_at_pi needs it as the CODOMAIN of an \
             arrow inside a recursor motive, and an inline (fun (_ : KExpr) => Type) qT beta-redex \
             is not a sort the elaborator accepts there.",
        )?;
        add_thm(
            self,
            "synTyC_no_const_at_pi",
            TY_SYNTYC_NO_CONST_AT_PI.to_string(),
            val_syntyc_no_const_at_pi(),
            &[
                "SynTyC",
                "SynTyC.rec",
                "kexpr_is_const_b",
                "r11_pi_discr",
                "bool_false_ne_true_t",
            ],
            "THE CONVERSE OF THE BRIDGE IS FALSE, PROVED: no SynTyC derivation concludes at a \
             const EXPRESSION with a pi TYPE, in any context at any A B. One SynTyC.rec whose \
             motive pairs a Bool discriminator on the subject with r11_pi_discr on the type; six \
             arms refute their is-const hypothesis by computation, and the two arms that cannot — \
             konstDead and konstDelta, the only rules that reach a const at all — both conclude at \
             a SORT, where the type discriminator is inhabited. Together with \
             synTyP_konst_pi_witness this makes synTyC_to_synTyP a STRICT inclusion.",
        )?;

        // --- Group C: the witnesses ---
        for (name, ty, val, deps, desc) in [
            (
                "synTyP_id",
                ty_synty_p_id(),
                val_synty_p_id(),
                vec!["SynTyP", "SimpleTy"],
                "The fragment's identity function typed at pi (sort 0) (sort 0) in an arbitrary \
                 context — the premise gate's unconditional supply for SynTyP, and the subject of \
                 the conversion witness below.",
            ),
            (
                "synTyP_sort_witness",
                ty_synty_p_sort_witness(),
                val_synty_p_sort_witness(),
                vec!["SynTyP"],
                "(sort 0 : sort 1) in the empty context — the second registered conclusion of \
                 SynTyP, since a CONSTRUCTOR does not count on the premise gate's supply side.",
            ),
            (
                "synTyP_konst_pi_witness",
                ty_synty_p_konst_pi_witness(),
                val_synty_p_konst_pi_witness(),
                vec!["SynTyP", "the_red_env"],
                "THE DELIVERABLE'S WITNESS: the REAL reflected kernel constant fixture_def_env_name (the \
                 inductive type DefEnv) typed at the PI type pi (sort 0) (sort 0). R9 named `no \
                 rule reaches a const at a PI type at all' as the newest gap and R10 closed it \
                 SEMANTICALLY; this is the same fact inside the JUDGMENT. Both side conditions — \
                 no definitional value, no recursor metadata, over the real environment — are one \
                 @Eq.refl each, so a regeneration of the reflection that defined that name would \
                 fail this CLOSED.",
            ),
            (
                "synTyP_sn_konst_pi_witness",
                ty_synty_p_sn_konst_pi_witness(),
                val_synty_p_sn_konst_pi_witness(),
                vec!["synTyP_sn", "synTyP_konst_pi_witness"],
                "...and its strong normalization THROUGH the capstone rather than around it: the \
                 SN of a term typed by the NEW rule is obtained by applying synTyP_sn to the new \
                 rule's derivation, so the capstone is exercised at exactly the rung's addition.",
            ),
            (
                "synTyP_convI_witness",
                ty_synty_p_convi_witness(),
                val_synty_p_convi_witness(),
                vec!["SynTyP", "synTyP_id", "candInterp"],
                "THE CONVERSION RULE AT A CONCRETE TERM: the identity lambda typed at pi (sort 0) \
                 (bvar 0), a Pi type whose CODOMAIN IS A VARIABLE. Both codomains are non-Pi \
                 formers, so both interpretations are the top candidate and the premise is one \
                 @Eq.refl — but the two types are different KExprs and R9's conv-free judgment \
                 reaches only the first of them.",
            ),
            (
                "synTyP_sn_convI_witness",
                ty_synty_p_sn_convi_witness(),
                val_synty_p_sn_convi_witness(),
                vec!["synTyP_sn", "synTyP_convI_witness"],
                "SN of the conversion witness, again THROUGH the capstone: the derivation whose \
                 last rule is convI still yields whnf_acc by synTyP_sn.",
            ),
            (
                "r11_synTyP_unlift_type",
                TY_R11_SYNTYP_UNLIFT_TYPE.to_string(),
                VAL_R11_SYNTYP_UNLIFT_TYPE.to_string(),
                vec!["SynTyP", "candInterp_lift_eq"],
                "THE CONVERSION RULE'S GENERAL CONTENT, and the answer to `is convI just @Eq.refl \
                 decoration?': R8's candInterp_lift_eq equates the two membership PREDICATES at an \
                 ARBITRARY type, so SynTyP is closed under UN-LIFTING the type. That is exactly \
                 the conversion TypingCtx.var's lifted conclusion needs, and SynTyC cannot perform \
                 it.",
            ),
            (
                "r11_synTyP_lift_type",
                TY_R11_SYNTYP_LIFT_TYPE.to_string(),
                VAL_R11_SYNTYP_LIFT_TYPE.to_string(),
                vec!["SynTyP", "candInterp_lift_eq", "Eq.symm"],
                "...and under lifting it, by the same equality read backwards. The pair is why the \
                 premise is stated as an EQUALITY of predicates rather than an implication: PiSet \
                 is contravariant in its domain, so an implication-only rule would not have both \
                 directions.",
            ),
            (
                "synTyP_not_total",
                ty_synty_p_not_total(),
                val_synty_p_not_total(),
                vec![
                    "SynTyP",
                    "synTyP_fundamental",
                    "candInterp_pi_not_total",
                    "r5_omegaLam",
                ],
                "THE NON-DEGENERACY GUARD: r5_omegaLam — a strongly normalizing term — is NOT \
                 SynTyP-derivable at pi (sort 0) (sort 0) in ANY context, through the fundamental \
                 theorem and R5's properness of the Pi interpretation. The micro_has_type \
                 total-predicate trap; no automated gate performs it.",
            ),
            (
                "r11_const_pi_rule_proper",
                ty_r11_const_pi_rule_proper(),
                val_r11_const_pi_rule_proper(),
                vec!["synTyP_konst_pi_witness", "synTyP_not_total"],
                "Non-degeneracy OF THE NEW RULE specifically: the real reflected constant IS \
                 derivable at the Pi type and R5's looping lambda is still not, so admitting \
                 constants at every type did not collapse the judgment into the total relation. \
                 R10's r10_const_unlock_proper one level up, at the judgment instead of the \
                 interpretation.",
            ),
        ] {
            add_thm(self, name, ty, val, &deps, desc)?;
        }

        // --- Group D: THE CONVERSION SETTLEMENT ---
        add_thm(
            self,
            "r11_conv_type_defeq",
            ty_r11_conv_type_defeq(),
            val_r11_conv_type_defeq(),
            &["DefEq"],
            "The counterexample's conversion, at the relation TypingCtxConv.conv actually converts \
             along: app (lam (sort 0) (bvar 0)) (pi (sort 0) (sort 0)) is DefEq to pi (sort 0) \
             (sort 0), by DefEq.beta and one kernel computation of instantiate. A type-level beta \
             redex, the cheapest conversion there is.",
        )?;
        add_thm(
            self,
            "r11_candInterp_top_at_app",
            TY_R11_CANDINTERP_TOP_AT_APP.to_string(),
            VAL_R11_CANDINTERP_TOP_AT_APP.to_string(),
            &["candInterp"],
            "candInterp at an APP-headed type is the TOP candidate, definitionally — the app arm \
             of its KExpr.rec ignores its subterms, as every non-Pi arm does. The identity \
             function is the whole proof. This is one of the three properties the incompatibility \
             below pits against each other, and it is not an accident of this rung: it is what \
             makes candInterp structural in the type.",
        )?;
        add_thm(
            self,
            "r11_conv_top_proper_incompatible",
            ty_r11_conv_top_proper_incompatible(),
            val_r11_conv_top_proper_incompatible(),
            &["DefEq", "r11_conv_type_defeq", "r5_whnfAcc_omegaLam"],
            "THE INCOMPATIBILITY, at an ARBITRARY interpretation I : KExpr -> KExpr -> Type: \
             conversion-invariance along DefEq, top-at-every-app-headed-type, and \
             properness-at-pi (sort 0) (sort 0) cannot all hold. Any two can. The proof is one \
             type-level beta step: r5_omegaLam is in I of the redex by top-ness, transports to I \
             of the contractum by conversion-invariance, and is excluded there by properness. \
             SCOPE: this is NOT the corpus's general impossibility \
             (no_conv_invariant_substitutive_interpretation, Stratified/SubstConvWall.lean), whose \
             hypotheses are environment-indexing, a variable clause, lambda-body uniformity and a \
             substitution law — none of which candInterp has. The two results are independent; \
             this one is cheaper and narrower.",
        )?;
        add_thm(
            self,
            "r11_candInterp_conv_refuted",
            TY_R11_CANDINTERP_CONV_REFUTED.to_string(),
            val_r11_candinterp_conv_refuted(),
            &[
                "candInterp",
                "DefEq",
                "r11_conv_top_proper_incompatible",
                "r11_candInterp_top_at_app",
                "candInterp_pi_not_total",
            ],
            "THE SETTLEMENT: candInterp is NOT conversion-invariant, so TypingCtxConv's conv rule \
             has NO counterpart in this ladder's interpretation. Registered as an INSTANCE of the \
             abstract incompatibility rather than re-proved, with candInterp's two witnesses \
             supplied: r11_candInterp_top_at_app and R5's candInterp_pi_not_total. The reason is \
             structural and worth stating once: candInterp is defined by KExpr.rec ON THE TYPE, so \
             a conversion that changes the type's head former from app to pi changes its value \
             from the top candidate to a proper subset. HONESTY: this refutes conversion \
             invariance for candInterp, the interpretation every rung of this ladder uses; it is \
             not the corpus's general theorem about environment-based substitutive \
             interpretations, whose hypotheses candInterp does not satisfy.",
        )?;
        add_thm(
            self,
            "r11_candInterp_conv_eq_refuted",
            TY_R11_CANDINTERP_CONV_EQ_REFUTED.to_string(),
            VAL_R11_CANDINTERP_CONV_EQ_REFUTED.to_string(),
            &["r11_candInterp_conv_refuted", "Eq.substType"],
            "...and in the EQUALITY form R8 had to use for lifting, because PiSet is contravariant \
             in its domain and a one-way implication would not carry both directions: DefEq A B \
             does NOT give Eq (KExpr -> Type) (candInterp A) (candInterp B). This is the exact \
             premise SynTyP.convI would need to be strengthened to TypingCtxConv.conv, and it is \
             false.",
        )?;
        add_thm(
            self,
            "r11_candInterp_step_conv_refuted",
            TY_R11_CANDINTERP_STEP_CONV_REFUTED.to_string(),
            val_r11_candinterp_step_conv_refuted(),
            &[
                "candInterp",
                "candInterp_pi_not_total",
                "r5_whnfAcc_omegaLam",
            ],
            "THE SHARPEST FORM: not even ONE whnf_step of the TYPE may be transported through the \
             interpretation. DefEq contains that step, so the wall is met at its narrowest, which \
             locates the obstruction precisely — it is the type-level beta redex itself, not the \
             size of the conversion relation. Anyone tempted to weaken the conv rule from DefEq to \
             single-step reduction should read this first.",
        )?;
        add_thm(
            self,
            "r11_conv_gap_is_real",
            ty_r11_conv_gap_is_real(),
            val_r11_conv_gap_is_real(),
            &[
                "candInterp",
                "DefEq",
                "r11_conv_type_defeq",
                "candInterp_pi_not_total",
            ],
            "The three measured facts of the conversion counterexample in one kernel-checked \
             constant, R10's r10_cr3_gap_is_real for this rung: the term IS in the redex type's \
             interpretation (definitionally, since that type is app-headed), the two types ARE \
             DefEq, and the term is NOT in the contractum type's. A refutation is the conjunction \
             of those three and nothing else.",
        )?;
        add_thm(
            self,
            "r11_interpEq_conv",
            TY_R11_INTERPEQ_CONV.to_string(),
            VAL_R11_INTERPEQ_CONV.to_string(),
            &["candInterp", "Eq.substType"],
            "THE POSITIVE HALF, standalone: conversion along equality of INTERPRETATIONS is sound \
             at every A, B and e — one Eq.substType at the pointwise motive. This is the premise \
             SynTyP.convI carries, and the honest strongest one, since strengthening it to DefEq \
             is refuted above and weakening it to a single reduction step is refuted too.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r11_tests.rs"]
mod tests;
