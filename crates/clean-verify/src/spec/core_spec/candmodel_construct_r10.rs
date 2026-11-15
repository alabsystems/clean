// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R10 of the candidate-model construction ladder — the KEYSTONE rung. The
//! head-free restriction on the Pi-candidate's cr3 is **not** an artefact of
//! R5's proof and it is **not** liftable by any stratification: unrestricted
//! cr3 for `PiSet` is **FALSE at the real reflected environment**, and this
//! rung proves it. The circularity question four rungs deferred is therefore
//! settled in the strongest possible direction — not "circular", not
//! "stratifiable", but REFUTED — and the honest strongest cr3 face is landed
//! beside the refutation, widened exactly as far as the counterexample allows.
//!
//! ## A — the question, and why it does not have the shape everyone assumed
//!
//! R5 closed with: *"full cr3 may well be true, but it must be supplied from
//! outside cr3, after the fundamental theorem gives SN of real-env ι
//! contracta."* R1, R5, R8 and R9 all recorded the same wall from different
//! sides. The task for this rung was to decide whether that SN can be obtained
//! independently of `candInterp` — by R9's δ-rank induction, by the ι-rule
//! structure of `red_rec the_red_env`, or by R3/R4's spine inversions.
//!
//! **The dependency graph does not close, because the goal it would close is
//! false.** Written out, the obligation R5 could not discharge is
//!
//! ```text
//! e Neutral,  (forall e2, whnf_step e e2 -> PiSet CA CB e2),  CA a,
//! iota_step (red_rec the_red_env) (app e a) w   |-   CB a w
//! ```
//!
//! and the only inputs are the ι rule and the two candidate interfaces. R5's
//! own exhibit (`Nat.rec (bvar 0) (bvar 0) (bvar 0)` at `Nat.zero`) shows the
//! premises carry NO information about `w`; it does not show that no `w` is
//! bad, and in fact for THAT term the contractum β-collapses to `bvar 0`, which
//! every candidate contains by cr3. So R5's exhibit is a gap, not a refutation.
//!
//! This rung closes the question with a term for which the contractum IS bad:
//!
//! ```text
//! e := Nat.rec (bvar 0) omegaLam (bvar 0)        -- 3-argument, STUCK
//! a := Nat.zero                                   -- in CA := whnf_acc
//! b := omegaLam                                   -- in candInterp (sort 0)
//! ```
//!
//! with `CA := whnf_acc` and the CONSTANT codomain family
//! `CB := fun _ => candInterp (pi (sort 0) (sort 0))`. Every side condition of
//! `isCandHF_piSet` holds — `isCandHF_whnfAcc`, `candInterp_isCandHF`,
//! `candStepInv_const` — `e` is `Neutral`, and `e` takes NO `whnf_step` at all
//! (`r10_stuckOmega_no_whnf_step`), so cr3's reduct premise is satisfied
//! vacuously and costs nothing. Yet
//!
//! ```text
//! app (app e Nat.zero) omegaLam
//!   ->iota  app (rhsZero (bvar 0) omegaLam (bvar 0)) omegaLam
//!   ->beta  ->beta  ->beta   app omegaLam omegaLam   -- and that is Omega
//! ```
//!
//! `r10_appStuck_not_whnfAcc` walks that five-step chain with
//! `whnfAcc_inv_step` and lands on R5's `r5_omegaV_not_whnfAcc`. So the cr3
//! CONCLUSION `PiSet CA CB e` is false while every hypothesis holds:
//! `r10_piSet_cr3_unrestricted_refuted`. The ι contractum's SN is not merely
//! unavailable early — it is **not a theorem**, so no reordering of the
//! dependency graph can supply it.
//!
//! Three structural facts make the counterexample work, and they are worth
//! keeping because they say exactly which reduction the wall is:
//!
//! 1. **The δ leg was never the problem.** R5's `deltaReduct_app_gen` already
//!    proves `delta_reduct env (app e a)` factors through `delta_reduct env e`,
//!    so a δ step of `app e a` is a δ step of `e` under a congruence — which
//!    cr3's own reduct premise covers. `appIC_whnf_inv` below uses that fact
//!    rather than head-freeness.
//! 2. **The ZERO rule is harmless.** `rhsZero mot m0 m1` β-collapses to the
//!    minor `m0`, a SUBTERM of a step-free `e`, hence itself step-free hence
//!    SN. What is NOT harmless is that the codomain candidate can then take one
//!    more argument: `PiSet` is a set of FUNCTIONS, so refuting membership only
//!    needs the applied term to diverge, and `m0` is free to be a lambda that
//!    self-applies. That is the whole counterexample.
//! 3. **`e` is step-free, so the rank is irrelevant.** R9's `EnvAcyclic` and
//!    the 127-entry rank table are true and are not consumed here: there is no
//!    δ anywhere in the counterexample. A rank induction cannot break a
//!    circularity that is not a circularity.
//!
//! ## B — the honest strongest form: `HeadInert`, and the const unlock
//!
//! Unrestricted cr3 is out. The right question is then how far the restriction
//! can be WIDENED, and the answer is: to exactly the terms whose head cannot
//! start an ι, keeping δ (which factors) and β (which cr3 already covers).
//! `HeadInert` is that predicate, as a two-constructor `Type`-valued inductive:
//!
//! ```text
//! | free  : HeadFree e -> HeadInert e
//! | inert : forall (n : Name) (e : KExpr),
//!             kexpr_const_name (kapp_fn e) = some n
//!          -> defval_for (red_def the_red_env) n = none
//!          -> recmeta_for  (red_rec the_red_env) n = none
//!          -> HeadInert e
//! ```
//!
//! It is HEREDITARY under application — `kapp_fn (app e a)` REDUCES to
//! `kapp_fn e`, so `headInert_app` rebuilds either constructor at the larger
//! term with its side conditions UNCHANGED — and it is STRICTLY weaker than
//! `HeadFree` (`r10_headInert_strictly_weaker`, at the real reflected `DefEnv`
//! constant, which is inert and is NOT head-free). One measured caveat, because
//! it cost this rung a cycle: `headInert_app` is NOT the identity the way R5's
//! `headFree_app` is. `HeadFree` is a `def` unfolding to an `Eq` about
//! `kapp_fn`, so `HeadFree e` and `HeadFree (app e a)` are literally the same
//! type; `HeadInert` is an inductive FAMILY indexed by the term, so they are
//! different types with definitionally identical contents and the transport has
//! to be applied. That is the single site where the weakened Pi-candidate proof
//! is not R5's text (`hi_weaken`'s first replacement). The payoff is exactly
//! R9's item 5:
//!
//! - `piSet_cr3HI` / `isCandHI_piSet` / `candInterp_isCandHI` — R5's Pi-candidate
//!   and interpretation at the widened face, derived by textual weakening of
//!   R5's own builders so the proofs cannot drift apart;
//! - `r10_deadConst_cand_mem` — a δ-dead, non-recursor constant is in EVERY
//!   `IsCandHI` candidate;
//! - `r10_interp_const_pi_witness : candInterp (pi (sort 0) (sort 0))
//!   (const fixture_def_env_name nil)` — **the ladder's first constant at a PI type.**
//!   R9 named that gap ("no rule reaches a const at a PI type at all") and
//!   attributed it to the head-free wall; the wall is real but it is narrower
//!   than head-freeness, and this is the part of it that lifts.
//!
//! And the widening is TIGHT, proved rather than hoped:
//! `r10_natRec3_not_headInert` shows every three-argument `Nat.rec` spine —
//! R5's exhibit (`r10_r5_term_excluded`) and this rung's counterexample alike —
//! is NOT `HeadInert`, by feeding the real `Nat.rec` ι fire to
//! `iota_step_no_recmeta_absurd`. So the counterexample sits exactly outside
//! the widened face, and A says nothing wider can be true.
//!
//! ## Honesty notes (read before quoting)
//!
//! - **Nothing here discharges `M : CandModel tenv`,** and this rung makes that
//!   MORE final rather than less: `CandModel.cr3` is the unrestricted face over
//!   the FULL `Neutral` predicate, and A refutes it for the Pi-candidate at the
//!   real env. That is a statement about `PiSet`, not about `CandModel.Red` —
//!   a `CandModel` instance is free to interpret `pi` by something other than
//!   `PiSet` — but every corpus construction and every rung of this ladder
//!   interprets it by `PiSet`, so the route those constructions take is closed.
//! - **The refutation is about the REAL environment.** `natRecZ_iota_fires` is
//!   R3's `Eq.refl` over `kernel_core_red_env`; `r10_zc_collapse` is an
//!   `Eq.refl` that makes the kernel evaluate the reflected `Nat.rec` zero-rule
//!   RHS applied to three concrete arguments. A regeneration of the reflection
//!   that changed that rule would fail those constants CLOSED.
//! - **`r10_beta_lam_head` reads a lambda's parts through `r10_lamTy` /
//!   `r10_lamBody` rather than hard-coding the reflected rule RHS.** The
//!   generated zero-rule RHS is `lam _ (lam _ (lam _ (bvar 1)))` — the second
//!   minor — but writing that spelling into the proof would pin the rung to a
//!   generated term. Projecting it instead means the kernel computes each β
//!   reduct and the chain stays correct under regeneration as long as the rule
//!   still returns a minor.
//! - **The counterexample needs the CODOMAIN to be a Pi-candidate.** With
//!   `CB := whnf_acc` the same `e` is harmless, because the zero-rule
//!   contractum of a step-free spine is SN. Anyone re-deriving this should not
//!   simplify `candInterp (pi (sort 0) (sort 0))` to `whnf_acc`.
//! - **Prop/Type discipline.** `HeadFree`, `Eq`, `delta_step` and `iota_step`
//!   are Prop; `HeadInert`, `IsCandHI`, `candCr3HI`, `Neutral`, `whnf_acc`,
//!   `candInterp T` and `Empty` are Type. `HeadInert` is a `Type`-valued
//!   inductive ON PURPOSE — a `Prop`-valued one could not eliminate into the
//!   `C : Type` of `appHI_whnf_inv`. `AndType (A : Type) (B : Type)` is
//!   `Type 0` and the kernel is NON-CUMULATIVE, which is why `HeadInert` is an
//!   inductive rather than a CPS `forall (C : Type), ...` disjunction: the
//!   latter is `Type 1` and would push `candCr3HI` out of `AndType`'s reach.
//! - **No `fixedIndicesToParams` promotion.** `HeadInert.free` leads with
//!   `(e : KExpr)` and `HeadInert.inert` leads with `(n : Name)`, so there is
//!   no uniform leading constructor-argument prefix and the measured 2026-08-23
//!   promotion cannot fire; the shape guard pins that `HeadInert.rec` is
//!   consumed with the two-binder `fun (ze : KExpr) (_ : HeadInert ze) => ...`
//!   motive, so a promotion would fail the rung loudly.
//! - **Every predicate R10 introduces in hypothesis position is WITNESSED
//!   here.** `HeadInert` by `r10_deadConst_headInert`, `IsCandHI` by
//!   `isCandHI_whnfAcc` and `candInterp_isCandHI`, `candCr3HI` by
//!   `piSet_cr3HI`. Constructors do not count on the supply side, which is why
//!   `r10_deadConst_headInert` is a registered definition and why the ladder
//!   guard `test_candmodel_ladder_premises_are_witnessed` names all three.
//! - **Non-degeneracy.** `r10_const_unlock_proper` pairs the new membership
//!   with R5's `candInterp_pi_not_total`: the constant IS in the Pi-candidate
//!   and `omegaLam` is NOT, so the unlock did not turn the interpretation into
//!   the total predicate.
//!
//! ## What still separates the judgment from `TypingCtx`, after this rung
//!
//! R9's list, with one item moved and one item hardened:
//!
//! 1. `TypingCtx.const` reads a DECLARED type off a `tenv` at ANY `A`. The
//!    ladder now reaches a const at a Pi type SEMANTICALLY
//!    (`r10_interp_const_pi_witness`) but only for δ-dead non-recursor names,
//!    and no `SynTyC`-style rule consumes it yet — wiring it into the judgment
//!    is R11's job, not a wall;
//! 2. `app` is NON-DEPENDENT and `lam` carries `SimpleTy A` (R5/R6, unchanged);
//! 3. the `let_` rule is the sort-annotated fragment only (R8, unchanged);
//! 4. no conversion rule, and `lam` has no `TypingCtx G A (sort u)` premise;
//! 5. **HARDENED**: the remaining const-at-Pi cases are the ones with a live
//!    recursor head or a live δ value. The δ half is R9's `konstDelta` and is
//!    vacuous over this env; the recursor half is the counterexample class of
//!    §A and is now known to be UNREACHABLE by cr3 in principle. Anything that
//!    wants it must supply ι-contractum membership from an ι-EXPANSION engine
//!    (R2/R3's `candExp_iota_natrec_zero` shape), never from cr3.
//!
//! ## Census
//!
//! ZERO new axioms: one genuine inductive via `add_inductive`, four plain defs
//! via `add_recursive_def`, everything else a value-bearing theorem via
//! `add_definition` with kernel `add_decl` checking. Census-neutral.

use std::collections::HashSet;

use super::candmodel_construct_r10_src::*;
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Register one value-bearing theorem (R6/R7/R8/R9's helper, verbatim).
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
    /// Register R10: the KEYSTONE settlement (unrestricted cr3 for `PiSet` is
    /// FALSE at the real reflected environment) plus the honest strongest cr3
    /// face `IsCandHI` over `HeadInert`, the interpretation at that face, and
    /// the const-at-a-Pi-type unlock it buys.
    ///
    /// MUST be registered AFTER `add_candmodel_construct_r9`
    /// (`whnfAcc_const_dead`, `r9_const_delta_dead`,
    /// `r9_const_headfree_absurd`), and therefore after R0-R8. Also requires
    /// `add_complete_development` (`iota_step_no_recmeta_absurd`),
    /// `add_par_reduces_iota_delta` (`delta_reduct_eq_none_of_defval_none`),
    /// `add_iota_step` (`recmeta_for`, `iota_reduct`), `add_delta_step`
    /// (`defval_for`, `delta_reduct`) and the generated `kernel_core_red_env`
    /// atoms (`fixture_def_env_name`, `fixture_nat_zero_name`, `fixture_nat_rec_name`,
    /// `kcre_witness_nat_zero_reduct`).
    pub(super) fn add_candmodel_construct_r10(&mut self) -> Result<(), SpecError> {
        // --- Group A: the two lambda projections and the settlement ---
        self.add_recursive_def(
            &src_r10_lam_ty(),
            "r10_lamTy e — the type annotation of a lambda, e itself at every other former. \
             Paired with r10_lamBody it lets r10_beta_lam_head fire a head beta at a term that \
             COMPUTES to a lambda without the proof ever naming that lambda's parts. That is \
             deliberate: the reflected Nat.rec zero-rule RHS is a generated term, and hard-coding \
             its three binders into the divergence chain would pin this rung to one regeneration \
             of the reflection. Value-bearing plain def; zero axioms.",
        )?;
        self.add_recursive_def(
            &src_r10_lam_body(),
            "r10_lamBody e — the body of a lambda, e itself at every other former. See r10_lamTy \
             for why the divergence chain projects rather than transcribes.",
        )?;
        add_thm(
            self,
            "r10_beta_lam_head",
            TY_R10_BETA_LAM_HEAD.to_string(),
            VAL_R10_BETA_LAM_HEAD.to_string(),
            &["beta_reduces", "r10_lamTy", "r10_lamBody", "instantiate"],
            "A head beta at a term that is PROPAGATED to be a lambda: given f = lam (r10_lamTy f) \
             (r10_lamBody f) — one Eq.refl whenever f whnf-computes to a lambda — the application \
             app f a beta-reduces to instantiate (r10_lamBody f) a, which the kernel then \
             computes. beta_reduces.beta transported along that equation. This is the tool that \
             makes the counterexample chain independent of the generated rule RHS's spelling. \
             Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r10_omegaLam_no_beta",
            TY_R10_OMEGALAM_NO_BETA.to_string(),
            val_r10_omegalam_no_beta(),
            &[
                "lamHead_beta_inv",
                "no_whnf_step_bvar",
                "r5_bvarApp_no_beta",
            ],
            "R5's looping lambda takes NO beta step, delivered to any continuation. The beta arm \
             of R5's own r5_whnfAcc_omegaLam, extracted as a standalone fact because the \
             counterexample needs it in an argument SLOT of a Nat.rec spine rather than at the \
             top. Both legs of lamHead_beta_inv die: the annotation is a bvar (no_whnf_step_bvar) \
             and the body is a bvar-headed application (r5_bvarApp_no_beta). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r10_stuckOmega_delta_none",
            ty_r10_stuckomega_delta_none(),
            VAL_R10_STUCKOMEGA_DELTA_NONE.to_string(),
            &["delta_reduct", "the_red_env"],
            "The counterexample's three-argument Nat.rec spine has NO delta reduct over the real \
             reflected environment — one Eq.refl, because fixture_nat_rec_name carries no definitional \
             value. R5's r5_natRecV3_delta_none at the omega-bearing argument list.",
        )?;
        add_thm(
            self,
            "r10_stuckOmega_no_whnf_step",
            ty_r10_stuckomega_no_whnf_step(),
            val_r10_stuckomega_no_whnf_step(),
            &[
                "constSpine3_beta_inv",
                "r10_omegaLam_no_beta",
                "no_whnf_step_bvar",
                "r10_stuckOmega_delta_none",
            ],
            "THE COUNTEREXAMPLE'S LOAD-BEARING FACT: Nat.rec (bvar 0) omegaLam (bvar 0) takes no \
             whnf_step AT ALL. That is what makes cr3's reduct premise satisfiable for free — it \
             is vacuous — so the refutation below cannot be answered with `your hypothesis was \
             unsatisfiable'. beta via constSpine3_beta_inv at the Nat.rec head with the three \
             iota-deadness side conditions by Eq.refl, the three argument slots killed by \
             no_whnf_step_bvar (slots 1 and 3) and r10_omegaLam_no_beta (slot 2); delta by \
             r10_stuckOmega_delta_none. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r10_natZero_whnfAcc",
            ty_r10_natzero_whnfacc(),
            VAL_R10_NATZERO_WHNFACC.to_string(),
            &["whnfAcc_const_dead"],
            "The real reflected Nat.zero constructor is strongly normalizing — R9's \
             whnfAcc_const_dead at fixture_nat_zero_name, whose defval lookup is one Eq.refl. This is what \
             puts the counterexample's argument in the domain candidate whnf_acc.",
        )?;
        add_thm(
            self,
            "r10_zc_collapse",
            ty_r10_zc_collapse(),
            VAL_R10_ZC_COLLAPSE.to_string(),
            &["instantiate", "r10_lamBody", "r5_omegaLam"],
            "COMPUTED, not assumed: three head betas of the REAL reflected Nat.rec zero rule, \
             applied to (bvar 0), omegaLam and (bvar 0), land exactly on omegaLam. One Eq.refl — \
             the kernel evaluates kapp_fn of the generated zero-rule reduct, projects three \
             lambda bodies and runs instantiate three times, and the lift/instantiate pair \
             introduced by the second step cancels. If a regeneration of the reflection changed \
             the zero rule to return anything but its second minor, this fails CLOSED.",
        )?;
        add_thm(
            self,
            "r10_appStuck_not_whnfAcc",
            ty_r10_appstuck_not_whnfacc(),
            val_r10_appstuck_not_whnfacc(),
            &[
                "whnfAcc_inv_step",
                "whnfStep_app_left",
                "natRecZ_iota_fires",
                "r10_beta_lam_head",
                "r10_zc_collapse",
                "r5_omegaV_not_whnfAcc",
            ],
            "THE DIVERGENCE: the stuck Nat.rec spine, applied to the real Nat.zero and then to \
             omegaLam, is NOT strongly normalizing. Five whnf_acc-preserving steps — one real \
             iota over the reflected environment (natRecZ_iota_fires) and three head betas of the \
             rule RHS, all lifted through whnfStep_app_left — reach app omegaLam omegaLam, which \
             loops (r5_omegaV_not_whnfAcc). Every intermediate is written as the kernel's own \
             computation, so the chain does not transcribe the generated rule. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r10_piSet_cr3_unrestricted_refuted",
            ty_r10_piset_cr3_unrestricted_refuted(),
            val_r10_piset_cr3_unrestricted_refuted(),
            &[
                "PiSet",
                "candCr3",
                "IsCandHF",
                "candStepInv",
                "candInterp",
                "r10_appStuck_not_whnfAcc",
                "r10_stuckOmega_no_whnf_step",
            ],
            "THE KEYSTONE, SETTLED: the UNRESTRICTED cr3 face of the Pi-candidate is FALSE at the \
             real reflected environment. R5 proved the head-free restriction NECESSARY for its \
             proof and left open whether the full law holds, suggesting it be supplied from \
             outside cr3 once the fundamental theorem gives SN of iota contracta. It cannot be: \
             instantiate CA := whnf_acc, CB := fun _ => candInterp (pi (sort 0) (sort 0)) — every \
             side condition isCandHF_piSet asks for holds (isCandHF_whnfAcc, \
             candInterp_isCandHF, candStepInv_const) — at the Neutral, STEP-FREE spine Nat.rec \
             (bvar 0) omegaLam (bvar 0), whose cr3 reduct premise is therefore vacuous, and the \
             conclusion fails because applying it to Nat.zero and then to omegaLam diverges. So \
             the missing SN of real-env iota contracta is not merely unavailable early in the \
             dependency order; it is NOT A THEOREM, and no stratification can supply it. Anything \
             wanting membership of an iota contractum must get it from an iota-EXPANSION engine \
             (R2/R3's candExp_iota_natrec_zero shape), never from cr3. HONESTY: this refutes the \
             law for PiSet, the interpretation every corpus construction and every rung of this \
             ladder uses for pi; it is not a claim about an arbitrary CandModel.Red. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "r10_isCandSet_piSet_refuted",
            ty_r10_iscandset_piset_refuted(),
            val_r10_iscandset_piset_refuted(),
            &[
                "IsCandSet",
                "isCandSet_cr3",
                "r10_piSet_cr3_unrestricted_refuted",
            ],
            "The keystone at the packaged interface: the Pi-candidate is never an IsCandSet under \
             the hypotheses that make it an IsCandHF. Immediate from the cr3 refutation through \
             isCandSet_cr3, registered separately because that is the spelling R5's isCandHF_piSet \
             would have carried if the head-free premise could have been dropped.",
        )?;
        add_thm(
            self,
            "r10_cr3_gap_is_real",
            ty_r10_cr3_gap_is_real(),
            val_r10_cr3_gap_is_real(),
            &["r10_stuckOmega_no_whnf_step", "r10_appStuck_not_whnfAcc"],
            "The three measured facts of the counterexample in one kernel-checked constant, the \
             sharpening of R5's piSet_cr3_headFree_necessary: the domain member is SN, the neutral \
             is STEP-FREE (so cr3's premise carries no information and costs nothing to supply), \
             and the applied term is NOT SN. R5's exhibit stopped at `the iota fires'; this one \
             says the fire is FATAL, which is the difference between a gap and a refutation.",
        )?;

        // --- Group B: the honest strongest cr3 face ---
        self.add_inductive(
            &src_head_inert(),
            "HeadInert e — the widest restriction under which cr3 for the Pi-candidate survives: \
             the head of e cannot start an iota. Two constructors — e is head-free (R5's \
             restriction), or its spine head is a constant that is neither delta-defined nor a \
             recursor in the real reflected environment. HEREDITARY under application for the same \
             definitional reason head-freeness is, kapp_fn (app e a) reducing to kapp_fn e, so \
             every side condition transports by Eq.refl (headInert_app). Type-valued ON PURPOSE: \
             a Prop-valued inductive could not eliminate into the C : Type of appHI_whnf_inv, and \
             a CPS forall (C : Type) disjunction would be Type 1 and push candCr3HI out of \
             AndType's non-cumulative Type 0. No fixedIndicesToParams promotion: free leads with \
             (e : KExpr) and inert with (n : Name), so there is no uniform leading prefix. \
             Non-vacuous by r10_deadConst_headInert at a REAL reflected name.",
        )?;
        add_thm(
            self,
            "headInert_app",
            TY_HEADINERT_APP.to_string(),
            val_headinert_app(),
            &["HeadInert", "HeadFree"],
            "Head-inertness passes through application, which is what lets the Pi-candidate's cr3 \
             apply the codomain candidate's cr3 at app e a. Both constructors rebuild at the \
             larger term with their side conditions UNCHANGED — kapp_fn (app ze a) reduces to \
             kapp_fn ze, so HeadFree ze and the head-name equation are definitionally the ones \
             needed. Consumed with the two-binder HeadInert.rec motive, which is the shape guard's \
             promotion tripwire.",
        )?;
        add_thm(
            self,
            "headFree_headInert",
            TY_HEADFREE_HEADINERT.to_string(),
            VAL_HEADFREE_HEADINERT.to_string(),
            &["HeadInert", "HeadFree"],
            "R5's restriction is a special case of R10's, so every head-free use in R1/R5 keeps \
             working at the new interface and isCandHI_weaken can hand an IsCandHI back as an \
             IsCandHF.",
        )?;
        add_thm(
            self,
            "inertConst_headInert",
            ty_inertconst_headinert(),
            val_inertconst_headinert(),
            &["HeadInert", "defval_for", "recmeta_for", "the_red_env"],
            "A BARE CONSTANT is head-inert whenever the real environment gives it no definitional \
             value and no recursor metadata — the head-name side condition is Eq.refl. This is \
             precisely the case R9's r9_const_obstruction_located showed head-freeness rejects, \
             and it is the entry point of the const unlock below.",
        )?;
        add_thm(
            self,
            "appIC_beta_inv",
            ty_appic_beta_inv(),
            val_appic_beta_inv(),
            &["beta_reduces", "iota_step_no_recmeta_absurd"],
            "R5's appHF_beta_inv at an INERT CONST head instead of a head-free one: the 15-arm \
             beta_reduces inversion of app e a, delivering the same three continuations (head \
             lambda / step in the function / step in the argument). Exactly one arm differs — the \
             iota leg, which head-freeness killed by the head having no const name and which here \
             dies on that const having no recursor metadata (iota_step_no_recmeta_absurd). The \
             continuation types are rebuilt from R5's own type by textual splice, and the shape \
             guard pins that they still agree.",
        )?;
        add_thm(
            self,
            "appIC_whnf_inv",
            ty_appic_whnf_inv(),
            val_appic_whnf_inv(),
            &["appIC_beta_inv", "delta_reduct_eq_none_of_defval_none"],
            "The whnf_step inversion at an inert const head. beta via appIC_beta_inv; the DELTA \
             leg dies on the head const having no definitional value \
             (delta_reduct_eq_none_of_defval_none). Worth recording why delta needed a side \
             condition at all: R5's deltaReduct_app_gen already shows a delta step of app e a is a \
             delta step of e under a congruence, so the general Pi-candidate proof could route it \
             through cr3's own reduct premise — the inert branch takes the cheaper route because \
             it has the hypothesis in hand.",
        )?;
        add_thm(
            self,
            "appHI_whnf_inv",
            ty_apphi_whnf_inv(),
            val_apphi_whnf_inv(),
            &["HeadInert", "appHF_whnf_inv", "appIC_whnf_inv"],
            "THE UNIFIED INVERSION: every whnf_step of app e a, for HeadInert e, is a head beta, a \
             step in e, or a step in a. Dispatches HeadInert.rec to R5's head-free inversion or to \
             the inert-const one. Its type is R5's ty_apphf_whnf_inv with the single premise \
             swapped, built by textual replacement so the continuation shapes cannot drift and \
             piSet_cr3HI_aux can be R5's proof weakened verbatim.",
        )?;
        self.add_recursive_def(
            &src_cand_cr3hi(),
            "candCr3HI S — cr3 at the head-inert restriction. R5's candCr3HF with HeadFree \
             replaced by HeadInert, which is STRICTLY weaker (r10_headInert_strictly_weaker), so \
             this is a STRICTLY STRONGER demand on S. It is also the strongest one available: \
             r10_piSet_cr3_unrestricted_refuted refutes the unrestricted face and \
             r10_natRec3_not_headInert shows the refuting term sits exactly outside this one.",
        )?;
        self.add_recursive_def(
            &src_is_cand_hi(),
            "IsCandHI S — the candidate interface at the head-inert cr3 face: cr1 and cr2 \
             unrestricted (as R5 has them) and cr3 over every head-inert neutral. Packaged with \
             AndType exactly as IsCandSet and IsCandHF are.",
        )?;
        for (name, ty, val, deps, desc) in [
            (
                "isCandHI_intro",
                ty_iscandhi_intro(),
                val_iscandhi_intro(),
                vec!["IsCandHI", "AndType"],
                "Introduce the head-inert candidate interface from its three faces.",
            ),
            (
                "isCandHI_cr1",
                ty_iscandhi_cr1(),
                val_iscandhi_cr1(),
                vec!["IsCandHI"],
                "cr1 projection: members of a head-inert candidate are strongly normalizing.",
            ),
            (
                "isCandHI_cr2",
                ty_iscandhi_cr2(),
                val_iscandhi_cr2(),
                vec!["IsCandHI"],
                "cr2 projection: head-inert candidates are closed under whnf_step.",
            ),
            (
                "isCandHI_cr3",
                ty_iscandhi_cr3(),
                val_iscandhi_cr3(),
                vec!["IsCandHI", "HeadInert"],
                "cr3 projection at the widened restriction — the face this rung exists to widen.",
            ),
        ] {
            add_thm(self, name, ty, val, &deps, desc)?;
        }
        add_thm(
            self,
            "isCandHI_weaken",
            TY_ISCANDHI_WEAKEN.to_string(),
            VAL_ISCANDHI_WEAKEN.to_string(),
            &["IsCandHI", "IsCandHF", "headFree_headInert"],
            "Every head-inert candidate is a head-free candidate, so R5's engines (candExpHF_beta, \
             piSet_cr1, piSet_cr2, candInterp_lam) apply unchanged and R10 re-derives nothing they \
             already prove.",
        )?;
        add_thm(
            self,
            "isCandSet_weakenHI",
            TY_ISCANDSET_WEAKENHI.to_string(),
            VAL_ISCANDSET_WEAKENHI.to_string(),
            &["IsCandSet", "IsCandHI"],
            "A candidate satisfying the UNRESTRICTED cr3 satisfies the head-inert one — the \
             direction that is free. The converse is exactly what this rung refutes for the \
             Pi-candidate.",
        )?;
        add_thm(
            self,
            "isCandHI_whnfAcc",
            TY_ISCANDHI_WHNFACC.to_string(),
            VAL_ISCANDHI_WHNFACC.to_string(),
            &["isCandSet_weakenHI", "isCand_whnfAcc"],
            "The top candidate at the head-inert interface, and the unconditional witness that \
             IsCandHI is inhabited (the premise gate's supply side).",
        )?;
        add_thm(
            self,
            "piSet_cr3HI_aux",
            ty_piset_cr3hi_aux(),
            val_piset_cr3hi_aux(),
            &["PiSet", "HeadInert", "appHI_whnf_inv", "isCandHI_cr3"],
            "The inner Acc induction of the Pi-candidate's cr3 at the WIDENED restriction, derived \
             by textual weakening of R5's piSet_cr3_aux rather than retyped: HeadFree becomes \
             HeadInert, isCandHF_* becomes isCandHI_*, appHF_whnf_inv becomes appHI_whnf_inv — and \
             exactly ONE site is not textual. R5 hands hhf straight to the codomain candidate's \
             cr3 at app e qa0, because HeadFree unfolds to an Eq about kapp_fn and so HeadFree e \
             and HeadFree (app e qa0) are the SAME type; HeadInert is an inductive family indexed \
             by the term, so the transport headInert_app is genuinely applied there (measured \
             2026-08-27: without it the elaborator refuses with expected HeadInert (KExpr.app _ \
             _), Discriminant(1) vs Discriminant(4)). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "piSet_cr3HI",
            ty_piset_cr3hi(),
            val_piset_cr3hi(),
            &["piSet_cr3HI_aux", "isCandHI_cr1", "candCr3HI"],
            "cr3 for the Pi-candidate at the head-inert restriction — THE honest strongest form. \
             r10_piSet_cr3_unrestricted_refuted says the restriction cannot be dropped and \
             r10_natRec3_not_headInert says this is where the boundary falls.",
        )?;
        add_thm(
            self,
            "isCandHI_piSet",
            TY_ISCANDHI_PISET.to_string(),
            VAL_ISCANDHI_PISET.to_string(),
            &["isCandHI_intro", "piSet_cr1", "piSet_cr2", "piSet_cr3HI"],
            "The Pi-candidate is a head-inert candidate. cr1 and cr2 are R5's, applied through \
             isCandHI_weaken (they never touch cr3); cr3 is the widened face.",
        )?;
        add_thm(
            self,
            "candInterp_isCandHI",
            ty_candinterp_iscandhi(),
            val_candinterp_iscandhi(),
            &[
                "candInterp",
                "IsCandHI",
                "isCandHI_piSet",
                "isCandHI_whnfAcc",
            ],
            "R5's interpretation is a candidate at EVERY untyped type under the widened cr3 face. \
             Same KExpr.rec as candInterp_isCandHF, textually weakened, so the two cannot drift. \
             This is what makes the const unlock reach a PI-typed slot.",
        )?;

        // --- Group C: the unlock, the tightness proof, the witnesses ---
        add_thm(
            self,
            "r10_deadConst_headInert",
            ty_r10_deadconst_headinert(),
            VAL_R10_DEADCONST_HEADINERT.to_string(),
            &["HeadInert", "inertConst_headInert"],
            "A REAL reflected kernel constant is head-inert: fixture_def_env_name (the inductive type \
             DefEnv), whose defval and recmeta lookups over the real environment are both one \
             Eq.refl. The premise gate's unconditional supply for HeadInert, and the entry point \
             of the unlock.",
        )?;
        add_thm(
            self,
            "r10_deadConst_cand_mem",
            ty_r10_deadconst_cand_mem(),
            val_r10_deadconst_cand_mem(),
            &[
                "isCandHI_cr3",
                "inertConst_headInert",
                "constRedex_whnf_inv",
                "r9_const_delta_dead",
            ],
            "A delta-dead, non-recursor constant is in EVERY head-inert candidate. cr3 applies \
             because the constant is head-inert and Neutral, and its reduct premise is vacuous \
             because R2's constRedex_whnf_inv shows a bare const's only possible whnf_step is a \
             delta step, which r9_const_delta_dead refutes. This is the general form of what R9 \
             could only get at a SORT-typed slot.",
        )?;
        add_thm(
            self,
            "r10_interp_const_pi_witness",
            ty_r10_interp_const_pi_witness(),
            val_r10_interp_const_pi_witness(),
            &["candInterp", "r10_deadConst_cand_mem", "candInterp_isCandHI"],
            "THE UNLOCK: a REAL reflected constant in the PI-typed candidate candInterp (pi (sort \
             0) (sort 0)). R9 named this the ladder's newest gap — `no rule reaches a const at a PI \
             type at all' — and attributed it to R5's head-free wall. The wall is real, but it is \
             NARROWER than head-freeness: what cr3 cannot introduce is a head that can start an \
             iota, and a constant that is not a recursor cannot. Semantic membership only; wiring \
             it into a SynTyC-style rule is a later rung.",
        )?;
        add_thm(
            self,
            "r10_headInert_strictly_weaker",
            ty_r10_headinert_strictly_weaker(),
            val_r10_headinert_strictly_weaker(),
            &["HeadInert", "HeadFree", "r9_const_headfree_absurd"],
            "The widening is REAL, not a renaming: the same real reflected constant is head-inert \
             and is NOT head-free. Without this pair, IsCandHI could have been IsCandHF under \
             another name and the unlock would have been circular.",
        )?;
        add_thm(
            self,
            "r10_natRec3_not_headInert",
            ty_r10_natrec3_not_headinert(),
            val_r10_natrec3_not_headinert(),
            &[
                "HeadInert",
                "iota_step_no_recmeta_absurd",
                "natRecZ_iota_fires",
            ],
            "TIGHTNESS: no three-argument Nat.rec spine is head-inert, at ANY arguments. The \
             head-free branch dies because the head IS a const; the inert branch dies because \
             that const has recursor metadata — proved without naming the metadata, by feeding \
             the REAL zero-rule iota fire (natRecZ_iota_fires) to iota_step_no_recmeta_absurd. So \
             the term that refutes unrestricted cr3 sits exactly outside the widened face, and the \
             boundary between what cr3 can and cannot introduce is drawn at the right place.",
        )?;
        add_thm(
            self,
            "r10_r5_term_excluded",
            ty_r10_r5_term_excluded(),
            val_r10_r5_term_excluded(),
            &["r10_natRec3_not_headInert"],
            "R5's own exhibit — Nat.rec (bvar 0) (bvar 0) (bvar 0), the term \
             piSet_cr3_headFree_necessary is stated over — is excluded by the widened restriction \
             too. Registered at that exact term because it is the one whose iota fire made the \
             original restriction necessary.",
        )?;
        add_thm(
            self,
            "r10_counterexample_excluded",
            ty_r10_counterexample_excluded(),
            val_r10_counterexample_excluded(),
            &["r10_natRec3_not_headInert"],
            "And so is this rung's refuting term. Together with piSet_cr3HI that is the complete \
             picture: cr3 holds at every head-inert neutral, the counterexample is not one, and \
             nothing between the two is available.",
        )?;
        add_thm(
            self,
            "r10_const_unlock_proper",
            ty_r10_const_unlock_proper(),
            val_r10_const_unlock_proper(),
            &["r10_interp_const_pi_witness", "candInterp_pi_not_total"],
            "NON-DEGENERACY of the unlock, the micro_has_type trap guard: the real reflected \
             constant IS in candInterp (pi (sort 0) (sort 0)) and R5's omegaLam is still NOT, so \
             admitting constants did not collapse the Pi interpretation into the total predicate.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r10_tests.rs"]
mod tests;
