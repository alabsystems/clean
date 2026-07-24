// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment F+++ (#2859 computational-iota/delta track): the `topIotaStar`
//! head-iota developer port from the VERIFIED app-spine blueprint
//! (`scratch/confluence-proof/AppSpine_confluence_PROVEN.lean`), targeting the
//! `par_reduces_p` DIAMOND (the corrected confluence route — see
//! `scratch/CONFLUENCE_REDIRECT_2026-06-27.md`).
//!
//! ## What the blueprint's `topIotaStar` is, and why it collapses here
//!
//! In the blueprint, `topIotaStar` fires the *entire top-level iota redex CHAIN*
//! of a term: `e ↦ᵢ r1 ↦ᵢ r2 ↦ ⋯`. It is structurally terminating in the toy
//! because the toy recursor has FIXED arity with two hard-coded rules whose
//! reducts have the subterm-decrease property (`zero` ↦ the bound premise `z`, a
//! strict subterm; the `succ` contractum is provably never itself a top redex).
//!
//! Clean's `KExpr` recursor is a CONST-headed app-spine of VARIABLE arity, and
//! its iota reduct is
//!   `apply_spine extras (apply_spine fields (apply_spine prefix (recrule_rhs rule)))`
//! — NOT a structural subterm of the input (it is built from the OPAQUE
//! environment `recrule_rhs`). So the blueprint's structural recursion on the
//! reduct does not port, and no uniform fuel bounds the chain.
//!
//! KEY FAITHFULNESS FACT (this module): in a well-formed kernel env an iota reduct
//! is *never itself a top iota redex*. The reduct's head is `kapp_fn (recrule_rhs
//! rule)`, which for a real recursor rule is the closed binder template — so
//! `kexpr_const_name` of it is `none` and `iota_reduct` short-circuits. Captured
//! as `RecEnvReductNotRedex env` (a HYPOTHESIS carried through, NOT an axiom — the
//! mirror of `RecEnvClosed` / `RecEnvCtorRecDisjoint`; its kernel-env witness is
//! discharged end-of-track). Given it, the head-iota CHAIN has length ≤ 1, so
//! `topIotaStar` collapses to a SINGLE head-iota fire
//!   `topIotaStar env t := opt_default (iota_reduct env t) t`
//! and the blueprint's `topIotaStar`/`topIotaStar_no_redex`/`topIotaStar_step`
//! port directly. `par_topIotaStar` (every `par_reduces_p`-reduct of `e` reduces
//! one further step to `topIotaStar` of it, via `iota_p`) needs no interface at
//! all.
//!
//! These are the chain-absorber bricks the open `iota_p` arm of `cd_triangle`
//! (the "whole-app-reduces-then-fires" / over-application wall,
//! `complete_development.rs`) consumes. STOP point per the confluence redirect:
//! the single-step `par_diamond` and Tait–Martin-Löf lift are later stages.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The faithful fact carried by `RecEnvReductNotRedex env`: an iota reduct is
/// never itself a top iota redex. If `iota_reduct env e = some r` (so `e` is a
/// redex with reduct `r`), then `iota_reduct env r = none` (`r` is not a redex).
/// True for the kernel env because the reduct's head is the recursor rule's
/// (binder-headed) `recrule_rhs`, on which `iota_reduct` short-circuits at the
/// `kexpr_const_name` lookup. The fact that collapses the blueprint's head-iota
/// CHAIN to a single fire (so `topIotaStar = opt_default ∘ iota_reduct`).
const REDUCT_NOT_REDEX_FACT: &str = concat!(
    "forall (e : KExpr) (r : KExpr), ",
    "Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr r) -> ",
    "Eq (OptionType KExpr) (iota_reduct env r) (OptionType.none KExpr)"
);

impl Specification {
    pub(super) fn add_par_reduces_p_topdev(&mut self) -> Result<(), SpecError> {
        // topIotaStar env t: fire the top head-iota of t if present, else t. The
        // single-fire collapse of the blueprint's head-iota chain firer (valid
        // under RecEnvReductNotRedex — the reduct is never a top redex, so the
        // chain has length <= 1). opt_default (iota_reduct env t) t: some r -> r
        // (the reduct), none -> t (no top redex).
        self.add_recursive_def(
            r"def topIotaStar (env : RecEnv) (t : KExpr) : KExpr := opt_default (iota_reduct env t) t",
            "topIotaStar env t = the top head-iota fire of t (opt_default (iota_reduct env t) t): the reduct \
             if t is a top iota redex, else t. The blueprint's head-iota chain firer, collapsed to a SINGLE \
             fire — valid under RecEnvReductNotRedex (an iota reduct is never itself a top redex, so the chain \
             has length <= 1). Part of #2859 (Increment F+++, topIotaStar port).",
        )?;

        // RecEnvReductNotRedex env: the reduct-not-redex faithful interface. A real
        // inductive (proper recursor, NOT an axiom), mirror of RecEnvClosed. Its
        // witness for the kernel env is discharged at the end of the track (the
        // reduct's head is the binder-headed recrule_rhs).
        self.add_inductive(
            &format!(
                "inductive RecEnvReductNotRedex (env : RecEnv) : Type\n| mk : ({REDUCT_NOT_REDEX_FACT}) → RecEnvReductNotRedex env"
            ),
            "Reduct-not-redex interface for a recursor environment: an iota reduct is never itself a top iota \
             redex — iota_reduct env e = some r implies iota_reduct env r = none. A defined hypothesis (NOT an \
             axiom); its witness for the kernel env is discharged at the end of the track (the reduct's head is \
             the binder-headed recrule_rhs, so iota_reduct short-circuits). Collapses the blueprint's head-iota \
             chain to a single fire — topIotaStar_no_redex / topIotaStar_step consume its projector. Part of \
             #2859 (Increment F+++, topIotaStar port).",
        )?;

        // recenv_reduct_not_redex_fact: the projector. Given the env is reduct-not-
        // redex and e fired to r, r is not a redex. Mirror of recenv_closed_rhs.
        self.add_definition(SpecDefinition {
            name: "recenv_reduct_not_redex_fact".to_string(),
            type_src: "forall (env : RecEnv) (e : KExpr) (r : KExpr), \
                 RecEnvReductNotRedex env -> \
                 Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr r) -> \
                 Eq (OptionType KExpr) (iota_reduct env r) (OptionType.none KExpr)"
                .to_string(),
            value_src: Some(format!(
                "fun (env : RecEnv) (e : KExpr) (r : KExpr) \
                 (w : RecEnvReductNotRedex env) \
                 (heq : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr r)) => \
                 RecEnvReductNotRedex.rec env \
                 (fun (_ : RecEnvReductNotRedex env) => \
                 Eq (OptionType KExpr) (iota_reduct env r) (OptionType.none KExpr)) \
                 (fun (hc : {REDUCT_NOT_REDEX_FACT}) => hc e r heq) \
                 w"
            )),
            is_axiom: false,
            description: concat!(
                "Projector for RecEnvReductNotRedex: in a reduct-not-redex environment, the reduct r of a fired ",
                "redex e (iota_reduct env e = some r) is not itself a redex (iota_reduct env r = none). Projects ",
                "the single fact via RecEnvReductNotRedex.rec and applies it to the fire witness. Mirror of ",
                "recenv_closed_rhs. DerivedProved; zero axiom_deps. Part of #2859 (Increment F+++)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvReductNotRedex".to_string(),
                "RecEnvReductNotRedex.rec".to_string(),
                "iota_reduct".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_topIotaStar: every par_reduces_p-reduct of e reduces one further step
        // to topIotaStar of it. Blueprint par_topIotaStar (single-fire form). Convoy
        // on iota_reduct env t: none -> topIotaStar t = t, return h; some r ->
        // topIotaStar t = r, fire via par_reduces_p.iota_p (h : e =>_p t, gate eqn :
        // iota_step env t r). No interface needed.
        self.add_definition(SpecDefinition {
            name: "par_topIotaStar".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (t : KExpr), ",
                "par_reduces_p env e t -> par_reduces_p env e (topIotaStar env t)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (t : KExpr) (h : par_reduces_p env e t) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (iota_reduct env t) o -> ",
                    "par_reduces_p env e (opt_default o t)) ",
                    // none arm: opt_default none t = t, return h
                    "(fun (_eqn : Eq (OptionType KExpr) (iota_reduct env t) (OptionType.none KExpr)) => h) ",
                    // some arm: opt_default (some r) t = r, fire iota_p
                    "(fun (r : KExpr) (eqn : Eq (OptionType KExpr) (iota_reduct env t) (OptionType.some KExpr r)) => ",
                    "par_reduces_p.iota_p env e t r h eqn) ",
                    "(iota_reduct env t) ",
                    "(Eq.refl (OptionType KExpr) (iota_reduct env t))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "par_topIotaStar: par_reduces_p env e t -> par_reduces_p env e (topIotaStar env t) — every ",
                "par_reduces_p-reduct of e reduces one further step to the top head-iota fire of it. Convoy ",
                "(OptionType.rec) on iota_reduct env t: the none arm keeps t (h), the some-r arm fires the top ",
                "iota via par_reduces_p.iota_p (h is the reduced premise, the convoy witness is the iota_step ",
                "gate). The blueprint's par_topIotaStar (single-fire form); no interface needed. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment F+++, topIotaStar port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "topIotaStar".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "iota_step".to_string(),
                "par_reduces_p".to_string(),
                "par_reduces_p.iota_p".to_string(),
                "OptionType.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // topIotaStar_no_redex: topIotaStar env t is never a top iota redex. Convoy
        // on iota_reduct env t: none -> topIotaStar t = t, goal = the convoy eqn;
        // some r -> topIotaStar t = r, goal iota_reduct env r = none from the
        // interface (recenv_reduct_not_redex_fact). Blueprint topIotaStar_no_redex.
        self.add_definition(SpecDefinition {
            name: "topIotaStar_no_redex".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (t : KExpr), ",
                "RecEnvReductNotRedex env -> ",
                "Eq (OptionType KExpr) (iota_reduct env (topIotaStar env t)) (OptionType.none KExpr)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (t : KExpr) (w : RecEnvReductNotRedex env) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (iota_reduct env t) o -> ",
                    "Eq (OptionType KExpr) (iota_reduct env (opt_default o t)) (OptionType.none KExpr)) ",
                    // none arm: opt_default none t = t, goal iota_reduct env t = none = eqn
                    "(fun (eqn : Eq (OptionType KExpr) (iota_reduct env t) (OptionType.none KExpr)) => eqn) ",
                    // some arm: opt_default (some r) t = r, goal iota_reduct env r = none from interface
                    "(fun (r : KExpr) (eqn : Eq (OptionType KExpr) (iota_reduct env t) (OptionType.some KExpr r)) => ",
                    "recenv_reduct_not_redex_fact env t r w eqn) ",
                    "(iota_reduct env t) ",
                    "(Eq.refl (OptionType KExpr) (iota_reduct env t))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "topIotaStar_no_redex: in a reduct-not-redex env, topIotaStar env t is never a top iota redex ",
                "(iota_reduct env (topIotaStar env t) = none). Convoy on iota_reduct env t: the none arm leaves ",
                "t (the convoy eqn IS the goal), the some-r arm leaves the reduct r whose non-redex status is ",
                "recenv_reduct_not_redex_fact. The blueprint's topIotaStar_no_redex (idempotence base). ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F+++, topIotaStar port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "topIotaStar".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "recenv_reduct_not_redex_fact".to_string(),
                "OptionType.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // topIotaStar_step: firing the head iota of e3 (iota_step env e3 t) does not
        // change topIotaStar: topIotaStar env e3 = topIotaStar env t. e3 is a redex
        // (reduct t), so topIotaStar env e3 = t; t is not a redex (interface), so
        // topIotaStar env t = t. The cascade absorber. Blueprint topIotaStar_step.
        self.add_definition(SpecDefinition {
            name: "topIotaStar_step".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e3 : KExpr) (t : KExpr), ",
                "RecEnvReductNotRedex env -> ",
                "iota_step env e3 t -> ",
                "Eq KExpr (topIotaStar env e3) (topIotaStar env t)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e3 : KExpr) (t : KExpr) (w : RecEnvReductNotRedex env) ",
                    "(hi : iota_step env e3 t) => ",
                    // step1 : topIotaStar e3 (= opt_default (iota_reduct e3) e3) = t
                    //   via cong (fun o => opt_default o e3) on hi : iota_reduct e3 = some t
                    //   (RHS opt_default (some t) e3 reduces to t).
                    "Eq.trans KExpr (topIotaStar env e3) t (topIotaStar env t) ",
                    "(Eq.cong (OptionType KExpr) KExpr ",
                    "(fun (o : OptionType KExpr) => opt_default o e3) ",
                    "(iota_reduct env e3) (OptionType.some KExpr t) hi) ",
                    // step2 : t (= opt_default none t) = topIotaStar t (= opt_default (iota_reduct t) t)
                    //   via cong (fun o => opt_default o t) on (symm of) the interface fact
                    //   recenv_reduct_not_redex_fact env e3 t w hi : iota_reduct t = none.
                    "(Eq.cong (OptionType KExpr) KExpr ",
                    "(fun (o : OptionType KExpr) => opt_default o t) ",
                    "(OptionType.none KExpr) (iota_reduct env t) ",
                    "(Eq.symm (OptionType KExpr) (iota_reduct env t) (OptionType.none KExpr) ",
                    "(recenv_reduct_not_redex_fact env e3 t w hi)))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "topIotaStar_step (the cascade absorber): in a reduct-not-redex env, firing the head iota of e3 ",
                "(iota_step env e3 t) leaves topIotaStar unchanged — topIotaStar env e3 = topIotaStar env t. e3 ",
                "is a redex with reduct t (so topIotaStar env e3 fires to t), and t is not a redex (interface, so ",
                "topIotaStar env t = t); both sides equal t, joined by Eq.trans of two opt_default congruences. ",
                "The blueprint's topIotaStar_step — the off-by-one chain absorber the iota_p arm of cd_triangle ",
                "needs. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+++, topIotaStar port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "topIotaStar".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "iota_step".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "recenv_reduct_not_redex_fact".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // topIotaStar_fix: if t is not a top iota redex (iota_reduct env t = none),
        // topIotaStar leaves it unchanged: topIotaStar env t = t. The idempotence base
        // (blueprint topIotaStar_fix). topIotaStar env t = opt_default (iota_reduct env t)
        // t; Eq.cong (fun o => opt_default o t) over the none-equation yields
        // opt_default none t = t (defeq). No interface needed.
        self.add_definition(SpecDefinition {
            name: "topIotaStar_fix".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (t : KExpr), ",
                "Eq (OptionType KExpr) (iota_reduct env t) (OptionType.none KExpr) -> ",
                "Eq KExpr (topIotaStar env t) t"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (t : KExpr) ",
                    "(h : Eq (OptionType KExpr) (iota_reduct env t) (OptionType.none KExpr)) => ",
                    "Eq.cong (OptionType KExpr) KExpr ",
                    "(fun (o : OptionType KExpr) => opt_default o t) ",
                    "(iota_reduct env t) (OptionType.none KExpr) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "topIotaStar_fix: if iota_reduct env t = none (t is not a top iota redex), topIotaStar leaves t ",
                "unchanged — topIotaStar env t = t. topIotaStar env t = opt_default (iota_reduct env t) t (defeq); ",
                "Eq.cong (fun o => opt_default o t) over the none-equation gives opt_default none t, which is t by ",
                "opt_default's none branch (defeq). The blueprint's topIotaStar_fix (idempotence base for ",
                "topIotaStar_dev). DerivedProved, zero axiom_deps. Part of #2859 (Increment F+++, topIotaStar port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "topIotaStar".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_dev_developer()?;
        self.add_par_reduces_p_confluence()?;

        Ok(())
    }

    /// The Tait–Martin-Löf lift of the strong single-step diamond `par_diamond`
    /// to full Church–Rosser confluence of `par_reduces_c_star`. Three bricks
    /// (mirroring the iota-free BD template `par_strips_bd_star_strip` /
    /// `par_reduces_bd_star_diamond`) plus the two star-level sandwich bridges:
    ///
    ///   1. `par_strips_p_star_strip` — tile `par_diamond` down one
    ///      `par_reduces_p_star` leg (the STRIP lemma).
    ///   2. `par_reduces_p_star_diamond` — confluence of `par_reduces_p_star`
    ///      (induction on the first star leg, strip each head step via (1)).
    ///   3. `par_reduces_c_star_diamond` — confluence of `par_reduces_c_star`
    ///      via the sandwich `par_reduces_c_star ⊆ par_reduces_p_star ⊆
    ///      par_reduces_c_star`. This is the result that makes `church_rosser_whnf`
    ///      deletable.
    ///
    /// The four faithful interfaces (`RecEnvReductNotRedex` / `RecEnvCtorNoRecMeta`
    /// / `RecEnvClosed` / `RecEnvLiftClosed`) are carried as HYPOTHESES throughout —
    /// they are discharged for the kernel env at the capstone, not here. All bricks
    /// are DerivedProved (closed, kernel-checked terms), zero axiom_deps. Part of
    /// #2859 (Increment F+++, Tait–Martin-Löf lift to CR).
    fn add_par_reduces_p_confluence(&mut self) -> Result<(), SpecError> {
        // par_reduces_c_star_subsumes_par_p_star: lift par_reduces_c_subsumes_par_p
        // over the RT-closure. Induction on the par_reduces_c_star derivation,
        // prefixing each subsumed single step via par_reduces_p_star.step.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_subsumes_par_p_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_c_star env e e' -> par_reduces_p_star env e e'"
            )
            .to_string(),
            value_src: Some(par_reduces_c_star_subsumes_par_p_star_proof()),
            is_axiom: false,
            description: concat!(
                "Star-level embedding par_reduces_c_star ⊆ par_reduces_p_star: lift the single-step ",
                "embedding par_reduces_c_subsumes_par_p over the reflexive-transitive closure. ",
                "par_reduces_c_star.rec on the first chain — the refl arm is par_reduces_p_star.refl, ",
                "the step arm prefixes the subsumed single step (par_reduces_c_subsumes_par_p) onto the ",
                "IH via par_reduces_p_star.step. The forward half of the star-level sandwich the ",
                "par_reduces_c_star diamond rides on. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment F+++, Tait–Martin-Löf lift)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star.refl".to_string(),
                "par_reduces_p_star.step".to_string(),
                "par_reduces_c_subsumes_par_p".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_star_subsumes_par_c_star: lift par_reduces_p_subsumes_par_c_star
        // (single p step -> c star) over the RT-closure. Induction on the
        // par_reduces_p_star derivation, gluing each step's c-star with the IH via
        // par_reduces_c_star_trans.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_star_subsumes_par_c_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_p_star env e e' -> par_reduces_c_star env e e'"
            )
            .to_string(),
            value_src: Some(par_reduces_p_star_subsumes_par_c_star_proof()),
            is_axiom: false,
            description: concat!(
                "Star-level embedding par_reduces_p_star ⊆ par_reduces_c_star: lift the single-step ",
                "embedding par_reduces_p_subsumes_par_c_star (one proper par-step is a computational ",
                "multi-step) over the reflexive-transitive closure. par_reduces_p_star.rec on the chain — ",
                "the refl arm is par_reduces_c_star.refl, the step arm glues the head step's c-star with ",
                "the IH via par_reduces_c_star_trans. The backward half of the star-level sandwich; with ",
                "par_reduces_c_star_subsumes_par_p_star it makes the two RT-closures coincide. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment F+++, Tait–Martin-Löf lift)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star.rec".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_p_subsumes_par_c_star".to_string(),
                "par_reduces_c_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_p_star_strip: THE STRIP lemma. Tile par_diamond down one
        // par_reduces_p_star leg — strip one MULTI-step leg (e ⇒_p* e1) against one
        // SINGLE-step leg (e ⇒_p e2) into a multi-step join. Mirror of the iota-free
        // par_strips_bd_star_strip; now valid because par_diamond is a TRUE single-step
        // diamond. Induction on the par_reduces_p_star derivation e ⇒_p* e1 with the
        // motive generalized over the single-step target; the refl arm meets at e2,
        // the step arm joins via par_diamond (CPS) then the IH, closing the single-step
        // side through par_subsumes_par_p_star + par_reduces_p_star_trans.
        self.add_definition(SpecDefinition {
            name: "par_strips_p_star_strip".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "RecEnvReductNotRedex env -> RecEnvCtorNoRecMeta env -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_p_star env e e1 -> par_reduces_p env e e2 -> ",
                "par_strips_witness_p_star env e1 e2"
            )
            .to_string(),
            value_src: Some(par_strips_p_star_strip_proof()),
            is_axiom: false,
            description: concat!(
                "The STRIP lemma: strip one multi-step leg (par_reduces_p_star env e e1) against one ",
                "single-step leg (par_reduces_p env e e2) into a multi-step join par_strips_witness_p_star ",
                "env e1 e2. Proved by induction on the par_reduces_p_star derivation via ",
                "par_reduces_p_star.rec, generalizing the motive over the single-step target; the refl arm ",
                "meets at e2, the step arm joins via the STRONG single-step diamond par_diamond (CPS form) ",
                "then the IH, closing the single-step side through par_subsumes_par_p_star + ",
                "par_reduces_p_star_trans. The proper-parallel analogue of par_strips_bd_star_strip — valid ",
                "because par_diamond is a true single-step diamond (unlike par_reduces_c's WCR). Carries the ",
                "four faithful interfaces as hypotheses. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment F+++, Tait–Martin-Löf lift)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star.rec".to_string(),
                "par_reduces_p_star.refl".to_string(),
                "par_diamond".to_string(),
                "par_strips_witness_p_star".to_string(),
                "par_strips_witness_p_star.intro".to_string(),
                "par_strips_witness_p_star.rec".to_string(),
                "par_subsumes_par_p_star".to_string(),
                "par_reduces_p_star_trans".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_star_diamond: par_reduces_p_star CONFLUENCE (the Tait–Martin-Löf
        // multi-step diamond). Two par_reduces_p_star reductions from a common source
        // join at a shared reduct. Induction on the FIRST star leg via
        // par_reduces_p_star.rec, motive generalized over the second multi-step target;
        // the refl arm meets at e2, the step arm strips the single step e ⇒_p e' out of
        // the second leg via par_strips_p_star_strip, recurses through the IH, and
        // re-closes with par_reduces_p_star_trans. Mirror of par_reduces_bd_star_diamond.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_star_diamond".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "RecEnvReductNotRedex env -> RecEnvCtorNoRecMeta env -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_p_star env e e1 -> par_reduces_p_star env e e2 -> ",
                "par_strips_witness_p_star env e1 e2"
            )
            .to_string(),
            value_src: Some(par_reduces_p_star_diamond_proof()),
            is_axiom: false,
            description: concat!(
                "par_reduces_p_star CONFLUENCE (the Tait–Martin-Löf multi-step diamond): two proper-parallel ",
                "multi-step reductions from a common source join at a shared reduct, packaged as ",
                "par_strips_witness_p_star. Proved by induction on the first star leg via par_reduces_p_star.rec ",
                "(motive generalized over the second target); the refl arm meets at e2, the step arm strips the ",
                "head step out of the second leg via the strip lemma par_strips_p_star_strip then recurses ",
                "through the IH and re-closes with par_reduces_p_star_trans. The proper-parallel analogue of the ",
                "iota-free par_reduces_bd_star_diamond — but UNCONDITIONAL on the iota seam (par_diamond already ",
                "absorbed it). Carries the four faithful interfaces as hypotheses. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment F+++, Tait–Martin-Löf lift)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star.rec".to_string(),
                "par_reduces_p_star.refl".to_string(),
                "par_strips_p_star_strip".to_string(),
                "par_strips_witness_p_star".to_string(),
                "par_strips_witness_p_star.intro".to_string(),
                "par_strips_witness_p_star.rec".to_string(),
                "par_reduces_p_star_trans".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_c_star_diamond: par_reduces_c_star CONFLUENCE (CHURCH–ROSSER) —
        // the result that makes church_rosser_whnf deletable. UNCONDITIONAL except for
        // the four faithful interfaces. Via the star-level SANDWICH: lift both
        // par_reduces_c_star legs into par_reduces_p_star (par_reduces_c_star_subsumes_-
        // par_p_star), join them with the par_reduces_p_star diamond (brick 2), project
        // the p-star witness, and bridge each leg back to par_reduces_c_star
        // (par_reduces_p_star_subsumes_par_c_star), packaging par_strips_witness_c_star.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_diamond".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "RecEnvReductNotRedex env -> RecEnvCtorNoRecMeta env -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_c_star env e e1 -> par_reduces_c_star env e e2 -> ",
                "par_strips_witness_c_star env e1 e2"
            )
            .to_string(),
            value_src: Some(par_reduces_c_star_diamond_proof()),
            is_axiom: false,
            description: concat!(
                "par_reduces_c_star CONFLUENCE (CHURCH–ROSSER): two computational multi-step reductions from a ",
                "common source join at a shared reduct, packaged as par_strips_witness_c_star. UNCONDITIONAL ",
                "except for the four faithful interfaces. Proved via the star-level sandwich par_reduces_c_star ",
                "⊆ par_reduces_p_star ⊆ par_reduces_c_star: lift both legs into par_reduces_p_star ",
                "(par_reduces_c_star_subsumes_par_p_star), confluence-join them via the Tait–Martin-Löf ",
                "par_reduces_p_star_diamond, project the par_strips_witness_p_star reduct, and bridge each join ",
                "leg back to par_reduces_c_star (par_reduces_p_star_subsumes_par_c_star). THIS is the result that ",
                "makes the church_rosser_whnf HelperAxiom deletable (the capstone discharges the four interfaces ",
                "for the kernel env). Carries the four faithful interfaces as hypotheses. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment F+++, Tait–Martin-Löf lift to CR)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c_star".to_string(),
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star_diamond".to_string(),
                "par_reduces_c_star_subsumes_par_p_star".to_string(),
                "par_reduces_p_star_subsumes_par_c_star".to_string(),
                "par_strips_witness_p_star".to_string(),
                "par_strips_witness_p_star.rec".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.intro".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The blueprint's single-fire complete development `dev` (= develop subterms,
    /// then `topIotaStar` the node). Identical to `cd` (complete_development.rs) in
    /// every arm EXCEPT the BETA arm, which `dev` wraps in `topIotaStar` so that
    /// `dev e` is NEVER itself a top iota redex (the idempotence `cd` lacks: cd's
    /// beta output `instantiate (cd b)(cd a)` CAN be a fresh top redex). That
    /// idempotence (`topIotaStar_dev`) is exactly what the iota arm of `dev_triangle`
    /// needs. The app/iota arm is already `topIotaStar`-wrapped in `cd`
    /// (`opt_default (iota_reduct …) … = topIotaStar …`), so `dev` differs from `cd`
    /// only by the extra beta-arm fire. STRUCTURAL `KExpr.rec` (7 minors — the trailing
    /// `let_` minor fires ZETA on the developed value/body then topIotaStar-wraps, exactly
    /// as the beta arm does — so `dev (let_ ty val body) = topIotaStar (instantiate (dev
    /// body)(dev val))`, never itself a top iota redex).
    fn add_dev_developer(&mut self) -> Result<(), SpecError> {
        // dev env e: develop subterms then topIotaStar the node. STRUCTURAL KExpr.rec.
        // app arm: if the original head f is a lam (beta present) -> topIotaStar env
        // (instantiate (kexpr_lam_body (dev f)) (dev a)); else -> topIotaStar env
        // (app (dev f)(dev a)). sort/bvar/const fixed; lam/pi recurse. let_ arm: fire
        // zeta on the developed body/value -> topIotaStar env (instantiate (dev b)(dev v)).
        self.add_recursive_def(
            r"def dev (env : RecEnv) (e : KExpr) : KExpr := KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (f : KExpr) (a : KExpr) (df : KExpr) (da : KExpr) => Bool.rec (fun (_ : Bool) => KExpr) (topIotaStar env (KExpr.app df da)) (topIotaStar env (instantiate (kexpr_lam_body df) da)) (kexpr_is_lam f)) (fun (ty : KExpr) (b : KExpr) (dty : KExpr) (db : KExpr) => KExpr.lam dty db) (fun (ty : KExpr) (b : KExpr) (dty : KExpr) (db : KExpr) => KExpr.pi dty db) (fun (nm : Name) (us : ListType Level) => KExpr.const nm us) (fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (dlt : KExpr) (dlv : KExpr) (dlb : KExpr) => topIotaStar env (instantiate dlb dlv)) (fun (s : Name) (i : Nat) (sub : KExpr) (dsub : KExpr) => KExpr.proj s i dsub) (fun (v : Nat) => KExpr.lit v) e",
            "The blueprint's single-fire complete development dev env e: develop subterms then topIotaStar the \
             node. STRUCTURAL KExpr.rec (7 minors). app arm: if the original head f is a lam (beta present) -> \
             topIotaStar env (instantiate (kexpr_lam_body (dev f)) (dev a)); else -> topIotaStar env (app (dev \
             f)(dev a)). sort/bvar/const fixed; lam/pi recurse; let_ arm fires zeta on the developed body/value \
             -> topIotaStar env (instantiate (dev b)(dev v)). Identical to cd EXCEPT the beta AND let_ arms are \
             topIotaStar-wrapped (so dev e is never a top iota redex — the idempotence cd lacks). Part of #2859 \
             (Increment F+++, dev developer / par_reduces_p diamond port).",
        )?;

        // dev_lam / dev_pi: binder unfold dev env (HEAD ty b) = HEAD (dev ty)(dev b) — refl.
        for (name, head) in [("dev_lam", "KExpr.lam"), ("dev_pi", "KExpr.pi")] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    "forall (env : RecEnv) (ty : KExpr) (b : KExpr), \
                     Eq KExpr (dev env ({head} ty b)) ({head} (dev env ty) (dev env b))"
                ),
                value_src: Some(format!(
                    "fun (env : RecEnv) (ty : KExpr) (b : KExpr) => \
                     Eq.refl KExpr (dev env ({head} ty b))"
                )),
                is_axiom: false,
                description: format!(
                    "dev unfold for {head}: dev env ({head} ty b) = {head} (dev env ty)(dev env b). \
                     Reflexivity (the kernel computes the KExpr.rec binder arm). Part of #2859 (Increment F+++)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from(["dev".to_string(), "Eq.refl".to_string()])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // dev_app: the raw app-arm unfold (stuck on kexpr_is_lam f for abstract f).
        self.add_definition(SpecDefinition {
            name: "dev_app".to_string(),
            type_src: "forall (env : RecEnv) (f : KExpr) (a : KExpr), \
                 Eq KExpr (dev env (KExpr.app f a)) \
                 (Bool.rec (fun (_ : Bool) => KExpr) \
                 (topIotaStar env (KExpr.app (dev env f) (dev env a))) \
                 (topIotaStar env (instantiate (kexpr_lam_body (dev env f)) (dev env a))) \
                 (kexpr_is_lam f))"
                .to_string(),
            value_src: Some(
                "fun (env : RecEnv) (f : KExpr) (a : KExpr) => \
                 Eq.refl KExpr (dev env (KExpr.app f a))"
                    .to_string(),
            ),
            is_axiom: false,
            description: "dev unfold for app (raw, stuck on kexpr_is_lam f): dev env (app f a) = Bool.rec ... (kexpr_is_lam f), both branches topIotaStar-wrapped (false: topIotaStar (app (dev f)(dev a)); true: topIotaStar (instantiate (kexpr_lam_body (dev f))(dev a))). Reflexivity. Part of #2859 (Increment F+++).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "dev".to_string(),
                "topIotaStar".to_string(),
                "Bool.rec".to_string(),
                "instantiate".to_string(),
                "kexpr_lam_body".to_string(),
                "kexpr_is_lam".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // dev_app_lam: the resolved beta branch (head is a syntactic lam). dev env
        // (app (lam A b) a) = topIotaStar env (instantiate (dev b)(dev a)). Refl.
        self.add_definition(SpecDefinition {
            name: "dev_app_lam".to_string(),
            type_src: "forall (env : RecEnv) (A : KExpr) (b : KExpr) (a : KExpr), \
                 Eq KExpr (dev env (KExpr.app (KExpr.lam A b) a)) (topIotaStar env (instantiate (dev env b) (dev env a)))"
                .to_string(),
            value_src: Some(
                "fun (env : RecEnv) (A : KExpr) (b : KExpr) (a : KExpr) => \
                 Eq.refl KExpr (dev env (KExpr.app (KExpr.lam A b) a))"
                    .to_string(),
            ),
            is_axiom: false,
            description: "dev unfold for an app whose head is a syntactic lam (beta present): dev env (app (lam A b) a) = topIotaStar env (instantiate (dev env b)(dev env a)). Reflexivity (kexpr_is_lam (lam A b) = true; kexpr_lam_body (dev (lam A b)) = dev b). Part of #2859 (Increment F+++).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "dev".to_string(),
                "topIotaStar".to_string(),
                "instantiate".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // dev_let: the zeta branch (genuine let_ node). dev env (let_ ty val body) =
        // topIotaStar env (instantiate (dev env body)(dev env val)). Refl (the KExpr.rec
        // let_ minor fires zeta on the developed body/value, exactly as dev_app_lam does
        // for beta). The transport lemma dev_self / dev_triangle use on the two let arms.
        self.add_definition(SpecDefinition {
            name: "dev_let".to_string(),
            type_src: "forall (env : RecEnv) (ty : KExpr) (val : KExpr) (body : KExpr), \
                 Eq KExpr (dev env (KExpr.let_ ty val body)) (topIotaStar env (instantiate (dev env body) (dev env val)))"
                .to_string(),
            value_src: Some(
                "fun (env : RecEnv) (ty : KExpr) (val : KExpr) (body : KExpr) => \
                 Eq.refl KExpr (dev env (KExpr.let_ ty val body))"
                    .to_string(),
            ),
            is_axiom: false,
            description: "dev unfold for a genuine let_ node (zeta present): dev env (let_ ty val body) = topIotaStar env (instantiate (dev env body)(dev env val)). Reflexivity (the KExpr.rec let_ minor fires zeta on the developed body/value, the topIotaStar-wrapped analogue of dev_app_lam's beta). Part of #2859 (Increment F+++, let-promotion).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "dev".to_string(),
                "topIotaStar".to_string(),
                "instantiate".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_dev_idempotent()?;

        Ok(())
    }

    /// The idempotence chain for `dev`: `dev e` is never a top iota redex
    /// (`dev_iotaReduct_none`), hence `topIotaStar (dev e) = dev e` (`topIotaStar_dev`).
    /// This is exactly the fact the iota arm of `dev_triangle` consumes to absorb the
    /// off-by-one `topIotaStar` step. Needs the `RecEnvReductNotRedex` interface (via
    /// `topIotaStar_no_redex` on the app arms). The const arm needs `iota_reduct_const_none`
    /// (a const has an empty spine, so no major premise — not a redex).
    fn add_dev_idempotent(&mut self) -> Result<(), SpecError> {
        // iota_reduct_const_none: a const applied to nothing is never an iota redex
        // (its spine kapp_args is nil, so the major-premise lookup list_head (list_drop
        // _ nil) = none). Case on iota_reduct env (const nm us): the none arm is the
        // goal; the some arm is refuted via iota_reduct_some_inv (which would yield a
        // major h3 : list_head (list_drop major_idx nil) = some major, absurd by
        // list_drop_nil + list_head_nil).
        let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
        let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
        let reduct = format!(
            "(apply_spine (list_drop (Nat.succ {major_idx}) (kapp_args (KExpr.const nm us))) \
             (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) \
             (apply_spine (list_take {prefix_n} (kapp_args (KExpr.const nm us))) (recrule_rhs rule))))"
        );
        // nilhead : list_head (list_drop major_idx (kapp_args (const nm us))) = none.
        let nilhead = format!(
            "(Eq.trans (OptionType KExpr) \
             (list_head (list_drop {major_idx} (kapp_args (KExpr.const nm us)))) \
             (list_head (ListType.nil KExpr)) (OptionType.none KExpr) \
             (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) \
             (list_drop {major_idx} (kapp_args (KExpr.const nm us))) (ListType.nil KExpr) (list_drop_nil {major_idx})) \
             list_head_nil)"
        );
        let goal_none =
            "Eq (OptionType KExpr) (iota_reduct env (KExpr.const nm us)) (OptionType.none KExpr)";
        let const_none_value = format!(
            "fun (env : RecEnv) (nm : Name) (us : ListType Level) => \
             OptionType.rec KExpr \
             (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (iota_reduct env (KExpr.const nm us)) o -> {goal_none}) \
             (fun (heq : {goal_none}) => heq) \
             (fun (e2 : KExpr) (heq : Eq (OptionType KExpr) (iota_reduct env (KExpr.const nm us)) (OptionType.some KExpr e2)) => \
             iota_reduct_some_inv env (KExpr.const nm us) e2 ({goal_none}) heq \
             (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
             (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.const nm us))) (OptionType.some Name recname)) \
             (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
             (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args (KExpr.const nm us)))) (OptionType.some KExpr major)) \
             (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
             (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
             (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e2)) => \
             option_none_ne_some KExpr major ({goal_none}) \
             (Eq.trans (OptionType KExpr) (OptionType.none KExpr) \
             (list_head (list_drop {major_idx} (kapp_args (KExpr.const nm us)))) (OptionType.some KExpr major) \
             (Eq.symm (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args (KExpr.const nm us)))) (OptionType.none KExpr) {nilhead}) \
             h3))) \
             (iota_reduct env (KExpr.const nm us)) \
             (Eq.refl (OptionType KExpr) (iota_reduct env (KExpr.const nm us)))"
        );
        self.add_definition(SpecDefinition {
            name: "iota_reduct_const_none".to_string(),
            type_src: "forall (env : RecEnv) (nm : Name) (us : ListType Level), \
                 Eq (OptionType KExpr) (iota_reduct env (KExpr.const nm us)) (OptionType.none KExpr)"
                .to_string(),
            value_src: Some(const_none_value),
            is_axiom: false,
            description: concat!(
                "iota_reduct_const_none: a bare const (empty application spine) is never a top iota redex — ",
                "iota_reduct env (const nm us) = none. kapp_args (const nm us) = nil, so the major-premise lookup ",
                "list_head (list_drop major_idx nil) = none. OptionType.rec convoy on iota_reduct env (const nm ",
                "us): the none arm returns the reflexive equation; the some arm is refuted via iota_reduct_some_inv ",
                "(its h3 would assert list_head (list_drop major_idx nil) = some major, absurd by list_drop_nil + ",
                "list_head_nil + option_none_ne_some). DerivedProved, zero axiom_deps. Part of #2859 (Increment F+++)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "iota_reduct_some_inv".to_string(),
                "option_none_ne_some".to_string(),
                "list_drop_nil".to_string(),
                "list_head_nil".to_string(),
                "list_head".to_string(),
                "list_drop".to_string(),
                "kapp_args".to_string(),
                "OptionType.rec".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // dev_iotaReduct_none: dev env e is never a top iota redex. KExpr.rec on e:
        // sort/bvar/lam/pi arms are refl (iota_reduct of a non-const / binder head is
        // definitionally none); the const arm is iota_reduct_const_none; the app arm
        // runs a Bool.rec on kexpr_is_lam f — both branches are topIotaStar-wrapped, so
        // topIotaStar_no_redex (interface) gives none; the let_ arm is topIotaStar-wrapped
        // too (dev of a let_ = topIotaStar (instantiate (dev b)(dev v))), so
        // topIotaStar_no_redex (interface) again gives none.
        let m_motive = "(fun (x : KExpr) => Eq (OptionType KExpr) (iota_reduct env (dev env x)) (OptionType.none KExpr))";
        let refl_none = "(Eq.refl (OptionType KExpr) (OptionType.none KExpr))";
        let app_arm = "(fun (f : KExpr) (a : KExpr) \
             (_ihf : Eq (OptionType KExpr) (iota_reduct env (dev env f)) (OptionType.none KExpr)) \
             (_iha : Eq (OptionType KExpr) (iota_reduct env (dev env a)) (OptionType.none KExpr)) => \
             Bool.rec \
             (fun (bcond : Bool) => Eq (OptionType KExpr) (iota_reduct env (Bool.rec (fun (_ : Bool) => KExpr) \
             (topIotaStar env (KExpr.app (dev env f) (dev env a))) \
             (topIotaStar env (instantiate (kexpr_lam_body (dev env f)) (dev env a))) bcond)) (OptionType.none KExpr)) \
             (topIotaStar_no_redex env (KExpr.app (dev env f) (dev env a)) w) \
             (topIotaStar_no_redex env (instantiate (kexpr_lam_body (dev env f)) (dev env a)) w) \
             (kexpr_is_lam f))"
            .to_string();
        let binder_arm = format!(
            "(fun (ty : KExpr) (b : KExpr) \
             (_ihty : Eq (OptionType KExpr) (iota_reduct env (dev env ty)) (OptionType.none KExpr)) \
             (_ihb : Eq (OptionType KExpr) (iota_reduct env (dev env b)) (OptionType.none KExpr)) => {refl_none})"
        );
        // let_ arm: dev env (let_ lt lv lb) = topIotaStar env (instantiate (dev lb)(dev lv))
        // (topIotaStar-wrapped like the app arm), so it is never a top iota redex —
        // topIotaStar_no_redex (RecEnvReductNotRedex interface) gives none.
        let let_none_arm =
            "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) \
             (_ihlt : Eq (OptionType KExpr) (iota_reduct env (dev env lt)) (OptionType.none KExpr)) \
             (_ihlv : Eq (OptionType KExpr) (iota_reduct env (dev env lv)) (OptionType.none KExpr)) \
             (_ihlb : Eq (OptionType KExpr) (iota_reduct env (dev env lb)) (OptionType.none KExpr)) => \
             topIotaStar_no_redex env (instantiate (dev env lb) (dev env lv)) w)"
                .to_string();
        let dev_none_value = format!(
            "fun (env : RecEnv) (e : KExpr) (w : RecEnvReductNotRedex env) => \
             KExpr.rec {m_motive} \
             (fun (n : Level) => {refl_none}) \
             (fun (i : Nat) => {refl_none}) \
             {app_arm} \
             {binder_arm} \
             {binder_arm} \
             (fun (nm : Name) (us : ListType Level) => iota_reduct_const_none env nm us) \
             {let_none_arm} \
             (fun (s : Name) (i : Nat) (sub : KExpr) (_ihsub : Eq (OptionType KExpr) (iota_reduct env (dev env sub)) (OptionType.none KExpr)) => {refl_none}) \
             (fun (v : Nat) => {refl_none}) \
             e"
        );
        self.add_definition(SpecDefinition {
            name: "dev_iotaReduct_none".to_string(),
            type_src: "forall (env : RecEnv) (e : KExpr), \
                 RecEnvReductNotRedex env -> \
                 Eq (OptionType KExpr) (iota_reduct env (dev env e)) (OptionType.none KExpr)"
                .to_string(),
            value_src: Some(dev_none_value),
            is_axiom: false,
            description: concat!(
                "dev_iotaReduct_none: dev env e is never a top iota redex (iota_reduct env (dev env e) = none). ",
                "KExpr.rec on e: sort/bvar arms refl (non-const head -> none defeq); lam/pi arms refl (binder head ",
                "-> none defeq); const arm iota_reduct_const_none; app arm Bool.rec on kexpr_is_lam f, both branches ",
                "topIotaStar-wrapped so topIotaStar_no_redex (RecEnvReductNotRedex interface) gives none; let_ arm ",
                "topIotaStar-wrapped (dev of a let_ = topIotaStar (instantiate (dev b)(dev v))) so topIotaStar_no_redex ",
                "again gives none. The idempotence premise for topIotaStar_dev. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+++)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "dev".to_string(),
                "iota_reduct".to_string(),
                "iota_reduct_const_none".to_string(),
                "topIotaStar".to_string(),
                "topIotaStar_no_redex".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "kexpr_is_lam".to_string(),
                "kexpr_lam_body".to_string(),
                "instantiate".to_string(),
                "KExpr.rec".to_string(),
                "Bool.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // topIotaStar_dev: topIotaStar (dev e) = dev e. Direct from topIotaStar_fix +
        // dev_iotaReduct_none. The idempotence the iota arm of dev_triangle consumes.
        self.add_definition(SpecDefinition {
            name: "topIotaStar_dev".to_string(),
            type_src: "forall (env : RecEnv) (e : KExpr), \
                 RecEnvReductNotRedex env -> \
                 Eq KExpr (topIotaStar env (dev env e)) (dev env e)"
                .to_string(),
            value_src: Some(
                "fun (env : RecEnv) (e : KExpr) (w : RecEnvReductNotRedex env) => \
                 topIotaStar_fix env (dev env e) (dev_iotaReduct_none env e w)"
                    .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "topIotaStar_dev: topIotaStar env (dev env e) = dev env e (idempotence on developments). Direct ",
                "from topIotaStar_fix (iota_reduct = none -> topIotaStar fixed) applied to dev_iotaReduct_none (dev ",
                "e is never a top redex). The off-by-one absorber the iota arm of dev_triangle needs. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment F+++, par_reduces_p diamond port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "topIotaStar".to_string(),
                "topIotaStar_fix".to_string(),
                "dev".to_string(),
                "dev_iotaReduct_none".to_string(),
                "RecEnvReductNotRedex".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_dev_self()?;

        Ok(())
    }

    /// `dev_self`: every term parallel-reduces to its development (`par_reduces_p env
    /// e (dev env e)`). Structural `KExpr.rec` mirroring `cd_refl`, but the app arm is
    /// `par_topIotaStar`-wrapped on BOTH branches (matching dev's extra top fire):
    ///   * false branch (`kexpr_is_lam f = false`): `dev (app f a) = topIotaStar (app
    ///     (dev f)(dev a))` (dev_app + hfalse); `app (dev f)(dev a)` is a one-step app
    ///     congruence, lifted to its topIotaStar by `par_topIotaStar`.
    ///   * lam branch (`f = lam A b0`): `dev (app (lam A b0) a) = topIotaStar
    ///     (instantiate (dev b0)(dev a))` (dev_app_lam); a `par_reduces_p.beta` (its
    ///     A/b0 components recovered from the f-IH via `par_reduces_p_lam_inv`) lands the
    ///     contraction, lifted to its topIotaStar by `par_topIotaStar`.
    /// No interface needed (par_topIotaStar uses iota_p directly).
    fn add_dev_self(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "dev_self".to_string(),
            type_src: "forall (env : RecEnv) (e : KExpr), par_reduces_p env e (dev env e)"
                .to_string(),
            value_src: Some(dev_self_proof()),
            is_axiom: false,
            description: concat!(
                "dev_self: every term parallel-reduces to its development — par_reduces_p env e (dev env e). ",
                "Structural KExpr.rec mirroring cd_refl, but the app arm is par_topIotaStar-wrapped on both ",
                "branches (matching dev's extra top fire): false branch (kexpr_is_lam f = false) lifts the app ",
                "congruence app (dev f)(dev a) to its topIotaStar via par_topIotaStar (dev_app + hfalse); lam ",
                "branch (f = lam A b0) lifts a par_reduces_p.beta (A/b0 components recovered from the f-IH via ",
                "par_reduces_p_lam_inv) to its topIotaStar via par_topIotaStar (dev_app_lam). sort/bvar/const ",
                "refl; lam/pi par_reduces_p.lam/.pi on the IHs (dev_lam/dev_pi). DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F+++, par_reduces_p diamond port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p.beta".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p.lam".to_string(),
                "par_reduces_p.pi".to_string(),
                "par_reduces_p.let_".to_string(),
                "par_reduces_p_lam_inv".to_string(),
                "par_topIotaStar".to_string(),
                "topIotaStar".to_string(),
                "dev".to_string(),
                "dev_lam".to_string(),
                "dev_pi".to_string(),
                "dev_app".to_string(),
                "dev_app_lam".to_string(),
                "dev_let".to_string(),
                "kexpr_lam_cases".to_string(),
                "kexpr_is_lam".to_string(),
                "kexpr_lam_body".to_string(),
                "instantiate".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "KExpr.rec".to_string(),
                "Bool.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_app_redex_tri()?;

        Ok(())
    }

    /// `app_redex_tri`: the app-arm content of the iota triangle, isolated as a
    /// standalone (NON-inductive) lemma so the 8-arm `iota_redex_tri_aux` induction can
    /// just hand it the f-IH. Given the IH `ihf` for f (every redex of f reaches
    /// `topIotaStar f'`), the originals `f ⇒_p f'` / `a ⇒_p a'`, and that `app f a` is a
    /// redex with reduct r, it shows `r ⇒_p topIotaStar (app f' a')`. Case split on
    /// `iota_reduct env f`: none = MINIMAL/boundary (major = a), reusing the keystone
    /// `par_reduces_p_reduct_cong` (LEFT leg) + `par_reduces_p_app_redex` (reconstruct
    /// the (app f' a')-side reduct); some f1 = OVER-application (f itself a redex), where
    /// the IH supplies the inner reduct congruence (this is the case the marked-fuel
    /// route walled on — the derivation IH replaces the fuel). Needs only the
    /// `RecEnvCtorNoRecMeta` disjointness interface.
    fn add_app_redex_tri(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "app_redex_tri".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (r : KExpr), ",
                "RecEnvCtorNoRecMeta env -> ",
                "(forall (rf : KExpr), Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr rf) -> ",
                "par_reduces_p env rf (topIotaStar env f')) -> ",
                "par_reduces_p env f f' -> par_reduces_p env a a' -> ",
                "Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr r) -> ",
                "par_reduces_p env r (topIotaStar env (KExpr.app f' a'))"
            )
            .to_string(),
            value_src: Some(app_redex_tri_proof()),
            is_axiom: false,
            description: concat!(
                "app_redex_tri (the over-application crux): the app-arm content of the iota triangle isolated as a ",
                "standalone non-inductive lemma. Given the f-IH (ihf : every redex of f reaches topIotaStar f'), ",
                "f ⇒_p f', a ⇒_p a', and iota_reduct env (app f a) = some r, it delivers r ⇒_p topIotaStar (app f' ",
                "a'). Case split on iota_reduct env f: NONE = MINIMAL/boundary (major = a) — invert via ",
                "iota_reduct_app_minimal_boundary_idx_type, LEFT leg r ⇒_p reduct_m by par_reduces_p_reduct_cong, ",
                "RIGHT recon iota_reduct (app f' a') = some reduct_m by par_reduces_p_app_redex (so topIotaStar (app ",
                "f' a') = reduct_m); SOME f1 = OVER-application (f a redex) — r = app f1 a (iota_reduct_app_some + ",
                "option_some_inj), ihf f1 gives f1 ⇒_p topIotaStar f', then split iota_reduct f' (none: topIotaStar ",
                "f' = f', par_topIotaStar absorbs; some f1': topIotaStar (app f' a') = app f1' a' via ",
                "iota_reduct_app_some). The OVER case is where the marked-fuel keystone walled — here the DERIVATION ",
                "IH supplies the inner reduct congruence, no fuel needed. Needs only RecEnvCtorNoRecMeta. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F+++, par_reduces_p diamond port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p_reduct_cong".to_string(),
                "par_reduces_p_app_redex".to_string(),
                "iota_reduct_app_minimal_boundary_idx_type".to_string(),
                "iota_reduct_app_some".to_string(),
                "option_some_inj".to_string(),
                "topIotaStar".to_string(),
                "topIotaStar_fix".to_string(),
                "par_topIotaStar".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_args".to_string(),
                "list_head".to_string(),
                "list_drop".to_string(),
                "list_take".to_string(),
                "list_length".to_string(),
                "apply_spine".to_string(),
                "recmeta_num_params".to_string(),
                "recmeta_num_motives".to_string(),
                "recmeta_num_minors".to_string(),
                "recmeta_num_indices".to_string(),
                "recrule_num_fields".to_string(),
                "recrule_rhs".to_string(),
                "OptionType.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_iota_redex_tri()?;

        Ok(())
    }

    /// `iota_redex_tri_aux` + `iota_redex_tri`: the iota↔Par commutation for a redex,
    /// the brick that closes the open iota_p arm. By induction on the `par_reduces_p`
    /// DERIVATION (NOT a term measure): if `X` parallel-reduces to `t` and `X` is a
    /// redex with reduct `r`, then `r ⇒_p topIotaStar t`. refl uses the opt_default
    /// computation; the iota_p (cascade) case telescopes via `topIotaStar_step`; the
    /// app-congruence case delegates to `app_redex_tri` (the f-IH is exactly the
    /// recursor IH); beta/lam/pi/forall_/let_/let_cong are vacuous (non-recursor head —
    /// a let_ is its own spine head, so never an iota redex — discharged
    /// by `iota_step_head_none_absurd_type`). Carries the faithful interfaces
    /// `RecEnvReductNotRedex` (for topIotaStar_step) and `RecEnvCtorNoRecMeta` (for the
    /// minimal app case) as HYPOTHESES.
    fn add_iota_redex_tri(&mut self) -> Result<(), SpecError> {
        // iota_redex_tri_aux: the derivation-induction core.
        self.add_definition(SpecDefinition {
            name: "iota_redex_tri_aux".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (X : KExpr) (t : KExpr), ",
                "RecEnvReductNotRedex env -> RecEnvCtorNoRecMeta env -> ",
                "par_reduces_p env X t -> ",
                "forall (r : KExpr), Eq (OptionType KExpr) (iota_reduct env X) (OptionType.some KExpr r) -> ",
                "par_reduces_p env r (topIotaStar env t)"
            )
            .to_string(),
            value_src: Some(iota_redex_tri_aux_proof()),
            is_axiom: false,
            description: concat!(
                "iota_redex_tri_aux: by induction on the par_reduces_p DERIVATION X ⇒_p t, if iota_reduct env X = ",
                "some r then r ⇒_p topIotaStar env t. refl: topIotaStar env X = r (opt_default computation), refl; ",
                "iota_p (cascade): transport the IH along topIotaStar_step (off-by-one absorber, needs ",
                "RecEnvReductNotRedex); app-congruence: delegate to app_redex_tri (the recursor's f-IH is exactly ",
                "app_redex_tri's ihf, needs RecEnvCtorNoRecMeta); beta/lam/pi/forall_/let_/let_cong: vacuous ",
                "(non-recursor head — a let_ is its own spine head, so never an iota redex -> ",
                "iota_step_head_none_absurd_type with a refl head-none witness). The blueprint's ",
                "iota_redex_tri_aux ported to Clean's variable-arity app-spine recursor. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment F+++, par_reduces_p diamond port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "par_reduces_p.refl".to_string(),
                "app_redex_tri".to_string(),
                "topIotaStar".to_string(),
                "topIotaStar_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "iota_step".to_string(),
                "instantiate".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "OptionType.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_redex_tri: the user-facing wrapper. From iota_step env e2 r and
        // par_reduces_p env e2 t, conclude r ⇒_p topIotaStar env t (apply the aux at r).
        self.add_definition(SpecDefinition {
            name: "iota_redex_tri".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e2 : KExpr) (r : KExpr) (t : KExpr), ",
                "RecEnvReductNotRedex env -> RecEnvCtorNoRecMeta env -> ",
                "iota_step env e2 r -> par_reduces_p env e2 t -> ",
                "par_reduces_p env r (topIotaStar env t)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e2 : KExpr) (r : KExpr) (t : KExpr) ",
                    "(w : RecEnvReductNotRedex env) (disjoint : RecEnvCtorNoRecMeta env) ",
                    "(hr : iota_step env e2 r) (h : par_reduces_p env e2 t) => ",
                    "iota_redex_tri_aux env e2 t w disjoint h r hr"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "iota_redex_tri: the iota↔Par commutation for a redex — if the redex e2 contracts to r ",
                "(iota_step env e2 r) and also parallel-reduces to t (par_reduces_p env e2 t), then r reaches the ",
                "top-developed t (par_reduces_p env r (topIotaStar env t)). Thin wrapper applying iota_redex_tri_aux ",
                "at the reduct r (iota_step env e2 r is defeq to iota_reduct env e2 = some r). The blueprint's ",
                "iota_redex_tri — the brick that makes the open iota_p arm of dev_triangle mechanical. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment F+++, par_reduces_p diamond port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "iota_redex_tri_aux".to_string(),
                "iota_step".to_string(),
                "iota_reduct".to_string(),
                "topIotaStar".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_dev_triangle()?;

        Ok(())
    }

    /// `dev_triangle` + `par_diamond`, plus the two arm helpers `dev_kbeta` /
    /// `dev_kcong` (the dev analogues of `par_reduces_p_beta_dev` /
    /// `par_reduces_p_app_dev`, topIotaStar-wrapped). `dev_triangle` is the Takahashi
    /// triangle (`par_reduces_p e a -> par_reduces_p a (dev e)`) by induction on the
    /// derivation, closing the previously-open iota_p arm via `iota_redex_tri` +
    /// `topIotaStar_dev`. `par_diamond` is the strong single-step diamond.
    fn add_dev_triangle(&mut self) -> Result<(), SpecError> {
        // dev_kbeta: the beta-redex triangle arm for dev. par_subst_p +
        // par_topIotaStar, transported via dev_app_lam. Threads RecEnvClosed /
        // RecEnvLiftClosed (par_subst_p's gates). No topIotaStar interface needed.
        // (The two let_ arms — ZETA and let_cong — are handled directly in
        // dev_triangle_proof via dev_let, no longer through this beta helper.)
        self.add_definition(SpecDefinition {
            name: "dev_kbeta".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (A : KExpr) (body : KExpr) (a : KExpr) (body' : KExpr) (arg' : KExpr), ",
                "par_reduces_p env body' (dev env body) -> par_reduces_p env arg' (dev env a) -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_p env (instantiate body' arg') (dev env (KExpr.app (KExpr.lam A body) a))"
            )
            .to_string(),
            value_src: Some(dev_kbeta_proof()),
            is_axiom: false,
            description: concat!(
                "dev_kbeta: the beta-redex triangle arm for dev. dev (app (lam A body) a) = topIotaStar ",
                "(instantiate (dev body)(dev a)) (dev_app_lam); from body' ⇒_p dev body and arg' ⇒_p dev a, ",
                "par_subst_p (depth 0) lands instantiate body' arg' ⇒_p instantiate (dev body)(dev a), then ",
                "par_topIotaStar lifts to the topIotaStar, transported via dev_app_lam. Threads RecEnvClosed / ",
                "RecEnvLiftClosed (par_subst_p's gates). DerivedProved, zero axiom_deps. Part of #2859 (Increment F+++)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_subst_p".to_string(),
                "par_topIotaStar".to_string(),
                "topIotaStar".to_string(),
                "dev".to_string(),
                "dev_app_lam".to_string(),
                "instantiate".to_string(),
                "instantiate_at".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // dev_kcong: the app-congruence triangle arm for dev. Mirror of
        // par_reduces_p_app_dev (cd kcong arm) with cd -> dev: the false branch lifts
        // the app congruence via par_topIotaStar (dev's false arm IS topIotaStar, no
        // OptionType convoy needed); the lam branch builds the par_reduces_p.beta (double
        // par_reduces_p_lam_inv) then par_topIotaStar + dev_app_lam. No interface needed.
        self.add_definition(SpecDefinition {
            name: "dev_kcong".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), ",
                "par_reduces_p env f f' -> par_reduces_p env a a' -> ",
                "par_reduces_p env f' (dev env f) -> par_reduces_p env a' (dev env a) -> ",
                "par_reduces_p env (KExpr.app f' a') (dev env (KExpr.app f a))"
            )
            .to_string(),
            value_src: Some(dev_kcong_proof()),
            is_axiom: false,
            description: concat!(
                "dev_kcong: the app-congruence triangle arm for dev. Given f ⇒_p f', a ⇒_p a', and the post-IH ",
                "developments f' ⇒_p dev f, a' ⇒_p dev a, the reassembled app reaches the development target: app ",
                "f' a' ⇒_p dev (app f a). Mirror of par_reduces_p_app_dev (cd kcong arm) with cd -> dev: kexpr_lam_cases ",
                "f splits the false branch (kexpr_is_lam f = false — dev (app f a) = topIotaStar (app (dev f)(dev a)), ",
                "lifted from the app congruence by par_topIotaStar, NO OptionType convoy) from the lam branch (f = lam ",
                "A b0 — double par_reduces_p_lam_inv recovers the beta components, par_reduces_p.beta to instantiate ",
                "(dev b0)(dev a), then par_topIotaStar + dev_app_lam). No interface needed. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment F+++)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p.beta".to_string(),
                "par_reduces_p_lam_inv".to_string(),
                "par_topIotaStar".to_string(),
                "topIotaStar".to_string(),
                "dev".to_string(),
                "dev_lam".to_string(),
                "dev_app".to_string(),
                "dev_app_lam".to_string(),
                "kexpr_lam_cases".to_string(),
                "kexpr_is_lam".to_string(),
                "kexpr_lam_body".to_string(),
                "instantiate".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "Bool.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // dev_triangle: THE Takahashi triangle. Every one-step par_reduces_p-reduct of e
        // reduces in one further step to the complete development dev e. Induction on the
        // par_reduces_p derivation (par_reduces_p.rec, motive M e a := par_reduces_p a
        // (dev e)): refl = dev_self; beta = dev_kbeta; app = dev_kcong; lam/pi/forall_
        // = the binder congruence (dev_lam/dev_pi/the forall_ alias); let_ (ZETA) =
        // par_subst_p + par_topIotaStar (transported via dev_let); let_cong = zeta-fire
        // (par_reduces_p.let_) + par_topIotaStar (dev_let); iota_p = iota_redex_tri
        // + topIotaStar_dev (the previously-open arm — the iota fires on the reduced premise,
        // iota_redex_tri lands r at topIotaStar (dev e), topIotaStar_dev absorbs the extra
        // fire). Carries the 4 faithful interfaces.
        self.add_definition(SpecDefinition {
            name: "dev_triangle".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (a : KExpr), ",
                "RecEnvReductNotRedex env -> RecEnvCtorNoRecMeta env -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_p env e a -> par_reduces_p env a (dev env e)"
            )
            .to_string(),
            value_src: Some(dev_triangle_proof()),
            is_axiom: false,
            description: concat!(
                "dev_triangle (the Takahashi triangle): every one-step par_reduces_p-reduct of e reduces in one ",
                "further step to the complete development dev e — par_reduces_p env e a -> par_reduces_p env a (dev ",
                "env e). Induction on the par_reduces_p derivation (motive M e a := par_reduces_p a (dev e)): refl = ",
                "dev_self; beta = dev_kbeta; app = dev_kcong; lam/pi/forall_ = binder congruence; let_ (ZETA) = ",
                "par_subst_p + par_topIotaStar (dev_let transport); let_cong = zeta-fire (par_reduces_p.let_) + ",
                "par_topIotaStar (dev_let); iota_p = ",
                "iota_redex_tri + topIotaStar_dev (the previously-OPEN iota arm — now mechanical: iota_redex_tri ",
                "lands r at topIotaStar (dev e), topIotaStar_dev absorbs the off-by-one fire). Carries the four ",
                "faithful interfaces RecEnvReductNotRedex / RecEnvCtorNoRecMeta / RecEnvClosed / RecEnvLiftClosed as ",
                "HYPOTHESES (not axioms). DerivedProved, zero axiom_deps. Part of #2859 (Increment F+++, par_reduces_p ",
                "diamond port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "par_reduces_p.lam".to_string(),
                "par_reduces_p.pi".to_string(),
                "par_reduces_p.forall_".to_string(),
                "par_reduces_p.let_".to_string(),
                "par_subst_p".to_string(),
                "par_topIotaStar".to_string(),
                "dev_self".to_string(),
                "dev_kbeta".to_string(),
                "dev_kcong".to_string(),
                "dev_let".to_string(),
                "iota_redex_tri".to_string(),
                "topIotaStar_dev".to_string(),
                "topIotaStar".to_string(),
                "dev".to_string(),
                "dev_lam".to_string(),
                "dev_pi".to_string(),
                "iota_step".to_string(),
                "instantiate".to_string(),
                "Nat.zero".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_diamond: THE strong single-step diamond. If e ⇒_p a and e ⇒_p b then both a
        // and b reach a common reduct c (= dev e) in ONE further par_reduces_p step each.
        // CPS form (the c witness is dev e, delivered to the continuation). Immediate from
        // dev_triangle on both legs. The breakthrough brick — it makes the church_rosser_whnf
        // deletion mechanical (Tait-Martin-Löf lift + sandwich remain).
        self.add_definition(SpecDefinition {
            name: "par_diamond".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (a : KExpr) (b : KExpr) (C : Type), ",
                "RecEnvReductNotRedex env -> RecEnvCtorNoRecMeta env -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_p env e a -> par_reduces_p env e b -> ",
                "(forall (c : KExpr), par_reduces_p env a c -> par_reduces_p env b c -> C) -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (a : KExpr) (b : KExpr) (C : Type) ",
                    "(w : RecEnvReductNotRedex env) (disjoint : RecEnvCtorNoRecMeta env) ",
                    "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
                    "(h1 : par_reduces_p env e a) (h2 : par_reduces_p env e b) ",
                    "(k : forall (c : KExpr), par_reduces_p env a c -> par_reduces_p env b c -> C) => ",
                    "k (dev env e) ",
                    "(dev_triangle env e a w disjoint closed liftclosed h1) ",
                    "(dev_triangle env e b w disjoint closed liftclosed h2)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "par_diamond (THE strong single-step diamond): if e ⇒_p a and e ⇒_p b then a and b reach a common ",
                "reduct c (= dev e) in ONE further par_reduces_p step each. CPS form — the witness c = dev e is ",
                "delivered to the continuation k with the two legs dev_triangle h1 / dev_triangle h2. Immediate from ",
                "the Takahashi triangle. The breakthrough brick of the par_reduces_p diamond route: it makes the ",
                "church_rosser_whnf retirement mechanical (the Tait-Martin-Löf lift + sandwich are the remaining ",
                "stages). Carries the four faithful interfaces. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment F+++, par_reduces_p diamond port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "dev_triangle".to_string(),
                "dev".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `par_reduces_c_star_subsumes_par_p_star` — induction on the
/// `par_reduces_c_star` chain (motive `M a b _ := par_reduces_p_star env a b`); the
/// refl arm is `par_reduces_p_star.refl`, the step arm prefixes the subsumed single
/// step via `par_reduces_p_star.step`.
fn par_reduces_c_star_subsumes_par_p_star_proof() -> String {
    concat!(
        "fun (env : RecEnv) (e : KExpr) (e' : KExpr) ",
        "(h : par_reduces_c_star env e e') => ",
        "par_reduces_c_star.rec env ",
        "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_c_star env a b) => ",
        "par_reduces_p_star env a b) ",
        "(fun (s : KExpr) => par_reduces_p_star.refl env s) ",
        "(fun (s : KExpr) (s' : KExpr) (s'' : KExpr) ",
        "(hstep : par_reduces_c env s s') (_htail : par_reduces_c_star env s' s'') ",
        "(ih : par_reduces_p_star env s' s'') => ",
        "par_reduces_p_star.step env s s' s'' ",
        "(par_reduces_c_subsumes_par_p env s s' hstep) ih) ",
        "e e' h"
    )
    .to_string()
}

/// Closed proof term for `par_reduces_p_star_subsumes_par_c_star` — induction on the
/// `par_reduces_p_star` chain (motive `M a b _ := par_reduces_c_star env a b`); the
/// refl arm is `par_reduces_c_star.refl`, the step arm glues the head step's c-star
/// (`par_reduces_p_subsumes_par_c_star`) with the IH via `par_reduces_c_star_trans`.
fn par_reduces_p_star_subsumes_par_c_star_proof() -> String {
    concat!(
        "fun (env : RecEnv) (e : KExpr) (e' : KExpr) ",
        "(h : par_reduces_p_star env e e') => ",
        "par_reduces_p_star.rec env ",
        "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_p_star env a b) => ",
        "par_reduces_c_star env a b) ",
        "(fun (s : KExpr) => par_reduces_c_star.refl env s) ",
        "(fun (s : KExpr) (s' : KExpr) (s'' : KExpr) ",
        "(hstep : par_reduces_p env s s') (_htail : par_reduces_p_star env s' s'') ",
        "(ih : par_reduces_c_star env s' s'') => ",
        "par_reduces_c_star_trans env s s' s'' ",
        "(par_reduces_p_subsumes_par_c_star env s s' hstep) ih) ",
        "e e' h"
    )
    .to_string()
}

/// Closed proof term for the STRIP lemma `par_strips_p_star_strip` — the
/// proper-parallel analogue of `par_strips_bd_star_strip`, with the per-step join
/// supplied by the STRONG single-step diamond `par_diamond` (CPS form) instead of a
/// witness projection. Induction on `par_reduces_p_star env e e1` via
/// `par_reduces_p_star.rec`, motive `M a b _ := forall x2, par_reduces_p env a x2 ->
/// par_strips_witness_p_star env b x2`. Carries the four faithful interfaces.
fn par_strips_p_star_strip_proof() -> String {
    // Outer recursor motive: generalize over the single-step target x2 so the IH can
    // be applied to par_diamond's reduct.
    let motive = concat!(
        "(fun (a : KExpr) (b : KExpr) (_h : par_reduces_p_star env a b) => ",
        "forall (x2 : KExpr), par_reduces_p env a x2 -> par_strips_witness_p_star env b x2)"
    );
    // refl arm (a = b = e0): meet at x2. e0 ⇒_p* x2 via par_subsumes_par_p_star,
    // x2 ⇒_p* x2 via par_reduces_p_star.refl.
    let refl_arm = concat!(
        "(fun (e0 : KExpr) => ",
        "fun (x2 : KExpr) (hx2 : par_reduces_p env e0 x2) => ",
        "par_strips_witness_p_star.intro env e0 x2 x2 ",
        "(par_subsumes_par_p_star env e0 x2 hx2) ",
        "(par_reduces_p_star.refl env x2))"
    );
    // step arm: hstep : e0 ⇒_p e0', _htail : e0' ⇒_p* e0'', ih : forall x,
    //   par_reduces_p env e0' x -> par_strips_witness_p_star env e0'' x. Goal: forall
    //   x2, par_reduces_p env e0 x2 -> par_strips_witness_p_star env e0'' x2.
    //
    // par_diamond (CPS) joins e0' and x2 at m (e0' ⇒_p m, x2 ⇒_p m); the IH on
    // e0' ⇒_p m joins e0'' and m at e3 (e0'' ⇒_p* e3, m ⇒_p* e3); x2 ⇒_p m ⇒_p* e3
    // via par_subsumes_par_p_star + par_reduces_p_star_trans.
    let star_proj = concat!(
        "(@par_strips_witness_p_star.rec env e0'' m ",
        "(fun (_w : par_strips_witness_p_star env e0'' m) => ",
        "par_strips_witness_p_star env e0'' x2) ",
        "(fun (e3 : KExpr) ",
        "(pe2e3 : par_reduces_p_star env e0'' e3) (pme3 : par_reduces_p_star env m e3) => ",
        "par_strips_witness_p_star.intro env e0'' x2 e3 pe2e3 ",
        "(par_reduces_p_star_trans env x2 m e3 ",
        "(par_subsumes_par_p_star env x2 m pe2m) pme3)) ",
        "(ih m pe1m))"
    );
    let diamond_k = format!(
        concat!(
            "(fun (m : KExpr) ",
            "(pe1m : par_reduces_p env e0' m) (pe2m : par_reduces_p env x2 m) => ",
            "{star_proj})"
        ),
        star_proj = star_proj,
    );
    let step_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e0' : KExpr) (e0'' : KExpr) ",
            "(hstep : par_reduces_p env e0 e0') ",
            "(_htail : par_reduces_p_star env e0' e0'') ",
            "(ih : forall (x : KExpr), par_reduces_p env e0' x -> ",
            "par_strips_witness_p_star env e0'' x) => ",
            "fun (x2 : KExpr) (hx2 : par_reduces_p env e0 x2) => ",
            "par_diamond env e0 e0' x2 (par_strips_witness_p_star env e0'' x2) ",
            "w disjoint closed liftclosed hstep hx2 {diamond_k})"
        ),
        diamond_k = diamond_k,
    );
    format!(
        concat!(
            "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
            "(w : RecEnvReductNotRedex env) (disjoint : RecEnvCtorNoRecMeta env) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
            "(h1 : par_reduces_p_star env e e1) (h2 : par_reduces_p env e e2) => ",
            "par_reduces_p_star.rec env {motive} {refl_arm} {step_arm} ",
            "e e1 h1 e2 h2"
        ),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Closed proof term for the multi-step diamond `par_reduces_p_star_diamond`
/// (par_reduces_p_star CONFLUENCE). Induction on the first star leg
/// `par_reduces_p_star env e e1` via `par_reduces_p_star.rec`, motive
/// `M a b _ := forall x2, par_reduces_p_star env a x2 -> par_strips_witness_p_star
/// env b x2`. The refl arm meets at the second target; the step arm strips the head
/// step out of the second leg via `par_strips_p_star_strip`, recurses through the IH,
/// and re-closes with `par_reduces_p_star_trans`. Mirror of
/// `par_reduces_bd_star_diamond`, threading env + the four faithful interfaces.
fn par_reduces_p_star_diamond_proof() -> String {
    let motive = concat!(
        "(fun (a : KExpr) (b : KExpr) (_h : par_reduces_p_star env a b) => ",
        "forall (x2 : KExpr), par_reduces_p_star env a x2 -> par_strips_witness_p_star env b x2)"
    );
    // refl arm (a = b = e0): meet at x2 — e0 ⇒_p* x2 is the given leg, x2 ⇒_p* x2 refl.
    let refl_arm = concat!(
        "(fun (e0 : KExpr) => ",
        "fun (x2 : KExpr) (hx2 : par_reduces_p_star env e0 x2) => ",
        "par_strips_witness_p_star.intro env e0 x2 x2 hx2 ",
        "(par_reduces_p_star.refl env x2))"
    );
    // step arm: hstep : e0 ⇒_p e0', _htail : e0' ⇒_p* e0'', ih : forall x,
    //   par_reduces_p_star env e0' x -> par_strips_witness_p_star env e0'' x. Goal:
    //   forall x2, par_reduces_p_star env e0 x2 -> par_strips_witness_p_star env e0'' x2.
    //
    // Strip lemma joins the multi-step e0 ⇒_p* x2 against the single step e0 ⇒_p e0' at
    // m (x2 ⇒_p* m, e0' ⇒_p* m); the IH on e0' ⇒_p* m joins e0'' and m at e3
    // (e0'' ⇒_p* e3, m ⇒_p* e3); x2 ⇒_p* m ⇒_p* e3 via transitivity.
    let star_proj = concat!(
        "(@par_strips_witness_p_star.rec env e0'' m ",
        "(fun (_w2 : par_strips_witness_p_star env e0'' m) => ",
        "par_strips_witness_p_star env e0'' x2) ",
        "(fun (e3 : KExpr) ",
        "(pe2e3 : par_reduces_p_star env e0'' e3) (pme3 : par_reduces_p_star env m e3) => ",
        "par_strips_witness_p_star.intro env e0'' x2 e3 pe2e3 ",
        "(par_reduces_p_star_trans env x2 m e3 pe2m pme3)) ",
        "(ih m pe1m))"
    );
    let strip_proj = format!(
        concat!(
            "(@par_strips_witness_p_star.rec env x2 e0' ",
            "(fun (_w : par_strips_witness_p_star env x2 e0') => ",
            "par_strips_witness_p_star env e0'' x2) ",
            "(fun (m : KExpr) ",
            "(pe2m : par_reduces_p_star env x2 m) (pe1m : par_reduces_p_star env e0' m) => ",
            "{star_proj}) ",
            "(par_strips_p_star_strip env e0 x2 e0' ",
            "w disjoint closed liftclosed hx2 hstep))"
        ),
        star_proj = star_proj,
    );
    let step_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e0' : KExpr) (e0'' : KExpr) ",
            "(hstep : par_reduces_p env e0 e0') ",
            "(_htail : par_reduces_p_star env e0' e0'') ",
            "(ih : forall (x : KExpr), par_reduces_p_star env e0' x -> ",
            "par_strips_witness_p_star env e0'' x) => ",
            "fun (x2 : KExpr) (hx2 : par_reduces_p_star env e0 x2) => ",
            "{strip_proj})"
        ),
        strip_proj = strip_proj,
    );
    format!(
        concat!(
            "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
            "(w : RecEnvReductNotRedex env) (disjoint : RecEnvCtorNoRecMeta env) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
            "(h1 : par_reduces_p_star env e e1) (h2 : par_reduces_p_star env e e2) => ",
            "par_reduces_p_star.rec env {motive} {refl_arm} {step_arm} ",
            "e e1 h1 e2 h2"
        ),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Closed proof term for `par_reduces_c_star_diamond` (par_reduces_c_star
/// CHURCH–ROSSER) — the star-level sandwich. Lift both par_reduces_c_star legs into
/// par_reduces_p_star (`par_reduces_c_star_subsumes_par_p_star`), confluence-join via
/// `par_reduces_p_star_diamond`, project the par_strips_witness_p_star reduct, and
/// bridge each leg back to par_reduces_c_star (`par_reduces_p_star_subsumes_par_c_star`),
/// packaging `par_strips_witness_c_star`. Carries the four faithful interfaces.
fn par_reduces_c_star_diamond_proof() -> String {
    concat!(
        "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
        "(w : RecEnvReductNotRedex env) (disjoint : RecEnvCtorNoRecMeta env) ",
        "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
        "(h1 : par_reduces_c_star env e e1) (h2 : par_reduces_c_star env e e2) => ",
        "@par_strips_witness_p_star.rec env e1 e2 ",
        "(fun (_w : par_strips_witness_p_star env e1 e2) => par_strips_witness_c_star env e1 e2) ",
        "(fun (e3 : KExpr) ",
        "(l1 : par_reduces_p_star env e1 e3) (l2 : par_reduces_p_star env e2 e3) => ",
        "par_strips_witness_c_star.intro env e1 e2 e3 ",
        "(par_reduces_p_star_subsumes_par_c_star env e1 e3 l1) ",
        "(par_reduces_p_star_subsumes_par_c_star env e2 e3 l2)) ",
        "(par_reduces_p_star_diamond env e e1 e2 w disjoint closed liftclosed ",
        "(par_reduces_c_star_subsumes_par_p_star env e e1 h1) ",
        "(par_reduces_c_star_subsumes_par_p_star env e e2 h2))"
    )
    .to_string()
}

/// Closed proof term for `dev_triangle` — induction on the `par_reduces_p` derivation
/// (motive `M e a := par_reduces_p a (dev e)`). The 8 arms delegate to dev_self /
/// dev_kbeta / dev_kcong / the binder congruences / iota_redex_tri + topIotaStar_dev.
fn dev_triangle_proof() -> String {
    let m_at = |x: &str, y: &str| -> String { format!("par_reduces_p env {y} (dev env {x})") };
    let motive = "(fun (e : KExpr) (a : KExpr) (_h : par_reduces_p env e a) => par_reduces_p env a (dev env e))";

    let refl_arm = "(fun (e : KExpr) => dev_self env e)";

    let beta_arm = format!(
        "(fun (A : KExpr) (Ap : KExpr) (body : KExpr) (bodyp : KExpr) (arg : KExpr) (argp : KExpr) \
         (hA : par_reduces_p env A Ap) (hbody : par_reduces_p env body bodyp) (harg : par_reduces_p env arg argp) \
         (ihA : {mA}) (ihbody : {mbody}) (iharg : {marg}) => \
         dev_kbeta env A body arg bodyp argp ihbody iharg closed liftclosed)",
        mA = m_at("A", "Ap"),
        mbody = m_at("body", "bodyp"),
        marg = m_at("arg", "argp"),
    );

    let app_arm = format!(
        "(fun (f : KExpr) (fp : KExpr) (a : KExpr) (ap : KExpr) \
         (hf : par_reduces_p env f fp) (ha : par_reduces_p env a ap) \
         (ihf : {mf}) (iha : {ma}) => \
         dev_kcong env f fp a ap hf ha ihf iha)",
        mf = m_at("f", "fp"),
        ma = m_at("a", "ap"),
    );

    let lam_arm = format!(
        "(fun (ty : KExpr) (typ : KExpr) (body : KExpr) (bodyp : KExpr) \
         (hty : par_reduces_p env ty typ) (hbody : par_reduces_p env body bodyp) \
         (ihty : {mty}) (ihbody : {mbody}) => \
         Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env (KExpr.lam typ bodyp) x) \
         (KExpr.lam (dev env ty) (dev env body)) (dev env (KExpr.lam ty body)) \
         (Eq.symm KExpr (dev env (KExpr.lam ty body)) (KExpr.lam (dev env ty) (dev env body)) (dev_lam env ty body)) \
         (par_reduces_p.lam env typ (dev env ty) bodyp (dev env body) ihty ihbody))",
        mty = m_at("ty", "typ"),
        mbody = m_at("body", "bodyp"),
    );

    let pi_arm = format!(
        "(fun (dom : KExpr) (domp : KExpr) (body : KExpr) (bodyp : KExpr) \
         (hd : par_reduces_p env dom domp) (hbody : par_reduces_p env body bodyp) \
         (ihd : {md}) (ihbody : {mbody}) => \
         Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env (KExpr.pi domp bodyp) x) \
         (KExpr.pi (dev env dom) (dev env body)) (dev env (KExpr.pi dom body)) \
         (Eq.symm KExpr (dev env (KExpr.pi dom body)) (KExpr.pi (dev env dom) (dev env body)) (dev_pi env dom body)) \
         (par_reduces_p.pi env domp (dev env dom) bodyp (dev env body) ihd ihbody))",
        md = m_at("dom", "domp"),
        mbody = m_at("body", "bodyp"),
    );

    let forall_arm = format!(
        "(fun (dom : KExpr) (domp : KExpr) (body : KExpr) (bodyp : KExpr) \
         (hd : par_reduces_p env dom domp) (hbody : par_reduces_p env body bodyp) \
         (ihd : {md}) (ihbody : {mbody}) => \
         par_reduces_p.forall_ env domp (dev env dom) bodyp (dev env body) ihd ihbody)",
        md = m_at("dom", "domp"),
        mbody = m_at("body", "bodyp"),
    );

    // let_ arm (ZETA ctor: source let_ lt lv lb, target instantiate lbp lvp). Genuine
    // let-constructor reasoning (the OLD alias let_ = app(lam) is gone): dev (let_ lt lv
    // lb) = topIotaStar (instantiate (dev lb)(dev lv)) (dev_let); par_subst_p at depth 0
    // lands instantiate lbp lvp ⇒_p instantiate (dev lb)(dev lv) from ihlb/ihlv, then
    // par_topIotaStar lifts to the topIotaStar, transported via dev_let. (The type IH ihlt
    // is dropped, exactly as the beta arm drops the lam-annotation IH.)
    let let_arm = format!(
        "(fun (lt : KExpr) (ltp : KExpr) (lv : KExpr) (lvp : KExpr) (lb : KExpr) (lbp : KExpr) \
         (hlt : par_reduces_p env lt ltp) (hlv : par_reduces_p env lv lvp) (hlb : par_reduces_p env lb lbp) \
         (ihlt : {mlt}) (ihlv : {mlv}) (ihlb : {mlb}) => \
         Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env (instantiate lbp lvp) x) \
         (topIotaStar env (instantiate (dev env lb) (dev env lv))) (dev env (KExpr.let_ lt lv lb)) \
         (Eq.symm KExpr (dev env (KExpr.let_ lt lv lb)) (topIotaStar env (instantiate (dev env lb) (dev env lv))) (dev_let env lt lv lb)) \
         (par_topIotaStar env (instantiate lbp lvp) (instantiate (dev env lb) (dev env lv)) \
         (par_subst_p env lbp (dev env lb) lvp (dev env lv) Nat.zero ihlb ihlv closed liftclosed)))",
        mlt = m_at("lt", "ltp"),
        mlv = m_at("lv", "lvp"),
        mlb = m_at("lb", "lbp"),
    );

    // let_cong arm (the NEW trailing congruence ctor: source let_ lt lv lb, target let_
    // ltp lvp lbp). The reduct let_ ltp lvp lbp fires the zeta the development took —
    // par_reduces_p.let_ (ZETA) on ihlt/ihlv/ihlb lands it at instantiate (dev lb)(dev
    // lv), par_topIotaStar lifts to the topIotaStar, transported via dev_let. (Mirrors
    // ConfZeta SORRY 4: `rw [dev_let]; apply par_getD_iota; exact .zeta ihv ihb`.)
    let let_cong_arm = format!(
        "(fun (lt : KExpr) (ltp : KExpr) (lv : KExpr) (lvp : KExpr) (lb : KExpr) (lbp : KExpr) \
         (hlt : par_reduces_p env lt ltp) (hlv : par_reduces_p env lv lvp) (hlb : par_reduces_p env lb lbp) \
         (ihlt : {mlt}) (ihlv : {mlv}) (ihlb : {mlb}) => \
         Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env (KExpr.let_ ltp lvp lbp) x) \
         (topIotaStar env (instantiate (dev env lb) (dev env lv))) (dev env (KExpr.let_ lt lv lb)) \
         (Eq.symm KExpr (dev env (KExpr.let_ lt lv lb)) (topIotaStar env (instantiate (dev env lb) (dev env lv))) (dev_let env lt lv lb)) \
         (par_topIotaStar env (KExpr.let_ ltp lvp lbp) (instantiate (dev env lb) (dev env lv)) \
         (par_reduces_p.let_ env ltp (dev env lt) lvp (dev env lv) lbp (dev env lb) ihlt ihlv ihlb)))",
        mlt = m_at("lt", "ltp"),
        mlv = m_at("lv", "lvp"),
        mlb = m_at("lb", "lbp"),
    );

    let iota_arm = format!(
        "(fun (e : KExpr) (e2 : KExpr) (tf : KExpr) \
         (he : par_reduces_p env e e2) (hi : iota_step env e2 tf) \
         (ihe : {me}) => \
         Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p env tf Z) \
         (topIotaStar env (dev env e)) (dev env e) (topIotaStar_dev env e w) \
         (iota_redex_tri env e2 tf (dev env e) w disjoint hi ihe))",
        me = m_at("e", "e2"),
    );

    // proj arm: dev descends into the scrutinee (dev env (proj s i sub) = proj s i
    // (dev env sub) by defeq); congruence via par_reduces_p.proj on the IH.
    let proj_arm = format!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (subp : KExpr) \
         (hsub : par_reduces_p env sub subp) (ihsub : {msub}) => \
         par_reduces_p.proj env s i subp (dev env sub) ihsub)",
        msub = m_at("sub", "subp"),
    );

    format!(
        "fun (env : RecEnv) (E0 : KExpr) (A0 : KExpr) \
         (w : RecEnvReductNotRedex env) (disjoint : RecEnvCtorNoRecMeta env) \
         (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) \
         (hpar : par_reduces_p env E0 A0) => \
         par_reduces_p.rec env {motive} \
         {refl_arm} {beta_arm} {app_arm} {lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} \
         E0 A0 hpar"
    )
}

/// Closed proof term for `dev_kbeta` — par_subst_p (depth 0) + par_topIotaStar,
/// transported to `dev (app (lam A body) a)` via `dev_app_lam`.
fn dev_kbeta_proof() -> String {
    "fun (env : RecEnv) (A : KExpr) (body : KExpr) (a : KExpr) (body' : KExpr) (arg' : KExpr) \
     (hbody : par_reduces_p env body' (dev env body)) (harg : par_reduces_p env arg' (dev env a)) \
     (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => \
     Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env (instantiate body' arg') x) \
     (topIotaStar env (instantiate (dev env body) (dev env a))) (dev env (KExpr.app (KExpr.lam A body) a)) \
     (Eq.symm KExpr (dev env (KExpr.app (KExpr.lam A body) a)) (topIotaStar env (instantiate (dev env body) (dev env a))) (dev_app_lam env A body a)) \
     (par_topIotaStar env (instantiate body' arg') (instantiate (dev env body) (dev env a)) \
     (par_subst_p env body' (dev env body) arg' (dev env a) Nat.zero hbody harg closed liftclosed))"
        .to_string()
}

/// Closed proof term for `dev_kcong` — mirror of `par_reduces_p_app_dev_proof` with
/// cd -> dev, the false branch using `par_topIotaStar` (no convoy) and the lam branch
/// `par_topIotaStar`-wrapping the beta + transporting via `dev_app_lam`.
fn dev_kcong_proof() -> String {
    let app_cong = "(par_reduces_p.app env f' (dev env f) a' (dev env a) hf' ha')";

    // FALSE branch: dev (app f a) = topIotaStar (app (dev f)(dev a)); par_topIotaStar lifts.
    let dev_false_val = "(topIotaStar env (KExpr.app (dev env f) (dev env a)))";
    let eq_dev_false = "(Eq.subst Bool \
         (fun (bcond : Bool) => Eq KExpr (dev env (KExpr.app f a)) \
         (Bool.rec (fun (_ : Bool) => KExpr) \
         (topIotaStar env (KExpr.app (dev env f) (dev env a))) \
         (topIotaStar env (instantiate (kexpr_lam_body (dev env f)) (dev env a))) bcond)) \
         (kexpr_is_lam f) Bool.false hfalse (dev_app env f a))"
        .to_string();
    let false_branch = format!(
        "(fun (hfalse : Eq Bool (kexpr_is_lam f) Bool.false) => \
         Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env (KExpr.app f' a') x) \
         {dev_false_val} (dev env (KExpr.app f a)) \
         (Eq.symm KExpr (dev env (KExpr.app f a)) {dev_false_val} {eq_dev_false}) \
         (par_topIotaStar env (KExpr.app f' a') (KExpr.app (dev env f) (dev env a)) {app_cong}))"
    );

    // LAM branch (f = lam A b0): double par_reduces_p_lam_inv (cd -> dev), then
    // par_topIotaStar + dev_app_lam.
    let hf_lam = "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x f') f (KExpr.lam A b0) hflam hf)";
    let hf_dev_lam = "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env f' x) \
         (dev env f) (KExpr.lam (dev env A) (dev env b0)) \
         (Eq.substType KExpr (fun (g : KExpr) => Eq KExpr (dev env g) (KExpr.lam (dev env A) (dev env b0))) \
         (KExpr.lam A b0) f (Eq.symm KExpr f (KExpr.lam A b0) hflam) (dev_lam env A b0)) \
         hf')";
    let beta_fire =
        "(par_reduces_p.beta env A' (dev env A) b0' (dev env b0) a' (dev env a) hA'devA hb0'devb0 ha')";
    let klam2 = format!(
        "(fun (ty2 : KExpr) (body2 : KExpr) \
         (hty2 : par_reduces_p env A' ty2) (hbody2 : par_reduces_p env b0' body2) \
         (zeq2 : Eq KExpr (KExpr.lam ty2 body2) (KExpr.lam (dev env A) (dev env b0))) => \
         (fun (hA'devA : par_reduces_p env A' (dev env A)) (hb0'devb0 : par_reduces_p env b0' (dev env b0)) => \
         {beta_fire}) \
         (Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env A' x) ty2 (dev env A) \
         (lam_inj_fst ty2 body2 (dev env A) (dev env b0) zeq2) hty2) \
         (Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env b0' x) body2 (dev env b0) \
         (lam_inj_snd ty2 body2 (dev env A) (dev env b0) zeq2) hbody2))"
    );
    let klam1 = format!(
        "(fun (A' : KExpr) (b0' : KExpr) \
         (hA : par_reduces_p env A A') (hb0 : par_reduces_p env b0 b0') \
         (zeq1 : Eq KExpr (KExpr.lam A' b0') f') => \
         Eq.substType KExpr (fun (g : KExpr) => par_reduces_p env (KExpr.app g a') (instantiate (dev env b0) (dev env a))) \
         (KExpr.lam A' b0') f' zeq1 \
         (par_reduces_p_lam_inv env A' b0' (KExpr.lam (dev env A) (dev env b0)) \
         (fun (z : KExpr) => Eq KExpr z (KExpr.lam (dev env A) (dev env b0)) -> par_reduces_p env (KExpr.app (KExpr.lam A' b0') a') (instantiate (dev env b0) (dev env a))) \
         (Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x (KExpr.lam (dev env A) (dev env b0))) \
         f' (KExpr.lam A' b0') (Eq.symm KExpr (KExpr.lam A' b0') f' zeq1) {hf_dev_lam}) \
         {klam2} \
         (Eq.refl KExpr (KExpr.lam (dev env A) (dev env b0)))))"
    );
    let beta_goal_proof = format!(
        "(par_reduces_p_lam_inv env A b0 f' \
         (fun (z : KExpr) => Eq KExpr z f' -> par_reduces_p env (KExpr.app f' a') (instantiate (dev env b0) (dev env a))) \
         {hf_lam} {klam1} (Eq.refl KExpr f'))"
    );
    let p_lam = format!(
        "(Eq.substType KExpr \
         (fun (x : KExpr) => par_reduces_p env (KExpr.app f' a') x) \
         (topIotaStar env (instantiate (dev env b0) (dev env a))) (dev env (KExpr.app (KExpr.lam A b0) a)) \
         (Eq.symm KExpr (dev env (KExpr.app (KExpr.lam A b0) a)) (topIotaStar env (instantiate (dev env b0) (dev env a))) (dev_app_lam env A b0 a)) \
         (par_topIotaStar env (KExpr.app f' a') (instantiate (dev env b0) (dev env a)) {beta_goal_proof}))"
    );
    let lam_branch = format!(
        "(fun (A : KExpr) (b0 : KExpr) (hflam : Eq KExpr f (KExpr.lam A b0)) => \
         Eq.substType KExpr \
         (fun (g : KExpr) => par_reduces_p env (KExpr.app f' a') (dev env (KExpr.app g a))) \
         (KExpr.lam A b0) f \
         (Eq.symm KExpr f (KExpr.lam A b0) hflam) \
         {p_lam})"
    );

    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
         (hf : par_reduces_p env f f') (ha : par_reduces_p env a a') \
         (hf' : par_reduces_p env f' (dev env f)) (ha' : par_reduces_p env a' (dev env a)) => \
         kexpr_lam_cases f (par_reduces_p env (KExpr.app f' a') (dev env (KExpr.app f a))) \
         {lam_branch} {false_branch}"
    )
}

/// Closed proof term for `dev_self`. Structural `KExpr.rec` over `e0`, mirroring
/// `cd_refl_proof` with cd -> dev, the cd_lam/cd_pi unfolds -> dev_lam/dev_pi, and
/// the app arm `par_topIotaStar`-wrapped on both branches (dev's extra top fire).
fn dev_self_proof() -> String {
    let motive = "(fun (e : KExpr) => par_reduces_p env e (dev env e))";
    let sort_arm = "(fun (n : Level) => par_reduces_p.refl env (KExpr.sort n))";
    let bvar_arm = "(fun (i : Nat) => par_reduces_p.refl env (KExpr.bvar i))";
    let const_arm =
        "(fun (nm : Name) (us : ListType Level) => par_reduces_p.refl env (KExpr.const nm us))";

    // lam/pi binder arm: dev env (HEAD ty b) = HEAD (dev ty)(dev b) (dev_lam/dev_pi).
    let binder_arm = |ctor: &str, head: &str, unfold: &str| -> String {
        format!(
            "(fun (ty : KExpr) (b : KExpr) \
             (ihty : par_reduces_p env ty (dev env ty)) (ihb : par_reduces_p env b (dev env b)) => \
             Eq.substType KExpr \
             (fun (x : KExpr) => par_reduces_p env ({head} ty b) x) \
             ({head} (dev env ty) (dev env b)) (dev env ({head} ty b)) \
             (Eq.symm KExpr (dev env ({head} ty b)) ({head} (dev env ty) (dev env b)) ({unfold} env ty b)) \
             ({ctor} env ty (dev env ty) b (dev env b) ihty ihb))"
        )
    };

    // ---- app arm ----
    let app_cong = "(par_reduces_p.app env f (dev env f) a (dev env a) ihf iha)";

    // FALSE branch: dev (app f a) = topIotaStar (app (dev f)(dev a)) (dev_app + hfalse),
    // then par_topIotaStar of the app congruence.
    let dev_false_val = "(topIotaStar env (KExpr.app (dev env f) (dev env a)))";
    let eq_dev_false = "(Eq.subst Bool \
         (fun (bcond : Bool) => Eq KExpr (dev env (KExpr.app f a)) \
         (Bool.rec (fun (_ : Bool) => KExpr) \
         (topIotaStar env (KExpr.app (dev env f) (dev env a))) \
         (topIotaStar env (instantiate (kexpr_lam_body (dev env f)) (dev env a))) bcond)) \
         (kexpr_is_lam f) Bool.false hfalse (dev_app env f a))"
        .to_string();
    let false_branch = format!(
        "(fun (hfalse : Eq Bool (kexpr_is_lam f) Bool.false) => \
         Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env (KExpr.app f a) x) \
         {dev_false_val} (dev env (KExpr.app f a)) \
         (Eq.symm KExpr (dev env (KExpr.app f a)) {dev_false_val} {eq_dev_false}) \
         (par_topIotaStar env (KExpr.app f a) (KExpr.app (dev env f) (dev env a)) {app_cong}))"
    );

    // LAM branch (f = lam A b0): build the beta to instantiate (dev b0)(dev a), then
    // par_topIotaStar, transported to dev (app (lam A b0) a) via dev_app_lam.
    let ihf_lam = "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env (KExpr.lam A b0) x) \
         (dev env (KExpr.lam A b0)) (KExpr.lam (dev env A) (dev env b0)) (dev_lam env A b0) \
         (Eq.substType KExpr (fun (g : KExpr) => par_reduces_p env g (dev env g)) f (KExpr.lam A b0) hf ihf))";
    let beta_reduct = "(instantiate (dev env b0) (dev env a))";
    let beta_goal = format!("(par_reduces_p env (KExpr.app (KExpr.lam A b0) a) {beta_reduct})");
    let klam_inv = "(fun (ty2 : KExpr) (body2 : KExpr) \
         (hty2 : par_reduces_p env A ty2) (hbody2 : par_reduces_p env b0 body2) \
         (zeq : Eq KExpr (KExpr.lam ty2 body2) (KExpr.lam (dev env A) (dev env b0))) => \
         par_reduces_p.beta env A (dev env A) b0 (dev env b0) a (dev env a) \
         (Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env A x) ty2 (dev env A) \
         (lam_inj_fst ty2 body2 (dev env A) (dev env b0) zeq) hty2) \
         (Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env b0 x) body2 (dev env b0) \
         (lam_inj_snd ty2 body2 (dev env A) (dev env b0) zeq) hbody2) \
         iha)";
    let beta_p = format!(
        "(par_reduces_p_lam_inv env A b0 (KExpr.lam (dev env A) (dev env b0)) \
         (fun (z : KExpr) => Eq KExpr z (KExpr.lam (dev env A) (dev env b0)) -> {beta_goal}) \
         {ihf_lam} {klam_inv} \
         (Eq.refl KExpr (KExpr.lam (dev env A) (dev env b0))))"
    );
    let dev_lam_target = "(topIotaStar env (instantiate (dev env b0) (dev env a)))";
    let p_lam = format!(
        "(Eq.substType KExpr \
         (fun (x : KExpr) => par_reduces_p env (KExpr.app (KExpr.lam A b0) a) x) \
         {dev_lam_target} (dev env (KExpr.app (KExpr.lam A b0) a)) \
         (Eq.symm KExpr (dev env (KExpr.app (KExpr.lam A b0) a)) {dev_lam_target} (dev_app_lam env A b0 a)) \
         (par_topIotaStar env (KExpr.app (KExpr.lam A b0) a) {beta_reduct} {beta_p}))"
    );
    let lam_branch = format!(
        "(fun (A : KExpr) (b0 : KExpr) (hf : Eq KExpr f (KExpr.lam A b0)) => \
         Eq.substType KExpr \
         (fun (g : KExpr) => par_reduces_p env (KExpr.app g a) (dev env (KExpr.app g a))) \
         (KExpr.lam A b0) f \
         (Eq.symm KExpr f (KExpr.lam A b0) hf) \
         {p_lam})"
    );

    let app_arm = format!(
        "(fun (f : KExpr) (a : KExpr) \
         (ihf : par_reduces_p env f (dev env f)) (iha : par_reduces_p env a (dev env a)) => \
         kexpr_lam_cases f (par_reduces_p env (KExpr.app f a) (dev env (KExpr.app f a))) \
         {lam_branch} {false_branch})"
    );

    // ---- let_ arm ----
    // dev (let_ lt lv lb) = topIotaStar (instantiate (dev lb)(dev lv)) (dev_let). Fire the
    // zeta directly on the IHs (par_reduces_p.let_ — no inversion needed, the recursor
    // hands us lt/lv/lb and their dev-IHs), then par_topIotaStar, transported via dev_let.
    let let_arm = "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) \
         (ihlt : par_reduces_p env lt (dev env lt)) (ihlv : par_reduces_p env lv (dev env lv)) \
         (ihlb : par_reduces_p env lb (dev env lb)) => \
         Eq.substType KExpr \
         (fun (x : KExpr) => par_reduces_p env (KExpr.let_ lt lv lb) x) \
         (topIotaStar env (instantiate (dev env lb) (dev env lv))) (dev env (KExpr.let_ lt lv lb)) \
         (Eq.symm KExpr (dev env (KExpr.let_ lt lv lb)) (topIotaStar env (instantiate (dev env lb) (dev env lv))) (dev_let env lt lv lb)) \
         (par_topIotaStar env (KExpr.let_ lt lv lb) (instantiate (dev env lb) (dev env lv)) \
         (par_reduces_p.let_ env lt (dev env lt) lv (dev env lv) lb (dev env lb) ihlt ihlv ihlb)))"
        .to_string();

    // proj arm: dev descends into the scrutinee (defeq); congruence via par_reduces_p.proj.
    let proj_arm = "(fun (s : Name) (i : Nat) (sub : KExpr) \
         (ihsub : par_reduces_p env sub (dev env sub)) => \
         par_reduces_p.proj env s i sub (dev env sub) ihsub)"
        .to_string();
    // lit arm: dev env (lit v) = lit v (defeq); reflexive par-step.
    let lit_arm = "(fun (v : Nat) => par_reduces_p.refl env (KExpr.lit v))".to_string();

    format!(
        "fun (env : RecEnv) (e0 : KExpr) => \
         KExpr.rec {motive} \
         {sort_arm} {bvar_arm} {app_arm} \
         {lam_arm} {pi_arm} {const_arm} {let_arm} {proj_arm} {lit_arm} \
         e0",
        lam_arm = binder_arm("par_reduces_p.lam", "KExpr.lam", "dev_lam"),
        pi_arm = binder_arm("par_reduces_p.pi", "KExpr.pi", "dev_pi"),
        let_arm = let_arm,
        proj_arm = proj_arm,
        lit_arm = lit_arm,
    )
}

/// Closed proof term for `app_redex_tri` — the app-arm content of the iota triangle,
/// isolated as a standalone (NON-inductive) lemma. Outer `OptionType.rec` convoy on
/// `iota_reduct env f`: the none arm is the MINIMAL/boundary case (keystone reduct
/// congruence + reduct reconstruction), the some arm is the OVER-application case
/// (the f-IH supplies the inner reduct congruence, replacing the marked fuel).
fn app_redex_tri_proof() -> String {
    let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
    let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
    // The (app f a)-side reduct R_fa (matches iota_reduct_app_minimal_boundary_idx_type's
    // reduct_app and par_reduces_p_reduct_cong's r_fa) and the (app f' a')-side reduct
    // reduct_m (matches par_reduces_p_reduct_cong / par_reduces_p_app_redex's output).
    let r_fa = format!(
        "(apply_spine (list_drop (Nat.succ {major_idx}) (kapp_args (KExpr.app f a))) \
         (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) \
         (apply_spine (list_take {prefix_n} (kapp_args (KExpr.app f a))) (recrule_rhs rule))))"
    );
    let reduct_m = format!(
        "(apply_spine (list_drop (Nat.succ {major_idx}) (kapp_args (KExpr.app f' a'))) \
         (apply_spine (list_drop (Nat.sub (list_length (kapp_args a')) (recrule_num_fields rule)) (kapp_args a')) \
         (apply_spine (list_take {prefix_n} (kapp_args (KExpr.app f' a'))) (recrule_rhs rule))))"
    );
    let goal = "(par_reduces_p env r (topIotaStar env (KExpr.app f' a')))";

    // ---- MINIMAL (iota_reduct f = none) arm ----
    let left_leg = "(par_reduces_p_reduct_cong env f f' a a' r recname meta major cname rule \
         disjoint h1 h2 h4 h5 h5r hbnd hidx hf ha)";
    let right_recon = "(par_reduces_p_app_redex env f f' a a' recname meta major cname rule \
         disjoint h1 h2 h4 h5 hbnd hidx hf ha)";
    let minimal_body = format!(
        "(Eq.substType (OptionType KExpr) \
         (fun (o : OptionType KExpr) => par_reduces_p env r (opt_default o (KExpr.app f' a'))) \
         (OptionType.some KExpr {reduct_m}) (iota_reduct env (KExpr.app f' a')) \
         (Eq.symm (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr {reduct_m}) {right_recon}) \
         {left_leg})"
    );
    let none_arm = format!(
        "(fun (hfnone : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) => \
         iota_reduct_app_minimal_boundary_idx_type env f a r hr hfnone {goal} \
         (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
         (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
         (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
         (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args (KExpr.app f a)))) (OptionType.some KExpr major)) \
         (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
         (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
         (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {r_fa}) (OptionType.some KExpr r)) \
         (hbnd : Eq KExpr major a) \
         (hidx : Eq Nat {major_idx} (list_length (kapp_args f))) => \
         {minimal_body}))"
    );

    // ---- OVER-application (iota_reduct f = some f1) arm ----
    let happ_src = "(iota_reduct_app_some env f a f1 hf1)";
    let r_eq = format!(
        "(option_some_inj KExpr (KExpr.app f1 a) r \
         (Eq.trans (OptionType KExpr) (OptionType.some KExpr (KExpr.app f1 a)) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr r) \
         (Eq.symm (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr (KExpr.app f1 a)) {happ_src}) hr))"
    );
    let ihfres = "(ihf f1 hf1)";
    // none' subcase: iota_reduct f' = none, topIotaStar f' = f', par_topIotaStar absorbs.
    let f1_to_fp = format!(
        "(Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p env f1 Z) (topIotaStar env f') f' \
         (topIotaStar_fix env f' hfpnone) {ihfres})"
    );
    let appcong_none = format!("(par_reduces_p.app env f1 f' a a' {f1_to_fp} ha)");
    let lift_none =
        format!("(par_topIotaStar env (KExpr.app f1 a) (KExpr.app f' a') {appcong_none})");
    let nonep_body = format!(
        "(Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p env Z (topIotaStar env (KExpr.app f' a'))) \
         (KExpr.app f1 a) r {r_eq} {lift_none})"
    );
    // some' subcase: iota_reduct f' = some f1', topIotaStar (app f' a') = app f1' a'.
    let eq_tifp = "(Eq.cong (OptionType KExpr) KExpr (fun (o : OptionType KExpr) => opt_default o f') (iota_reduct env f') (OptionType.some KExpr f1p) hf1p)";
    let f1_to_f1p = format!(
        "(Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p env f1 Z) (topIotaStar env f') f1p {eq_tifp} {ihfres})"
    );
    let happ_tgt = "(iota_reduct_app_some env f' a' f1p hf1p)";
    let appcong_some = format!("(par_reduces_p.app env f1 f1p a a' {f1_to_f1p} ha)");
    let r_to_f1p = format!(
        "(Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p env Z (KExpr.app f1p a')) (KExpr.app f1 a) r {r_eq} {appcong_some})"
    );
    let somep_body = format!(
        "(Eq.substType (OptionType KExpr) \
         (fun (o : OptionType KExpr) => par_reduces_p env r (opt_default o (KExpr.app f' a'))) \
         (OptionType.some KExpr (KExpr.app f1p a')) (iota_reduct env (KExpr.app f' a')) \
         (Eq.symm (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr (KExpr.app f1p a')) {happ_tgt}) \
         {r_to_f1p})"
    );
    let some_arm = format!(
        "(fun (f1 : KExpr) (hf1 : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1)) => \
         OptionType.rec KExpr \
         (fun (ofp : OptionType KExpr) => Eq (OptionType KExpr) (iota_reduct env f') ofp -> {goal}) \
         (fun (hfpnone : Eq (OptionType KExpr) (iota_reduct env f') (OptionType.none KExpr)) => {nonep_body}) \
         (fun (f1p : KExpr) (hf1p : Eq (OptionType KExpr) (iota_reduct env f') (OptionType.some KExpr f1p)) => {somep_body}) \
         (iota_reduct env f') \
         (Eq.refl (OptionType KExpr) (iota_reduct env f')))"
    );

    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (r : KExpr) \
         (disjoint : RecEnvCtorNoRecMeta env) \
         (ihf : forall (rf : KExpr), Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr rf) -> par_reduces_p env rf (topIotaStar env f')) \
         (hf : par_reduces_p env f f') (ha : par_reduces_p env a a') \
         (hr : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr r)) => \
         OptionType.rec KExpr \
         (fun (of0 : OptionType KExpr) => Eq (OptionType KExpr) (iota_reduct env f) of0 -> {goal}) \
         {none_arm} \
         {some_arm} \
         (iota_reduct env f) \
         (Eq.refl (OptionType KExpr) (iota_reduct env f))"
    )
}

/// Closed proof term for `iota_redex_tri_aux` — induction on the `par_reduces_p`
/// derivation. The motive is the blueprint's: `forall r, iota_reduct env X = some r
/// -> par_reduces_p r (topIotaStar t)`. 9 arms (refl / beta / app / lam / pi / forall_
/// / let_ / iota_p / let_cong): refl computes `topIotaStar X = r`; the app arm delegates
/// to `app_redex_tri` (the recursor f-IH IS app_redex_tri's ihf); the iota_p arm
/// telescopes via `topIotaStar_step`; the six binder/beta/let arms (beta, lam, pi,
/// forall_, let_ ZETA and let_cong) are vacuous (the source has a non-recursor head —
/// a let_ is its own spine head, so kexpr_const_name = none — discharged by
/// `iota_step_head_none_absurd_type` with a refl head-none witness).
fn iota_redex_tri_aux_proof() -> String {
    // M X t (applied to endpoints x,y): the per-IH / motive type.
    let m_at = |x: &str, y: &str| -> String {
        format!(
            "forall (rr : KExpr), Eq (OptionType KExpr) (iota_reduct env {x}) (OptionType.some KExpr rr) -> par_reduces_p env rr (topIotaStar env {y})"
        )
    };
    let motive = "(fun (X : KExpr) (t : KExpr) (_h : par_reduces_p env X t) => forall (rr : KExpr), Eq (OptionType KExpr) (iota_reduct env X) (OptionType.some KExpr rr) -> par_reduces_p env rr (topIotaStar env t))";

    // Type-valued head-none discharge for a vacuous (non-recursor-headed) source.
    let vacuous = |src: &str, tgt: &str| -> String {
        format!(
            "(fun (r : KExpr) (hr : Eq (OptionType KExpr) (iota_reduct env {src}) (OptionType.some KExpr r)) => \
             iota_step_head_none_absurd_type env {src} r \
             (par_reduces_p env r (topIotaStar env {tgt})) \
             (Eq.refl (OptionType Name) (OptionType.none Name)) hr)"
        )
    };

    // refl arm: topIotaStar env e = r (opt_default computation), transport refl r.
    let refl_arm = "(fun (e : KExpr) => \
         fun (r : KExpr) (hr : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr r)) => \
         Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p env r Z) r (topIotaStar env e) \
         (Eq.symm KExpr (topIotaStar env e) r \
         (Eq.cong (OptionType KExpr) KExpr (fun (o : OptionType KExpr) => opt_default o e) (iota_reduct env e) (OptionType.some KExpr r) hr)) \
         (par_reduces_p.refl env r))";

    // beta arm (vacuous).
    let beta_arm = format!(
        "(fun (A : KExpr) (Ap : KExpr) (body : KExpr) (bodyp : KExpr) (arg : KExpr) (argp : KExpr) \
         (hA : par_reduces_p env A Ap) (hbody : par_reduces_p env body bodyp) (harg : par_reduces_p env arg argp) \
         (ihA : {mA}) (ihbody : {mbody}) (iharg : {marg}) => \
         {disch})",
        mA = m_at("A", "Ap"),
        mbody = m_at("body", "bodyp"),
        marg = m_at("arg", "argp"),
        disch = vacuous("(KExpr.app (KExpr.lam A body) arg)", "(instantiate bodyp argp)"),
    );

    // app arm (delegated to app_redex_tri; the recursor f-IH IS its ihf).
    let app_arm = format!(
        "(fun (f : KExpr) (fp : KExpr) (a : KExpr) (ap : KExpr) \
         (hf : par_reduces_p env f fp) (ha : par_reduces_p env a ap) \
         (ihf : {mf}) (iha : {ma}) => \
         fun (r : KExpr) (hr : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr r)) => \
         app_redex_tri env f fp a ap r disjoint ihf hf ha hr)",
        mf = m_at("f", "fp"),
        ma = m_at("a", "ap"),
    );

    // lam / pi / forall_ arms (vacuous, two recursive premises).
    let binder_vac =
        |dctor_src: &str, tgt: &str, d0: &str, d0p: &str, b0: &str, b0p: &str| -> String {
            format!(
                "(fun ({d0} : KExpr) ({d0p} : KExpr) ({b0} : KExpr) ({b0p} : KExpr) \
                 (hd : par_reduces_p env {d0} {d0p}) (hb : par_reduces_p env {b0} {b0p}) \
                 (ihd : {mihd}) (ihb : {mihb}) => \
                 {disch})",
                mihd = m_at(d0, d0p),
                mihb = m_at(b0, b0p),
                disch = vacuous(dctor_src, tgt),
            )
        };
    let lam_arm = binder_vac(
        "(KExpr.lam ty tyb)",
        "(KExpr.lam typ tybp)",
        "ty",
        "typ",
        "tyb",
        "tybp",
    );
    let pi_arm = binder_vac(
        "(KExpr.pi dom domb)",
        "(KExpr.pi domp dombp)",
        "dom",
        "domp",
        "domb",
        "dombp",
    );
    let forall_arm = binder_vac(
        "(KExpr.forall_ fd fdb)",
        "(KExpr.forall_ fdp fdbp)",
        "fd",
        "fdp",
        "fdb",
        "fdbp",
    );

    // let_ arm (ZETA ctor, vacuous: source is a genuine let_ node whose spine head is
    // itself, so kexpr_const_name (kapp_fn (let_ ...)) = none — a let_ is NEVER an iota
    // redex, hence the some-r hypothesis is refuted). Three recursive premises; target
    // instantiate lbp lvp.
    let let_arm = format!(
        "(fun (lt : KExpr) (ltp : KExpr) (lv : KExpr) (lvp : KExpr) (lb : KExpr) (lbp : KExpr) \
         (hlt : par_reduces_p env lt ltp) (hlv : par_reduces_p env lv lvp) (hlb : par_reduces_p env lb lbp) \
         (ihlt : {mlt}) (ihlv : {mlv}) (ihlb : {mlb}) => \
         {disch})",
        mlt = m_at("lt", "ltp"),
        mlv = m_at("lv", "lvp"),
        mlb = m_at("lb", "lbp"),
        disch = vacuous("(KExpr.let_ lt lv lb)", "(instantiate lbp lvp)"),
    );

    // let_cong arm (the NEW trailing congruence ctor, also vacuous — SAME let_-headed
    // source, so again never an iota redex; only the target differs: KExpr.let_ ltp lvp
    // lbp). Three recursive premises.
    let let_cong_arm = format!(
        "(fun (lt : KExpr) (ltp : KExpr) (lv : KExpr) (lvp : KExpr) (lb : KExpr) (lbp : KExpr) \
         (hlt : par_reduces_p env lt ltp) (hlv : par_reduces_p env lv lvp) (hlb : par_reduces_p env lb lbp) \
         (ihlt : {mlt}) (ihlv : {mlv}) (ihlb : {mlb}) => \
         {disch})",
        mlt = m_at("lt", "ltp"),
        mlv = m_at("lv", "lvp"),
        mlb = m_at("lb", "lbp"),
        disch = vacuous("(KExpr.let_ lt lv lb)", "(KExpr.let_ ltp lvp lbp)"),
    );

    // iota_p arm: transport the IH along topIotaStar_step (off-by-one absorber).
    let iota_arm = format!(
        "(fun (e : KExpr) (e2 : KExpr) (tf : KExpr) \
         (he : par_reduces_p env e e2) (hi : iota_step env e2 tf) \
         (ihe : {me}) => \
         fun (r : KExpr) (hr : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr r)) => \
         Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p env r Z) (topIotaStar env e2) (topIotaStar env tf) \
         (topIotaStar_step env e2 tf w hi) \
         (ihe r hr))",
        me = m_at("e", "e2"),
    );

    // proj arm (vacuous — a proj is its own spine head, never an iota redex).
    let proj_arm = format!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (subp : KExpr) \
         (hsub : par_reduces_p env sub subp) (ihsub : {msub}) => \
         {disch})",
        msub = m_at("sub", "subp"),
        disch = vacuous("(KExpr.proj s i sub)", "(KExpr.proj s i subp)"),
    );

    format!(
        "fun (env : RecEnv) (X0 : KExpr) (t0 : KExpr) (w : RecEnvReductNotRedex env) (disjoint : RecEnvCtorNoRecMeta env) (hpar : par_reduces_p env X0 t0) => \
         par_reduces_p.rec env {motive} \
         {refl_arm} {beta_arm} {app_arm} {lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} \
         X0 t0 hpar"
    )
}
