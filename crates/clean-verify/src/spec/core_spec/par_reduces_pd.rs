// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H+ (#2859 computational-iota/delta track, DELTA INCREMENT Stage 3):
//! the PROPER (Takahashi) δ-extended parallel reduction `par_reduces_pd` — the
//! 3-way (β+ι+δ) sibling of `par_reduces_p` whose iota AND delta constructors
//! BAKE IN the parallel reduction of the redex subterms.
//!
//! `par_reduces_cd` (Stage 2, par_reduces_cd.rs) is the ATOMIC 3-way relation: its
//! iota/delta ctors carry the bare deterministic steps with subterms NOT further
//! reduced. As for `par_reduces_c` vs `par_reduces_p`, that makes the substitution
//! lemma 2-step and yields only the WEAK diamond. The Takahashi fix is the PARALLEL
//! iota/delta rules `iota_p` / `delta_p` that reduce the subterms BEFORE contracting
//! (exactly as `beta` does): `e ⇒_pd e2` (subterms par-reduce) then the deterministic
//! `iota_step (red_rec env) e2 r` / `delta_step (red_def env) e2 r` fires.
//!
//! This module is the 3-way mirror of `par_reduces_p.rs` over the combined product
//! env `RedEnv = RecEnv × DefEnv` (Stage 2's carrier), threading the `red_rec` /
//! `red_def` projections. Layer 1 lands the relation + its RT-closure + the join
//! witnesses + the basic combinators + the `par_reduces_cd ⊆ par_reduces_pd`
//! embedding (atomic iota/delta map to the parallel ctors with a reflexive premise).
//!
//! Runs AFTER `add_par_reduces_p_topdev` (so the whole β+ι development, the
//! `par_reduces_cd` relation + `RedEnv` + `RecEnvDefEnvDisjoint`, and the delta
//! substrate are all in scope). Part of #2859 (Increment H+, delta increment Stage 3).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_par_reduces_pd(&mut self) -> Result<(), SpecError> {
        self.add_par_reduces_pd_relation()?;
        self.add_par_reduces_pd_star()?;
        self.add_par_reduces_pd_embeddings()?;
        self.add_par_reduces_cd_star()?;
        self.add_par_reduces_pd_cd_star_bridges()?;
        self.add_par_reduces_pd_delta_substrate()?;
        Ok(())
    }

    /// Brick 6: the delta-arm substitution/lift bridges — `delta_step_lift_pd` /
    /// `delta_step_subst_pd` — lifting the Stage-1 delta E-core keystones
    /// (`delta_lift_commutes` / `delta_subst_commutes`) into SINGLE `par_reduces_pd`
    /// steps via the `delta_p` ctor with a reflexive premise. These are the exact
    /// delta_p arm ingredients the eventual 1-step substitution lemma `par_subst_pd`
    /// consumes (the δ analogues of `iota_step_subst_p`), and the first concrete
    /// demonstration that the Stage-1 delta substrate plugs into the proper 3-way
    /// relation. Threads the delta closure gates `DefEnvLiftClosed (red_def env)` /
    /// `DefEnvClosed (red_def env)`.
    fn add_par_reduces_pd_delta_substrate(&mut self) -> Result<(), SpecError> {
        // delta_step_lift_pd: under DefEnvLiftClosed (red_def env), a delta fire commutes
        // with lift_at, lifted to a single par_reduces_pd step. delta_lift_commutes gives
        // delta_step (red_def env) (lift e)(lift e'); delta_p (refl premise) reassembles.
        self.add_definition(SpecDefinition {
            name: "delta_step_lift_pd".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr) (c : Nat) (a : Nat), ",
                "DefEnvLiftClosed (red_def env) -> delta_step (red_def env) e e' -> ",
                "par_reduces_pd env (lift_at e c a) (lift_at e' c a)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e' : KExpr) (c : Nat) (a : Nat) ",
                    "(dliftclosed : DefEnvLiftClosed (red_def env)) (h : delta_step (red_def env) e e') => ",
                    "par_reduces_pd.delta_p env (lift_at e c a) (lift_at e c a) (lift_at e' c a) ",
                    "(par_reduces_pd.refl env (lift_at e c a)) ",
                    "(delta_lift_commutes (red_def env) e e' c a dliftclosed h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "delta-arm lift bridge for par_reduces_pd: under DefEnvLiftClosed (red_def env), a delta fire ",
                "delta_step (red_def env) e e' commutes with lift_at as a SINGLE par_reduces_pd step lift_at e c a ",
                "⇒_pd lift_at e' c a. delta_lift_commutes (Stage 1) lifts the fired delta to delta_step (red_def env) ",
                "(lift e)(lift e'); par_reduces_pd.delta_p with a reflexive premise reassembles. The δ analogue of ",
                "iota_step_subst_p's lift companion and a delta_p arm ingredient of the eventual par_subst_pd. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_pd".to_string(),
                "par_reduces_pd.delta_p".to_string(),
                "par_reduces_pd.refl".to_string(),
                "delta_lift_commutes".to_string(),
                "delta_step".to_string(),
                "DefEnvLiftClosed".to_string(),
                "red_def".to_string(),
                "lift_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_step_subst_pd: under DefEnvClosed (red_def env), a delta fire commutes
        // with instantiate_at, lifted to a single par_reduces_pd step. delta_subst_commutes
        // gives delta_step (red_def env) (inst e)(inst e'); delta_p (refl premise) reassembles.
        self.add_definition(SpecDefinition {
            name: "delta_step_subst_pd".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat), ",
                "DefEnvClosed (red_def env) -> delta_step (red_def env) e e' -> ",
                "par_reduces_pd env (instantiate_at e v d) (instantiate_at e' v d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat) ",
                    "(dclosed : DefEnvClosed (red_def env)) (h : delta_step (red_def env) e e') => ",
                    "par_reduces_pd.delta_p env (instantiate_at e v d) (instantiate_at e v d) (instantiate_at e' v d) ",
                    "(par_reduces_pd.refl env (instantiate_at e v d)) ",
                    "(delta_subst_commutes (red_def env) e e' v d dclosed h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "delta-arm substitution bridge for par_reduces_pd: under DefEnvClosed (red_def env), a delta fire ",
                "delta_step (red_def env) e e' commutes with instantiate_at as a SINGLE par_reduces_pd step ",
                "instantiate_at e v d ⇒_pd instantiate_at e' v d. delta_subst_commutes (Stage 1) lifts the fired ",
                "delta to delta_step (red_def env) (inst e v d)(inst e' v d); par_reduces_pd.delta_p with a reflexive ",
                "premise reassembles. The δ analogue of iota_step_subst_p and the delta_p arm ingredient of the ",
                "eventual 1-step substitution lemma par_subst_pd. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment H+, delta increment Stage 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_pd".to_string(),
                "par_reduces_pd.delta_p".to_string(),
                "par_reduces_pd.refl".to_string(),
                "delta_subst_commutes".to_string(),
                "delta_step".to_string(),
                "DefEnvClosed".to_string(),
                "red_def".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 1: the PROPER δ-extended parallel reduction `par_reduces_pd (env :
    /// RedEnv)` — the 8 `par_reduces_p` structural ctors PLUS the parallel `iota_p`
    /// (carrying `iota_step (red_rec env)`) AND `delta_p` (carrying `delta_step
    /// (red_def env)`) — and the single-step meeting-point package
    /// `par_strips_witness_pd`.
    fn add_par_reduces_pd_relation(&mut self) -> Result<(), SpecError> {
        // par_reduces_pd env: the proper (Takahashi) 3-way parallel reduction.
        // Identical to par_reduces_p plus a delta_p ctor; the two contraction ctors
        // bake in the subterm reduction (e ⇒_pd e2) before the deterministic fire.
        self.add_inductive(
            r"inductive par_reduces_pd (env : RedEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_pd env e e
| beta : forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr), par_reduces_pd env A A' → par_reduces_pd env body body' → par_reduces_pd env arg arg' → par_reduces_pd env (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')
| app : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), par_reduces_pd env f f' → par_reduces_pd env a a' → par_reduces_pd env (KExpr.app f a) (KExpr.app f' a')
| lam : forall (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_pd env ty ty' → par_reduces_pd env body body' → par_reduces_pd env (KExpr.lam ty body) (KExpr.lam ty' body')
| pi : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_pd env dom dom' → par_reduces_pd env body body' → par_reduces_pd env (KExpr.pi dom body) (KExpr.pi dom' body')
| forall_ : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_pd env dom dom' → par_reduces_pd env body body' → par_reduces_pd env (KExpr.forall_ dom body) (KExpr.forall_ dom' body')
| let_ : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_pd env ty ty' → par_reduces_pd env val val' → par_reduces_pd env body body' → par_reduces_pd env (KExpr.let_ ty val body) (instantiate body' val')
| iota_p : forall (e : KExpr) (e2 : KExpr) (r : KExpr), par_reduces_pd env e e2 → iota_step (red_rec env) e2 r → par_reduces_pd env e r
| delta_p : forall (e : KExpr) (e2 : KExpr) (r : KExpr), par_reduces_pd env e e2 → delta_step (red_def env) e2 r → par_reduces_pd env e r
| let_cong : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_pd env ty ty' → par_reduces_pd env val val' → par_reduces_pd env body body' → par_reduces_pd env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), par_reduces_pd env sub sub' → par_reduces_pd env (KExpr.proj s i sub) (KExpr.proj s i sub')",
            "par_reduces_pd env e e' — the PROPER (Takahashi) 3-way (β+ι+δ+ζ) parallel reduction over a \
             combined RedEnv. The par_reduces_p structural ctors (refl/beta/app/lam/pi/forall_ and the let_ \
             ZETA arm, whose target is instantiate body' val') PLUS a PARALLEL iota_p (par-reduce subterms e \
             ⇒_pd e2, then fire iota_step (red_rec env) e2 r), a PARALLEL delta_p (par-reduce subterms, then \
             fire delta_step (red_def env) e2 r), AND a trailing let_cong congruence (the non-contracting \
             sibling of let_: par-reduce ty/val/body componentwise into a genuine KExpr.let_ ty' val' body' \
             node). Baking in the sub-reductions makes the substitution lemma 1-step and is the route to the \
             STRONG single-step diamond (unlike the atomic par_reduces_cd). Part of #2859 (Increment H+, delta \
             increment Stage 3).",
        )?;

        // par_strips_witness_pd env: the single-step join witness (mirror of
        // par_strips_witness_p) — the endpoint of the eventual 3-way strong diamond.
        self.add_inductive(
            r"inductive par_strips_witness_pd (env : RedEnv) : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), par_reduces_pd env e1 e3 → par_reduces_pd env e2 e3 → par_strips_witness_pd env e1 e2",
            "par_strips_witness_pd env e1 e2 packages a common reduct e3 with par_reduces_pd env e1 e3 and \
             par_reduces_pd env e2 e3 — the SINGLE-step join witness for the proper 3-way relation. \
             Part of #2859 (Increment H+, delta increment Stage 3).",
        )?;

        Ok(())
    }

    /// Brick 2: the reflexive-transitive closure `par_reduces_pd_star`, the
    /// multi-step join witness, and the basic combinators (subsumes / trans /
    /// witness-to-star). Mechanical mirrors of the `par_reduces_p_star` substrate.
    fn add_par_reduces_pd_star(&mut self) -> Result<(), SpecError> {
        // par_reduces_pd_star: RT-closure of par_reduces_pd (mirror of par_reduces_p_star).
        self.add_inductive(
            r"inductive par_reduces_pd_star (env : RedEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_pd_star env e e
| step : forall (e : KExpr) (e' : KExpr) (e'' : KExpr), par_reduces_pd env e e' → par_reduces_pd_star env e' e'' → par_reduces_pd_star env e e''",
            "par_reduces_pd_star env e e'' — the reflexive-transitive closure of the proper 3-way parallel \
             reduction par_reduces_pd. The multi-step level the eventual 3-way confluence endpoint lives at. \
             Part of #2859 (Increment H+, delta increment Stage 3).",
        )?;

        // par_strips_witness_pd_star: the multi-step join witness (mirror of
        // par_strips_witness_p_star) — the strip lemma and multi-step diamond endpoint.
        self.add_inductive(
            r"inductive par_strips_witness_pd_star (env : RedEnv) : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), par_reduces_pd_star env e1 e3 → par_reduces_pd_star env e2 e3 → par_strips_witness_pd_star env e1 e2",
            "par_strips_witness_pd_star env e1 e2 packages a common reduct e3 with par_reduces_pd_star legs — \
             the multi-step join witness the eventual 3-way strip lemma and confluence theorem land at. \
             Part of #2859 (Increment H+, delta increment Stage 3).",
        )?;

        // par_subsumes_par_pd_star: single par_reduces_pd step embeds into the closure.
        self.add_definition(SpecDefinition {
            name: "par_subsumes_par_pd_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_pd env e e' -> par_reduces_pd_star env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e' : KExpr) (h : par_reduces_pd env e e') => ",
                    "par_reduces_pd_star.step env e e' e' h (par_reduces_pd_star.refl env e')"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Single-step par_reduces_pd embeds into par_reduces_pd_star (step with a refl tail). DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_pd".to_string(),
                "par_reduces_pd_star".to_string(),
                "par_reduces_pd_star.refl".to_string(),
                "par_reduces_pd_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_pd_star_trans: transitivity (mirror of par_reduces_p_star_trans).
        self.add_definition(SpecDefinition {
            name: "par_reduces_pd_star_trans".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), ",
                "par_reduces_pd_star env e1 e2 -> par_reduces_pd_star env e2 e3 -> ",
                "par_reduces_pd_star env e1 e3"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) ",
                    "(h1 : par_reduces_pd_star env e1 e2) (h2 : par_reduces_pd_star env e2 e3) => ",
                    "par_reduces_pd_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_pd_star env a b) => ",
                    "par_reduces_pd_star env b e3 -> par_reduces_pd_star env a e3) ",
                    "(fun (e : KExpr) (k : par_reduces_pd_star env e e3) => k) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces_pd env e e') ",
                    "(_htail : par_reduces_pd_star env e' e'') ",
                    "(ih : par_reduces_pd_star env e'' e3 -> par_reduces_pd_star env e' e3) ",
                    "(k : par_reduces_pd_star env e'' e3) => ",
                    "par_reduces_pd_star.step env e e' e3 hstep (ih k)) ",
                    "e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Transitivity of par_reduces_pd_star (par_reduces_pd_star.rec on the first chain, prefixing each step onto the extended tail). DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_pd".to_string(),
                "par_reduces_pd_star".to_string(),
                "par_reduces_pd_star.rec".to_string(),
                "par_reduces_pd_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_witness_pd_to_star: lift a single-step join to a multi-step join.
        self.add_definition(SpecDefinition {
            name: "par_strips_witness_pd_to_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e1 : KExpr) (e2 : KExpr), ",
                "par_strips_witness_pd env e1 e2 -> par_strips_witness_pd_star env e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e1 : KExpr) (e2 : KExpr) (w : par_strips_witness_pd env e1 e2) => ",
                    "@par_strips_witness_pd.rec env e1 e2 ",
                    "(fun (_w : par_strips_witness_pd env e1 e2) => par_strips_witness_pd_star env e1 e2) ",
                    "(fun (e3 : KExpr) (l1 : par_reduces_pd env e1 e3) (l2 : par_reduces_pd env e2 e3) => ",
                    "par_strips_witness_pd_star.intro env e1 e2 e3 ",
                    "(par_subsumes_par_pd_star env e1 e3 l1) (par_subsumes_par_pd_star env e2 e3 l2)) ",
                    "w"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Lift a single-step pd join witness to a multi-step one (subsume both legs). DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_strips_witness_pd".to_string(),
                "par_strips_witness_pd.rec".to_string(),
                "par_strips_witness_pd_star".to_string(),
                "par_strips_witness_pd_star.intro".to_string(),
                "par_reduces_pd".to_string(),
                "par_reduces_pd_star".to_string(),
                "par_subsumes_par_pd_star".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 3: the `par_reduces_cd ⊆ par_reduces_pd` embedding — every atomic 3-way
    /// computational par-step is a proper 3-way par-step. `par_reduces_cd.rec` maps
    /// each of the 10 ctors to the matching `par_reduces_pd` ctor; the atomic iota / delta
    /// map to `iota_p` / `delta_p` with a reflexive subterm-reduction premise, and the
    /// trailing `let_cong` congruence maps to `par_reduces_pd.let_cong`. The bridge that
    /// lifts the landed atomic 3-way relation into the proper one. Mirror of
    /// `par_reduces_c_subsumes_par_p`.
    fn add_par_reduces_pd_embeddings(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_subsumes_par_pd".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_cd env e e' -> par_reduces_pd env e e'"
            )
            .to_string(),
            value_src: Some(par_reduces_cd_subsumes_par_pd_proof()),
            is_axiom: false,
            description: concat!(
                "Embedding par_reduces_cd ⊆ par_reduces_pd: every atomic 3-way computational par-step is a ",
                "proper 3-way par-step. par_reduces_cd.rec mapping refl/beta/app/lam/pi/forall_/let_ (zeta) to ",
                "the matching par_reduces_pd ctor via the IHs; the atomic iota maps to iota_p (par_reduces_pd.refl ",
                "env e) h and the atomic delta maps to delta_p (par_reduces_pd.refl env e) h — the bare steps ",
                "are the parallel steps with no subterm reduction — and the trailing let_cong congruence maps to ",
                "par_reduces_pd.let_cong. The forward half of the closure-coincidence bridge. Mirror of ",
                "par_reduces_c_subsumes_par_p. DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, ",
                "delta increment Stage 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.rec".to_string(),
                "par_reduces_pd".to_string(),
                "par_reduces_pd.refl".to_string(),
                "par_reduces_pd.beta".to_string(),
                "par_reduces_pd.app".to_string(),
                "par_reduces_pd.lam".to_string(),
                "par_reduces_pd.pi".to_string(),
                "par_reduces_pd.forall_".to_string(),
                "par_reduces_pd.let_".to_string(),
                "par_reduces_pd.iota_p".to_string(),
                "par_reduces_pd.delta_p".to_string(),
                "par_reduces_cd.let_cong".to_string(),
                "par_reduces_pd.let_cong".to_string(),
                "iota_step".to_string(),
                "delta_step".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 4: the RT-closure `par_reduces_cd_star` of the ATOMIC 3-way relation,
    /// its combinators (subsumes / trans), and the structural _star congruences
    /// (app / lam / pi / forall / beta / let (zeta) / let_cong). Mechanical mirror of the
    /// `par_reduces_c_star` family (par_reduces_c.rs) over RedEnv. These are the
    /// multi-step congruences the `par_reduces_pd ⊆ par_reduces_cd_star` embedding
    /// lifts its structural arms through.
    fn add_par_reduces_cd_star(&mut self) -> Result<(), SpecError> {
        // par_reduces_cd_star: RT-closure of par_reduces_cd (mirror of par_reduces_c_star).
        self.add_inductive(
            r"inductive par_reduces_cd_star (env : RedEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_cd_star env e e
| step : forall (e : KExpr) (e' : KExpr) (e'' : KExpr), par_reduces_cd env e e' → par_reduces_cd_star env e' e'' → par_reduces_cd_star env e e''",
            "par_reduces_cd_star env e e'' — the reflexive-transitive closure of the atomic 3-way parallel \
             reduction par_reduces_cd. Coincides with par_reduces_pd_star via the two embeddings (the \
             closure-coincidence sandwich). Part of #2859 (Increment H+, delta increment Stage 3).",
        )?;

        // par_subsumes_par_cd_star: single par_reduces_cd step embeds into the closure.
        self.add_definition(SpecDefinition {
            name: "par_subsumes_par_cd_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_cd env e e' -> par_reduces_cd_star env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e' : KExpr) (h : par_reduces_cd env e e') => ",
                    "par_reduces_cd_star.step env e e' e' h (par_reduces_cd_star.refl env e')"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Single-step par_reduces_cd embeds into par_reduces_cd_star (step with a refl tail). DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_star_trans: transitivity (mirror of par_reduces_c_star_trans).
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_trans".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), ",
                "par_reduces_cd_star env e1 e2 -> par_reduces_cd_star env e2 e3 -> ",
                "par_reduces_cd_star env e1 e3"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) ",
                    "(h1 : par_reduces_cd_star env e1 e2) (h2 : par_reduces_cd_star env e2 e3) => ",
                    "par_reduces_cd_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_cd_star env a b) => ",
                    "par_reduces_cd_star env b e3 -> par_reduces_cd_star env a e3) ",
                    "(fun (e : KExpr) (k : par_reduces_cd_star env e e3) => k) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces_cd env e e') ",
                    "(_htail : par_reduces_cd_star env e' e'') ",
                    "(ih : par_reduces_cd_star env e'' e3 -> par_reduces_cd_star env e' e3) ",
                    "(k : par_reduces_cd_star env e'' e3) => ",
                    "par_reduces_cd_star.step env e e' e3 hstep (ih k)) ",
                    "e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Transitivity of par_reduces_cd_star (par_reduces_cd_star.rec on the first chain, prefixing each step onto the extended tail). DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.rec".to_string(),
                "par_reduces_cd_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_star_app: f =>* f' and a =>* a' give app f a =>* app f' a'.
        // Two one-sided star inductions composed by par_reduces_cd_star_trans through
        // app f' a. Mirror of par_reduces_c_star_app.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_app".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), ",
                "par_reduces_cd_star env f f' -> par_reduces_cd_star env a a' -> ",
                "par_reduces_cd_star env (KExpr.app f a) (KExpr.app f' a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(hf : par_reduces_cd_star env f f') (ha : par_reduces_cd_star env a a') => ",
                    "par_reduces_cd_star_trans env (KExpr.app f a) (KExpr.app f' a) (KExpr.app f' a') ",
                    "(par_reduces_cd_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_cd_star env x y) => ",
                    "par_reduces_cd_star env (KExpr.app x a) (KExpr.app y a)) ",
                    "(fun (x : KExpr) => par_reduces_cd_star.refl env (KExpr.app x a)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_cd env x x') (_htail : par_reduces_cd_star env x' x'') ",
                    "(ih : par_reduces_cd_star env (KExpr.app x' a) (KExpr.app x'' a)) => ",
                    "par_reduces_cd_star.step env (KExpr.app x a) (KExpr.app x' a) (KExpr.app x'' a) ",
                    "(par_reduces_cd.app env x x' a a hstep (par_reduces_cd.refl env a)) ih) ",
                    "f f' hf) ",
                    "(par_reduces_cd_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_cd_star env x y) => ",
                    "par_reduces_cd_star env (KExpr.app f' x) (KExpr.app f' y)) ",
                    "(fun (x : KExpr) => par_reduces_cd_star.refl env (KExpr.app f' x)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_cd env x x') (_htail : par_reduces_cd_star env x' x'') ",
                    "(ih : par_reduces_cd_star env (KExpr.app f' x') (KExpr.app f' x'')) => ",
                    "par_reduces_cd_star.step env (KExpr.app f' x) (KExpr.app f' x') (KExpr.app f' x'') ",
                    "(par_reduces_cd.app env f' f' x x' (par_reduces_cd.refl env f') hstep) ih) ",
                    "a a' ha)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "app congruence at the par_reduces_cd_star level: two one-sided star inductions composed by par_reduces_cd_star_trans through app f' a; each single step lifts via par_reduces_cd.app with a reflexive companion. Mirror of par_reduces_c_star_app. DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.app".to_string(),
                "par_reduces_cd.refl".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star.step".to_string(),
                "par_reduces_cd_star.rec".to_string(),
                "par_reduces_cd_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_star_proj: proj congruence at the par_reduces_cd_star level
        // (proj/lit fragment rung). One star induction prefixing par_reduces_cd.proj
        // on each step. Mirror of par_reduces_c_star_proj.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_proj".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (s : Name) (i : Nat) (sub1 : KExpr) (sub2 : KExpr), ",
                "par_reduces_cd_star env sub1 sub2 -> ",
                "par_reduces_cd_star env (KExpr.proj s i sub1) (KExpr.proj s i sub2)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (s : Name) (i : Nat) (sub1 : KExpr) (sub2 : KExpr) ",
                    "(hsub : par_reduces_cd_star env sub1 sub2) => ",
                    "par_reduces_cd_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_cd_star env x y) => ",
                    "par_reduces_cd_star env (KExpr.proj s i x) (KExpr.proj s i y)) ",
                    "(fun (x : KExpr) => par_reduces_cd_star.refl env (KExpr.proj s i x)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_cd env x x') (_htail : par_reduces_cd_star env x' x'') ",
                    "(ih : par_reduces_cd_star env (KExpr.proj s i x') (KExpr.proj s i x'')) => ",
                    "par_reduces_cd_star.step env (KExpr.proj s i x) (KExpr.proj s i x') (KExpr.proj s i x'') ",
                    "(par_reduces_cd.proj env s i x x' hstep) ih) ",
                    "sub1 sub2 hsub"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "proj congruence at the par_reduces_cd_star level: sub1 =>* sub2 gives proj s i sub1 =>* proj s i sub2. One star induction prefixing par_reduces_cd.proj on each step. Mirror of par_reduces_c_star_proj. DerivedProved, zero axiom_deps. Part of the proj/lit fragment rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.proj".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star.step".to_string(),
                "par_reduces_cd_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_star_lam / _pi / _forall: binder congruences (same shape as
        // par_reduces_cd_star_app via the matching binder ctor). Mirror of
        // par_reduces_c_star_{lam,pi,forall}.
        for (name, head, ctor, label) in [
            (
                "par_reduces_cd_star_lam",
                "KExpr.lam",
                "par_reduces_cd.lam",
                "lam",
            ),
            (
                "par_reduces_cd_star_pi",
                "KExpr.pi",
                "par_reduces_cd.pi",
                "pi",
            ),
            (
                "par_reduces_cd_star_forall",
                "KExpr.forall_",
                "par_reduces_cd.forall_",
                "forall_",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (env : RedEnv) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), ",
                        "par_reduces_cd_star env ty ty' -> par_reduces_cd_star env body body' -> ",
                        "par_reduces_cd_star env ({head} ty body) ({head} ty' body')"
                    ),
                    head = head,
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (env : RedEnv) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                        "(hty : par_reduces_cd_star env ty ty') (hbody : par_reduces_cd_star env body body') => ",
                        "par_reduces_cd_star_trans env ({head} ty body) ({head} ty' body) ({head} ty' body') ",
                        "(par_reduces_cd_star.rec env ",
                        "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_cd_star env x y) => ",
                        "par_reduces_cd_star env ({head} x body) ({head} y body)) ",
                        "(fun (x : KExpr) => par_reduces_cd_star.refl env ({head} x body)) ",
                        "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                        "(hstep : par_reduces_cd env x x') (_htail : par_reduces_cd_star env x' x'') ",
                        "(ih : par_reduces_cd_star env ({head} x' body) ({head} x'' body)) => ",
                        "par_reduces_cd_star.step env ({head} x body) ({head} x' body) ({head} x'' body) ",
                        "({ctor} env x x' body body hstep (par_reduces_cd.refl env body)) ih) ",
                        "ty ty' hty) ",
                        "(par_reduces_cd_star.rec env ",
                        "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_cd_star env x y) => ",
                        "par_reduces_cd_star env ({head} ty' x) ({head} ty' y)) ",
                        "(fun (x : KExpr) => par_reduces_cd_star.refl env ({head} ty' x)) ",
                        "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                        "(hstep : par_reduces_cd env x x') (_htail : par_reduces_cd_star env x' x'') ",
                        "(ih : par_reduces_cd_star env ({head} ty' x') ({head} ty' x'')) => ",
                        "par_reduces_cd_star.step env ({head} ty' x) ({head} ty' x') ({head} ty' x'') ",
                        "({ctor} env ty' ty' x x' (par_reduces_cd.refl env ty') hstep) ih) ",
                        "body body' hbody)"
                    ),
                    head = head,
                    ctor = ctor,
                )),
                is_axiom: false,
                description: format!(
                    "{label} congruence at the par_reduces_cd_star level: two one-sided star inductions composed by par_reduces_cd_star_trans; each single step lifts via {ctor} with a reflexive companion. Mirror of par_reduces_c_star_{label}. DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_cd".to_string(),
                    ctor.to_string(),
                    "par_reduces_cd.refl".to_string(),
                    "par_reduces_cd_star".to_string(),
                    "par_reduces_cd_star.refl".to_string(),
                    "par_reduces_cd_star.step".to_string(),
                    "par_reduces_cd_star.rec".to_string(),
                    "par_reduces_cd_star_trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // par_reduces_cd_star_beta: A =>* A', body =>* body', arg =>* arg' give
        // app (lam A body) arg =>* instantiate body' arg'. Skeleton congruence (star
        // app+lam) then one par_reduces_cd.beta. Mirror of par_reduces_c_star_beta.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_beta".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr), ",
                "par_reduces_cd_star env A A' -> par_reduces_cd_star env body body' -> par_reduces_cd_star env arg arg' -> ",
                "par_reduces_cd_star env (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
                    "(hA : par_reduces_cd_star env A A') (hbody : par_reduces_cd_star env body body') (harg : par_reduces_cd_star env arg arg') => ",
                    "par_reduces_cd_star_trans env ",
                    "(KExpr.app (KExpr.lam A body) arg) (KExpr.app (KExpr.lam A' body') arg') (instantiate body' arg') ",
                    "(par_reduces_cd_star_app env (KExpr.lam A body) (KExpr.lam A' body') arg arg' ",
                    "(par_reduces_cd_star_lam env A A' body body' hA hbody) harg) ",
                    "(par_subsumes_par_cd_star env (KExpr.app (KExpr.lam A' body') arg') (instantiate body' arg') ",
                    "(par_reduces_cd.beta env A' A' body' body' arg' arg' ",
                    "(par_reduces_cd.refl env A') (par_reduces_cd.refl env body') (par_reduces_cd.refl env arg')))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "beta contraction at the par_reduces_cd_star level: skeleton congruence (star app+lam) reduces to app (lam A' body') arg', then one par_reduces_cd.beta (reflexive sub-derivations) embedded via par_subsumes_par_cd_star; composed by par_reduces_cd_star_trans. Mirror of par_reduces_c_star_beta. DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.beta".to_string(),
                "par_reduces_cd.refl".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star_app".to_string(),
                "par_reduces_cd_star_lam".to_string(),
                "par_subsumes_par_cd_star".to_string(),
                "par_reduces_cd_star_trans".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_star_let_cong: ty =>* ty', val =>* val', body =>* body' give
        // let_ ty val body =>* let_ ty' val' body' — the genuine-constructor 3-component
        // congruence over the let_ node (the non-contracting sibling of the zeta closure
        // par_reduces_cd_star_let). Three one-sided star inductions (reduce ty, then val,
        // then body) composed by par_reduces_cd_star_trans; each single step lifts via
        // par_reduces_cd.let_cong with reflexive companions on the untouched slots. The
        // let analogue of par_reduces_cd_star_app (app-vs-app 3-component mechanism).
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_let_cong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), ",
                "par_reduces_cd_star env ty ty' -> par_reduces_cd_star env val val' -> par_reduces_cd_star env body body' -> ",
                "par_reduces_cd_star env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(hty : par_reduces_cd_star env ty ty') (hval : par_reduces_cd_star env val val') (hbody : par_reduces_cd_star env body body') => ",
                    "par_reduces_cd_star_trans env ",
                    "(KExpr.let_ ty val body) (KExpr.let_ ty' val body) (KExpr.let_ ty' val' body') ",
                    // phase 1: reduce ty, val/body fixed.
                    "(par_reduces_cd_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_cd_star env x y) => ",
                    "par_reduces_cd_star env (KExpr.let_ x val body) (KExpr.let_ y val body)) ",
                    "(fun (x : KExpr) => par_reduces_cd_star.refl env (KExpr.let_ x val body)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_cd env x x') (_htail : par_reduces_cd_star env x' x'') ",
                    "(ih : par_reduces_cd_star env (KExpr.let_ x' val body) (KExpr.let_ x'' val body)) => ",
                    "par_reduces_cd_star.step env (KExpr.let_ x val body) (KExpr.let_ x' val body) (KExpr.let_ x'' val body) ",
                    "(par_reduces_cd.let_cong env x x' val val body body hstep (par_reduces_cd.refl env val) (par_reduces_cd.refl env body)) ih) ",
                    "ty ty' hty) ",
                    "(par_reduces_cd_star_trans env ",
                    "(KExpr.let_ ty' val body) (KExpr.let_ ty' val' body) (KExpr.let_ ty' val' body') ",
                    // phase 2: reduce val, ty'/body fixed.
                    "(par_reduces_cd_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_cd_star env x y) => ",
                    "par_reduces_cd_star env (KExpr.let_ ty' x body) (KExpr.let_ ty' y body)) ",
                    "(fun (x : KExpr) => par_reduces_cd_star.refl env (KExpr.let_ ty' x body)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_cd env x x') (_htail : par_reduces_cd_star env x' x'') ",
                    "(ih : par_reduces_cd_star env (KExpr.let_ ty' x' body) (KExpr.let_ ty' x'' body)) => ",
                    "par_reduces_cd_star.step env (KExpr.let_ ty' x body) (KExpr.let_ ty' x' body) (KExpr.let_ ty' x'' body) ",
                    "(par_reduces_cd.let_cong env ty' ty' x x' body body (par_reduces_cd.refl env ty') hstep (par_reduces_cd.refl env body)) ih) ",
                    "val val' hval) ",
                    // phase 3: reduce body, ty'/val' fixed.
                    "(par_reduces_cd_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_cd_star env x y) => ",
                    "par_reduces_cd_star env (KExpr.let_ ty' val' x) (KExpr.let_ ty' val' y)) ",
                    "(fun (x : KExpr) => par_reduces_cd_star.refl env (KExpr.let_ ty' val' x)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_cd env x x') (_htail : par_reduces_cd_star env x' x'') ",
                    "(ih : par_reduces_cd_star env (KExpr.let_ ty' val' x') (KExpr.let_ ty' val' x'')) => ",
                    "par_reduces_cd_star.step env (KExpr.let_ ty' val' x) (KExpr.let_ ty' val' x') (KExpr.let_ ty' val' x'') ",
                    "(par_reduces_cd.let_cong env ty' ty' val' val' x x' (par_reduces_cd.refl env ty') (par_reduces_cd.refl env val') hstep) ih) ",
                    "body body' hbody))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "let_ congruence at the par_reduces_cd_star level: the genuine-constructor 3-component congruence (let_ ty val body =>* let_ ty' val' body'), the non-contracting sibling of par_reduces_cd_star_let. Three one-sided star inductions (ty, then val, then body) composed by par_reduces_cd_star_trans; each single step lifts via par_reduces_cd.let_cong with reflexive companions. The let analogue of par_reduces_cd_star_app. DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.let_cong".to_string(),
                "par_reduces_cd.refl".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star.step".to_string(),
                "par_reduces_cd_star.rec".to_string(),
                "par_reduces_cd_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_star_let: ty =>* ty', val =>* val', body =>* body' give
        // let_ ty val body =>* instantiate body' val'. Two-phase: the genuine-ctor
        // congruence par_reduces_cd_star_let_cong reduces the subterms, then one
        // par_reduces_cd.let_ (ZETA) fires. Mirror of par_reduces_c_star_let.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_let".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), ",
                "par_reduces_cd_star env ty ty' -> par_reduces_cd_star env val val' -> par_reduces_cd_star env body body' -> ",
                "par_reduces_cd_star env (KExpr.let_ ty val body) (instantiate body' val')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(hty : par_reduces_cd_star env ty ty') (hval : par_reduces_cd_star env val val') (hbody : par_reduces_cd_star env body body') => ",
                    "par_reduces_cd_star_trans env ",
                    "(KExpr.let_ ty val body) (KExpr.let_ ty' val' body') (instantiate body' val') ",
                    "(par_reduces_cd_star_let_cong env ty ty' val val' body body' hty hval hbody) ",
                    "(par_subsumes_par_cd_star env (KExpr.let_ ty' val' body') (instantiate body' val') ",
                    "(par_reduces_cd.let_ env ty' ty' val' val' body' body' ",
                    "(par_reduces_cd.refl env ty') (par_reduces_cd.refl env val') (par_reduces_cd.refl env body')))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "let_ contraction (zeta) at the par_reduces_cd_star level: phase 1 reduces the subterms via the genuine-constructor congruence par_reduces_cd_star_let_cong (let_ ty val body =>* let_ ty' val' body'); phase 2 fires one par_reduces_cd.let_ (zeta, reflexive sub-derivations) to instantiate body' val', embedded via par_subsumes_par_cd_star; composed by par_reduces_cd_star_trans. Mirror of par_reduces_c_star_let. DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.let_".to_string(),
                "par_reduces_cd.refl".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star_let_cong".to_string(),
                "par_subsumes_par_cd_star".to_string(),
                "par_reduces_cd_star_trans".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 5: the closure-coincidence SANDWICH bridges at the relation + star
    /// levels — `par_reduces_pd ⊆ par_reduces_cd_star` (single proper step is an
    /// atomic multi-step) plus the two RT-closure embeddings making
    /// `par_reduces_cd_star` and `par_reduces_pd_star` coincide. These are exactly
    /// what the eventual 3-way CR `par_reduces_cd_star_diamond` rides on (mirror of
    /// the β+ι sandwich in par_reduces_p_topdev.rs).
    fn add_par_reduces_pd_cd_star_bridges(&mut self) -> Result<(), SpecError> {
        // par_reduces_pd_subsumes_par_cd_star: single proper step -> atomic multi-step.
        self.add_definition(SpecDefinition {
            name: "par_reduces_pd_subsumes_par_cd_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_pd env e e' -> par_reduces_cd_star env e e'"
            )
            .to_string(),
            value_src: Some(par_reduces_pd_subsumes_par_cd_star_proof()),
            is_axiom: false,
            description: concat!(
                "Embedding par_reduces_pd ⊆ par_reduces_cd_star: every proper 3-way par-step is an atomic ",
                "3-way multi-step. par_reduces_pd.rec into par_reduces_cd_star — the structural arms lift via ",
                "the matching par_reduces_cd_star_{app,lam,pi,forall,beta,let,let_cong} congruence on the IHs, ",
                "and the iota_p / delta_p arms lift by par_reduces_cd_star_trans of the subterm-reduction IH (e ",
                "⇒*_cd e2) with the fired step (e2 ⇒_cd r via par_reduces_cd.iota / .delta, subsumed to star). ",
                "The backward half of the closure-coincidence sandwich. Mirror of par_reduces_p_subsumes_par_c_star. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, delta increment Stage 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_pd".to_string(),
                "par_reduces_pd.rec".to_string(),
                "par_reduces_cd".to_string(),
                "par_reduces_cd.iota".to_string(),
                "par_reduces_cd.delta".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star_app".to_string(),
                "par_reduces_cd_star_lam".to_string(),
                "par_reduces_cd_star_pi".to_string(),
                "par_reduces_cd_star_forall".to_string(),
                "par_reduces_cd_star_beta".to_string(),
                "par_reduces_cd_star_let".to_string(),
                "par_reduces_cd_star_let_cong".to_string(),
                "par_reduces_pd.let_cong".to_string(),
                "par_reduces_cd_star_trans".to_string(),
                "par_subsumes_par_cd_star".to_string(),
                "iota_step".to_string(),
                "delta_step".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_star_subsumes_par_pd_star: lift cd ⊆ pd over the RT-closure.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_subsumes_par_pd_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_cd_star env e e' -> par_reduces_pd_star env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e' : KExpr) ",
                    "(h : par_reduces_cd_star env e e') => ",
                    "par_reduces_cd_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_cd_star env a b) => ",
                    "par_reduces_pd_star env a b) ",
                    "(fun (s : KExpr) => par_reduces_pd_star.refl env s) ",
                    "(fun (s : KExpr) (s' : KExpr) (s'' : KExpr) ",
                    "(hstep : par_reduces_cd env s s') (_htail : par_reduces_cd_star env s' s'') ",
                    "(ih : par_reduces_pd_star env s' s'') => ",
                    "par_reduces_pd_star.step env s s' s'' ",
                    "(par_reduces_cd_subsumes_par_pd env s s' hstep) ih) ",
                    "e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level embedding par_reduces_cd_star ⊆ par_reduces_pd_star: lift par_reduces_cd_subsumes_par_pd ",
                "over the RT-closure. par_reduces_cd_star.rec — refl is par_reduces_pd_star.refl, step prefixes the ",
                "subsumed single step via par_reduces_pd_star.step. The forward half of the star-level sandwich the ",
                "3-way CR rides on. Mirror of par_reduces_c_star_subsumes_par_p_star. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment H+, delta increment Stage 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.rec".to_string(),
                "par_reduces_pd_star".to_string(),
                "par_reduces_pd_star.refl".to_string(),
                "par_reduces_pd_star.step".to_string(),
                "par_reduces_cd_subsumes_par_pd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_pd_star_subsumes_par_cd_star: lift pd ⊆ cd_star over the
        // RT-closure, gluing each step's cd-star with the IH via par_reduces_cd_star_trans.
        self.add_definition(SpecDefinition {
            name: "par_reduces_pd_star_subsumes_par_cd_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_pd_star env e e' -> par_reduces_cd_star env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e' : KExpr) ",
                    "(h : par_reduces_pd_star env e e') => ",
                    "par_reduces_pd_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_pd_star env a b) => ",
                    "par_reduces_cd_star env a b) ",
                    "(fun (s : KExpr) => par_reduces_cd_star.refl env s) ",
                    "(fun (s : KExpr) (s' : KExpr) (s'' : KExpr) ",
                    "(hstep : par_reduces_pd env s s') (_htail : par_reduces_pd_star env s' s'') ",
                    "(ih : par_reduces_cd_star env s' s'') => ",
                    "par_reduces_cd_star_trans env s s' s'' ",
                    "(par_reduces_pd_subsumes_par_cd_star env s s' hstep) ih) ",
                    "e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level embedding par_reduces_pd_star ⊆ par_reduces_cd_star: lift par_reduces_pd_subsumes_par_cd_star ",
                "over the RT-closure. par_reduces_pd_star.rec — refl is par_reduces_cd_star.refl, step glues the head ",
                "step's cd-star with the IH via par_reduces_cd_star_trans. The backward half of the star-level sandwich; ",
                "with par_reduces_cd_star_subsumes_par_pd_star it makes the two RT-closures coincide. Mirror of ",
                "par_reduces_p_star_subsumes_par_c_star. DerivedProved, zero axiom_deps. Part of #2859 (Increment H+, ",
                "delta increment Stage 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_pd_star".to_string(),
                "par_reduces_pd_star.rec".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_pd_subsumes_par_cd_star".to_string(),
                "par_reduces_cd_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `par_reduces_pd_subsumes_par_cd_star` — par_reduces_pd.rec
/// into par_reduces_cd_star: structural arms via the matching _star congruence on the
/// IHs; iota_p / delta_p via par_reduces_cd_star_trans (IH) ∘ (fired step subsumed to
/// star). Mirror of par_reduces_p_subsumes_par_c_star_proof, with the extra delta_p arm.
fn par_reduces_pd_subsumes_par_cd_star_proof() -> String {
    concat!(
        "fun (env : RedEnv) (e : KExpr) (e' : KExpr) (h : par_reduces_pd env e e') => ",
        "par_reduces_pd.rec env ",
        "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_pd env x y) => par_reduces_cd_star env x y) ",
        // refl
        "(fun (a : KExpr) => par_reduces_cd_star.refl env a) ",
        // beta
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_pd env A A') (_hbody : par_reduces_pd env body body') (_harg : par_reduces_pd env arg arg') ",
        "(ihA : par_reduces_cd_star env A A') (ihbody : par_reduces_cd_star env body body') (iharg : par_reduces_cd_star env arg arg') => ",
        "par_reduces_cd_star_beta env A A' body body' arg arg' ihA ihbody iharg) ",
        // app
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_hf : par_reduces_pd env f f') (_ha : par_reduces_pd env a a') ",
        "(ihf : par_reduces_cd_star env f f') (iha : par_reduces_cd_star env a a') => ",
        "par_reduces_cd_star_app env f f' a a' ihf iha) ",
        // lam
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_pd env ty ty') (_hbody : par_reduces_pd env body body') ",
        "(ihty : par_reduces_cd_star env ty ty') (ihbody : par_reduces_cd_star env body body') => ",
        "par_reduces_cd_star_lam env ty ty' body body' ihty ihbody) ",
        // pi
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_pd env dom dom') (_hbody : par_reduces_pd env body body') ",
        "(ihd : par_reduces_cd_star env dom dom') (ihbody : par_reduces_cd_star env body body') => ",
        "par_reduces_cd_star_pi env dom dom' body body' ihd ihbody) ",
        // forall_
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_pd env dom dom') (_hbody : par_reduces_pd env body body') ",
        "(ihd : par_reduces_cd_star env dom dom') (ihbody : par_reduces_cd_star env body body') => ",
        "par_reduces_cd_star_forall env dom dom' body body' ihd ihbody) ",
        // let_
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_pd env ty ty') (_hval : par_reduces_pd env val val') (_hbody : par_reduces_pd env body body') ",
        "(ihty : par_reduces_cd_star env ty ty') (ihval : par_reduces_cd_star env val val') (ihbody : par_reduces_cd_star env body body') => ",
        "par_reduces_cd_star_let env ty ty' val val' body body' ihty ihval ihbody) ",
        // iota_p: e ⇒_pd e2 (IH ⇒*_cd) then iota_step (red_rec env) e2 r (⇒_cd subsumed), trans.
        "(fun (a : KExpr) (a2 : KExpr) (r : KExpr) ",
        "(_hp : par_reduces_pd env a a2) (hi : iota_step (red_rec env) a2 r) ",
        "(ihp : par_reduces_cd_star env a a2) => ",
        "par_reduces_cd_star_trans env a a2 r ihp ",
        "(par_subsumes_par_cd_star env a2 r (par_reduces_cd.iota env a2 r hi))) ",
        // delta_p: e ⇒_pd e2 (IH ⇒*_cd) then delta_step (red_def env) e2 r (⇒_cd subsumed), trans.
        "(fun (a : KExpr) (a2 : KExpr) (r : KExpr) ",
        "(_hp : par_reduces_pd env a a2) (hd : delta_step (red_def env) a2 r) ",
        "(ihp : par_reduces_cd_star env a a2) => ",
        "par_reduces_cd_star_trans env a a2 r ihp ",
        "(par_subsumes_par_cd_star env a2 r (par_reduces_cd.delta env a2 r hd))) ",
        // let_cong: positional congruence over a genuine let_ node -> par_reduces_cd_star_let_cong on the IHs.
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_pd env ty ty') (_hval : par_reduces_pd env val val') (_hbody : par_reduces_pd env body body') ",
        "(ihty : par_reduces_cd_star env ty ty') (ihval : par_reduces_cd_star env val val') (ihbody : par_reduces_cd_star env body body') => ",
        "par_reduces_cd_star_let_cong env ty ty' val val' body body' ihty ihval ihbody) ",
        // proj: positional congruence over the scrutinee -> par_reduces_cd_star_proj on the IH.
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_pd env sub sub') (ihsub : par_reduces_cd_star env sub sub') => ",
        "par_reduces_cd_star_proj env s i sub sub' ihsub) ",
        "e e' h"
    )
    .to_string()
}

/// Closed proof term for `par_reduces_cd_subsumes_par_pd` — par_reduces_cd.rec mapping
/// each of the 10 ctors to the matching par_reduces_pd ctor; the atomic iota / delta map
/// to iota_p / delta_p with a reflexive premise, and the trailing let_cong congruence maps
/// to par_reduces_pd.let_cong. Mirror of par_reduces_c_subsumes_par_p_proof.
fn par_reduces_cd_subsumes_par_pd_proof() -> String {
    concat!(
        "fun (env : RedEnv) (e : KExpr) (e' : KExpr) (h : par_reduces_cd env e e') => ",
        "par_reduces_cd.rec env ",
        "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_cd env x y) => par_reduces_pd env x y) ",
        // refl
        "(fun (a : KExpr) => par_reduces_pd.refl env a) ",
        // beta
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_cd env A A') (_hbody : par_reduces_cd env body body') (_harg : par_reduces_cd env arg arg') ",
        "(ihA : par_reduces_pd env A A') (ihbody : par_reduces_pd env body body') (iharg : par_reduces_pd env arg arg') => ",
        "par_reduces_pd.beta env A A' body body' arg arg' ihA ihbody iharg) ",
        // app
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_hf : par_reduces_cd env f f') (_ha : par_reduces_cd env a a') ",
        "(ihf : par_reduces_pd env f f') (iha : par_reduces_pd env a a') => ",
        "par_reduces_pd.app env f f' a a' ihf iha) ",
        // lam
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_cd env ty ty') (_hbody : par_reduces_cd env body body') ",
        "(ihty : par_reduces_pd env ty ty') (ihbody : par_reduces_pd env body body') => ",
        "par_reduces_pd.lam env ty ty' body body' ihty ihbody) ",
        // pi
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_cd env dom dom') (_hbody : par_reduces_cd env body body') ",
        "(ihd : par_reduces_pd env dom dom') (ihbody : par_reduces_pd env body body') => ",
        "par_reduces_pd.pi env dom dom' body body' ihd ihbody) ",
        // forall_
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_cd env dom dom') (_hbody : par_reduces_cd env body body') ",
        "(ihd : par_reduces_pd env dom dom') (ihbody : par_reduces_pd env body body') => ",
        "par_reduces_pd.forall_ env dom dom' body body' ihd ihbody) ",
        // let_
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_cd env ty ty') (_hval : par_reduces_cd env val val') (_hbody : par_reduces_cd env body body') ",
        "(ihty : par_reduces_pd env ty ty') (ihval : par_reduces_pd env val val') (ihbody : par_reduces_pd env body body') => ",
        "par_reduces_pd.let_ env ty ty' val val' body body' ihty ihval ihbody) ",
        // iota (atomic): map to iota_p with a reflexive subterm reduction.
        "(fun (a : KExpr) (a' : KExpr) (hi : iota_step (red_rec env) a a') => ",
        "par_reduces_pd.iota_p env a a a' (par_reduces_pd.refl env a) hi) ",
        // delta (atomic): map to delta_p with a reflexive subterm reduction.
        "(fun (a : KExpr) (a' : KExpr) (hd : delta_step (red_def env) a a') => ",
        "par_reduces_pd.delta_p env a a a' (par_reduces_pd.refl env a) hd) ",
        // let_cong: positional congruence over a genuine let_ node -> par_reduces_pd.let_cong on the IHs.
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_cd env ty ty') (_hval : par_reduces_cd env val val') (_hbody : par_reduces_cd env body body') ",
        "(ihty : par_reduces_pd env ty ty') (ihval : par_reduces_pd env val val') (ihbody : par_reduces_pd env body body') => ",
        "par_reduces_pd.let_cong env ty ty' val val' body body' ihty ihval ihbody) ",
        // proj: positional congruence over the scrutinee -> par_reduces_pd.proj on the IH.
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_cd env sub sub') (ihsub : par_reduces_pd env sub sub') => ",
        "par_reduces_pd.proj env s i sub sub' ihsub) ",
        "e e' h"
    )
    .to_string()
}
