// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment F+ (#2859 computational-iota/delta track): the PROPER parallel
//! reduction `par_reduces_p` — the Takahashi-shaped sibling of `par_reduces_c`
//! whose iota constructor BAKES IN the parallel reduction of the redex subterms.
//!
//! Why: `par_reduces_c.iota` is ATOMIC (it carries the bare deterministic
//! `iota_step env e e'`, with the constructor/recursor arguments NOT further
//! reduced). That makes the substitution lemma 2-step for a top-level iota, which
//! makes the single-step diamond `par_strips_c_full` produce STAR legs (the WEAK
//! diamond) — insufficient for R*-confluence. The conventional Takahashi fix is a
//! parallel-iota rule that reduces the subterms BEFORE contracting, exactly as
//! `par_reduces_c.beta` does (`app (lam A b) arg ⇒ inst b' arg'` with `b ⇒ b'`,
//! `arg ⇒ arg'`). `iota_p` captures that: `e ⇒_p e2` (subterms par-reduce, e2 still
//! an iota redex of the same recursor) then `iota_step env e2 r` fires.
//!
//! With `iota_p` the substitution lemma is 1-step, so `par_reduces_p` has the
//! STRONG single-step diamond, which lifts mechanically to R*-confluence. The
//! bridge `par_reduces_c ⊆ par_reduces_p ⊆ par_reduces_c_star` makes the two
//! RT-closures coincide, so confluence of `par_reduces_c_star` follows.
//!
//! This module is ADDITIVE — it does NOT touch `par_reduces_c` or any of the
//! `par_strips_c_*` work; the hard (iota,app) overlap machinery transfers to the
//! `par_reduces_p` diamond in later increments. See
//! `designs/2026-06-14-computational-iota-delta-track.md` §10.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_par_reduces_p(&mut self) -> Result<(), SpecError> {
        // par_reduces_p env: the proper (Takahashi) parallel reduction. Identical to
        // par_reduces_c except the iota constructor is PARALLEL: iota_p reduces the
        // subterms (e ⇒_p e2) then fires the deterministic iota on the reduced redex
        // (iota_step env e2 r). e2 is the recursive premise (positive occurrence), so
        // the contraction bakes in the sub-reductions — the key to a 1-step
        // substitution lemma and the STRONG single-step diamond.
        self.add_inductive(
            r"inductive par_reduces_p (env : RecEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_p env e e
| beta : forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr), par_reduces_p env A A' → par_reduces_p env body body' → par_reduces_p env arg arg' → par_reduces_p env (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')
| app : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), par_reduces_p env f f' → par_reduces_p env a a' → par_reduces_p env (KExpr.app f a) (KExpr.app f' a')
| lam : forall (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_p env ty ty' → par_reduces_p env body body' → par_reduces_p env (KExpr.lam ty body) (KExpr.lam ty' body')
| pi : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_p env dom dom' → par_reduces_p env body body' → par_reduces_p env (KExpr.pi dom body) (KExpr.pi dom' body')
| forall_ : forall (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_p env dom dom' → par_reduces_p env body body' → par_reduces_p env (KExpr.forall_ dom body) (KExpr.forall_ dom' body')
| let_ : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_p env ty ty' → par_reduces_p env val val' → par_reduces_p env body body' → par_reduces_p env (KExpr.let_ ty val body) (instantiate body' val')
| iota_p : forall (e : KExpr) (e2 : KExpr) (r : KExpr), par_reduces_p env e e2 → iota_step env e2 r → par_reduces_p env e r
| let_cong : forall (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_p env ty ty' → par_reduces_p env val val' → par_reduces_p env body body' → par_reduces_p env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')
| proj : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), par_reduces_p env sub sub' → par_reduces_p env (KExpr.proj s i sub) (KExpr.proj s i sub')",
            "par_reduces_p env e e' — the PROPER (Takahashi) parallel reduction: par_reduces_c with the iota \
             constructor made PARALLEL. iota_p first par-reduces the redex subterms (e ⇒_p e2) then fires the \
             deterministic iota on the reduced redex (iota_step env e2 r). Baking in the sub-reductions makes \
             the substitution lemma 1-step and gives par_reduces_p the STRONG single-step diamond (unlike \
             par_reduces_c, whose atomic iota only yields the weak/star diamond). The let_ arm is the ZETA \
             contraction (KExpr.let_ ty val body ⇒_p instantiate body' val'); the trailing let_cong arm is the \
             positional let CONGRUENCE (KExpr.let_ ty val body ⇒_p KExpr.let_ ty' val' body') — now that let_ is \
             a genuine 7th KExpr constructor (no longer the app(lam) alias), a let node needs both. Additive; \
             bridged to par_reduces_c_star. Part of #2859 (Increment F+, parallel-iota redesign).",
        )?;

        // par_reduces_c_subsumes_par_p: every par_reduces_c step is a par_reduces_p
        // step. par_reduces_c.rec mapping each ctor to the matching par_reduces_p ctor;
        // the (atomic) iota ctor maps to iota_p with a reflexive subterm-reduction
        // premise (e ⇒_p e via refl, then the same iota_step fires).
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_subsumes_par_p".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_c env e e' -> par_reduces_p env e e'"
            )
            .to_string(),
            value_src: Some(par_reduces_c_subsumes_par_p_proof()),
            is_axiom: false,
            description: concat!(
                "Embedding par_reduces_c ⊆ par_reduces_p: every computational par-step is a proper par-step. ",
                "par_reduces_c.rec mapping refl/beta/app/lam/pi/forall_/let_/let_cong to the matching par_reduces_p ctor ",
                "via the recursor IHs; the atomic iota maps to iota_p (par_reduces_p.refl env e) h — the bare ",
                "iota is the parallel iota with no subterm reduction. The forward half of the closure-coincidence ",
                "bridge. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_p".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p.beta".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p.lam".to_string(),
                "par_reduces_p.pi".to_string(),
                "par_reduces_p.forall_".to_string(),
                "par_reduces_p.let_".to_string(),
                "par_reduces_p.iota_p".to_string(),
                "par_reduces_p.let_cong".to_string(),
                "iota_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_subsumes_par_c_star: every par_reduces_p step is a
        // par_reduces_c multi-step. par_reduces_p.rec into par_reduces_c_star; the
        // structural ctors lift via the matching _star congruence, and iota_p lifts by
        // par_reduces_c_star_trans (the IH e ⇒*_c e2) ∘ (e2 ⇒_c r via .iota subsumed).
        // This is the bridge direction that makes par_reduces_p_star ⊆ par_reduces_c_star.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_subsumes_par_c_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_p env e e' -> par_reduces_c_star env e e'"
            )
            .to_string(),
            value_src: Some(par_reduces_p_subsumes_par_c_star_proof()),
            is_axiom: false,
            description: concat!(
                "Embedding par_reduces_p ⊆ par_reduces_c_star: every proper par-step is a computational ",
                "multi-step. par_reduces_p.rec into par_reduces_c_star — the structural arms lift via the ",
                "matching par_reduces_c_star_{app,lam,pi,forall,beta,let,let_cong} congruence on the IHs, and iota_p ",
                "lifts by par_reduces_c_star_trans of the subterm-reduction IH (e ⇒*_c e2) with the fired iota ",
                "(e2 ⇒_c r via par_reduces_c.iota, subsumed to star). With par_reduces_c_subsumes_par_p this ",
                "makes the two RT-closures coincide, so confluence of par_reduces_p_star transfers to ",
                "par_reduces_c_star. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "par_reduces_c".to_string(),
                "par_reduces_c.iota".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star_app".to_string(),
                "par_reduces_c_star_lam".to_string(),
                "par_reduces_c_star_pi".to_string(),
                "par_reduces_c_star_forall".to_string(),
                "par_reduces_c_star_beta".to_string(),
                "par_reduces_c_star_let".to_string(),
                "par_reduces_c_star_let_cong".to_string(),
                "par_reduces_c_star_trans".to_string(),
                "par_subsumes_par_c_star".to_string(),
                "iota_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_par_reduces_p_star()?;

        Ok(())
    }

    /// The reflexive-transitive closure `par_reduces_p_star`, its single- and
    /// multi-step join witnesses, and the basic combinators (subsumes / trans /
    /// witness-to-star) — the substrate the strong single-step diamond and its
    /// multi-step lift consume. All mechanical mirrors of the par_reduces_c_star /
    /// par_strips_witness_c analogues.
    fn add_par_reduces_p_star(&mut self) -> Result<(), SpecError> {
        // par_reduces_p_star: RT-closure of par_reduces_p (mirror of par_reduces_c_star).
        self.add_inductive(
            r"inductive par_reduces_p_star (env : RecEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_p_star env e e
| step : forall (e : KExpr) (e' : KExpr) (e'' : KExpr), par_reduces_p env e e' → par_reduces_p_star env e' e'' → par_reduces_p_star env e e''",
            "par_reduces_p_star env e e'' — the reflexive-transitive closure of the proper parallel \
             reduction par_reduces_p. The multi-step level the par_reduces_p confluence endpoint lives \
             at; coincides with par_reduces_c_star via the two embeddings. Part of #2859 (Increment F+).",
        )?;

        // par_subsumes_par_p_star: single par_reduces_p step embeds into the closure.
        self.add_definition(SpecDefinition {
            name: "par_subsumes_par_p_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_p env e e' -> par_reduces_p_star env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (h : par_reduces_p env e e') => ",
                    "par_reduces_p_star.step env e e' e' h (par_reduces_p_star.refl env e')"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Single-step par_reduces_p embeds into par_reduces_p_star (step with a refl tail). DerivedProved, zero axiom_deps. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star.refl".to_string(),
                "par_reduces_p_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_star_trans: transitivity (mirror of par_reduces_c_star_trans).
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_star_trans".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), ",
                "par_reduces_p_star env e1 e2 -> par_reduces_p_star env e2 e3 -> ",
                "par_reduces_p_star env e1 e3"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) ",
                    "(h1 : par_reduces_p_star env e1 e2) (h2 : par_reduces_p_star env e2 e3) => ",
                    "par_reduces_p_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_p_star env a b) => ",
                    "par_reduces_p_star env b e3 -> par_reduces_p_star env a e3) ",
                    "(fun (e : KExpr) (k : par_reduces_p_star env e e3) => k) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces_p env e e') ",
                    "(_htail : par_reduces_p_star env e' e'') ",
                    "(ih : par_reduces_p_star env e'' e3 -> par_reduces_p_star env e' e3) ",
                    "(k : par_reduces_p_star env e'' e3) => ",
                    "par_reduces_p_star.step env e e' e3 hstep (ih k)) ",
                    "e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Transitivity of par_reduces_p_star (par_reduces_p_star.rec on the first chain, prefixing each step onto the extended tail). DerivedProved, zero axiom_deps. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star.rec".to_string(),
                "par_reduces_p_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_strips_witness_p: the single-step join witness (mirror of
        // par_strips_witness_c). The STRONG single-step diamond par_strips_p lands here.
        self.add_inductive(
            r"inductive par_strips_witness_p (env : RecEnv) : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), par_reduces_p env e1 e3 → par_reduces_p env e2 e3 → par_strips_witness_p env e1 e2",
            "par_strips_witness_p env e1 e2 packages a common reduct e3 with par_reduces_p env e1 e3 and \
             par_reduces_p env e2 e3 — the SINGLE-step join witness. Because par_reduces_p's iota is \
             parallel (1-step substitution), the strong single-step diamond par_strips_p lands here (not a \
             star witness). Part of #2859 (Increment F+).",
        )?;

        // par_strips_witness_p_star: the multi-step join witness (mirror of
        // par_strips_witness_bd_star) — the strip lemma and multi-step diamond endpoint.
        self.add_inductive(
            r"inductive par_strips_witness_p_star (env : RecEnv) : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), par_reduces_p_star env e1 e3 → par_reduces_p_star env e2 e3 → par_strips_witness_p_star env e1 e2",
            "par_strips_witness_p_star env e1 e2 packages a common reduct e3 with par_reduces_p_star legs — \
             the multi-step join witness the strip lemma and the confluence theorem par_reduces_p_star_diamond \
             land at. Part of #2859 (Increment F+).",
        )?;

        // par_strips_witness_p_to_star: lift a single-step join to a multi-step join.
        self.add_definition(SpecDefinition {
            name: "par_strips_witness_p_to_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e1 : KExpr) (e2 : KExpr), ",
                "par_strips_witness_p env e1 e2 -> par_strips_witness_p_star env e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e1 : KExpr) (e2 : KExpr) (w : par_strips_witness_p env e1 e2) => ",
                    "@par_strips_witness_p.rec env e1 e2 ",
                    "(fun (_w : par_strips_witness_p env e1 e2) => par_strips_witness_p_star env e1 e2) ",
                    "(fun (e3 : KExpr) (l1 : par_reduces_p env e1 e3) (l2 : par_reduces_p env e2 e3) => ",
                    "par_strips_witness_p_star.intro env e1 e2 e3 ",
                    "(par_subsumes_par_p_star env e1 e3 l1) (par_subsumes_par_p_star env e2 e3 l2)) ",
                    "w"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Lift a single-step join witness to a multi-step one (subsume both legs). DerivedProved, zero axiom_deps. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_strips_witness_p".to_string(),
                "par_strips_witness_p.rec".to_string(),
                "par_strips_witness_p_star".to_string(),
                "par_strips_witness_p_star.intro".to_string(),
                "par_reduces_p".to_string(),
                "par_reduces_p_star".to_string(),
                "par_subsumes_par_p_star".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_par_reduces_p_star_congruences()?;
        self.add_par_reduces_p_spine()?;

        Ok(())
    }

    /// The `par_reduces_p_star` STRUCTURAL CONGRUENCES — binder (`_lam` / `_pi` /
    /// `_forall`), application (`_app`), and the substitution congruence (`par_subst_p_star`,
    /// depth 0). Mechanical p-side mirrors of the landed c-side
    /// `par_reduces_c_star_{app,lam,pi,forall}` family (par_reduces_c.rs:3258-3414): each
    /// binder/app congruence is two one-sided star inductions (`par_reduces_p_star.rec`)
    /// composed by `par_reduces_p_star_trans` through a waypoint, every single step
    /// lifted via the matching `par_reduces_p` constructor with a reflexive companion.
    /// `par_subst_p_star` is the same two-one-sided-induction shape lifting `par_subst_p`
    /// (RecEnvClosed / RecEnvLiftClosed gated). These are the multi-step congruences the
    /// STAR-valued marked triangle (`par_reduces_pL_triangle_star`) needs to lift the
    /// single-step development bricks to the star motive. DerivedProved, zero axiom_deps.
    /// Part of #2859 (Increment F++, STAR-valued marked triangle, design §17).
    fn add_par_reduces_p_star_congruences(&mut self) -> Result<(), SpecError> {
        // par_reduces_p_star_app: f =>* f' and a =>* a' give app f a =>* app f' a'.
        // Two one-sided star inductions composed by par_reduces_p_star_trans through the
        // waypoint app f' a. p-side mirror of par_reduces_c_star_app.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_star_app".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), ",
                "par_reduces_p_star env f f' -> par_reduces_p_star env a a' -> ",
                "par_reduces_p_star env (KExpr.app f a) (KExpr.app f' a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(hf : par_reduces_p_star env f f') (ha : par_reduces_p_star env a a') => ",
                    // left leg: app f a =>* app f' a  (induct on hf, fix arg a)
                    "par_reduces_p_star_trans env (KExpr.app f a) (KExpr.app f' a) (KExpr.app f' a') ",
                    "(par_reduces_p_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_p_star env x y) => ",
                    "par_reduces_p_star env (KExpr.app x a) (KExpr.app y a)) ",
                    "(fun (x : KExpr) => par_reduces_p_star.refl env (KExpr.app x a)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_p env x x') (_htail : par_reduces_p_star env x' x'') ",
                    "(ih : par_reduces_p_star env (KExpr.app x' a) (KExpr.app x'' a)) => ",
                    "par_reduces_p_star.step env (KExpr.app x a) (KExpr.app x' a) (KExpr.app x'' a) ",
                    "(par_reduces_p.app env x x' a a hstep (par_reduces_p.refl env a)) ih) ",
                    "f f' hf) ",
                    // right leg: app f' a =>* app f' a'  (induct on ha, fix fn f')
                    "(par_reduces_p_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_p_star env x y) => ",
                    "par_reduces_p_star env (KExpr.app f' x) (KExpr.app f' y)) ",
                    "(fun (x : KExpr) => par_reduces_p_star.refl env (KExpr.app f' x)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_p env x x') (_htail : par_reduces_p_star env x' x'') ",
                    "(ih : par_reduces_p_star env (KExpr.app f' x') (KExpr.app f' x'')) => ",
                    "par_reduces_p_star.step env (KExpr.app f' x) (KExpr.app f' x') (KExpr.app f' x'') ",
                    "(par_reduces_p.app env f' f' x x' (par_reduces_p.refl env f') hstep) ih) ",
                    "a a' ha)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "app congruence at the par_reduces_p_star level: f =>* f' and a =>* a' give app f a =>* app f' a'. ",
                "Two one-sided star inductions (par_reduces_p_star.rec) composed by par_reduces_p_star_trans through ",
                "app f' a; each single step lifts via par_reduces_p.app with a reflexive companion. p-side mirror of ",
                "par_reduces_c_star_app. DerivedProved, zero axiom_deps. Part of #2859 (Increment F++, design §17)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star.refl".to_string(),
                "par_reduces_p_star.step".to_string(),
                "par_reduces_p_star.rec".to_string(),
                "par_reduces_p_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_star_lam / _pi / _forall: binder congruences at the
        // par_reduces_p_star level. ty =>* ty' and body =>* body' give
        // HEAD ty body =>* HEAD ty' body'. Same two-one-sided-induction shape as
        // par_reduces_p_star_app, using the matching binder ctor (par_reduces_p.lam /
        // .pi / .forall_) with a reflexive companion at each single step. p-side mirror
        // of par_reduces_c_star_{lam,pi,forall}.
        for (name, head, ctor, label) in [
            (
                "par_reduces_p_star_lam",
                "KExpr.lam",
                "par_reduces_p.lam",
                "lam",
            ),
            (
                "par_reduces_p_star_pi",
                "KExpr.pi",
                "par_reduces_p.pi",
                "pi",
            ),
            (
                "par_reduces_p_star_forall",
                "KExpr.forall_",
                "par_reduces_p.forall_",
                "forall_",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (env : RecEnv) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), ",
                        "par_reduces_p_star env ty ty' -> par_reduces_p_star env body body' -> ",
                        "par_reduces_p_star env ({head} ty body) ({head} ty' body')"
                    ),
                    head = head,
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (env : RecEnv) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                        "(hty : par_reduces_p_star env ty ty') (hbody : par_reduces_p_star env body body') => ",
                        // left leg: HEAD ty body =>* HEAD ty' body  (induct on hty)
                        "par_reduces_p_star_trans env ({head} ty body) ({head} ty' body) ({head} ty' body') ",
                        "(par_reduces_p_star.rec env ",
                        "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_p_star env x y) => ",
                        "par_reduces_p_star env ({head} x body) ({head} y body)) ",
                        "(fun (x : KExpr) => par_reduces_p_star.refl env ({head} x body)) ",
                        "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                        "(hstep : par_reduces_p env x x') (_htail : par_reduces_p_star env x' x'') ",
                        "(ih : par_reduces_p_star env ({head} x' body) ({head} x'' body)) => ",
                        "par_reduces_p_star.step env ({head} x body) ({head} x' body) ({head} x'' body) ",
                        "({ctor} env x x' body body hstep (par_reduces_p.refl env body)) ih) ",
                        "ty ty' hty) ",
                        // right leg: HEAD ty' body =>* HEAD ty' body'  (induct on hbody)
                        "(par_reduces_p_star.rec env ",
                        "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_p_star env x y) => ",
                        "par_reduces_p_star env ({head} ty' x) ({head} ty' y)) ",
                        "(fun (x : KExpr) => par_reduces_p_star.refl env ({head} ty' x)) ",
                        "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                        "(hstep : par_reduces_p env x x') (_htail : par_reduces_p_star env x' x'') ",
                        "(ih : par_reduces_p_star env ({head} ty' x') ({head} ty' x'')) => ",
                        "par_reduces_p_star.step env ({head} ty' x) ({head} ty' x') ({head} ty' x'') ",
                        "({ctor} env ty' ty' x x' (par_reduces_p.refl env ty') hstep) ih) ",
                        "body body' hbody)"
                    ),
                    head = head,
                    ctor = ctor,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "{label} congruence at the par_reduces_p_star level: ty =>* ty' and body =>* body' give ",
                        "{head} ty body =>* {head} ty' body'. Two one-sided star inductions composed by ",
                        "par_reduces_p_star_trans; each single step lifts via {ctor} with a reflexive companion. ",
                        "p-side mirror of par_reduces_c_star_{label}. DerivedProved, zero axiom_deps. ",
                        "Part of #2859 (Increment F++, design §17)."
                    ),
                    label = label,
                    head = head,
                    ctor = ctor,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_p".to_string(),
                    ctor.to_string(),
                    "par_reduces_p.refl".to_string(),
                    "par_reduces_p_star".to_string(),
                    "par_reduces_p_star.refl".to_string(),
                    "par_reduces_p_star.step".to_string(),
                    "par_reduces_p_star.rec".to_string(),
                    "par_reduces_p_star_trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }

    /// The (iota,app) SPINE-CONGRUENCE substrate for `par_reduces_p` — the pointwise
    /// par-list relation `par_reduces_p_list` and the `apply_spine` / `list_append`
    /// congruences. Mechanical mirrors of the `par_reduces_c_list` / `apply_spine_par_c`
    /// family (the relation is the only difference); these are the spine lemmas the
    /// `par_reduces_p` reduct congruence (`r ⇒_p rm` from `e2 ⇒_p m`) is built from.
    fn add_par_reduces_p_spine(&mut self) -> Result<(), SpecError> {
        // par_reduces_p_list: pointwise parallel reduction of KExpr lists.
        self.add_inductive(
            r"inductive par_reduces_p_list (env : RecEnv) : ListType KExpr → ListType KExpr → Type
| nil : par_reduces_p_list env (ListType.nil KExpr) (ListType.nil KExpr)
| cons : forall (x : KExpr) (x' : KExpr) (xs : ListType KExpr) (xs' : ListType KExpr), par_reduces_p env x x' → par_reduces_p_list env xs xs' → par_reduces_p_list env (ListType.cons KExpr x xs) (ListType.cons KExpr x' xs')",
            "par_reduces_p_list env xs xs' — pointwise parallel reduction of KExpr lists for the proper \
             relation (nil to nil; cons reduces head and tail). The spine-argument relation the \
             par_reduces_p reduct congruence consumes. Part of #2859 (Increment F+).",
        )?;

        // apply_spine_par_p: apply_spine is a par_reduces_p congruence.
        self.add_definition(SpecDefinition {
            name: "apply_spine_par_p".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (head : KExpr) (head' : KExpr), ",
                "par_reduces_p_list env xs xs' -> par_reduces_p env head head' -> ",
                "par_reduces_p env (apply_spine xs head) (apply_spine xs' head')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (head : KExpr) (head' : KExpr) ",
                    "(hl : par_reduces_p_list env xs xs') (hh : par_reduces_p env head head') => ",
                    "par_reduces_p_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_ : par_reduces_p_list env a a') => ",
                    "forall (h : KExpr) (h' : KExpr), par_reduces_p env h h' -> ",
                    "par_reduces_p env (apply_spine a h) (apply_spine a' h')) ",
                    "(fun (h : KExpr) (h' : KExpr) (hp : par_reduces_p env h h') => ",
                    "Eq.substType KExpr ",
                    "(fun (Z : KExpr) => par_reduces_p env (apply_spine (ListType.nil KExpr) h) Z) ",
                    "h' (apply_spine (ListType.nil KExpr) h') ",
                    "(Eq.symm KExpr (apply_spine (ListType.nil KExpr) h') h' (apply_spine_nil h')) ",
                    "(Eq.substType KExpr ",
                    "(fun (Z : KExpr) => par_reduces_p env Z h') ",
                    "h (apply_spine (ListType.nil KExpr) h) ",
                    "(Eq.symm KExpr (apply_spine (ListType.nil KExpr) h) h (apply_spine_nil h)) ",
                    "hp)) ",
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : par_reduces_p env x x') (hxs : par_reduces_p_list env xs0 xs0') ",
                    "(ihxs : forall (h : KExpr) (h' : KExpr), par_reduces_p env h h' -> ",
                    "par_reduces_p env (apply_spine xs0 h) (apply_spine xs0' h')) => ",
                    "fun (h : KExpr) (h' : KExpr) (hp : par_reduces_p env h h') => ",
                    "Eq.substType KExpr ",
                    "(fun (Z : KExpr) => par_reduces_p env (apply_spine (ListType.cons KExpr x xs0) h) Z) ",
                    "(apply_spine xs0' (KExpr.app h' x')) (apply_spine (ListType.cons KExpr x' xs0') h') ",
                    "(Eq.symm KExpr (apply_spine (ListType.cons KExpr x' xs0') h') (apply_spine xs0' (KExpr.app h' x')) ",
                    "(apply_spine_cons x' xs0' h')) ",
                    "(Eq.substType KExpr ",
                    "(fun (Z : KExpr) => par_reduces_p env Z (apply_spine xs0' (KExpr.app h' x'))) ",
                    "(apply_spine xs0 (KExpr.app h x)) (apply_spine (ListType.cons KExpr x xs0) h) ",
                    "(Eq.symm KExpr (apply_spine (ListType.cons KExpr x xs0) h) (apply_spine xs0 (KExpr.app h x)) ",
                    "(apply_spine_cons x xs0 h)) ",
                    "(ihxs (KExpr.app h x) (KExpr.app h' x') (par_reduces_p.app env h h' x x' hp hx)))) ",
                    "xs xs' hl head head' hh"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "apply_spine is a par_reduces_p congruence (pointwise-reducing args + reducing head). par_reduces_p_list.rec with the head universalized; nil via apply_spine_nil, cons via par_reduces_p.app + the tail IH + apply_spine_cons. Mirror of apply_spine_par_c. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list.rec".to_string(),
                "apply_spine".to_string(),
                "apply_spine_nil".to_string(),
                "apply_spine_cons".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_list_refl: pointwise reflexivity.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_list_refl".to_string(),
            type_src: "forall (env : RecEnv) (xs : ListType KExpr), par_reduces_p_list env xs xs"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (xs : ListType KExpr) => ",
                    "ListType.rec KExpr ",
                    "(fun (a : ListType KExpr) => par_reduces_p_list env a a) ",
                    "(par_reduces_p_list.nil env) ",
                    "(fun (x : KExpr) (rest : ListType KExpr) (ih : par_reduces_p_list env rest rest) => ",
                    "par_reduces_p_list.cons env x x rest rest (par_reduces_p.refl env x) ih) ",
                    "xs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Reflexivity of pointwise par_reduces_p list reduction (ListType.rec with par_reduces_p.refl at each element). The refl base for spine congruences. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list.nil".to_string(),
                "par_reduces_p_list.cons".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_list_append: pointwise par-reduction respects list_append.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_list_append".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (ys : ListType KExpr) (ys' : ListType KExpr), ",
                "par_reduces_p_list env xs xs' -> par_reduces_p_list env ys ys' -> ",
                "par_reduces_p_list env (list_append xs ys) (list_append xs' ys')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (ys : ListType KExpr) (ys' : ListType KExpr) ",
                    "(hxs : par_reduces_p_list env xs xs') (hys : par_reduces_p_list env ys ys') => ",
                    "par_reduces_p_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_ : par_reduces_p_list env a a') => ",
                    "par_reduces_p_list env (list_append a ys) (list_append a' ys')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env (list_append (ListType.nil KExpr) ys) Z) ",
                    "ys' (list_append (ListType.nil KExpr) ys') ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.nil KExpr) ys') ys' (list_append_nil ys')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env Z ys') ",
                    "ys (list_append (ListType.nil KExpr) ys) ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.nil KExpr) ys) ys (list_append_nil ys)) ",
                    "hys)) ",
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : par_reduces_p env x x') (hxs0 : par_reduces_p_list env xs0 xs0') ",
                    "(ih : par_reduces_p_list env (list_append xs0 ys) (list_append xs0' ys')) => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env (list_append (ListType.cons KExpr x xs0) ys) Z) ",
                    "(ListType.cons KExpr x' (list_append xs0' ys')) (list_append (ListType.cons KExpr x' xs0') ys') ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.cons KExpr x' xs0') ys') (ListType.cons KExpr x' (list_append xs0' ys')) ",
                    "(list_append_cons x' xs0' ys')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env Z (ListType.cons KExpr x' (list_append xs0' ys'))) ",
                    "(ListType.cons KExpr x (list_append xs0 ys)) (list_append (ListType.cons KExpr x xs0) ys) ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.cons KExpr x xs0) ys) (ListType.cons KExpr x (list_append xs0 ys)) ",
                    "(list_append_cons x xs0 ys)) ",
                    "(par_reduces_p_list.cons env x x' (list_append xs0 ys) (list_append xs0' ys') hx ih))) ",
                    "xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Pointwise par_reduces_p respects list_append. par_reduces_p_list.rec on the first list; nil via list_append_nil, cons via par_reduces_p_list.cons + list_append_cons. With kapp_args_app this lifts an app-step into a spine-args congruence. Mirror of par_reduces_c_list_append. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list.rec".to_string(),
                "par_reduces_p_list.cons".to_string(),
                "list_append".to_string(),
                "list_append_nil".to_string(),
                "list_append_cons".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_tail_par_p: pointwise par-reduction respects list_tail.
        // par_reduces_p_list.rec; nil via list_tail_nil, cons exposes the tail field.
        self.add_definition(SpecDefinition {
            name: "list_tail_par_p".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "par_reduces_p_list env xs xs' -> par_reduces_p_list env (list_tail xs) (list_tail xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(hxs : par_reduces_p_list env xs xs') => ",
                    "par_reduces_p_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_ : par_reduces_p_list env a a') => ",
                    "par_reduces_p_list env (list_tail a) (list_tail a')) ",
                    // nil arm
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env (list_tail (ListType.nil KExpr)) Z) ",
                    "(ListType.nil KExpr) (list_tail (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.nil KExpr)) (ListType.nil KExpr) list_tail_nil) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env Z (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) (list_tail (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.nil KExpr)) (ListType.nil KExpr) list_tail_nil) ",
                    "(par_reduces_p_list.nil env))) ",
                    // cons arm
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : par_reduces_p env x x') (hxs0 : par_reduces_p_list env xs0 xs0') ",
                    "(_ih : par_reduces_p_list env (list_tail xs0) (list_tail xs0')) => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env (list_tail (ListType.cons KExpr x xs0)) Z) ",
                    "xs0' (list_tail (ListType.cons KExpr x' xs0')) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.cons KExpr x' xs0')) xs0' (list_tail_cons x' xs0')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env Z xs0') ",
                    "xs0 (list_tail (ListType.cons KExpr x xs0)) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.cons KExpr x xs0)) xs0 (list_tail_cons x xs0)) ",
                    "hxs0)) ",
                    "xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise par-reduction respects list_tail. par_reduces_p_list.rec; nil via list_tail_nil, ",
                "cons exposes the tail field. Mirror of list_map_tail. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list.rec".to_string(),
                "par_reduces_p_list.nil".to_string(),
                "list_tail".to_string(),
                "list_tail_nil".to_string(),
                "list_tail_cons".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_drop_par_p: pointwise par-reduction respects list_drop (the iota
        // reduct's extras/fields/prefix are list_drop/list_take segments). Nat.rec on
        // the offset (motive universalizing the two lists); zero via list_drop_zero,
        // succ via list_drop_succ + list_tail_par_p + the IH. Mirror of list_map_drop.
        self.add_definition(SpecDefinition {
            name: "list_drop_par_p".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "par_reduces_p_list env xs xs' -> par_reduces_p_list env (list_drop n xs) (list_drop n xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(hxs : par_reduces_p_list env xs xs') => ",
                    "Nat.rec ",
                    "(fun (n0 : Nat) => forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "par_reduces_p_list env a a' -> par_reduces_p_list env (list_drop n0 a) (list_drop n0 a')) ",
                    // zero arm
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (ha : par_reduces_p_list env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env (list_drop Nat.zero a) Z) ",
                    "a' (list_drop Nat.zero a') ",
                    "(Eq.symm (ListType KExpr) (list_drop Nat.zero a') a' (list_drop_zero a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env Z a') ",
                    "a (list_drop Nat.zero a) ",
                    "(Eq.symm (ListType KExpr) (list_drop Nat.zero a) a (list_drop_zero a)) ",
                    "ha)) ",
                    // succ arm
                    "(fun (m : Nat) (ihm : forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "par_reduces_p_list env a a' -> par_reduces_p_list env (list_drop m a) (list_drop m a')) => ",
                    "fun (a : ListType KExpr) (a' : ListType KExpr) (ha : par_reduces_p_list env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env (list_drop (Nat.succ m) a) Z) ",
                    "(list_drop m (list_tail a')) (list_drop (Nat.succ m) a') ",
                    "(Eq.symm (ListType KExpr) (list_drop (Nat.succ m) a') (list_drop m (list_tail a')) (list_drop_succ m a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env Z (list_drop m (list_tail a'))) ",
                    "(list_drop m (list_tail a)) (list_drop (Nat.succ m) a) ",
                    "(Eq.symm (ListType KExpr) (list_drop (Nat.succ m) a) (list_drop m (list_tail a)) (list_drop_succ m a)) ",
                    "(ihm (list_tail a) (list_tail a') (list_tail_par_p env a a' ha)))) ",
                    "n xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise par-reduction respects list_drop. Nat.rec on the offset (motive universalizing the ",
                "two lists); zero via list_drop_zero, succ via list_drop_succ + list_tail_par_p + the IH. The ",
                "extras/prefix segments of the iota reduct are list_drop/list_take. Mirror of list_map_drop. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F+)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p_list".to_string(),
                "list_drop".to_string(),
                "list_tail".to_string(),
                "list_tail_par_p".to_string(),
                "list_drop_zero".to_string(),
                "list_drop_succ".to_string(),
                "Nat.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_take_par_p: pointwise par-reduction respects list_take. Nat.rec on
        // the offset (motive universalizing the two lists); succ arm CASE-SPLITS the
        // par_reduces_p_list derivation via par_reduces_p_list.rec and uses the OUTER
        // Nat IH on the cons tail (no inner induction — mirror of list_map_take).
        self.add_definition(SpecDefinition {
            name: "list_take_par_p".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "par_reduces_p_list env xs xs' -> par_reduces_p_list env (list_take n xs) (list_take n xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(hxs : par_reduces_p_list env xs xs') => ",
                    "Nat.rec ",
                    "(fun (n0 : Nat) => forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "par_reduces_p_list env a a' -> par_reduces_p_list env (list_take n0 a) (list_take n0 a')) ",
                    // zero arm: list_take zero _ = nil
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (ha : par_reduces_p_list env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env (list_take Nat.zero a) Z) ",
                    "(ListType.nil KExpr) (list_take Nat.zero a') ",
                    "(Eq.symm (ListType KExpr) (list_take Nat.zero a') (ListType.nil KExpr) (list_take_zero a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env Z (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) (list_take Nat.zero a) ",
                    "(Eq.symm (ListType KExpr) (list_take Nat.zero a) (ListType.nil KExpr) (list_take_zero a)) ",
                    "(par_reduces_p_list.nil env))) ",
                    // succ arm
                    "(fun (m : Nat) (ihm : forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "par_reduces_p_list env a a' -> par_reduces_p_list env (list_take m a) (list_take m a')) => ",
                    "fun (a : ListType KExpr) (a' : ListType KExpr) (h : par_reduces_p_list env a a') => ",
                    "par_reduces_p_list.rec env ",
                    "(fun (b : ListType KExpr) (b' : ListType KExpr) (_ : par_reduces_p_list env b b') => ",
                    "par_reduces_p_list env (list_take (Nat.succ m) b) (list_take (Nat.succ m) b')) ",
                    // inner nil
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env (list_take (Nat.succ m) (ListType.nil KExpr)) Z) ",
                    "(ListType.nil KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) (ListType.nil KExpr) (list_take_succ_nil m)) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env Z (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) (ListType.nil KExpr) (list_take_succ_nil m)) ",
                    "(par_reduces_p_list.nil env))) ",
                    // inner cons: cons x (list_take m xs0), tail via ihm
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : par_reduces_p env x x') (hxs0 : par_reduces_p_list env xs0 xs0') ",
                    "(_ih2 : par_reduces_p_list env (list_take (Nat.succ m) xs0) (list_take (Nat.succ m) xs0')) => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env (list_take (Nat.succ m) (ListType.cons KExpr x xs0)) Z) ",
                    "(ListType.cons KExpr x' (list_take m xs0')) (list_take (Nat.succ m) (ListType.cons KExpr x' xs0')) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.cons KExpr x' xs0')) (ListType.cons KExpr x' (list_take m xs0')) (list_take_succ_cons m x' xs0')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env Z (ListType.cons KExpr x' (list_take m xs0'))) ",
                    "(ListType.cons KExpr x (list_take m xs0)) (list_take (Nat.succ m) (ListType.cons KExpr x xs0)) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.cons KExpr x xs0)) (ListType.cons KExpr x (list_take m xs0)) (list_take_succ_cons m x xs0)) ",
                    "(par_reduces_p_list.cons env x x' (list_take m xs0) (list_take m xs0') hx (ihm xs0 xs0' hxs0)))) ",
                    "a a' h) ",
                    "n xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise par-reduction respects list_take. Nat.rec on the offset; succ arm case-splits the ",
                "derivation (par_reduces_p_list.rec) and uses the outer Nat IH on the cons tail (no inner ",
                "induction). The iota reduct's prefix segment is a list_take. Mirror of list_map_take. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F+)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list.rec".to_string(),
                "par_reduces_p_list.nil".to_string(),
                "par_reduces_p_list.cons".to_string(),
                "list_take".to_string(),
                "list_take_zero".to_string(),
                "list_take_succ_nil".to_string(),
                "list_take_succ_cons".to_string(),
                "Nat.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kapp_args_par_p: extend a spine-args par-reduction by one applied arg.
        // Given the spine args of f par-reduce (kapp_args f ⇒_p_list kapp_args f') and
        // the new last arg reduces (a ⇒_p a'), the spine args of (app f a) par-reduce
        // to those of (app f' a'). Via kapp_args_app (snoc) + par_reduces_p_list_append.
        // The bridge from an app-ctor step to a spine-args congruence (the (iota,app)
        // cross-case feeds this its f-spine congruence + the major/extra arg step).
        self.add_definition(SpecDefinition {
            name: "kapp_args_par_p".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), ",
                "par_reduces_p_list env (kapp_args f) (kapp_args f') -> ",
                "par_reduces_p env a a' -> ",
                "par_reduces_p_list env (kapp_args (KExpr.app f a)) (kapp_args (KExpr.app f' a'))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(hf : par_reduces_p_list env (kapp_args f) (kapp_args f')) ",
                    "(ha : par_reduces_p env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env (kapp_args (KExpr.app f a)) Z) ",
                    "(list_append (kapp_args f') (ListType.cons KExpr a' (ListType.nil KExpr))) (kapp_args (KExpr.app f' a')) ",
                    "(Eq.symm (ListType KExpr) (kapp_args (KExpr.app f' a')) (list_append (kapp_args f') (ListType.cons KExpr a' (ListType.nil KExpr))) (kapp_args_app f' a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => par_reduces_p_list env Z (list_append (kapp_args f') (ListType.cons KExpr a' (ListType.nil KExpr)))) ",
                    "(list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args (KExpr.app f a)) ",
                    "(Eq.symm (ListType KExpr) (kapp_args (KExpr.app f a)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args_app f a)) ",
                    "(par_reduces_p_list_append env (kapp_args f) (kapp_args f') ",
                    "(ListType.cons KExpr a (ListType.nil KExpr)) (ListType.cons KExpr a' (ListType.nil KExpr)) ",
                    "hf ",
                    "(par_reduces_p_list.cons env a a' (ListType.nil KExpr) (ListType.nil KExpr) ha (par_reduces_p_list.nil env)))))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Extend a spine-args par-reduction by one applied arg: kapp_args f ⇒_p_list kapp_args f' and ",
                "a ⇒_p a' give kapp_args (app f a) ⇒_p_list kapp_args (app f' a'). kapp_args_app (snoc) + ",
                "par_reduces_p_list_append. The bridge from an app-ctor step to a spine-args congruence for the ",
                "(iota,app) cross-case. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list.nil".to_string(),
                "par_reduces_p_list.cons".to_string(),
                "par_reduces_p_list_append".to_string(),
                "kapp_args".to_string(),
                "kapp_args_app".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_list_length_eq: pointwise par-reduction preserves list
        // length. par_reduces_p_list.rec; nil = refl 0, cons = succ-cong on the IH
        // through list_length_cons on both sides. The arg-count-stability fact the
        // (iota,app) redex reconstruction needs (the major sits at a FIXED position
        // major_idx in both kapp_args f and kapp_args f', because f ⇒_p f' preserves
        // the spine length).
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_list_length_eq".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "par_reduces_p_list env xs xs' -> Eq Nat (list_length xs) (list_length xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(h : par_reduces_p_list env xs xs') => ",
                    "par_reduces_p_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_h : par_reduces_p_list env a a') => ",
                    "Eq Nat (list_length a) (list_length a')) ",
                    // nil arm: length nil = length nil
                    "(Eq.refl Nat (list_length (ListType.nil KExpr))) ",
                    // cons arm: length (x::xs0) = succ (length xs0) = succ (length xs0') = length (x'::xs0')
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(_hx : par_reduces_p env x x') (_hxs : par_reduces_p_list env xs0 xs0') ",
                    "(ih : Eq Nat (list_length xs0) (list_length xs0')) => ",
                    "Eq.trans Nat ",
                    "(list_length (ListType.cons KExpr x xs0)) ",
                    "(Nat.succ (list_length xs0)) ",
                    "(list_length (ListType.cons KExpr x' xs0')) ",
                    "(list_length_cons x xs0) ",
                    "(Eq.trans Nat ",
                    "(Nat.succ (list_length xs0)) ",
                    "(Nat.succ (list_length xs0')) ",
                    "(list_length (ListType.cons KExpr x' xs0')) ",
                    "(Eq.cong Nat Nat (fun (n : Nat) => Nat.succ n) (list_length xs0) (list_length xs0') ih) ",
                    "(Eq.symm Nat (list_length (ListType.cons KExpr x' xs0')) (Nat.succ (list_length xs0')) (list_length_cons x' xs0')))) ",
                    "xs xs' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise par-reduction preserves list length: par_reduces_p_list xs xs' gives ",
                "list_length xs = list_length xs'. par_reduces_p_list.rec; nil = refl, cons = succ-cong ",
                "on the IH through list_length_cons on both sides. The spine-length-stability fact: the ",
                "iota major premise sits at the SAME position in kapp_args f and kapp_args f' because the ",
                "app-step preserves arg count. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list.rec".to_string(),
                "list_length".to_string(),
                "list_length_cons".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_par_reduces_p_subst()?;
        self.add_par_reduces_p_subst_full()?;

        // par_subst_p_star: the depth-0 substitution congruence at the
        // par_reduces_p_star level. body =>* body' and val =>* val' give
        // instantiate body val =>* instantiate body' val'. Two one-sided star inductions
        // composed by par_reduces_p_star_trans through the waypoint instantiate body' val;
        // each single step lifts via par_subst_p (at depth Nat.zero, since
        // instantiate x y = instantiate_at x y Nat.zero definitionally) with a reflexive
        // companion (par_reduces_p.refl). RecEnvClosed / RecEnvLiftClosed gated
        // (par_subst_p's gates). Registered HERE, AFTER add_par_reduces_p_subst_full (which
        // registers par_subst_p, its single-step ingredient), so the dependency is in scope
        // (the par_reduces_p_star.{rec,refl,step} / _trans substrate was registered earlier
        // in add_par_reduces_p_star). The star-valued beta/let development the STAR-valued
        // marked triangle's contraction arms need. DerivedProved, zero axiom_deps.
        // Part of #2859 (Increment F++, design §17).
        self.add_definition(SpecDefinition {
            name: "par_subst_p_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (body : KExpr) (body' : KExpr) (val : KExpr) (val' : KExpr), ",
                "par_reduces_p_star env body body' -> par_reduces_p_star env val val' -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_p_star env (instantiate body val) (instantiate body' val')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (body : KExpr) (body' : KExpr) (val : KExpr) (val' : KExpr) ",
                    "(hbody : par_reduces_p_star env body body') (hval : par_reduces_p_star env val val') ",
                    "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
                    "par_reduces_p_star_trans env ",
                    "(instantiate body val) (instantiate body' val) (instantiate body' val') ",
                    // left leg: instantiate body val =>* instantiate body' val  (induct on hbody, fix val)
                    "(par_reduces_p_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_p_star env x y) => ",
                    "par_reduces_p_star env (instantiate x val) (instantiate y val)) ",
                    "(fun (x : KExpr) => par_reduces_p_star.refl env (instantiate x val)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_p env x x') (_htail : par_reduces_p_star env x' x'') ",
                    "(ih : par_reduces_p_star env (instantiate x' val) (instantiate x'' val)) => ",
                    "par_reduces_p_star.step env (instantiate x val) (instantiate x' val) (instantiate x'' val) ",
                    "(par_subst_p env x x' val val Nat.zero hstep (par_reduces_p.refl env val) closed liftclosed) ih) ",
                    "body body' hbody) ",
                    // right leg: instantiate body' val =>* instantiate body' val'  (induct on hval, fix body')
                    "(par_reduces_p_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_p_star env x y) => ",
                    "par_reduces_p_star env (instantiate body' x) (instantiate body' y)) ",
                    "(fun (x : KExpr) => par_reduces_p_star.refl env (instantiate body' x)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : par_reduces_p env x x') (_htail : par_reduces_p_star env x' x'') ",
                    "(ih : par_reduces_p_star env (instantiate body' x') (instantiate body' x'')) => ",
                    "par_reduces_p_star.step env (instantiate body' x) (instantiate body' x') (instantiate body' x'') ",
                    "(par_subst_p env body' body' x x' Nat.zero (par_reduces_p.refl env body') hstep closed liftclosed) ih) ",
                    "val val' hval)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "depth-0 substitution congruence at the par_reduces_p_star level: body =>* body' and val =>* val' ",
                "give instantiate body val =>* instantiate body' val'. Two one-sided star inductions composed by ",
                "par_reduces_p_star_trans through instantiate body' val; each single step lifts via par_subst_p at ",
                "depth Nat.zero (instantiate x y = instantiate_at x y Nat.zero definitionally) with a reflexive ",
                "companion. RecEnvClosed / RecEnvLiftClosed gated. The star-valued beta/let development the ",
                "STAR-valued marked triangle needs. DerivedProved, zero axiom_deps. Part of #2859 (design §17)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_subst_p".to_string(),
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star.refl".to_string(),
                "par_reduces_p_star.step".to_string(),
                "par_reduces_p_star.rec".to_string(),
                "par_reduces_p_star_trans".to_string(),
                "instantiate".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The substitution substrate for `par_reduces_p`, lifted from the `par_reduces_c`
    /// substitution lemmas through the embedding `par_reduces_c_subsumes_par_p` — these
    /// are trivial wrappers (no re-proof). `par_lift_p` / `par_subst_refl_p` lift a
    /// bd-value reduction into a lifted/substituted body; `iota_step_subst_p` lifts the
    /// E-core (an iota fire commutes with instantiate). They feed the 1-step
    /// substitution lemma `par_subst_p` and the complete-development triangle.
    fn add_par_reduces_p_subst(&mut self) -> Result<(), SpecError> {
        // par_lift_p: a bd-value reduction lifts through lift_at (wrapper over par_lift_c).
        self.add_definition(SpecDefinition {
            name: "par_lift_p".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (v : KExpr) (v' : KExpr) (c : Nat) (a : Nat), ",
                "par_reduces_bd v v' -> par_reduces_p env (lift_at v c a) (lift_at v' c a)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (v : KExpr) (v' : KExpr) (c : Nat) (a : Nat) ",
                    "(h : par_reduces_bd v v') => ",
                    "par_reduces_c_subsumes_par_p env (lift_at v c a) (lift_at v' c a) ",
                    "(par_lift_c env v v' c a h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Lift congruence for par_reduces_p: a bd-value reduction v => v' lifts through lift_at. Wrapper: par_reduces_c_subsumes_par_p over par_lift_c. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_c_subsumes_par_p".to_string(),
                "par_lift_c".to_string(),
                "lift_at".to_string(),
                "par_reduces_bd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_subst_refl_p: substitute a reducing bd-value into a fixed body (wrapper
        // over par_subst_refl_c). The v-congruence base of the substitution lemma.
        self.add_definition(SpecDefinition {
            name: "par_subst_refl_p".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "par_reduces_bd v v' -> ",
                "par_reduces_p env (instantiate_at e v d) (instantiate_at e v' d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat) ",
                    "(h : par_reduces_bd v v') => ",
                    "par_reduces_c_subsumes_par_p env (instantiate_at e v d) (instantiate_at e v' d) ",
                    "(par_subst_refl_c env e v v' d h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Substitution-into-fixed-body congruence for par_reduces_p: a bd-value v => v' substituted at depth d into a fixed body e. Wrapper: par_reduces_c_subsumes_par_p over par_subst_refl_c. The v-congruence base of par_subst_p. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_c_subsumes_par_p".to_string(),
                "par_subst_refl_c".to_string(),
                "instantiate_at".to_string(),
                "par_reduces_bd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_step_subst_p: the E-core lifted to par_reduces_p — an iota fire commutes
        // with instantiate (inst e v d => inst e' v d when iota_step env e e'), under
        // RecEnvClosed. Wrapper over iota_step_subst_c. The 1-step iota-substitution
        // fact the par_subst_p iota_p arm bakes in (via iota_subst_commutes).
        self.add_definition(SpecDefinition {
            name: "iota_step_subst_p".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat), ",
                "RecEnvClosed env -> iota_step env e e' -> ",
                "par_reduces_p env (instantiate_at e v d) (instantiate_at e' v d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat) ",
                    "(closed : RecEnvClosed env) (h : iota_step env e e') => ",
                    "par_reduces_c_subsumes_par_p env (instantiate_at e v d) (instantiate_at e' v d) ",
                    "(iota_step_subst_c env e e' v d closed h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "E-core lifted to par_reduces_p: under RecEnvClosed, an iota fire commutes with instantiate (inst e v d => inst e' v d when iota_step env e e'). Wrapper over iota_step_subst_c. The iota-substitution fact the par_subst_p iota_p arm bakes in. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_c_subsumes_par_p".to_string(),
                "iota_step_subst_c".to_string(),
                "RecEnvClosed".to_string(),
                "iota_step".to_string(),
                "instantiate_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The FULL (par_reduces_p-valued) lift congruence `par_lift_p_full` — a mirror of
    /// `par_lift_full_c` with the iota arm adapted to the parallel `iota_p` constructor
    /// (the IH lifts the subterm reduction, `iota_lift_commutes` lifts the fired iota,
    /// and `iota_p` reassembles in ONE par-step). The p-valued lift congruence the
    /// p-valued substitution-refl recurses into at the bvar position.
    fn add_par_reduces_p_subst_full(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_lift_p_full".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (v : KExpr) (v' : KExpr) (c : Nat) (a : Nat), ",
                "RecEnvLiftClosed env -> par_reduces_p env v v' -> ",
                "par_reduces_p env (lift_at v c a) (lift_at v' c a)"
            )
            .to_string(),
            value_src: Some(par_lift_p_full_proof()),
            is_axiom: false,
            description: concat!(
                "The FULL par_reduces_p-valued lift congruence: under RecEnvLiftClosed, v ⇒_p v' gives ",
                "lift_at v c a ⇒_p lift_at v' c a. par_reduces_p.rec on v ⇒_p v'; the structural arms (incl. the ",
                "trailing let_cong) mirror ",
                "par_lift_full_c (lift distributes; binder arms recurse at succ c; beta/let transport the ",
                "contracted index via lift_instantiate_swap), and the iota_p arm reassembles in one par-step ",
                "(IH lifts the subterm reduction, iota_lift_commutes lifts the fired iota). DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment F+)."
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
                "par_reduces_p.beta".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p.lam".to_string(),
                "par_reduces_p.pi".to_string(),
                "par_reduces_p.forall_".to_string(),
                "par_reduces_p.let_".to_string(),
                "par_reduces_p.iota_p".to_string(),
                "par_reduces_p.let_cong".to_string(),
                "iota_step".to_string(),
                "iota_lift_commutes".to_string(),
                "RecEnvLiftClosed".to_string(),
                "lift_at".to_string(),
                "instantiate_at".to_string(),
                "lift_instantiate_swap".to_string(),
                "nat_zero_add".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "par_subst_refl_p_full".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "RecEnvLiftClosed env -> par_reduces_p env v v' -> ",
                "par_reduces_p env (instantiate_at e v d) (instantiate_at e v' d)"
            )
            .to_string(),
            value_src: Some(par_subst_refl_p_full_proof()),
            is_axiom: false,
            description: concat!(
                "The FULL par_reduces_p-valued reflexive substitution congruence: substituting a ",
                "parallel-reducing value v ⇒_p v' into a FIXED term e at depth d yields a SINGLE-step ",
                "par_reduces_p between the instantiations. c→p mirror of par_subst_refl_full_c but ",
                "concluding a single par_reduces_p (not _star): KExpr.rec on e with the triple-Nat.rec ",
                "convoy at the bvar arm; the i=d leaf calls par_lift_p_full (the FULL p-valued lift ",
                "congruence) DIRECTLY in one step, structural arms use par_reduces_p.{refl,app,lam,pi}. ",
                "Threads RecEnvLiftClosed (which par_lift_p_full gates on). DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F+)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p.lam".to_string(),
                "par_reduces_p.pi".to_string(),
                "par_reduces_p.let_cong".to_string(),
                "par_lift_p_full".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate_at".to_string(),
                "lift_at".to_string(),
                "KExpr.rec".to_string(),
                "Nat.rec".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at".to_string(),
                "instantiate_bvar_at_below".to_string(),
                "instantiate_bvar_at_above".to_string(),
                "instantiate_at_bvar_eq_from_zero_witnesses".to_string(),
                "nat_pos_witness_from_succ_eq".to_string(),
                "nat_sub_zero_of_sub_pos".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "par_subst_p".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (v' : KExpr) (d : Nat), ",
                "par_reduces_p env e e' -> par_reduces_p env v v' -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_p env (instantiate_at e v d) (instantiate_at e' v' d)"
            )
            .to_string(),
            value_src: Some(par_subst_p_proof()),
            is_axiom: false,
            description: concat!(
                "The 1-step substitution lemma for par_reduces_p — the payoff of the parallel-iota relation. ",
                "Given e ⇒_p e' and v ⇒_p v' (and both closure predicates), the instantiations reduce in a ",
                "SINGLE par_reduces_p step (NOT _star). c→p single-step mirror of par_subst_full_c: ",
                "par_reduces_p.rec on e ⇒_p e'; structural arms rewrite the _star congruences to the matching ",
                "par_reduces_p constructors (refl via par_subst_refl_p_full, app/lam/pi/forall_/let_cong via the ",
                "ctors, beta/let_ via the ctor + instantiate_nested_commutes_zero_subst transport), and the iota_p arm ",
                "reassembles in ONE step: the IH gives the premise par_reduces_p (inst e0 v d)(inst e2 v' d) and ",
                "iota_subst_commutes lifts the fired iota to iota_step (inst e2 v' d)(inst r v' d), so iota_p ",
                "concludes par_reduces_p (inst e0 v d)(inst r v' d). DerivedProved, zero axiom_deps. Part of ",
                "#2859 (Increment F+)."
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
                "par_reduces_p.beta".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p.lam".to_string(),
                "par_reduces_p.pi".to_string(),
                "par_reduces_p.forall_".to_string(),
                "par_reduces_p.let_".to_string(),
                "par_reduces_p.iota_p".to_string(),
                "par_reduces_p.let_cong".to_string(),
                "par_subst_refl_p_full".to_string(),
                "iota_subst_commutes".to_string(),
                "iota_step".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "instantiate_at".to_string(),
                "instantiate_nested_commutes_zero_subst".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `par_lift_p_full` — c→p mirror of `par_lift_full_c_proof`
/// (par_reduces_c.rs) with the iota arm adapted to `iota_p`: the IH lifts the subterm
/// reduction (lift e0 ⇒_p lift e2), `iota_lift_commutes` lifts the fired iota
/// (iota_step (lift e2)(lift r)), and `iota_p` reassembles in ONE par-step.
fn par_lift_p_full_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p env e e') => ",
        "forall (c : Nat) (a : Nat), RecEnvLiftClosed env -> ",
        "par_reduces_p env (lift_at e c a) (lift_at e' c a))"
    );
    let ih = concat!(
        "forall (c : Nat) (a : Nat), RecEnvLiftClosed env -> ",
        "par_reduces_p env (lift_at SUB c a) (lift_at SUB' c a)"
    );
    let refl_arm = concat!(
        "(fun (e : KExpr) (c : Nat) (a : Nat) (_liftclosed : RecEnvLiftClosed env) => ",
        "par_reduces_p.refl env (lift_at e c a))"
    );
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) ",
            "(_hf : par_reduces_p env f f') (_ha : par_reduces_p env a0 a0') ",
            "(ihf : {ih_f}) (iha : {ih_a}) (c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p.app env (lift_at f c a) (lift_at f' c a) ",
            "(lift_at a0 c a) (lift_at a0' c a) (ihf c a liftclosed) (iha c a liftclosed))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );
    // beta/let contraction transport (relation = par_reduces_p; eq is shared lift algebra).
    let contract = |lhs_head: &str, ctor_term: &str, bodyp: &str, argp: &str| -> String {
        let goal_lhs = format!("(lift_at (instantiate_at {bodyp} {argp} Nat.zero) c a)");
        let swap_lhs =
            format!("(lift_at (instantiate_at {bodyp} {argp} Nat.zero) (Nat.add Nat.zero c) a)");
        let swap_rhs = format!(
            "(instantiate_at (lift_at {bodyp} (Nat.succ (Nat.add Nat.zero c)) a) (lift_at {argp} c a) Nat.zero)"
        );
        let goal_rhs = format!(
            "(instantiate_at (lift_at {bodyp} (Nat.succ c) a) (lift_at {argp} c a) Nat.zero)"
        );
        let swap_raw = format!("(lift_instantiate_swap {bodyp} {argp} Nat.zero c a)");
        let cong_lhs = format!(
            "(Eq.cong Nat KExpr (fun (n : Nat) => lift_at (instantiate_at {bodyp} {argp} Nat.zero) n a) c (Nat.add Nat.zero c) (Eq.symm Nat (Nat.add Nat.zero c) c (nat_zero_add c)))"
        );
        let cong_rhs = format!(
            "(Eq.cong Nat KExpr (fun (n : Nat) => instantiate_at (lift_at {bodyp} (Nat.succ n) a) (lift_at {argp} c a) Nat.zero) (Nat.add Nat.zero c) c (nat_zero_add c))"
        );
        let eq = format!(
            "(Eq.trans KExpr {goal_lhs} {swap_lhs} {goal_rhs} {cong_lhs} (Eq.trans KExpr {swap_lhs} {swap_rhs} {goal_rhs} {swap_raw} {cong_rhs}))"
        );
        let p = format!("(fun (x : KExpr) => par_reduces_p env {lhs_head} x)");
        format!(
            "(Eq.substType KExpr {p} {goal_rhs} {goal_lhs} (Eq.symm KExpr {goal_lhs} {goal_rhs} {eq}) {ctor_term})"
        )
    };
    let beta_lhs_head = concat!(
        "(KExpr.app (KExpr.lam (lift_at A c a) (lift_at body (Nat.succ c) a)) ",
        "(lift_at arg c a))"
    );
    let beta_ctor = concat!(
        "(par_reduces_p.beta env (lift_at A c a) (lift_at A' c a) ",
        "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
        "(lift_at arg c a) (lift_at arg' c a) ",
        "(ihA c a liftclosed) (ihbody (Nat.succ c) a liftclosed) (iharg c a liftclosed))"
    );
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_p env A A') (_hbody : par_reduces_p env body body') ",
            "(_harg : par_reduces_p env arg arg') ",
            "(ihA : {ih_A}) (ihbody : {ih_body}) (iharg : {ih_arg}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
        body = contract(beta_lhs_head, beta_ctor, "body'", "arg'"),
    );
    let binder_arm = |ctor: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(_hty : par_reduces_p env ty ty') (_hbody : par_reduces_p env body body') ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) (c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
                "{ctor} env (lift_at ty c a) (lift_at ty' c a) ",
                "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
                "(ihty c a liftclosed) (ihbody (Nat.succ c) a liftclosed))"
            ),
            ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
            ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
            ctor = ctor,
        )
    };
    // let_ (ZETA): source lift_at (KExpr.let_ ty val body) c a = KExpr.let_ (lift ty)(lift val)
    // (lift body succ) (genuine ctor, no longer the app(lam) alias); ctor target instantiates,
    // transported to the goal RHS by the shared lift-instantiate contract.
    let let_lhs_head =
        "(KExpr.let_ (lift_at ty c a) (lift_at val c a) (lift_at body (Nat.succ c) a))";
    let let_ctor = concat!(
        "(par_reduces_p.let_ env (lift_at ty c a) (lift_at ty' c a) ",
        "(lift_at val c a) (lift_at val' c a) ",
        "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
        "(ihty c a liftclosed) (ihval c a liftclosed) (ihbody (Nat.succ c) a liftclosed))"
    );
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') ",
            "(_hbody : par_reduces_p env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        body = contract(let_lhs_head, let_ctor, "body'", "val'"),
    );
    // let_cong (trailing CONGRUENCE): both sides are genuine lets; lift distributes over let_
    // definitionally, so par_reduces_p.let_cong on the lifted IHs concludes directly.
    let let_cong_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') ",
            "(_hbody : par_reduces_p env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p.let_cong env (lift_at ty c a) (lift_at ty' c a) ",
            "(lift_at val c a) (lift_at val' c a) ",
            "(lift_at body (Nat.succ c) a) (lift_at body' (Nat.succ c) a) ",
            "(ihty c a liftclosed) (ihval c a liftclosed) (ihbody (Nat.succ c) a liftclosed))"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
    );
    // iota_p arm: source e0 ⇒_p e2 then iota_step e2 r. IH lifts e0⇒_p e2 to
    // lift e0 ⇒_p lift e2; iota_lift_commutes lifts the fired iota to
    // iota_step (lift e2)(lift r); iota_p reassembles in ONE par-step.
    let iota_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e2 : KExpr) (r : KExpr) ",
            "(_hp : par_reduces_p env e0 e2) (hi : iota_step env e2 r) ",
            "(ihp : {ih_e0e2}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p.iota_p env (lift_at e0 c a) (lift_at e2 c a) (lift_at r c a) ",
            "(ihp c a liftclosed) ",
            "(iota_lift_commutes env e2 r c a liftclosed hi))"
        ),
        ih_e0e2 = ih.replace("SUB'", "e2").replace("SUB", "e0"),
    );
    // proj arm: lift descends into the scrutinee; congruence via par_reduces_p.proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_p env sub sub') (ihsub : {ih_sub}) ",
            "(c : Nat) (a : Nat) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p.proj env s i (lift_at sub c a) (lift_at sub' c a) ",
            "(ihsub c a liftclosed))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );
    format!(
        concat!(
            "fun (env : RecEnv) (v0 : KExpr) (v0' : KExpr) (c0 : Nat) (a0 : Nat) ",
            "(liftclosed0 : RecEnvLiftClosed env) (h0 : par_reduces_p env v0 v0') => ",
            "par_reduces_p.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "v0 v0' h0 c0 a0 liftclosed0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_p.lam"),
        pi_arm = binder_arm("par_reduces_p.pi"),
        forall_arm = binder_arm("par_reduces_p.forall_"),
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_subst_refl_p_full` — c→p single-step mirror of
/// `par_subst_refl_full_c_proof` (par_reduces_c.rs). Identical KExpr.rec-on-body
/// structure with the triple-Nat.rec convoy at the bvar arm, but concludes a SINGLE
/// `par_reduces_p` (not `par_reduces_c_star`): structural arms use
/// `par_reduces_p.{refl,app,lam,pi}`, and the i=d bvar leaf calls `par_lift_p_full`
/// DIRECTLY (one par-step, no subsume-to-star). All eq-algebra helpers are
/// relation-agnostic and shared verbatim.
fn par_subst_refl_p_full_proof() -> String {
    // Motive over the recursed term e: universalize v, v', d; thread RecEnvLiftClosed.
    let motive = concat!(
        "(fun (e : KExpr) => forall (v : KExpr) (v' : KExpr) (d : Nat), ",
        "RecEnvLiftClosed env -> par_reduces_p env v v' -> ",
        "par_reduces_p env (instantiate_at e v d) (instantiate_at e v' d))"
    );
    // IH shape for a sub-term SUB.
    let ih = concat!(
        "forall (v : KExpr) (v' : KExpr) (d : Nat), RecEnvLiftClosed env -> ",
        "par_reduces_p env v v' -> ",
        "par_reduces_p env (instantiate_at SUB v d) (instantiate_at SUB v' d)"
    );

    // Goal G(i) for the bvar arm.
    let goal_l = "(instantiate_at (KExpr.bvar i) v d)";
    let goal_r = "(instantiate_at (KExpr.bvar i) v' d)";

    // transport: given X X' eqL eqR T, produce
    //   par_reduces_p env (instantiate_at (bvar i) v d) (instantiate_at (bvar i) v' d)
    // from T : par_reduces_p env X X', eqL : goal_l = X, eqR : goal_r = X'.
    let transport = |xl: &str, xr: &str, eql: &str, eqr: &str, t: &str| -> String {
        // inner : par_reduces_p env goal_l X'  (rewrite X -> goal_l on first index)
        let inner = format!(
            concat!(
                "(Eq.substType KExpr (fun (y : KExpr) => par_reduces_p env y {xr}) ",
                "{xl} {goal_l} ",
                "(Eq.symm KExpr {goal_l} {xl} {eql}) {t})"
            ),
            xr = xr,
            xl = xl,
            goal_l = goal_l,
            eql = eql,
            t = t,
        );
        // outer : par_reduces_p env goal_l goal_r (rewrite X' -> goal_r on 2nd index)
        format!(
            concat!(
                "(Eq.substType KExpr ",
                "(fun (y : KExpr) => par_reduces_p env {goal_l} y) ",
                "{xr} {goal_r} ",
                "(Eq.symm KExpr {goal_r} {xr} {eqr}) {inner})"
            ),
            goal_l = goal_l,
            xr = xr,
            goal_r = goal_r,
            eqr = eqr,
            inner = inner,
        )
    };

    // LEAF: i = d (h_id : sub i d = 0, h_di0 : sub d i = 0). The substituted value
    // is lifted by the binder depth d: par_lift_p_full v v' 0 d, in ONE par-step.
    let leaf_eq = {
        let xl = "(lift_at v Nat.zero d)";
        let xr = "(lift_at v' Nat.zero d)";
        let eql = "(instantiate_at_bvar_eq_from_zero_witnesses i d v h_di0 h_id)";
        let eqr = "(instantiate_at_bvar_eq_from_zero_witnesses i d v' h_di0 h_id)";
        let t = "(par_lift_p_full env v v' Nat.zero d liftclosed h)";
        transport(xl, xr, eql, eqr, t)
    };

    // LEAF: i < d (h_di : sub d i = succ k2, h_id : sub i d = 0). Both = bvar i.
    let leaf_below = {
        let w_di = "(nat_pos_witness_from_succ_eq (Nat.sub d i) k2 h_di)";
        let xl = "(KExpr.bvar i)";
        let xr = "(KExpr.bvar i)";
        let eql = format!(
            concat!(
                "(Eq.trans KExpr {goal_l} (instantiate_bvar_at i d v) (KExpr.bvar i) ",
                "(instantiate_at_bvar i v d) ",
                "(instantiate_bvar_at_below i d v {w_di}))"
            ),
            goal_l = goal_l,
            w_di = w_di,
        );
        let eqr = format!(
            concat!(
                "(Eq.trans KExpr {goal_r} (instantiate_bvar_at i d v') (KExpr.bvar i) ",
                "(instantiate_at_bvar i v' d) ",
                "(instantiate_bvar_at_below i d v' {w_di}))"
            ),
            goal_r = goal_r,
            w_di = w_di,
        );
        let t = "(par_reduces_p.refl env (KExpr.bvar i))";
        transport(xl, xr, &eql, &eqr, t)
    };

    // LEAF: i > d (h_id : sub i d = succ k4). Both = bvar (i-1).
    let leaf_above = {
        let h_di0 = "(nat_sub_zero_of_sub_pos i d k4 h_id)";
        let w_id = "(nat_pos_witness_from_succ_eq (Nat.sub i d) k4 h_id)";
        let xl = "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))";
        let xr = "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))";
        let eql = format!(
            concat!(
                "(Eq.trans KExpr {goal_l} (instantiate_bvar_at i d v) ",
                "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
                "(instantiate_at_bvar i v d) ",
                "(instantiate_bvar_at_above i d v {h_di0} {w_id}))"
            ),
            goal_l = goal_l,
            h_di0 = h_di0,
            w_id = w_id,
        );
        let eqr = format!(
            concat!(
                "(Eq.trans KExpr {goal_r} (instantiate_bvar_at i d v') ",
                "(KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) ",
                "(instantiate_at_bvar i v' d) ",
                "(instantiate_bvar_at_above i d v' {h_di0} {w_id}))"
            ),
            goal_r = goal_r,
            h_di0 = h_di0,
            w_id = w_id,
        );
        let t = "(par_reduces_p.refl env (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))))";
        transport(xl, xr, &eql, &eqr, t)
    };

    // bvar arm: double-Nat.rec convoy (same shape as par_subst_refl_full_c).
    let bvar_arm = format!(
        concat!(
            "(fun (i : Nat) (v : KExpr) (v' : KExpr) (d : Nat) ",
            "(liftclosed : RecEnvLiftClosed env) (h : par_reduces_p env v v') => ",
            // OUTER Nat.rec on sub(i, d)
            "Nat.rec ",
            "(fun (g : Nat) => Eq Nat (Nat.sub i d) g -> ",
            "par_reduces_p env {goal_l} {goal_r}) ",
            // OUTER ZERO: sub(i,d) = 0
            "(fun (h_id : Eq Nat (Nat.sub i d) Nat.zero) => ",
            // MIDDLE Nat.rec on sub(d, i)
            "Nat.rec ",
            "(fun (g2 : Nat) => Eq Nat (Nat.sub d i) g2 -> ",
            "par_reduces_p env {goal_l} {goal_r}) ",
            // MIDDLE ZERO: sub(d,i) = 0 (i = d)
            "(fun (h_di0 : Eq Nat (Nat.sub d i) Nat.zero) => {leaf_eq}) ",
            // MIDDLE SUCC: sub(d,i) = succ k2 (i < d)
            "(fun (k2 : Nat) ",
            "(_ : Eq Nat (Nat.sub d i) k2 -> par_reduces_p env {goal_l} {goal_r}) ",
            "(h_di : Eq Nat (Nat.sub d i) (Nat.succ k2)) => {leaf_below}) ",
            "(Nat.sub d i) (Eq.refl Nat (Nat.sub d i))) ",
            // OUTER SUCC: sub(i,d) = succ k4 (i > d)
            "(fun (k4 : Nat) ",
            "(_ : Eq Nat (Nat.sub i d) k4 -> par_reduces_p env {goal_l} {goal_r}) ",
            "(h_id : Eq Nat (Nat.sub i d) (Nat.succ k4)) => {leaf_above}) ",
            "(Nat.sub i d) (Eq.refl Nat (Nat.sub i d)))"
        ),
        goal_l = goal_l,
        goal_r = goal_r,
        leaf_eq = leaf_eq,
        leaf_below = leaf_below,
        leaf_above = leaf_above,
    );

    // sort/const arms — refl.
    let sort_arm = concat!(
        "(fun (sv : Level) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_lc : RecEnvLiftClosed env) (_h : par_reduces_p env v v') => ",
        "par_reduces_p.refl env (KExpr.sort sv))"
    );
    let const_arm = concat!(
        "(fun (nm : Name) (us : ListType Level) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_lc : RecEnvLiftClosed env) (_h : par_reduces_p env v v') => ",
        "par_reduces_p.refl env (KExpr.const nm us))"
    );

    // app arm: the app congruence on the two IHs.
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (a0 : KExpr) ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_p env v v') => ",
            "par_reduces_p.app env ",
            "(instantiate_at f v d) (instantiate_at f v' d) ",
            "(instantiate_at a0 v d) (instantiate_at a0 v' d) ",
            "(ihf v v' d lc h) (iha v v' d lc h))"
        ),
        ih_f = ih.replace("SUB", "f"),
        ih_a = ih.replace("SUB", "a0"),
    );

    // lam/pi arm parametric in the binder congruence (body IH at succ d).
    let binder_arm = |star_cong: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (body : KExpr) ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) ",
                "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_p env v v') => ",
                "{star_cong} env ",
                "(instantiate_at ty v d) (instantiate_at ty v' d) ",
                "(instantiate_at body v (Nat.succ d)) (instantiate_at body v' (Nat.succ d)) ",
                "(ihty v v' d lc h) (ihbody v v' (Nat.succ d) lc h))"
            ),
            ih_ty = ih.replace("SUB", "ty"),
            ih_body = ih.replace("SUB", "body"),
            star_cong = star_cong,
        )
    };

    // let_ arm (KExpr now has a genuine 7th let_ ctor): three-subterm value-congruence.
    // instantiate_at (KExpr.let_ ty val body) v d = KExpr.let_ (inst ty)(inst val)(inst body
    // succ) definitionally, so par_reduces_p.let_cong on the fixed-body IHs concludes (ty and
    // val recurse at depth d, body at succ d — exactly the lam/pi treatment plus the val field).
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_p env v v') => ",
            "par_reduces_p.let_cong env ",
            "(instantiate_at ty v d) (instantiate_at ty v' d) ",
            "(instantiate_at val v d) (instantiate_at val v' d) ",
            "(instantiate_at body v (Nat.succ d)) (instantiate_at body v' (Nat.succ d)) ",
            "(ihty v v' d lc h) (ihval v v' d lc h) (ihbody v v' (Nat.succ d) lc h))"
        ),
        ih_ty = ih.replace("SUB", "ty"),
        ih_val = ih.replace("SUB", "val"),
        ih_body = ih.replace("SUB", "body"),
    );

    // proj arm: subst descends into the scrutinee; congruence via par_reduces_p.proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : {ih_sub}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (lc : RecEnvLiftClosed env) (h : par_reduces_p env v v') => ",
            "par_reduces_p.proj env s i ",
            "(instantiate_at sub v d) (instantiate_at sub v' d) ",
            "(ihsub v v' d lc h))"
        ),
        ih_sub = ih.replace("SUB", "sub"),
    );

    // lit arm: a numeral is closed, so instantiate_at (lit n) v d = lit n; refl.
    let lit_arm = concat!(
        "(fun (litv : Nat) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(_lc : RecEnvLiftClosed env) (_h : par_reduces_p env v v') => ",
        "par_reduces_p.refl env (KExpr.lit litv))"
    );

    format!(
        concat!(
            "fun (env : RecEnv) (e0 : KExpr) => ",
            "KExpr.rec {motive} ",
            "{sort_arm} {bvar_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {const_arm} {let_arm} {proj_arm} {lit_arm} ",
            "e0"
        ),
        motive = motive,
        sort_arm = sort_arm,
        bvar_arm = bvar_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_p.lam"),
        pi_arm = binder_arm("par_reduces_p.pi"),
        const_arm = const_arm,
        let_arm = let_arm,
        proj_arm = proj_arm,
        lit_arm = lit_arm,
    )
}

/// Closed proof term for `par_reduces_c_subsumes_par_p`. par_reduces_c.rec mapping
/// each constructor to the matching par_reduces_p constructor via the recursor IHs;
/// the atomic iota maps to iota_p with a reflexive subterm-reduction premise.
fn par_reduces_c_subsumes_par_p_proof() -> String {
    concat!(
        "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (h : par_reduces_c env e e') => ",
        "par_reduces_c.rec env ",
        "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_c env x y) => par_reduces_p env x y) ",
        // refl
        "(fun (a : KExpr) => par_reduces_p.refl env a) ",
        // beta
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_c env A A') (_hbody : par_reduces_c env body body') (_harg : par_reduces_c env arg arg') ",
        "(ihA : par_reduces_p env A A') (ihbody : par_reduces_p env body body') (iharg : par_reduces_p env arg arg') => ",
        "par_reduces_p.beta env A A' body body' arg arg' ihA ihbody iharg) ",
        // app
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_hf : par_reduces_c env f f') (_ha : par_reduces_c env a a') ",
        "(ihf : par_reduces_p env f f') (iha : par_reduces_p env a a') => ",
        "par_reduces_p.app env f f' a a' ihf iha) ",
        // lam
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_c env ty ty') (_hbody : par_reduces_c env body body') ",
        "(ihty : par_reduces_p env ty ty') (ihbody : par_reduces_p env body body') => ",
        "par_reduces_p.lam env ty ty' body body' ihty ihbody) ",
        // pi
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_c env dom dom') (_hbody : par_reduces_c env body body') ",
        "(ihd : par_reduces_p env dom dom') (ihbody : par_reduces_p env body body') => ",
        "par_reduces_p.pi env dom dom' body body' ihd ihbody) ",
        // forall_
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_c env dom dom') (_hbody : par_reduces_c env body body') ",
        "(ihd : par_reduces_p env dom dom') (ihbody : par_reduces_p env body body') => ",
        "par_reduces_p.forall_ env dom dom' body body' ihd ihbody) ",
        // let_
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') ",
        "(ihty : par_reduces_p env ty ty') (ihval : par_reduces_p env val val') (ihbody : par_reduces_p env body body') => ",
        "par_reduces_p.let_ env ty ty' val val' body body' ihty ihval ihbody) ",
        // iota (atomic): map to iota_p with a reflexive subterm reduction.
        "(fun (a : KExpr) (a' : KExpr) (hi : iota_step env a a') => ",
        "par_reduces_p.iota_p env a a a' (par_reduces_p.refl env a) hi) ",
        // let_cong (trailing congruence): map to par_reduces_p.let_cong on the IHs.
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_c env ty ty') (_hval : par_reduces_c env val val') (_hbody : par_reduces_c env body body') ",
        "(ihty : par_reduces_p env ty ty') (ihval : par_reduces_p env val val') (ihbody : par_reduces_p env body body') => ",
        "par_reduces_p.let_cong env ty ty' val val' body body' ihty ihval ihbody) ",
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_c env sub sub') (ihsub : par_reduces_p env sub sub') => ",
        "par_reduces_p.proj env s i sub sub' ihsub) ",
        "e e' h"
    )
    .to_string()
}

/// Closed proof term for `par_reduces_p_subsumes_par_c_star`. par_reduces_p.rec into
/// par_reduces_c_star: structural arms via the matching _star congruence on the IHs;
/// iota_p via par_reduces_c_star_trans (IH) ∘ (fired iota subsumed to star).
fn par_reduces_p_subsumes_par_c_star_proof() -> String {
    concat!(
        "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (h : par_reduces_p env e e') => ",
        "par_reduces_p.rec env ",
        "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_p env x y) => par_reduces_c_star env x y) ",
        // refl
        "(fun (a : KExpr) => par_reduces_c_star.refl env a) ",
        // beta
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_p env A A') (_hbody : par_reduces_p env body body') (_harg : par_reduces_p env arg arg') ",
        "(ihA : par_reduces_c_star env A A') (ihbody : par_reduces_c_star env body body') (iharg : par_reduces_c_star env arg arg') => ",
        "par_reduces_c_star_beta env A A' body body' arg arg' ihA ihbody iharg) ",
        // app
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_hf : par_reduces_p env f f') (_ha : par_reduces_p env a a') ",
        "(ihf : par_reduces_c_star env f f') (iha : par_reduces_c_star env a a') => ",
        "par_reduces_c_star_app env f f' a a' ihf iha) ",
        // lam
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_p env ty ty') (_hbody : par_reduces_p env body body') ",
        "(ihty : par_reduces_c_star env ty ty') (ihbody : par_reduces_c_star env body body') => ",
        "par_reduces_c_star_lam env ty ty' body body' ihty ihbody) ",
        // pi
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_p env dom dom') (_hbody : par_reduces_p env body body') ",
        "(ihd : par_reduces_c_star env dom dom') (ihbody : par_reduces_c_star env body body') => ",
        "par_reduces_c_star_pi env dom dom' body body' ihd ihbody) ",
        // forall_
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_p env dom dom') (_hbody : par_reduces_p env body body') ",
        "(ihd : par_reduces_c_star env dom dom') (ihbody : par_reduces_c_star env body body') => ",
        "par_reduces_c_star_forall env dom dom' body body' ihd ihbody) ",
        // let_
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') (_hbody : par_reduces_p env body body') ",
        "(ihty : par_reduces_c_star env ty ty') (ihval : par_reduces_c_star env val val') (ihbody : par_reduces_c_star env body body') => ",
        "par_reduces_c_star_let env ty ty' val val' body body' ihty ihval ihbody) ",
        // iota_p: e ⇒_p e2 (IH ⇒*_c) then iota_step e2 r (⇒_c subsumed), composed by trans.
        "(fun (a : KExpr) (a2 : KExpr) (r : KExpr) ",
        "(_hp : par_reduces_p env a a2) (hi : iota_step env a2 r) ",
        "(ihp : par_reduces_c_star env a a2) => ",
        "par_reduces_c_star_trans env a a2 r ihp ",
        "(par_subsumes_par_c_star env a2 r (par_reduces_c.iota env a2 r hi))) ",
        // let_cong (trailing congruence): lift via the c-star let congruence on the IHs.
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') (_hbody : par_reduces_p env body body') ",
        "(ihty : par_reduces_c_star env ty ty') (ihval : par_reduces_c_star env val val') (ihbody : par_reduces_c_star env body body') => ",
        "par_reduces_c_star_let_cong env ty ty' val val' body body' ihty ihval ihbody) ",
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_p env sub sub') (ihsub : par_reduces_c_star env sub sub') => ",
        "par_reduces_c_star_proj env s i sub sub' ihsub) ",
        "e e' h"
    )
    .to_string()
}

/// Closed proof term for `par_subst_p` — the 1-step substitution lemma for
/// par_reduces_p. c→p single-step mirror of `par_subst_full_c_proof` (par_reduces_c.rs):
/// the same par_reduces_*.rec-on-(e ⇒ e') structure with a depth-generalized motive
/// threading v ⇒_p v' + both closure predicates, but concluding a SINGLE par_reduces_p
/// (not _star). The structural arms rewrite the _star congruences to the matching
/// par_reduces_p constructors (refl via par_subst_refl_p_full, app/lam/pi/forall_ via
/// the ctors, beta/let_ via the ctor + the shared instantiate_nested_commutes_zero_subst
/// transport). The iota arm is the genuinely-new 1-step iota_p arm: the IH delivers the
/// premise par_reduces_p (inst e0 v d)(inst e2 v' d) and iota_subst_commutes lifts the
/// fired iota to iota_step (inst e2 v' d)(inst r v' d), so iota_p concludes in ONE step.
fn par_subst_p_proof() -> String {
    // Depth-generalized, single-step motive threading the full value reduction
    // par_reduces_p env v v' + both closure predicates.
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p env e e') => ",
        "forall (v : KExpr) (v' : KExpr) (d : Nat), par_reduces_p env v v' -> ",
        "RecEnvClosed env -> RecEnvLiftClosed env -> ",
        "par_reduces_p env (instantiate_at e v d) (instantiate_at e' v' d))"
    );
    // IH shape for a sub-derivation SUB => SUB'.
    let ih = concat!(
        "forall (v : KExpr) (v' : KExpr) (d : Nat), par_reduces_p env v v' -> ",
        "RecEnvClosed env -> RecEnvLiftClosed env -> ",
        "par_reduces_p env (instantiate_at SUB v d) (instantiate_at SUB' v' d)"
    );

    // refl arm: par_subst_refl_p_full, already single-step.
    let refl_arm = concat!(
        "(fun (e : KExpr) (v : KExpr) (v' : KExpr) (d : Nat) ",
        "(h : par_reduces_p env v v') (_closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
        "par_subst_refl_p_full env e v v' d liftclosed h)"
    );

    // app arm.
    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (f' : KExpr) (a0 : KExpr) (a0' : KExpr) ",
            "(_hf : par_reduces_p env f f') (_ha : par_reduces_p env a0 a0') ",
            "(ihf : {ih_f}) (iha : {ih_a}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p.app env ",
            "(instantiate_at f v d) (instantiate_at f' v' d) ",
            "(instantiate_at a0 v d) (instantiate_at a0' v' d) ",
            "(ihf v v' d h closed liftclosed) (iha v v' d h closed liftclosed))"
        ),
        ih_f = ih.replace("SUB'", "f'").replace("SUB", "f"),
        ih_a = ih.replace("SUB'", "a0'").replace("SUB", "a0"),
    );

    // lam/pi/forall_ congruence arm, parametric in the par_reduces_p binder ctor.
    let binder_arm = |ctor: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                "(_hty : par_reduces_p env ty ty') (_hbody : par_reduces_p env body body') ",
                "(ihty : {ih_ty}) (ihbody : {ih_body}) ",
                "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p env v v') ",
                "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
                "{ctor} env ",
                "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
                "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
                "(ihty v v' d h closed liftclosed) (ihbody v v' (Nat.succ d) h closed liftclosed))"
            ),
            ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
            ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
            ctor = ctor,
        )
    };

    // beta/let_ contraction transport (same shape as par_subst_full_c's `contract`,
    // at the single-step level). instantiate_nested_commutes_zero_subst bridges the
    // contraction-congruence RHS to the goal RHS.
    let contract = |lhs_head: &str, ctor_term: &str, bodyp: &str, argp: &str| -> String {
        let goal_rhs = format!(
            "(instantiate_at (instantiate_at {bodyp} {argp} Nat.zero) v' d)",
            bodyp = bodyp,
            argp = argp,
        );
        let ctor_rhs = format!(
            concat!(
                "(instantiate_at (instantiate_at {bodyp} v' (Nat.succ d)) ",
                "(instantiate_at {argp} v' d) Nat.zero)"
            ),
            bodyp = bodyp,
            argp = argp,
        );
        let eq = format!(
            "(instantiate_nested_commutes_zero_subst {bodyp} {argp} v' d)",
            bodyp = bodyp,
            argp = argp,
        );
        format!(
            concat!(
                "(Eq.substType KExpr ",
                "(fun (x : KExpr) => par_reduces_p env {lhs_head} x) ",
                "{ctor_rhs} {goal_rhs} ",
                "(Eq.symm KExpr {goal_rhs} {ctor_rhs} {eq}) ",
                "{ctor_term})"
            ),
            lhs_head = lhs_head,
            ctor_rhs = ctor_rhs,
            goal_rhs = goal_rhs,
            eq = eq,
            ctor_term = ctor_term,
        )
    };

    // beta arm.
    let beta_lhs_head = concat!(
        "(KExpr.app ",
        "(KExpr.lam (instantiate_at A v d) (instantiate_at body v (Nat.succ d))) ",
        "(instantiate_at arg v d))"
    );
    let beta_ctor = concat!(
        "(par_reduces_p.beta env ",
        "(instantiate_at A v d) (instantiate_at A' v' d) ",
        "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
        "(instantiate_at arg v d) (instantiate_at arg' v' d) ",
        "(ihA v v' d h closed liftclosed) (ihbody v v' (Nat.succ d) h closed liftclosed) ",
        "(iharg v v' d h closed liftclosed))"
    );
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_p env A A') (_hbody : par_reduces_p env body body') ",
            "(_harg : par_reduces_p env arg arg') ",
            "(ihA : {ih_A}) (ihbody : {ih_body}) (iharg : {ih_arg}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
        body = contract(beta_lhs_head, beta_ctor, "body'", "arg'"),
    );

    // let_ (ZETA) arm: source instantiate_at (KExpr.let_ ty val body) v d = KExpr.let_
    // (inst ty)(inst val)(inst body succ) (genuine ctor); ctor target instantiates, bridged
    // to the goal RHS by the shared instantiate_nested_commutes_zero_subst contract (arg := val).
    let let_lhs_head =
        "(KExpr.let_ (instantiate_at ty v d) (instantiate_at val v d) (instantiate_at body v (Nat.succ d)))";
    let let_ctor = concat!(
        "(par_reduces_p.let_ env ",
        "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
        "(instantiate_at val v d) (instantiate_at val' v' d) ",
        "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
        "(ihty v v' d h closed liftclosed) (ihval v v' d h closed liftclosed) ",
        "(ihbody v v' (Nat.succ d) h closed liftclosed))"
    );
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') ",
            "(_hbody : par_reduces_p env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => {body})"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
        body = contract(let_lhs_head, let_ctor, "body'", "val'"),
    );
    // let_cong (trailing CONGRUENCE) arm: both sides are genuine lets; instantiate_at
    // distributes over let_ definitionally, so par_reduces_p.let_cong on the IHs concludes.
    let let_cong_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') ",
            "(_hbody : par_reduces_p env body body') ",
            "(ihty : {ih_ty}) (ihval : {ih_val}) (ihbody : {ih_body}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p.let_cong env ",
            "(instantiate_at ty v d) (instantiate_at ty' v' d) ",
            "(instantiate_at val v d) (instantiate_at val' v' d) ",
            "(instantiate_at body v (Nat.succ d)) (instantiate_at body' v' (Nat.succ d)) ",
            "(ihty v v' d h closed liftclosed) (ihval v v' d h closed liftclosed) ",
            "(ihbody v v' (Nat.succ d) h closed liftclosed))"
        ),
        ih_ty = ih.replace("SUB'", "ty'").replace("SUB", "ty"),
        ih_val = ih.replace("SUB'", "val'").replace("SUB", "val"),
        ih_body = ih.replace("SUB'", "body'").replace("SUB", "body"),
    );

    // iota_p arm: source e0 ⇒_p e2 then iota_step e2 r. The IH delivers the premise
    // par_reduces_p (inst e0 v d)(inst e2 v' d), and iota_subst_commutes lifts the fired
    // iota to iota_step (inst e2 v' d)(inst r v' d); iota_p assembles in ONE par-step.
    let iota_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e2 : KExpr) (r : KExpr) ",
            "(_hp : par_reduces_p env e0 e2) (hi : iota_step env e2 r) ",
            "(ihp : {ih_e0e2}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p.iota_p env (instantiate_at e0 v d) (instantiate_at e2 v' d) (instantiate_at r v' d) ",
            "(ihp v v' d h closed liftclosed) ",
            "(iota_subst_commutes env e2 r v' d closed hi))"
        ),
        ih_e0e2 = ih.replace("SUB'", "e2").replace("SUB", "e0"),
    );

    // proj arm: subst descends into the scrutinee; congruence via par_reduces_p.proj.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_p env sub sub') (ihsub : {ih_sub}) ",
            "(v : KExpr) (v' : KExpr) (d : Nat) (h : par_reduces_p env v v') ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "par_reduces_p.proj env s i ",
            "(instantiate_at sub v d) (instantiate_at sub' v' d) ",
            "(ihsub v v' d h closed liftclosed))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );

    format!(
        concat!(
            "fun (env : RecEnv) (e0 : KExpr) (e0' : KExpr) (v0 : KExpr) (v0' : KExpr) (d0 : Nat) ",
            "(h_ee : par_reduces_p env e0 e0') (h_vv : par_reduces_p env v0 v0') ",
            "(closed0 : RecEnvClosed env) (liftclosed0 : RecEnvLiftClosed env) => ",
            "par_reduces_p.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "e0 e0' h_ee v0 v0' d0 h_vv closed0 liftclosed0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_p.lam"),
        pi_arm = binder_arm("par_reduces_p.pi"),
        forall_arm = binder_arm("par_reduces_p.forall_"),
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}
