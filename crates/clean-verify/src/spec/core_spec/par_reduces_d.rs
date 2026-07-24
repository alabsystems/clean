// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H++ (#2859 computational-iota/delta track, DELTA INCREMENT Stage 4,
//! the HINDLEY-ROSEN redirect): the δ-ONLY single-position reduction `delta_cong`
//! and its reflexive-transitive closure `delta_cong_star` — the `→₂` of the
//! Hindley-Rosen route to β+ι+δ Church-Rosser.
//!
//! ## Why a separate δ-only relation (the Stage-3 wall and its sidestep)
//!
//! Stage 3 (`par_reduces_pd`) tried to build the COMBINED 3-way Takahashi diamond.
//! That needs a `topDeltaStar` normalising cascade for definition chains
//! (`def c := d := f`), which in turn needs well-founded recursion on definition
//! depth — ABSENT from the structural-recursor spec fragment (unlike `topIotaStar`,
//! which collapses to a single head-iota fire under `RecEnvCtorNoRecMeta`; there is
//! no true `DefEnvNoChain` interface, because real kernel definitions chain).
//!
//! The Hindley-Rosen redirect keeps β+ι (`par_reduces_c`, CR LANDED as
//! `par_reduces_c_star_diamond`) and δ as SEPARATE relations: union confluence
//! follows from each relation's own confluence plus their commutation — NO combined
//! diamond, NO `dev`, NO `topDeltaStar`, NO WF-recursion.
//!
//! `delta_cong` is the SINGLE-POSITION full-δ reduction (the congruence closure of
//! the deterministic head step `delta_step (red_def env)`): each step fires δ at
//! exactly one const-leaf position. It is ORTHOGONAL — two δ-redexes are distinct
//! const leaves, hence either the same leaf (⟹ `delta_step_deterministic`) or
//! disjoint (⟹ fire the other on each side). So its single-step diamond is direct
//! (no developer); a def-chain `c → d → f` is simply three `delta_cong` steps, joined
//! by the strip/tile of the RT-closure — never normalised inside one step. This is
//! deliberately NOT the parallel δ-development `par_reduces_d` (refl + congruences +
//! `delta_p`), whose Takahashi `dev` would be exactly the `topDeltaStar` wall.
//!
//! Layer 1 (this commit): the relation + its RT-closure + the join witness + the two
//! basic combinators (`delta_cong_subsumes_star` / `delta_cong_star_trans`).
//! Mechanical mirrors of the `par_reduces_pd_star` substrate (par_reduces_pd.rs).
//!
//! Runs AFTER `add_par_reduces_pd` (so `RedEnv` / `red_rec` / `red_def` /
//! `delta_step` / the `par_strips_witness` pattern are all in scope). Part of #2859
//! (Increment H++, delta increment Stage 4 — Hindley-Rosen route).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_par_reduces_d(&mut self) -> Result<(), SpecError> {
        self.add_delta_cong_relation()?;
        self.add_delta_cong_star_combinators()?;
        self.add_delta_cong_cd_embeddings()?;
        self.add_delta_cong_star_congruences()?;
        Ok(())
    }

    /// Brick 4: the δ-star structural congruences `delta_cong_star_{app,lam,pi,let}` —
    /// component-wise multi-step δ lifts through KExpr's compound ctors (app/lam/pi
    /// two-slot; the genuine let_ three-slot). Each is two (three for let) one-sided
    /// star inductions composed by `delta_cong_star_trans`; a single δ-step lifts via
    /// the matching single-position congruence ctor (`delta_cong.app_f`/`.app_a`,
    /// `.lam_t`/`.lam_b`, `.pi_d`/`.pi_b`, `.let_t`/`.let_v`/`.let_b`) directly — no
    /// reflexive companion (unlike the parallel `par_reduces_cd_star_*`, because
    /// `delta_cong` is single-position). Required infrastructure for the strip
    /// lemma, the orthogonal single-step diamond, and the β+ι commutation.
    fn add_delta_cong_star_congruences(&mut self) -> Result<(), SpecError> {
        // delta_cong_star_app: f =>* f' and a =>* a' give app f a =>* app f' a'.
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_app".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), ",
                "delta_cong_star env f f' -> delta_cong_star env a a' -> ",
                "delta_cong_star env (KExpr.app f a) (KExpr.app f' a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(hf : delta_cong_star env f f') (ha : delta_cong_star env a a') => ",
                    "delta_cong_star_trans env (KExpr.app f a) (KExpr.app f' a) (KExpr.app f' a') ",
                    "(delta_cong_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : delta_cong_star env x y) => ",
                    "delta_cong_star env (KExpr.app x a) (KExpr.app y a)) ",
                    "(fun (x : KExpr) => delta_cong_star.refl env (KExpr.app x a)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : delta_cong env x x') (_htail : delta_cong_star env x' x'') ",
                    "(ih : delta_cong_star env (KExpr.app x' a) (KExpr.app x'' a)) => ",
                    "delta_cong_star.step env (KExpr.app x a) (KExpr.app x' a) (KExpr.app x'' a) ",
                    "(delta_cong.app_f env x x' a hstep) ih) ",
                    "f f' hf) ",
                    "(delta_cong_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : delta_cong_star env x y) => ",
                    "delta_cong_star env (KExpr.app f' x) (KExpr.app f' y)) ",
                    "(fun (x : KExpr) => delta_cong_star.refl env (KExpr.app f' x)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : delta_cong env x x') (_htail : delta_cong_star env x' x'') ",
                    "(ih : delta_cong_star env (KExpr.app f' x') (KExpr.app f' x'')) => ",
                    "delta_cong_star.step env (KExpr.app f' x) (KExpr.app f' x') (KExpr.app f' x'') ",
                    "(delta_cong.app_a env f' x x' hstep) ih) ",
                    "a a' ha)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "app congruence at the delta_cong_star level: two one-sided star inductions composed by delta_cong_star_trans through app f' a; each single δ-step lifts via delta_cong.app_f / .app_a directly (no reflexive companion — delta_cong is single-position). DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.app_f".to_string(),
                "delta_cong.app_a".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star.step".to_string(),
                "delta_cong_star.rec".to_string(),
                "delta_cong_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_star_proj: proj congruence at the delta_cong_star level (single
        // position — one star induction lifting delta_cong.proj_s on each step).
        // Part of the proj/lit fragment rung.
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_proj".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (s : Name) (i : Nat) (sub1 : KExpr) (sub2 : KExpr), ",
                "delta_cong_star env sub1 sub2 -> ",
                "delta_cong_star env (KExpr.proj s i sub1) (KExpr.proj s i sub2)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (s : Name) (i : Nat) (sub1 : KExpr) (sub2 : KExpr) ",
                    "(hsub : delta_cong_star env sub1 sub2) => ",
                    "delta_cong_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : delta_cong_star env x y) => ",
                    "delta_cong_star env (KExpr.proj s i x) (KExpr.proj s i y)) ",
                    "(fun (x : KExpr) => delta_cong_star.refl env (KExpr.proj s i x)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : delta_cong env x x') (_htail : delta_cong_star env x' x'') ",
                    "(ih : delta_cong_star env (KExpr.proj s i x') (KExpr.proj s i x'')) => ",
                    "delta_cong_star.step env (KExpr.proj s i x) (KExpr.proj s i x') (KExpr.proj s i x'') ",
                    "(delta_cong.proj_s env s i x x' hstep) ih) ",
                    "sub1 sub2 hsub"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "proj congruence at the delta_cong_star level: sub1 =>* sub2 gives proj s i sub1 =>* proj s i sub2. One star induction lifting delta_cong.proj_s on each step. DerivedProved, zero axiom_deps. Part of the proj/lit fragment rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.proj_s".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star.step".to_string(),
                "delta_cong_star.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_star_lam / _pi: binder congruences (same shape via the matching
        // two single-position ctors). lam uses lam_t/lam_b, pi uses pi_d/pi_b.
        for (name, head, ctor_t, ctor_b, label) in [
            (
                "delta_cong_star_lam",
                "KExpr.lam",
                "delta_cong.lam_t",
                "delta_cong.lam_b",
                "lam",
            ),
            (
                "delta_cong_star_pi",
                "KExpr.pi",
                "delta_cong.pi_d",
                "delta_cong.pi_b",
                "pi",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (env : RedEnv) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), ",
                        "delta_cong_star env ty ty' -> delta_cong_star env body body' -> ",
                        "delta_cong_star env ({head} ty body) ({head} ty' body')"
                    ),
                    head = head,
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (env : RedEnv) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                        "(hty : delta_cong_star env ty ty') (hbody : delta_cong_star env body body') => ",
                        "delta_cong_star_trans env ({head} ty body) ({head} ty' body) ({head} ty' body') ",
                        "(delta_cong_star.rec env ",
                        "(fun (x : KExpr) (y : KExpr) (_ : delta_cong_star env x y) => ",
                        "delta_cong_star env ({head} x body) ({head} y body)) ",
                        "(fun (x : KExpr) => delta_cong_star.refl env ({head} x body)) ",
                        "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                        "(hstep : delta_cong env x x') (_htail : delta_cong_star env x' x'') ",
                        "(ih : delta_cong_star env ({head} x' body) ({head} x'' body)) => ",
                        "delta_cong_star.step env ({head} x body) ({head} x' body) ({head} x'' body) ",
                        "({ctor_t} env x x' body hstep) ih) ",
                        "ty ty' hty) ",
                        "(delta_cong_star.rec env ",
                        "(fun (x : KExpr) (y : KExpr) (_ : delta_cong_star env x y) => ",
                        "delta_cong_star env ({head} ty' x) ({head} ty' y)) ",
                        "(fun (x : KExpr) => delta_cong_star.refl env ({head} ty' x)) ",
                        "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                        "(hstep : delta_cong env x x') (_htail : delta_cong_star env x' x'') ",
                        "(ih : delta_cong_star env ({head} ty' x') ({head} ty' x'')) => ",
                        "delta_cong_star.step env ({head} ty' x) ({head} ty' x') ({head} ty' x'') ",
                        "({ctor_b} env ty' x x' hstep) ih) ",
                        "body body' hbody)"
                    ),
                    head = head,
                    ctor_t = ctor_t,
                    ctor_b = ctor_b,
                )),
                is_axiom: false,
                description: format!(
                    "{label} congruence at the delta_cong_star level: two one-sided star inductions composed by delta_cong_star_trans; each single δ-step lifts via {ctor_t} / {ctor_b} directly. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "delta_cong".to_string(),
                    ctor_t.to_string(),
                    ctor_b.to_string(),
                    "delta_cong_star".to_string(),
                    "delta_cong_star.refl".to_string(),
                    "delta_cong_star.step".to_string(),
                    "delta_cong_star.rec".to_string(),
                    "delta_cong_star_trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // delta_cong_star_let: the three-slot congruence over the GENUINE let_ ctor —
        // ty =>* ty', val =>* val', body =>* body' give let_ ty val body =>* let_ ty'
        // val' body'. Three one-sided star inductions (ty via let_t, then val via
        // let_v, then body via let_b) composed by delta_cong_star_trans. Consumed by
        // the par_strong_join_d let congruence lifts (par_reduces_d_conf.rs).
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_let".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), ",
                "delta_cong_star env ty ty' -> delta_cong_star env val val' -> delta_cong_star env body body' -> ",
                "delta_cong_star env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(hty : delta_cong_star env ty ty') (hval : delta_cong_star env val val') (hbody : delta_cong_star env body body') => ",
                    "delta_cong_star_trans env (KExpr.let_ ty val body) (KExpr.let_ ty' val body) (KExpr.let_ ty' val' body') ",
                    // phase 1: reduce ty via let_t.
                    "(delta_cong_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : delta_cong_star env x y) => ",
                    "delta_cong_star env (KExpr.let_ x val body) (KExpr.let_ y val body)) ",
                    "(fun (x : KExpr) => delta_cong_star.refl env (KExpr.let_ x val body)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : delta_cong env x x') (_htail : delta_cong_star env x' x'') ",
                    "(ih : delta_cong_star env (KExpr.let_ x' val body) (KExpr.let_ x'' val body)) => ",
                    "delta_cong_star.step env (KExpr.let_ x val body) (KExpr.let_ x' val body) (KExpr.let_ x'' val body) ",
                    "(delta_cong.let_t env x x' val body hstep) ih) ",
                    "ty ty' hty) ",
                    "(delta_cong_star_trans env (KExpr.let_ ty' val body) (KExpr.let_ ty' val' body) (KExpr.let_ ty' val' body') ",
                    // phase 2: reduce val via let_v.
                    "(delta_cong_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : delta_cong_star env x y) => ",
                    "delta_cong_star env (KExpr.let_ ty' x body) (KExpr.let_ ty' y body)) ",
                    "(fun (x : KExpr) => delta_cong_star.refl env (KExpr.let_ ty' x body)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : delta_cong env x x') (_htail : delta_cong_star env x' x'') ",
                    "(ih : delta_cong_star env (KExpr.let_ ty' x' body) (KExpr.let_ ty' x'' body)) => ",
                    "delta_cong_star.step env (KExpr.let_ ty' x body) (KExpr.let_ ty' x' body) (KExpr.let_ ty' x'' body) ",
                    "(delta_cong.let_v env ty' x x' body hstep) ih) ",
                    "val val' hval) ",
                    // phase 3: reduce body via let_b.
                    "(delta_cong_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : delta_cong_star env x y) => ",
                    "delta_cong_star env (KExpr.let_ ty' val' x) (KExpr.let_ ty' val' y)) ",
                    "(fun (x : KExpr) => delta_cong_star.refl env (KExpr.let_ ty' val' x)) ",
                    "(fun (x : KExpr) (x' : KExpr) (x'' : KExpr) ",
                    "(hstep : delta_cong env x x') (_htail : delta_cong_star env x' x'') ",
                    "(ih : delta_cong_star env (KExpr.let_ ty' val' x') (KExpr.let_ ty' val' x'')) => ",
                    "delta_cong_star.step env (KExpr.let_ ty' val' x) (KExpr.let_ ty' val' x') (KExpr.let_ ty' val' x'') ",
                    "(delta_cong.let_b env ty' val' x x' hstep) ih) ",
                    "body body' hbody))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "let_ congruence at the delta_cong_star level (genuine three-slot ctor): three one-sided star inductions (ty via delta_cong.let_t, val via .let_v, body via .let_b) composed by delta_cong_star_trans; each single δ-step lifts via the matching let congruence ctor directly. The let analogue of delta_cong_star_app; consumed by the par_strong_join_d let lifts. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.let_t".to_string(),
                "delta_cong.let_v".to_string(),
                "delta_cong.let_b".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star.step".to_string(),
                "delta_cong_star.rec".to_string(),
                "delta_cong_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 3: the embeddings `delta_cong ⊆ par_reduces_cd` and (lifted over the
    /// RT-closure) `delta_cong_star ⊆ par_reduces_cd_star`. Every single-position δ
    /// step is an atomic 3-way par-step: `delta_cong.rec` maps `here` to
    /// `par_reduces_cd.delta` and each congruence ctor to the matching
    /// `par_reduces_cd` congruence with a reflexive companion. The bridge that lets
    /// the eventual Hindley-Rosen union confluence land as `par_reduces_cd_star`
    /// confluence (the named 3-way CR target). Mirror of `par_reduces_c_subsumes_cd`.
    fn add_delta_cong_cd_embeddings(&mut self) -> Result<(), SpecError> {
        // delta_cong_subsumes_cd: single-position δ step ⊆ par_reduces_cd.
        self.add_definition(SpecDefinition {
            name: "delta_cong_subsumes_cd".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "delta_cong env e e' -> par_reduces_cd env e e'"
            )
            .to_string(),
            value_src: Some(delta_cong_subsumes_cd_proof()),
            is_axiom: false,
            description: concat!(
                "Embedding delta_cong ⊆ par_reduces_cd: every single-position δ step is an atomic 3-way ",
                "par-step. delta_cong.rec maps `here` to par_reduces_cd.delta and each of the nine congruence ",
                "ctors (app_f/app_a, lam_t/lam_b, pi_d/pi_b to the matching par_reduces_cd congruence; the ",
                "trailing let_t/let_v/let_b to par_reduces_cd.let_cong) with a ",
                "reflexive companion on the untouched subterms. The bridge ",
                "into the landed atomic 3-way machinery. Mirror of par_reduces_c_subsumes_cd. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.rec".to_string(),
                "par_reduces_cd".to_string(),
                "par_reduces_cd.refl".to_string(),
                "par_reduces_cd.app".to_string(),
                "par_reduces_cd.lam".to_string(),
                "par_reduces_cd.pi".to_string(),
                "par_reduces_cd.let_cong".to_string(),
                "par_reduces_cd.delta".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_star_subsumes_cd_star: lift delta_cong ⊆ par_reduces_cd over the
        // RT-closure. delta_cong_star.rec — refl is par_reduces_cd_star.refl, step
        // prefixes the embedded single step via par_reduces_cd_star.step. Mirror of
        // par_reduces_cd_star_subsumes_par_pd_star.
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_subsumes_cd_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "delta_cong_star env e e' -> par_reduces_cd_star env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e' : KExpr) ",
                    "(h : delta_cong_star env e e') => ",
                    "delta_cong_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : delta_cong_star env a b) => ",
                    "par_reduces_cd_star env a b) ",
                    "(fun (s : KExpr) => par_reduces_cd_star.refl env s) ",
                    "(fun (s : KExpr) (s' : KExpr) (s'' : KExpr) ",
                    "(hstep : delta_cong env s s') (_htail : delta_cong_star env s' s'') ",
                    "(ih : par_reduces_cd_star env s' s'') => ",
                    "par_reduces_cd_star.step env s s' s'' ",
                    "(delta_cong_subsumes_cd env s s' hstep) ih) ",
                    "e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level embedding delta_cong_star ⊆ par_reduces_cd_star: lift delta_cong_subsumes_cd over ",
                "the RT-closure. delta_cong_star.rec — refl is par_reduces_cd_star.refl, step prefixes the ",
                "embedded single step via par_reduces_cd_star.step. Carries full multi-step δ into the atomic ",
                "3-way closure. Mirror of par_reduces_cd_star_subsumes_par_pd_star. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.rec".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star.step".to_string(),
                "delta_cong_subsumes_cd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 1: the single-position full-δ reduction `delta_cong (env : RedEnv)` —
    /// the congruence closure of the deterministic head step `delta_step (red_def
    /// env)` — together with its RT-closure `delta_cong_star` and the multi-step
    /// join witness `par_strips_witness_d_star`.
    fn add_delta_cong_relation(&mut self) -> Result<(), SpecError> {
        // delta_cong env: δ fires at exactly ONE position. `here` fires the head δ
        // at the whole term; the nine congruence ctors descend into the subterms of
        // the compound ctors app/lam/pi/let_. KExpr.forall_ ≡ KExpr.pi is still a
        // REDUCIBLE surface alias, so δ inside a forall_ is reached by the pi
        // congruences. KExpr.let_ is a GENUINE 7th KExpr ctor (no longer app(lam)),
        // so it carries its own three TRAILING congruences let_t/let_v/let_b
        // (appended last, preserving the original minor positions) — without them
        // par_reduces_cd.let_cong steps firing δ inside a let component would have
        // no delta_cong image (par_reduces_cd_subsumes-style embeddings would be
        // false as stated) and the Hindley-Rosen δ leg would be δ-incomplete; the
        // ConfZeta guide's Step relation likewise carries the three let congruences
        // over δ. A let_ node itself is never a δ-redex (its own spine head,
        // kexpr_const_name none), so `here` on a let is vacuous — lets add congruence
        // positions but NO new redex overlaps. const/sort/bvar carry no KExpr
        // subterms ⟹ no congruence ctor. NO refl ctor (a single δ-step always fires
        // one δ); refl lives in the closure.
        self.add_inductive(
            r"inductive delta_cong (env : RedEnv) : KExpr → KExpr → Type
| here : forall (e : KExpr) (e' : KExpr), delta_step (red_def env) e e' → delta_cong env e e'
| app_f : forall (f : KExpr) (f' : KExpr) (a : KExpr), delta_cong env f f' → delta_cong env (KExpr.app f a) (KExpr.app f' a)
| app_a : forall (f : KExpr) (a : KExpr) (a' : KExpr), delta_cong env a a' → delta_cong env (KExpr.app f a) (KExpr.app f a')
| lam_t : forall (t : KExpr) (t' : KExpr) (b : KExpr), delta_cong env t t' → delta_cong env (KExpr.lam t b) (KExpr.lam t' b)
| lam_b : forall (t : KExpr) (b : KExpr) (b' : KExpr), delta_cong env b b' → delta_cong env (KExpr.lam t b) (KExpr.lam t b')
| pi_d : forall (d : KExpr) (d' : KExpr) (b : KExpr), delta_cong env d d' → delta_cong env (KExpr.pi d b) (KExpr.pi d' b)
| pi_b : forall (d : KExpr) (b : KExpr) (b' : KExpr), delta_cong env b b' → delta_cong env (KExpr.pi d b) (KExpr.pi d b')
| let_t : forall (t : KExpr) (t' : KExpr) (v : KExpr) (b : KExpr), delta_cong env t t' → delta_cong env (KExpr.let_ t v b) (KExpr.let_ t' v b)
| let_v : forall (t : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr), delta_cong env v v' → delta_cong env (KExpr.let_ t v b) (KExpr.let_ t v' b)
| let_b : forall (t : KExpr) (v : KExpr) (b : KExpr) (b' : KExpr), delta_cong env b b' → delta_cong env (KExpr.let_ t v b) (KExpr.let_ t v b')
| proj_s : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), delta_cong env sub sub' → delta_cong env (KExpr.proj s i sub) (KExpr.proj s i sub')",
            "delta_cong env e e' — the SINGLE-POSITION full-δ reduction: the congruence closure of the \
             deterministic head step delta_step (red_def env). The `here` ctor fires the head δ at the whole \
             term; the nine congruence ctors (app_f/app_a, lam_t/lam_b, pi_d/pi_b, and the trailing \
             let_t/let_v/let_b over the genuine KExpr.let_ ctor) descend into the subterms of the compound \
             ctors so any const-leaf δ-redex is reachable (forall_ is a reducible pi alias, so δ inside a \
             forall_ is reached by the pi congruences; δ inside a let component is reached by the let \
             congruences — required for the par_reduces_cd embeddings, whose let_cong arm fires δ inside let \
             components). A let_ node itself is never a δ-redex (its own spine head, kexpr_const_name none), \
             so lets add congruence positions but NO new redex overlaps: δ stays ORTHOGONAL (δ-redexes are \
             distinct const leaves, never root-overlapping) and its single-step diamond stays direct — no \
             developer, no topDeltaStar, no WF-recursion. The `→₂` of the Hindley-Rosen route. Part of #2859 \
             (Increment H++, delta increment Stage 4).",
        )?;

        // delta_cong_star env: the reflexive-transitive closure of delta_cong — full
        // multi-step δ. Mirror of par_reduces_pd_star.
        self.add_inductive(
            r"inductive delta_cong_star (env : RedEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), delta_cong_star env e e
| step : forall (e : KExpr) (e' : KExpr) (e'' : KExpr), delta_cong env e e' → delta_cong_star env e' e'' → delta_cong_star env e e''",
            "delta_cong_star env e e'' — the reflexive-transitive closure of the single-position full-δ \
             reduction delta_cong. Full multi-step δ-reduction; the `→₂*` of the Hindley-Rosen route, whose \
             confluence (the δ Church-Rosser) the strip/tile of the orthogonal single-step diamond yields. \
             Mirror of par_reduces_pd_star. Part of #2859 (Increment H++, delta increment Stage 4).",
        )?;

        // par_strips_witness_d_star env: the multi-step δ join witness (mirror of
        // par_strips_witness_pd_star) — the endpoint of the δ confluence theorem.
        self.add_inductive(
            r"inductive par_strips_witness_d_star (env : RedEnv) : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), delta_cong_star env e1 e3 → delta_cong_star env e2 e3 → par_strips_witness_d_star env e1 e2",
            "par_strips_witness_d_star env e1 e2 packages a common reduct e3 with delta_cong_star env e1 e3 \
             and delta_cong_star env e2 e3 — the multi-step join witness the δ confluence theorem \
             (delta_cong_star_diamond) lands at. Mirror of par_strips_witness_pd_star. Part of #2859 \
             (Increment H++, delta increment Stage 4).",
        )?;

        Ok(())
    }

    /// Brick 2: the two basic RT-closure combinators — `delta_cong_subsumes_star`
    /// (single step embeds into the closure) and `delta_cong_star_trans`
    /// (transitivity). Verbatim mirrors of `par_subsumes_par_pd_star` /
    /// `par_reduces_pd_star_trans` (par_reduces_pd.rs).
    fn add_delta_cong_star_combinators(&mut self) -> Result<(), SpecError> {
        // delta_cong_subsumes_star: single delta_cong step embeds into delta_cong_star
        // (step with a refl tail).
        self.add_definition(SpecDefinition {
            name: "delta_cong_subsumes_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "delta_cong env e e' -> delta_cong_star env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e' : KExpr) (h : delta_cong env e e') => ",
                    "delta_cong_star.step env e e' e' h (delta_cong_star.refl env e')"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Single-step delta_cong embeds into delta_cong_star (step with a refl tail). DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_star_trans: transitivity of delta_cong_star (delta_cong_star.rec
        // on the first chain, prefixing each step onto the extended tail). Mirror of
        // par_reduces_pd_star_trans.
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_trans".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), ",
                "delta_cong_star env e1 e2 -> delta_cong_star env e2 e3 -> ",
                "delta_cong_star env e1 e3"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) ",
                    "(h1 : delta_cong_star env e1 e2) (h2 : delta_cong_star env e2 e3) => ",
                    "delta_cong_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : delta_cong_star env a b) => ",
                    "delta_cong_star env b e3 -> delta_cong_star env a e3) ",
                    "(fun (e : KExpr) (k : delta_cong_star env e e3) => k) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : delta_cong env e e') ",
                    "(_htail : delta_cong_star env e' e'') ",
                    "(ih : delta_cong_star env e'' e3 -> delta_cong_star env e' e3) ",
                    "(k : delta_cong_star env e'' e3) => ",
                    "delta_cong_star.step env e e' e3 hstep (ih k)) ",
                    "e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Transitivity of delta_cong_star (delta_cong_star.rec on the first chain, prefixing each step onto the extended tail). Mirror of par_reduces_pd_star_trans. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.rec".to_string(),
                "delta_cong_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `delta_cong_subsumes_cd` — `delta_cong.rec` maps `here` to
/// `par_reduces_cd.delta` and each of the nine congruence ctors to the matching
/// `par_reduces_cd` congruence (app/lam/pi; the trailing let_t/let_v/let_b to
/// `par_reduces_cd.let_cong`) with `par_reduces_cd.refl` on the untouched subterms.
/// Mirror of `par_reduces_c_subsumes_cd`'s shape.
fn delta_cong_subsumes_cd_proof() -> String {
    concat!(
        "fun (env : RedEnv) (e0 : KExpr) (e0' : KExpr) (h0 : delta_cong env e0 e0') => ",
        "delta_cong.rec env ",
        "(fun (x : KExpr) (y : KExpr) (_h : delta_cong env x y) => par_reduces_cd env x y) ",
        // here: head δ on the whole term -> par_reduces_cd.delta
        "(fun (e : KExpr) (e' : KExpr) (hd : delta_step (red_def env) e e') => ",
        "par_reduces_cd.delta env e e' hd) ",
        // app_f: reduce f, refl on a
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
        "(_h : delta_cong env f f') (ih : par_reduces_cd env f f') => ",
        "par_reduces_cd.app env f f' a a ih (par_reduces_cd.refl env a)) ",
        // app_a: refl on f, reduce a
        "(fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_h : delta_cong env a a') (ih : par_reduces_cd env a a') => ",
        "par_reduces_cd.app env f f a a' (par_reduces_cd.refl env f) ih) ",
        // lam_t: reduce type, refl on body
        "(fun (t : KExpr) (t' : KExpr) (b : KExpr) ",
        "(_h : delta_cong env t t') (ih : par_reduces_cd env t t') => ",
        "par_reduces_cd.lam env t t' b b ih (par_reduces_cd.refl env b)) ",
        // lam_b: refl on type, reduce body
        "(fun (t : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_h : delta_cong env b b') (ih : par_reduces_cd env b b') => ",
        "par_reduces_cd.lam env t t b b' (par_reduces_cd.refl env t) ih) ",
        // pi_d: reduce domain, refl on body
        "(fun (d : KExpr) (d' : KExpr) (b : KExpr) ",
        "(_h : delta_cong env d d') (ih : par_reduces_cd env d d') => ",
        "par_reduces_cd.pi env d d' b b ih (par_reduces_cd.refl env b)) ",
        // pi_b: refl on domain, reduce body
        "(fun (d : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_h : delta_cong env b b') (ih : par_reduces_cd env b b') => ",
        "par_reduces_cd.pi env d d b b' (par_reduces_cd.refl env d) ih) ",
        // let_t: reduce annotation, refl on val/body (genuine-ctor let_cong congruence)
        "(fun (t : KExpr) (t' : KExpr) (v : KExpr) (b : KExpr) ",
        "(_h : delta_cong env t t') (ih : par_reduces_cd env t t') => ",
        "par_reduces_cd.let_cong env t t' v v b b ih (par_reduces_cd.refl env v) (par_reduces_cd.refl env b)) ",
        // let_v: refl on annotation/body, reduce val
        "(fun (t : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) ",
        "(_h : delta_cong env v v') (ih : par_reduces_cd env v v') => ",
        "par_reduces_cd.let_cong env t t v v' b b (par_reduces_cd.refl env t) ih (par_reduces_cd.refl env b)) ",
        // let_b: refl on annotation/val, reduce body
        "(fun (t : KExpr) (v : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_h : delta_cong env b b') (ih : par_reduces_cd env b b') => ",
        "par_reduces_cd.let_cong env t t v v b b' (par_reduces_cd.refl env t) (par_reduces_cd.refl env v) ih) ",
        // proj_s: reduce the scrutinee -> par_reduces_cd.proj congruence on the IH.
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_h : delta_cong env sub sub') (ih : par_reduces_cd env sub sub') => ",
        "par_reduces_cd.proj env s i sub sub' ih) ",
        "e0 e0' h0"
    )
    .to_string()
}
