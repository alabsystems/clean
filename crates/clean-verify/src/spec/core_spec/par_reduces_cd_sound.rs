// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness of the 3-way (β+ι+δ) computational parallel reduction into `DefEq`
//! (church_rosser_whnf retirement track — the S-HALF that mirrors the I-HALF of
//! `par_reduces_cd_injectivity.rs`).
//!
//! Registers, in dependency order:
//!  - `par_reduces_cd_sound`     : `par_reduces_cd the_red_env e e' -> DefEq e e'`,
//!    by `par_reduces_cd.rec`. The atomic structural arms map to the matching
//!    `DefEq` congruence; the `beta` arm contracts the par-reduced redex via the
//!    UNTYPED `DefEq.beta` (no typing needed — exactly the unblock the untyped beta
//!    landing buys); the `let_` (zeta) arm fires the kernel-faithful `DefEq.zeta`
//!    on the genuine `KExpr.let_` node after a `DefEq.let_cong` on the components,
//!    and the trailing `let_cong` congruence arm maps straight to `DefEq.let_cong`;
//!    `forall_` still reuses the `pi` proof through the reducible `KExpr.forall_`
//!    alias; `iota`/`delta` bridge the
//!    operational step to the abstract reduction witness
//!    (`iota_step_to_reduces` / `delta_step_to_reduces`) then apply `DefEq.iota` /
//!    `DefEq.delta`.
//!  - `par_reduces_cd_star_sound`: the multi-step closure soundness, by
//!    `par_reduces_cd_star.rec` (refl = `DefEq.refl`, step = `DefEq.trans` of the
//!    single-step soundness with the IH).
//!  - `join_to_def_eq`           : `par_strips_witness_cd_star the_red_env a b ->
//!    DefEq a b`, by destructuring the common reduct `c` (`a =>* c`, `b =>* c`) and
//!    `DefEq.trans a c b (sound a c) (DefEq.symm (sound b c))`.
//!
//! All three are `is_axiom: false`, `DerivedProved`, ZERO axiom_deps — every leaf
//! is a `FoundationalRule` (DefEq ctors / the recursors) or a debt-free
//! `DerivedProved` bridge. NO `i1..i8` interface hypotheses are carried here:
//! soundness of a par-step into `DefEq` is unconditional; the faithful interfaces
//! enter only at the diamond (def_eq_joinable), consumed downstream.
//!
//! Registered AFTER `add_def_eq_joinable` (so `par_reduces_cd` / `_star` /
//! `par_strips_witness_cd_star` / the step bridges all exist).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register `par_reduces_cd_sound`, `par_reduces_cd_star_sound`, and
    /// Register the `RedEnvFaithful` bundle (the eight faithful RecEnv/DefEnv
    /// interfaces packaged into one carried hypothesis) and its 8 projectors.
    ///
    /// Carried, NOT discharged: `RedEnvFaithful the_red_env` remains a HYPOTHESIS
    /// threaded through the church_rosser_whnf-retirement chain (the honest
    /// conditional residual, dischargeable to the real kernel env at end-of-track).
    /// Bundling the eight into one param keeps the downstream threading to a single
    /// binder per declaration. `RedEnvFaithful.mk` is an inductive constructor
    /// (FoundationalRule, NOT an admitted/HelperAxiom — like RecEnvWellformed etc.).
    pub(super) fn add_redenv_faithful(&mut self) -> Result<(), SpecError> {
        // The eight faithful interfaces (generic over `env : RedEnv`), in the exact
        // order def_eq_joinable's i1..i8 expect.
        const IFACES: [&str; 8] = [
            "RecEnvReductNotRedex (red_rec env)",
            "RecEnvCtorNoRecMeta (red_rec env)",
            "RecEnvClosed (red_rec env)",
            "RecEnvLiftClosed (red_rec env)",
            "DefEnvClosed (red_def env)",
            "DefEnvLiftClosed (red_def env)",
            "RecEnvDefEnvDisjoint env",
            "RecEnvCtorNoDefVal env",
        ];

        // RedEnvFaithful env: one constructor bundling the eight interfaces.
        let mk_args = IFACES
            .iter()
            .enumerate()
            .map(|(k, t)| format!("(h{} : {t})", k + 1))
            .collect::<Vec<_>>()
            .join(" ");
        self.add_inductive(
            &format!(
                "inductive RedEnvFaithful (env : RedEnv) : Type\n| mk : forall {mk_args}, RedEnvFaithful env"
            ),
            "Bundle of the eight faithful RecEnv/DefEnv interfaces over a combined reduction \
             environment. A single carried hypothesis threaded through the church_rosser_whnf \
             retirement chain so the type-preservation theorems stay conditional on the env's \
             faithfulness, NOT discharged over the_red_env's placeholder value. Part of the \
             church_rosser_whnf retirement track.",
        )?;

        // Eight projectors redenv_faithful_i1..i8 via RedEnvFaithful.rec.
        let binders = IFACES
            .iter()
            .enumerate()
            .map(|(k, t)| format!("(a{} : {t})", k + 1))
            .collect::<Vec<_>>()
            .join(" ");
        for (k, iface) in IFACES.iter().enumerate() {
            let n = k + 1;
            self.add_definition(SpecDefinition {
                name: format!("redenv_faithful_i{n}"),
                type_src: format!("forall (env : RedEnv), RedEnvFaithful env -> {iface}"),
                value_src: Some(format!(
                    "fun (env : RedEnv) (h : RedEnvFaithful env) => \
                     RedEnvFaithful.rec env \
                     (fun (_ : RedEnvFaithful env) => {iface}) \
                     (fun {binders} => a{n}) h"
                )),
                is_axiom: false,
                description: format!(
                    "Projector {n} of RedEnvFaithful: recover the {iface} component. DerivedProved, \
                     zero axiom_deps. Part of the church_rosser_whnf retirement track."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "RedEnvFaithful".to_string(),
                    "RedEnvFaithful.rec".to_string(),
                    "red_rec".to_string(),
                    "red_def".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }

    /// `join_to_def_eq` (the par-reduction-into-DefEq soundness chain).
    pub(super) fn add_par_reduces_cd_sound(&mut self) -> Result<(), SpecError> {
        self.add_redenv_faithful()?;
        // par_reduces_cd_sound: a single 3-way par-step is a DefEq.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_sound".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "par_reduces_cd the_red_env e e' -> DefEq e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e0 : KExpr) (e0' : KExpr) (h0 : par_reduces_cd the_red_env e0 e0') => ",
                    "par_reduces_cd.rec the_red_env ",
                    "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_cd the_red_env x y) => DefEq x y) ",
                    // refl
                    "(fun (e : KExpr) => DefEq.refl e) ",
                    // beta: contract the par-reduced redex via untyped DefEq.beta
                    "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(arg : KExpr) (arg' : KExpr) ",
                    "(_hA : par_reduces_cd the_red_env A A') ",
                    "(_hbody : par_reduces_cd the_red_env body body') ",
                    "(_harg : par_reduces_cd the_red_env arg arg') ",
                    "(ihA : DefEq A A') (ihbody : DefEq body body') (iharg : DefEq arg arg') => ",
                    "DefEq.trans (KExpr.app (KExpr.lam A body) arg) ",
                    "(KExpr.app (KExpr.lam A' body') arg') (instantiate body' arg') ",
                    "(DefEq.app_cong (KExpr.lam A body) (KExpr.lam A' body') arg arg' ",
                    "(DefEq.lam_cong A A' body body' ihA ihbody) iharg) ",
                    "(DefEq.beta A' body' arg')) ",
                    // app
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(_hf : par_reduces_cd the_red_env f f') ",
                    "(_ha : par_reduces_cd the_red_env a a') ",
                    "(ihf : DefEq f f') (iha : DefEq a a') => ",
                    "DefEq.app_cong f f' a a' ihf iha) ",
                    // lam
                    "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_cd the_red_env ty ty') ",
                    "(_hbody : par_reduces_cd the_red_env body body') ",
                    "(ihty : DefEq ty ty') (ihbody : DefEq body body') => ",
                    "DefEq.lam_cong ty ty' body body' ihty ihbody) ",
                    // pi
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_cd the_red_env dom dom') ",
                    "(_hb : par_reduces_cd the_red_env body body') ",
                    "(ihd : DefEq dom dom') (ihb : DefEq body body') => ",
                    "DefEq.pi_cong dom dom' body body' ihd ihb) ",
                    // forall_ (KExpr.forall_ is the reducible pi alias)
                    "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(_hd : par_reduces_cd the_red_env dom dom') ",
                    "(_hb : par_reduces_cd the_red_env body body') ",
                    "(ihd : DefEq dom dom') (ihb : DefEq body body') => ",
                    "DefEq.pi_cong dom dom' body body' ihd ihb) ",
                    // let_ (zeta): the genuine KExpr.let_ node — congruence on the components
                    // (DefEq.let_cong) then fire the kernel-faithful zeta (DefEq.zeta) on the
                    // reduced node; DefEq.trans (let_ ty val body) (let_ ty' val' body')
                    // (instantiate body' val').
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
                    "(body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_cd the_red_env ty ty') ",
                    "(_hval : par_reduces_cd the_red_env val val') ",
                    "(_hbody : par_reduces_cd the_red_env body body') ",
                    "(ihty : DefEq ty ty') (ihval : DefEq val val') (ihbody : DefEq body body') => ",
                    "DefEq.trans (KExpr.let_ ty val body) ",
                    "(KExpr.let_ ty' val' body') (instantiate body' val') ",
                    "(DefEq.let_cong ty ty' val val' body body' ihty ihval ihbody) ",
                    "(DefEq.zeta ty' val' body')) ",
                    // iota: bridge the operational step to iota_reduces, then DefEq.iota
                    "(fun (e : KExpr) (e' : KExpr) (hi : iota_step (red_rec the_red_env) e e') => ",
                    "DefEq.iota e e' (iota_step_to_reduces e e' hi)) ",
                    // delta: bridge the operational step to delta_reduces, then DefEq.delta
                    "(fun (e : KExpr) (e' : KExpr) (hd : delta_step (red_def the_red_env) e e') => ",
                    "DefEq.delta e e' (delta_step_to_reduces e e' hd)) ",
                    // let_cong: positional congruence over the genuine let_ node — DefEq.let_cong on the IHs
                    "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
                    "(body : KExpr) (body' : KExpr) ",
                    "(_hty : par_reduces_cd the_red_env ty ty') ",
                    "(_hval : par_reduces_cd the_red_env val val') ",
                    "(_hbody : par_reduces_cd the_red_env body body') ",
                    "(ihty : DefEq ty ty') (ihval : DefEq val val') (ihbody : DefEq body body') => ",
                    "DefEq.let_cong ty ty' val val' body body' ihty ihval ihbody) ",
                    // proj (proj/lit rung): positional congruence over the scrutinee -> DefEq.proj_cong on the IH.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
                    "(_hsub : par_reduces_cd the_red_env sub sub') (ihsub : DefEq sub sub') => ",
                    "DefEq.proj_cong s i sub sub' ihsub) ",
                    // apply to indices + major
                    "e0 e0' h0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Soundness of the atomic 3-way (β+ι+δ+ζ) parallel reduction into DefEq: ",
                "par_reduces_cd the_red_env e e' -> DefEq e e'. By par_reduces_cd.rec; the beta arm ",
                "contracts via the UNTYPED DefEq.beta (no typing premises), the let_ (zeta) arm via ",
                "DefEq.let_cong then the kernel-faithful DefEq.zeta on the genuine let_ node, the ",
                "structural arms via the matching DefEq congruence (forall_ through the reducible pi ",
                "alias; let_cong straight to DefEq.let_cong), and iota/delta via the step->reduces ",
                "bridges + DefEq.iota/.delta. DerivedProved, zero ",
                "axiom_deps. Part of the church_rosser_whnf retirement track (the S-half)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.rec".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.app_cong".to_string(),
                "DefEq.lam_cong".to_string(),
                "DefEq.pi_cong".to_string(),
                "DefEq.beta".to_string(),
                "DefEq.zeta".to_string(),
                "DefEq.let_cong".to_string(),
                "DefEq.iota".to_string(),
                "DefEq.delta".to_string(),
                "iota_step_to_reduces".to_string(),
                "delta_step_to_reduces".to_string(),
                "iota_step".to_string(),
                "delta_step".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "instantiate".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_star_sound: the multi-step closure is a DefEq.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_sound".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), ",
                "par_reduces_cd_star the_red_env e e' -> DefEq e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e0 : KExpr) (e0' : KExpr) (h0 : par_reduces_cd_star the_red_env e0 e0') => ",
                    "par_reduces_cd_star.rec the_red_env ",
                    "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_cd_star the_red_env x y) => DefEq x y) ",
                    // refl
                    "(fun (e : KExpr) => DefEq.refl e) ",
                    // step: par_reduces_cd e e', tail e' e'', ih : DefEq e' e''
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces_cd the_red_env e e') ",
                    "(_htail : par_reduces_cd_star the_red_env e' e'') ",
                    "(ih : DefEq e' e'') => ",
                    "DefEq.trans e e' e'' (par_reduces_cd_sound e e' hstep) ih) ",
                    "e0 e0' h0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Soundness of the reflexive-transitive closure of par_reduces_cd into DefEq: ",
                "par_reduces_cd_star the_red_env e e' -> DefEq e e'. By par_reduces_cd_star.rec — refl = ",
                "DefEq.refl, step = DefEq.trans of par_reduces_cd_sound with the IH. DerivedProved, zero ",
                "axiom_deps. Part of the church_rosser_whnf retirement track (the S-half)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.rec".to_string(),
                "par_reduces_cd_sound".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.trans".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // join_to_def_eq: a 3-way join witness yields a DefEq between its sources.
        self.add_definition(SpecDefinition {
            name: "join_to_def_eq".to_string(),
            type_src: concat!(
                "forall (a : KExpr) (b : KExpr), ",
                "par_strips_witness_cd_star the_red_env a b -> DefEq a b"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : KExpr) (b : KExpr) (w : par_strips_witness_cd_star the_red_env a b) => ",
                    "@par_strips_witness_cd_star.rec the_red_env a b ",
                    "(fun (_w : par_strips_witness_cd_star the_red_env a b) => DefEq a b) ",
                    "(fun (c : KExpr) (l1 : par_reduces_cd_star the_red_env a c) ",
                    "(l2 : par_reduces_cd_star the_red_env b c) => ",
                    "DefEq.trans a c b (par_reduces_cd_star_sound a c l1) ",
                    "(DefEq.symm b c (par_reduces_cd_star_sound b c l2))) ",
                    "w"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "A 3-way (β+ι+δ) join witness yields a DefEq between its sources: ",
                "par_strips_witness_cd_star the_red_env a b -> DefEq a b. Destructure the common reduct c ",
                "(a =>* c, b =>* c) via par_strips_witness_cd_star.rec, then DefEq.trans a c b (sound a c) ",
                "(DefEq.symm (sound b c)). The S-half companion of def_eq_joinable: together they witness ",
                "DefEq <-> joinability, letting binder injectivity descend through confluence instead of ",
                "church_rosser_whnf. DerivedProved, zero axiom_deps. Part of the church_rosser_whnf ",
                "retirement track."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_strips_witness_cd_star".to_string(),
                "par_strips_witness_cd_star.rec".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star_sound".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.symm".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
