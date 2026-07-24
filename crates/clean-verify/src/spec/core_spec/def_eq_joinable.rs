// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `def_eq_joinable` — turn a `DefEq` into a 3-way (β+ι+δ+ζ) confluence JOIN
//! witness (`par_strips_witness_cd_star the_red_env`), by `DefEq.rec`.
//!
//! Brick 6 of the church_rosser_whnf retirement track. The diamond
//! `par_reduces_cd_star_diamond` (the unconditional 3-way Church-Rosser of
//! `par_reduces_cd_star`, carrying the faithful `RecEnv`/`DefEnv` interfaces
//! `i1..i8` as bound hypotheses) plus the reverse step bridges
//! (`delta_reduces_to_step` / `iota_reduces_to_step`) and the `_star`
//! congruences (`par_reduces_cd_star_{trans,app,lam,pi,beta,let,let_cong}`,
//! `par_subsumes_par_cd_star`) are exactly the parts a structural `DefEq.rec`
//! needs to map each `DefEq` constructor to a common-reduct join:
//!
//! - `refl a`            → both legs `refl` at `a`;
//! - `symm`              → swap the two legs (`join_symm`);
//! - `trans`             → diamond-join the two inner reducts, then `trans` the
//!                         outer legs through (`join_compose`, the only consumer
//!                         of `i1..i8`);
//! - `beta`              → the redex `=>*` its contractum via the `_star` β
//!                         contraction; meeting point = the contractum;
//! - `app/lam/pi_cong`   → push both sides to the common head-applied reduct via
//!                         the matching `_star` congruence;
//! - `delta` / `iota`    → the single reverse-bridged `par_reduces_cd` step,
//!                         embedded into `par_reduces_cd_star`; meeting point =
//!                         the reduct;
//! - `zeta`              → the let_ redex `=>*` its contractum via the `_star` ζ
//!                         contraction (`par_reduces_cd_star_let` with refl
//!                         components — exactly the beta shape); meeting point =
//!                         the contractum `instantiate b v`;
//! - `let_cong`          → push both sides to the common `let_` reduct via the
//!                         3-component `par_reduces_cd_star_let_cong` (the
//!                         ternary sibling of the app_cong mechanism).
//!
//! `the_red_env` is the literal environment everywhere; `i1..i8` are CARRIED
//! parameters (never discharged from `the_red_env`'s value, never axiomatized).
//! All three definitions are `is_axiom: false`, `DerivedProved`, with complete
//! kernel-checked `value_src`. Their transitive non-foundational closure is
//! empty (every leaf is a `FoundationalRule` or a debt-free `DerivedProved`
//! lemma), so the DerivedProved label is honest.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The eight carried faithful-interface hypotheses, as a binder prefix shared by
/// `join_compose` and `def_eq_joinable` (verbatim from
/// `par_reduces_cd_star_diamond`, specialized to `the_red_env`).
const I_BINDERS: &str = concat!(
    "(i1 : RecEnvReductNotRedex (red_rec the_red_env)) (i2 : RecEnvCtorNoRecMeta (red_rec the_red_env)) ",
    "(i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) ",
    "(i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) ",
    "(i7 : RecEnvDefEnvDisjoint the_red_env) (i8 : RecEnvCtorNoDefVal the_red_env) "
);

impl Specification {
    /// Register `join_symm`, `join_compose`, and `def_eq_joinable`.
    ///
    /// MUST be registered AFTER `add_par_reduces_iota_delta` (which lands the
    /// diamond `par_reduces_cd_star_diamond`) and after the reverse step bridges
    /// `iota_reduces_to_step` / `delta_reduces_to_step`.
    pub(super) fn add_def_eq_joinable(&mut self) -> Result<(), SpecError> {
        // join_symm: symmetry of the multi-step join witness — destructure via
        // par_strips_witness_cd_star.rec, keep the meeting point, swap the two
        // par_reduces_cd_star legs. Mirror of par_strips_witness_c_star_symm.
        self.add_definition(SpecDefinition {
            name: "join_symm".to_string(),
            type_src: concat!(
                "forall (a : KExpr) (b : KExpr), ",
                "par_strips_witness_cd_star the_red_env a b -> par_strips_witness_cd_star the_red_env b a"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : KExpr) (b : KExpr) (w : par_strips_witness_cd_star the_red_env a b) => ",
                    "@par_strips_witness_cd_star.rec the_red_env a b ",
                    "(fun (_w : par_strips_witness_cd_star the_red_env a b) => par_strips_witness_cd_star the_red_env b a) ",
                    "(fun (c : KExpr) (l1 : par_reduces_cd_star the_red_env a c) (l2 : par_reduces_cd_star the_red_env b c) => ",
                    "par_strips_witness_cd_star.intro the_red_env b a c l2 l1) ",
                    "w"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Symmetry of the multi-step 3-way join witness par_strips_witness_cd_star over the_red_env: ",
                "swap the two sources, keep the meeting point, swap the two par_reduces_cd_star legs. Closed ",
                "term via par_strips_witness_cd_star.rec. Mirror of par_strips_witness_c_star_symm. DerivedProved, ",
                "zero axiom_deps. Part of the church_rosser_whnf retirement track (Brick 6)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd_star".to_string(),
                "par_strips_witness_cd_star".to_string(),
                "par_strips_witness_cd_star.intro".to_string(),
                "par_strips_witness_cd_star.rec".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // join_compose: transitivity of joinability via the diamond. Destructure
        // join a b (-> reduct d, a=>*d, b=>*d) and join b c (-> reduct g, b=>*g,
        // c=>*g), diamond-join the two b-legs (b=>*d, b=>*g) -> join d g (reduct
        // f, d=>*f, g=>*f), then a=>*f = trans(a=>*d, d=>*f) and c=>*f =
        // trans(c=>*g, g=>*f). The ONLY consumer of the carried i1..i8.
        self.add_definition(SpecDefinition {
            name: "join_compose".to_string(),
            type_src: format!(
                concat!(
                    "forall {ib}",
                    "(a : KExpr) (b : KExpr) (c : KExpr), ",
                    "par_strips_witness_cd_star the_red_env a b -> par_strips_witness_cd_star the_red_env b c -> ",
                    "par_strips_witness_cd_star the_red_env a c"
                ),
                ib = I_BINDERS,
            ),
            value_src: Some(format!(
                concat!(
                    "fun {ib}",
                    "(a : KExpr) (b : KExpr) (c : KExpr) ",
                    "(wab : par_strips_witness_cd_star the_red_env a b) ",
                    "(wbc : par_strips_witness_cd_star the_red_env b c) => ",
                    "@par_strips_witness_cd_star.rec the_red_env a b ",
                    "(fun (_w : par_strips_witness_cd_star the_red_env a b) => par_strips_witness_cd_star the_red_env a c) ",
                    "(fun (d : KExpr) (lad : par_reduces_cd_star the_red_env a d) (lbd : par_reduces_cd_star the_red_env b d) => ",
                    "@par_strips_witness_cd_star.rec the_red_env b c ",
                    "(fun (_w2 : par_strips_witness_cd_star the_red_env b c) => par_strips_witness_cd_star the_red_env a c) ",
                    "(fun (g : KExpr) (lbg : par_reduces_cd_star the_red_env b g) (lcg : par_reduces_cd_star the_red_env c g) => ",
                    "@par_strips_witness_cd_star.rec the_red_env d g ",
                    "(fun (_w3 : par_strips_witness_cd_star the_red_env d g) => par_strips_witness_cd_star the_red_env a c) ",
                    "(fun (f : KExpr) (ldf : par_reduces_cd_star the_red_env d f) (lgf : par_reduces_cd_star the_red_env g f) => ",
                    "par_strips_witness_cd_star.intro the_red_env a c f ",
                    "(par_reduces_cd_star_trans the_red_env a d f lad ldf) ",
                    "(par_reduces_cd_star_trans the_red_env c g f lcg lgf)) ",
                    "(par_reduces_cd_star_diamond the_red_env i1 i2 i3 i4 i5 i6 i7 i8 b d g lbd lbg)) ",
                    "wbc) ",
                    "wab"
                ),
                ib = I_BINDERS,
            )),
            is_axiom: false,
            description: concat!(
                "Transitivity of the multi-step 3-way join witness over the_red_env: from join a b and join b c ",
                "build join a c by diamond-joining the two inner b-reducts (par_reduces_cd_star_diamond, the only ",
                "consumer of the carried faithful interfaces i1..i8) and composing the outer legs via ",
                "par_reduces_cd_star_trans. DerivedProved, zero axiom_deps; i1..i8 are CARRIED hypotheses (never ",
                "discharged from the_red_env, never axiomatized). Part of the church_rosser_whnf retirement track (Brick 6)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd_star".to_string(),
                "par_strips_witness_cd_star".to_string(),
                "par_strips_witness_cd_star.intro".to_string(),
                "par_strips_witness_cd_star.rec".to_string(),
                "par_reduces_cd_star_trans".to_string(),
                "par_reduces_cd_star_diamond".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "DefEnvClosed".to_string(),
                "DefEnvLiftClosed".to_string(),
                "RecEnvDefEnvDisjoint".to_string(),
                "RecEnvCtorNoDefVal".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // def_eq_joinable: DefEq e1 e2 -> par_strips_witness_cd_star the_red_env
        // e1 e2, by DefEq.rec. Motive: fun (a b : KExpr) (_ : DefEq a b) =>
        // par_strips_witness_cd_star the_red_env a b. The eleven arms (refl/symm/
        // trans/beta/app_cong/lam_cong/pi_cong/delta/iota/zeta/let_cong) each
        // land a common reduct, as described in the module header.
        self.add_definition(SpecDefinition {
            name: "def_eq_joinable".to_string(),
            type_src: format!(
                concat!(
                    "forall {ib}",
                    "(e1 : KExpr) (e2 : KExpr), ",
                    "DefEq e1 e2 -> par_strips_witness_cd_star the_red_env e1 e2"
                ),
                ib = I_BINDERS,
            ),
            value_src: Some(format!(
                concat!(
                    "fun {ib}",
                    "(e1 : KExpr) (e2 : KExpr) (h : DefEq e1 e2) => ",
                    "DefEq.rec ",
                    // motive
                    "(fun (a : KExpr) (b : KExpr) (_h : DefEq a b) => par_strips_witness_cd_star the_red_env a b) ",
                    // refl
                    "(fun (a : KExpr) => ",
                    "par_strips_witness_cd_star.intro the_red_env a a a ",
                    "(par_reduces_cd_star.refl the_red_env a) (par_reduces_cd_star.refl the_red_env a)) ",
                    // symm
                    "(fun (a : KExpr) (b : KExpr) (_hab : DefEq a b) ",
                    "(ih : par_strips_witness_cd_star the_red_env a b) => join_symm a b ih) ",
                    // trans
                    "(fun (a : KExpr) (b : KExpr) (c : KExpr) (_hab : DefEq a b) (_hbc : DefEq b c) ",
                    "(ih_ab : par_strips_witness_cd_star the_red_env a b) ",
                    "(ih_bc : par_strips_witness_cd_star the_red_env b c) => ",
                    "join_compose i1 i2 i3 i4 i5 i6 i7 i8 a b c ih_ab ih_bc) ",
                    // beta (untyped — only A0, body, arg)
                    "(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) => ",
                    "par_strips_witness_cd_star.intro the_red_env ",
                    "(KExpr.app (KExpr.lam A0 body) arg) (instantiate body arg) (instantiate body arg) ",
                    "(par_reduces_cd_star_beta the_red_env A0 A0 body body arg arg ",
                    "(par_reduces_cd_star.refl the_red_env A0) (par_reduces_cd_star.refl the_red_env body) ",
                    "(par_reduces_cd_star.refl the_red_env arg)) ",
                    "(par_reduces_cd_star.refl the_red_env (instantiate body arg))) ",
                    // app_cong
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (_hf : DefEq f f') (_ha : DefEq a a') ",
                    "(ih_f : par_strips_witness_cd_star the_red_env f f') ",
                    "(ih_a : par_strips_witness_cd_star the_red_env a a') => ",
                    "@par_strips_witness_cd_star.rec the_red_env f f' ",
                    "(fun (_w : par_strips_witness_cd_star the_red_env f f') => ",
                    "par_strips_witness_cd_star the_red_env (KExpr.app f a) (KExpr.app f' a')) ",
                    "(fun (cf : KExpr) (lfcf : par_reduces_cd_star the_red_env f cf) ",
                    "(lf2cf : par_reduces_cd_star the_red_env f' cf) => ",
                    "@par_strips_witness_cd_star.rec the_red_env a a' ",
                    "(fun (_w2 : par_strips_witness_cd_star the_red_env a a') => ",
                    "par_strips_witness_cd_star the_red_env (KExpr.app f a) (KExpr.app f' a')) ",
                    "(fun (ca : KExpr) (laca : par_reduces_cd_star the_red_env a ca) ",
                    "(la2ca : par_reduces_cd_star the_red_env a' ca) => ",
                    "par_strips_witness_cd_star.intro the_red_env (KExpr.app f a) (KExpr.app f' a') (KExpr.app cf ca) ",
                    "(par_reduces_cd_star_app the_red_env f cf a ca lfcf laca) ",
                    "(par_reduces_cd_star_app the_red_env f' cf a' ca lf2cf la2ca)) ",
                    "ih_a) ",
                    "ih_f) ",
                    // lam_cong
                    "(fun (A0 : KExpr) (A0' : KExpr) (b0 : KExpr) (b0' : KExpr) (_hA : DefEq A0 A0') (_hb : DefEq b0 b0') ",
                    "(ih_A : par_strips_witness_cd_star the_red_env A0 A0') ",
                    "(ih_b : par_strips_witness_cd_star the_red_env b0 b0') => ",
                    "@par_strips_witness_cd_star.rec the_red_env A0 A0' ",
                    "(fun (_w : par_strips_witness_cd_star the_red_env A0 A0') => ",
                    "par_strips_witness_cd_star the_red_env (KExpr.lam A0 b0) (KExpr.lam A0' b0')) ",
                    "(fun (cA : KExpr) (lAcA : par_reduces_cd_star the_red_env A0 cA) ",
                    "(lA2cA : par_reduces_cd_star the_red_env A0' cA) => ",
                    "@par_strips_witness_cd_star.rec the_red_env b0 b0' ",
                    "(fun (_w2 : par_strips_witness_cd_star the_red_env b0 b0') => ",
                    "par_strips_witness_cd_star the_red_env (KExpr.lam A0 b0) (KExpr.lam A0' b0')) ",
                    "(fun (cb : KExpr) (lbcb : par_reduces_cd_star the_red_env b0 cb) ",
                    "(lb2cb : par_reduces_cd_star the_red_env b0' cb) => ",
                    "par_strips_witness_cd_star.intro the_red_env (KExpr.lam A0 b0) (KExpr.lam A0' b0') (KExpr.lam cA cb) ",
                    "(par_reduces_cd_star_lam the_red_env A0 cA b0 cb lAcA lbcb) ",
                    "(par_reduces_cd_star_lam the_red_env A0' cA b0' cb lA2cA lb2cb)) ",
                    "ih_b) ",
                    "ih_A) ",
                    // pi_cong
                    "(fun (A0 : KExpr) (A0' : KExpr) (B0 : KExpr) (B0' : KExpr) (_hA : DefEq A0 A0') (_hB : DefEq B0 B0') ",
                    "(ih_A : par_strips_witness_cd_star the_red_env A0 A0') ",
                    "(ih_B : par_strips_witness_cd_star the_red_env B0 B0') => ",
                    "@par_strips_witness_cd_star.rec the_red_env A0 A0' ",
                    "(fun (_w : par_strips_witness_cd_star the_red_env A0 A0') => ",
                    "par_strips_witness_cd_star the_red_env (KExpr.pi A0 B0) (KExpr.pi A0' B0')) ",
                    "(fun (cA : KExpr) (lAcA : par_reduces_cd_star the_red_env A0 cA) ",
                    "(lA2cA : par_reduces_cd_star the_red_env A0' cA) => ",
                    "@par_strips_witness_cd_star.rec the_red_env B0 B0' ",
                    "(fun (_w2 : par_strips_witness_cd_star the_red_env B0 B0') => ",
                    "par_strips_witness_cd_star the_red_env (KExpr.pi A0 B0) (KExpr.pi A0' B0')) ",
                    "(fun (cB : KExpr) (lBcB : par_reduces_cd_star the_red_env B0 cB) ",
                    "(lB2cB : par_reduces_cd_star the_red_env B0' cB) => ",
                    "par_strips_witness_cd_star.intro the_red_env (KExpr.pi A0 B0) (KExpr.pi A0' B0') (KExpr.pi cA cB) ",
                    "(par_reduces_cd_star_pi the_red_env A0 cA B0 cB lAcA lBcB) ",
                    "(par_reduces_cd_star_pi the_red_env A0' cA B0' cB lA2cA lB2cB)) ",
                    "ih_B) ",
                    "ih_A) ",
                    // delta
                    "(fun (e : KExpr) (e' : KExpr) (hd : delta_reduces e e') => ",
                    "par_strips_witness_cd_star.intro the_red_env e e' e' ",
                    "(par_subsumes_par_cd_star the_red_env e e' ",
                    "(par_reduces_cd.delta the_red_env e e' (delta_reduces_to_step e e' hd))) ",
                    "(par_reduces_cd_star.refl the_red_env e')) ",
                    // iota
                    "(fun (e : KExpr) (e' : KExpr) (hi : iota_reduces e e') => ",
                    "par_strips_witness_cd_star.intro the_red_env e e' e' ",
                    "(par_subsumes_par_cd_star the_red_env e e' ",
                    "(par_reduces_cd.iota the_red_env e e' (iota_reduces_to_step e e' hi))) ",
                    "(par_reduces_cd_star.refl the_red_env e')) ",
                    // zeta (untyped — ty0, v0, b0; the let_ redex joins at its
                    // contractum: fire the _star zeta contraction with refl
                    // components on the left leg, exactly the beta arm's shape)
                    "(fun (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr) => ",
                    "par_strips_witness_cd_star.intro the_red_env ",
                    "(KExpr.let_ ty0 v0 b0) (instantiate b0 v0) (instantiate b0 v0) ",
                    "(par_reduces_cd_star_let the_red_env ty0 ty0 v0 v0 b0 b0 ",
                    "(par_reduces_cd_star.refl the_red_env ty0) ",
                    "(par_reduces_cd_star.refl the_red_env v0) ",
                    "(par_reduces_cd_star.refl the_red_env b0)) ",
                    "(par_reduces_cd_star.refl the_red_env (instantiate b0 v0))) ",
                    // let_cong (ternary congruence: destructure the three joins,
                    // meet at let_ cty cv cb via par_reduces_cd_star_let_cong)
                    "(fun (ty0 : KExpr) (ty0' : KExpr) (v0 : KExpr) (v0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
                    "(_hty : DefEq ty0 ty0') (_hv : DefEq v0 v0') (_hb : DefEq b0 b0') ",
                    "(ih_ty : par_strips_witness_cd_star the_red_env ty0 ty0') ",
                    "(ih_v : par_strips_witness_cd_star the_red_env v0 v0') ",
                    "(ih_b : par_strips_witness_cd_star the_red_env b0 b0') => ",
                    "@par_strips_witness_cd_star.rec the_red_env ty0 ty0' ",
                    "(fun (_w : par_strips_witness_cd_star the_red_env ty0 ty0') => ",
                    "par_strips_witness_cd_star the_red_env (KExpr.let_ ty0 v0 b0) (KExpr.let_ ty0' v0' b0')) ",
                    "(fun (cty : KExpr) (ltycty : par_reduces_cd_star the_red_env ty0 cty) ",
                    "(lty2cty : par_reduces_cd_star the_red_env ty0' cty) => ",
                    "@par_strips_witness_cd_star.rec the_red_env v0 v0' ",
                    "(fun (_w2 : par_strips_witness_cd_star the_red_env v0 v0') => ",
                    "par_strips_witness_cd_star the_red_env (KExpr.let_ ty0 v0 b0) (KExpr.let_ ty0' v0' b0')) ",
                    "(fun (cv : KExpr) (lvcv : par_reduces_cd_star the_red_env v0 cv) ",
                    "(lv2cv : par_reduces_cd_star the_red_env v0' cv) => ",
                    "@par_strips_witness_cd_star.rec the_red_env b0 b0' ",
                    "(fun (_w3 : par_strips_witness_cd_star the_red_env b0 b0') => ",
                    "par_strips_witness_cd_star the_red_env (KExpr.let_ ty0 v0 b0) (KExpr.let_ ty0' v0' b0')) ",
                    "(fun (cb : KExpr) (lbcb : par_reduces_cd_star the_red_env b0 cb) ",
                    "(lb2cb : par_reduces_cd_star the_red_env b0' cb) => ",
                    "par_strips_witness_cd_star.intro the_red_env ",
                    "(KExpr.let_ ty0 v0 b0) (KExpr.let_ ty0' v0' b0') (KExpr.let_ cty cv cb) ",
                    "(par_reduces_cd_star_let_cong the_red_env ty0 cty v0 cv b0 cb ltycty lvcv lbcb) ",
                    "(par_reduces_cd_star_let_cong the_red_env ty0' cty v0' cv b0' cb lty2cty lv2cv lb2cb)) ",
                    "ih_b) ",
                    "ih_v) ",
                    "ih_ty) ",
                    // proj_cong (proj/lit rung): single-hole congruence — destructure the
                    // scrutinee join, meet at proj s i csub via par_reduces_cd_star_proj.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) (_hsub : DefEq sub sub') ",
                    "(ih_sub : par_strips_witness_cd_star the_red_env sub sub') => ",
                    "@par_strips_witness_cd_star.rec the_red_env sub sub' ",
                    "(fun (_w : par_strips_witness_cd_star the_red_env sub sub') => ",
                    "par_strips_witness_cd_star the_red_env (KExpr.proj s i sub) (KExpr.proj s i sub')) ",
                    "(fun (csub : KExpr) (lsub : par_reduces_cd_star the_red_env sub csub) ",
                    "(lsub2 : par_reduces_cd_star the_red_env sub' csub) => ",
                    "par_strips_witness_cd_star.intro the_red_env (KExpr.proj s i sub) (KExpr.proj s i sub') (KExpr.proj s i csub) ",
                    "(par_reduces_cd_star_proj the_red_env s i sub csub lsub) ",
                    "(par_reduces_cd_star_proj the_red_env s i sub' csub lsub2)) ",
                    "ih_sub) ",
                    // conclusion
                    "e1 e2 h"
                ),
                ib = I_BINDERS,
            )),
            is_axiom: false,
            description: concat!(
                "def_eq_joinable — every DefEq e1 e2 yields a multi-step 3-way (β+ι+δ+ζ) join witness ",
                "par_strips_witness_cd_star the_red_env e1 e2, by structural DefEq.rec. The trans arm is the sole ",
                "consumer of the carried faithful interfaces i1..i8 (via join_compose -> the diamond ",
                "par_reduces_cd_star_diamond); refl/symm/beta/app_cong/lam_cong/pi_cong/delta/iota/zeta/let_cong ",
                "each land a common reduct directly (zeta fires the _star let contraction with refl components ",
                "exactly like beta; let_cong is the ternary sibling of app_cong via par_reduces_cd_star_let_cong). ",
                "the_red_env is the literal environment everywhere; i1..i8 are CARRIED ",
                "hypotheses (never discharged from the_red_env, never axiomatized). DerivedProved, zero axiom_deps. ",
                "Part of the church_rosser_whnf retirement track (Brick 6)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq".to_string(),
                "DefEq.rec".to_string(),
                "par_reduces_cd".to_string(),
                "par_reduces_cd.delta".to_string(),
                "par_reduces_cd.iota".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_strips_witness_cd_star".to_string(),
                "par_strips_witness_cd_star.intro".to_string(),
                "par_strips_witness_cd_star.rec".to_string(),
                "par_reduces_cd_star_trans".to_string(),
                "par_reduces_cd_star_app".to_string(),
                "par_reduces_cd_star_lam".to_string(),
                "par_reduces_cd_star_pi".to_string(),
                "par_reduces_cd_star_beta".to_string(),
                "par_reduces_cd_star_let".to_string(),
                "par_reduces_cd_star_let_cong".to_string(),
                "par_subsumes_par_cd_star".to_string(),
                "par_reduces_cd_star_diamond".to_string(),
                "delta_reduces_to_step".to_string(),
                "iota_reduces_to_step".to_string(),
                "join_symm".to_string(),
                "join_compose".to_string(),
                "instantiate".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
