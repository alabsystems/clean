// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H++ (#2859 computational-iota/delta track, DELTA INCREMENT Stage 4,
//! the HINDLEY-ROSEN assembly): the ι×δ COMMUTATION — the sole residual obligation
//! of the single-step strong commutation `par_delta_sc` (the iota arm).
//!
//! `iota_step` is the head-reduct function graph (`iota_reduct (red_rec env) e =
//! some e'`); `delta_cong` is a single-position interior δ-step. The target lemma
//!
//!   `iota_delta_comm : iota_step (red_rec env) e e' → delta_cong env e v →
//!                      ∃ d, delta_cong_star env e' d ∧ iota_step (red_rec env) v d`
//!
//! discharges the iota arm of `par_delta_sc` (whose other 7 cases port from the
//! blueprint `SC`). Because a recursor redex's head is a recursor-const (NOT a
//! def-const) and its major is constructor-headed, a single δ-step `e → v` either
//! fires at the HEAD (impossible — `delta_iota_disjoint_absurd`) or in a spine arg,
//! leaving `v` the SAME recursor redex firing the SAME rule.
//!
//! This module mirrors the `par_reduces_c` iota spine machinery for `delta_cong`:
//!   - `delta_cong_star_list`        <- `par_reduces_c_list`        (pointwise δ* on KExpr lists)
//!   - `delta_cong_star_list_refl`   <- `par_reduces_c_list_refl`
//!   - `apply_spine_delta_cong_star` <- `apply_spine_par_c`         (δ* congruence through apply_spine)
//!   - `delta_cong_star_list_append` <- `par_reduces_c_list_append`
//!   - `list_tail_delta_cong`        <- `list_tail_par_c`
//!   - `list_drop_delta_cong`        <- `list_drop_par_c`
//!   - `list_take_delta_cong`        <- `list_take_par_c`
//!   - `kapp_args_delta_cong`        <- `kapp_args_par_c`
//!
//! Runs AFTER `add_par_reduces_delta_sc` (the δ-substitution tower), so `delta_cong`
//! / `delta_cong_star` / `delta_cong_star_app` / the (δ,ι) disjointness primitives
//! (`delta_iota_disjoint_absurd`, `RecEnvDefEnvDisjoint`) and the `par_reduces_c`
//! iota machinery (`iota_reduct_some_inv`, `iota_reduct_app_minimal_boundary_idx`)
//! are all in scope. Part of #2859 (Increment H++, delta increment Stage 4 —
//! Hindley-Rosen assembly).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_par_reduces_iota_delta(&mut self) -> Result<(), SpecError> {
        self.add_delta_cong_star_list_infra()?;
        self.add_list_noconfusion_and_trans()?;
        self.add_delta_cong_spine_cong()?;
        self.add_delta_cong_star_spine_cong()?;
        self.add_recenv_ctor_no_defval()?;
        self.add_iota_delta_disjoint_plumbing()?;
        self.add_iota_delta_comm_helpers()?;
        self.add_iota_delta_comm()?;
        self.add_delta_cong_app_lam_inv()?;
        self.add_sc_join_helpers()?;
        self.add_par_delta_sc()?;
        self.add_par_reduces_cd_star_diamond()?;
        Ok(())
    }

    /// The `par_delta_sc` JOIN helpers — standalone lemmas that each take an already-
    /// inverted δ-step (a reduct equation + the relevant IH witness) and BUILD the
    /// `par_delta_sc_witness`. Hoisting the witness construction (which uses the large
    /// elimination `@par_delta_sc_witness.rec`) into named lemmas keeps every
    /// continuation passed to an inversion a simple application, so `par_delta_sc`'s
    /// value stays small (the kernel rejects the equivalent inline-everything term).
    ///   - `sc_beta_join_{type,body,arg}` — the three δ-subcases of a β-redex.
    ///   - `sc_cong_join_{app,lam,pi}_{left,right}` — the two slots of each congruence.
    ///   - `sc_cong_join_let_{ty,val,body}` — the three slots of the trailing
    ///     `let_cong` congruence over the genuine `KExpr.let_` node (let promotion,
    ///     task #28). (The ZETA arm's joins `sc_let_join_{ty,val,body}` live with the
    ///     δ-subst tower in `par_reduces_delta_sc.rs`.)
    fn add_sc_join_helpers(&mut self) -> Result<(), SpecError> {
        // Beta δ-in-type: the binder type is discarded, so the join is one β+ι (d = u0).
        self.add_definition(SpecDefinition {
            name: "sc_beta_join_type".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (A : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) ",
                "(arg' : KExpr) (w : KExpr) (hbody : par_reduces_c (red_rec env) body body') ",
                "(harg : par_reduces_c (red_rec env) arg arg') ",
                "(heqr : Eq KExpr w (KExpr.app (KExpr.lam A body) arg)), ",
                "par_delta_sc_witness env (instantiate body' arg') w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (A : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) ",
                    "(arg' : KExpr) (w : KExpr) (hbody : par_reduces_c (red_rec env) body body') ",
                    "(harg : par_reduces_c (red_rec env) arg arg') ",
                    "(heqr : Eq KExpr w (KExpr.app (KExpr.lam A body) arg)) => ",
                    "Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env (instantiate body' arg') x) ",
                    "(KExpr.app (KExpr.lam A body) arg) w (Eq.symm KExpr w (KExpr.app (KExpr.lam A body) arg) heqr) ",
                    "(par_delta_sc_witness.intro env (instantiate body' arg') (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg') ",
                    "(delta_cong_star.refl env (instantiate body' arg')) ",
                    "(par_reduces_c.beta (red_rec env) A A body body' arg arg' (par_reduces_c.refl (red_rec env) A) hbody harg))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "sc_beta_join_type — β-redex δ-in-type join: the binder type is discarded, so the δ-reduct fires one β+ι to the common reduct u0 = instantiate body' arg'. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_reduces_c.beta".to_string(),
                "par_reduces_c.refl".to_string(),
                "delta_cong_star.refl".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Beta δ-in-body: body δ* db (from the IH witness), re-substituted via delta_substStar_body.
        self.add_definition(SpecDefinition {
            name: "sc_beta_join_body".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (closed : DefEnvClosed (red_def env)) (A : KExpr) (body' : KExpr) ",
                "(arg : KExpr) (arg' : KExpr) (bt : KExpr) (w : KExpr) ",
                "(harg : par_reduces_c (red_rec env) arg arg') ",
                "(heqr : Eq KExpr w (KExpr.app (KExpr.lam A bt) arg)) ",
                "(ihw : par_delta_sc_witness env body' bt), ",
                "par_delta_sc_witness env (instantiate body' arg') w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (closed : DefEnvClosed (red_def env)) (A : KExpr) (body' : KExpr) ",
                    "(arg : KExpr) (arg' : KExpr) (bt : KExpr) (w : KExpr) ",
                    "(harg : par_reduces_c (red_rec env) arg arg') ",
                    "(heqr : Eq KExpr w (KExpr.app (KExpr.lam A bt) arg)) ",
                    "(ihw : par_delta_sc_witness env body' bt) => ",
                    "@par_delta_sc_witness.rec env body' bt ",
                    "(fun (_ : par_delta_sc_witness env body' bt) => par_delta_sc_witness env (instantiate body' arg') w) ",
                    "(fun (db : KExpr) (hdb : delta_cong_star env body' db) (hpbt : par_reduces_c (red_rec env) bt db) => ",
                    "Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env (instantiate body' arg') x) ",
                    "(KExpr.app (KExpr.lam A bt) arg) w (Eq.symm KExpr w (KExpr.app (KExpr.lam A bt) arg) heqr) ",
                    "(par_delta_sc_witness.intro env (instantiate body' arg') (KExpr.app (KExpr.lam A bt) arg) (instantiate db arg') ",
                    "(delta_substStar_body env closed arg' Nat.zero body' db hdb) ",
                    "(par_reduces_c.beta (red_rec env) A A bt db arg arg' (par_reduces_c.refl (red_rec env) A) hpbt harg))) ",
                    "ihw"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "sc_beta_join_body — β-redex δ-in-body join: destructure the body IH witness (db, δ* body' db, par bt db), re-substitute the δ-chain into the argument via delta_substStar_body, fire one β+ι. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_delta_sc_witness.rec".to_string(),
                "par_reduces_c.beta".to_string(),
                "par_reduces_c.refl".to_string(),
                "delta_substStar_body".to_string(),
                "DefEnvClosed".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Beta δ-in-arg: arg δ* da (from the IH witness), re-substituted via delta_substStar_val.
        self.add_definition(SpecDefinition {
            name: "sc_beta_join_arg".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (liftclosed : DefEnvLiftClosed (red_def env)) (A : KExpr) (body : KExpr) ",
                "(body' : KExpr) (arg' : KExpr) (ar : KExpr) (w : KExpr) ",
                "(hbody : par_reduces_c (red_rec env) body body') ",
                "(heqr : Eq KExpr w (KExpr.app (KExpr.lam A body) ar)) ",
                "(ihw : par_delta_sc_witness env arg' ar), ",
                "par_delta_sc_witness env (instantiate body' arg') w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (liftclosed : DefEnvLiftClosed (red_def env)) (A : KExpr) (body : KExpr) ",
                    "(body' : KExpr) (arg' : KExpr) (ar : KExpr) (w : KExpr) ",
                    "(hbody : par_reduces_c (red_rec env) body body') ",
                    "(heqr : Eq KExpr w (KExpr.app (KExpr.lam A body) ar)) ",
                    "(ihw : par_delta_sc_witness env arg' ar) => ",
                    "@par_delta_sc_witness.rec env arg' ar ",
                    "(fun (_ : par_delta_sc_witness env arg' ar) => par_delta_sc_witness env (instantiate body' arg') w) ",
                    "(fun (da : KExpr) (hda : delta_cong_star env arg' da) (hpar : par_reduces_c (red_rec env) ar da) => ",
                    "Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env (instantiate body' arg') x) ",
                    "(KExpr.app (KExpr.lam A body) ar) w (Eq.symm KExpr w (KExpr.app (KExpr.lam A body) ar) heqr) ",
                    "(par_delta_sc_witness.intro env (instantiate body' arg') (KExpr.app (KExpr.lam A body) ar) (instantiate body' da) ",
                    "(delta_substStar_val env liftclosed arg' da hda body' Nat.zero) ",
                    "(par_reduces_c.beta (red_rec env) A A body body' ar da (par_reduces_c.refl (red_rec env) A) hbody hpar))) ",
                    "ihw"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "sc_beta_join_arg — β-redex δ-in-arg join: destructure the argument IH witness (da, δ* arg' da, par ar da), re-substitute the δ-chain into the body via delta_substStar_val, fire one β+ι. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_delta_sc_witness.rec".to_string(),
                "par_reduces_c.beta".to_string(),
                "par_reduces_c.refl".to_string(),
                "delta_substStar_val".to_string(),
                "DefEnvLiftClosed".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The six congruence joins (app/lam/pi × left/right).
        for (head_tag, head, star, pc) in [
            (
                "app",
                "KExpr.app",
                "delta_cong_star_app",
                "par_reduces_c.app",
            ),
            (
                "lam",
                "KExpr.lam",
                "delta_cong_star_lam",
                "par_reduces_c.lam",
            ),
            ("pi", "KExpr.pi", "delta_cong_star_pi", "par_reduces_c.pi"),
        ] {
            // left: δ reduces slot0 (b0); slot1 (n1) is carried by its premise h1.
            self.add_definition(SpecDefinition {
                name: format!("sc_cong_join_{head_tag}_left"),
                type_src: format!(
                    "forall (env : RedEnv) (n0p : KExpr) (n1 : KExpr) (n1p : KExpr) (b0 : KExpr) (w : KExpr) \
                     (h1 : par_reduces_c (red_rec env) n1 n1p) (heqw : Eq KExpr w ({head} b0 n1)) \
                     (ihw : par_delta_sc_witness env n0p b0), par_delta_sc_witness env ({head} n0p n1p) w"
                ),
                value_src: Some(format!(
                    "fun (env : RedEnv) (n0p : KExpr) (n1 : KExpr) (n1p : KExpr) (b0 : KExpr) (w : KExpr) \
                     (h1 : par_reduces_c (red_rec env) n1 n1p) (heqw : Eq KExpr w ({head} b0 n1)) \
                     (ihw : par_delta_sc_witness env n0p b0) => \
                     @par_delta_sc_witness.rec env n0p b0 \
                     (fun (_ : par_delta_sc_witness env n0p b0) => par_delta_sc_witness env ({head} n0p n1p) w) \
                     (fun (d0 : KExpr) (hd0 : delta_cong_star env n0p d0) (hp0 : par_reduces_c (red_rec env) b0 d0) => \
                     Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env ({head} n0p n1p) x) \
                     ({head} b0 n1) w (Eq.symm KExpr w ({head} b0 n1) heqw) \
                     (par_delta_sc_witness.intro env ({head} n0p n1p) ({head} b0 n1) ({head} d0 n1p) \
                     ({star} env n0p d0 n1p n1p hd0 (delta_cong_star.refl env n1p)) \
                     ({pc} (red_rec env) b0 d0 n1 n1p hp0 h1))) \
                     ihw"
                )),
                is_axiom: false,
                description: format!(
                    "sc_cong_join_{head_tag}_left — {head_tag} congruence join (δ in slot0): destructure the slot0 IH witness, re-close δ* via {star} (slot1 fixed) and β+ι via {pc}. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, Stage 4)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_delta_sc_witness".to_string(),
                    "par_delta_sc_witness.intro".to_string(),
                    "par_delta_sc_witness.rec".to_string(),
                    "delta_cong_star.refl".to_string(),
                    star.to_string(),
                    pc.to_string(),
                    "Eq.substType".to_string(),
                    "Eq.symm".to_string(),
                    "red_rec".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
            // right: δ reduces slot1 (b1); slot0 (n0) is carried by its premise h0.
            self.add_definition(SpecDefinition {
                name: format!("sc_cong_join_{head_tag}_right"),
                type_src: format!(
                    "forall (env : RedEnv) (n0 : KExpr) (n0p : KExpr) (n1p : KExpr) (b1 : KExpr) (w : KExpr) \
                     (h0 : par_reduces_c (red_rec env) n0 n0p) (heqw : Eq KExpr w ({head} n0 b1)) \
                     (ihw : par_delta_sc_witness env n1p b1), par_delta_sc_witness env ({head} n0p n1p) w"
                ),
                value_src: Some(format!(
                    "fun (env : RedEnv) (n0 : KExpr) (n0p : KExpr) (n1p : KExpr) (b1 : KExpr) (w : KExpr) \
                     (h0 : par_reduces_c (red_rec env) n0 n0p) (heqw : Eq KExpr w ({head} n0 b1)) \
                     (ihw : par_delta_sc_witness env n1p b1) => \
                     @par_delta_sc_witness.rec env n1p b1 \
                     (fun (_ : par_delta_sc_witness env n1p b1) => par_delta_sc_witness env ({head} n0p n1p) w) \
                     (fun (d1 : KExpr) (hd1 : delta_cong_star env n1p d1) (hp1 : par_reduces_c (red_rec env) b1 d1) => \
                     Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env ({head} n0p n1p) x) \
                     ({head} n0 b1) w (Eq.symm KExpr w ({head} n0 b1) heqw) \
                     (par_delta_sc_witness.intro env ({head} n0p n1p) ({head} n0 b1) ({head} n0p d1) \
                     ({star} env n0p n0p n1p d1 (delta_cong_star.refl env n0p) hd1) \
                     ({pc} (red_rec env) n0 n0p b1 d1 h0 hp1))) \
                     ihw"
                )),
                is_axiom: false,
                description: format!(
                    "sc_cong_join_{head_tag}_right — {head_tag} congruence join (δ in slot1): destructure the slot1 IH witness, re-close δ* via {star} (slot0 fixed) and β+ι via {pc}. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, Stage 4)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_delta_sc_witness".to_string(),
                    "par_delta_sc_witness.intro".to_string(),
                    "par_delta_sc_witness.rec".to_string(),
                    "delta_cong_star.refl".to_string(),
                    star.to_string(),
                    pc.to_string(),
                    "Eq.substType".to_string(),
                    "Eq.symm".to_string(),
                    "red_rec".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // sc_cong_join_proj (proj/lit rung): the SINGLE-hole congruence join at the
        // genuine proj node — δ reduces the (only) scrutinee. Destructure the scrutinee
        // IH witness, re-close δ* via delta_cong_star_proj and β+ι via par_reduces_c.proj.
        // The proj analogue of sc_cong_join_{app,lam,pi}_left with no fixed companion slot.
        self.add_definition(SpecDefinition {
            name: "sc_cong_join_proj".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (n0p : KExpr) (b0 : KExpr) (w : KExpr) (s : Name) (i : Nat) ",
                "(heqw : Eq KExpr w (KExpr.proj s i b0)) (ihw : par_delta_sc_witness env n0p b0), ",
                "par_delta_sc_witness env (KExpr.proj s i n0p) w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (n0p : KExpr) (b0 : KExpr) (w : KExpr) (s : Name) (i : Nat) ",
                    "(heqw : Eq KExpr w (KExpr.proj s i b0)) (ihw : par_delta_sc_witness env n0p b0) => ",
                    "@par_delta_sc_witness.rec env n0p b0 ",
                    "(fun (_ : par_delta_sc_witness env n0p b0) => par_delta_sc_witness env (KExpr.proj s i n0p) w) ",
                    "(fun (d0 : KExpr) (hd0 : delta_cong_star env n0p d0) (hp0 : par_reduces_c (red_rec env) b0 d0) => ",
                    "Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env (KExpr.proj s i n0p) x) ",
                    "(KExpr.proj s i b0) w (Eq.symm KExpr w (KExpr.proj s i b0) heqw) ",
                    "(par_delta_sc_witness.intro env (KExpr.proj s i n0p) (KExpr.proj s i b0) (KExpr.proj s i d0) ",
                    "(delta_cong_star_proj env s i n0p d0 hd0) ",
                    "(par_reduces_c.proj (red_rec env) s i b0 d0 hp0))) ",
                    "ihw"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "sc_cong_join_proj — single-hole proj congruence join (δ in the scrutinee): destructure the scrutinee IH witness, re-close δ* via delta_cong_star_proj and β+ι via par_reduces_c.proj. The proj analogue of sc_cong_join_{app,lam,pi}_left with no fixed companion slot. DerivedProved, zero axiom_deps. Part of the proj/lit fragment rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_delta_sc_witness.rec".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star_proj".to_string(),
                "par_reduces_c".to_string(),
                "par_reduces_c.proj".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The three let_cong congruence joins (let promotion, task #28): the 3-slot
        // mirrors of sc_cong_join_{app,lam,pi}_{left,right} at the genuine let_ node.
        // δ in one slot (from the slot IH witness), the other two slots carried by
        // their par premises; δ* re-closes via the compound delta_cong_star_let
        // (refls on the fixed slots), β+ι+ζ via one par_reduces_c.let_cong.
        //
        // sc_cong_join_let_ty: δ in the ty slot.
        self.add_definition(SpecDefinition {
            name: "sc_cong_join_let_ty".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (typ : KExpr) (val : KExpr) (valp : KExpr) (body : KExpr) ",
                "(bodyp : KExpr) (b0 : KExpr) (w : KExpr) ",
                "(hval : par_reduces_c (red_rec env) val valp) ",
                "(hbody : par_reduces_c (red_rec env) body bodyp) ",
                "(heqw : Eq KExpr w (KExpr.let_ b0 val body)) ",
                "(ihw : par_delta_sc_witness env typ b0), ",
                "par_delta_sc_witness env (KExpr.let_ typ valp bodyp) w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (typ : KExpr) (val : KExpr) (valp : KExpr) (body : KExpr) ",
                    "(bodyp : KExpr) (b0 : KExpr) (w : KExpr) ",
                    "(hval : par_reduces_c (red_rec env) val valp) ",
                    "(hbody : par_reduces_c (red_rec env) body bodyp) ",
                    "(heqw : Eq KExpr w (KExpr.let_ b0 val body)) ",
                    "(ihw : par_delta_sc_witness env typ b0) => ",
                    "@par_delta_sc_witness.rec env typ b0 ",
                    "(fun (_ : par_delta_sc_witness env typ b0) => par_delta_sc_witness env (KExpr.let_ typ valp bodyp) w) ",
                    "(fun (d0 : KExpr) (hd0 : delta_cong_star env typ d0) (hp0 : par_reduces_c (red_rec env) b0 d0) => ",
                    "Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env (KExpr.let_ typ valp bodyp) x) ",
                    "(KExpr.let_ b0 val body) w (Eq.symm KExpr w (KExpr.let_ b0 val body) heqw) ",
                    "(par_delta_sc_witness.intro env (KExpr.let_ typ valp bodyp) (KExpr.let_ b0 val body) (KExpr.let_ d0 valp bodyp) ",
                    "(delta_cong_star_let env typ d0 valp valp bodyp bodyp hd0 ",
                    "(delta_cong_star.refl env valp) (delta_cong_star.refl env bodyp)) ",
                    "(par_reduces_c.let_cong (red_rec env) b0 d0 val valp body bodyp hp0 hval hbody))) ",
                    "ihw"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "sc_cong_join_let_ty — let_cong congruence join (δ in the ty slot): destructure the ty IH witness, re-close δ* via delta_cong_star_let (val/body fixed) and β+ι+ζ via par_reduces_c.let_cong. The 3-slot mirror of sc_cong_join_lam_left at the genuine let_ node (let promotion, task #28). DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_delta_sc_witness.rec".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star_let".to_string(),
                "par_reduces_c.let_cong".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // sc_cong_join_let_val: δ in the val slot.
        self.add_definition(SpecDefinition {
            name: "sc_cong_join_let_val".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (ty : KExpr) (typ : KExpr) (valp : KExpr) (body : KExpr) ",
                "(bodyp : KExpr) (b1 : KExpr) (w : KExpr) ",
                "(hty : par_reduces_c (red_rec env) ty typ) ",
                "(hbody : par_reduces_c (red_rec env) body bodyp) ",
                "(heqw : Eq KExpr w (KExpr.let_ ty b1 body)) ",
                "(ihw : par_delta_sc_witness env valp b1), ",
                "par_delta_sc_witness env (KExpr.let_ typ valp bodyp) w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (ty : KExpr) (typ : KExpr) (valp : KExpr) (body : KExpr) ",
                    "(bodyp : KExpr) (b1 : KExpr) (w : KExpr) ",
                    "(hty : par_reduces_c (red_rec env) ty typ) ",
                    "(hbody : par_reduces_c (red_rec env) body bodyp) ",
                    "(heqw : Eq KExpr w (KExpr.let_ ty b1 body)) ",
                    "(ihw : par_delta_sc_witness env valp b1) => ",
                    "@par_delta_sc_witness.rec env valp b1 ",
                    "(fun (_ : par_delta_sc_witness env valp b1) => par_delta_sc_witness env (KExpr.let_ typ valp bodyp) w) ",
                    "(fun (d1 : KExpr) (hd1 : delta_cong_star env valp d1) (hp1 : par_reduces_c (red_rec env) b1 d1) => ",
                    "Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env (KExpr.let_ typ valp bodyp) x) ",
                    "(KExpr.let_ ty b1 body) w (Eq.symm KExpr w (KExpr.let_ ty b1 body) heqw) ",
                    "(par_delta_sc_witness.intro env (KExpr.let_ typ valp bodyp) (KExpr.let_ ty b1 body) (KExpr.let_ typ d1 bodyp) ",
                    "(delta_cong_star_let env typ typ valp d1 bodyp bodyp ",
                    "(delta_cong_star.refl env typ) hd1 (delta_cong_star.refl env bodyp)) ",
                    "(par_reduces_c.let_cong (red_rec env) ty typ b1 d1 body bodyp hty hp1 hbody))) ",
                    "ihw"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "sc_cong_join_let_val — let_cong congruence join (δ in the val slot): destructure the val IH witness, re-close δ* via delta_cong_star_let (ty/body fixed) and β+ι+ζ via par_reduces_c.let_cong. Let promotion, task #28. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_delta_sc_witness.rec".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star_let".to_string(),
                "par_reduces_c.let_cong".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // sc_cong_join_let_body: δ in the body slot.
        self.add_definition(SpecDefinition {
            name: "sc_cong_join_let_body".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (ty : KExpr) (typ : KExpr) (val : KExpr) (valp : KExpr) ",
                "(bodyp : KExpr) (b2 : KExpr) (w : KExpr) ",
                "(hty : par_reduces_c (red_rec env) ty typ) ",
                "(hval : par_reduces_c (red_rec env) val valp) ",
                "(heqw : Eq KExpr w (KExpr.let_ ty val b2)) ",
                "(ihw : par_delta_sc_witness env bodyp b2), ",
                "par_delta_sc_witness env (KExpr.let_ typ valp bodyp) w"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (ty : KExpr) (typ : KExpr) (val : KExpr) (valp : KExpr) ",
                    "(bodyp : KExpr) (b2 : KExpr) (w : KExpr) ",
                    "(hty : par_reduces_c (red_rec env) ty typ) ",
                    "(hval : par_reduces_c (red_rec env) val valp) ",
                    "(heqw : Eq KExpr w (KExpr.let_ ty val b2)) ",
                    "(ihw : par_delta_sc_witness env bodyp b2) => ",
                    "@par_delta_sc_witness.rec env bodyp b2 ",
                    "(fun (_ : par_delta_sc_witness env bodyp b2) => par_delta_sc_witness env (KExpr.let_ typ valp bodyp) w) ",
                    "(fun (d2 : KExpr) (hd2 : delta_cong_star env bodyp d2) (hp2 : par_reduces_c (red_rec env) b2 d2) => ",
                    "Eq.substType KExpr (fun (x : KExpr) => par_delta_sc_witness env (KExpr.let_ typ valp bodyp) x) ",
                    "(KExpr.let_ ty val b2) w (Eq.symm KExpr w (KExpr.let_ ty val b2) heqw) ",
                    "(par_delta_sc_witness.intro env (KExpr.let_ typ valp bodyp) (KExpr.let_ ty val b2) (KExpr.let_ typ valp d2) ",
                    "(delta_cong_star_let env typ typ valp valp bodyp d2 ",
                    "(delta_cong_star.refl env typ) (delta_cong_star.refl env valp) hd2) ",
                    "(par_reduces_c.let_cong (red_rec env) ty typ val valp b2 d2 hty hval hp2))) ",
                    "ihw"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "sc_cong_join_let_body — let_cong congruence join (δ in the body slot): destructure the body IH witness, re-close δ* via delta_cong_star_let (ty/val fixed) and β+ι+ζ via par_reduces_c.let_cong. Let promotion, task #28. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, Stage 4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_delta_sc_witness.rec".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star_let".to_string(),
                "par_reduces_c.let_cong".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// `delta_cong_app_lam_inv` — a flat 3-way inversion of a δ-step at a β-redex
    /// `app (lam A body) arg`: the δ lands in the binder TYPE (`kt`), the BODY (`kb`),
    /// or the ARGUMENT (`ka`). Internally nests `delta_cong_app_inv` (function leg) over
    /// `delta_cong_lam_inv` (type/body split), folding the two-level reduct equations
    /// into one per continuation via `Eq.trans` + `Eq.cong`. Hoisting the nesting into
    /// its own (abstract-continuation) lemma keeps `par_delta_sc`'s beta arm FLAT.
    /// (Since the let promotion, task #28, the `let_` arm no longer rides this app(lam)
    /// inversion — it has its own `delta_cong_let_inv` in `par_reduces_delta_sc.rs`.)
    fn add_delta_cong_app_lam_inv(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "delta_cong_app_lam_inv".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (A : KExpr) (body : KExpr) (arg : KExpr) (r : KExpr) (C : Type), ",
                "delta_cong env (KExpr.app (KExpr.lam A body) arg) r -> ",
                "(forall (At : KExpr), delta_cong env A At -> Eq KExpr r (KExpr.app (KExpr.lam At body) arg) -> C) -> ",
                "(forall (bt : KExpr), delta_cong env body bt -> Eq KExpr r (KExpr.app (KExpr.lam A bt) arg) -> C) -> ",
                "(forall (ar : KExpr), delta_cong env arg ar -> Eq KExpr r (KExpr.app (KExpr.lam A body) ar) -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(delta_cong_app_lam_inv_proof()),
            is_axiom: false,
            description: concat!(
                "delta_cong_app_lam_inv — flat 3-way inversion of a δ-step at a β-redex app (lam A body) arg: ",
                "δ-in-type (kt), δ-in-body (kb), δ-in-arg (ka). Nests delta_cong_app_inv over delta_cong_lam_inv ",
                "and folds the two-level reduct equations into one per continuation (Eq.trans + Eq.cong). Keeps ",
                "par_delta_sc's beta/let_ arms flat. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, ",
                "delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong_app_inv".to_string(),
                "delta_cong_lam_inv".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick 4 helpers (the ι×δ reconstruction substrate):
    ///   - `delta_cong_star_preserves_head_const` — the STAR-lift of the landed
    ///     single-step `delta_cong_preserves_head_const` (the head const survives a
    ///     multi-step δ chain, under the def-value-none guard).
    ///   - `list_head_some_delta_cong` — a Type-valued list_head congruence: a δ*-list
    ///     relation carries `list_head xs = some a` to `∃b, list_head ys = some b ∧
    ///     delta_cong_star a b` (inverts the δ*-list derivation via the list
    ///     no-confusion lemmas + list_head_cons).
    ///   - `iota_reduct_recon_general` — the generalized iota-reduct reconstruction:
    ///     from the five preserved lookups (recursor head / recmeta / major-at-K /
    ///     constructor head / rule) rebuild `iota_reduct env e0 = some REDUCT` via five
    ///     `opt_bind_some_intro`. The δ-agnostic generalization of `iota_reduct_par_app_recon`
    ///     (the major sits at the interior boundary K, not as the last applied arg).
    fn add_iota_delta_comm_helpers(&mut self) -> Result<(), SpecError> {
        // delta_cong_star_preserves_head_const.
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_preserves_head_const".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (f : KExpr) (f' : KExpr) (nm : Name), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> ",
                "Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr) -> ",
                "delta_cong_star env f f' -> ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn f')) (OptionType.some Name nm)"
            )
            .to_string(),
            value_src: Some(delta_cong_star_preserves_head_const_proof()),
            is_axiom: false,
            description: concat!(
                "delta_cong_star_preserves_head_const — the STAR-lift of delta_cong_preserves_head_const: under the ",
                "head-const + def-value-none guards, a multi-step δ chain delta_cong_star env f f' preserves the ",
                "spine head const (kexpr_const_name (kapp_fn f') = some nm). delta_cong_star.rec with a ",
                "head-const-guard-carrying motive; refl = identity, step threads the single-step preservation ",
                "through the IH. The head-stability fact the ι×δ commutation's major/recursor reconstruction ",
                "consumes. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
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
                "delta_cong_preserves_head_const".to_string(),
                "defval_for".to_string(),
                "red_def".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_head_some_delta_cong.
        self.add_definition(SpecDefinition {
            name: "list_head_some_delta_cong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (xs : ListType KExpr) (ys : ListType KExpr) (a : KExpr) (C : Type), ",
                "delta_cong_star_list env xs ys -> ",
                "Eq (OptionType KExpr) (list_head xs) (OptionType.some KExpr a) -> ",
                "(forall (b : KExpr), Eq (OptionType KExpr) (list_head ys) (OptionType.some KExpr b) -> ",
                "delta_cong_star env a b -> C) -> C"
            )
            .to_string(),
            value_src: Some(list_head_some_delta_cong_proof()),
            is_axiom: false,
            description: concat!(
                "list_head_some_delta_cong — a Type-valued list_head congruence under the pointwise δ*-list ",
                "relation: from delta_cong_star_list env xs ys and list_head xs = some a, deliver to a continuation ",
                "a witness b with list_head ys = some b and delta_cong_star env a b. delta_cong_star_list.rec ",
                "inversion (nil arm absurd via option_none_ne_some_type on list_head nil = none; cons arm reads the ",
                "head fields through list_head_cons + option_some_inj). The head-extraction the ι×δ commutation ",
                "uses to lift the major out of the δ*-related spine. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star".to_string(),
                "delta_cong_star_list".to_string(),
                "delta_cong_star_list.rec".to_string(),
                "list_head".to_string(),
                "list_head_cons".to_string(),
                "option_some_inj".to_string(),
                "option_none_ne_some_type".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_reduct_recon_general.
        self.add_definition(SpecDefinition {
            name: "iota_reduct_recon_general".to_string(),
            type_src: iota_reduct_recon_general_type(),
            value_src: Some(iota_reduct_recon_general_proof()),
            is_axiom: false,
            description: concat!(
                "iota_reduct_recon_general — the δ-agnostic generalization of iota_reduct_par_app_recon: from the ",
                "five preserved lookups (recursor head = some recname; recmeta_for env recname = some meta; the ",
                "major at the interior boundary K = list_head (list_drop K (kapp_args e0)) = some major; the ",
                "constructor head = some cname; recrule_for env recname cname = some rule), rebuild iota_reduct env ",
                "e0 = some REDUCT, where REDUCT is the iota_reduct formula over kapp_args e0 / kapp_args major / ",
                "recrule_rhs rule. Five nested opt_bind_some_intro (e0 generic, major at the interior boundary, NOT ",
                "the last applied arg). The reconstruction the ι×δ commutation fires on the δ-stepped redex v. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "opt_bind".to_string(),
                "opt_bind_some_intro".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_args".to_string(),
                "recmeta_for".to_string(),
                "recrule_for".to_string(),
                "recmeta_num_params".to_string(),
                "recmeta_num_motives".to_string(),
                "recmeta_num_minors".to_string(),
                "recmeta_num_indices".to_string(),
                "recrule_num_fields".to_string(),
                "recrule_rhs".to_string(),
                "apply_spine".to_string(),
                "list_drop".to_string(),
                "list_take".to_string(),
                "list_head".to_string(),
                "list_length".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 2: `delta_cong_star_spine_cong` — the STAR-lift of `delta_cong_spine_cong`.
    /// Under the head-const + def-value-none guards, a multi-step δ chain `delta_cong_star
    /// env f f'` induces a pointwise spine-args δ*: `delta_cong_star_list env (kapp_args f)
    /// (kapp_args f')`. `delta_cong_star.rec` on the chain with a guard-carrying motive
    /// (the head-const guard is preserved step-by-step by `delta_cong_preserves_head_const`;
    /// the def-value-none guard is constant in the fixed `nm`): refl arm = `delta_cong_star_list_refl`,
    /// step arm composes the single-step `delta_cong_spine_cong` on the head with the IH
    /// (re-guarded by the preserved head) through `delta_cong_star_list_trans`. The δ*-spine
    /// reflection the ι×δ commutation's interior-δ reconstruction consumes.
    fn add_delta_cong_star_spine_cong(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_spine_cong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (f : KExpr) (f' : KExpr) (nm : Name), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> ",
                "Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr) -> ",
                "delta_cong_star env f f' -> ",
                "delta_cong_star_list env (kapp_args f) (kapp_args f')"
            )
            .to_string(),
            value_src: Some(delta_cong_star_spine_cong_proof()),
            is_axiom: false,
            description: concat!(
                "delta_cong_star_spine_cong — the STAR-lift of delta_cong_spine_cong. Under the head-const guard ",
                "(kexpr_const_name (kapp_fn f) = some nm) and the def-value-none guard (defval_for (red_def env) nm ",
                "= none), a multi-step δ chain delta_cong_star env f f' induces delta_cong_star_list env (kapp_args ",
                "f) (kapp_args f'). delta_cong_star.rec on the chain with a head-const-guard-carrying motive (the ",
                "guard preserved step-by-step by delta_cong_preserves_head_const; the def-value-none guard constant ",
                "in the fixed nm): refl = delta_cong_star_list_refl, step composes the single-step delta_cong_spine_cong ",
                "on the head (re-guarded by the preserved head) with the IH through delta_cong_star_list_trans. The ",
                "δ*-spine reflection the ι×δ commutation's interior-δ reconstruction consumes. DerivedProved, zero ",
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
                "delta_cong_star_list".to_string(),
                "delta_cong_star_list_refl".to_string(),
                "delta_cong_star_list_trans".to_string(),
                "delta_cong_spine_cong".to_string(),
                "delta_cong_preserves_head_const".to_string(),
                "defval_for".to_string(),
                "red_def".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_args".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick 3: the constructor/def-value-disjointness interface `RecEnvCtorNoDefVal`
    /// and its projector `recenv_ctor_no_defval_cname`. The head name `cname` of a
    /// constructor-headed term that is a constructor of some recursor rule
    /// (`recrule_for (red_rec env) recname cname = some _`) carries NO def value
    /// (`defval_for (red_def env) cname = none`): a constructor is never a definition.
    /// A faithful defined HYPOTHESIS (real inductive, proper recursor, NOT an axiom);
    /// mirrors `RecEnvDefEnvDisjoint` / `RecEnvCtorNoRecMeta`. Its witness for the
    /// kernel env is discharged at the end of the track. The ι×δ commutation consumes
    /// its projector to discharge a δ-step at the major's constructor head (the
    /// constructor head carries no def value, so the interior δ leaves it fixed).
    fn add_recenv_ctor_no_defval(&mut self) -> Result<(), SpecError> {
        let no_defval_fact = concat!(
            "forall (recname : Name) (cname : Name) (rule : RecRule) (major : KExpr), ",
            "Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> ",
            "Eq (OptionType RecRule) (recrule_for (red_rec env) recname cname) (OptionType.some RecRule rule) -> ",
            "Eq (OptionType KExpr) (defval_for (red_def env) cname) (OptionType.none KExpr)"
        );
        self.add_inductive(
            &format!(
                "inductive RecEnvCtorNoDefVal (env : RedEnv) : Type\n| mk : ({no_defval_fact}) → RecEnvCtorNoDefVal env"
            ),
            "Constructor/def-value-disjointness interface for a combined reduction environment: the head \
             name cname of a constructor-headed term that is a constructor of some recursor rule \
             (recrule_for (red_rec env) recname cname = some _) carries NO def value (defval_for (red_def \
             env) cname = none). A constructor is never a definition. A defined hypothesis (NOT an axiom); \
             its witness for the kernel env is discharged at the end of the track. The δ analogue of \
             RecEnvCtorNoRecMeta on the def-value slot; the ι×δ commutation consumes its projector to \
             discharge an interior δ-step at the major's constructor head. Part of #2859 (Increment H++, \
             delta increment Stage 4).",
        )?;

        self.add_definition(SpecDefinition {
            name: "recenv_ctor_no_defval_cname".to_string(),
            type_src: "forall (env : RedEnv) (recname : Name) (cname : Name) (rule : RecRule) (major : KExpr), \
                 RecEnvCtorNoDefVal env -> \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
                 Eq (OptionType RecRule) (recrule_for (red_rec env) recname cname) (OptionType.some RecRule rule) -> \
                 Eq (OptionType KExpr) (defval_for (red_def env) cname) (OptionType.none KExpr)"
                .to_string(),
            value_src: Some(format!(
                "fun (env : RedEnv) (recname : Name) (cname : Name) (rule : RecRule) (major : KExpr) \
                 (w : RecEnvCtorNoDefVal env) \
                 (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (hrule : Eq (OptionType RecRule) (recrule_for (red_rec env) recname cname) (OptionType.some RecRule rule)) => \
                 RecEnvCtorNoDefVal.rec env \
                 (fun (_ : RecEnvCtorNoDefVal env) => \
                 Eq (OptionType KExpr) (defval_for (red_def env) cname) (OptionType.none KExpr)) \
                 (fun (hc : {no_defval_fact}) => hc recname cname rule major hhead hrule) \
                 w"
            )),
            is_axiom: false,
            description: concat!(
                "Projector for RecEnvCtorNoDefVal: in a ctor/no-defval combined environment, the head name cname ",
                "of a term whose head is a constructor of recursor recname (recrule_for (red_rec env) recname cname ",
                "= some rule) carries no def value (defval_for (red_def env) cname = none). Projects the single ",
                "disjointness fact via RecEnvCtorNoDefVal.rec and applies it to the head + rule witnesses. The ",
                "interface the ι×δ commutation consumes to discharge an interior δ-step at the major's constructor ",
                "head. The δ analogue of recenv_ctor_no_recmeta_cname on the def-value slot. DerivedProved; zero ",
                "axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvCtorNoDefVal".to_string(),
                "RecEnvCtorNoDefVal.rec".to_string(),
                "recrule_for".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "defval_for".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick 1: the KExpr-list no-confusion primitives (`list_cons_inj_head`,
    /// `list_cons_inj_tail`, `list_nil_ne_cons`) and the transitivity of the
    /// pointwise δ*-list relation (`delta_cong_star_list_trans`). The list
    /// no-confusion lemmas mirror `option_some_inj` / `option_none_ne_some_type`
    /// (a `ListType.rec` payload projector + `Eq.cong` for the injections; a
    /// large-elimination discriminator `list_is_nil` + `Empty.rec` for the
    /// nil-vs-cons disjointness). `delta_cong_star_list_trans` recurses on the
    /// first chain with a `forall cs` motive; the cons arm INVERTS the second
    /// chain at `cons x' xs0'` (via a `ListType`-eq-carrying `delta_cong_star_list.rec`
    /// motive discharged by the no-confusion lemmas) and composes head/tail through
    /// `delta_cong_star_trans` + the IH. The transitivity the STAR-lift of the spine
    /// congruence (`delta_cong_star_spine_cong`) consumes at each chain step.
    fn add_list_noconfusion_and_trans(&mut self) -> Result<(), SpecError> {
        // list_is_nil: large-elimination discriminator (nil -> Nat, cons -> Empty),
        // the ListType analogue of opt_is_none. Anchors list_nil_ne_cons.
        self.add_recursive_def(
            r"def list_is_nil (b : Type) (l : ListType b) : Type := ListType.rec b (fun (_ : ListType b) => Type) Nat (fun (_ : b) (_ : ListType b) (_ : Type) => Empty) l",
            "Discriminator: list_is_nil nil = Nat, list_is_nil (cons _ _) = Empty. The ListType analogue \
             of opt_is_none; anchors list_nil_ne_cons. Part of #2859 (Increment H++, delta increment Stage 4).",
        )?;

        // list_nil_ne_cons: nil /= cons (Type-valued no-confusion). Empty
        // discriminator (nil -> Nat inhabited by zero, cons -> Empty) transported
        // along the false nil = cons equation via list_is_nil + Empty.rec. Mirror of
        // option_none_ne_some_type.
        self.add_definition(SpecDefinition {
            name: "list_nil_ne_cons".to_string(),
            type_src: concat!(
                "forall (b : Type) (x : b) (xs : ListType b) (C : Type), ",
                "Eq (ListType b) (ListType.nil b) (ListType.cons b x xs) -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (b : Type) (x : b) (xs : ListType b) (C : Type) ",
                    "(h : Eq (ListType b) (ListType.nil b) (ListType.cons b x xs)) => ",
                    "Empty.rec (fun (_ : Empty) => C) ",
                    "(Eq.substType (ListType b) (list_is_nil b) ",
                    "(ListType.nil b) (ListType.cons b x xs) h Nat.zero)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Type-valued ListType no-confusion: nil /= cons, discharging a Type-valued goal C. Empty ",
                "discriminator (nil -> Nat inhabited by zero, cons -> Empty) transported along the false ",
                "equation via list_is_nil + Empty.rec. Mirror of option_none_ne_some_type. The nil-vs-cons ",
                "disjointness delta_cong_star_list_trans's inversion consumes. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "list_is_nil".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_cons_inj_head: cons x xs = cons y ys -> x = y. ListType.rec head
        // projector (dummy x on nil, head on cons) transported by Eq.cong. Mirror of
        // option_some_inj.
        self.add_definition(SpecDefinition {
            name: "list_cons_inj_head".to_string(),
            type_src: concat!(
                "forall (b : Type) (x : b) (xs : ListType b) (y : b) (ys : ListType b), ",
                "Eq (ListType b) (ListType.cons b x xs) (ListType.cons b y ys) -> Eq b x y"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (b : Type) (x : b) (xs : ListType b) (y : b) (ys : ListType b) ",
                    "(h : Eq (ListType b) (ListType.cons b x xs) (ListType.cons b y ys)) => ",
                    "Eq.cong (ListType b) b ",
                    "(fun (l : ListType b) => ListType.rec b (fun (_ : ListType b) => b) ",
                    "x (fun (hh : b) (t : ListType b) (_ : b) => hh) l) ",
                    "(ListType.cons b x xs) (ListType.cons b y ys) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "ListType.cons head injectivity: cons x xs = cons y ys -> x = y. A ListType.rec head ",
                "projector (dummy x on nil, head on cons) transported via Eq.cong. Mirror of option_some_inj. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ListType.rec".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_cons_inj_tail: cons x xs = cons y ys -> xs = ys. ListType.rec tail
        // projector (dummy xs on nil, tail on cons) transported by Eq.cong.
        self.add_definition(SpecDefinition {
            name: "list_cons_inj_tail".to_string(),
            type_src: concat!(
                "forall (b : Type) (x : b) (xs : ListType b) (y : b) (ys : ListType b), ",
                "Eq (ListType b) (ListType.cons b x xs) (ListType.cons b y ys) -> Eq (ListType b) xs ys"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (b : Type) (x : b) (xs : ListType b) (y : b) (ys : ListType b) ",
                    "(h : Eq (ListType b) (ListType.cons b x xs) (ListType.cons b y ys)) => ",
                    "Eq.cong (ListType b) (ListType b) ",
                    "(fun (l : ListType b) => ListType.rec b (fun (_ : ListType b) => ListType b) ",
                    "xs (fun (hh : b) (t : ListType b) (_ : ListType b) => t) l) ",
                    "(ListType.cons b x xs) (ListType.cons b y ys) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "ListType.cons tail injectivity: cons x xs = cons y ys -> xs = ys. A ListType.rec tail ",
                "projector (dummy xs on nil, tail on cons) transported via Eq.cong. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ListType.rec".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_star_list_trans: transitivity of the pointwise δ*-list relation.
        // delta_cong_star_list.rec on the first chain (motive `forall cs,
        // delta_cong_star_list ys cs -> delta_cong_star_list xs cs`); nil arm = the
        // identity, cons arm inverts the second chain at `cons x' xs0'` (eq-carrying
        // delta_cong_star_list.rec discharged by list_nil_ne_cons / list_cons_inj_*)
        // and composes head/tail via delta_cong_star_trans + the IH.
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_list_trans".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (xs : ListType KExpr) (ys : ListType KExpr) (zs : ListType KExpr), ",
                "delta_cong_star_list env xs ys -> delta_cong_star_list env ys zs -> ",
                "delta_cong_star_list env xs zs"
            )
            .to_string(),
            value_src: Some(delta_cong_star_list_trans_proof()),
            is_axiom: false,
            description: concat!(
                "Transitivity of the pointwise δ*-list relation: delta_cong_star_list xs ys and ys zs give ",
                "delta_cong_star_list xs zs. delta_cong_star_list.rec on the first chain (motive `forall cs, ",
                "delta_cong_star_list ys cs -> delta_cong_star_list xs cs`); nil arm = the identity, cons arm ",
                "INVERTS the second chain at cons x' xs0' (an eq-carrying delta_cong_star_list.rec motive ",
                "discharged by list_nil_ne_cons / list_cons_inj_head / list_cons_inj_tail) and composes head/tail ",
                "via delta_cong_star_trans + the IH. The transitivity the STAR-lift delta_cong_star_spine_cong ",
                "consumes at each chain step. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta ",
                "increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star".to_string(),
                "delta_cong_star_trans".to_string(),
                "delta_cong_star_list".to_string(),
                "delta_cong_star_list.rec".to_string(),
                "delta_cong_star_list.cons".to_string(),
                "list_nil_ne_cons".to_string(),
                "list_cons_inj_head".to_string(),
                "list_cons_inj_tail".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 4 (THE RESIDUAL): `iota_delta_comm` — the ι×δ commutation. From an iota
    /// redex `iota_reduct (red_rec env) e = some e'` and an interior single δ-step
    /// `delta_cong env e v`, the δ-stepped redex `v` fires the SAME rule to a reduct
    /// `d` with `delta_cong_star env e' d` (packaged as `par_delta_sc_witness env e'
    /// v`, the iota arm of `par_delta_sc`). The δ-step is head-disjoint (e's head is
    /// the recursor `recname`, which has no def value via `RecEnvDefEnvDisjoint`), so
    /// it is a spine congruence (`delta_cong_spine_cong`); the major (constructor
    /// `cname`, no def value via `RecEnvCtorNoDefVal`) δ*-steps to `major_v` whose
    /// constructor head + fields are preserved, so `iota_reduct (red_rec env) v` fires
    /// the same `rule` (`iota_reduct_recon_general`); the reduct congruence
    /// `delta_cong_star e' d` is the 3-layer `apply_spine_delta_cong_star` over the
    /// δ*-related extras / fields / prefix segments — the δ mirror of
    /// `par_reduces_c_reduct_cong` + `par_strips_c_iota_app_minimal`.
    fn add_iota_delta_comm(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "iota_delta_comm".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr) (v : KExpr), ",
                "Eq (OptionType KExpr) (iota_reduct (red_rec env) e) (OptionType.some KExpr e') -> ",
                "delta_cong env e v -> ",
                "RecEnvDefEnvDisjoint env -> ",
                "RecEnvCtorNoDefVal env -> ",
                "par_delta_sc_witness env e' v"
            )
            .to_string(),
            value_src: Some(iota_delta_comm_proof()),
            is_axiom: false,
            description: concat!(
                "iota_delta_comm — the ι×δ COMMUTATION (the residual obligation of par_delta_sc's iota arm). From ",
                "iota_reduct (red_rec env) e = some e' and a single interior δ-step delta_cong env e v, the ",
                "δ-stepped redex v fires the SAME rule to a reduct d with delta_cong_star env e' d, packaged as ",
                "par_delta_sc_witness env e' v. Invert e (iota_reduct_some_inv_type); the head δ is impossible (e's ",
                "head recname is a recursor, no def value via RecEnvDefEnvDisjoint + recmeta_some_defval_none), so ",
                "the δ-step is a spine congruence (delta_cong_spine_cong) preserving the recursor head; the major ",
                "(constructor cname, no def value via RecEnvCtorNoDefVal) δ*-steps to major_v with preserved head + ",
                "δ*-related fields, so iota_reduct (red_rec env) v fires the same rule (iota_reduct_recon_general); ",
                "the reduct congruence delta_cong_star e' d is the 3-layer apply_spine_delta_cong_star over the ",
                "δ*-related extras/fields/prefix (δ mirror of par_reduces_c_reduct_cong). DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_reduces_c".to_string(),
                "par_reduces_c.iota".to_string(),
                "iota_reduct".to_string(),
                "iota_reduct_some_inv_type".to_string(),
                "iota_reduct_recon_general".to_string(),
                "delta_cong".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star_list".to_string(),
                "delta_cong_spine_cong".to_string(),
                "delta_cong_preserves_head_const".to_string(),
                "delta_cong_star_spine_cong".to_string(),
                "delta_cong_star_preserves_head_const".to_string(),
                "delta_cong_list_length_eq".to_string(),
                "list_head_some_delta_cong".to_string(),
                "list_drop_delta_cong".to_string(),
                "list_take_delta_cong".to_string(),
                "apply_spine_delta_cong_star".to_string(),
                "recmeta_some_defval_none".to_string(),
                "recenv_ctor_no_defval_cname".to_string(),
                "RecEnvDefEnvDisjoint".to_string(),
                "RecEnvCtorNoDefVal".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "option_some_inj".to_string(),
                "Eq.cong".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// THE TARGET: `par_delta_sc` — the single-step β+ι+ζ/δ STRONG COMMUTATION. From
    /// a single β+ι+ζ parallel step `par_reduces_c (red_rec env) s u` and a single
    /// interior δ-step `delta_cong env s v`, the two join: `u` catches up on δ
    /// (possibly DUPLICATED, hence a `delta_cong_star`) and `v` catches up in ONE
    /// β+ι+ζ step, packaged as `par_delta_sc_witness env u v`. Induction on
    /// `par_reduces_c.rec` (motive generalized over the δ-target `w`), 9 arms
    /// (blueprint `SC`):
    ///   - `refl` (u = s): the δ-step is the join — δ* via `delta_cong_subsumes_star`,
    ///     β+ι via `par_reduces_c.refl`.
    ///   - `app`/`lam`/`pi`: invert the δ-step against the head (`delta_cong_{app,lam,
    ///     pi}_inv`), recurse via the matching IH, re-close δ* with `delta_cong_star_*`
    ///     and β+ι with `par_reduces_c.{app,lam,pi}`. Clean's TYPED `lam`/`pi` carry a
    ///     TYPE slot, so each has TWO δ subcases (δ-in-type / δ-in-body).
    ///   - `beta`: invert app, then (for the function leg) `lam`; δ-in-type is
    ///     trivial (the type is discarded by the contraction), δ-in-body re-substitutes
    ///     via `delta_substStar_body`, δ-in-arg via `delta_substStar_val`.
    ///   - `let_` (ZETA, at the GENUINE `KExpr.let_` node — let promotion, task #28):
    ///     invert via `delta_cong_let_inv`; δ-in-ty is trivial (ζ drops the
    ///     annotation), δ-in-val via `delta_substStar_val`, δ-in-body via
    ///     `delta_substStar_body` (`sc_let_join_{ty,val,body}`).
    ///   - `let_cong` (the TRAILING congruence ctor): invert via `delta_cong_let_inv`,
    ///     recurse via the slot IH, re-close δ* with `delta_cong_star_let` and β+ι+ζ
    ///     with `par_reduces_c.let_cong` (`sc_cong_join_let_{ty,val,body}`).
    ///   - `forall_`: rides the `pi` reducible alias (identical arm body, defeq).
    ///   - `iota`: the landed `iota_delta_comm` (carrying the `RecEnvDefEnvDisjoint` /
    ///     `RecEnvCtorNoDefVal` interfaces as the bound hypotheses `disj` / `ctorNoDef`).
    /// Carries `DefEnvClosed (red_def env)` / `DefEnvLiftClosed (red_def env)` (consumed
    /// by the δ-subst tower) and the two `RecEnv` disjointness interfaces — all BOUND
    /// HYPOTHESES, NOT registered axioms. Discharges the SOLE bound hypothesis of
    /// `par_reduces_cd_star_diamond_of_sc`, making the 3-way β+ι+δ Church-Rosser
    /// unconditional. Blueprint `SC` (HindleyRosen_delta_VERIFIED.lean ~line 1211).
    fn add_par_delta_sc(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_delta_sc".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (closed : DefEnvClosed (red_def env)) ",
                "(liftclosed : DefEnvLiftClosed (red_def env)) (disj : RecEnvDefEnvDisjoint env) ",
                "(ctorNoDef : RecEnvCtorNoDefVal env) (s : KExpr) (u : KExpr) (v : KExpr), ",
                "par_reduces_c (red_rec env) s u -> delta_cong env s v -> ",
                "par_delta_sc_witness env u v"
            )
            .to_string(),
            value_src: Some(par_delta_sc_proof()),
            is_axiom: false,
            description: concat!(
                "par_delta_sc — THE single-step β+ι/δ STRONG COMMUTATION (blueprint SC). A single β+ι parallel ",
                "step par_reduces_c (red_rec env) s u and a single interior δ-step delta_cong env s v join: u ",
                "catches up on δ (possibly DUPLICATED, a delta_cong_star) and v catches up in ONE β+ι step, ",
                "packaged as par_delta_sc_witness env u v. Induction on par_reduces_c.rec (motive over the δ-target ",
                "w): refl = the δ-step is the join; app/lam/pi invert via delta_cong_{app,lam,pi}_inv + recurse + ",
                "re-close (delta_cong_star_* / par_reduces_c.{app,lam,pi}) with the extra δ-in-type subcase of the ",
                "typed binders; beta inverts app then lam, δ-in-type trivial / δ-in-body via ",
                "delta_substStar_body / δ-in-arg via delta_substStar_val; the GENUINE let_ (zeta) arm inverts via ",
                "delta_cong_let_inv (δ-in-ty trivial — zeta drops the annotation; δ-in-val/body re-substitute via ",
                "sc_let_join_{ty,val,body}); the trailing let_cong arm joins per-slot via ",
                "sc_cong_join_let_{ty,val,body}; forall_ rides the pi alias; iota = the ",
                "landed iota_delta_comm. Carries DefEnvClosed / DefEnvLiftClosed (red_def env) + ",
                "RecEnvDefEnvDisjoint / RecEnvCtorNoDefVal as BOUND HYPOTHESES (not axioms). Discharges the sole ",
                "bound hypothesis of par_reduces_cd_star_diamond_of_sc. DerivedProved, zero axiom_deps. Part of ",
                "#2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c.rec".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_reduces_c.app".to_string(),
                "par_reduces_c.lam".to_string(),
                "par_reduces_c.pi".to_string(),
                "par_reduces_c.beta".to_string(),
                "par_reduces_c.let_".to_string(),
                "par_reduces_c.let_cong".to_string(),
                "iota_step".to_string(),
                "delta_cong".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_subsumes_star".to_string(),
                "delta_cong_app_inv".to_string(),
                "delta_cong_lam_inv".to_string(),
                "delta_cong_pi_inv".to_string(),
                "delta_cong_let_inv".to_string(),
                "delta_cong_proj_inv".to_string(),
                "delta_cong_app_lam_inv".to_string(),
                "sc_beta_join_type".to_string(),
                "sc_beta_join_body".to_string(),
                "sc_beta_join_arg".to_string(),
                "sc_let_join_ty".to_string(),
                "sc_let_join_val".to_string(),
                "sc_let_join_body".to_string(),
                "sc_cong_join_app_left".to_string(),
                "sc_cong_join_app_right".to_string(),
                "sc_cong_join_lam_left".to_string(),
                "sc_cong_join_lam_right".to_string(),
                "sc_cong_join_pi_left".to_string(),
                "sc_cong_join_pi_right".to_string(),
                "sc_cong_join_let_ty".to_string(),
                "sc_cong_join_let_val".to_string(),
                "sc_cong_join_let_body".to_string(),
                "sc_cong_join_proj".to_string(),
                "iota_delta_comm".to_string(),
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.intro".to_string(),
                "par_delta_sc_witness.rec".to_string(),
                "instantiate".to_string(),
                "DefEnvClosed".to_string(),
                "DefEnvLiftClosed".to_string(),
                "RecEnvDefEnvDisjoint".to_string(),
                "RecEnvCtorNoDefVal".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// THE UNCONDITIONAL 3-WAY (β+ι+δ) CHURCH-ROSSER: `par_reduces_cd_star_diamond`.
    /// Discharges the SOLE bound hypothesis `SC` of `par_reduces_cd_star_diamond_of_sc`
    /// with the proven single-step strong commutation `par_delta_sc env i5 i6 i7 i8`,
    /// leaving only the standard faithful `RecEnv` / `DefEnv` interfaces as bound
    /// hypotheses (NOT axioms) — exactly the posture of every other lemma in the
    /// Hindley-Rosen assembly. COMPLETES the delta increment: the confluence of the
    /// union reduction `par_reduces_cd_star` (β+ι atomic steps ∪ δ congruence steps) is
    /// now a genuine 0-axiom theorem.
    fn add_par_reduces_cd_star_diamond(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_diamond".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) ",
                "(i1 : RecEnvReductNotRedex (red_rec env)) (i2 : RecEnvCtorNoRecMeta (red_rec env)) ",
                "(i3 : RecEnvClosed (red_rec env)) (i4 : RecEnvLiftClosed (red_rec env)) ",
                "(i5 : DefEnvClosed (red_def env)) (i6 : DefEnvLiftClosed (red_def env)) ",
                "(i7 : RecEnvDefEnvDisjoint env) (i8 : RecEnvCtorNoDefVal env) ",
                "(e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_cd_star env e e1 -> par_reduces_cd_star env e e2 -> ",
                "par_strips_witness_cd_star env e1 e2"
            )
            .to_string(),
            value_src: Some(par_reduces_cd_star_diamond_proof()),
            is_axiom: false,
            description: concat!(
                "par_reduces_cd_star_diamond — the UNCONDITIONAL 3-way (β+ι+δ) Church-Rosser of ",
                "par_reduces_cd_star. Discharges the sole bound hypothesis SC of ",
                "par_reduces_cd_star_diamond_of_sc with the proven single-step strong commutation par_delta_sc, ",
                "leaving only the standard faithful RecEnv / DefEnv interfaces as bound hypotheses (NOT axioms). ",
                "COMPLETES the delta increment: the confluence of the union reduction par_reduces_cd_star is now a ",
                "genuine 0-axiom theorem. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta ",
                "increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star_diamond_of_sc".to_string(),
                "par_delta_sc".to_string(),
                "par_strips_witness_cd_star".to_string(),
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
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick C0: `recmeta_some_defval_none` — the disjointness plumbing the ι×δ
    /// assembly needs to turn an iota redex's recursor-metadata witness into the
    /// def-value-none guard the spine congruences (`delta_cong_spine_cong` /
    /// `delta_cong_preserves_head_const`) consume. From `RecEnvDefEnvDisjoint env`
    /// and `recmeta_for (red_rec env) nm = some meta` (the head IS a recursor),
    /// conclude `defval_for (red_def env) nm = none` (the head is NOT a definition):
    /// the contrapositive of `recenv_defenv_disjoint_recmeta`, by case-analysis on
    /// `defval_for (red_def env) nm` (none arm = the carried eq; some arm = absurd,
    /// the disjointness fact forces `recmeta = none`, contradicting `recmeta = some`).
    fn add_iota_delta_disjoint_plumbing(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "recmeta_some_defval_none".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (nm : Name) (meta : RecMeta), ",
                "RecEnvDefEnvDisjoint env -> ",
                "Eq (OptionType RecMeta) (recmeta_for (red_rec env) nm) (OptionType.some RecMeta meta) -> ",
                "Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (nm : Name) (meta : RecMeta) (w : RecEnvDefEnvDisjoint env) ",
                    "(hm : Eq (OptionType RecMeta) (recmeta_for (red_rec env) nm) (OptionType.some RecMeta meta)) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => Eq (OptionType KExpr) (defval_for (red_def env) nm) o -> Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr)) ",
                    // none arm: the carried equation is the goal.
                    "(fun (heq : Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr)) => heq) ",
                    // some arm: recenv_defenv_disjoint_recmeta forces recmeta = none, contradicting hm.
                    "(fun (val : KExpr) (heq : Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.some KExpr val)) => ",
                    "option_none_ne_some RecMeta meta (Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr)) ",
                    "(Eq.trans (OptionType RecMeta) (OptionType.none RecMeta) (recmeta_for (red_rec env) nm) (OptionType.some RecMeta meta) ",
                    "(Eq.symm (OptionType RecMeta) (recmeta_for (red_rec env) nm) (OptionType.none RecMeta) ",
                    "(recenv_defenv_disjoint_recmeta env nm val w heq)) ",
                    "hm)) ",
                    "(defval_for (red_def env) nm) ",
                    "(Eq.refl (OptionType KExpr) (defval_for (red_def env) nm))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "recmeta_some_defval_none — the disjointness plumbing the ι×δ commutation consumes: given ",
                "RecEnvDefEnvDisjoint env and recmeta_for (red_rec env) nm = some meta (the head is a recursor), ",
                "defval_for (red_def env) nm = none (the head is not a definition). The contrapositive of ",
                "recenv_defenv_disjoint_recmeta, by OptionType.rec on defval_for with an equation-carrying ",
                "motive (none arm = the carried eq; some arm = absurd via the disjointness fact + ",
                "option_none_ne_some). The def-value-none guard the δ spine congruences need at a recursor ",
                "redex head. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment ",
                "Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvDefEnvDisjoint".to_string(),
                "recenv_defenv_disjoint_recmeta".to_string(),
                "recmeta_for".to_string(),
                "defval_for".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "OptionType.rec".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick B: the head/spine reflection lemmas for a single δ-step against a
    /// recursor-redex spine. `delta_reduct_eq_none_of_defval_none` (a δ-redex's head
    /// const has no def value ⟹ no δ reduct — the `here`-discharge primitive),
    /// `delta_cong_list_length_eq` (a spine δ* preserves arg count),
    /// `delta_cong_preserves_head_const` (a non-head δ-step preserves the spine head
    /// const), and `delta_cong_spine_cong` (a non-head δ-step on a const-headed term
    /// induces a pointwise spine-args δ*). Mirror of `par_reduces_c_list_length_eq` /
    /// `par_reduces_c_preserves_head_const` / `par_reduces_c_spine_cong`, with the
    /// `here` arm discharged by the def-value-none guard (the head is a recursor
    /// const, hence carries no def value, via the `RecEnvDefEnvDisjoint` interface).
    fn add_delta_cong_spine_cong(&mut self) -> Result<(), SpecError> {
        // delta_reduct_eq_none_of_defval_none: if the head const of e has NO def
        // value (defval_for denv nm = none) then delta_reduct denv e = none. Rewrites
        // the head-const lookup (some nm) then the def-value lookup (none) through the
        // two opt_bind layers definitionally. The δ analogue of the head-none reduct
        // collapse; the `here`-arm discharge primitive for the spine congruences.
        self.add_definition(SpecDefinition {
            name: "delta_reduct_eq_none_of_defval_none".to_string(),
            type_src: concat!(
                "forall (denv : DefEnv) (e : KExpr) (nm : Name), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) -> ",
                "Eq (OptionType KExpr) (defval_for denv nm) (OptionType.none KExpr) -> ",
                "Eq (OptionType KExpr) (delta_reduct denv e) (OptionType.none KExpr)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (denv : DefEnv) (e : KExpr) (nm : Name) ",
                    "(gh : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm)) ",
                    "(gd : Eq (OptionType KExpr) (defval_for denv nm) (OptionType.none KExpr)) => ",
                    "Eq.trans (OptionType KExpr) ",
                    "(delta_reduct denv e) ",
                    "(opt_bind KExpr KExpr (defval_for denv nm) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val))) ",
                    "(OptionType.none KExpr) ",
                    // h1: delta_reduct denv e = opt_bind KExpr KExpr (defval_for denv nm) SMALL (rewrite head)
                    "(Eq.cong (OptionType Name) (OptionType KExpr) ",
                    "(fun (O : OptionType Name) => opt_bind Name KExpr O (fun (dname : Name) => opt_bind KExpr KExpr (defval_for denv dname) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val)))) ",
                    "(kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) gh) ",
                    // h2: opt_bind KExpr KExpr (defval_for denv nm) SMALL = none (rewrite def-value)
                    "(Eq.cong (OptionType KExpr) (OptionType KExpr) ",
                    "(fun (O : OptionType KExpr) => opt_bind KExpr KExpr O (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val))) ",
                    "(defval_for denv nm) (OptionType.none KExpr) gd)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "If the head const of e has no def value (defval_for denv nm = none, under the head-const guard ",
                "kexpr_const_name (kapp_fn e) = some nm) then delta_reduct denv e = none. Two opt_bind rewrites ",
                "(head-const lookup to some nm, then def-value lookup to none) closed definitionally. The ",
                "`here`-arm discharge primitive for the δ spine congruences. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_reduct".to_string(),
                "defval_for".to_string(),
                "opt_bind".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_args".to_string(),
                "apply_spine".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_list_length_eq: pointwise δ* preserves list length. Mirror of
        // par_reduces_c_list_length_eq.
        self.add_definition(SpecDefinition {
            name: "delta_cong_list_length_eq".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "delta_cong_star_list env xs xs' -> Eq Nat (list_length xs) (list_length xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(h : delta_cong_star_list env xs xs') => ",
                    "delta_cong_star_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_h : delta_cong_star_list env a a') => ",
                    "Eq Nat (list_length a) (list_length a')) ",
                    "(Eq.refl Nat (list_length (ListType.nil KExpr))) ",
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(_hx : delta_cong_star env x x') (_hxs : delta_cong_star_list env xs0 xs0') ",
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
                "Pointwise δ* preserves list length: delta_cong_star_list xs xs' gives list_length xs = ",
                "list_length xs'. delta_cong_star_list.rec; nil = refl, cons = succ-cong on the IH through ",
                "list_length_cons on both sides. The spine-length-stability fact. Mirror of ",
                "par_reduces_c_list_length_eq. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, ",
                "delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star".to_string(),
                "delta_cong_star_list".to_string(),
                "delta_cong_star_list.rec".to_string(),
                "list_length".to_string(),
                "list_length_cons".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_preserves_head_const: under the head-const guard + the
        // def-value-none guard (the head is not a def-const), a single δ-step
        // preserves the spine head const. delta_cong.rec; here discharged (no δ
        // reduct), app_f lifts the head IH, app_a leaves the head fixed, the binder
        // arms and the trailing let_t/let_v/let_b arms discharged (binder/let head ⟹ const_name none). Mirror of
        // par_reduces_c_preserves_head_const (NR form).
        self.add_definition(SpecDefinition {
            name: "delta_cong_preserves_head_const".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (f : KExpr) (f' : KExpr) (nm : Name), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> ",
                "Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr) -> ",
                "delta_cong env f f' -> ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn f')) (OptionType.some Name nm)"
            )
            .to_string(),
            value_src: Some(delta_cong_preserves_head_const_proof()),
            is_axiom: false,
            description: concat!(
                "Under the head-const guard (kexpr_const_name (kapp_fn f) = some nm) and the def-value-none ",
                "guard (defval_for (red_def env) nm = none, i.e. the head is not a def-const), a single δ-step ",
                "delta_cong f f' preserves the spine head const: kexpr_const_name (kapp_fn f') = some nm. ",
                "delta_cong.rec; here discharged via delta_reduct_eq_none_of_defval_none, app_f lifts the head ",
                "IH through kapp_fn_app, app_a leaves the head fixed, the lam/pi and trailing let_t/let_v/let_b arms discharged (binder/let head ⟹ ",
                "const_name none). Mirror of par_reduces_c_preserves_head_const. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.rec".to_string(),
                "delta_step".to_string(),
                "delta_reduct_eq_none_of_defval_none".to_string(),
                "defval_for".to_string(),
                "red_def".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.subst".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_spine_cong: under the head-const guard + the def-value-none
        // guard, a single δ-step is a spine congruence: kapp_args f δ*-list-reduce to
        // kapp_args f'. delta_cong.rec with the delta_cong_star_list motive carrying
        // both guards; here discharged (no δ reduct), app_f via kapp_args_delta_cong
        // on the head IH (+ refl on the fixed arg), app_a via kapp_args_delta_cong on
        // the refl-list head (+ the arg δ-step subsumed to δ*), the lam/pi arms
        // discharged. Mirror of par_reduces_c_spine_cong.
        self.add_definition(SpecDefinition {
            name: "delta_cong_spine_cong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (f : KExpr) (f' : KExpr) (nm : Name), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> ",
                "Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr) -> ",
                "delta_cong env f f' -> ",
                "delta_cong_star_list env (kapp_args f) (kapp_args f')"
            )
            .to_string(),
            value_src: Some(delta_cong_spine_cong_proof()),
            is_axiom: false,
            description: concat!(
                "Under the head-const guard (kexpr_const_name (kapp_fn f) = some nm) and the def-value-none ",
                "guard (defval_for (red_def env) nm = none), a single δ-step delta_cong f f' is a spine ",
                "congruence: delta_cong_star_list (kapp_args f) (kapp_args f'). delta_cong.rec with the ",
                "delta_cong_star_list motive carrying both guards; here discharged via ",
                "delta_reduct_eq_none_of_defval_none; app_f via kapp_args_delta_cong on the head IH + refl on the ",
                "fixed arg; app_a via kapp_args_delta_cong on the refl-list head + the arg δ-step subsumed to δ*; ",
                "the lam/pi and trailing let_t/let_v/let_b arms discharged (binder/let head ⟹ const_name none). Mirror of par_reduces_c_spine_cong. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.rec".to_string(),
                "delta_step".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_subsumes_star".to_string(),
                "delta_cong_star_list".to_string(),
                "delta_cong_star_list_refl".to_string(),
                "kapp_args_delta_cong".to_string(),
                "delta_reduct_eq_none_of_defval_none".to_string(),
                "defval_for".to_string(),
                "red_def".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "kapp_args".to_string(),
                "option_none_ne_some_type".to_string(),
                "Eq.subst".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick A: the pointwise δ*-list relation `delta_cong_star_list` and the spine
    /// congruences (`apply_spine_delta_cong_star`, `list_{tail,drop,take}_delta_cong`,
    /// `kapp_args_delta_cong`, `delta_cong_star_list_append`, `delta_cong_star_list_refl`).
    /// Verbatim δ* mirrors of the `par_reduces_c_list` spine machinery (par_reduces_c.rs).
    fn add_delta_cong_star_list_infra(&mut self) -> Result<(), SpecError> {
        // delta_cong_star_list env: pointwise δ* reduction of KExpr lists (nil to
        // nil; cons reduces head [delta_cong_star] and tail [recursively]). The δ
        // analogue of par_reduces_c_list. Each element independently δ*-steps, so the
        // unchanged spine segments of an iota redex relate by delta_cong_star_list_refl
        // and the single changed arg by its delta_cong_star step.
        self.add_inductive(
            r"inductive delta_cong_star_list (env : RedEnv) : ListType KExpr → ListType KExpr → Type
| nil : delta_cong_star_list env (ListType.nil KExpr) (ListType.nil KExpr)
| cons : forall (x : KExpr) (x' : KExpr) (xs : ListType KExpr) (xs' : ListType KExpr), delta_cong_star env x x' → delta_cong_star_list env xs xs' → delta_cong_star_list env (ListType.cons KExpr x xs) (ListType.cons KExpr x' xs')",
            "delta_cong_star_list env xs xs' — pointwise δ* reduction of KExpr lists (nil to nil; cons \
             reduces head via delta_cong_star and tail recursively). The δ analogue of par_reduces_c_list: \
             the spine-argument relation the (iota,δ) commutation needs (the unchanged spine segments \
             relate by refl, the single δ-changed arg by its delta_cong_star step). Part of #2859 \
             (Increment H++, delta increment Stage 4).",
        )?;

        // delta_cong_star_list_refl: pointwise reflexivity — every list δ*-reduces to
        // itself. ListType.rec on xs, delta_cong_star.refl at each element. The refl
        // base for the unchanged prefix/extra segments of a redex spine.
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_list_refl".to_string(),
            type_src:
                "forall (env : RedEnv) (xs : ListType KExpr), delta_cong_star_list env xs xs"
                    .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (xs : ListType KExpr) => ",
                    "ListType.rec KExpr ",
                    "(fun (a : ListType KExpr) => delta_cong_star_list env a a) ",
                    "(delta_cong_star_list.nil env) ",
                    "(fun (x : KExpr) (rest : ListType KExpr) (ih : delta_cong_star_list env rest rest) => ",
                    "delta_cong_star_list.cons env x x rest rest (delta_cong_star.refl env x) ih) ",
                    "xs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Reflexivity of pointwise δ* list reduction: delta_cong_star_list env xs xs. ListType.rec ",
                "on xs with delta_cong_star.refl at each element. The refl base for unchanged spine segments. ",
                "Mirror of par_reduces_c_list_refl. DerivedProved, zero axiom_deps. Part of #2859 (Increment ",
                "H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star_list".to_string(),
                "delta_cong_star_list.nil".to_string(),
                "delta_cong_star_list.cons".to_string(),
                "ListType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // apply_spine_delta_cong_star: apply_spine is a δ*-congruence in both its
        // argument list and its head. delta_cong_star_list.rec with the head
        // universalized; nil via apply_spine_nil, cons via delta_cong_star_app + the
        // tail IH + apply_spine_cons. Mirror of apply_spine_par_c.
        self.add_definition(SpecDefinition {
            name: "apply_spine_delta_cong_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (head : KExpr) (head' : KExpr), ",
                "delta_cong_star_list env xs xs' -> delta_cong_star env head head' -> ",
                "delta_cong_star env (apply_spine xs head) (apply_spine xs' head')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (head : KExpr) (head' : KExpr) ",
                    "(hl : delta_cong_star_list env xs xs') (hh : delta_cong_star env head head') => ",
                    "delta_cong_star_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_ : delta_cong_star_list env a a') => ",
                    "forall (h : KExpr) (h' : KExpr), delta_cong_star env h h' -> ",
                    "delta_cong_star env (apply_spine a h) (apply_spine a' h')) ",
                    // nil arm
                    "(fun (h : KExpr) (h' : KExpr) (hp : delta_cong_star env h h') => ",
                    "Eq.substType KExpr ",
                    "(fun (Z : KExpr) => delta_cong_star env (apply_spine (ListType.nil KExpr) h) Z) ",
                    "h' (apply_spine (ListType.nil KExpr) h') ",
                    "(Eq.symm KExpr (apply_spine (ListType.nil KExpr) h') h' (apply_spine_nil h')) ",
                    "(Eq.substType KExpr ",
                    "(fun (Z : KExpr) => delta_cong_star env Z h') ",
                    "h (apply_spine (ListType.nil KExpr) h) ",
                    "(Eq.symm KExpr (apply_spine (ListType.nil KExpr) h) h (apply_spine_nil h)) ",
                    "hp)) ",
                    // cons arm
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : delta_cong_star env x x') (hxs : delta_cong_star_list env xs0 xs0') ",
                    "(ihxs : forall (h : KExpr) (h' : KExpr), delta_cong_star env h h' -> ",
                    "delta_cong_star env (apply_spine xs0 h) (apply_spine xs0' h')) => ",
                    "fun (h : KExpr) (h' : KExpr) (hp : delta_cong_star env h h') => ",
                    "Eq.substType KExpr ",
                    "(fun (Z : KExpr) => delta_cong_star env (apply_spine (ListType.cons KExpr x xs0) h) Z) ",
                    "(apply_spine xs0' (KExpr.app h' x')) (apply_spine (ListType.cons KExpr x' xs0') h') ",
                    "(Eq.symm KExpr (apply_spine (ListType.cons KExpr x' xs0') h') (apply_spine xs0' (KExpr.app h' x')) ",
                    "(apply_spine_cons x' xs0' h')) ",
                    "(Eq.substType KExpr ",
                    "(fun (Z : KExpr) => delta_cong_star env Z (apply_spine xs0' (KExpr.app h' x'))) ",
                    "(apply_spine xs0 (KExpr.app h x)) (apply_spine (ListType.cons KExpr x xs0) h) ",
                    "(Eq.symm KExpr (apply_spine (ListType.cons KExpr x xs0) h) (apply_spine xs0 (KExpr.app h x)) ",
                    "(apply_spine_cons x xs0 h)) ",
                    "(ihxs (KExpr.app h x) (KExpr.app h' x') (delta_cong_star_app env h h' x x' hp hx)))) ",
                    "xs xs' hl head head' hh"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "apply_spine is a δ*-congruence: pointwise-δ*-reducing args (delta_cong_star_list) and a ",
                "δ*-reducing head give delta_cong_star on the spine applications. delta_cong_star_list.rec with ",
                "the head universalized; nil via apply_spine_nil, cons via delta_cong_star_app + the tail IH + ",
                "apply_spine_cons. Mirror of apply_spine_par_c. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star".to_string(),
                "delta_cong_star_app".to_string(),
                "delta_cong_star_list".to_string(),
                "delta_cong_star_list.rec".to_string(),
                "apply_spine".to_string(),
                "apply_spine_nil".to_string(),
                "apply_spine_cons".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_star_list_append: pointwise δ* respects list_append.
        // delta_cong_star_list.rec on the first list (motive append-ing the fixed
        // second), nil via list_append_nil, cons via delta_cong_star_list.cons +
        // list_append_cons. Mirror of par_reduces_c_list_append.
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_list_append".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (ys : ListType KExpr) (ys' : ListType KExpr), ",
                "delta_cong_star_list env xs xs' -> delta_cong_star_list env ys ys' -> ",
                "delta_cong_star_list env (list_append xs ys) (list_append xs' ys')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (xs : ListType KExpr) (xs' : ListType KExpr) (ys : ListType KExpr) (ys' : ListType KExpr) ",
                    "(hxs : delta_cong_star_list env xs xs') (hys : delta_cong_star_list env ys ys') => ",
                    "delta_cong_star_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_ : delta_cong_star_list env a a') => ",
                    "delta_cong_star_list env (list_append a ys) (list_append a' ys')) ",
                    // nil arm
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env (list_append (ListType.nil KExpr) ys) Z) ",
                    "ys' (list_append (ListType.nil KExpr) ys') ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.nil KExpr) ys') ys' (list_append_nil ys')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env Z ys') ",
                    "ys (list_append (ListType.nil KExpr) ys) ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.nil KExpr) ys) ys (list_append_nil ys)) ",
                    "hys)) ",
                    // cons arm
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : delta_cong_star env x x') (hxs0 : delta_cong_star_list env xs0 xs0') ",
                    "(ih : delta_cong_star_list env (list_append xs0 ys) (list_append xs0' ys')) => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env (list_append (ListType.cons KExpr x xs0) ys) Z) ",
                    "(ListType.cons KExpr x' (list_append xs0' ys')) (list_append (ListType.cons KExpr x' xs0') ys') ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.cons KExpr x' xs0') ys') (ListType.cons KExpr x' (list_append xs0' ys')) ",
                    "(list_append_cons x' xs0' ys')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env Z (ListType.cons KExpr x' (list_append xs0' ys'))) ",
                    "(ListType.cons KExpr x (list_append xs0 ys)) (list_append (ListType.cons KExpr x xs0) ys) ",
                    "(Eq.symm (ListType KExpr) (list_append (ListType.cons KExpr x xs0) ys) (ListType.cons KExpr x (list_append xs0 ys)) ",
                    "(list_append_cons x xs0 ys)) ",
                    "(delta_cong_star_list.cons env x x' (list_append xs0 ys) (list_append xs0' ys') hx ih))) ",
                    "xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise δ* respects list_append: delta_cong_star_list xs xs' and ys ys' give ",
                "delta_cong_star_list (list_append xs ys) (list_append xs' ys'). delta_cong_star_list.rec on ",
                "the first list; nil via list_append_nil, cons via delta_cong_star_list.cons + list_append_cons. ",
                "Mirror of par_reduces_c_list_append. DerivedProved, zero axiom_deps. Part of #2859 (Increment ",
                "H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star".to_string(),
                "delta_cong_star_list".to_string(),
                "delta_cong_star_list.rec".to_string(),
                "delta_cong_star_list.cons".to_string(),
                "list_append".to_string(),
                "list_append_nil".to_string(),
                "list_append_cons".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_tail_delta_cong: pointwise δ* respects list_tail. delta_cong_star_list.rec;
        // nil via list_tail_nil, cons exposes the tail field. Mirror of list_tail_par_c.
        self.add_definition(SpecDefinition {
            name: "list_tail_delta_cong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "delta_cong_star_list env xs xs' -> delta_cong_star_list env (list_tail xs) (list_tail xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(hxs : delta_cong_star_list env xs xs') => ",
                    "delta_cong_star_list.rec env ",
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (_ : delta_cong_star_list env a a') => ",
                    "delta_cong_star_list env (list_tail a) (list_tail a')) ",
                    // nil arm
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env (list_tail (ListType.nil KExpr)) Z) ",
                    "(ListType.nil KExpr) (list_tail (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.nil KExpr)) (ListType.nil KExpr) list_tail_nil) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env Z (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) (list_tail (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.nil KExpr)) (ListType.nil KExpr) list_tail_nil) ",
                    "(delta_cong_star_list.nil env))) ",
                    // cons arm
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : delta_cong_star env x x') (hxs0 : delta_cong_star_list env xs0 xs0') ",
                    "(_ih : delta_cong_star_list env (list_tail xs0) (list_tail xs0')) => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env (list_tail (ListType.cons KExpr x xs0)) Z) ",
                    "xs0' (list_tail (ListType.cons KExpr x' xs0')) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.cons KExpr x' xs0')) xs0' (list_tail_cons x' xs0')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env Z xs0') ",
                    "xs0 (list_tail (ListType.cons KExpr x xs0)) ",
                    "(Eq.symm (ListType KExpr) (list_tail (ListType.cons KExpr x xs0)) xs0 (list_tail_cons x xs0)) ",
                    "hxs0)) ",
                    "xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise δ* respects list_tail. delta_cong_star_list.rec; nil via list_tail_nil, cons ",
                "exposes the tail field. Mirror of list_tail_par_c. DerivedProved, zero axiom_deps. Part of ",
                "#2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star".to_string(),
                "delta_cong_star_list".to_string(),
                "delta_cong_star_list.rec".to_string(),
                "delta_cong_star_list.nil".to_string(),
                "list_tail".to_string(),
                "list_tail_nil".to_string(),
                "list_tail_cons".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_drop_delta_cong: pointwise δ* respects list_drop. Nat.rec on the offset
        // (motive universalizing the two lists); zero via list_drop_zero, succ via
        // list_drop_succ + list_tail_delta_cong + the IH. Mirror of list_drop_par_c.
        self.add_definition(SpecDefinition {
            name: "list_drop_delta_cong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "delta_cong_star_list env xs xs' -> delta_cong_star_list env (list_drop n xs) (list_drop n xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(hxs : delta_cong_star_list env xs xs') => ",
                    "Nat.rec ",
                    "(fun (n0 : Nat) => forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "delta_cong_star_list env a a' -> delta_cong_star_list env (list_drop n0 a) (list_drop n0 a')) ",
                    // zero arm
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (ha : delta_cong_star_list env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env (list_drop Nat.zero a) Z) ",
                    "a' (list_drop Nat.zero a') ",
                    "(Eq.symm (ListType KExpr) (list_drop Nat.zero a') a' (list_drop_zero a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env Z a') ",
                    "a (list_drop Nat.zero a) ",
                    "(Eq.symm (ListType KExpr) (list_drop Nat.zero a) a (list_drop_zero a)) ",
                    "ha)) ",
                    // succ arm
                    "(fun (m : Nat) (ihm : forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "delta_cong_star_list env a a' -> delta_cong_star_list env (list_drop m a) (list_drop m a')) => ",
                    "fun (a : ListType KExpr) (a' : ListType KExpr) (ha : delta_cong_star_list env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env (list_drop (Nat.succ m) a) Z) ",
                    "(list_drop m (list_tail a')) (list_drop (Nat.succ m) a') ",
                    "(Eq.symm (ListType KExpr) (list_drop (Nat.succ m) a') (list_drop m (list_tail a')) (list_drop_succ m a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env Z (list_drop m (list_tail a'))) ",
                    "(list_drop m (list_tail a)) (list_drop (Nat.succ m) a) ",
                    "(Eq.symm (ListType KExpr) (list_drop (Nat.succ m) a) (list_drop m (list_tail a)) (list_drop_succ m a)) ",
                    "(ihm (list_tail a) (list_tail a') (list_tail_delta_cong env a a' ha)))) ",
                    "n xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise δ* respects list_drop. Nat.rec on the offset (motive universalizing the two lists); ",
                "zero via list_drop_zero, succ via list_drop_succ + list_tail_delta_cong + the IH. The ",
                "extras/prefix segments of the iota reduct are list_drop/list_take. Mirror of list_drop_par_c. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star_list".to_string(),
                "list_drop".to_string(),
                "list_tail".to_string(),
                "list_tail_delta_cong".to_string(),
                "list_drop_zero".to_string(),
                "list_drop_succ".to_string(),
                "Nat.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_take_delta_cong: pointwise δ* respects list_take. Nat.rec on the offset;
        // succ arm case-splits the delta_cong_star_list derivation and uses the outer
        // Nat IH on the cons tail (no inner induction). Mirror of list_take_par_c.
        self.add_definition(SpecDefinition {
            name: "list_take_delta_cong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr), ",
                "delta_cong_star_list env xs xs' -> delta_cong_star_list env (list_take n xs) (list_take n xs')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (n : Nat) (xs : ListType KExpr) (xs' : ListType KExpr) ",
                    "(hxs : delta_cong_star_list env xs xs') => ",
                    "Nat.rec ",
                    "(fun (n0 : Nat) => forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "delta_cong_star_list env a a' -> delta_cong_star_list env (list_take n0 a) (list_take n0 a')) ",
                    // zero arm
                    "(fun (a : ListType KExpr) (a' : ListType KExpr) (ha : delta_cong_star_list env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env (list_take Nat.zero a) Z) ",
                    "(ListType.nil KExpr) (list_take Nat.zero a') ",
                    "(Eq.symm (ListType KExpr) (list_take Nat.zero a') (ListType.nil KExpr) (list_take_zero a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env Z (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) (list_take Nat.zero a) ",
                    "(Eq.symm (ListType KExpr) (list_take Nat.zero a) (ListType.nil KExpr) (list_take_zero a)) ",
                    "(delta_cong_star_list.nil env))) ",
                    // succ arm
                    "(fun (m : Nat) (ihm : forall (a : ListType KExpr) (a' : ListType KExpr), ",
                    "delta_cong_star_list env a a' -> delta_cong_star_list env (list_take m a) (list_take m a')) => ",
                    "fun (a : ListType KExpr) (a' : ListType KExpr) (h : delta_cong_star_list env a a') => ",
                    "delta_cong_star_list.rec env ",
                    "(fun (b : ListType KExpr) (b' : ListType KExpr) (_ : delta_cong_star_list env b b') => ",
                    "delta_cong_star_list env (list_take (Nat.succ m) b) (list_take (Nat.succ m) b')) ",
                    // inner nil
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env (list_take (Nat.succ m) (ListType.nil KExpr)) Z) ",
                    "(ListType.nil KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) (ListType.nil KExpr) (list_take_succ_nil m)) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env Z (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.nil KExpr)) (ListType.nil KExpr) (list_take_succ_nil m)) ",
                    "(delta_cong_star_list.nil env))) ",
                    // inner cons
                    "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
                    "(hx : delta_cong_star env x x') (hxs0 : delta_cong_star_list env xs0 xs0') ",
                    "(_ih2 : delta_cong_star_list env (list_take (Nat.succ m) xs0) (list_take (Nat.succ m) xs0')) => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env (list_take (Nat.succ m) (ListType.cons KExpr x xs0)) Z) ",
                    "(ListType.cons KExpr x' (list_take m xs0')) (list_take (Nat.succ m) (ListType.cons KExpr x' xs0')) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.cons KExpr x' xs0')) (ListType.cons KExpr x' (list_take m xs0')) (list_take_succ_cons m x' xs0')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env Z (ListType.cons KExpr x' (list_take m xs0'))) ",
                    "(ListType.cons KExpr x (list_take m xs0)) (list_take (Nat.succ m) (ListType.cons KExpr x xs0)) ",
                    "(Eq.symm (ListType KExpr) (list_take (Nat.succ m) (ListType.cons KExpr x xs0)) (ListType.cons KExpr x (list_take m xs0)) (list_take_succ_cons m x xs0)) ",
                    "(delta_cong_star_list.cons env x x' (list_take m xs0) (list_take m xs0') hx (ihm xs0 xs0' hxs0)))) ",
                    "a a' h) ",
                    "n xs xs' hxs"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pointwise δ* respects list_take. Nat.rec on the offset; succ arm case-splits the derivation ",
                "(delta_cong_star_list.rec) and uses the outer Nat IH on the cons tail (no inner induction). ",
                "Mirror of list_take_par_c. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta ",
                "increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star".to_string(),
                "delta_cong_star_list".to_string(),
                "delta_cong_star_list.rec".to_string(),
                "delta_cong_star_list.nil".to_string(),
                "delta_cong_star_list.cons".to_string(),
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

        // kapp_args_delta_cong: extend a spine-args δ* by one applied arg. kapp_args f
        // δ*-list-reduce to kapp_args f' and a δ*-reduces to a' give kapp_args (app f a)
        // δ*-list-reduce to kapp_args (app f' a'). Via kapp_args_app (snoc) +
        // delta_cong_star_list_append. Mirror of kapp_args_par_c.
        self.add_definition(SpecDefinition {
            name: "kapp_args_delta_cong".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), ",
                "delta_cong_star_list env (kapp_args f) (kapp_args f') -> ",
                "delta_cong_star env a a' -> ",
                "delta_cong_star_list env (kapp_args (KExpr.app f a)) (kapp_args (KExpr.app f' a'))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(hf : delta_cong_star_list env (kapp_args f) (kapp_args f')) ",
                    "(ha : delta_cong_star env a a') => ",
                    "Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env (kapp_args (KExpr.app f a)) Z) ",
                    "(list_append (kapp_args f') (ListType.cons KExpr a' (ListType.nil KExpr))) (kapp_args (KExpr.app f' a')) ",
                    "(Eq.symm (ListType KExpr) (kapp_args (KExpr.app f' a')) (list_append (kapp_args f') (ListType.cons KExpr a' (ListType.nil KExpr))) (kapp_args_app f' a')) ",
                    "(Eq.substType (ListType KExpr) ",
                    "(fun (Z : ListType KExpr) => delta_cong_star_list env Z (list_append (kapp_args f') (ListType.cons KExpr a' (ListType.nil KExpr)))) ",
                    "(list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args (KExpr.app f a)) ",
                    "(Eq.symm (ListType KExpr) (kapp_args (KExpr.app f a)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args_app f a)) ",
                    "(delta_cong_star_list_append env (kapp_args f) (kapp_args f') ",
                    "(ListType.cons KExpr a (ListType.nil KExpr)) (ListType.cons KExpr a' (ListType.nil KExpr)) ",
                    "hf ",
                    "(delta_cong_star_list.cons env a a' (ListType.nil KExpr) (ListType.nil KExpr) ha (delta_cong_star_list.nil env)))))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Extend a spine-args δ* by one applied arg: kapp_args f ⇒δ*_list kapp_args f' and a ⇒δ* a' ",
                "give kapp_args (app f a) ⇒δ*_list kapp_args (app f' a'). kapp_args_app (snoc) + ",
                "delta_cong_star_list_append. Mirror of kapp_args_par_c. DerivedProved, zero axiom_deps. Part of ",
                "#2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star".to_string(),
                "delta_cong_star_list".to_string(),
                "delta_cong_star_list.nil".to_string(),
                "delta_cong_star_list.cons".to_string(),
                "delta_cong_star_list_append".to_string(),
                "kapp_args".to_string(),
                "kapp_args_app".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Proof term for `delta_cong_star_list_trans`. `delta_cong_star_list.rec` on the
/// first chain with a `forall cs` motive; the cons arm inverts the second chain at
/// `cons x' xs0'` (an eq-carrying inner `delta_cong_star_list.rec` discharged by the
/// list no-confusion lemmas) and composes head/tail through `delta_cong_star_trans` +
/// the IH.
fn delta_cong_star_list_trans_proof() -> String {
    let outer_motive = concat!(
        "(fun (a : ListType KExpr) (b : ListType KExpr) (_ : delta_cong_star_list env a b) => ",
        "forall (cs : ListType KExpr), delta_cong_star_list env b cs -> delta_cong_star_list env a cs)"
    );
    let outer_nil =
        "(fun (cs : ListType KExpr) (k : delta_cong_star_list env (ListType.nil KExpr) cs) => k)";
    // Inner inversion of the second chain at (cons x' xs0').
    let inner_motive = concat!(
        "(fun (p : ListType KExpr) (q : ListType KExpr) (_ : delta_cong_star_list env p q) => ",
        "Eq (ListType KExpr) p (ListType.cons KExpr x' xs0') -> ",
        "delta_cong_star_list env (ListType.cons KExpr x xs0) q)"
    );
    let inner_nil = concat!(
        "(fun (heq : Eq (ListType KExpr) (ListType.nil KExpr) (ListType.cons KExpr x' xs0')) => ",
        "list_nil_ne_cons KExpr x' xs0' ",
        "(delta_cong_star_list env (ListType.cons KExpr x xs0) (ListType.nil KExpr)) heq)"
    );
    let inner_cons = concat!(
        "(fun (xx : KExpr) (xx' : KExpr) (yy : ListType KExpr) (yy' : ListType KExpr) ",
        "(hxx : delta_cong_star env xx xx') (hyy : delta_cong_star_list env yy yy') ",
        "(_ihq : Eq (ListType KExpr) yy (ListType.cons KExpr x' xs0') -> ",
        "delta_cong_star_list env (ListType.cons KExpr x xs0) yy') => ",
        "fun (heq : Eq (ListType KExpr) (ListType.cons KExpr xx yy) (ListType.cons KExpr x' xs0')) => ",
        "delta_cong_star_list.cons env x xx' xs0 yy' ",
        "(delta_cong_star_trans env x x' xx' hx ",
        "(Eq.substType KExpr (fun (Z : KExpr) => delta_cong_star env Z xx') xx x' ",
        "(list_cons_inj_head KExpr xx yy x' xs0' heq) hxx)) ",
        "(ih yy' ",
        "(Eq.substType (ListType KExpr) (fun (Z : ListType KExpr) => delta_cong_star_list env Z yy') yy xs0' ",
        "(list_cons_inj_tail KExpr xx yy x' xs0' heq) hyy)))"
    );
    let outer_cons = format!(
        concat!(
            "(fun (x : KExpr) (x' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
            "(hx : delta_cong_star env x x') (hxs : delta_cong_star_list env xs0 xs0') ",
            "(ih : forall (cs : ListType KExpr), delta_cong_star_list env xs0' cs -> ",
            "delta_cong_star_list env xs0 cs) => ",
            "fun (cs : ListType KExpr) (k : delta_cong_star_list env (ListType.cons KExpr x' xs0') cs) => ",
            "delta_cong_star_list.rec env {inner_motive} {inner_nil} {inner_cons} ",
            "(ListType.cons KExpr x' xs0') cs k ",
            "(Eq.refl (ListType KExpr) (ListType.cons KExpr x' xs0')))"
        ),
        inner_motive = inner_motive,
        inner_nil = inner_nil,
        inner_cons = inner_cons,
    );
    format!(
        concat!(
            "fun (env : RedEnv) (xs : ListType KExpr) (ys : ListType KExpr) (zs : ListType KExpr) ",
            "(h1 : delta_cong_star_list env xs ys) (h2 : delta_cong_star_list env ys zs) => ",
            "delta_cong_star_list.rec env {motive} {nil} {cons} xs ys h1 zs h2"
        ),
        motive = outer_motive,
        nil = outer_nil,
        cons = outer_cons,
    )
}

/// Proof term for `delta_cong_star_preserves_head_const`. `delta_cong_star.rec` on
/// the δ chain with a head-const-guard-carrying motive; refl = identity, step threads
/// the single-step `delta_cong_preserves_head_const` through the IH.
fn delta_cong_star_preserves_head_const_proof() -> String {
    let guard_head = |s: &str| {
        format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {s})) (OptionType.some Name nm)")
    };
    let motive = format!(
        "(fun (a : KExpr) (b : KExpr) (_ : delta_cong_star env a b) => {ga} -> {gb})",
        ga = guard_head("a"),
        gb = guard_head("b"),
    );
    let refl_arm = format!("(fun (e : KExpr) (g : {ge}) => g)", ge = guard_head("e"),);
    let step_arm = format!(
        "(fun (a : KExpr) (a1 : KExpr) (a2 : KExpr) \
         (hstep : delta_cong env a a1) (_htail : delta_cong_star env a1 a2) \
         (ih : {ga1} -> {ga2}) => \
         fun (ga : {ga}) => \
         ih (delta_cong_preserves_head_const env a a1 nm ga gdef hstep))",
        ga = guard_head("a"),
        ga1 = guard_head("a1"),
        ga2 = guard_head("a2"),
    );
    format!(
        "fun (env : RedEnv) (f : KExpr) (f' : KExpr) (nm : Name) \
         (ghead : {gf}) (gdef : Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr)) \
         (h : delta_cong_star env f f') => \
         delta_cong_star.rec env {motive} {refl_arm} {step_arm} f f' h ghead",
        gf = guard_head("f"),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Proof term for `list_head_some_delta_cong`. `delta_cong_star_list.rec` inversion of
/// the δ*-list derivation: the nil arm is absurd (list_head nil = none vs some a), the
/// cons arm reads the head fields through `list_head_cons` + `option_some_inj` and
/// transports the head δ* along x0 = a.
fn list_head_some_delta_cong_proof() -> String {
    let kont = concat!(
        "(forall (b : KExpr), Eq (OptionType KExpr) (list_head ys) (OptionType.some KExpr b) -> ",
        "delta_cong_star env a b -> C)"
    );
    // The inversion motive carries the head-eq hypothesis + the (q-specialized) kont.
    let motive = concat!(
        "(fun (p : ListType KExpr) (q : ListType KExpr) (_ : delta_cong_star_list env p q) => ",
        "Eq (OptionType KExpr) (list_head p) (OptionType.some KExpr a) -> ",
        "(forall (b : KExpr), Eq (OptionType KExpr) (list_head q) (OptionType.some KExpr b) -> ",
        "delta_cong_star env a b -> C) -> C)"
    );
    let nil_arm = concat!(
        "(fun (hh : Eq (OptionType KExpr) (list_head (ListType.nil KExpr)) (OptionType.some KExpr a)) ",
        "(_k : forall (b : KExpr), Eq (OptionType KExpr) (list_head (ListType.nil KExpr)) (OptionType.some KExpr b) -> ",
        "delta_cong_star env a b -> C) => ",
        "option_none_ne_some_type KExpr a C hh)"
    );
    // cons arm: p = cons x0 xs0, q = cons x0' xs0'. list_head reduces to some x0 / some x0'.
    let cons_arm = concat!(
        "(fun (x0 : KExpr) (x0' : KExpr) (xs0 : ListType KExpr) (xs0' : ListType KExpr) ",
        "(hx : delta_cong_star env x0 x0') (_hxs : delta_cong_star_list env xs0 xs0') ",
        "(_ih : Eq (OptionType KExpr) (list_head xs0) (OptionType.some KExpr a) -> ",
        "(forall (b : KExpr), Eq (OptionType KExpr) (list_head xs0') (OptionType.some KExpr b) -> ",
        "delta_cong_star env a b -> C) -> C) => ",
        "fun (hh : Eq (OptionType KExpr) (list_head (ListType.cons KExpr x0 xs0)) (OptionType.some KExpr a)) ",
        "(k2 : forall (b : KExpr), Eq (OptionType KExpr) (list_head (ListType.cons KExpr x0' xs0')) (OptionType.some KExpr b) -> ",
        "delta_cong_star env a b -> C) => ",
        "k2 x0' (list_head_cons x0' xs0') ",
        "(Eq.substType KExpr (fun (Z : KExpr) => delta_cong_star env Z x0') x0 a ",
        "(option_some_inj KExpr x0 a ",
        "(Eq.trans (OptionType KExpr) (OptionType.some KExpr x0) (list_head (ListType.cons KExpr x0 xs0)) (OptionType.some KExpr a) ",
        "(Eq.symm (OptionType KExpr) (list_head (ListType.cons KExpr x0 xs0)) (OptionType.some KExpr x0) (list_head_cons x0 xs0)) ",
        "hh)) ",
        "hx))"
    );
    format!(
        "fun (env : RedEnv) (xs : ListType KExpr) (ys : ListType KExpr) (a : KExpr) (C : Type) \
         (h : delta_cong_star_list env xs ys) \
         (hhead : Eq (OptionType KExpr) (list_head xs) (OptionType.some KExpr a)) \
         (k : {kont}) => \
         delta_cong_star_list.rec env {motive} {nil_arm} {cons_arm} xs ys h hhead k",
        kont = kont,
        motive = motive,
        nil_arm = nil_arm,
        cons_arm = cons_arm,
    )
}

/// The iota_reduct arithmetic sub-terms (verbatim from `iota_reduct`'s definition,
/// over `e0` / `major` / `meta` / `rule`).
fn iota_recon_subterms() -> (String, String, String, String, String, String) {
    let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))".to_string();
    let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))".to_string();
    let extras = format!("(list_drop (Nat.succ {major_idx}) (kapp_args e0))");
    let fields = "(list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major))".to_string();
    let prefix = format!("(list_take {prefix_n} (kapp_args e0))");
    let reduct = format!(
        "(apply_spine {extras} (apply_spine {fields} (apply_spine {prefix} (recrule_rhs rule))))"
    );
    (major_idx, prefix_n, extras, fields, prefix, reduct)
}

/// Type of `iota_reduct_recon_general`.
fn iota_reduct_recon_general_type() -> String {
    let (major_idx, _prefix_n, _extras, _fields, _prefix, reduct) = iota_recon_subterms();
    format!(
        "forall (env : RecEnv) (e0 : KExpr) (recname : Name) (meta : RecMeta) (major : KExpr) \
         (cname : Name) (rule : RecRule), \
         Eq (OptionType Name) (kexpr_const_name (kapp_fn e0)) (OptionType.some Name recname) -> \
         Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
         Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e0))) (OptionType.some KExpr major) -> \
         Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
         Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
         Eq (OptionType KExpr) (iota_reduct env e0) (OptionType.some KExpr {reduct})",
        major_idx = major_idx,
        reduct = reduct,
    )
}

/// Proof term for `iota_reduct_recon_general`. Five nested `opt_bind_some_intro`
/// rebuilding `iota_reduct env e0`'s opt_bind chain bottom-up; the innermost reduct
/// equation is `Eq.refl` (the final bind reduces to `some REDUCT`).
fn iota_reduct_recon_general_proof() -> String {
    let (major_idx, _prefix_n, _extras, _fields, _prefix, reduct) = iota_recon_subterms();
    // The opt_bind continuations (verbatim from iota_reduct, over e0, bottom-up).
    let l6 = format!("(fun (rule : RecRule) => OptionType.some KExpr {reduct})");
    let l5 = format!(
        "(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) {l6})"
    );
    let l4 = format!(
        "(fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) {l5})"
    );
    let l3 = format!(
        "(fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop {major_idx} (kapp_args e0))) {l4})"
    );
    let l2 =
        format!("(fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) {l3})");
    format!(
        "fun (env : RecEnv) (e0 : KExpr) (recname : Name) (meta : RecMeta) (major : KExpr) \
         (cname : Name) (rule : RecRule) \
         (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e0)) (OptionType.some Name recname)) \
         (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
         (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e0))) (OptionType.some KExpr major)) \
         (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
         (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) => \
         opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn e0)) {l2} recname {reduct} h1 \
         (opt_bind_some_intro RecMeta KExpr (recmeta_for env recname) {l3} meta {reduct} h2 \
         (opt_bind_some_intro KExpr KExpr (list_head (list_drop {major_idx} (kapp_args e0))) {l4} major {reduct} h3 \
         (opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn major)) {l5} cname {reduct} h4 \
         (opt_bind_some_intro RecRule KExpr (recrule_for env recname cname) {l6} rule {reduct} h5 \
         (Eq.refl (OptionType KExpr) (OptionType.some KExpr {reduct}))))))",
        major_idx = major_idx,
        reduct = reduct,
        l2 = l2,
        l3 = l3,
        l4 = l4,
        l5 = l5,
        l6 = l6,
    )
}

/// Proof term for `iota_delta_comm`. Invert `e` via `iota_reduct_some_inv_type`;
/// the head δ is discharged (recursor head, no def value via `recmeta_some_defval_none`);
/// `delta_cong_spine_cong` + `delta_cong_preserves_head_const` give the δ*-related spine
/// + preserved recursor head; `list_head_some_delta_cong` lifts the major to `major_v`;
/// `RecEnvCtorNoDefVal` discharges the major's constructor head so its head + fields are
/// preserved (`delta_cong_star_preserves_head_const` / `delta_cong_star_spine_cong`);
/// `iota_reduct_recon_general` fires the same rule on `v`; the reduct congruence is the
/// 3-layer `apply_spine_delta_cong_star` over the δ*-related extras / fields / prefix.
fn iota_delta_comm_proof() -> String {
    // Arithmetic sub-terms over `meta` / `rule` (verbatim from iota_reduct).
    let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
    let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
    let nf = "(recrule_num_fields rule)";
    // The three spine segments over a term `t` / major `m`.
    let extras = |t: &str| format!("(list_drop (Nat.succ {major_idx}) (kapp_args {t}))");
    let fields = |m: &str| {
        format!("(list_drop (Nat.sub (list_length (kapp_args {m})) {nf}) (kapp_args {m}))")
    };
    let prefix = |t: &str| format!("(list_take {prefix_n} (kapp_args {t}))");
    let reduct = |t: &str, m: &str| {
        format!(
            "(apply_spine {ex} (apply_spine {fl} (apply_spine {pf} (recrule_rhs rule))))",
            ex = extras(t),
            fl = fields(m),
            pf = prefix(t),
        )
    };
    let e_reduct = reduct("e", "major");
    let v_reduct = reduct("v", "major_v");
    let inner_e = format!("(apply_spine {pf} (recrule_rhs rule))", pf = prefix("e"));
    let inner_v = format!("(apply_spine {pf} (recrule_rhs rule))", pf = prefix("v"));

    // hspine_ev / h1v: spine δ*-congruence + preserved recursor head, under gd_rec.
    let gd_rec = "(recmeta_some_defval_none env recname meta wdisj h2)";
    let hspine_ev = format!("(delta_cong_spine_cong env e v recname h1 {gd_rec} hdelta)");
    let h1v = format!("(delta_cong_preserves_head_const env e v recname h1 {gd_rec} hdelta)");

    // Inside the list_head_some_delta_cong continuation (major_v, h3v, hmaj bound):
    let gd_ctor = "(recenv_ctor_no_defval_cname env recname cname rule major wctor h4 h5)";
    let h4v =
        format!("(delta_cong_star_preserves_head_const env major major_v cname h4 {gd_ctor} hmaj)");
    let hspine_major =
        format!("(delta_cong_star_spine_cong env major major_v cname h4 {gd_ctor} hmaj)");
    let hiota_v =
        format!("(iota_reduct_recon_general (red_rec env) v recname meta major_v cname rule {h1v} h2 h3v {h4v} h5)");

    // The 3-layer reduct congruence: delta_cong_star env e_reduct v_reduct.
    let inner_cong = format!(
        "(apply_spine_delta_cong_star env {pe} {pv} (recrule_rhs rule) (recrule_rhs rule) \
         (list_take_delta_cong env {prefix_n} (kapp_args e) (kapp_args v) {hspine_ev}) \
         (delta_cong_star.refl env (recrule_rhs rule)))",
        pe = prefix("e"),
        pv = prefix("v"),
    );
    let fields_cong = format!(
        "(Eq.substType Nat \
         (fun (Z : Nat) => delta_cong_star_list env {fe} (list_drop Z (kapp_args major_v))) \
         (Nat.sub (list_length (kapp_args major)) {nf}) \
         (Nat.sub (list_length (kapp_args major_v)) {nf}) \
         (Eq.cong Nat Nat (fun (N : Nat) => Nat.sub N {nf}) \
         (list_length (kapp_args major)) (list_length (kapp_args major_v)) \
         (delta_cong_list_length_eq env (kapp_args major) (kapp_args major_v) {hspine_major})) \
         (list_drop_delta_cong env (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major) (kapp_args major_v) {hspine_major}))",
        fe = fields("major"),
    );
    let middle_cong = format!(
        "(apply_spine_delta_cong_star env {fe} {fv} {inner_e} {inner_v} {fields_cong} {inner_cong})",
        fe = fields("major"),
        fv = fields("major_v"),
    );
    let head_e = format!("(apply_spine {fe} {inner_e})", fe = fields("major"));
    let head_v = format!("(apply_spine {fv} {inner_v})", fv = fields("major_v"));
    let outer_cong = format!(
        "(apply_spine_delta_cong_star env {exe} {exv} {head_e} {head_v} \
         (list_drop_delta_cong env (Nat.succ {major_idx}) (kapp_args e) (kapp_args v) {hspine_ev}) \
         {middle_cong})",
        exe = extras("e"),
        exv = extras("v"),
    );
    // delta_cong_star env e' v_reduct (transport e_reduct = e' via h5r).
    let leg_delta = format!(
        "(Eq.substType KExpr (fun (Z : KExpr) => delta_cong_star env Z {v_reduct}) {e_reduct} e' \
         (option_some_inj KExpr {e_reduct} e' h5r) {outer_cong})"
    );
    let witness = format!(
        "(par_delta_sc_witness.intro env e' v {v_reduct} {leg_delta} \
         (par_reduces_c.iota (red_rec env) v {v_reduct} {hiota_v}))"
    );

    // The list_head_some_delta_cong continuation.
    let lh_cont = format!(
        "(fun (major_v : KExpr) \
         (h3v : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args v))) (OptionType.some KExpr major_v)) \
         (hmaj : delta_cong_star env major major_v) => {witness})"
    );

    // The iota_reduct_some_inv_type continuation (binds recname..rule, h1..h5, h5r).
    let inv_cont = format!(
        "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
         (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) \
         (h2 : Eq (OptionType RecMeta) (recmeta_for (red_rec env) recname) (OptionType.some RecMeta meta)) \
         (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major)) \
         (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
         (h5 : Eq (OptionType RecRule) (recrule_for (red_rec env) recname cname) (OptionType.some RecRule rule)) \
         (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {e_reduct}) (OptionType.some KExpr e')) => \
         list_head_some_delta_cong env (list_drop {major_idx} (kapp_args e)) (list_drop {major_idx} (kapp_args v)) major \
         (par_delta_sc_witness env e' v) \
         (list_drop_delta_cong env {major_idx} (kapp_args e) (kapp_args v) {hspine_ev}) \
         h3 {lh_cont})"
    );

    format!(
        "fun (env : RedEnv) (e : KExpr) (e' : KExpr) (v : KExpr) \
         (hsome : Eq (OptionType KExpr) (iota_reduct (red_rec env) e) (OptionType.some KExpr e')) \
         (hdelta : delta_cong env e v) (wdisj : RecEnvDefEnvDisjoint env) (wctor : RecEnvCtorNoDefVal env) => \
         iota_reduct_some_inv_type (red_rec env) e e' (par_delta_sc_witness env e' v) hsome {inv_cont}"
    )
}

/// Proof term for `delta_cong_star_spine_cong`. `delta_cong_star.rec` on the δ chain
/// with a head-const-guard-carrying motive; refl = `delta_cong_star_list_refl`, step
/// composes the single-step `delta_cong_spine_cong` on the head (re-guarded by
/// `delta_cong_preserves_head_const`) with the IH through `delta_cong_star_list_trans`.
fn delta_cong_star_spine_cong_proof() -> String {
    let guard_head = |s: &str| {
        format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {s})) (OptionType.some Name nm)")
    };
    let motive = format!(
        "(fun (a : KExpr) (b : KExpr) (_ : delta_cong_star env a b) => {ga} -> \
         delta_cong_star_list env (kapp_args a) (kapp_args b))",
        ga = guard_head("a"),
    );
    let refl_arm = format!(
        "(fun (e : KExpr) (_g : {ge}) => delta_cong_star_list_refl env (kapp_args e))",
        ge = guard_head("e"),
    );
    let step_arm = format!(
        "(fun (a : KExpr) (a1 : KExpr) (a2 : KExpr) \
         (hstep : delta_cong env a a1) (_htail : delta_cong_star env a1 a2) \
         (ih : {ga1} -> delta_cong_star_list env (kapp_args a1) (kapp_args a2)) => \
         fun (ga : {ga}) => \
         delta_cong_star_list_trans env (kapp_args a) (kapp_args a1) (kapp_args a2) \
         (delta_cong_spine_cong env a a1 nm ga gdef hstep) \
         (ih (delta_cong_preserves_head_const env a a1 nm ga gdef hstep)))",
        ga = guard_head("a"),
        ga1 = guard_head("a1"),
    );
    format!(
        "fun (env : RedEnv) (f : KExpr) (f' : KExpr) (nm : Name) \
         (ghead : {gf}) (gdef : Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr)) \
         (h : delta_cong_star env f f') => \
         delta_cong_star.rec env {motive} {refl_arm} {step_arm} f f' h ghead",
        gf = guard_head("f"),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Proof term for `delta_cong_preserves_head_const`. `delta_cong.rec` with a motive
/// carrying the head-const + def-value-none guards; the `here` arm is discharged by
/// `delta_reduct_eq_none_of_defval_none` (the head has no δ reduct), `app_f` lifts the
/// head IH through `kapp_fn_app`, `app_a` transports the fixed head, the four binder
/// arms and the trailing let arms are discharged (a binder/let head ⟹
/// `kexpr_const_name = none`).
fn delta_cong_preserves_head_const_proof() -> String {
    let nm_some = "(OptionType.some Name nm)";
    let guard_head =
        |s: &str| format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {s})) {nm_some}");
    let guard_defval =
        "Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr)";
    let concl =
        |t: &str| format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {t})) {nm_some}");
    let motive = format!(
        "(fun (s : KExpr) (t : KExpr) (_h : delta_cong env s t) => {gh} -> {gd} -> {concl})",
        gh = guard_head("s"),
        gd = guard_defval,
        concl = concl("t"),
    );
    // here: delta_step e0 e0' but head has no def value ⟹ delta_reduct = none ⟹ absurd.
    let here_arm = format!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hd : delta_step (red_def env) e0 e0') \
         (gh : {gh}) (gd : {gd}) => \
         option_none_ne_some KExpr e0' ({concl}) \
         (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def env) e0) (OptionType.some KExpr e0') \
         (Eq.symm (OptionType KExpr) (delta_reduct (red_def env) e0) (OptionType.none KExpr) \
         (delta_reduct_eq_none_of_defval_none (red_def env) e0 nm gh gd)) hd))",
        gh = guard_head("e0"),
        gd = guard_defval,
        concl = concl("e0'"),
    );
    // app_f: f ⇒ f', a fixed. head (app f' a) = head f' = some nm via IH (head f lifted).
    let app_f_arm = format!(
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (_h : delta_cong env f f') \
         (ih : {gh_f} -> {gd} -> {concl_fp}) \
         (gh : {gh_app}) (gd : {gd}) => \
         Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name x) {nm_some}) \
         (kapp_fn f') (kapp_fn (KExpr.app f' a)) (Eq.symm KExpr (kapp_fn (KExpr.app f' a)) (kapp_fn f') (kapp_fn_app f' a)) \
         (ih (Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name x) {nm_some}) \
         (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a) gh) gd))",
        gh_f = guard_head("f"),
        gd = guard_defval,
        concl_fp = concl("f'"),
        gh_app = guard_head("(KExpr.app f a)"),
        nm_some = nm_some,
    );
    // app_a: a ⇒ a', f fixed. head (app f a') = head f = head (app f a) = some nm (gh).
    let app_a_arm = format!(
        "(fun (f : KExpr) (a : KExpr) (a' : KExpr) (_h : delta_cong env a a') \
         (_ih : {gh_a} -> {gd} -> {concl_ap}) \
         (gh : {gh_app}) (gd : {gd}) => \
         Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name x) {nm_some}) \
         (kapp_fn f) (kapp_fn (KExpr.app f a')) (Eq.symm KExpr (kapp_fn (KExpr.app f a')) (kapp_fn f) (kapp_fn_app f a')) \
         (Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name x) {nm_some}) \
         (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a) gh))",
        gh_a = guard_head("a"),
        gd = guard_defval,
        concl_ap = concl("a'"),
        gh_app = guard_head("(KExpr.app f a)"),
        nm_some = nm_some,
    );
    // binder arms: head is a binder ⟹ kexpr_const_name = none, contradicting gh.
    let lam_t_arm = format!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b : KExpr) (_h : delta_cong env t0 t0') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.lam t0 b))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("t0"),
        gd = guard_defval,
        concl_sub = concl("t0'"),
        gh_src = guard_head("(KExpr.lam t0 b)"),
        concl_t = concl("(KExpr.lam t0' b)"),
        nm_some = nm_some,
    );
    let lam_b_arm = format!(
        "(fun (t0 : KExpr) (b : KExpr) (b' : KExpr) (_h : delta_cong env b b') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.lam t0 b))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("b"),
        gd = guard_defval,
        concl_sub = concl("b'"),
        gh_src = guard_head("(KExpr.lam t0 b)"),
        concl_t = concl("(KExpr.lam t0 b')"),
        nm_some = nm_some,
    );
    let pi_d_arm = format!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b : KExpr) (_h : delta_cong env d0 d0') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.pi d0 b))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("d0"),
        gd = guard_defval,
        concl_sub = concl("d0'"),
        gh_src = guard_head("(KExpr.pi d0 b)"),
        concl_t = concl("(KExpr.pi d0' b)"),
        nm_some = nm_some,
    );
    let pi_b_arm = format!(
        "(fun (d0 : KExpr) (b : KExpr) (b' : KExpr) (_h : delta_cong env b b') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.pi d0 b))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("b"),
        gd = guard_defval,
        concl_sub = concl("b'"),
        gh_src = guard_head("(KExpr.pi d0 b)"),
        concl_t = concl("(KExpr.pi d0 b')"),
        nm_some = nm_some,
    );
    // Trailing let arms (let promotion, task #28): a genuine let_ node is its own
    // spine head and never const-headed (kexpr_const_name (kapp_fn (let_ ..)) = none
    // by rfl), so gh is refuted exactly like the binder arms.
    let let_t_arm = format!(
        "(fun (t0 : KExpr) (t0' : KExpr) (vv : KExpr) (bb : KExpr) (_h : delta_cong env t0 t0') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ t0 vv bb))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("t0"),
        gd = guard_defval,
        concl_sub = concl("t0'"),
        gh_src = guard_head("(KExpr.let_ t0 vv bb)"),
        concl_t = concl("(KExpr.let_ t0' vv bb)"),
        nm_some = nm_some,
    );
    let let_v_arm = format!(
        "(fun (t0 : KExpr) (vv : KExpr) (vv' : KExpr) (bb : KExpr) (_h : delta_cong env vv vv') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ t0 vv bb))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("vv"),
        gd = guard_defval,
        concl_sub = concl("vv'"),
        gh_src = guard_head("(KExpr.let_ t0 vv bb)"),
        concl_t = concl("(KExpr.let_ t0 vv' bb)"),
        nm_some = nm_some,
    );
    let let_b_arm = format!(
        "(fun (t0 : KExpr) (vv : KExpr) (bb : KExpr) (bb' : KExpr) (_h : delta_cong env bb bb') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ t0 vv bb))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("bb"),
        gd = guard_defval,
        concl_sub = concl("bb'"),
        gh_src = guard_head("(KExpr.let_ t0 vv bb)"),
        concl_t = concl("(KExpr.let_ t0 vv bb')"),
        nm_some = nm_some,
    );
    // proj_s arm (proj/lit rung): a genuine proj node is its own spine head and never
    // const-headed (kexpr_const_name (kapp_fn (proj ..)) = none by rfl), so gh is
    // refuted exactly like the binder/let arms.
    let proj_s_arm = format!(
        "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub' : KExpr) (_h : delta_cong env sub sub') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.proj ps pidx sub))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("sub"),
        gd = guard_defval,
        concl_sub = concl("sub'"),
        gh_src = guard_head("(KExpr.proj ps pidx sub)"),
        concl_t = concl("(KExpr.proj ps pidx sub')"),
        nm_some = nm_some,
    );
    format!(
        "fun (env : RedEnv) (f : KExpr) (f' : KExpr) (nm : Name) \
         (ghead : {gh_f}) (gdef : {gd}) (h : delta_cong env f f') => \
         delta_cong.rec env {motive} {here} {app_f} {app_a} {lam_t} {lam_b} {pi_d} {pi_b} {let_t} {let_v} {let_b} {proj_s} f f' h ghead gdef",
        gh_f = guard_head("f"),
        gd = guard_defval,
        motive = motive,
        here = here_arm,
        app_f = app_f_arm,
        app_a = app_a_arm,
        lam_t = lam_t_arm,
        lam_b = lam_b_arm,
        pi_d = pi_d_arm,
        pi_b = pi_b_arm,
        let_t = let_t_arm,
        let_v = let_v_arm,
        let_b = let_b_arm,
        proj_s = proj_s_arm,
    )
}

/// Proof term for `delta_cong_spine_cong`. `delta_cong.rec` with the
/// `delta_cong_star_list` motive carrying the head-const + def-value-none guards;
/// the `here` arm is discharged by `delta_reduct_eq_none_of_defval_none`, `app_f`
/// via `kapp_args_delta_cong` on the head IH (+ refl on the fixed arg), `app_a` via
/// `kapp_args_delta_cong` on the refl-list head (+ the arg δ-step subsumed to δ*),
/// the four binder arms and the three trailing let arms discharged
/// (binder/let head ⟹ const_name none).
fn delta_cong_spine_cong_proof() -> String {
    let nm_some = "(OptionType.some Name nm)";
    let guard_head =
        |s: &str| format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {s})) {nm_some}");
    let guard_defval =
        "Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr)";
    let concl =
        |s: &str, t: &str| format!("delta_cong_star_list env (kapp_args {s}) (kapp_args {t})");
    let motive = format!(
        "(fun (s : KExpr) (t : KExpr) (_h : delta_cong env s t) => {gh} -> {gd} -> {concl})",
        gh = guard_head("s"),
        gd = guard_defval,
        concl = concl("s", "t"),
    );
    let here_arm = format!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hd : delta_step (red_def env) e0 e0') \
         (gh : {gh}) (gd : {gd}) => \
         option_none_ne_some_type KExpr e0' ({concl}) \
         (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def env) e0) (OptionType.some KExpr e0') \
         (Eq.symm (OptionType KExpr) (delta_reduct (red_def env) e0) (OptionType.none KExpr) \
         (delta_reduct_eq_none_of_defval_none (red_def env) e0 nm gh gd)) hd))",
        gh = guard_head("e0"),
        gd = guard_defval,
        concl = concl("e0", "e0'"),
    );
    let app_f_arm = format!(
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (_h : delta_cong env f f') \
         (ih : {gh_f} -> {gd} -> {concl_f}) (gh : {gh_app}) (gd : {gd}) => \
         kapp_args_delta_cong env f f' a a \
         (ih (Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name x) {nm_some}) \
         (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a) gh) gd) \
         (delta_cong_star.refl env a))",
        gh_f = guard_head("f"),
        gd = guard_defval,
        concl_f = concl("f", "f'"),
        gh_app = guard_head("(KExpr.app f a)"),
        nm_some = nm_some,
    );
    let app_a_arm = format!(
        "(fun (f : KExpr) (a : KExpr) (a' : KExpr) (h : delta_cong env a a') \
         (_ih : {gh_a} -> {gd} -> {concl_a}) (gh : {gh_app}) (gd : {gd}) => \
         kapp_args_delta_cong env f f a a' \
         (delta_cong_star_list_refl env (kapp_args f)) \
         (delta_cong_subsumes_star env a a' h))",
        gh_a = guard_head("a"),
        gd = guard_defval,
        concl_a = concl("a", "a'"),
        gh_app = guard_head("(KExpr.app f a)"),
    );
    let lam_t_arm = format!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b : KExpr) (_h : delta_cong env t0 t0') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some_type Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.lam t0 b))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("t0"),
        gd = guard_defval,
        concl_sub = concl("t0", "t0'"),
        gh_src = guard_head("(KExpr.lam t0 b)"),
        concl_t = concl("(KExpr.lam t0 b)", "(KExpr.lam t0' b)"),
        nm_some = nm_some,
    );
    let lam_b_arm = format!(
        "(fun (t0 : KExpr) (b : KExpr) (b' : KExpr) (_h : delta_cong env b b') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some_type Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.lam t0 b))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("b"),
        gd = guard_defval,
        concl_sub = concl("b", "b'"),
        gh_src = guard_head("(KExpr.lam t0 b)"),
        concl_t = concl("(KExpr.lam t0 b)", "(KExpr.lam t0 b')"),
        nm_some = nm_some,
    );
    let pi_d_arm = format!(
        "(fun (d0 : KExpr) (d0' : KExpr) (b : KExpr) (_h : delta_cong env d0 d0') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some_type Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.pi d0 b))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("d0"),
        gd = guard_defval,
        concl_sub = concl("d0", "d0'"),
        gh_src = guard_head("(KExpr.pi d0 b)"),
        concl_t = concl("(KExpr.pi d0 b)", "(KExpr.pi d0' b)"),
        nm_some = nm_some,
    );
    let pi_b_arm = format!(
        "(fun (d0 : KExpr) (b : KExpr) (b' : KExpr) (_h : delta_cong env b b') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some_type Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.pi d0 b))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("b"),
        gd = guard_defval,
        concl_sub = concl("b", "b'"),
        gh_src = guard_head("(KExpr.pi d0 b)"),
        concl_t = concl("(KExpr.pi d0 b)", "(KExpr.pi d0 b')"),
        nm_some = nm_some,
    );
    // Trailing let arms (let promotion, task #28): a genuine let_ node is its own
    // spine head and never const-headed, so gh is refuted like the binder arms.
    let let_t_arm = format!(
        "(fun (t0 : KExpr) (t0' : KExpr) (vv : KExpr) (bb : KExpr) (_h : delta_cong env t0 t0') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some_type Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ t0 vv bb))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("t0"),
        gd = guard_defval,
        concl_sub = concl("t0", "t0'"),
        gh_src = guard_head("(KExpr.let_ t0 vv bb)"),
        concl_t = concl("(KExpr.let_ t0 vv bb)", "(KExpr.let_ t0' vv bb)"),
        nm_some = nm_some,
    );
    let let_v_arm = format!(
        "(fun (t0 : KExpr) (vv : KExpr) (vv' : KExpr) (bb : KExpr) (_h : delta_cong env vv vv') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some_type Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ t0 vv bb))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("vv"),
        gd = guard_defval,
        concl_sub = concl("vv", "vv'"),
        gh_src = guard_head("(KExpr.let_ t0 vv bb)"),
        concl_t = concl("(KExpr.let_ t0 vv bb)", "(KExpr.let_ t0 vv' bb)"),
        nm_some = nm_some,
    );
    let let_b_arm = format!(
        "(fun (t0 : KExpr) (vv : KExpr) (bb : KExpr) (bb' : KExpr) (_h : delta_cong env bb bb') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some_type Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ t0 vv bb))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("bb"),
        gd = guard_defval,
        concl_sub = concl("bb", "bb'"),
        gh_src = guard_head("(KExpr.let_ t0 vv bb)"),
        concl_t = concl("(KExpr.let_ t0 vv bb)", "(KExpr.let_ t0 vv bb')"),
        nm_some = nm_some,
    );
    // proj_s arm (proj/lit rung): a genuine proj node is its own spine head and never
    // const-headed, so gh is refuted like the binder/let arms.
    let proj_s_arm = format!(
        "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub' : KExpr) (_h : delta_cong env sub sub') \
         (_ih : {gh_sub} -> {gd} -> {concl_sub}) (gh : {gh_src}) (gd : {gd}) => \
         option_none_ne_some_type Name nm ({concl_t}) \
         (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.proj ps pidx sub))) {nm_some} \
         (Eq.refl (OptionType Name) (OptionType.none Name)) gh))",
        gh_sub = guard_head("sub"),
        gd = guard_defval,
        concl_sub = concl("sub", "sub'"),
        gh_src = guard_head("(KExpr.proj ps pidx sub)"),
        concl_t = concl("(KExpr.proj ps pidx sub)", "(KExpr.proj ps pidx sub')"),
        nm_some = nm_some,
    );
    format!(
        "fun (env : RedEnv) (f : KExpr) (f' : KExpr) (nm : Name) \
         (ghead : {gh_f}) (gdef : {gd}) (h : delta_cong env f f') => \
         delta_cong.rec env {motive} {here} {app_f} {app_a} {lam_t} {lam_b} {pi_d} {pi_b} {let_t} {let_v} {let_b} {proj_s} f f' h ghead gdef",
        gh_f = guard_head("f"),
        gd = guard_defval,
        motive = motive,
        here = here_arm,
        app_f = app_f_arm,
        app_a = app_a_arm,
        lam_t = lam_t_arm,
        lam_b = lam_b_arm,
        pi_d = pi_d_arm,
        pi_b = pi_b_arm,
        let_t = let_t_arm,
        let_v = let_v_arm,
        let_b = let_b_arm,
        proj_s = proj_s_arm,
    )
}

/// Proof term for `par_delta_sc` (blueprint `SC`). `par_reduces_c.rec (red_rec env)`
/// on the β+ι+ζ step `s ⇒ u`, motive `fun s0 u0 _ => forall w, delta_cong env s0 w ->
/// par_delta_sc_witness env u0 w`. Each compound arm inverts the δ-step against its
/// head shape and joins; the typed binders carry an extra δ-in-type subcase; beta
/// re-substitutes the δ-residual (`delta_cong_app_lam_inv` + `sc_beta_join_*`);
/// the GENUINE `let_` (zeta) arm mirrors it at the let node (`delta_cong_let_inv` +
/// `sc_let_join_*` — δ-in-ty is discarded by ζ, δ-in-val/body re-substitute);
/// the trailing `let_cong` arm joins per-slot (`sc_cong_join_let_*`);
/// forall_ rides the pi alias; iota = `iota_delta_comm`.
fn par_delta_sc_proof() -> String {
    let motive = concat!(
        "(fun (s0 : KExpr) (u0 : KExpr) (_ : par_reduces_c (red_rec env) s0 u0) => ",
        "forall (w : KExpr), delta_cong env s0 w -> par_delta_sc_witness env u0 w)"
    );

    // refl: u = s; the δ-step IS the join (δ* via subsumes_star, β+ι via refl).
    let refl_arm = concat!(
        "(fun (e : KExpr) => fun (w : KExpr) (hw : delta_cong env e w) => ",
        "par_delta_sc_witness.intro env e w w ",
        "(delta_cong_subsumes_star env e w hw) (par_reduces_c.refl (red_rec env) w))"
    );

    // iota: the landed ι×δ commutation (carrying the two RecEnv interfaces). iota_step
    // is defeq to `iota_reduct (red_rec env) e0 = some e0'`, so hi feeds straight in.
    let iota_arm = concat!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hi : iota_step (red_rec env) e0 e0') => ",
        "fun (w : KExpr) (hw : delta_cong env e0 w) => ",
        "iota_delta_comm env e0 e0' w hi hw disj ctorNoDef)"
    );

    let app_arm = format!(
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
         (hf : par_reduces_c (red_rec env) f f') (ha : par_reduces_c (red_rec env) a a') \
         (ihf : forall (w : KExpr), delta_cong env f w -> par_delta_sc_witness env f' w) \
         (iha : forall (w : KExpr), delta_cong env a w -> par_delta_sc_witness env a' w) => {body})",
        body = sc_cong_body(
            "KExpr.app",
            "delta_cong_app_inv",
            "f",
            "f'",
            "a",
            "a'",
            "hf",
            "ha",
            "ihf",
            "iha",
        ),
    );

    let lam_arm = format!(
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) \
         (hty : par_reduces_c (red_rec env) ty ty') (hbody : par_reduces_c (red_rec env) body body') \
         (ihty : forall (w : KExpr), delta_cong env ty w -> par_delta_sc_witness env ty' w) \
         (ihbody : forall (w : KExpr), delta_cong env body w -> par_delta_sc_witness env body' w) => {body})",
        body = sc_cong_body(
            "KExpr.lam",
            "delta_cong_lam_inv",
            "ty",
            "ty'",
            "body",
            "body'",
            "hty",
            "hbody",
            "ihty",
            "ihbody",
        ),
    );

    // pi (and forall_) share the same arm body: forall_ X Y is the reducible alias of
    // pi X Y, so the pi-shaped proof type-checks against the forall_ arm by defeq.
    let pi_body = sc_cong_body(
        "KExpr.pi",
        "delta_cong_pi_inv",
        "dom",
        "dom'",
        "body",
        "body'",
        "hdom",
        "hbody",
        "ihdom",
        "ihbody",
    );
    let pi_binders = "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) \
         (hdom : par_reduces_c (red_rec env) dom dom') (hbody : par_reduces_c (red_rec env) body body') \
         (ihdom : forall (w : KExpr), delta_cong env dom w -> par_delta_sc_witness env dom' w) \
         (ihbody : forall (w : KExpr), delta_cong env body w -> par_delta_sc_witness env body' w) => ";
    let pi_arm = format!("{pi_binders}{pi_body})");
    let forall_arm = format!("{pi_binders}{pi_body})");

    let beta_arm = format!(
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) \
         (hA : par_reduces_c (red_rec env) A A') (hbody : par_reduces_c (red_rec env) body body') \
         (harg : par_reduces_c (red_rec env) arg arg') \
         (ihA : forall (w : KExpr), delta_cong env A w -> par_delta_sc_witness env A' w) \
         (ihbody : forall (w : KExpr), delta_cong env body w -> par_delta_sc_witness env body' w) \
         (iharg : forall (w : KExpr), delta_cong env arg w -> par_delta_sc_witness env arg' w) => {body})",
        body = sc_beta_body("A", "body", "body'", "arg", "arg'", "hbody", "harg", "ihbody", "iharg"),
    );

    // The shared 6-field/3-premise/3-IH binder prefix of the let_ (zeta) and
    // let_cong arms (identical fields — they differ only in the reduct/body).
    let let_binders = "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) \
         (hty : par_reduces_c (red_rec env) ty ty') (hval : par_reduces_c (red_rec env) val val') \
         (hbody : par_reduces_c (red_rec env) body body') \
         (ihty : forall (w : KExpr), delta_cong env ty w -> par_delta_sc_witness env ty' w) \
         (ihval : forall (w : KExpr), delta_cong env val w -> par_delta_sc_witness env val' w) \
         (ihbody : forall (w : KExpr), delta_cong env body w -> par_delta_sc_witness env body' w) => ";

    // let_ (ZETA): the GENUINE let_ node fires to instantiate body' val'. FLAT 3-way
    // split via delta_cong_let_inv with simple continuations — each leg one
    // application of a named sc_let_join_* lemma (mirroring the beta arm's
    // delta_cong_app_lam_inv + sc_beta_join_* treatment). δ-in-ty is discarded by ζ
    // (hAt and ihty unused, exactly as the beta arm drops the type IH).
    let let_zeta_body = concat!(
        "(fun (w : KExpr) (hw : delta_cong env (KExpr.let_ ty val body) w) => ",
        "delta_cong_let_inv env ty val body w (par_delta_sc_witness env (instantiate body' val') w) hw ",
        "(fun (At : KExpr) (_hAt : delta_cong env ty At) (heqr : Eq KExpr w (KExpr.let_ At val body)) => ",
        "sc_let_join_ty env At val val' body body' w hval hbody heqr) ",
        "(fun (vt : KExpr) (hvt : delta_cong env val vt) (heqr : Eq KExpr w (KExpr.let_ ty vt body)) => ",
        "sc_let_join_val env liftclosed ty body body' val' vt w hbody heqr (ihval vt hvt)) ",
        "(fun (bt : KExpr) (hbt : delta_cong env body bt) (heqr : Eq KExpr w (KExpr.let_ ty val bt)) => ",
        "sc_let_join_body env closed ty val val' body' bt w hval heqr (ihbody bt hbt)))"
    );
    let let_arm = format!("{let_binders}{let_zeta_body})");

    // let_cong (TRAILING congruence ctor): the reduct is let_ ty' val' body'. Same
    // flat 3-way split, each leg one sc_cong_join_let_* application (per-slot join,
    // the app-vs-app mechanism over three slots).
    let let_cong_body = concat!(
        "(fun (w : KExpr) (hw : delta_cong env (KExpr.let_ ty val body) w) => ",
        "delta_cong_let_inv env ty val body w (par_delta_sc_witness env (KExpr.let_ ty' val' body') w) hw ",
        "(fun (b0 : KExpr) (hb0 : delta_cong env ty b0) (heqw : Eq KExpr w (KExpr.let_ b0 val body)) => ",
        "sc_cong_join_let_ty env ty' val val' body body' b0 w hval hbody heqw (ihty b0 hb0)) ",
        "(fun (b1 : KExpr) (hb1 : delta_cong env val b1) (heqw : Eq KExpr w (KExpr.let_ ty b1 body)) => ",
        "sc_cong_join_let_val env ty ty' val' body body' b1 w hty hbody heqw (ihval b1 hb1)) ",
        "(fun (b2 : KExpr) (hb2 : delta_cong env body b2) (heqw : Eq KExpr w (KExpr.let_ ty val b2)) => ",
        "sc_cong_join_let_body env ty ty' val val' body' b2 w hty hval heqw (ihbody b2 hb2)))"
    );
    let let_cong_arm = format!("{let_binders}{let_cong_body})");

    // proj (TRAILING congruence ctor): the genuine proj node fires to proj s i sub'.
    // Single-hole join — invert the δ-step on the scrutinee via delta_cong_proj_inv,
    // then one sc_cong_join_proj application (the app-vs-app mechanism, one slot).
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(hsub : par_reduces_c (red_rec env) sub sub') ",
        "(ihsub : forall (w : KExpr), delta_cong env sub w -> par_delta_sc_witness env sub' w) => ",
        "fun (w : KExpr) (hw : delta_cong env (KExpr.proj s i sub) w) => ",
        "delta_cong_proj_inv env s i sub w (par_delta_sc_witness env (KExpr.proj s i sub') w) hw ",
        "(fun (b0 : KExpr) (hb0 : delta_cong env sub b0) (heqw : Eq KExpr w (KExpr.proj s i b0)) => ",
        "sc_cong_join_proj env sub' b0 w s i heqw (ihsub b0 hb0)))"
    );

    format!(
        "fun (env : RedEnv) (closed : DefEnvClosed (red_def env)) \
         (liftclosed : DefEnvLiftClosed (red_def env)) (disj : RecEnvDefEnvDisjoint env) \
         (ctorNoDef : RecEnvCtorNoDefVal env) (s : KExpr) (u : KExpr) (v : KExpr) \
         (hpar : par_reduces_c (red_rec env) s u) (hd : delta_cong env s v) => \
         par_reduces_c.rec (red_rec env) {motive} {refl_arm} {beta_arm} {app_arm} {lam_arm} \
         {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} s u hpar v hd",
        proj_arm = proj_arm,
    )
}

/// Congruence-arm body (the `fun w hw => ...`) for `par_delta_sc`'s app/lam/pi (and
/// forall via pi). `n0`/`n1` are the source slots, `n0p`/`n1p` their β+ι reducts;
/// `h0`/`h1` the slot premises, `ih0`/`ih1` the slot IHs. Two δ subcases: δ in slot0
/// (left) / δ in slot1 (right). Assumes `env` is in scope in the generated term.
#[allow(clippy::too_many_arguments)]
fn sc_cong_body(
    head: &str,
    inv: &str,
    n0: &str,
    n0p: &str,
    n1: &str,
    n1p: &str,
    h0: &str,
    h1: &str,
    ih0: &str,
    ih1: &str,
) -> String {
    let head_tag = head.strip_prefix("KExpr.").unwrap_or(head);
    let wit_ty = format!("par_delta_sc_witness env ({head} {n0p} {n1p}) w");
    // Simple continuations: each delegates the witness construction (large elimination
    // + transport) to a named sc_cong_join_* lemma, so the inversion's arguments stay
    // first-order and par_delta_sc's value stays small.
    let left = format!(
        "(fun (b0 : KExpr) (hb0 : delta_cong env {n0} b0) (heqw : Eq KExpr w ({head} b0 {n1})) => \
         sc_cong_join_{head_tag}_left env {n0p} {n1} {n1p} b0 w {h1} heqw ({ih0} b0 hb0))"
    );
    let right = format!(
        "(fun (b1 : KExpr) (hb1 : delta_cong env {n1} b1) (heqw : Eq KExpr w ({head} {n0} b1)) => \
         sc_cong_join_{head_tag}_right env {n0} {n0p} {n1p} b1 w {h0} heqw ({ih1} b1 hb1))"
    );
    format!(
        "(fun (w : KExpr) (hw : delta_cong env ({head} {n0} {n1}) w) => \
         {inv} env {n0} {n1} w ({wit_ty}) hw {left} {right})"
    )
}

/// beta arm body for `par_delta_sc`. Source = `app (lam tn bd) ag`; reduct =
/// `instantiate bd' ag'`. Invert app, then (function leg) lam: δ-in-type is trivial
/// (the type is discarded), δ-in-body via `delta_substStar_body`, δ-in-arg via
/// `delta_substStar_val`. Assumes `env`/`closed`/`liftclosed` are in scope. (Since
/// the let promotion, task #28, the `let_` zeta arm no longer rides this app(lam)
/// shape — it has its own flat split via `delta_cong_let_inv` + `sc_let_join_*`.)
#[allow(clippy::too_many_arguments)]
fn sc_beta_body(
    tn: &str,
    bd: &str,
    bdp: &str,
    ag: &str,
    agp: &str,
    hbody: &str,
    harg: &str,
    ihbody: &str,
    iharg: &str,
) -> String {
    let wit_ty = format!("par_delta_sc_witness env (instantiate {bdp} {agp}) w");
    // FLAT 3-way split via delta_cong_app_lam_inv with SIMPLE continuations — each leg
    // is one application of a named sc_beta_join_* lemma (which carries the large
    // elimination + transport), keeping par_delta_sc's value small.
    let kt = format!(
        "(fun (At : KExpr) (hAt : delta_cong env {tn} At) (heqr : Eq KExpr w (KExpr.app (KExpr.lam At {bd}) {ag})) => \
         sc_beta_join_type env At {bd} {bdp} {ag} {agp} w {hbody} {harg} heqr)"
    );
    let kb = format!(
        "(fun (bt : KExpr) (hbt : delta_cong env {bd} bt) (heqr : Eq KExpr w (KExpr.app (KExpr.lam {tn} bt) {ag})) => \
         sc_beta_join_body env closed {tn} {bdp} {ag} {agp} bt w {harg} heqr ({ihbody} bt hbt))"
    );
    let ka = format!(
        "(fun (ar : KExpr) (har : delta_cong env {ag} ar) (heqr : Eq KExpr w (KExpr.app (KExpr.lam {tn} {bd}) ar)) => \
         sc_beta_join_arg env liftclosed {tn} {bd} {bdp} {agp} ar w {hbody} heqr ({iharg} ar har))"
    );
    format!(
        "(fun (w : KExpr) (hw : delta_cong env (KExpr.app (KExpr.lam {tn} {bd}) {ag}) w) => \
         delta_cong_app_lam_inv env {tn} {bd} {ag} w ({wit_ty}) hw {kt} {kb} {ka})"
    )
}

/// Proof term for `delta_cong_app_lam_inv`. `delta_cong_app_inv` on the β-redex's
/// outer app (function leg `app_inv` left, argument leg right), then `delta_cong_lam_inv`
/// on the function leg, folding each two-level reduct equation into one via `Eq.trans`
/// + `Eq.cong` so the three exposed continuations (`kt`/`kb`/`ka`) each see a single
/// `Eq KExpr r (app (lam ..) ..)`.
fn delta_cong_app_lam_inv_proof() -> String {
    // The two type/body legs fold heqw : r = app b0 arg with heql : b0 = lam .. into
    // r = app (lam ..) arg via Eq.trans over an Eq.cong on (fun z => app z arg).
    let fold = |lam_term: &str| {
        format!(
            "(Eq.trans KExpr r (KExpr.app b0 arg) (KExpr.app {lam_term} arg) heqw \
             (Eq.cong KExpr KExpr (fun (z : KExpr) => KExpr.app z arg) b0 {lam_term} heql))"
        )
    };
    let kt_leg = format!(
        "(fun (At : KExpr) (hAt : delta_cong env A At) (heql : Eq KExpr b0 (KExpr.lam At body)) => \
         kt At hAt {eqf})",
        eqf = fold("(KExpr.lam At body)"),
    );
    let kb_leg = format!(
        "(fun (bt : KExpr) (hbt : delta_cong env body bt) (heql : Eq KExpr b0 (KExpr.lam A bt)) => \
         kb bt hbt {eqf})",
        eqf = fold("(KExpr.lam A bt)"),
    );
    let func_leg = format!(
        "(fun (b0 : KExpr) (hb0 : delta_cong env (KExpr.lam A body) b0) (heqw : Eq KExpr r (KExpr.app b0 arg)) => \
         delta_cong_lam_inv env A body b0 C hb0 {kt_leg} {kb_leg})"
    );
    let arg_leg = concat!(
        "(fun (b1 : KExpr) (hb1 : delta_cong env arg b1) (heqw : Eq KExpr r (KExpr.app (KExpr.lam A body) b1)) => ",
        "ka b1 hb1 heqw)"
    );
    format!(
        "fun (env : RedEnv) (A : KExpr) (body : KExpr) (arg : KExpr) (r : KExpr) (C : Type) \
         (h : delta_cong env (KExpr.app (KExpr.lam A body) arg) r) \
         (kt : forall (At : KExpr), delta_cong env A At -> Eq KExpr r (KExpr.app (KExpr.lam At body) arg) -> C) \
         (kb : forall (bt : KExpr), delta_cong env body bt -> Eq KExpr r (KExpr.app (KExpr.lam A bt) arg) -> C) \
         (ka : forall (ar : KExpr), delta_cong env arg ar -> Eq KExpr r (KExpr.app (KExpr.lam A body) ar) -> C) => \
         delta_cong_app_inv env (KExpr.lam A body) arg r C h {func_leg} {arg_leg}"
    )
}

/// Proof term for `par_reduces_cd_star_diamond` — the one-liner that discharges the
/// `SC` bound hypothesis of `par_reduces_cd_star_diamond_of_sc` with `par_delta_sc`.
fn par_reduces_cd_star_diamond_proof() -> String {
    concat!(
        "fun (env : RedEnv) ",
        "(i1 : RecEnvReductNotRedex (red_rec env)) (i2 : RecEnvCtorNoRecMeta (red_rec env)) ",
        "(i3 : RecEnvClosed (red_rec env)) (i4 : RecEnvLiftClosed (red_rec env)) ",
        "(i5 : DefEnvClosed (red_def env)) (i6 : DefEnvLiftClosed (red_def env)) ",
        "(i7 : RecEnvDefEnvDisjoint env) (i8 : RecEnvCtorNoDefVal env) ",
        "(e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
        "(h1 : par_reduces_cd_star env e e1) (h2 : par_reduces_cd_star env e e2) => ",
        "par_reduces_cd_star_diamond_of_sc env i1 i2 i3 i4 ",
        "(par_delta_sc env i5 i6 i7 i8) e e1 e2 h1 h2"
    )
    .to_string()
}

#[cfg(test)]
#[path = "par_reduces_iota_delta_tests.rs"]
mod par_reduces_iota_delta_tests;
