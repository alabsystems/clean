// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! #2859 (church_rosser_whnf-deletion, STEP 5): pi shape-inversion + injectivity
//! lemmas for the PROPER (Takahashi) parallel reduction `par_reduces_p` and its
//! reflexive-transitive closure `par_reduces_p_star`.
//!
//! This module is a VERBATIM MIRROR of the landed Wave-142/143 iota-free `_bd`
//! tower in `par_reduction.rs`, with two systematic swaps:
//!   * relation swap   `par_reduces_bd`  -> `par_reduces_p`   (env-threaded)
//!   * single->star    `par_reduces_bd_star` -> `par_reduces_p_star`
//! plus the genuine-new PARALLEL-iota (`iota_p`) recursor arm that `par_reduces_p`
//! carries and `par_reduces_bd` does not. The iota arm is discharged exactly as in
//! the landed `par_reduces_p_lam_inv`: the iota fires on the REDUCED redex (a
//! par-reduct of the binder-headed source), which a `*_reduct_not_redex`
//! prerequisite proves cannot be an iota redex.
//!
//! The lemmas it lands:
//!   * `par_reduces_p_pi_reduct_not_redex` — prerequisite (pi dual of the landed
//!     `par_reduces_p_lam_reduct_not_redex`); a par-reduct of a pi is never an iota
//!     redex.
//!   * `par_reduces_p_pi_inv_eq` — single-step Eq-DATA pi inversion (pi dual of the
//!     landed `par_reduces_p_lam_inv`, Eq-data form mirroring
//!     `par_reduces_bd_pi_inv_eq`).
//!   * `par_reduces_p_star_pi_inv` / `_eq` — star-level pi inversion (mirror of
//!     `par_reduces_bd_star_pi_inv` / `_eq`).
//!   * `par_p_pi_injectivity_dom` / `_cod` — pi injectivity up to confluence
//!     (mirror of `par_bd_pi_injectivity_dom` / `_cod`).
//!
//! These are the iota-free-modulo-the-discharged-iota-arm analogue of the
//! pi-injectivity-for-DefEq the `church_rosser_whnf` HelperAxiom stands in for.
//! INDEPENDENT of the in-flight complete-development keystone (consumes only the
//! landed `par_reduces_p_star` substrate + `par_reduces_p_lam_inv`'s sibling
//! prerequisite shapes). All DerivedProved, zero axiom_deps. Part of #2859 STEP 5.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Wire the STEP-5 pi shape-inversion + injectivity tower for `par_reduces_p`.
    /// Runs after `add_complete_development` (par_reduces_p_lam_inv landed) and
    /// `add_par_reduces_p` (par_reduces_p_star substrate landed).
    pub(super) fn add_par_reduces_p_injectivity(&mut self) -> Result<(), SpecError> {
        self.add_par_reduces_p_pi_inv_single()?;
        self.add_par_reduces_p_star_pi_inv()?;
        self.add_par_p_pi_injectivity()?;
        self.add_par_reduces_p_lam_inv_eq()?;
        self.add_par_reduces_p_star_lam_inv()?;
        self.add_par_p_lam_injectivity()?;
        Ok(())
    }

    /// lam dual, single-step layer: the Eq-data single-step lam inversion. The
    /// landed `par_reduces_p_lam_inv` is the KExpr-INDEXED (CPS) form; the star lam
    /// inversion's step arm needs the reduct equality as DATA, exactly as
    /// `par_reduces_bd_lam_inv_eq` provides on the `_bd` side. This is the lam
    /// analogue of `par_reduces_p_pi_inv_eq` (lam swap of pi), reusing the landed
    /// `par_reduces_p_lam_reduct_not_redex` for its iota arm.
    fn add_par_reduces_p_lam_inv_eq(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_lam_inv_eq".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : Type), ",
                "par_reduces_p env (KExpr.lam ty body) t -> ",
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "Eq KExpr t (KExpr.lam ty' body') -> ",
                "par_reduces_p env ty ty' -> par_reduces_p env body body' -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(par_reduces_p_lam_inv_eq_proof()),
            is_axiom: false,
            description: concat!(
                "STEP-5 lam dual (#2859): Eq-data shape recovery for a lam-headed par_reduces_p — from ",
                "par_reduces_p env (lam ty body) t, hand the continuation the reduct equality ",
                "Eq t (lam ty' body') together with ty ⇒_p ty' and body ⇒_p body'. The Eq-DATA sibling of the ",
                "landed (KExpr-indexed/CPS) par_reduces_p_lam_inv and the lam swap of par_reduces_p_pi_inv_eq ",
                "(the analogue of par_reduces_bd_lam_inv_eq the _bd side carries). par_reduces_p.rec with a ",
                "source-equation motive whose Kont is parameterized by the arm reduct; the lam arm matches ",
                "(Eq.refl reduct, components transported via lam injectivity); refl folds in; pi/forall_ ",
                "discharged by pi_ne_lam, beta/app by app_ne_lam, the let_ (ZETA) and let_cong arms by ",
                "let_ne_lam (a genuine let node is never a lam); the PARALLEL-iota arm fires on the ",
                "REDUCED redex (a par-reduct of the lam), discharged via par_reduces_p_lam_reduct_not_redex on ",
                "the transported premise. DerivedProved, zero axiom_deps."
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
                "par_reduces_p_lam_reduct_not_redex".to_string(),
                "iota_step".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "app_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "let_ne_lam".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// lam dual, star layer: multi-step lam inversion (KExpr-indexed) + Eq-data
    /// sibling. lam swap of the pi star tower; net-new on the `_bd` side (which only
    /// carries the pi star tower), built honestly by mirroring the pi star proofs.
    fn add_par_reduces_p_star_lam_inv(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_star_lam_inv".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (body : KExpr) (w : KExpr) (C : KExpr -> Type), ",
                "par_reduces_p_star env (KExpr.lam ty body) w -> ",
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "par_reduces_p_star env ty ty' -> par_reduces_p_star env body body' -> ",
                "C (KExpr.lam ty' body')) -> ",
                "C w"
            )
            .to_string(),
            value_src: Some(par_reduces_p_star_lam_inv_proof()),
            is_axiom: false,
            description: concat!(
                "STEP-5 lam dual (#2859): star-level (multi-step) lam inversion / shape preservation — from ",
                "par_reduces_p_star env (lam ty body) w, recover w = lam ty' body' with ty ⇒*_p ty' and ",
                "body ⇒*_p body'. The lam swap of par_reduces_p_star_pi_inv (net-new on the _bd side, built ",
                "honestly). Induction on the star derivation via par_reduces_p_star.rec with an accumulator ",
                "motive carrying Eq s (lam A B) and the prefixes ty ⇒*_p A, body ⇒*_p B; the step arm ",
                "Eq-inverts each step via par_reduces_p_lam_inv_eq and extends the prefixes via ",
                "par_subsumes_par_p_star + par_reduces_p_star_trans. DerivedProved, zero axiom_deps."
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
                "par_reduces_p_lam_inv_eq".to_string(),
                "par_subsumes_par_p_star".to_string(),
                "par_reduces_p_star_trans".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "par_reduces_p_star_lam_inv_eq".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (body : KExpr) (w : KExpr) (C : Type), ",
                "par_reduces_p_star env (KExpr.lam ty body) w -> ",
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "Eq KExpr w (KExpr.lam ty' body') -> ",
                "par_reduces_p_star env ty ty' -> par_reduces_p_star env body body' -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(par_reduces_p_star_lam_inv_eq_proof()),
            is_axiom: false,
            description: concat!(
                "STEP-5 lam dual (#2859): Eq-data star-level lam inversion — from ",
                "par_reduces_p_star env (lam ty body) w, hand the continuation Eq w (lam ty' body') with ",
                "ty ⇒*_p ty' and body ⇒*_p body'. The reduct-as-data sibling of par_reduces_p_star_lam_inv ",
                "(lam swap of par_reduces_p_star_pi_inv_eq), derived from it by the motive ",
                "M(ww) := Eq w ww -> C applied at Eq.refl w. The form lam-injectivity consumes. DerivedProved, ",
                "zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star_lam_inv".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// lam dual, injectivity layer: lam injectivity up to confluence (domain +
    /// codomain). lam swap of the pi injectivity lemmas.
    fn add_par_p_lam_injectivity(&mut self) -> Result<(), SpecError> {
        for (name, lam_inj, clhs, crhs, meet1, meet2, leg2, what) in [
            (
                "par_p_lam_injectivity_dom",
                "lam_inj_fst",
                "a1",
                "a2",
                "a1'",
                "a2'",
                "hda2",
                "domains",
            ),
            (
                "par_p_lam_injectivity_cod",
                "lam_inj_snd",
                "b1",
                "b2",
                "b1'",
                "b2'",
                "hdb2",
                "codomains",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (env : RecEnv) (a1 : KExpr) (b1 : KExpr) (a2 : KExpr) (b2 : KExpr), ",
                        "par_strips_witness_p_star env (KExpr.lam a1 b1) (KExpr.lam a2 b2) -> ",
                        "par_strips_witness_p_star env {clhs} {crhs}"
                    ),
                    clhs = clhs,
                    crhs = crhs,
                ),
                value_src: Some(par_p_lam_injectivity_proof(
                    clhs, crhs, meet1, meet2, leg2, lam_inj,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "STEP-5 lam dual (#2859): lam injectivity up to proper-parallel confluence ({what}) — ",
                        "from a shared-reduct join witness on lam a1 b1 and lam a2 b2, produce a join witness on ",
                        "the {what}. Project the common reduct e3, Eq-invert both legs via ",
                        "par_reduces_p_star_lam_inv_eq (e3 = lam a1' b1' = lam a2' b2'), read off the {what} ",
                        "equality by {lam_inj} of the trans'd reduct equation, transport the second leg onto the ",
                        "meet, and package via par_strips_witness_p_star.intro. The lam swap of ",
                        "par_p_pi_injectivity_{what}. DerivedProved, zero axiom_deps."
                    ),
                    what = what,
                    lam_inj = lam_inj,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_p_star".to_string(),
                    "par_strips_witness_p_star".to_string(),
                    "par_strips_witness_p_star.rec".to_string(),
                    "par_strips_witness_p_star.intro".to_string(),
                    "par_reduces_p_star_lam_inv_eq".to_string(),
                    lam_inj.to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                    "Eq.substType".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }

    /// Single-step layer: the pi-reduct-not-redex prerequisite + the Eq-data
    /// single-step pi inversion.
    fn add_par_reduces_p_pi_inv_single(&mut self) -> Result<(), SpecError> {
        // par_reduces_p_pi_reduct_not_redex: the pi dual of the landed
        // par_reduces_p_lam_reduct_not_redex. From a pi-headed par-step
        // (pi dom body) ⇒_p t and a fired iota (iota_step env t r), derive any
        // C : Type. A par-reduct of a pi is pi-headed (pi/forall_ arms), and an iota
        // on a pi head is absurd (iota_step_head_none_absurd_type); lam is lam-headed
        // (lam_ne_pi), beta/app are app-headed (app_ne_pi), let_/let_cong are
        // let_-headed (let_ne_pi — the genuine 7th ctor, never a pi); the iota_p arm
        // discharges via its OWN IH on the fire premise (the reduced sub-redex is
        // again a par-reduct of the pi, hence not a redex).
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_pi_reduct_not_redex".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (dom : KExpr) (body : KExpr) (t : KExpr) (r : KExpr) (C : Type), ",
                "par_reduces_p env (KExpr.pi dom body) t -> ",
                "iota_step env t r -> C"
            )
            .to_string(),
            value_src: Some(par_reduces_p_pi_reduct_not_redex_proof()),
            is_axiom: false,
            description: concat!(
                "STEP-5 prerequisite (#2859): a par-reduct of a pi is never an iota redex (pi dual of the ",
                "landed par_reduces_p_lam_reduct_not_redex). From par_reduces_p env (pi dom body) t and ",
                "iota_step env t r, derive any C. Type-valued (C : Type) so the par_reduces_p.rec motive lands ",
                "in Type. par_reduces_p.rec with a source-equation motive universalizing the new redex (r, C): ",
                "refl/pi/forall_ arms have a pi-headed reduct, so the iota on it is absurd via ",
                "iota_step_head_none_absurd_type; lam is lam-headed (lam_ne_pi); beta/app are app-headed ",
                "(app_ne_pi); the let_ (ZETA) and let_cong arms are let_-headed (let_ne_pi); the iota_p arm ",
                "discharges via its OWN IH applied to the constructor's fire premise ",
                "(the reduced sub-redex is again a par-reduct of the pi, so not a redex). DerivedProved, zero ",
                "axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "iota_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "app_ne_pi".to_string(),
                "lam_ne_pi".to_string(),
                "let_ne_pi".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "instantiate".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_pi_inv_eq: single-step Eq-DATA pi inversion. From
        // par_reduces_p env (pi dom body) t, hand the continuation the reduct equality
        // Eq t (pi dom' body') together with dom ⇒_p dom' and body ⇒_p body'. The pi
        // and forall_ arms are the genuine matches (forall_ is the reducible pi alias);
        // refl folds in; lam discharged by lam_ne_pi; beta/app by app_ne_pi; the let_
        // (ZETA) and let_cong arms by let_ne_pi (a genuine let node is never a pi); the
        // PARALLEL-iota arm fires on the REDUCED redex (a par-reduct of the pi), so it
        // is discharged via par_reduces_p_pi_reduct_not_redex on the transported
        // premise. The pi dual of par_reduces_p_lam_inv (Eq-data form), the p-side
        // mirror of par_reduces_bd_pi_inv_eq.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_pi_inv_eq".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (dom : KExpr) (body : KExpr) (t : KExpr) (C : Type), ",
                "par_reduces_p env (KExpr.pi dom body) t -> ",
                "(forall (dom' : KExpr) (body' : KExpr), ",
                "Eq KExpr t (KExpr.pi dom' body') -> ",
                "par_reduces_p env dom dom' -> par_reduces_p env body body' -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(par_reduces_p_pi_inv_eq_proof()),
            is_axiom: false,
            description: concat!(
                "STEP-5 (#2859): Eq-data shape recovery for a pi-headed par_reduces_p — from ",
                "par_reduces_p env (pi dom body) t, hand the continuation the reduct equality ",
                "Eq t (pi dom' body') together with dom ⇒_p dom' and body ⇒_p body', returning the fixed ",
                "result type C. The pi dual of par_reduces_p_lam_inv and the p-side mirror of ",
                "par_reduces_bd_pi_inv_eq: par_reduces_p.rec with a source-equation motive whose continuation ",
                "Kont is parameterized by the arm reduct, so the recursor substitutes the genuine reduct t. The ",
                "pi and forall_ arms match (forall_ is the reducible pi alias, Eq.refl reduct equation); refl ",
                "folds in; lam discharged by lam_ne_pi, beta/app by app_ne_pi, the let_ (ZETA) and let_cong arms ",
                "by let_ne_pi (a genuine let node is never a pi); the PARALLEL-iota arm fires ",
                "on the REDUCED redex (a par-reduct of the pi), discharged via par_reduces_p_pi_reduct_not_redex ",
                "on the transported premise. DerivedProved, zero axiom_deps."
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
                "par_reduces_p_pi_reduct_not_redex".to_string(),
                "iota_step".to_string(),
                "pi_inj_fst".to_string(),
                "pi_inj_snd".to_string(),
                "app_ne_pi".to_string(),
                "lam_ne_pi".to_string(),
                "let_ne_pi".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Star layer: multi-step pi inversion (KExpr-indexed) + its Eq-data sibling.
    fn add_par_reduces_p_star_pi_inv(&mut self) -> Result<(), SpecError> {
        // par_reduces_p_star_pi_inv: star-level (multi-step) pi inversion. From
        // par_reduces_p_star (pi dom body) w, recover w = pi dom' body' with
        // dom ⇒*_p dom' and body ⇒*_p body'. Induction on the star derivation with an
        // accumulator motive carrying Eq s (pi A B) + the prefixes dom ⇒*_p A,
        // body ⇒*_p B; the step arm Eq-inverts each single step via
        // par_reduces_p_pi_inv_eq and extends the prefixes through
        // par_subsumes_par_p_star + par_reduces_p_star_trans. Mirror of
        // par_reduces_bd_star_pi_inv.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_star_pi_inv".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (dom : KExpr) (body : KExpr) (w : KExpr) (C : KExpr -> Type), ",
                "par_reduces_p_star env (KExpr.pi dom body) w -> ",
                "(forall (dom' : KExpr) (body' : KExpr), ",
                "par_reduces_p_star env dom dom' -> par_reduces_p_star env body body' -> ",
                "C (KExpr.pi dom' body')) -> ",
                "C w"
            )
            .to_string(),
            value_src: Some(par_reduces_p_star_pi_inv_proof()),
            is_axiom: false,
            description: concat!(
                "STEP-5 (#2859): star-level (multi-step) pi inversion / shape preservation for the proper ",
                "parallel join — from par_reduces_p_star env (pi dom body) w, recover w = pi dom' body' with ",
                "dom ⇒*_p dom' and body ⇒*_p body'. The multi-step lift of par_reduces_p_pi_inv_eq and the ",
                "p-side mirror of par_reduces_bd_star_pi_inv. Proved by induction on the star derivation via ",
                "par_reduces_p_star.rec with an accumulator motive carrying the reduct equation Eq s (pi A B) ",
                "and the accumulated prefixes dom ⇒*_p A, body ⇒*_p B; the refl arm hands the continuation the ",
                "prefixes (transporting C (pi A B) onto C s), the step arm Eq-inverts each step via ",
                "par_reduces_p_pi_inv_eq and extends the prefixes via par_subsumes_par_p_star + ",
                "par_reduces_p_star_trans. DerivedProved, zero axiom_deps."
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
                "par_reduces_p_pi_inv_eq".to_string(),
                "par_subsumes_par_p_star".to_string(),
                "par_reduces_p_star_trans".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_star_pi_inv_eq: the Eq-DATA star pi inversion — the reduct
        // equality handed back as data. Derived from par_reduces_p_star_pi_inv by the
        // motive M(ww) := Eq w ww -> C applied at Eq.refl. The form pi injectivity
        // consumes. Mirror of par_reduces_bd_star_pi_inv_eq.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_star_pi_inv_eq".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (dom : KExpr) (body : KExpr) (w : KExpr) (C : Type), ",
                "par_reduces_p_star env (KExpr.pi dom body) w -> ",
                "(forall (dom' : KExpr) (body' : KExpr), ",
                "Eq KExpr w (KExpr.pi dom' body') -> ",
                "par_reduces_p_star env dom dom' -> par_reduces_p_star env body body' -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(par_reduces_p_star_pi_inv_eq_proof()),
            is_axiom: false,
            description: concat!(
                "STEP-5 (#2859): Eq-data star-level pi inversion — from par_reduces_p_star env (pi dom body) w, ",
                "hand the continuation the reduct equality Eq w (pi dom' body') together with dom ⇒*_p dom' and ",
                "body ⇒*_p body', returning the fixed result type C. The reduct-as-data sibling of ",
                "par_reduces_p_star_pi_inv (the p-side mirror of par_reduces_bd_star_pi_inv_eq), derived from it ",
                "by the motive M(ww) := Eq w ww -> C applied at Eq.refl w. The form pi-injectivity consumes (two ",
                "inversions of the SAME reduct align via their reduct equations). DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star_pi_inv".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Injectivity layer: pi injectivity up to confluence (domain + codomain).
    fn add_par_p_pi_injectivity(&mut self) -> Result<(), SpecError> {
        // par_p_pi_injectivity_dom / _cod: pi injectivity up to confluence. From a
        // join witness on pi a1 b1 and pi a2 b2, produce a join witness on the domains
        // (a1, a2) / codomains (b1, b2). Project the shared reduct e3, Eq-invert both
        // legs via par_reduces_p_star_pi_inv_eq to e3 = pi a1' b1' = pi a2' b2', read
        // off a1' = a2' (resp. b1' = b2') by pi injectivity of the equality, and meet.
        // Mirror of par_bd_pi_injectivity_dom / _cod.
        for (name, pi_inj, clhs, crhs, meet1, meet2, leg2, what) in [
            (
                "par_p_pi_injectivity_dom",
                "pi_inj_fst",
                "a1",
                "a2",
                "a1'",
                "a2'",
                "hda2",
                "domains",
            ),
            (
                "par_p_pi_injectivity_cod",
                "pi_inj_snd",
                "b1",
                "b2",
                "b1'",
                "b2'",
                "hdb2",
                "codomains",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    concat!(
                        "forall (env : RecEnv) (a1 : KExpr) (b1 : KExpr) (a2 : KExpr) (b2 : KExpr), ",
                        "par_strips_witness_p_star env (KExpr.pi a1 b1) (KExpr.pi a2 b2) -> ",
                        "par_strips_witness_p_star env {clhs} {crhs}"
                    ),
                    clhs = clhs,
                    crhs = crhs,
                ),
                value_src: Some(par_p_pi_injectivity_proof(
                    clhs, crhs, meet1, meet2, leg2, pi_inj,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "STEP-5 (#2859): pi injectivity up to proper-parallel confluence ({what}) — from a ",
                        "shared-reduct join witness on pi a1 b1 and pi a2 b2, produce a join witness on the ",
                        "{what}. Project the common reduct e3, Eq-invert both legs via ",
                        "par_reduces_p_star_pi_inv_eq (e3 = pi a1' b1' = pi a2' b2'), read off the {what} ",
                        "equality by {pi_inj} of the trans'd reduct equation, transport the second leg onto the ",
                        "meet, and package via par_strips_witness_p_star.intro. The p-side mirror of ",
                        "par_bd_pi_injectivity_{what} and the analogue of pi-injectivity-for-DefEq (the ",
                        "church_rosser_whnf payload). DerivedProved, zero axiom_deps."
                    ),
                    what = what,
                    pi_inj = pi_inj,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_p_star".to_string(),
                    "par_strips_witness_p_star".to_string(),
                    "par_strips_witness_p_star.rec".to_string(),
                    "par_strips_witness_p_star.intro".to_string(),
                    "par_reduces_p_star_pi_inv_eq".to_string(),
                    pi_inj.to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                    "Eq.substType".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }
}

// =====================================================================
// STEP-5 (#2859) proof terms — p-side mirror of the Wave-142/143 _bd tower.
// =====================================================================

/// Closed proof term for `par_reduces_p_pi_reduct_not_redex` (STEP-5 prerequisite).
/// The pi dual of `par_reduces_p_lam_reduct_not_redex`: from a pi-headed par-step
/// `(pi dom body) ⇒_p t` and a fired iota `iota_step env t r`, derive any `C : Type`.
/// `par_reduces_p.rec` with a source-equation motive universalizing the new redex
/// `(r2, C2)` and threading `iota_step env e' r2 → Empty`. refl/pi/forall_ reducts
/// are pi-headed, so the iota on them is absurd (`iota_step_head_none_absurd_type`
/// on the none head, computed by refl); lam is lam-headed (`lam_ne_pi`),
/// beta/app are app-headed (`app_ne_pi`), the let_ (ZETA) and let_cong arms are
/// let_-headed (`let_ne_pi` — a genuine let node is never a pi); the iota_p arm
/// discharges via its OWN IH applied to the constructor's FIRE premise (the reduced
/// sub-redex is again a par-reduct of the pi, hence not a redex).
fn par_reduces_p_pi_reduct_not_redex_proof() -> String {
    // Motive over (e ⇒_p e'): from e = pi dom body, the reduct e' is not a redex for
    // ANY new redex r2 — concluding Empty (Sort 1 = Type, keeping the recursor motive
    // in Type without quantifying over an arbitrary Type C2). The outer wrapper turns
    // Empty into any C via Empty.rec.
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p env e e') => ",
        "Eq KExpr e (KExpr.pi dom body) -> ",
        "forall (r2 : KExpr), iota_step env e' r2 -> Empty)"
    );
    // The IH shape for a sub-derivation SUB ⇒ SUB'.
    let ih = concat!(
        "Eq KExpr SUB (KExpr.pi dom body) -> ",
        "forall (r2 : KExpr), iota_step env SUB' r2 -> Empty"
    );

    // Discharge a pi-headed reduct PIRED: iota_step env PIRED r2 (named HIN) is
    // absurd (kexpr_const_name (kapp_fn PIRED) = none, by refl on a pi head). Empty as
    // the Type-valued discharge target.
    let pi_head_discharge = |pired: &str, hin: &str| -> String {
        format!(
            concat!(
                "(iota_step_head_none_absurd_type env {pired} r2 Empty ",
                "(Eq.refl (OptionType Name) (kexpr_const_name (kapp_fn {pired}))) {hin})"
            ),
            pired = pired,
            hin = hin,
        )
    };

    // refl: reduct e; rewrite e -> pi dom body, the reduct is the pi (pi-headed).
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.pi dom body)) ",
            "(r2 : KExpr) (hi2 : iota_step env e r2) => ",
            "Eq.substType KExpr ",
            "(fun (x : KExpr) => iota_step env x r2 -> Empty) ",
            "(KExpr.pi dom body) e ",
            "(Eq.symm KExpr e (KExpr.pi dom body) eq) ",
            "(fun (hi3 : iota_step env (KExpr.pi dom body) r2) => {discharge}) ",
            "hi2)"
        ),
        discharge = pi_head_discharge("(KExpr.pi dom body)", "hi3"),
    );

    // beta: source app (lam A b0) arg — app /= pi.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_p env A A') (_hb0 : par_reduces_p env b0 b0') ",
            "(_harg : par_reduces_p env arg arg') ",
            "(_ihA : {ih_A}) (_ihb0 : {ih_b0}) (_iharg : {ih_arg}) ",
            "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.pi dom body)) => ",
            "app_ne_pi (KExpr.lam A b0) arg dom body ",
            "(forall (r2 : KExpr), iota_step env (instantiate b0' arg') r2 -> Empty) eq)"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
    );

    // app: source app g b — app /= pi.
    let app_arm = format!(
        concat!(
            "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(_hg : par_reduces_p env g g') (_hb : par_reduces_p env b b') ",
            "(_ihg : {ih_g}) (_ihb : {ih_b}) ",
            "(eq : Eq KExpr (KExpr.app g b) (KExpr.pi dom body)) => ",
            "app_ne_pi g b dom body ",
            "(forall (r2 : KExpr), iota_step env (KExpr.app g' b') r2 -> Empty) eq)"
        ),
        ih_g = ih.replace("SUB'", "g'").replace("SUB", "g"),
        ih_b = ih.replace("SUB'", "b'").replace("SUB", "b"),
    );

    // lam: source lam t0 b0 — lam /= pi.
    let lam_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_ht : par_reduces_p env t0 t0') (_hb : par_reduces_p env b0 b0') ",
            "(_iht : {ih_t0}) (_ihb : {ih_b0}) ",
            "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.pi dom body)) => ",
            "lam_ne_pi t0 b0 dom body ",
            "(forall (r2 : KExpr), iota_step env (KExpr.lam t0' b0') r2 -> Empty) eq)"
        ),
        ih_t0 = ih.replace("SUB'", "t0'").replace("SUB", "t0"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
    );

    // pi: source pi d0 b0 — reduct pi d0' b0' (pi-headed), iota absurd.
    let pi_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_p env d0 d0') (_hb0 : par_reduces_p env b0 b0') ",
            "(_ihd : {ih_d0}) (_ihb0 : {ih_b0}) ",
            "(_eq : Eq KExpr (KExpr.pi d0 b0) (KExpr.pi dom body)) ",
            "(r2 : KExpr) (hi2 : iota_step env (KExpr.pi d0' b0') r2) => {discharge})"
        ),
        ih_d0 = ih.replace("SUB'", "d0'").replace("SUB", "d0"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
        discharge = pi_head_discharge("(KExpr.pi d0' b0')", "hi2"),
    );

    // forall_: source forall_ d0 b0 = pi d0 b0 (alias) — reduct forall_ d0' b0' =
    // pi d0' b0' (pi-headed), iota absurd.
    let forall_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_p env d0 d0') (_hb0 : par_reduces_p env b0 b0') ",
            "(_ihd : {ih_d0}) (_ihb0 : {ih_b0}) ",
            "(_eq : Eq KExpr (KExpr.forall_ d0 b0) (KExpr.pi dom body)) ",
            "(r2 : KExpr) (hi2 : iota_step env (KExpr.forall_ d0' b0') r2) => {discharge})"
        ),
        ih_d0 = ih.replace("SUB'", "d0'").replace("SUB", "d0"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
        discharge = pi_head_discharge("(KExpr.forall_ d0' b0')", "hi2"),
    );

    // let_ (ZETA ctor): source let_ t0 v b0, a GENUINE let node — let_ /= pi
    // (let_ne_pi; the old app(lam)-alias reading is gone).
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : {ih_t0}) (_ihv : {ih_v}) (_ihb0 : {ih_b0}) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.pi dom body)) => ",
            "let_ne_pi t0 v b0 dom body ",
            "(forall (r2 : KExpr), iota_step env (instantiate b0' v') r2 -> Empty) eq)"
        ),
        ih_t0 = ih.replace("SUB'", "t0'").replace("SUB", "t0"),
        ih_v = ih.replace("SUB'", "v'").replace("SUB", "v"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
    );

    // iota_p: source e0 ⇒_p e2 (the FIRE on e2: iota_step env e2 r0; reduct r0). From
    // eq : e0 = pi dom body, the IH says e2 (a par-reduct of the pi) is not a redex;
    // apply it to the FIRE premise (r0, hi0) for Empty — the new outer iota
    // (hi2 : iota_step env r0 r2) is unused.
    let iota_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e2 : KExpr) (r0 : KExpr) ",
            "(_hprem : par_reduces_p env e0 e2) (hi0 : iota_step env e2 r0) ",
            "(ihprem : {ih_e0e2}) ",
            "(eq : Eq KExpr e0 (KExpr.pi dom body)) ",
            "(r2 : KExpr) (_hi2 : iota_step env r0 r2) => ",
            "ihprem eq r0 hi0)"
        ),
        ih_e0e2 = ih.replace("SUB'", "e2").replace("SUB", "e0"),
    );

    // let_cong (trailing congruence ctor): SAME let_-headed source — let_ /= pi
    // (let_ne_pi); only the reduct differs (KExpr.let_ t0' v' b0').
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : {ih_t0}) (_ihv : {ih_v}) (_ihb0 : {ih_b0}) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.pi dom body)) => ",
            "let_ne_pi t0 v b0 dom body ",
            "(forall (r2 : KExpr), iota_step env (KExpr.let_ t0' v' b0') r2 -> Empty) eq)"
        ),
        ih_t0 = ih.replace("SUB'", "t0'").replace("SUB", "t0"),
        ih_v = ih.replace("SUB'", "v'").replace("SUB", "v"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
    );

    // proj arm: source proj s i sub is proj-headed — proj /= pi via proj_ne_pi.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_p env sub sub') ",
            "(_ihsub : {ih_sub}) ",
            "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.pi dom body)) => ",
            "proj_ne_pi s i sub dom body ",
            "(forall (r2 : KExpr), iota_step env (KExpr.proj s i sub') r2 -> Empty) eq)"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
    );

    format!(
        concat!(
            "fun (env : RecEnv) (dom : KExpr) (body : KExpr) (t : KExpr) (r : KExpr) (C : Type) ",
            "(h : par_reduces_p env (KExpr.pi dom body) t) (hi : iota_step env t r) => ",
            "Empty.rec (fun (_e : Empty) => C) ",
            "(par_reduces_p.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.pi dom body) t h (Eq.refl KExpr (KExpr.pi dom body)) r hi)"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_reduces_p_pi_inv_eq` (STEP-5). The pi dual of
/// `par_reduces_p_lam_inv` (Eq-data form), the p-side mirror of
/// `par_reduces_bd_pi_inv_eq` with env threading + the genuine-new PARALLEL-iota arm.
///
/// `Kont(R) := forall dom' body', Eq R (pi dom' body') -> (dom ⇒_p dom') ->
///   (body ⇒_p body') -> C`. `par_reduces_p.rec` with a source-equation motive
/// `Eq e (pi dom body) -> Kont(e') -> C`: the pi and forall_ arms are the genuine
/// matches (forall_ is the reducible pi alias) feeding the continuation at the
/// reduct with `Eq.refl` + the components transported via pi injectivity of the
/// source equation; refl folds in reflexive sub-derivations; lam discharged by
/// `lam_ne_pi`, beta/app by `app_ne_pi`, the let_ (ZETA) and let_cong arms by
/// `let_ne_pi`; the iota_p arm fires on the REDUCED
/// redex `e2` (a par-reduct of the pi via the transported premise), discharged by
/// `par_reduces_p_pi_reduct_not_redex`.
fn par_reduces_p_pi_inv_eq_proof() -> String {
    // Kont(R) := forall dom' body', Eq R (pi dom' body') -> (dom ⇒_p dom') ->
    //   (body ⇒_p body') -> C.
    let kont = |reduct: &str| -> String {
        format!(
            concat!(
                "(forall (dom' : KExpr) (body' : KExpr), ",
                "Eq KExpr {reduct} (KExpr.pi dom' body') -> ",
                "par_reduces_p env dom dom' -> par_reduces_p env body body' -> C)"
            ),
            reduct = reduct,
        )
    };
    let motive = format!(
        concat!(
            "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p env e e') => ",
            "Eq KExpr e (KExpr.pi dom body) -> {kont} -> C)"
        ),
        kont = kont("e'"),
    );

    // refl arm: source e, reduct e. k expects Eq e (pi dom' body'); take dom' = dom,
    // body' = body so the equation is exactly eq, sub-derivs refl.
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.pi dom body)) ",
            "(k : {kont}) => ",
            "k dom body eq (par_reduces_p.refl env dom) (par_reduces_p.refl env body))"
        ),
        kont = kont("e"),
    );

    // beta arm: source app (lam A b0) arg — app /= pi.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_p env A A') (_hb0 : par_reduces_p env b0 b0') ",
            "(_harg : par_reduces_p env arg arg') ",
            "(_ihA : Eq KExpr A (KExpr.pi dom body) -> {kont_A} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(_iharg : Eq KExpr arg (KExpr.pi dom body) -> {kont_arg} -> C) ",
            "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "app_ne_pi (KExpr.lam A b0) arg dom body C eq)"
        ),
        kont_A = kont("A'"),
        kont_b0 = kont("b0'"),
        kont_arg = kont("arg'"),
        kont_red = kont("(instantiate b0' arg')"),
    );

    // app arm: source app g b — app /= pi.
    let app_arm = format!(
        concat!(
            "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(_hg : par_reduces_p env g g') (_hb : par_reduces_p env b b') ",
            "(_ihg : Eq KExpr g (KExpr.pi dom body) -> {kont_g} -> C) ",
            "(_ihb : Eq KExpr b (KExpr.pi dom body) -> {kont_b} -> C) ",
            "(eq : Eq KExpr (KExpr.app g b) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "app_ne_pi g b dom body C eq)"
        ),
        kont_g = kont("g'"),
        kont_b = kont("b'"),
        kont_red = kont("(KExpr.app g' b')"),
    );

    // lam arm: source lam t0 b0 — lam /= pi.
    let lam_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_ht : par_reduces_p env t0 t0') (_hb : par_reduces_p env b0 b0') ",
            "(_iht : Eq KExpr t0 (KExpr.pi dom body) -> {kont_t0} -> C) ",
            "(_ihb : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "lam_ne_pi t0 b0 dom body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.lam t0' b0')"),
    );

    // pi arm: source pi d0 b0, reduct pi d0' b0' — the genuine match. k receives
    // Eq.refl for the reduct equation and the sub-derivations transported from d0/b0
    // to dom/body via pi injectivity of eq.
    let pi_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(hd : par_reduces_p env d0 d0') (hb : par_reduces_p env b0 b0') ",
            "(_ihd : Eq KExpr d0 (KExpr.pi dom body) -> {kont_d} -> C) ",
            "(_ihb : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.pi d0 b0) (KExpr.pi dom body)) ",
            "(k : {kont_red}) => ",
            "k d0' b0' (Eq.refl KExpr (KExpr.pi d0' b0')) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x d0') d0 dom ",
            "(pi_inj_fst d0 b0 dom body eq) hd) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x b0') b0 body ",
            "(pi_inj_snd d0 b0 dom body eq) hb))"
        ),
        kont_d = kont("d0'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.pi d0' b0')"),
    );

    // forall_ arm: source forall_ d0 b0 = pi d0 b0 (alias), reduct forall_ d0' b0' =
    // pi d0' b0' — also a genuine match. The reduct equality is Eq.refl at the
    // pi-normalized reduct (the kernel unfolds forall_ -> pi), and eq feeds
    // pi_inj_fst/snd directly.
    let forall_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(hd : par_reduces_p env d0 d0') (hb : par_reduces_p env b0 b0') ",
            "(_ihd : Eq KExpr d0 (KExpr.pi dom body) -> {kont_d} -> C) ",
            "(_ihb : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.forall_ d0 b0) (KExpr.pi dom body)) ",
            "(k : {kont_red}) => ",
            "k d0' b0' (Eq.refl KExpr (KExpr.pi d0' b0')) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x d0') d0 dom ",
            "(pi_inj_fst d0 b0 dom body eq) hd) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x b0') b0 body ",
            "(pi_inj_snd d0 b0 dom body eq) hb))"
        ),
        kont_d = kont("d0'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.forall_ d0' b0')"),
    );

    // let_ arm (ZETA ctor): source let_ t0 v b0, a GENUINE let node — let_ /= pi
    // (let_ne_pi; the old app(lam)-alias reading is gone).
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.pi dom body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v (KExpr.pi dom body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "let_ne_pi t0 v b0 dom body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(instantiate b0' v')"),
    );

    // iota_p arm: source e0 ⇒_p e2 then iota_step e2 r. The iota fires on e2, NOT e0.
    // e2 is a par-reduct of (pi dom body) (transport hprem along eq), so by
    // par_reduces_p_pi_reduct_not_redex it is not a redex — discharging the fired iota
    // on e2 and yielding C directly (the continuation _k is irrelevant).
    let iota_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e2 : KExpr) (r : KExpr) ",
            "(hprem : par_reduces_p env e0 e2) (hi : iota_step env e2 r) ",
            "(_ihprem : Eq KExpr e0 (KExpr.pi dom body) -> {kont_e2} -> C) ",
            "(eq : Eq KExpr e0 (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "par_reduces_p_pi_reduct_not_redex env dom body e2 r C ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x e2) e0 (KExpr.pi dom body) eq hprem) ",
            "hi)"
        ),
        kont_e2 = kont("e2"),
        kont_red = kont("r"),
    );

    // let_cong arm (trailing congruence ctor): SAME let_-headed source — let_ /= pi
    // (let_ne_pi); only the reduct differs (KExpr.let_ t0' v' b0').
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.pi dom body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v (KExpr.pi dom body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.pi dom body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "let_ne_pi t0 v b0 dom body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.let_ t0' v' b0')"),
    );

    // proj arm: source proj s i sub is proj-headed — proj /= pi via proj_ne_pi.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_p env sub sub') ",
            "(_ihsub : Eq KExpr sub (KExpr.pi dom body) -> {kont_sub} -> C) ",
            "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.pi dom body)) ",
            "(_k : {kont_red}) => ",
            "proj_ne_pi s i sub dom body C eq)"
        ),
        kont_sub = kont("sub'"),
        kont_red = kont("(KExpr.proj s i sub')"),
    );

    format!(
        concat!(
            "fun (env : RecEnv) (dom : KExpr) (body : KExpr) (t : KExpr) (C : Type) ",
            "(h : par_reduces_p env (KExpr.pi dom body) t) ",
            "(kpi : {kont_t}) => ",
            "par_reduces_p.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.pi dom body) t h (Eq.refl KExpr (KExpr.pi dom body)) kpi"
        ),
        kont_t = kont("t"),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for the star-level pi inversion `par_reduces_p_star_pi_inv`
/// (STEP-5). The p-side mirror of `par_reduces_bd_star_pi_inv` (env threaded).
///
/// Induction on the multi-step derivation `pi dom body ⇒*_p w` via
/// `par_reduces_p_star.rec` with an ACCUMULATOR motive that carries, for the current
/// source `s`, the witness `Eq s (pi A B)` plus the accumulated prefixes
/// `dom ⇒*_p A` and `body ⇒*_p B`. The refl arm hands the continuation the
/// accumulated prefixes (transporting `C (pi A B)` onto `C s` via `eq.symm`); the
/// step arm transports the single step onto `pi A B`, Eq-inverts it via
/// `par_reduces_p_pi_inv_eq` to `e' = pi A' B'` with `A ⇒_p A'`, `B ⇒_p B'`, extends
/// the prefixes through `par_reduces_p_star_trans` + `par_subsumes_par_p_star`, and
/// recurses via the IH. The `par_reduces_p_star` recursor has no iota arm (the iota
/// is internal to the single steps, discharged inside `par_reduces_p_pi_inv_eq`).
fn par_reduces_p_star_pi_inv_proof() -> String {
    // Accumulator motive: M s r _ := forall A B, Eq s (pi A B) -> dom ⇒*_p A ->
    //   body ⇒*_p B -> C r.
    let motive = concat!(
        "(fun (s : KExpr) (r : KExpr) (_h : par_reduces_p_star env s r) => ",
        "forall (A : KExpr) (B : KExpr), Eq KExpr s (KExpr.pi A B) -> ",
        "par_reduces_p_star env dom A -> par_reduces_p_star env body B -> C r)"
    );
    // refl arm (s = r = e): hand kpi the accumulated prefixes at C (pi A B),
    // transported onto C e via eq.symm.
    let refl_arm = concat!(
        "(fun (e : KExpr) => ",
        "fun (A : KExpr) (B : KExpr) (eq : Eq KExpr e (KExpr.pi A B)) ",
        "(hd : par_reduces_p_star env dom A) (hb : par_reduces_p_star env body B) => ",
        "Eq.substType KExpr C (KExpr.pi A B) e ",
        "(Eq.symm KExpr e (KExpr.pi A B) eq) (kpi A B hd hb))"
    );
    // step arm: hstep : e ⇒_p e', _htail : e' ⇒*_p e'', ih : forall A B,
    //   Eq e' (pi A B) -> dom ⇒*_p A -> body ⇒*_p B -> C e''. Transport hstep onto
    //   pi A B, Eq-invert via par_reduces_p_pi_inv_eq to e' = pi A' B' with A ⇒_p A',
    //   B ⇒_p B', extend the prefixes, recurse via ih.
    let step_arm = concat!(
        "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
        "(hstep : par_reduces_p env e e') ",
        "(_htail : par_reduces_p_star env e' e'') ",
        "(ih : forall (A : KExpr) (B : KExpr), Eq KExpr e' (KExpr.pi A B) -> ",
        "par_reduces_p_star env dom A -> par_reduces_p_star env body B -> C e'') => ",
        "fun (A : KExpr) (B : KExpr) (eq : Eq KExpr e (KExpr.pi A B)) ",
        "(hd : par_reduces_p_star env dom A) (hb : par_reduces_p_star env body B) => ",
        "par_reduces_p_pi_inv_eq env A B e' (C e'') ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x e') e (KExpr.pi A B) eq hstep) ",
        "(fun (A' : KExpr) (B' : KExpr) (eq' : Eq KExpr e' (KExpr.pi A' B')) ",
        "(hAA' : par_reduces_p env A A') (hBB' : par_reduces_p env B B') => ",
        "ih A' B' eq' ",
        "(par_reduces_p_star_trans env dom A A' hd (par_subsumes_par_p_star env A A' hAA')) ",
        "(par_reduces_p_star_trans env body B B' hb (par_subsumes_par_p_star env B B' hBB'))))"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (dom : KExpr) (body : KExpr) (w : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_p_star env (KExpr.pi dom body) w) ",
            "(kpi : forall (dom' : KExpr) (body' : KExpr), ",
            "par_reduces_p_star env dom dom' -> par_reduces_p_star env body body' -> ",
            "C (KExpr.pi dom' body')) => ",
            "par_reduces_p_star.rec env {motive} {refl_arm} {step_arm} ",
            "(KExpr.pi dom body) w h ",
            "dom body (Eq.refl KExpr (KExpr.pi dom body)) ",
            "(par_reduces_p_star.refl env dom) (par_reduces_p_star.refl env body)"
        ),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Closed proof term for the Eq-data star pi inversion `par_reduces_p_star_pi_inv_eq`
/// (STEP-5). The p-side mirror of `par_reduces_bd_star_pi_inv_eq` (env threaded).
///
/// Derived from the KExpr-indexed `par_reduces_p_star_pi_inv` by instantiating its
/// motive at `M(ww) := Eq w ww -> C`: the inversion then returns `Eq w w -> C`, which
/// `Eq.refl w` discharges to `C`, and inside the inversion's continuation the reduct
/// equality `Eq w (pi dom' body')` is in scope and handed straight to the caller's
/// continuation `k`.
fn par_reduces_p_star_pi_inv_eq_proof() -> String {
    concat!(
        "fun (env : RecEnv) (dom : KExpr) (body : KExpr) (w : KExpr) (C : Type) ",
        "(h : par_reduces_p_star env (KExpr.pi dom body) w) ",
        "(k : forall (dom' : KExpr) (body' : KExpr), ",
        "Eq KExpr w (KExpr.pi dom' body') -> ",
        "par_reduces_p_star env dom dom' -> par_reduces_p_star env body body' -> C) => ",
        "par_reduces_p_star_pi_inv env dom body w ",
        "(fun (ww : KExpr) => Eq KExpr w ww -> C) h ",
        "(fun (dom' : KExpr) (body' : KExpr) ",
        "(hd : par_reduces_p_star env dom dom') (hb : par_reduces_p_star env body body') => ",
        "fun (eqw : Eq KExpr w (KExpr.pi dom' body')) => k dom' body' eqw hd hb) ",
        "(Eq.refl KExpr w)"
    )
    .to_string()
}

/// Closed proof term for the pi-injectivity-up-to-confluence lemmas
/// `par_p_pi_injectivity_dom` / `par_p_pi_injectivity_cod` (STEP-5), parametric in
/// the component projected. The p-side mirror of `par_bd_pi_injectivity_proof` (env
/// threaded).
///
/// From a shared-reduct join witness `par_strips_witness_p_star env (pi a1 b1)
/// (pi a2 b2)`, project the common reduct `e3` with `pi a1 b1 ⇒*_p e3` and
/// `pi a2 b2 ⇒*_p e3`. Eq-invert both legs (`par_reduces_p_star_pi_inv_eq`):
/// `eq1 : e3 = pi a1' b1'` with `a1 ⇒*_p a1'`, `b1 ⇒*_p b1'`, and `eq2 : e3 =
/// pi a2' b2'` with `a2 ⇒*_p a2'`, `b2 ⇒*_p b2'`. Then `pi a1' b1' = pi a2' b2'` by
/// `Eq.trans (Eq.symm eq1) eq2`, so the projected components are equal (`pi_inj_fst`
/// for the domain, `pi_inj_snd` for the codomain); transport the second leg onto the
/// first's meet and package via `par_strips_witness_p_star.intro`.
///
/// `clhs`/`crhs` are the conclusion's two terms (`a1`/`a2` or `b1`/`b2`),
/// `meet1`/`meet2` the recovered meet points (`a1'`/`a2'` or `b1'`/`b2'`), `leg2` the
/// recovered second-leg prefix derivation (`hda2` or `hdb2`), and `pi_inj` the
/// projection (`pi_inj_fst`/`pi_inj_snd`).
fn par_p_pi_injectivity_proof(
    clhs: &str,
    crhs: &str,
    meet1: &str,
    meet2: &str,
    leg2: &str,
    pi_inj: &str,
) -> String {
    // Inner continuation (after inverting the second leg p2): identify the meet by
    // pi injectivity of the trans'd reduct equation, transport leg2 onto it, and
    // package the join witness at meet1.
    let inner_k = format!(
        concat!(
            "(fun (a2' : KExpr) (b2' : KExpr) (eq2 : Eq KExpr e3 (KExpr.pi a2' b2')) ",
            "(hda2 : par_reduces_p_star env a2 a2') (hdb2 : par_reduces_p_star env b2 b2') => ",
            "par_strips_witness_p_star.intro env {clhs} {crhs} {meet1} {leg1} ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p_star env {crhs} x) {meet2} {meet1} ",
            "(Eq.symm KExpr {meet1} {meet2} ",
            "({pi_inj} a1' b1' a2' b2' ",
            "(Eq.trans KExpr (KExpr.pi a1' b1') e3 (KExpr.pi a2' b2') ",
            "(Eq.symm KExpr e3 (KExpr.pi a1' b1') eq1) eq2))) ",
            "{leg2}))"
        ),
        clhs = clhs,
        crhs = crhs,
        meet1 = meet1,
        meet2 = meet2,
        leg1 = if pi_inj == "pi_inj_fst" { "hda1" } else { "hdb1" },
        leg2 = leg2,
        pi_inj = pi_inj,
    );
    // Outer continuation (after inverting the first leg p1): invert p2 at the same
    // reduct e3.
    let outer_k = format!(
        concat!(
            "(fun (a1' : KExpr) (b1' : KExpr) (eq1 : Eq KExpr e3 (KExpr.pi a1' b1')) ",
            "(hda1 : par_reduces_p_star env a1 a1') (hdb1 : par_reduces_p_star env b1 b1') => ",
            "par_reduces_p_star_pi_inv_eq env a2 b2 e3 ",
            "(par_strips_witness_p_star env {clhs} {crhs}) p2 {inner_k})"
        ),
        clhs = clhs,
        crhs = crhs,
        inner_k = inner_k,
    );
    format!(
        concat!(
            "fun (env : RecEnv) (a1 : KExpr) (b1 : KExpr) (a2 : KExpr) (b2 : KExpr) ",
            "(w : par_strips_witness_p_star env (KExpr.pi a1 b1) (KExpr.pi a2 b2)) => ",
            "@par_strips_witness_p_star.rec env (KExpr.pi a1 b1) (KExpr.pi a2 b2) ",
            "(fun (_w : par_strips_witness_p_star env (KExpr.pi a1 b1) (KExpr.pi a2 b2)) => ",
            "par_strips_witness_p_star env {clhs} {crhs}) ",
            "(fun (e3 : KExpr) ",
            "(p1 : par_reduces_p_star env (KExpr.pi a1 b1) e3) ",
            "(p2 : par_reduces_p_star env (KExpr.pi a2 b2) e3) => ",
            "par_reduces_p_star_pi_inv_eq env a1 b1 e3 ",
            "(par_strips_witness_p_star env {clhs} {crhs}) p1 {outer_k}) ",
            "w"
        ),
        clhs = clhs,
        crhs = crhs,
        outer_k = outer_k,
    )
}

// =====================================================================
// STEP-5 (#2859) lam-dual proof terms — lam swap of the pi tower above.
// =====================================================================

/// Closed proof term for `par_reduces_p_lam_inv_eq` (STEP-5 lam dual). The Eq-data
/// sibling of the landed (CPS) `par_reduces_p_lam_inv` and the lam swap of
/// `par_reduces_p_pi_inv_eq` — the analogue of `par_reduces_bd_lam_inv_eq`.
fn par_reduces_p_lam_inv_eq_proof() -> String {
    // Kont(R) := forall ty' body', Eq R (lam ty' body') -> (ty ⇒_p ty') ->
    //   (body ⇒_p body') -> C.
    let kont = |reduct: &str| -> String {
        format!(
            concat!(
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "Eq KExpr {reduct} (KExpr.lam ty' body') -> ",
                "par_reduces_p env ty ty' -> par_reduces_p env body body' -> C)"
            ),
            reduct = reduct,
        )
    };
    let motive = format!(
        concat!(
            "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p env e e') => ",
            "Eq KExpr e (KExpr.lam ty body) -> {kont} -> C)"
        ),
        kont = kont("e'"),
    );

    // refl arm: source e, reduct e. ty' = ty, body' = body so the equation is eq.
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.lam ty body)) ",
            "(k : {kont}) => ",
            "k ty body eq (par_reduces_p.refl env ty) (par_reduces_p.refl env body))"
        ),
        kont = kont("e"),
    );

    // beta arm: source app (lam A b0) arg — app /= lam.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_p env A A') (_hb0 : par_reduces_p env b0 b0') ",
            "(_harg : par_reduces_p env arg arg') ",
            "(_ihA : Eq KExpr A (KExpr.lam ty body) -> {kont_A} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(_iharg : Eq KExpr arg (KExpr.lam ty body) -> {kont_arg} -> C) ",
            "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "app_ne_lam (KExpr.lam A b0) arg ty body C eq)"
        ),
        kont_A = kont("A'"),
        kont_b0 = kont("b0'"),
        kont_arg = kont("arg'"),
        kont_red = kont("(instantiate b0' arg')"),
    );

    // app arm: source app g b — app /= lam.
    let app_arm = format!(
        concat!(
            "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(_hg : par_reduces_p env g g') (_hb : par_reduces_p env b b') ",
            "(_ihg : Eq KExpr g (KExpr.lam ty body) -> {kont_g} -> C) ",
            "(_ihb : Eq KExpr b (KExpr.lam ty body) -> {kont_b} -> C) ",
            "(eq : Eq KExpr (KExpr.app g b) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "app_ne_lam g b ty body C eq)"
        ),
        kont_g = kont("g'"),
        kont_b = kont("b'"),
        kont_red = kont("(KExpr.app g' b')"),
    );

    // lam arm: source lam t0 b0, reduct lam t0' b0' — the genuine match.
    let lam_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(ht : par_reduces_p env t0 t0') (hb : par_reduces_p env b0 b0') ",
            "(_iht : Eq KExpr t0 (KExpr.lam ty body) -> {kont_t0} -> C) ",
            "(_ihb : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.lam ty body)) ",
            "(k : {kont_red}) => ",
            "k t0' b0' (Eq.refl KExpr (KExpr.lam t0' b0')) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x t0') t0 ty ",
            "(lam_inj_fst t0 b0 ty body eq) ht) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x b0') b0 body ",
            "(lam_inj_snd t0 b0 ty body eq) hb))"
        ),
        kont_t0 = kont("t0'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.lam t0' b0')"),
    );

    // pi arm: source pi d0 b0 — pi /= lam.
    let pi_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_p env d0 d0') (_hb0 : par_reduces_p env b0 b0') ",
            "(_ihd : Eq KExpr d0 (KExpr.lam ty body) -> {kont_d} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.pi d0 b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "pi_ne_lam d0 b0 ty body C eq)"
        ),
        kont_d = kont("d0'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.pi d0' b0')"),
    );

    // forall_ arm: source forall_ d0 b0 = pi d0 b0 (alias) — pi /= lam.
    let forall_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_p env d0 d0') (_hb0 : par_reduces_p env b0 b0') ",
            "(_ihd : Eq KExpr d0 (KExpr.lam ty body) -> {kont_d} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.forall_ d0 b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "pi_ne_lam d0 b0 ty body C eq)"
        ),
        kont_d = kont("d0'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.forall_ d0' b0')"),
    );

    // let_ arm (ZETA ctor): source let_ t0 v b0, a GENUINE let node — let_ /= lam
    // (let_ne_lam; the old app(lam)-alias reading is gone).
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v (KExpr.lam ty body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "let_ne_lam t0 v b0 ty body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(instantiate b0' v')"),
    );

    // iota_p arm: source e0 ⇒_p e2 then iota_step e2 r. e2 is a par-reduct of
    // (lam ty body), so par_reduces_p_lam_reduct_not_redex discharges the fired iota.
    let iota_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e2 : KExpr) (r : KExpr) ",
            "(hprem : par_reduces_p env e0 e2) (hi : iota_step env e2 r) ",
            "(_ihprem : Eq KExpr e0 (KExpr.lam ty body) -> {kont_e2} -> C) ",
            "(eq : Eq KExpr e0 (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "par_reduces_p_lam_reduct_not_redex env ty body e2 r C ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x e2) e0 (KExpr.lam ty body) eq hprem) ",
            "hi)"
        ),
        kont_e2 = kont("e2"),
        kont_red = kont("r"),
    );

    // let_cong arm (trailing congruence ctor): SAME let_-headed source — let_ /= lam
    // (let_ne_lam); only the reduct differs (KExpr.let_ t0' v' b0').
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v (KExpr.lam ty body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "let_ne_lam t0 v b0 ty body C eq)"
        ),
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.let_ t0' v' b0')"),
    );

    // proj arm: source proj s i sub is proj-headed — proj /= lam via proj_ne_lam.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_p env sub sub') ",
            "(_ihsub : Eq KExpr sub (KExpr.lam ty body) -> {kont_sub} -> C) ",
            "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.lam ty body)) ",
            "(_k : {kont_red}) => ",
            "proj_ne_lam s i sub ty body C eq)"
        ),
        kont_sub = kont("sub'"),
        kont_red = kont("(KExpr.proj s i sub')"),
    );

    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : Type) ",
            "(h : par_reduces_p env (KExpr.lam ty body) t) ",
            "(klam : {kont_t}) => ",
            "par_reduces_p.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.lam ty body) t h (Eq.refl KExpr (KExpr.lam ty body)) klam"
        ),
        kont_t = kont("t"),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for the star-level lam inversion `par_reduces_p_star_lam_inv`
/// (STEP-5 lam dual). lam swap of `par_reduces_p_star_pi_inv_proof`.
fn par_reduces_p_star_lam_inv_proof() -> String {
    let motive = concat!(
        "(fun (s : KExpr) (r : KExpr) (_h : par_reduces_p_star env s r) => ",
        "forall (A : KExpr) (B : KExpr), Eq KExpr s (KExpr.lam A B) -> ",
        "par_reduces_p_star env ty A -> par_reduces_p_star env body B -> C r)"
    );
    let refl_arm = concat!(
        "(fun (e : KExpr) => ",
        "fun (A : KExpr) (B : KExpr) (eq : Eq KExpr e (KExpr.lam A B)) ",
        "(hd : par_reduces_p_star env ty A) (hb : par_reduces_p_star env body B) => ",
        "Eq.substType KExpr C (KExpr.lam A B) e ",
        "(Eq.symm KExpr e (KExpr.lam A B) eq) (klam A B hd hb))"
    );
    let step_arm = concat!(
        "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
        "(hstep : par_reduces_p env e e') ",
        "(_htail : par_reduces_p_star env e' e'') ",
        "(ih : forall (A : KExpr) (B : KExpr), Eq KExpr e' (KExpr.lam A B) -> ",
        "par_reduces_p_star env ty A -> par_reduces_p_star env body B -> C e'') => ",
        "fun (A : KExpr) (B : KExpr) (eq : Eq KExpr e (KExpr.lam A B)) ",
        "(hd : par_reduces_p_star env ty A) (hb : par_reduces_p_star env body B) => ",
        "par_reduces_p_lam_inv_eq env A B e' (C e'') ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x e') e (KExpr.lam A B) eq hstep) ",
        "(fun (A' : KExpr) (B' : KExpr) (eq' : Eq KExpr e' (KExpr.lam A' B')) ",
        "(hAA' : par_reduces_p env A A') (hBB' : par_reduces_p env B B') => ",
        "ih A' B' eq' ",
        "(par_reduces_p_star_trans env ty A A' hd (par_subsumes_par_p_star env A A' hAA')) ",
        "(par_reduces_p_star_trans env body B B' hb (par_subsumes_par_p_star env B B' hBB'))))"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (body : KExpr) (w : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_p_star env (KExpr.lam ty body) w) ",
            "(klam : forall (ty' : KExpr) (body' : KExpr), ",
            "par_reduces_p_star env ty ty' -> par_reduces_p_star env body body' -> ",
            "C (KExpr.lam ty' body')) => ",
            "par_reduces_p_star.rec env {motive} {refl_arm} {step_arm} ",
            "(KExpr.lam ty body) w h ",
            "ty body (Eq.refl KExpr (KExpr.lam ty body)) ",
            "(par_reduces_p_star.refl env ty) (par_reduces_p_star.refl env body)"
        ),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Closed proof term for the Eq-data star lam inversion
/// `par_reduces_p_star_lam_inv_eq` (STEP-5 lam dual). lam swap of
/// `par_reduces_p_star_pi_inv_eq_proof`.
fn par_reduces_p_star_lam_inv_eq_proof() -> String {
    concat!(
        "fun (env : RecEnv) (ty : KExpr) (body : KExpr) (w : KExpr) (C : Type) ",
        "(h : par_reduces_p_star env (KExpr.lam ty body) w) ",
        "(k : forall (ty' : KExpr) (body' : KExpr), ",
        "Eq KExpr w (KExpr.lam ty' body') -> ",
        "par_reduces_p_star env ty ty' -> par_reduces_p_star env body body' -> C) => ",
        "par_reduces_p_star_lam_inv env ty body w ",
        "(fun (ww : KExpr) => Eq KExpr w ww -> C) h ",
        "(fun (ty' : KExpr) (body' : KExpr) ",
        "(hd : par_reduces_p_star env ty ty') (hb : par_reduces_p_star env body body') => ",
        "fun (eqw : Eq KExpr w (KExpr.lam ty' body')) => k ty' body' eqw hd hb) ",
        "(Eq.refl KExpr w)"
    )
    .to_string()
}

/// Closed proof term for the lam-injectivity-up-to-confluence lemmas
/// `par_p_lam_injectivity_dom` / `par_p_lam_injectivity_cod` (STEP-5 lam dual). lam
/// swap of `par_p_pi_injectivity_proof`.
fn par_p_lam_injectivity_proof(
    clhs: &str,
    crhs: &str,
    meet1: &str,
    meet2: &str,
    leg2: &str,
    lam_inj: &str,
) -> String {
    let inner_k = format!(
        concat!(
            "(fun (a2' : KExpr) (b2' : KExpr) (eq2 : Eq KExpr e3 (KExpr.lam a2' b2')) ",
            "(hda2 : par_reduces_p_star env a2 a2') (hdb2 : par_reduces_p_star env b2 b2') => ",
            "par_strips_witness_p_star.intro env {clhs} {crhs} {meet1} {leg1} ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p_star env {crhs} x) {meet2} {meet1} ",
            "(Eq.symm KExpr {meet1} {meet2} ",
            "({lam_inj} a1' b1' a2' b2' ",
            "(Eq.trans KExpr (KExpr.lam a1' b1') e3 (KExpr.lam a2' b2') ",
            "(Eq.symm KExpr e3 (KExpr.lam a1' b1') eq1) eq2))) ",
            "{leg2}))"
        ),
        clhs = clhs,
        crhs = crhs,
        meet1 = meet1,
        meet2 = meet2,
        leg1 = if lam_inj == "lam_inj_fst" { "hda1" } else { "hdb1" },
        leg2 = leg2,
        lam_inj = lam_inj,
    );
    let outer_k = format!(
        concat!(
            "(fun (a1' : KExpr) (b1' : KExpr) (eq1 : Eq KExpr e3 (KExpr.lam a1' b1')) ",
            "(hda1 : par_reduces_p_star env a1 a1') (hdb1 : par_reduces_p_star env b1 b1') => ",
            "par_reduces_p_star_lam_inv_eq env a2 b2 e3 ",
            "(par_strips_witness_p_star env {clhs} {crhs}) p2 {inner_k})"
        ),
        clhs = clhs,
        crhs = crhs,
        inner_k = inner_k,
    );
    format!(
        concat!(
            "fun (env : RecEnv) (a1 : KExpr) (b1 : KExpr) (a2 : KExpr) (b2 : KExpr) ",
            "(w : par_strips_witness_p_star env (KExpr.lam a1 b1) (KExpr.lam a2 b2)) => ",
            "@par_strips_witness_p_star.rec env (KExpr.lam a1 b1) (KExpr.lam a2 b2) ",
            "(fun (_w : par_strips_witness_p_star env (KExpr.lam a1 b1) (KExpr.lam a2 b2)) => ",
            "par_strips_witness_p_star env {clhs} {crhs}) ",
            "(fun (e3 : KExpr) ",
            "(p1 : par_reduces_p_star env (KExpr.lam a1 b1) e3) ",
            "(p2 : par_reduces_p_star env (KExpr.lam a2 b2) e3) => ",
            "par_reduces_p_star_lam_inv_eq env a1 b1 e3 ",
            "(par_strips_witness_p_star env {clhs} {crhs}) p1 {outer_k}) ",
            "w"
        ),
        clhs = clhs,
        crhs = crhs,
        outer_k = outer_k,
    )
}

#[cfg(test)]
mod tests {
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::Specification;

    /// Build the substitution subset of the spec (matches build_par_test_spec in
    /// par_reduction_tests.rs). The STEP-5 pi-inversion/injectivity tower is in the
    /// substitution bundle (its stage carries `in_substitution: true`), so reaching
    /// this builder IS the kernel-check witness: the closed proof terms were
    /// type-checked by `add_decl` during spec construction, so an ill-typed or faked
    /// term would have failed `new_substitution_test_spec()` before any assertion ran.
    fn build_spec() -> Specification {
        crate::test_utils::build_substitution_spec_with_stack()
    }

    /// STEP-5 (#2859): the pi shape-inversion + injectivity lemmas for
    /// `par_reduces_p` / `par_reduces_p_star` are DerivedProved closed terms with an
    /// empty axiom closure (genuine 0-axiom, not a masquerade).
    #[test]
    fn test_par_reduces_p_pi_injectivity_is_zero_axiom_derived_proved() {
        let spec = build_spec();
        for name in [
            "par_reduces_p_pi_reduct_not_redex",
            "par_reduces_p_pi_inv_eq",
            "par_reduces_p_star_pi_inv",
            "par_reduces_p_star_pi_inv_eq",
            "par_p_pi_injectivity_dom",
            "par_p_pi_injectivity_cod",
            "par_reduces_p_lam_inv_eq",
            "par_reduces_p_star_lam_inv",
            "par_reduces_p_star_lam_inv_eq",
            "par_p_lam_injectivity_dom",
            "par_p_lam_injectivity_cod",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(!def.is_axiom, "{name} should not be an axiom");
            assert_eq!(
                def.category,
                AxiomCategory::DerivedLemma,
                "{name} should be a DerivedLemma"
            );
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved (closed, kernel-checked term)"
            );
            assert!(
                def.value_src.is_some(),
                "{name} should carry a closed proof term"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must have an EMPTY axiom closure (genuine 0-axiom): {:?}",
                def.axiom_deps
            );
        }
    }
}
