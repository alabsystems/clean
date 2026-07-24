// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! #2859 (church_rosser_whnf-deletion): the I-HALF (join witness -> injectivity)
//! over the δ-carrying computational parallel reduction `par_reduces_cd` and its
//! reflexive-transitive closure `par_reduces_cd_star`.
//!
//! This module MIRRORS the landed p-side injectivity tower
//! (`par_reduces_p_injectivity.rs`, the `par_p_pi_injectivity_dom/_cod`) onto the
//! 3-way (β+ι+δ) relation `par_reduces_cd`. The landed 3-way Church-Rosser
//! (`par_reduces_cd_star_diamond_of_sc`) outputs `par_strips_witness_cd_star` (a
//! common reduct via `par_reduces_cd_star` legs); this tower turns that JOIN witness
//! into the structural INJECTIVITY consequence: a join on `Π A B` / `Π A' B'`
//! (resp. `λ`, resp. `Sort`) descends to a join on the components (resp. an equality
//! of sorts). This is the structural confluence CONSEQUENCE half — NOT
//! soundness-sensitive — required because the p-side I-half does NOT compose with the
//! cd-relation CR (cd carries δ), so it must be re-mirrored over the cd relation.
//!
//! ## Why the cd-side single-step inversion is SIMPLER than the p-side
//!
//! `par_reduces_cd`'s `iota` / `delta` constructors are ATOMIC — they fire DIRECTLY
//! on the source `e` (`iota_step (red_rec env) e e'` / `delta_step (red_def env) e
//! e'`), with no nested `par_reduces_cd` premise. (The PROPER parallel relation
//! `par_reduces_p`'s `iota_p` instead fires on a par-REDUCT, which forced the
//! `par_reduces_p_pi_reduct_not_redex` prerequisite.) So a `Π`/`λ`/`Sort`-headed
//! source directly contradicts iota/delta via `iota_step_head_none_absurd_type` /
//! `delta_step_head_none_absurd_type` (the head const name of a binder/sort is
//! `none`). No `_reduct_not_redex` prerequisite is needed on the cd side.
//!
//! Π/`Sort` are RIGID under β+ι+δ (no reduction fires at a Π/`Sort` head — they are
//! values; δ fires only on const-headed app-spines, β on lam-apps, ι on
//! recursor-spines), and `λ` reduces only its components. The lemmas it lands:
//!   * `par_reduces_cd_pi_inv_eq` / `par_reduces_cd_lam_inv_eq` — single-step Eq-data
//!     shape inversion (mirror of `par_reduces_p_pi_inv_eq` / `_lam_inv_eq`).
//!   * `par_reduces_cd_star_pi_inv` / `_eq`, `par_reduces_cd_star_lam_inv` / `_eq` —
//!     star-level shape inversion (mirror of `par_reduces_p_star_pi_inv` / `_lam_inv`).
//!   * `par_cd_pi_injectivity_dom` / `_cod`, `par_cd_lam_injectivity_dom` / `_cod` —
//!     binder injectivity up to confluence (mirror of `par_p_pi_injectivity_*`).
//!   * `par_reduces_cd_sort_inv_eq` (single + star) + `par_cd_sort_injectivity` — the
//!     NEW sort tower (the p-side lacks it): `Sort` is rigid, so the join forces the
//!     two sorts equal.
//!
//! All DerivedProved, zero axiom_deps (genuine 0-axiom: closure ⊆ FOUNDATIONAL ∪
//! FoundationalRule; the RecEnv/DefEnv interfaces remain HYPOTHESES, not axioms).
//! Runs after `add_par_reduces_cd_hr_compose` (`par_strips_witness_cd_star`) and
//! `add_par_reduces_pd` (`par_reduces_cd_star` + trans + `par_subsumes_par_cd_star`).
//! Part of #2859 (church_rosser_whnf-deletion, the cd-relation I-half).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Wire the cd-relation join-witness -> injectivity (I-half) tower. Runs after
    /// `add_par_reduces_cd_hr_compose` (par_strips_witness_cd_star landed) and
    /// `add_par_reduces_pd` (par_reduces_cd_star substrate landed).
    pub(super) fn add_par_reduces_cd_injectivity(&mut self) -> Result<(), SpecError> {
        self.add_par_reduces_cd_inv_single()?;
        self.add_par_reduces_cd_star_inv()?;
        self.add_par_cd_binder_injectivity()?;
        self.add_par_cd_sort_injectivity()?;
        Ok(())
    }

    /// Brick 1 (single-step layer): the Eq-data single-step pi / lam inversions
    /// `par_reduces_cd_pi_inv_eq` / `par_reduces_cd_lam_inv_eq`. From a pi-/lam-headed
    /// atomic 3-way step, hand the continuation the reduct equality + the component
    /// par-steps. Mirror of `par_reduces_p_pi_inv_eq` / `_lam_inv_eq` — but the
    /// PARALLEL-iota arm splits into the cd `iota` and `delta` arms, each ATOMIC on the
    /// (rigid) binder-headed source and so discharged DIRECTLY via the Type-valued
    /// `iota_step_head_none_absurd_type` / `delta_step_head_none_absurd_type` (no
    /// `_reduct_not_redex` prerequisite).
    fn add_par_reduces_cd_inv_single(&mut self) -> Result<(), SpecError> {
        // par_reduces_cd_pi_inv_eq.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_pi_inv_eq".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (dom : KExpr) (body : KExpr) (t : KExpr) (C : Type), ",
                "par_reduces_cd env (KExpr.pi dom body) t -> ",
                "(forall (dom' : KExpr) (body' : KExpr), ",
                "Eq KExpr t (KExpr.pi dom' body') -> ",
                "par_reduces_cd env dom dom' -> par_reduces_cd env body body' -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(par_reduces_cd_binder_inv_eq_proof(BinderInv::Pi)),
            is_axiom: false,
            description: concat!(
                "Eq-data shape recovery for a pi-headed par_reduces_cd — from par_reduces_cd env (pi dom body) ",
                "t, hand the continuation Eq t (pi dom' body') together with dom =>_cd dom' and body =>_cd ",
                "body'. The cd-relation mirror of par_reduces_p_pi_inv_eq: par_reduces_cd.rec with a ",
                "source-equation motive whose continuation Kont is parameterized by the arm reduct. The pi and ",
                "forall_ arms match (forall_ is the reducible pi alias, Eq.refl reduct equation, components ",
                "transported via pi_inj_fst/snd); refl folds in; lam discharged by lam_ne_pi, beta/app by ",
                "app_ne_pi, and the GENUINE let_/let_cong arms by let-vs-pi shape disjointness (let_ne_pi — ",
                "the let_ node is a real 7th ctor now, not the old app (lam) alias); the ATOMIC iota / delta arms fire on the rigid pi-headed source, discharged ",
                "directly via iota_step_head_none_absurd_type / delta_step_head_none_absurd_type (binder head ",
                "const name = none). DerivedProved, zero axiom_deps. Part of #2859 (church_rosser_whnf-deletion, ",
                "cd-relation I-half)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.rec".to_string(),
                "par_reduces_cd.refl".to_string(),
                "iota_step".to_string(),
                "delta_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "delta_step_head_none_absurd_type".to_string(),
                "pi_inj_fst".to_string(),
                "pi_inj_snd".to_string(),
                "app_ne_pi".to_string(),
                "lam_ne_pi".to_string(),
                "let_ne_pi".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_lam_inv_eq (lam swap of the pi inversion).
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_lam_inv_eq".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : Type), ",
                "par_reduces_cd env (KExpr.lam ty body) t -> ",
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "Eq KExpr t (KExpr.lam ty' body') -> ",
                "par_reduces_cd env ty ty' -> par_reduces_cd env body body' -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(par_reduces_cd_binder_inv_eq_proof(BinderInv::Lam)),
            is_axiom: false,
            description: concat!(
                "Eq-data shape recovery for a lam-headed par_reduces_cd — from par_reduces_cd env (lam ty ",
                "body) t, hand the continuation Eq t (lam ty' body') together with ty =>_cd ty' and body =>_cd ",
                "body'. The lam swap of par_reduces_cd_pi_inv_eq (cd-relation mirror of ",
                "par_reduces_p_lam_inv_eq): the lam arm matches (lam_inj_fst/snd); refl folds in; pi/forall_ ",
                "discharged by pi_ne_lam, beta/app by app_ne_lam, and the GENUINE let_/let_cong arms by ",
                "let-vs-lam shape disjointness (let_ne_lam — the let_ node is a real 7th ctor now, not the old ",
                "app (lam) alias); the ATOMIC iota / delta arms fire on ",
                "the rigid lam-headed source, discharged directly via iota_step_head_none_absurd_type / ",
                "delta_step_head_none_absurd_type. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(church_rosser_whnf-deletion, cd-relation I-half)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.rec".to_string(),
                "par_reduces_cd.refl".to_string(),
                "iota_step".to_string(),
                "delta_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "delta_step_head_none_absurd_type".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "app_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "let_ne_lam".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick 2 (star layer): the multi-step pi / lam inversions
    /// `par_reduces_cd_star_{pi,lam}_inv` (KExpr-indexed) + their Eq-data siblings
    /// `_eq`. From a binder-headed `par_reduces_cd_star`, recover that the reduct is the
    /// same binder with the components related by `par_reduces_cd_star`. Mirror of
    /// `par_reduces_p_star_pi_inv` / `_lam_inv`: induction on the star derivation via
    /// `par_reduces_cd_star.rec` with an accumulator motive carrying the reduct equation
    /// + the accumulated component prefixes; the step arm Eq-inverts each single step
    /// via the Brick-1 `par_reduces_cd_{pi,lam}_inv_eq` and extends the prefixes via
    /// `par_subsumes_par_cd_star` + `par_reduces_cd_star_trans`.
    fn add_par_reduces_cd_star_inv(&mut self) -> Result<(), SpecError> {
        for (b, kexpr_inv, eq_inv, head, first) in [
            (
                BinderInv::Pi,
                "par_reduces_cd_star_pi_inv",
                "par_reduces_cd_star_pi_inv_eq",
                "KExpr.pi",
                "dom",
            ),
            (
                BinderInv::Lam,
                "par_reduces_cd_star_lam_inv",
                "par_reduces_cd_star_lam_inv_eq",
                "KExpr.lam",
                "ty",
            ),
        ] {
            // KExpr-indexed star inversion.
            self.add_definition(SpecDefinition {
                name: kexpr_inv.to_string(),
                type_src: format!(
                    concat!(
                        "forall (env : RedEnv) ({first} : KExpr) (body : KExpr) (w : KExpr) (C : KExpr -> Type), ",
                        "par_reduces_cd_star env ({head} {first} body) w -> ",
                        "(forall ({first}' : KExpr) (body' : KExpr), ",
                        "par_reduces_cd_star env {first} {first}' -> par_reduces_cd_star env body body' -> ",
                        "C ({head} {first}' body')) -> ",
                        "C w"
                    ),
                    first = first,
                    head = head,
                ),
                value_src: Some(par_reduces_cd_star_binder_inv_proof(b)),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Star-level ({head}) shape inversion for the 3-way join — from par_reduces_cd_star env ",
                        "({head} {first} body) w, recover w = {head} {first}' body' with {first} =>*_cd {first}' and ",
                        "body =>*_cd body'. The cd-relation mirror of par_reduces_p_star_pi_inv. Induction on the ",
                        "star derivation via par_reduces_cd_star.rec with an accumulator motive carrying Eq s ",
                        "({head} A B) + the prefixes {first} =>*_cd A, body =>*_cd B; the refl arm hands the ",
                        "continuation the prefixes (transporting C ({head} A B) onto C s), the step arm Eq-inverts ",
                        "each step via {eq_inv_single} and extends the prefixes via par_subsumes_par_cd_star + ",
                        "par_reduces_cd_star_trans. DerivedProved, zero axiom_deps. Part of #2859 ",
                        "(church_rosser_whnf-deletion, cd-relation I-half)."
                    ),
                    head = head,
                    first = first,
                    eq_inv_single = b.single_inv_eq(),
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_cd".to_string(),
                    "par_reduces_cd_star".to_string(),
                    "par_reduces_cd_star.rec".to_string(),
                    "par_reduces_cd_star.refl".to_string(),
                    b.single_inv_eq().to_string(),
                    "par_subsumes_par_cd_star".to_string(),
                    "par_reduces_cd_star_trans".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.symm".to_string(),
                    "Eq.refl".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;

            // Eq-data star inversion (the reduct equality handed back as data).
            self.add_definition(SpecDefinition {
                name: eq_inv.to_string(),
                type_src: format!(
                    concat!(
                        "forall (env : RedEnv) ({first} : KExpr) (body : KExpr) (w : KExpr) (C : Type), ",
                        "par_reduces_cd_star env ({head} {first} body) w -> ",
                        "(forall ({first}' : KExpr) (body' : KExpr), ",
                        "Eq KExpr w ({head} {first}' body') -> ",
                        "par_reduces_cd_star env {first} {first}' -> par_reduces_cd_star env body body' -> C) -> ",
                        "C"
                    ),
                    first = first,
                    head = head,
                ),
                value_src: Some(par_reduces_cd_star_binder_inv_eq_proof(b)),
                is_axiom: false,
                description: format!(
                    concat!(
                        "Eq-data star-level ({head}) shape inversion — from par_reduces_cd_star env ({head} ",
                        "{first} body) w, hand the continuation Eq w ({head} {first}' body') together with ",
                        "{first} =>*_cd {first}' and body =>*_cd body'. The reduct-as-data sibling of {kexpr}, ",
                        "derived from it by the motive M(ww) := Eq w ww -> C applied at Eq.refl w. The form ",
                        "binder-injectivity consumes. DerivedProved, zero axiom_deps. Part of #2859 ",
                        "(church_rosser_whnf-deletion, cd-relation I-half)."
                    ),
                    head = head,
                    first = first,
                    kexpr = kexpr_inv,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "par_reduces_cd_star".to_string(),
                    kexpr_inv.to_string(),
                    "Eq.refl".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }

    /// Brick 3 (injectivity layer): binder injectivity up to confluence
    /// `par_cd_{pi,lam}_injectivity_{dom,cod}`. From a shared-reduct join witness on
    /// two same-binder terms, produce a join witness on the corresponding components.
    /// Mirror of `par_p_pi_injectivity_{dom,cod}` / `par_p_lam_injectivity_*`: project
    /// the common reduct `e3`, Eq-invert both legs via the Brick-2
    /// `par_reduces_cd_star_{pi,lam}_inv_eq` (`e3 = head a1' b1' = head a2' b2'`), read
    /// off the component equality by binder injectivity of the trans'd reduct equation,
    /// transport the second leg onto the meet, and package via
    /// `par_strips_witness_cd_star.intro`.
    fn add_par_cd_binder_injectivity(&mut self) -> Result<(), SpecError> {
        for (b, head, head_label) in [
            (BinderInv::Pi, "KExpr.pi", "pi"),
            (BinderInv::Lam, "KExpr.lam", "lam"),
        ] {
            let (inj_fst, inj_snd) = b.inj();
            let star_inv_eq = match b {
                BinderInv::Pi => "par_reduces_cd_star_pi_inv_eq",
                BinderInv::Lam => "par_reduces_cd_star_lam_inv_eq",
            };
            for (suffix, inj, clhs, crhs, meet1, meet2, leg2, what) in [
                ("dom", inj_fst, "a1", "a2", "a1'", "a2'", "hda2", "domains"),
                (
                    "cod",
                    inj_snd,
                    "b1",
                    "b2",
                    "b1'",
                    "b2'",
                    "hdb2",
                    "codomains",
                ),
            ] {
                let name = format!("par_cd_{head_label}_injectivity_{suffix}");
                self.add_definition(SpecDefinition {
                    name: name.clone(),
                    type_src: format!(
                        concat!(
                            "forall (env : RedEnv) (a1 : KExpr) (b1 : KExpr) (a2 : KExpr) (b2 : KExpr), ",
                            "par_strips_witness_cd_star env ({head} a1 b1) ({head} a2 b2) -> ",
                            "par_strips_witness_cd_star env {clhs} {crhs}"
                        ),
                        head = head,
                        clhs = clhs,
                        crhs = crhs,
                    ),
                    value_src: Some(par_cd_binder_injectivity_proof(
                        head, star_inv_eq, clhs, crhs, meet1, meet2, leg2, inj,
                    )),
                    is_axiom: false,
                    description: format!(
                        concat!(
                            "Binder injectivity up to 3-way (β+ι+δ) confluence ({what}) — from a shared-reduct ",
                            "join witness on {head} a1 b1 and {head} a2 b2, produce a join witness on the {what}. ",
                            "Project the common reduct e3, Eq-invert both legs via {star_inv_eq} (e3 = {head} a1' ",
                            "b1' = {head} a2' b2'), read off the {what} equality by {inj} of the trans'd reduct ",
                            "equation, transport the second leg onto the meet, and package via ",
                            "par_strips_witness_cd_star.intro. The cd-relation mirror of par_p_{head_label}_",
                            "injectivity_{suffix} (the join->injectivity I-half over the δ-carrying relation). ",
                            "DerivedProved, zero axiom_deps. Part of #2859 (church_rosser_whnf-deletion, ",
                            "cd-relation I-half)."
                        ),
                        what = what,
                        head = head,
                        star_inv_eq = star_inv_eq,
                        inj = inj,
                        head_label = head_label,
                        suffix = suffix,
                    ),
                    category: AxiomCategory::DerivedLemma,
                    proof_status: ProofStatus::DerivedProved,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(HashSet::from([
                        "par_reduces_cd_star".to_string(),
                        "par_strips_witness_cd_star".to_string(),
                        "par_strips_witness_cd_star.rec".to_string(),
                        "par_strips_witness_cd_star.intro".to_string(),
                        star_inv_eq.to_string(),
                        inj.to_string(),
                        "Eq.trans".to_string(),
                        "Eq.symm".to_string(),
                        "Eq.substType".to_string(),
                    ])),
                    axiom_deps: HashSet::new(),
                })?;
            }
        }

        Ok(())
    }

    /// Brick 4 (sort tower — NEW, the p-side lacks it): `Sort` shape inversion + sort
    /// injectivity. `Sort` is RIGID under β+ι+δ — no reduction fires at a sort head — so
    /// a `par_reduces_cd` / `par_reduces_cd_star` reduct of `Sort n` is `Sort n` itself
    /// (`par_reduces_cd_sort_inv_eq` single + star), and a join on `Sort n1` / `Sort n2`
    /// forces the two sorts equal (`par_cd_sort_injectivity`). Because the kernel is
    /// non-cumulative (`Sort 0` is not a `Sort 1`), these produce their `Eq` (Prop)
    /// conclusions via Prop-valued machinery: the structural arms discharge through an
    /// inline `Empty.rec` over a sort-vs-non-sort discriminator; the atomic iota / delta
    /// arms through the Prop-valued `iota_step_head_none_absurd` /
    /// `delta_step_head_none_absurd`.
    fn add_par_cd_sort_injectivity(&mut self) -> Result<(), SpecError> {
        // par_reduces_cd_sort_inv_eq: single-step sort rigidity.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_sort_inv_eq".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (n : Level) (t : KExpr), ",
                "par_reduces_cd env (KExpr.sort n) t -> Eq KExpr t (KExpr.sort n)"
            )
            .to_string(),
            value_src: Some(par_reduces_cd_sort_inv_eq_proof()),
            is_axiom: false,
            description: concat!(
                "Single-step sort rigidity — a par_reduces_cd reduct of Sort n is Sort n. par_reduces_cd.rec ",
                "with the Prop motive Eq e (sort n) -> Eq e' (sort n): refl folds in; the structural ",
                "beta/app/lam/pi/forall_/let_/let_cong arms (source not a sort — KEXPR_IS_SORT_INLINE now maps ",
                "the genuine let_ node to Empty) discharge into the Prop goal via an ",
                "inline Empty.rec over a sort-vs-non-sort KExpr.rec discriminator (Eq.substType + Eq.symm + ",
                "Nat.zero); the ATOMIC iota / delta arms fire on the rigid sort-headed source, discharged via ",
                "the Prop-valued iota_step_head_none_absurd / delta_step_head_none_absurd (sort head const name ",
                "= none). DerivedProved, zero axiom_deps. Part of #2859 (church_rosser_whnf-deletion, ",
                "cd-relation I-half)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.rec".to_string(),
                "iota_step".to_string(),
                "delta_step".to_string(),
                "iota_step_head_none_absurd".to_string(),
                "delta_step_head_none_absurd".to_string(),
                "KExpr.rec".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Nat.zero".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_star_sort_inv_eq: star-level sort rigidity.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_sort_inv_eq".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (n : Level) (w : KExpr), ",
                "par_reduces_cd_star env (KExpr.sort n) w -> Eq KExpr w (KExpr.sort n)"
            )
            .to_string(),
            value_src: Some(par_reduces_cd_star_sort_inv_eq_proof()),
            is_axiom: false,
            description: concat!(
                "Star-level sort rigidity — a par_reduces_cd_star reduct of Sort n is Sort n. Induction on the ",
                "star derivation via par_reduces_cd_star.rec with the Prop motive Eq s (sort n) -> Eq r (sort ",
                "n); the refl arm is the identity, the step arm transports each single step onto Sort n and ",
                "Eq-inverts it via par_reduces_cd_sort_inv_eq, threading the equality through the IH. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (church_rosser_whnf-deletion, cd-relation I-half)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.rec".to_string(),
                "par_reduces_cd_sort_inv_eq".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_cd_sort_injectivity: the join forces the two sorts equal.
        self.add_definition(SpecDefinition {
            name: "par_cd_sort_injectivity".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (n1 : Level) (n2 : Level), ",
                "par_strips_witness_cd_star env (KExpr.sort n1) (KExpr.sort n2) -> ",
                "Eq KExpr (KExpr.sort n1) (KExpr.sort n2)"
            )
            .to_string(),
            value_src: Some(par_cd_sort_injectivity_proof()),
            is_axiom: false,
            description: concat!(
                "Sort injectivity up to 3-way (β+ι+δ) confluence — from a shared-reduct join witness on Sort ",
                "n1 and Sort n2, the two sorts are equal. Project the common reduct e3; by sort rigidity ",
                "(par_reduces_cd_star_sort_inv_eq) both legs force e3 = Sort n1 and e3 = Sort n2, so Sort n1 = ",
                "Sort n2 by Eq.trans (Eq.symm ..). The sort analogue of par_cd_{pi,lam}_injectivity (the p-side ",
                "lacks it: Sort C carries no reducible component, so the join degenerates to an equality). ",
                "DerivedProved, zero axiom_deps. Part of #2859 (church_rosser_whnf-deletion, cd-relation I-half)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd_star".to_string(),
                "par_strips_witness_cd_star".to_string(),
                "par_strips_witness_cd_star.rec".to_string(),
                "par_reduces_cd_star_sort_inv_eq".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Which binder the single-step Eq-data inversion targets. The pi and lam proofs are
/// structurally identical up to the head constructor and the discrimination lemmas, so
/// they share one proof generator.
#[derive(Clone, Copy)]
enum BinderInv {
    Pi,
    Lam,
}

impl BinderInv {
    /// `KExpr.pi` / `KExpr.lam`.
    fn head(self) -> &'static str {
        match self {
            BinderInv::Pi => "KExpr.pi",
            BinderInv::Lam => "KExpr.lam",
        }
    }
    /// The injectivity projections for this head (`pi_inj_*` / `lam_inj_*`).
    fn inj(self) -> (&'static str, &'static str) {
        match self {
            BinderInv::Pi => ("pi_inj_fst", "pi_inj_snd"),
            BinderInv::Lam => ("lam_inj_fst", "lam_inj_snd"),
        }
    }
    /// The discriminator that kills an `app`-headed source against this head
    /// (`app_ne_pi` / `app_ne_lam`).
    fn app_ne(self) -> &'static str {
        match self {
            BinderInv::Pi => "app_ne_pi",
            BinderInv::Lam => "app_ne_lam",
        }
    }
    /// The discriminator that kills the OTHER binder against this head: a `lam`-headed
    /// source against `pi` (`lam_ne_pi`), or a `pi`-headed source against `lam`
    /// (`pi_ne_lam`). The forall_ arm reuses it (`forall_` is the pi alias).
    fn other_ne(self) -> &'static str {
        match self {
            BinderInv::Pi => "lam_ne_pi",
            BinderInv::Lam => "pi_ne_lam",
        }
    }
    /// The Brick-1 single-step Eq-data inversion lemma for this head.
    fn single_inv_eq(self) -> &'static str {
        match self {
            BinderInv::Pi => "par_reduces_cd_pi_inv_eq",
            BinderInv::Lam => "par_reduces_cd_lam_inv_eq",
        }
    }
}

/// Closed proof term for the single-step Eq-data binder inversion
/// `par_reduces_cd_pi_inv_eq` / `par_reduces_cd_lam_inv_eq`. The cd-relation mirror of
/// `par_reduces_p_{pi,lam}_inv_eq_proof`, with the PARALLEL-iota arm split into the
/// atomic `iota` and `delta` arms (each discharged on the rigid binder-headed source).
///
/// `Kont(R) := forall x' body', Eq R (HEAD x' body') -> (s0 =>_cd x') ->
///   (body =>_cd body') -> C` where `HEAD`/`s0` are the binder head / first slot.
/// `par_reduces_cd.rec` with a source-equation motive `Eq e (HEAD s0 body) -> Kont(e')
/// -> C`: the HEAD and forall_ arms (for pi) feed the continuation at the reduct via
/// `Eq.refl` + the components transported via injectivity; refl folds in; the wrong
/// binder/app arms discharge via the `_ne_` discriminators; the iota / delta arms
/// transport their step onto the rigid head and discharge via the Type-valued
/// head-none-absurd lemmas.
fn par_reduces_cd_binder_inv_eq_proof(b: BinderInv) -> String {
    let head = b.head();
    let (inj_fst, inj_snd) = b.inj();
    let app_ne = b.app_ne();
    let other_ne = b.other_ne();
    // The first slot binder name (dom for pi, ty for lam) — purely cosmetic in the
    // generated source; we use `s0` uniformly.
    // Kont(R) := forall x' body', Eq R (head s0 body') -> s0 =>_cd x' -> body =>_cd
    // body' -> C.
    let kont = |reduct: &str| -> String {
        format!(
            concat!(
                "(forall (s0' : KExpr) (body' : KExpr), ",
                "Eq KExpr {reduct} ({head} s0' body') -> ",
                "par_reduces_cd env s0 s0' -> par_reduces_cd env body body' -> C)"
            ),
            reduct = reduct,
            head = head,
        )
    };
    let motive = format!(
        concat!(
            "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_cd env e e') => ",
            "Eq KExpr e ({head} s0 body) -> {kont} -> C)"
        ),
        head = head,
        kont = kont("e'"),
    );

    // refl arm: source e, reduct e. Take s0' = s0, body' = body so the reduct equation
    // is exactly eq; sub-derivations refl.
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) (eq : Eq KExpr e ({head} s0 body)) ",
            "(k : {kont}) => ",
            "k s0 body eq (par_reduces_cd.refl env s0) (par_reduces_cd.refl env body))"
        ),
        head = head,
        kont = kont("e"),
    );

    // beta arm: source app (lam A b0) arg — app /= head.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_cd env A A') (_hb0 : par_reduces_cd env b0 b0') ",
            "(_harg : par_reduces_cd env arg arg') ",
            "(_ihA : Eq KExpr A ({head} s0 body) -> {kont_A} -> C) ",
            "(_ihb0 : Eq KExpr b0 ({head} s0 body) -> {kont_b0} -> C) ",
            "(_iharg : Eq KExpr arg ({head} s0 body) -> {kont_arg} -> C) ",
            "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) ({head} s0 body)) ",
            "(_k : {kont_red}) => ",
            "{app_ne} (KExpr.lam A b0) arg s0 body C eq)"
        ),
        head = head,
        app_ne = app_ne,
        kont_A = kont("A'"),
        kont_b0 = kont("b0'"),
        kont_arg = kont("arg'"),
        kont_red = kont("(instantiate b0' arg')"),
    );

    // app arm: source app g b — app /= head.
    let app_arm = format!(
        concat!(
            "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(_hg : par_reduces_cd env g g') (_hb : par_reduces_cd env b b') ",
            "(_ihg : Eq KExpr g ({head} s0 body) -> {kont_g} -> C) ",
            "(_ihb : Eq KExpr b ({head} s0 body) -> {kont_b} -> C) ",
            "(eq : Eq KExpr (KExpr.app g b) ({head} s0 body)) ",
            "(_k : {kont_red}) => ",
            "{app_ne} g b s0 body C eq)"
        ),
        head = head,
        app_ne = app_ne,
        kont_g = kont("g'"),
        kont_b = kont("b'"),
        kont_red = kont("(KExpr.app g' b')"),
    );

    // lam arm: GENUINE for lam inversion; for pi inversion, lam /= pi.
    let lam_arm = match b {
        BinderInv::Lam => format!(
            concat!(
                "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
                "(ht : par_reduces_cd env t0 t0') (hb : par_reduces_cd env b0 b0') ",
                "(_iht : Eq KExpr t0 ({head} s0 body) -> {kont_t0} -> C) ",
                "(_ihb : Eq KExpr b0 ({head} s0 body) -> {kont_b0} -> C) ",
                "(eq : Eq KExpr (KExpr.lam t0 b0) ({head} s0 body)) ",
                "(k : {kont_red}) => ",
                "k t0' b0' (Eq.refl KExpr (KExpr.lam t0' b0')) ",
                "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_cd env x t0') t0 s0 ",
                "({inj_fst} t0 b0 s0 body eq) ht) ",
                "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_cd env x b0') b0 body ",
                "({inj_snd} t0 b0 s0 body eq) hb))"
            ),
            head = head,
            inj_fst = inj_fst,
            inj_snd = inj_snd,
            kont_t0 = kont("t0'"),
            kont_b0 = kont("b0'"),
            kont_red = kont("(KExpr.lam t0' b0')"),
        ),
        BinderInv::Pi => format!(
            concat!(
                "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
                "(_ht : par_reduces_cd env t0 t0') (_hb : par_reduces_cd env b0 b0') ",
                "(_iht : Eq KExpr t0 ({head} s0 body) -> {kont_t0} -> C) ",
                "(_ihb : Eq KExpr b0 ({head} s0 body) -> {kont_b0} -> C) ",
                "(eq : Eq KExpr (KExpr.lam t0 b0) ({head} s0 body)) ",
                "(_k : {kont_red}) => ",
                "{other_ne} t0 b0 s0 body C eq)"
            ),
            head = head,
            other_ne = other_ne,
            kont_t0 = kont("t0'"),
            kont_b0 = kont("b0'"),
            kont_red = kont("(KExpr.lam t0' b0')"),
        ),
    };

    // pi arm: GENUINE for pi inversion; for lam inversion, pi /= lam.
    let pi_arm = match b {
        BinderInv::Pi => format!(
            concat!(
                "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
                "(hd : par_reduces_cd env d0 d0') (hb : par_reduces_cd env b0 b0') ",
                "(_ihd : Eq KExpr d0 ({head} s0 body) -> {kont_d} -> C) ",
                "(_ihb : Eq KExpr b0 ({head} s0 body) -> {kont_b0} -> C) ",
                "(eq : Eq KExpr (KExpr.pi d0 b0) ({head} s0 body)) ",
                "(k : {kont_red}) => ",
                "k d0' b0' (Eq.refl KExpr (KExpr.pi d0' b0')) ",
                "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_cd env x d0') d0 s0 ",
                "({inj_fst} d0 b0 s0 body eq) hd) ",
                "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_cd env x b0') b0 body ",
                "({inj_snd} d0 b0 s0 body eq) hb))"
            ),
            head = head,
            inj_fst = inj_fst,
            inj_snd = inj_snd,
            kont_d = kont("d0'"),
            kont_b0 = kont("b0'"),
            kont_red = kont("(KExpr.pi d0' b0')"),
        ),
        BinderInv::Lam => format!(
            concat!(
                "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
                "(_hd : par_reduces_cd env d0 d0') (_hb0 : par_reduces_cd env b0 b0') ",
                "(_ihd : Eq KExpr d0 ({head} s0 body) -> {kont_d} -> C) ",
                "(_ihb0 : Eq KExpr b0 ({head} s0 body) -> {kont_b0} -> C) ",
                "(eq : Eq KExpr (KExpr.pi d0 b0) ({head} s0 body)) ",
                "(_k : {kont_red}) => ",
                "{other_ne} d0 b0 s0 body C eq)"
            ),
            head = head,
            other_ne = other_ne,
            kont_d = kont("d0'"),
            kont_b0 = kont("b0'"),
            kont_red = kont("(KExpr.pi d0' b0')"),
        ),
    };

    // forall_ arm: source forall_ d0 b0 = pi d0 b0 (alias). GENUINE for pi inversion
    // (reduct forall_ d0' b0' = pi d0' b0'); for lam inversion, pi /= lam.
    let forall_arm = match b {
        BinderInv::Pi => format!(
            concat!(
                "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
                "(hd : par_reduces_cd env d0 d0') (hb : par_reduces_cd env b0 b0') ",
                "(_ihd : Eq KExpr d0 ({head} s0 body) -> {kont_d} -> C) ",
                "(_ihb : Eq KExpr b0 ({head} s0 body) -> {kont_b0} -> C) ",
                "(eq : Eq KExpr (KExpr.forall_ d0 b0) ({head} s0 body)) ",
                "(k : {kont_red}) => ",
                "k d0' b0' (Eq.refl KExpr (KExpr.pi d0' b0')) ",
                "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_cd env x d0') d0 s0 ",
                "({inj_fst} d0 b0 s0 body eq) hd) ",
                "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_cd env x b0') b0 body ",
                "({inj_snd} d0 b0 s0 body eq) hb))"
            ),
            head = head,
            inj_fst = inj_fst,
            inj_snd = inj_snd,
            kont_d = kont("d0'"),
            kont_b0 = kont("b0'"),
            kont_red = kont("(KExpr.forall_ d0' b0')"),
        ),
        BinderInv::Lam => format!(
            concat!(
                "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
                "(_hd : par_reduces_cd env d0 d0') (_hb0 : par_reduces_cd env b0 b0') ",
                "(_ihd : Eq KExpr d0 ({head} s0 body) -> {kont_d} -> C) ",
                "(_ihb0 : Eq KExpr b0 ({head} s0 body) -> {kont_b0} -> C) ",
                "(eq : Eq KExpr (KExpr.forall_ d0 b0) ({head} s0 body)) ",
                "(_k : {kont_red}) => ",
                "{other_ne} d0 b0 s0 body C eq)"
            ),
            head = head,
            other_ne = other_ne,
            kont_d = kont("d0'"),
            kont_b0 = kont("b0'"),
            kont_red = kont("(KExpr.forall_ d0' b0')"),
        ),
    };

    // let_ arm (ZETA): source the GENUINE let_ node let_ t0 v b0 (no longer the
    // app (lam t0 b0) v alias), reduct instantiate b0' v'. A let_ is never a lam/pi, so
    // the reduct equation eq is impossible — discharge via the registered let-vs-binder
    // no-confusion lemma let_ne_{pi,lam} (the lam-vs-pi shape-disjointness mechanism).
    let let_ne = match b {
        BinderInv::Pi => "let_ne_pi",
        BinderInv::Lam => "let_ne_lam",
    };
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_cd env t0 t0') (_hv : par_reduces_cd env v v') ",
            "(_hb0 : par_reduces_cd env b0 b0') ",
            "(_iht0 : Eq KExpr t0 ({head} s0 body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v ({head} s0 body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 ({head} s0 body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) ({head} s0 body)) ",
            "(_k : {kont_red}) => ",
            "{let_ne} t0 v b0 s0 body C eq)"
        ),
        head = head,
        let_ne = let_ne,
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(instantiate b0' v')"),
    );

    // let_cong arm (TRAILING congruence ctor): source let_ t0 v b0, reduct
    // let_ t0' v' b0'. Same shape-disjointness discharge as the zeta arm (a let_ is
    // never a lam/pi head).
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_cd env t0 t0') (_hv : par_reduces_cd env v v') ",
            "(_hb0 : par_reduces_cd env b0 b0') ",
            "(_iht0 : Eq KExpr t0 ({head} s0 body) -> {kont_t0} -> C) ",
            "(_ihv : Eq KExpr v ({head} s0 body) -> {kont_v} -> C) ",
            "(_ihb0 : Eq KExpr b0 ({head} s0 body) -> {kont_b0} -> C) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) ({head} s0 body)) ",
            "(_k : {kont_red}) => ",
            "{let_ne} t0 v b0 s0 body C eq)"
        ),
        head = head,
        let_ne = let_ne,
        kont_t0 = kont("t0'"),
        kont_v = kont("v'"),
        kont_b0 = kont("b0'"),
        kont_red = kont("(KExpr.let_ t0' v' b0')"),
    );

    // iota arm (ATOMIC): source e0, iota_step (red_rec env) e0 e0'. e0 = head s0 body
    // is rigid (binder head const name = none), so transport the step onto the head and
    // discharge via the Type-valued iota_step_head_none_absurd_type.
    let iota_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e0' : KExpr) (hi : iota_step (red_rec env) e0 e0') ",
            "(eq : Eq KExpr e0 ({head} s0 body)) ",
            "(_k : {kont_red}) => ",
            "iota_step_head_none_absurd_type (red_rec env) ({head} s0 body) e0' C ",
            "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
            "(Eq.substType KExpr (fun (x : KExpr) => iota_step (red_rec env) x e0') ",
            "e0 ({head} s0 body) eq hi))"
        ),
        head = head,
        kont_red = kont("e0'"),
    );

    // delta arm (ATOMIC): source e0, delta_step (red_def env) e0 e0'. Same rigid-head
    // discharge via delta_step_head_none_absurd_type.
    let delta_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e0' : KExpr) (hd : delta_step (red_def env) e0 e0') ",
            "(eq : Eq KExpr e0 ({head} s0 body)) ",
            "(_k : {kont_red}) => ",
            "delta_step_head_none_absurd_type (red_def env) ({head} s0 body) e0' C ",
            "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
            "(Eq.substType KExpr (fun (x : KExpr) => delta_step (red_def env) x e0') ",
            "e0 ({head} s0 body) eq hd))"
        ),
        head = head,
        kont_red = kont("e0'"),
    );

    // proj arm (TRAILING congruence ctor): source proj ps pidx psub, reduct
    // proj ps pidx psub'. A proj is never a lam/pi head, so the reduct equation eq is
    // impossible — discharge via the registered proj-vs-binder no-confusion lemma
    // proj_ne_{pi,lam}. Part of the proj/lit fragment rung.
    let proj_ne = match b {
        BinderInv::Pi => "proj_ne_pi",
        BinderInv::Lam => "proj_ne_lam",
    };
    let proj_arm = format!(
        concat!(
            "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub' : KExpr) ",
            "(_hsub : par_reduces_cd env psub psub') ",
            "(_ihsub : Eq KExpr psub ({head} s0 body) -> {kont_sub} -> C) ",
            "(eq : Eq KExpr (KExpr.proj ps pidx psub) ({head} s0 body)) ",
            "(_k : {kont_red}) => ",
            "{proj_ne} ps pidx psub s0 body C eq)"
        ),
        head = head,
        proj_ne = proj_ne,
        kont_sub = kont("psub'"),
        kont_red = kont("(KExpr.proj ps pidx psub')"),
    );

    // The proof's outer binders use uniform `s0`/`body` names; the kernel checks it
    // against the lemma's declared type (dom/body for pi, ty/body for lam) up to alpha.
    format!(
        concat!(
            "fun (env : RedEnv) (s0 : KExpr) (body : KExpr) (t : KExpr) (C : Type) ",
            "(h : par_reduces_cd env ({head} s0 body) t) ",
            "(kbinder : {kont_t}) => ",
            "par_reduces_cd.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {delta_arm} {let_cong_arm} {proj_arm} ",
            "({head} s0 body) t h (Eq.refl KExpr ({head} s0 body)) kbinder"
        ),
        head = head,
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
        delta_arm = delta_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for the star-level binder inversion
/// `par_reduces_cd_star_{pi,lam}_inv`. The cd-relation mirror of
/// `par_reduces_p_star_pi_inv_proof`: induction on the multi-step derivation via
/// `par_reduces_cd_star.rec` with an ACCUMULATOR motive carrying, for the current
/// source `s`, the witness `Eq s (head A B)` plus the accumulated prefixes
/// `s0 =>*_cd A` and `body =>*_cd B`. The refl arm hands the continuation the prefixes
/// (transporting `C (head A B)` onto `C s`); the step arm transports the single step
/// onto `head A B`, Eq-inverts it via the Brick-1 single-step inversion to `e' = head
/// A' B'` with `A =>_cd A'`, `B =>_cd B'`, extends the prefixes through
/// `par_reduces_cd_star_trans` + `par_subsumes_par_cd_star`, and recurses via the IH.
fn par_reduces_cd_star_binder_inv_proof(b: BinderInv) -> String {
    let head = b.head();
    let single = b.single_inv_eq();
    // Accumulator motive: M s r _ := forall A B, Eq s (head A B) -> s0 =>*_cd A ->
    //   body =>*_cd B -> C r.
    let motive = format!(
        concat!(
            "(fun (s : KExpr) (r : KExpr) (_h : par_reduces_cd_star env s r) => ",
            "forall (A : KExpr) (B : KExpr), Eq KExpr s ({head} A B) -> ",
            "par_reduces_cd_star env s0 A -> par_reduces_cd_star env body B -> C r)"
        ),
        head = head,
    );
    // refl arm (s = r = e): hand kbinder the accumulated prefixes at C (head A B),
    // transported onto C e via eq.symm.
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) => ",
            "fun (A : KExpr) (B : KExpr) (eq : Eq KExpr e ({head} A B)) ",
            "(hd : par_reduces_cd_star env s0 A) (hb : par_reduces_cd_star env body B) => ",
            "Eq.substType KExpr C ({head} A B) e ",
            "(Eq.symm KExpr e ({head} A B) eq) (kbinder A B hd hb))"
        ),
        head = head,
    );
    // step arm: hstep : e =>_cd e', tail : e' =>*_cd e'', ih over e'. Transport hstep
    // onto head A B, Eq-invert via the single-step inversion to e' = head A' B', extend
    // the prefixes, recurse via ih.
    let step_arm = format!(
        concat!(
            "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
            "(hstep : par_reduces_cd env e e') ",
            "(_htail : par_reduces_cd_star env e' e'') ",
            "(ih : forall (A : KExpr) (B : KExpr), Eq KExpr e' ({head} A B) -> ",
            "par_reduces_cd_star env s0 A -> par_reduces_cd_star env body B -> C e'') => ",
            "fun (A : KExpr) (B : KExpr) (eq : Eq KExpr e ({head} A B)) ",
            "(hd : par_reduces_cd_star env s0 A) (hb : par_reduces_cd_star env body B) => ",
            "{single} env A B e' (C e'') ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_cd env x e') e ({head} A B) eq hstep) ",
            "(fun (A' : KExpr) (B' : KExpr) (eq' : Eq KExpr e' ({head} A' B')) ",
            "(hAA' : par_reduces_cd env A A') (hBB' : par_reduces_cd env B B') => ",
            "ih A' B' eq' ",
            "(par_reduces_cd_star_trans env s0 A A' hd (par_subsumes_par_cd_star env A A' hAA')) ",
            "(par_reduces_cd_star_trans env body B B' hb (par_subsumes_par_cd_star env B B' hBB'))))"
        ),
        head = head,
        single = single,
    );
    format!(
        concat!(
            "fun (env : RedEnv) (s0 : KExpr) (body : KExpr) (w : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_cd_star env ({head} s0 body) w) ",
            "(kbinder : forall (s0' : KExpr) (body' : KExpr), ",
            "par_reduces_cd_star env s0 s0' -> par_reduces_cd_star env body body' -> ",
            "C ({head} s0' body')) => ",
            "par_reduces_cd_star.rec env {motive} {refl_arm} {step_arm} ",
            "({head} s0 body) w h ",
            "s0 body (Eq.refl KExpr ({head} s0 body)) ",
            "(par_reduces_cd_star.refl env s0) (par_reduces_cd_star.refl env body)"
        ),
        head = head,
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Closed proof term for the Eq-data star binder inversion
/// `par_reduces_cd_star_{pi,lam}_inv_eq`. Derived from the KExpr-indexed
/// `par_reduces_cd_star_{pi,lam}_inv` by instantiating its motive at `M(ww) := Eq w ww
/// -> C`: the inversion returns `Eq w w -> C`, which `Eq.refl w` discharges to `C`, and
/// inside the inversion's continuation the reduct equality `Eq w (head s0' body')` is in
/// scope and handed straight to the caller's continuation `k`.
fn par_reduces_cd_star_binder_inv_eq_proof(b: BinderInv) -> String {
    let head = b.head();
    let kexpr_inv = match b {
        BinderInv::Pi => "par_reduces_cd_star_pi_inv",
        BinderInv::Lam => "par_reduces_cd_star_lam_inv",
    };
    format!(
        concat!(
            "fun (env : RedEnv) (s0 : KExpr) (body : KExpr) (w : KExpr) (C : Type) ",
            "(h : par_reduces_cd_star env ({head} s0 body) w) ",
            "(k : forall (s0' : KExpr) (body' : KExpr), ",
            "Eq KExpr w ({head} s0' body') -> ",
            "par_reduces_cd_star env s0 s0' -> par_reduces_cd_star env body body' -> C) => ",
            "{kexpr_inv} env s0 body w ",
            "(fun (ww : KExpr) => Eq KExpr w ww -> C) h ",
            "(fun (s0' : KExpr) (body' : KExpr) ",
            "(hd : par_reduces_cd_star env s0 s0') (hb : par_reduces_cd_star env body body') => ",
            "fun (eqw : Eq KExpr w ({head} s0' body')) => k s0' body' eqw hd hb) ",
            "(Eq.refl KExpr w)"
        ),
        head = head,
        kexpr_inv = kexpr_inv,
    )
}

/// Closed proof term for the binder-injectivity-up-to-confluence lemmas
/// `par_cd_{pi,lam}_injectivity_{dom,cod}`, parametric in the head and the component
/// projected. The cd-relation mirror of `par_p_pi_injectivity_proof` /
/// `par_p_lam_injectivity_proof`.
///
/// From a shared-reduct join witness `par_strips_witness_cd_star env (head a1 b1) (head
/// a2 b2)`, project the common reduct `e3` with `head a1 b1 =>*_cd e3` and `head a2 b2
/// =>*_cd e3`. Eq-invert both legs (`star_inv_eq`): `eq1 : e3 = head a1' b1'` with `a1
/// =>*_cd a1'`, `b1 =>*_cd b1'`, and `eq2 : e3 = head a2' b2'` with `a2 =>*_cd a2'`, `b2
/// =>*_cd b2'`. Then `head a1' b1' = head a2' b2'` by `Eq.trans (Eq.symm eq1) eq2`, so
/// the projected components are equal (`inj` of the trans'd reduct equation); transport
/// the second leg onto the first's meet and package via `par_strips_witness_cd_star.intro`.
///
/// `clhs`/`crhs` are the conclusion's two terms (`a1`/`a2` or `b1`/`b2`), `meet1`/`meet2`
/// the recovered meet points (`a1'`/`a2'` or `b1'`/`b2'`), `leg2` the recovered
/// second-leg prefix derivation (`hda2` or `hdb2`), and `inj` the projection
/// (`pi_inj_fst`/`pi_inj_snd` or `lam_inj_fst`/`lam_inj_snd`).
#[allow(clippy::too_many_arguments)]
fn par_cd_binder_injectivity_proof(
    head: &str,
    star_inv_eq: &str,
    clhs: &str,
    crhs: &str,
    meet1: &str,
    meet2: &str,
    leg2: &str,
    inj: &str,
) -> String {
    // The first leg's prefix derivation onto meet1: hda1 for the domain projection,
    // hdb1 for the codomain projection (matches whether `inj` is the *_fst or *_snd).
    let leg1 = if inj.ends_with("_fst") {
        "hda1"
    } else {
        "hdb1"
    };
    // Inner continuation (after inverting the second leg p2): identify the meet by binder
    // injectivity of the trans'd reduct equation, transport leg2 onto it, and package the
    // join witness at meet1.
    let inner_k = format!(
        concat!(
            "(fun (a2' : KExpr) (b2' : KExpr) (eq2 : Eq KExpr e3 ({head} a2' b2')) ",
            "(hda2 : par_reduces_cd_star env a2 a2') (hdb2 : par_reduces_cd_star env b2 b2') => ",
            "par_strips_witness_cd_star.intro env {clhs} {crhs} {meet1} {leg1} ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_cd_star env {crhs} x) {meet2} {meet1} ",
            "(Eq.symm KExpr {meet1} {meet2} ",
            "({inj} a1' b1' a2' b2' ",
            "(Eq.trans KExpr ({head} a1' b1') e3 ({head} a2' b2') ",
            "(Eq.symm KExpr e3 ({head} a1' b1') eq1) eq2))) ",
            "{leg2}))"
        ),
        head = head,
        clhs = clhs,
        crhs = crhs,
        meet1 = meet1,
        meet2 = meet2,
        leg1 = leg1,
        leg2 = leg2,
        inj = inj,
    );
    // Outer continuation (after inverting the first leg p1): invert p2 at the same reduct
    // e3.
    let outer_k = format!(
        concat!(
            "(fun (a1' : KExpr) (b1' : KExpr) (eq1 : Eq KExpr e3 ({head} a1' b1')) ",
            "(hda1 : par_reduces_cd_star env a1 a1') (hdb1 : par_reduces_cd_star env b1 b1') => ",
            "{star_inv_eq} env a2 b2 e3 ",
            "(par_strips_witness_cd_star env {clhs} {crhs}) p2 {inner_k})"
        ),
        head = head,
        clhs = clhs,
        crhs = crhs,
        star_inv_eq = star_inv_eq,
        inner_k = inner_k,
    );
    format!(
        concat!(
            "fun (env : RedEnv) (a1 : KExpr) (b1 : KExpr) (a2 : KExpr) (b2 : KExpr) ",
            "(w : par_strips_witness_cd_star env ({head} a1 b1) ({head} a2 b2)) => ",
            "@par_strips_witness_cd_star.rec env ({head} a1 b1) ({head} a2 b2) ",
            "(fun (_w : par_strips_witness_cd_star env ({head} a1 b1) ({head} a2 b2)) => ",
            "par_strips_witness_cd_star env {clhs} {crhs}) ",
            "(fun (e3 : KExpr) ",
            "(p1 : par_reduces_cd_star env ({head} a1 b1) e3) ",
            "(p2 : par_reduces_cd_star env ({head} a2 b2) e3) => ",
            "{star_inv_eq} env a1 b1 e3 ",
            "(par_strips_witness_cd_star env {clhs} {crhs}) p1 {outer_k}) ",
            "w"
        ),
        head = head,
        clhs = clhs,
        crhs = crhs,
        star_inv_eq = star_inv_eq,
        outer_k = outer_k,
    )
}

/// Inline `KExpr.rec` discriminator `kexpr_is_sort : KExpr -> Type` — `Sort` maps to
/// `Nat` (inhabited by `Nat.zero`), every other head to `Empty`. Substituting it along
/// `Eq (sort n) S` over a non-sort source `S` yields an `Empty`, which `Empty.rec`
/// turns into any (Prop) goal. The sort dual of `KEXPR_NOT_PI_INLINE` (the structural
/// arms' Prop-goal discharger, since the kernel is non-cumulative — `sort_ne_*` only
/// targets `R : Type`).
const KEXPR_IS_SORT_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : ListType Level) => Empty) ",
    // let_ (the genuine 7th ctor: ty, val, body): not a sort -> Empty.
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) ",
    // proj (8th ctor: name, idx, sub) / lit (9th ctor: val): not a sort -> Empty.
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) ",
    "(fun (_ : Nat) => Empty))"
);

/// Discharge a structural (non-sort-headed) arm of the single-step sort inversion: from
/// `heq : Eq KExpr <source> (KExpr.sort n)` (an impossible equation, `source` not a
/// sort), produce the Prop goal `Eq KExpr <reduct> (KExpr.sort n)`. Transports
/// `Nat.zero` along `Eq (sort n) source` through `KEXPR_IS_SORT_INLINE` to an `Empty`,
/// then `Empty.rec` into the goal.
fn sort_struct_discharge(source: &str, reduct: &str) -> String {
    format!(
        concat!(
            "(Empty.rec (fun (_ : Empty) => Eq KExpr {reduct} (KExpr.sort n)) ",
            "(Eq.substType KExpr {discr} (KExpr.sort n) {source} ",
            "(Eq.symm KExpr {source} (KExpr.sort n) heq) Nat.zero))"
        ),
        reduct = reduct,
        discr = KEXPR_IS_SORT_INLINE,
        source = source,
    )
}

/// Closed proof term for `par_reduces_cd_sort_inv_eq` (single-step sort rigidity).
/// `par_reduces_cd.rec` with the Prop motive `Eq e (sort n) -> Eq e' (sort n)`.
fn par_reduces_cd_sort_inv_eq_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_cd env e e') => ",
        "Eq KExpr e (KExpr.sort n) -> Eq KExpr e' (KExpr.sort n))"
    );
    // refl: source = reduct = e; the goal is exactly the hypothesis.
    let refl_arm = "(fun (e : KExpr) (heq : Eq KExpr e (KExpr.sort n)) => heq)";
    // beta: source app (lam A b0) arg, reduct instantiate b0' arg'.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) (arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_cd env A A') (_hb0 : par_reduces_cd env b0 b0') ",
            "(_harg : par_reduces_cd env arg arg') ",
            "(_ihA : Eq KExpr A (KExpr.sort n) -> Eq KExpr A' (KExpr.sort n)) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.sort n) -> Eq KExpr b0' (KExpr.sort n)) ",
            "(_iharg : Eq KExpr arg (KExpr.sort n) -> Eq KExpr arg' (KExpr.sort n)) ",
            "(heq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.sort n)) => {discharge})"
        ),
        discharge =
            sort_struct_discharge("(KExpr.app (KExpr.lam A b0) arg)", "(instantiate b0' arg')"),
    );
    // app: source app g b, reduct app g' b'.
    let app_arm = format!(
        concat!(
            "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(_hg : par_reduces_cd env g g') (_hb : par_reduces_cd env b b') ",
            "(_ihg : Eq KExpr g (KExpr.sort n) -> Eq KExpr g' (KExpr.sort n)) ",
            "(_ihb : Eq KExpr b (KExpr.sort n) -> Eq KExpr b' (KExpr.sort n)) ",
            "(heq : Eq KExpr (KExpr.app g b) (KExpr.sort n)) => {discharge})"
        ),
        discharge = sort_struct_discharge("(KExpr.app g b)", "(KExpr.app g' b')"),
    );
    // lam: source lam t0 b0, reduct lam t0' b0'.
    let lam_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_ht : par_reduces_cd env t0 t0') (_hb : par_reduces_cd env b0 b0') ",
            "(_iht : Eq KExpr t0 (KExpr.sort n) -> Eq KExpr t0' (KExpr.sort n)) ",
            "(_ihb : Eq KExpr b0 (KExpr.sort n) -> Eq KExpr b0' (KExpr.sort n)) ",
            "(heq : Eq KExpr (KExpr.lam t0 b0) (KExpr.sort n)) => {discharge})"
        ),
        discharge = sort_struct_discharge("(KExpr.lam t0 b0)", "(KExpr.lam t0' b0')"),
    );
    // pi: source pi d0 b0, reduct pi d0' b0'.
    let pi_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_cd env d0 d0') (_hb0 : par_reduces_cd env b0 b0') ",
            "(_ihd : Eq KExpr d0 (KExpr.sort n) -> Eq KExpr d0' (KExpr.sort n)) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.sort n) -> Eq KExpr b0' (KExpr.sort n)) ",
            "(heq : Eq KExpr (KExpr.pi d0 b0) (KExpr.sort n)) => {discharge})"
        ),
        discharge = sort_struct_discharge("(KExpr.pi d0 b0)", "(KExpr.pi d0' b0')"),
    );
    // forall_: source forall_ d0 b0 = pi d0 b0 (alias), reduct forall_ d0' b0'.
    let forall_arm = format!(
        concat!(
            "(fun (d0 : KExpr) (d0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_cd env d0 d0') (_hb0 : par_reduces_cd env b0 b0') ",
            "(_ihd : Eq KExpr d0 (KExpr.sort n) -> Eq KExpr d0' (KExpr.sort n)) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.sort n) -> Eq KExpr b0' (KExpr.sort n)) ",
            "(heq : Eq KExpr (KExpr.forall_ d0 b0) (KExpr.sort n)) => {discharge})"
        ),
        discharge = sort_struct_discharge("(KExpr.forall_ d0 b0)", "(KExpr.forall_ d0' b0')"),
    );
    // let_ (ZETA): source the GENUINE let_ node let_ t0 v b0 (not the app (lam …) …
    // alias), reduct instantiate b0' v'. A let_ is not a sort, so heq is impossible —
    // KEXPR_IS_SORT_INLINE maps let_ to Empty (see its trailing let minor).
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_cd env t0 t0') (_hv : par_reduces_cd env v v') ",
            "(_hb0 : par_reduces_cd env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.sort n) -> Eq KExpr t0' (KExpr.sort n)) ",
            "(_ihv : Eq KExpr v (KExpr.sort n) -> Eq KExpr v' (KExpr.sort n)) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.sort n) -> Eq KExpr b0' (KExpr.sort n)) ",
            "(heq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.sort n)) => {discharge})"
        ),
        discharge = sort_struct_discharge("(KExpr.let_ t0 v b0)", "(instantiate b0' v')"),
    );
    // let_cong (TRAILING congruence ctor): source let_ t0 v b0, reduct let_ t0' v' b0'.
    // Same not-a-sort discharge.
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_cd env t0 t0') (_hv : par_reduces_cd env v v') ",
            "(_hb0 : par_reduces_cd env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.sort n) -> Eq KExpr t0' (KExpr.sort n)) ",
            "(_ihv : Eq KExpr v (KExpr.sort n) -> Eq KExpr v' (KExpr.sort n)) ",
            "(_ihb0 : Eq KExpr b0 (KExpr.sort n) -> Eq KExpr b0' (KExpr.sort n)) ",
            "(heq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.sort n)) => {discharge})"
        ),
        discharge = sort_struct_discharge("(KExpr.let_ t0 v b0)", "(KExpr.let_ t0' v' b0')"),
    );
    // proj (TRAILING congruence ctor): source proj ps pidx psub, reduct proj ps pidx
    // psub'. A proj is not a sort — same KEXPR_IS_SORT_INLINE discharge. Part of the
    // proj/lit fragment rung.
    let proj_arm = format!(
        concat!(
            "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub' : KExpr) ",
            "(_hsub : par_reduces_cd env psub psub') ",
            "(_ihsub : Eq KExpr psub (KExpr.sort n) -> Eq KExpr psub' (KExpr.sort n)) ",
            "(heq : Eq KExpr (KExpr.proj ps pidx psub) (KExpr.sort n)) => {discharge})"
        ),
        discharge =
            sort_struct_discharge("(KExpr.proj ps pidx psub)", "(KExpr.proj ps pidx psub')"),
    );
    // iota (ATOMIC): source e0 with iota_step (red_rec env) e0 e0'; e0 = sort n is rigid.
    let iota_arm = concat!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hi : iota_step (red_rec env) e0 e0') ",
        "(heq : Eq KExpr e0 (KExpr.sort n)) => ",
        "iota_step_head_none_absurd (red_rec env) (KExpr.sort n) e0' (Eq KExpr e0' (KExpr.sort n)) ",
        "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
        "(Eq.substType KExpr (fun (x : KExpr) => iota_step (red_rec env) x e0') ",
        "e0 (KExpr.sort n) heq hi))"
    );
    // delta (ATOMIC): source e0 with delta_step (red_def env) e0 e0'.
    let delta_arm = concat!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hd : delta_step (red_def env) e0 e0') ",
        "(heq : Eq KExpr e0 (KExpr.sort n)) => ",
        "delta_step_head_none_absurd (red_def env) (KExpr.sort n) e0' (Eq KExpr e0' (KExpr.sort n)) ",
        "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
        "(Eq.substType KExpr (fun (x : KExpr) => delta_step (red_def env) x e0') ",
        "e0 (KExpr.sort n) heq hd))"
    );
    format!(
        concat!(
            "fun (env : RedEnv) (n : Level) (t : KExpr) ",
            "(h : par_reduces_cd env (KExpr.sort n) t) => ",
            "par_reduces_cd.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {delta_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.sort n) t h (Eq.refl KExpr (KExpr.sort n))"
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
        delta_arm = delta_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_reduces_cd_star_sort_inv_eq` (star-level sort rigidity).
/// Induction on the star via `par_reduces_cd_star.rec` with the Prop motive `Eq s (sort
/// n) -> Eq r (sort n)`; the step arm transports each single step onto `Sort n` and
/// Eq-inverts via `par_reduces_cd_sort_inv_eq`.
fn par_reduces_cd_star_sort_inv_eq_proof() -> String {
    let motive = concat!(
        "(fun (s : KExpr) (r : KExpr) (_h : par_reduces_cd_star env s r) => ",
        "Eq KExpr s (KExpr.sort n) -> Eq KExpr r (KExpr.sort n))"
    );
    let refl_arm = "(fun (e : KExpr) (heq : Eq KExpr e (KExpr.sort n)) => heq)";
    let step_arm = concat!(
        "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
        "(hstep : par_reduces_cd env e e') ",
        "(_htail : par_reduces_cd_star env e' e'') ",
        "(ih : Eq KExpr e' (KExpr.sort n) -> Eq KExpr e'' (KExpr.sort n)) ",
        "(heq : Eq KExpr e (KExpr.sort n)) => ",
        "ih (par_reduces_cd_sort_inv_eq env n e' ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_cd env x e') ",
        "e (KExpr.sort n) heq hstep)))"
    );
    format!(
        concat!(
            "fun (env : RedEnv) (n : Level) (w : KExpr) ",
            "(h : par_reduces_cd_star env (KExpr.sort n) w) => ",
            "par_reduces_cd_star.rec env {motive} {refl_arm} {step_arm} ",
            "(KExpr.sort n) w h (Eq.refl KExpr (KExpr.sort n))"
        ),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Closed proof term for `par_cd_sort_injectivity`. Project the common reduct `e3` from
/// the join witness, invert both legs via `par_reduces_cd_star_sort_inv_eq` (`e3 = sort
/// n1`, `e3 = sort n2`), and conclude `sort n1 = sort n2` by `Eq.trans (Eq.symm ..)`.
fn par_cd_sort_injectivity_proof() -> String {
    concat!(
        "fun (env : RedEnv) (n1 : Level) (n2 : Level) ",
        "(w : par_strips_witness_cd_star env (KExpr.sort n1) (KExpr.sort n2)) => ",
        "@par_strips_witness_cd_star.rec env (KExpr.sort n1) (KExpr.sort n2) ",
        "(fun (_w : par_strips_witness_cd_star env (KExpr.sort n1) (KExpr.sort n2)) => ",
        "Eq KExpr (KExpr.sort n1) (KExpr.sort n2)) ",
        "(fun (e3 : KExpr) ",
        "(p1 : par_reduces_cd_star env (KExpr.sort n1) e3) ",
        "(p2 : par_reduces_cd_star env (KExpr.sort n2) e3) => ",
        "Eq.trans KExpr (KExpr.sort n1) e3 (KExpr.sort n2) ",
        "(Eq.symm KExpr e3 (KExpr.sort n1) (par_reduces_cd_star_sort_inv_eq env n1 e3 p1)) ",
        "(par_reduces_cd_star_sort_inv_eq env n2 e3 p2)) ",
        "w"
    )
    .to_string()
}

#[cfg(test)]
#[path = "par_reduces_cd_injectivity_tests.rs"]
mod par_reduces_cd_injectivity_tests;
