// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Front #1 Stage 3/4 prerequisite (the_red_env discharge program): the
//! DEPTH-AWARE closedness checker + its soundness/invariance bridge — the
//! upgrade that lets the one-rfl discharge pattern certify REAL kernel rule
//! RHSs (field-binding lambdas), not just bvar-free terms.
//!
//! ## Why the Stage-1 checkers are not enough
//!
//! The Stage-1 checkers (`env_closed_checkers.rs`) test
//! `nat_eqb (bvar_ceiling rhs) 0` — an ADD-based over-approximation whose 0
//! verdict means BVAR-FREE. Stage 2 measured the honest gap: the checker folds
//! evaluate fast (~10ms over the full reflected `kernel_core_red_env`) but to
//! `Bool.false` — 0/86 real rule RHSs are bvar-free. They are closed LAMBDAS:
//! every bvar is BOUND under a binder (`bvar i` at binder depth `d` with
//! `i < d`). The faithful closedness decision is the standard depth-aware de
//! Bruijn test, and its interface bridge is invariance-under-instantiate/lift
//! for `is_closed_at`-closed terms rather than the ceiling keystones.
//!
//! ## The pieces
//!
//! Checkers (recursive defs, kernel-evaluable on concrete envs):
//! - `nat_lt_b : Nat -> Nat -> Bool` — the Bool mirror of `Lt` (double
//!   `Nat.rec`; no in-tree Bool `<` test existed).
//! - `closed_at_b : KExpr -> Nat -> Bool` — the standard de Bruijn closedness
//!   decision: `bvar i` at depth `d` tests `nat_lt_b i d`; `lam`/`pi` bodies
//!   recurse at `succ d`; `app` folds both legs; `sort`/`const` are closed.
//! - `closed_b e := closed_at_b e 0` — top-level closedness.
//! - `rec_rules_closed_b2` / `rec_env_closed_b2` / `rec_env_lift_closed_b2` /
//!   `def_env_closed_b2` / `def_env_lift_closed_b2` — the Stage-1 env folds
//!   with the per-element test upgraded from `nat_eqb (bvar_ceiling _) 0` to
//!   `closed_b _`. The Stage-1 checkers are KEPT (they are consumed by the
//!   Stage-2 reflection allowlist + artifacts and the Stage-1 regression
//!   demos); the `b2` family is purely additive.
//!
//! Checker soundness (checker-true -> the inductive predicate):
//! - `bool_false_ne_true_t` — Type-valued Bool no-confusion (the in-tree
//!   `bool_false_ne_true` is Prop-CPS; `Lt`/`is_closed_at` live in Type).
//! - `nat_lt_b_sound : nat_lt_b i d = true -> Lt i d` (double `Nat.rec`).
//! - `closed_at_b_sound : closed_at_b e d = true -> is_closed_at e d`
//!   (`KExpr.rec`, depth-universalized motive; binder arms step to `succ d`).
//!
//! The invariance BRIDGE (the interface glue the ceiling keystones provided in
//! Stage 1; the in-tree closedness bundle has only the PRESERVATION direction
//! `lift_preserves_closed` / `instantiate_preserves_closed`, so the identity
//! direction is proved here):
//! - `inst_closed_at_id : is_closed_at e d -> Le d k ->
//!   instantiate_at e val k = e` (`is_closed_at.rec`; the bvar arm chains
//!   `lt_to_le_succ` + `le_trans` into `inst_bvar_lt`).
//! - `lift_closed_at_id : is_closed_at e d -> Le d cutoff ->
//!   lift_at e cutoff amount = e` (the lift mirror via `lift_bvar_lt`).
//!
//! Fold-membership soundness (Stage-1 shape, element test swapped):
//! - `rec_rules_closed_b2_sound` / `rec_env_closed_b2_sound` /
//!   `def_env_closed_b2_sound`.
//!
//! Generic interface discharge (one per closure interface, for ANY env):
//! - `rec_env_closed_of_b2` / `rec_env_lift_closed_of_b2` /
//!   `def_env_closed_of_b2` / `def_env_lift_closed_of_b2`.
//!
//! ## THE PAYOFF (the Stage-4 feasibility gate, for real this time)
//!
//! `add_kernel_core_red_env_closed_witnesses` discharges ALL FOUR closure
//! interfaces over the REFLECTED REAL ENV by the single-rfl route —
//! `<interface>_of_b2 (red_* kernel_core_red_env) (Eq.refl Bool Bool.true)` —
//! so the kernel whnf-EVALUATES `closed_at_b` over all real rule RHSs and def
//! values down to `Bool.true` at registration time. Nothing carried is
//! discharged (the retirement metatheory still consumes the CARRIED bundle);
//! the swap is Stage 4 proper.
//!
//! ## Anti-masquerade
//!
//! ZERO new axioms (census stays 11). The checkers are value-ful recursive
//! defs; every lemma/witness is a real `DerivedProved` term with empty
//! axiom_deps, registered on the fully checked path (no structural bypass).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// A `DerivedProved`, zero-axiom-dep `SpecDefinition` (local mirror of the
    /// Stage-1 `ecc_lemma` helper, which is private to `env_closed_checkers.rs`).
    fn eccd_lemma(
        name: &str,
        type_src: &str,
        value_src: &str,
        description: &str,
        deps: &[&str],
    ) -> SpecDefinition {
        SpecDefinition {
            name: name.to_string(),
            type_src: type_src.to_string(),
            value_src: Some(value_src.to_string()),
            is_axiom: false,
            description: description.to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(deps.iter().map(|s| (*s).to_string()).collect()),
            axiom_deps: HashSet::new(),
        }
    }

    /// Register the Front #1 Stage-3/4 prerequisite: the depth-aware closedness
    /// checkers, their soundness, the instantiate/lift invariance bridge, the
    /// generic `*_of_b2` interface discharge, and the toy-env regression demo.
    pub(super) fn add_env_closed_checkers_depth(&mut self) -> Result<(), SpecError> {
        self.add_depth_checker_defs()?;
        self.add_depth_checker_soundness()?;
        self.add_depth_invariance_bridge()?;
        self.add_depth_env_fold_soundness()?;
        self.add_depth_generic_discharge()?;
        self.add_depth_checker_demo()?;
        Ok(())
    }

    /// The eight checkers. `nat_lt_b` is an explicit double `Nat.rec` (the
    /// `lift_bvar_at` registration style); `closed_at_b` matches on KExpr with
    /// the depth stepping under binders (the `lift_at` recursion shape); the
    /// env folds mirror the Stage-1 checkers with the per-element test
    /// upgraded to `closed_b`.
    fn add_depth_checker_defs(&mut self) -> Result<(), SpecError> {
        // nat_lt_b: the Bool mirror of Lt. Outer Nat.rec on i (motive
        // Nat -> Bool), inner Nat.rec on d: (0, 0) -> false; (0, succ _) ->
        // true; (succ _, 0) -> false; (succ ip, succ dp) -> nat_lt_b ip dp.
        self.add_recursive_def(
            r"def nat_lt_b (i : Nat) (d : Nat) : Bool := Nat.rec (fun (_ : Nat) => Nat -> Bool) (fun (dd : Nat) => Nat.rec (fun (_ : Nat) => Bool) Bool.false (fun (dp : Nat) (_ : Bool) => Bool.true) dd) (fun (ip : Nat) (ih : Nat -> Bool) (dd : Nat) => Nat.rec (fun (_ : Nat) => Bool) Bool.false (fun (dp : Nat) (_ : Bool) => ih dp) dd) i d",
            "Bool mirror of Lt: nat_lt_b i d = true iff i < d. Double Nat.rec (outer on i with a \
             Nat -> Bool motive, inner case split on d); (succ, succ) recurses on both. \
             Kernel-evaluable; the bvar-depth test of closed_at_b. Front #1 Stage 3/4 \
             prerequisite (depth-aware checker).",
        )?;

        // closed_at_b: the standard depth-aware de Bruijn closedness decision.
        self.add_recursive_def(
            r"def closed_at_b (e : KExpr) (d : Nat) : Bool := match e with
| KExpr.sort n => Bool.true
| KExpr.bvar i => nat_lt_b i d
| KExpr.app f a => Bool.and (closed_at_b f d) (closed_at_b a d)
| KExpr.lam ty b => Bool.and (closed_at_b ty d) (closed_at_b b (Nat.succ d))
| KExpr.pi ty b => Bool.and (closed_at_b ty d) (closed_at_b b (Nat.succ d))
| KExpr.const n us => Bool.true
| KExpr.let_ ty v b => Bool.and (closed_at_b ty d) (Bool.and (closed_at_b v d) (closed_at_b b (Nat.succ d)))
| KExpr.proj s i sub => closed_at_b sub d
| KExpr.lit n => Bool.true",
            "Depth-aware de Bruijn closedness decision: every bvar i under binder depth d passes \
             nat_lt_b i d; lam/pi bodies recurse at succ d; sort/const are closed leaves. The \
             lift_at recursion shape, so it kernel-evaluates on concrete terms — including the \
             real (closed-lambda) rule RHSs the Stage-1 ceiling-0 test rejects. Front #1 \
             Stage 3/4 prerequisite (depth-aware checker).",
        )?;

        // closed_b: top-level closedness (depth 0).
        self.add_recursive_def(
            r"def closed_b (e : KExpr) : Bool := closed_at_b e Nat.zero",
            "Top-level de Bruijn closedness: closed_at_b at depth 0. The per-element test of the \
             b2 env checkers. Front #1 Stage 3/4 prerequisite (depth-aware checker).",
        )?;

        // The env folds: Stage-1 shapes with the per-element test upgraded.
        self.add_recursive_def(
            r"def rec_rules_closed_b2 (rs : RecRules) : Bool := match rs with
| RecRules.nil => Bool.true
| RecRules.cons r rest => Bool.and (closed_b (recrule_rhs r)) (rec_rules_closed_b2 rest)",
            "Depth-aware closure checker for a recursor rule list: every rule's rhs passes \
             closed_b (all bvars bound under their binders). The RecRules leg of \
             rec_env_closed_b2; upgrades the Stage-1 ceiling-0 test, which rejects real \
             field-binding lambda RHSs. Front #1 Stage 3/4 prerequisite (depth-aware checker).",
        )?;

        self.add_recursive_def(
            r"def rec_env_closed_b2 (env : RecEnv) : Bool := match env with
| RecEnv.empty => Bool.true
| RecEnv.addRec tail rname mta rules => Bool.and (rec_rules_closed_b2 rules) (rec_env_closed_b2 tail)",
            "Depth-aware closure checker for a recursor environment: every registered recursor's \
             rule list passes rec_rules_closed_b2. A concrete env discharges RecEnvClosed by \
             rec_env_closed_of_b2 + a single Eq.refl Bool.true — including the reflected real \
             env kernel_core_red_env. Front #1 Stage 3/4 prerequisite (depth-aware checker).",
        )?;

        // Lift alias: closedness is ONE decidable test for the inst and lift
        // interfaces; only the discharging bridge differs (inst_closed_at_id
        // vs lift_closed_at_id). Distinct name keeps the checker<->interface
        // pairing uniform (Stage-1 convention).
        self.add_recursive_def(
            r"def rec_env_lift_closed_b2 (env : RecEnv) : Bool := rec_env_closed_b2 env",
            "Depth-aware lift-closure checker for a recursor environment: alias of \
             rec_env_closed_b2 (closedness is one test; the lift interface differs only in the \
             discharging bridge lift_closed_at_id). Front #1 Stage 3/4 prerequisite \
             (depth-aware checker).",
        )?;

        self.add_recursive_def(
            r"def def_env_closed_b2 (env : DefEnv) : Bool := match env with
| DefEnv.empty => Bool.true
| DefEnv.addDef tail dname val => Bool.and (closed_b val) (def_env_closed_b2 tail)",
            "Depth-aware closure checker for a definition environment: every registered \
             definition's value passes closed_b. A concrete env discharges DefEnvClosed by \
             def_env_closed_of_b2 + a single Eq.refl Bool.true. Front #1 Stage 3/4 prerequisite \
             (depth-aware checker).",
        )?;

        self.add_recursive_def(
            r"def def_env_lift_closed_b2 (env : DefEnv) : Bool := def_env_closed_b2 env",
            "Depth-aware lift-closure checker for a definition environment: alias of \
             def_env_closed_b2 (closedness is one test; the lift interface differs only in the \
             discharging bridge lift_closed_at_id). Front #1 Stage 3/4 prerequisite \
             (depth-aware checker).",
        )?;

        Ok(())
    }

    /// Checker soundness: `checker = true` implies the inductive closedness
    /// predicate. `nat_lt_b_sound` by double `Nat.rec` (absurd (_, 0) arms via
    /// the Type-valued Bool no-confusion); `closed_at_b_sound` by `KExpr.rec`
    /// with a depth-universalized motive (binder arms instantiate the IH at
    /// `succ d`; the checker unfolds definitionally on constructor-headed
    /// scrutinees so `band_eq_true_left/right` split each conjunction).
    fn add_depth_checker_soundness(&mut self) -> Result<(), SpecError> {
        // bool_false_ne_true_t: the Type-CPS Bool no-confusion. The in-tree
        // bool_false_ne_true eliminates into Prop only; Lt / is_closed_at are
        // Type-valued, so the absurd checker arms need this mirror.
        self.add_definition(Self::eccd_lemma(
            "bool_false_ne_true_t",
            "forall (C : Type), Eq Bool Bool.false Bool.true -> C",
            "fun (C : Type) (h : Eq Bool Bool.false Bool.true) => \
             Empty.rec (fun (_ : Empty) => C) \
             (Eq.substType Bool \
             (fun (z : Bool) => Bool.rec (fun (_ : Bool) => Type) Nat Empty z) \
             Bool.false Bool.true h Nat.zero)",
            "Bool no-confusion, Type-valued: Eq false true is absurd (CPS into any Type). The \
             Type mirror of bool_false_ne_true (which is Prop-CPS); needed because Lt and \
             is_closed_at live in Type. DerivedProved, zero axiom_deps. Front #1 Stage 3/4 \
             prerequisite (checker soundness).",
            &["Bool.rec", "Empty", "Empty.rec", "Eq.substType"],
        ))?;

        // nat_lt_b_sound: nat_lt_b i d = true -> Lt i d. Outer Nat.rec on i
        // (motive universalized over d), inner Nat.rec on d; the d = 0 arms
        // are absurd (nat_lt_b _ 0 whnf-evaluates to false); (0, succ) is
        // Lt.zero_lt_succ; (succ, succ) recurses (nat_lt_b (succ ip) (succ dp)
        // reduces definitionally to nat_lt_b ip dp).
        self.add_definition(Self::eccd_lemma(
            "nat_lt_b_sound",
            "forall (i : Nat) (d : Nat), Eq Bool (nat_lt_b i d) Bool.true -> Lt i d",
            "fun (i : Nat) (d : Nat) (h : Eq Bool (nat_lt_b i d) Bool.true) => \
             Nat.rec \
             (fun (ii : Nat) => forall (dd : Nat), Eq Bool (nat_lt_b ii dd) Bool.true -> Lt ii dd) \
             (fun (dd : Nat) => Nat.rec \
             (fun (d0 : Nat) => Eq Bool (nat_lt_b Nat.zero d0) Bool.true -> Lt Nat.zero d0) \
             (fun (h0 : Eq Bool (nat_lt_b Nat.zero Nat.zero) Bool.true) => \
             bool_false_ne_true_t (Lt Nat.zero Nat.zero) h0) \
             (fun (dp : Nat) (_ihd : Eq Bool (nat_lt_b Nat.zero dp) Bool.true -> Lt Nat.zero dp) \
             (_h1 : Eq Bool (nat_lt_b Nat.zero (Nat.succ dp)) Bool.true) => \
             Lt.zero_lt_succ dp) \
             dd) \
             (fun (ip : Nat) \
             (ih : forall (dd : Nat), Eq Bool (nat_lt_b ip dd) Bool.true -> Lt ip dd) \
             (dd : Nat) => Nat.rec \
             (fun (d0 : Nat) => Eq Bool (nat_lt_b (Nat.succ ip) d0) Bool.true -> Lt (Nat.succ ip) d0) \
             (fun (h0 : Eq Bool (nat_lt_b (Nat.succ ip) Nat.zero) Bool.true) => \
             bool_false_ne_true_t (Lt (Nat.succ ip) Nat.zero) h0) \
             (fun (dp : Nat) \
             (_ihd : Eq Bool (nat_lt_b (Nat.succ ip) dp) Bool.true -> Lt (Nat.succ ip) dp) \
             (h1 : Eq Bool (nat_lt_b (Nat.succ ip) (Nat.succ dp)) Bool.true) => \
             Lt.succ_lt_succ ip dp (ih dp h1)) \
             dd) \
             i d h",
            "Soundness of the Bool < test: nat_lt_b i d = true -> Lt i d. Double Nat.rec; the \
             d = 0 arms are absurd (bool_false_ne_true_t on the whnf-false hypothesis); (0, succ) \
             is Lt.zero_lt_succ; (succ, succ) applies the IH (the checker reduces definitionally) \
             under Lt.succ_lt_succ. DerivedProved, zero axiom_deps. Front #1 Stage 3/4 \
             prerequisite (checker soundness).",
            &["Nat.rec", "nat_lt_b", "bool_false_ne_true_t", "Lt"],
        ))?;

        // closed_at_b_sound: closed_at_b e d = true -> is_closed_at e d.
        self.add_definition(Self::eccd_lemma(
            "closed_at_b_sound",
            "forall (e : KExpr) (d : Nat), \
             Eq Bool (closed_at_b e d) Bool.true -> is_closed_at e d",
            "fun (e : KExpr) (d : Nat) (h : Eq Bool (closed_at_b e d) Bool.true) => \
             KExpr.rec \
             (fun (x : KExpr) => forall (dd : Nat), \
             Eq Bool (closed_at_b x dd) Bool.true -> is_closed_at x dd) \
             (fun (n : Level) (dd : Nat) \
             (_hb : Eq Bool (closed_at_b (KExpr.sort n) dd) Bool.true) => \
             is_closed_at.sort n dd) \
             (fun (i : Nat) (dd : Nat) \
             (hb : Eq Bool (closed_at_b (KExpr.bvar i) dd) Bool.true) => \
             is_closed_at.bvar i dd (nat_lt_b_sound i dd hb)) \
             (fun (f : KExpr) (a : KExpr) \
             (ihf : forall (dd : Nat), Eq Bool (closed_at_b f dd) Bool.true -> is_closed_at f dd) \
             (iha : forall (dd : Nat), Eq Bool (closed_at_b a dd) Bool.true -> is_closed_at a dd) \
             (dd : Nat) (hb : Eq Bool (closed_at_b (KExpr.app f a) dd) Bool.true) => \
             is_closed_at.app f a dd \
             (ihf dd (band_eq_true_left (closed_at_b f dd) (closed_at_b a dd) hb)) \
             (iha dd (band_eq_true_right (closed_at_b f dd) (closed_at_b a dd) hb))) \
             (fun (ty : KExpr) (b : KExpr) \
             (ihty : forall (dd : Nat), Eq Bool (closed_at_b ty dd) Bool.true -> is_closed_at ty dd) \
             (ihb : forall (dd : Nat), Eq Bool (closed_at_b b dd) Bool.true -> is_closed_at b dd) \
             (dd : Nat) (hb : Eq Bool (closed_at_b (KExpr.lam ty b) dd) Bool.true) => \
             is_closed_at.lam ty b dd \
             (ihty dd (band_eq_true_left (closed_at_b ty dd) (closed_at_b b (Nat.succ dd)) hb)) \
             (ihb (Nat.succ dd) (band_eq_true_right (closed_at_b ty dd) (closed_at_b b (Nat.succ dd)) hb))) \
             (fun (ty : KExpr) (b : KExpr) \
             (ihty : forall (dd : Nat), Eq Bool (closed_at_b ty dd) Bool.true -> is_closed_at ty dd) \
             (ihb : forall (dd : Nat), Eq Bool (closed_at_b b dd) Bool.true -> is_closed_at b dd) \
             (dd : Nat) (hb : Eq Bool (closed_at_b (KExpr.pi ty b) dd) Bool.true) => \
             is_closed_at.pi ty b dd \
             (ihty dd (band_eq_true_left (closed_at_b ty dd) (closed_at_b b (Nat.succ dd)) hb)) \
             (ihb (Nat.succ dd) (band_eq_true_right (closed_at_b ty dd) (closed_at_b b (Nat.succ dd)) hb))) \
             (fun (nm : Name) (us : ListType Level) (dd : Nat) \
             (_hb : Eq Bool (closed_at_b (KExpr.const nm us) dd) Bool.true) => \
             is_closed_at.const nm us dd) \
             (fun (ty : KExpr) (val : KExpr) (body : KExpr) \
             (ihty : forall (dd : Nat), Eq Bool (closed_at_b ty dd) Bool.true -> is_closed_at ty dd) \
             (ihval : forall (dd : Nat), Eq Bool (closed_at_b val dd) Bool.true -> is_closed_at val dd) \
             (ihbody : forall (dd : Nat), Eq Bool (closed_at_b body dd) Bool.true -> is_closed_at body dd) \
             (dd : Nat) (hb : Eq Bool (closed_at_b (KExpr.let_ ty val body) dd) Bool.true) => \
             is_closed_at.let_ ty val body dd \
             (ihty dd (band_eq_true_left (closed_at_b ty dd) (Bool.and (closed_at_b val dd) (closed_at_b body (Nat.succ dd))) hb)) \
             (ihval dd (band_eq_true_left (closed_at_b val dd) (closed_at_b body (Nat.succ dd)) (band_eq_true_right (closed_at_b ty dd) (Bool.and (closed_at_b val dd) (closed_at_b body (Nat.succ dd))) hb))) \
             (ihbody (Nat.succ dd) (band_eq_true_right (closed_at_b val dd) (closed_at_b body (Nat.succ dd)) (band_eq_true_right (closed_at_b ty dd) (Bool.and (closed_at_b val dd) (closed_at_b body (Nat.succ dd))) hb)))) \
             (fun (s : Name) (i : Nat) (sub : KExpr) \
             (ihsub : forall (dd : Nat), Eq Bool (closed_at_b sub dd) Bool.true -> is_closed_at sub dd) \
             (dd : Nat) (hb : Eq Bool (closed_at_b (KExpr.proj s i sub) dd) Bool.true) => \
             is_closed_at.proj s i sub dd (ihsub dd hb)) \
             (fun (v : Nat) (dd : Nat) \
             (_hb : Eq Bool (closed_at_b (KExpr.lit v) dd) Bool.true) => \
             is_closed_at.lit v dd) \
             e d h",
            "Soundness of the depth-aware checker: closed_at_b e d = true -> is_closed_at e d. \
             KExpr.rec with a depth-universalized motive; the bvar arm is nat_lt_b_sound -> \
             is_closed_at.bvar; app/lam/pi split the conjunction (band_eq_true_left/right — the \
             checker unfolds definitionally on the constructor-headed scrutinee), with the \
             binder-body IH instantiated at succ d. DerivedProved, zero axiom_deps. Front #1 \
             Stage 3/4 prerequisite (checker soundness).",
            &[
                "KExpr.rec",
                "closed_at_b",
                "nat_lt_b_sound",
                "is_closed_at",
                "band_eq_true_left",
                "band_eq_true_right",
                "Bool.and",
            ],
        ))?;

        Ok(())
    }

    /// The invariance BRIDGE: an `is_closed_at`-closed term is fixed by
    /// `instantiate_at` / `lift_at` at any depth/cutoff at-or-above its
    /// closedness depth. The in-tree closedness bundle has only the
    /// PRESERVATION direction; the identity direction is a direct
    /// `is_closed_at.rec` induction (the bvar arm converts `Lt i d` + `Le d k`
    /// into `Le (succ i) k` via `lt_to_le_succ` + `le_trans` and closes with
    /// the `inst_bvar_lt` / `lift_bvar_lt` primitives; binder arms step the
    /// bound via `le_succ_succ`).
    fn add_depth_invariance_bridge(&mut self) -> Result<(), SpecError> {
        // inst_closed_at_id: is_closed_at e d -> Le d k ->
        // instantiate_at e val k = e.
        self.add_definition(Self::eccd_lemma(
            "inst_closed_at_id",
            "forall (e : KExpr) (d : Nat), is_closed_at e d -> \
             forall (val : KExpr) (k : Nat), Le d k -> \
             Eq KExpr (instantiate_at e val k) e",
            "fun (e : KExpr) (d : Nat) (h : is_closed_at e d) => \
             is_closed_at.rec \
             (fun (e0 : KExpr) (D : Nat) (_hc : is_closed_at e0 D) => \
             forall (v : KExpr) (k : Nat), Le D k -> Eq KExpr (instantiate_at e0 v k) e0) \
             (fun (n : Level) (D : Nat) (v : KExpr) (k : Nat) (_hk : Le D k) => \
             instantiate_at_sort n v k) \
             (fun (i : Nat) (D : Nat) (hlt : Lt i D) (v : KExpr) (k : Nat) (hk : Le D k) => \
             Eq.trans KExpr \
             (instantiate_at (KExpr.bvar i) v k) \
             (instantiate_bvar_at i k v) \
             (KExpr.bvar i) \
             (instantiate_at_bvar i v k) \
             (inst_bvar_lt i k v \
             (le_trans (Nat.succ i) D k (lt_to_le_succ i D hlt) hk))) \
             (fun (f : KExpr) (g : KExpr) (D : Nat) \
             (_hf : is_closed_at f D) (_hg : is_closed_at g D) \
             (ihf : forall (v : KExpr) (k : Nat), Le D k -> Eq KExpr (instantiate_at f v k) f) \
             (ihg : forall (v : KExpr) (k : Nat), Le D k -> Eq KExpr (instantiate_at g v k) g) \
             (v : KExpr) (k : Nat) (hk : Le D k) => \
             Eq.trans KExpr \
             (instantiate_at (KExpr.app f g) v k) \
             (KExpr.app (instantiate_at f v k) (instantiate_at g v k)) \
             (KExpr.app f g) \
             (instantiate_at_app f g v k) \
             (Eq.trans KExpr \
             (KExpr.app (instantiate_at f v k) (instantiate_at g v k)) \
             (KExpr.app f (instantiate_at g v k)) \
             (KExpr.app f g) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.app x (instantiate_at g v k)) \
             (instantiate_at f v k) f (ihf v k hk)) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.app f x) \
             (instantiate_at g v k) g (ihg v k hk)))) \
             (fun (ty : KExpr) (b : KExpr) (D : Nat) \
             (_hty : is_closed_at ty D) (_hb : is_closed_at b (Nat.succ D)) \
             (ihty : forall (v : KExpr) (k : Nat), Le D k -> Eq KExpr (instantiate_at ty v k) ty) \
             (ihb : forall (v : KExpr) (k : Nat), Le (Nat.succ D) k -> Eq KExpr (instantiate_at b v k) b) \
             (v : KExpr) (k : Nat) (hk : Le D k) => \
             Eq.trans KExpr \
             (instantiate_at (KExpr.lam ty b) v k) \
             (KExpr.lam (instantiate_at ty v k) (instantiate_at b v (Nat.succ k))) \
             (KExpr.lam ty b) \
             (instantiate_at_lam ty b v k) \
             (Eq.trans KExpr \
             (KExpr.lam (instantiate_at ty v k) (instantiate_at b v (Nat.succ k))) \
             (KExpr.lam ty (instantiate_at b v (Nat.succ k))) \
             (KExpr.lam ty b) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.lam x (instantiate_at b v (Nat.succ k))) \
             (instantiate_at ty v k) ty (ihty v k hk)) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.lam ty x) \
             (instantiate_at b v (Nat.succ k)) b \
             (ihb v (Nat.succ k) (le_succ_succ D k hk))))) \
             (fun (ty : KExpr) (b : KExpr) (D : Nat) \
             (_hty : is_closed_at ty D) (_hb : is_closed_at b (Nat.succ D)) \
             (ihty : forall (v : KExpr) (k : Nat), Le D k -> Eq KExpr (instantiate_at ty v k) ty) \
             (ihb : forall (v : KExpr) (k : Nat), Le (Nat.succ D) k -> Eq KExpr (instantiate_at b v k) b) \
             (v : KExpr) (k : Nat) (hk : Le D k) => \
             Eq.trans KExpr \
             (instantiate_at (KExpr.pi ty b) v k) \
             (KExpr.pi (instantiate_at ty v k) (instantiate_at b v (Nat.succ k))) \
             (KExpr.pi ty b) \
             (instantiate_at_pi ty b v k) \
             (Eq.trans KExpr \
             (KExpr.pi (instantiate_at ty v k) (instantiate_at b v (Nat.succ k))) \
             (KExpr.pi ty (instantiate_at b v (Nat.succ k))) \
             (KExpr.pi ty b) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.pi x (instantiate_at b v (Nat.succ k))) \
             (instantiate_at ty v k) ty (ihty v k hk)) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.pi ty x) \
             (instantiate_at b v (Nat.succ k)) b \
             (ihb v (Nat.succ k) (le_succ_succ D k hk))))) \
             (fun (nm : Name) (us : ListType Level) (D : Nat) \
             (v : KExpr) (k : Nat) (_hk : Le D k) => \
             instantiate_at_const nm us v k) \
             (fun (ty : KExpr) (val : KExpr) (body : KExpr) (D : Nat) \
             (_hty : is_closed_at ty D) (_hval : is_closed_at val D) (_hbody : is_closed_at body (Nat.succ D)) \
             (ihty : forall (v : KExpr) (k : Nat), Le D k -> Eq KExpr (instantiate_at ty v k) ty) \
             (ihval : forall (v : KExpr) (k : Nat), Le D k -> Eq KExpr (instantiate_at val v k) val) \
             (ihbody : forall (v : KExpr) (k : Nat), Le (Nat.succ D) k -> Eq KExpr (instantiate_at body v k) body) \
             (v : KExpr) (k : Nat) (hk : Le D k) => \
             Eq.trans KExpr \
             (instantiate_at (KExpr.let_ ty val body) v k) \
             (KExpr.let_ (instantiate_at ty v k) (instantiate_at val v k) (instantiate_at body v (Nat.succ k))) \
             (KExpr.let_ ty val body) \
             (instantiate_at_let_ ty val body v k) \
             (Eq.trans KExpr \
             (KExpr.let_ (instantiate_at ty v k) (instantiate_at val v k) (instantiate_at body v (Nat.succ k))) \
             (KExpr.let_ ty (instantiate_at val v k) (instantiate_at body v (Nat.succ k))) \
             (KExpr.let_ ty val body) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.let_ x (instantiate_at val v k) (instantiate_at body v (Nat.succ k))) \
             (instantiate_at ty v k) ty (ihty v k hk)) \
             (Eq.trans KExpr \
             (KExpr.let_ ty (instantiate_at val v k) (instantiate_at body v (Nat.succ k))) \
             (KExpr.let_ ty val (instantiate_at body v (Nat.succ k))) \
             (KExpr.let_ ty val body) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.let_ ty x (instantiate_at body v (Nat.succ k))) \
             (instantiate_at val v k) val (ihval v k hk)) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.let_ ty val x) \
             (instantiate_at body v (Nat.succ k)) body \
             (ihbody v (Nat.succ k) (le_succ_succ D k hk)))))) \
             (fun (s : Name) (i : Nat) (sub : KExpr) (D : Nat) \
             (_hsub : is_closed_at sub D) \
             (ihsub : forall (v : KExpr) (k : Nat), Le D k -> Eq KExpr (instantiate_at sub v k) sub) \
             (v : KExpr) (k : Nat) (hk : Le D k) => \
             Eq.trans KExpr \
             (instantiate_at (KExpr.proj s i sub) v k) \
             (KExpr.proj s i (instantiate_at sub v k)) \
             (KExpr.proj s i sub) \
             (instantiate_at_proj s i sub v k) \
             (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj s i x) (instantiate_at sub v k) sub (ihsub v k hk))) \
             (fun (litv : Nat) (D : Nat) (v : KExpr) (k : Nat) (_hk : Le D k) => \
             instantiate_at_lit litv v k) \
             e d h",
            "INVARIANCE BRIDGE (inst): is_closed_at e d -> Le d k -> instantiate_at e val k = e. \
             Substitution at-or-above the closedness depth is the identity — the depth-aware \
             replacement for the ceiling keystone inst_above_ceiling_id. is_closed_at.rec with a \
             (val, k)-universalized motive: the bvar arm chains lt_to_le_succ + le_trans into \
             inst_bvar_lt; app/lam/pi rebuild via the instantiate_at unfoldings + Eq.cong \
             (binder bounds step via le_succ_succ). DerivedProved, zero axiom_deps. Front #1 \
             Stage 3/4 prerequisite (invariance bridge).",
            &[
                "is_closed_at.rec",
                "instantiate_at",
                "instantiate_at_sort",
                "instantiate_at_bvar",
                "instantiate_at_app",
                "instantiate_at_lam",
                "instantiate_at_pi",
                "instantiate_at_const",
                "instantiate_at_let_",
                "instantiate_at_proj",
                "instantiate_at_lit",
                "inst_bvar_lt",
                "lt_to_le_succ",
                "le_trans",
                "le_succ_succ",
                "Eq.trans",
                "Eq.cong",
            ],
        ))?;

        // lift_closed_at_id: is_closed_at e d -> Le d cutoff ->
        // lift_at e cutoff amount = e.
        self.add_definition(Self::eccd_lemma(
            "lift_closed_at_id",
            "forall (e : KExpr) (d : Nat), is_closed_at e d -> \
             forall (cutoff : Nat) (amount : Nat), Le d cutoff -> \
             Eq KExpr (lift_at e cutoff amount) e",
            "fun (e : KExpr) (d : Nat) (h : is_closed_at e d) => \
             is_closed_at.rec \
             (fun (e0 : KExpr) (D : Nat) (_hc : is_closed_at e0 D) => \
             forall (c : Nat) (a : Nat), Le D c -> Eq KExpr (lift_at e0 c a) e0) \
             (fun (n : Level) (D : Nat) (c : Nat) (a : Nat) (_hk : Le D c) => \
             lift_at_sort n c a) \
             (fun (i : Nat) (D : Nat) (hlt : Lt i D) (c : Nat) (a : Nat) (hk : Le D c) => \
             lift_bvar_lt i c a \
             (le_trans (Nat.succ i) D c (lt_to_le_succ i D hlt) hk)) \
             (fun (f : KExpr) (g : KExpr) (D : Nat) \
             (_hf : is_closed_at f D) (_hg : is_closed_at g D) \
             (ihf : forall (c : Nat) (a : Nat), Le D c -> Eq KExpr (lift_at f c a) f) \
             (ihg : forall (c : Nat) (a : Nat), Le D c -> Eq KExpr (lift_at g c a) g) \
             (c : Nat) (a : Nat) (hk : Le D c) => \
             Eq.trans KExpr \
             (lift_at (KExpr.app f g) c a) \
             (KExpr.app (lift_at f c a) (lift_at g c a)) \
             (KExpr.app f g) \
             (lift_at_app f g c a) \
             (Eq.trans KExpr \
             (KExpr.app (lift_at f c a) (lift_at g c a)) \
             (KExpr.app f (lift_at g c a)) \
             (KExpr.app f g) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.app x (lift_at g c a)) \
             (lift_at f c a) f (ihf c a hk)) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.app f x) \
             (lift_at g c a) g (ihg c a hk)))) \
             (fun (ty : KExpr) (b : KExpr) (D : Nat) \
             (_hty : is_closed_at ty D) (_hb : is_closed_at b (Nat.succ D)) \
             (ihty : forall (c : Nat) (a : Nat), Le D c -> Eq KExpr (lift_at ty c a) ty) \
             (ihb : forall (c : Nat) (a : Nat), Le (Nat.succ D) c -> Eq KExpr (lift_at b c a) b) \
             (c : Nat) (a : Nat) (hk : Le D c) => \
             Eq.trans KExpr \
             (lift_at (KExpr.lam ty b) c a) \
             (KExpr.lam (lift_at ty c a) (lift_at b (Nat.succ c) a)) \
             (KExpr.lam ty b) \
             (lift_at_lam ty b c a) \
             (Eq.trans KExpr \
             (KExpr.lam (lift_at ty c a) (lift_at b (Nat.succ c) a)) \
             (KExpr.lam ty (lift_at b (Nat.succ c) a)) \
             (KExpr.lam ty b) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.lam x (lift_at b (Nat.succ c) a)) \
             (lift_at ty c a) ty (ihty c a hk)) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.lam ty x) \
             (lift_at b (Nat.succ c) a) b \
             (ihb (Nat.succ c) a (le_succ_succ D c hk))))) \
             (fun (ty : KExpr) (b : KExpr) (D : Nat) \
             (_hty : is_closed_at ty D) (_hb : is_closed_at b (Nat.succ D)) \
             (ihty : forall (c : Nat) (a : Nat), Le D c -> Eq KExpr (lift_at ty c a) ty) \
             (ihb : forall (c : Nat) (a : Nat), Le (Nat.succ D) c -> Eq KExpr (lift_at b c a) b) \
             (c : Nat) (a : Nat) (hk : Le D c) => \
             Eq.trans KExpr \
             (lift_at (KExpr.pi ty b) c a) \
             (KExpr.pi (lift_at ty c a) (lift_at b (Nat.succ c) a)) \
             (KExpr.pi ty b) \
             (lift_at_pi ty b c a) \
             (Eq.trans KExpr \
             (KExpr.pi (lift_at ty c a) (lift_at b (Nat.succ c) a)) \
             (KExpr.pi ty (lift_at b (Nat.succ c) a)) \
             (KExpr.pi ty b) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.pi x (lift_at b (Nat.succ c) a)) \
             (lift_at ty c a) ty (ihty c a hk)) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.pi ty x) \
             (lift_at b (Nat.succ c) a) b \
             (ihb (Nat.succ c) a (le_succ_succ D c hk))))) \
             (fun (nm : Name) (us : ListType Level) (D : Nat) \
             (c : Nat) (a : Nat) (_hk : Le D c) => \
             lift_at_const nm us c a) \
             (fun (ty : KExpr) (val : KExpr) (body : KExpr) (D : Nat) \
             (_hty : is_closed_at ty D) (_hval : is_closed_at val D) (_hbody : is_closed_at body (Nat.succ D)) \
             (ihty : forall (c : Nat) (a : Nat), Le D c -> Eq KExpr (lift_at ty c a) ty) \
             (ihval : forall (c : Nat) (a : Nat), Le D c -> Eq KExpr (lift_at val c a) val) \
             (ihbody : forall (c : Nat) (a : Nat), Le (Nat.succ D) c -> Eq KExpr (lift_at body c a) body) \
             (c : Nat) (a : Nat) (hk : Le D c) => \
             Eq.trans KExpr \
             (lift_at (KExpr.let_ ty val body) c a) \
             (KExpr.let_ (lift_at ty c a) (lift_at val c a) (lift_at body (Nat.succ c) a)) \
             (KExpr.let_ ty val body) \
             (lift_at_let_ ty val body c a) \
             (Eq.trans KExpr \
             (KExpr.let_ (lift_at ty c a) (lift_at val c a) (lift_at body (Nat.succ c) a)) \
             (KExpr.let_ ty (lift_at val c a) (lift_at body (Nat.succ c) a)) \
             (KExpr.let_ ty val body) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.let_ x (lift_at val c a) (lift_at body (Nat.succ c) a)) \
             (lift_at ty c a) ty (ihty c a hk)) \
             (Eq.trans KExpr \
             (KExpr.let_ ty (lift_at val c a) (lift_at body (Nat.succ c) a)) \
             (KExpr.let_ ty val (lift_at body (Nat.succ c) a)) \
             (KExpr.let_ ty val body) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.let_ ty x (lift_at body (Nat.succ c) a)) \
             (lift_at val c a) val (ihval c a hk)) \
             (Eq.cong KExpr KExpr \
             (fun (x : KExpr) => KExpr.let_ ty val x) \
             (lift_at body (Nat.succ c) a) body \
             (ihbody (Nat.succ c) a (le_succ_succ D c hk)))))) \
             (fun (s : Name) (i : Nat) (sub : KExpr) (D : Nat) \
             (_hsub : is_closed_at sub D) \
             (ihsub : forall (c : Nat) (a : Nat), Le D c -> Eq KExpr (lift_at sub c a) sub) \
             (c : Nat) (a : Nat) (hk : Le D c) => \
             Eq.trans KExpr \
             (lift_at (KExpr.proj s i sub) c a) \
             (KExpr.proj s i (lift_at sub c a)) \
             (KExpr.proj s i sub) \
             (lift_at_proj s i sub c a) \
             (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.proj s i x) (lift_at sub c a) sub (ihsub c a hk))) \
             (fun (litv : Nat) (D : Nat) (c : Nat) (a : Nat) (_hk : Le D c) => \
             lift_at_lit litv c a) \
             e d h",
            "INVARIANCE BRIDGE (lift): is_closed_at e d -> Le d cutoff -> \
             lift_at e cutoff amount = e. Lifting at a cutoff at-or-above the closedness depth \
             is the identity — the depth-aware replacement for the ceiling keystone \
             lift_ceiling_id. Same is_closed_at.rec shape as inst_closed_at_id; the bvar arm \
             closes with lift_bvar_lt. DerivedProved, zero axiom_deps. Front #1 Stage 3/4 \
             prerequisite (invariance bridge).",
            &[
                "is_closed_at.rec",
                "lift_at",
                "lift_at_sort",
                "lift_at_app",
                "lift_at_lam",
                "lift_at_pi",
                "lift_at_const",
                "lift_at_let_",
                "lift_at_proj",
                "lift_at_lit",
                "lift_bvar_lt",
                "lt_to_le_succ",
                "le_trans",
                "le_succ_succ",
                "Eq.trans",
                "Eq.cong",
            ],
        ))?;

        Ok(())
    }

    /// The fold-membership soundness lemmas for the b2 folds: checker-true
    /// implies every looked-up element passes `closed_b`. Exact Stage-1 shapes
    /// (structural induction + `opt_pick_some_inv` on the lookup fold) with
    /// the per-element test swapped.
    fn add_depth_env_fold_soundness(&mut self) -> Result<(), SpecError> {
        // rec_rules_closed_b2_sound: rules-level fold membership.
        self.add_definition(Self::eccd_lemma(
            "rec_rules_closed_b2_sound",
            "forall (rs : RecRules) (cname : Name) (rule : RecRule), \
             Eq (OptionType RecRule) (recrule_in_rules rs cname) (OptionType.some RecRule rule) -> \
             Eq Bool (rec_rules_closed_b2 rs) Bool.true -> \
             Eq Bool (closed_b (recrule_rhs rule)) Bool.true",
            "fun (rs : RecRules) (cname : Name) (rule : RecRule) => \
             RecRules.rec \
             (fun (l : RecRules) => \
             Eq (OptionType RecRule) (recrule_in_rules l cname) (OptionType.some RecRule rule) -> \
             Eq Bool (rec_rules_closed_b2 l) Bool.true -> \
             Eq Bool (closed_b (recrule_rhs rule)) Bool.true) \
             (fun (hlk : Eq (OptionType RecRule) (recrule_in_rules RecRules.nil cname) (OptionType.some RecRule rule)) \
             (_hb : Eq Bool (rec_rules_closed_b2 RecRules.nil) Bool.true) => \
             option_none_ne_some RecRule rule \
             (Eq Bool (closed_b (recrule_rhs rule)) Bool.true) hlk) \
             (fun (r : RecRule) (rest : RecRules) \
             (ih : Eq (OptionType RecRule) (recrule_in_rules rest cname) (OptionType.some RecRule rule) -> \
             Eq Bool (rec_rules_closed_b2 rest) Bool.true -> \
             Eq Bool (closed_b (recrule_rhs rule)) Bool.true) \
             (hlk : Eq (OptionType RecRule) (recrule_in_rules (RecRules.cons r rest) cname) (OptionType.some RecRule rule)) \
             (hb : Eq Bool (rec_rules_closed_b2 (RecRules.cons r rest)) Bool.true) => \
             opt_pick_some_inv RecRule (name_eqb (recrule_ctor_name r) cname) r \
             (recrule_in_rules rest cname) rule \
             (Eq Bool (closed_b (recrule_rhs rule)) Bool.true) hlk \
             (fun (_ht : Eq Bool (name_eqb (recrule_ctor_name r) cname) Bool.true) \
             (hval : Eq RecRule r rule) => \
             Eq.subst RecRule \
             (fun (z : RecRule) => Eq Bool (closed_b (recrule_rhs z)) Bool.true) \
             r rule hval \
             (band_eq_true_left (closed_b (recrule_rhs r)) (rec_rules_closed_b2 rest) hb)) \
             (fun (_hf : Eq Bool (name_eqb (recrule_ctor_name r) cname) Bool.false) \
             (hrest : Eq (OptionType RecRule) (recrule_in_rules rest cname) (OptionType.some RecRule rule)) => \
             ih hrest \
             (band_eq_true_right (closed_b (recrule_rhs r)) (rec_rules_closed_b2 rest) hb))) \
             rs",
            "Fold-membership (rules level, depth-aware): recrule_in_rules rs cname = some rule \
             and rec_rules_closed_b2 rs = true imply closed_b (recrule_rhs rule) = true. \
             RecRules.rec; nil lookup is absurd (option_none_ne_some); cons splits the opt_pick \
             fire (transport the left band conjunct along r = rule) / fall-through (IH on the \
             right band conjunct). The Stage-1 shape with the element test upgraded. \
             DerivedProved, zero axiom_deps. Front #1 Stage 3/4 prerequisite (fold soundness).",
            &[
                "RecRules.rec",
                "recrule_in_rules",
                "recrule_ctor_name",
                "recrule_rhs",
                "rec_rules_closed_b2",
                "closed_b",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "Eq.subst",
            ],
        ))?;

        // rec_env_closed_b2_sound: env-level fold membership.
        self.add_definition(Self::eccd_lemma(
            "rec_env_closed_b2_sound",
            "forall (env : RecEnv) (rname : Name) (rules : RecRules), \
             Eq (OptionType RecRules) (recrules_for env rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_closed_b2 env) Bool.true -> \
             Eq Bool (rec_rules_closed_b2 rules) Bool.true",
            "fun (env : RecEnv) (rname : Name) (rules : RecRules) => \
             RecEnv.rec \
             (fun (e : RecEnv) => \
             Eq (OptionType RecRules) (recrules_for e rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_closed_b2 e) Bool.true -> \
             Eq Bool (rec_rules_closed_b2 rules) Bool.true) \
             (fun (hlk : Eq (OptionType RecRules) (recrules_for RecEnv.empty rname) (OptionType.some RecRules rules)) \
             (_hb : Eq Bool (rec_env_closed_b2 RecEnv.empty) Bool.true) => \
             option_none_ne_some RecRules rules \
             (Eq Bool (rec_rules_closed_b2 rules) Bool.true) hlk) \
             (fun (tail : RecEnv) (rn : Name) (mta : RecMeta) (rls : RecRules) \
             (ih : Eq (OptionType RecRules) (recrules_for tail rname) (OptionType.some RecRules rules) -> \
             Eq Bool (rec_env_closed_b2 tail) Bool.true -> \
             Eq Bool (rec_rules_closed_b2 rules) Bool.true) \
             (hlk : Eq (OptionType RecRules) (recrules_for (RecEnv.addRec tail rn mta rls) rname) (OptionType.some RecRules rules)) \
             (hb : Eq Bool (rec_env_closed_b2 (RecEnv.addRec tail rn mta rls)) Bool.true) => \
             opt_pick_some_inv RecRules (name_eqb rn rname) rls \
             (recrules_for tail rname) rules \
             (Eq Bool (rec_rules_closed_b2 rules) Bool.true) hlk \
             (fun (_ht : Eq Bool (name_eqb rn rname) Bool.true) \
             (hval : Eq RecRules rls rules) => \
             Eq.subst RecRules \
             (fun (z : RecRules) => Eq Bool (rec_rules_closed_b2 z) Bool.true) \
             rls rules hval \
             (band_eq_true_left (rec_rules_closed_b2 rls) (rec_env_closed_b2 tail) hb)) \
             (fun (_hf : Eq Bool (name_eqb rn rname) Bool.false) \
             (htail : Eq (OptionType RecRules) (recrules_for tail rname) (OptionType.some RecRules rules)) => \
             ih htail \
             (band_eq_true_right (rec_rules_closed_b2 rls) (rec_env_closed_b2 tail) hb))) \
             env",
            "Fold-membership (env level, depth-aware): recrules_for env rname = some rules and \
             rec_env_closed_b2 env = true imply rec_rules_closed_b2 rules = true. RecEnv.rec; \
             empty lookup is absurd (option_none_ne_some); addRec splits the opt_pick fire \
             (transport the left band conjunct along rls = rules) / fall-through (IH on the \
             right band conjunct). The Stage-1 shape with the element test upgraded. \
             DerivedProved, zero axiom_deps. Front #1 Stage 3/4 prerequisite (fold soundness).",
            &[
                "RecEnv.rec",
                "recrules_for",
                "rec_env_closed_b2",
                "rec_rules_closed_b2",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "Eq.subst",
            ],
        ))?;

        // def_env_closed_b2_sound: def-env fold membership (single-level).
        self.add_definition(Self::eccd_lemma(
            "def_env_closed_b2_sound",
            "forall (env : DefEnv) (dname : Name) (defval : KExpr), \
             Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr defval) -> \
             Eq Bool (def_env_closed_b2 env) Bool.true -> \
             Eq Bool (closed_b defval) Bool.true",
            "fun (env : DefEnv) (dname : Name) (defval : KExpr) => \
             DefEnv.rec \
             (fun (e : DefEnv) => \
             Eq (OptionType KExpr) (defval_for e dname) (OptionType.some KExpr defval) -> \
             Eq Bool (def_env_closed_b2 e) Bool.true -> \
             Eq Bool (closed_b defval) Bool.true) \
             (fun (hlk : Eq (OptionType KExpr) (defval_for DefEnv.empty dname) (OptionType.some KExpr defval)) \
             (_hb : Eq Bool (def_env_closed_b2 DefEnv.empty) Bool.true) => \
             option_none_ne_some KExpr defval \
             (Eq Bool (closed_b defval) Bool.true) hlk) \
             (fun (tail : DefEnv) (dn : Name) (dv : KExpr) \
             (ih : Eq (OptionType KExpr) (defval_for tail dname) (OptionType.some KExpr defval) -> \
             Eq Bool (def_env_closed_b2 tail) Bool.true -> \
             Eq Bool (closed_b defval) Bool.true) \
             (hlk : Eq (OptionType KExpr) (defval_for (DefEnv.addDef tail dn dv) dname) (OptionType.some KExpr defval)) \
             (hb : Eq Bool (def_env_closed_b2 (DefEnv.addDef tail dn dv)) Bool.true) => \
             opt_pick_some_inv KExpr (name_eqb dn dname) dv \
             (defval_for tail dname) defval \
             (Eq Bool (closed_b defval) Bool.true) hlk \
             (fun (_ht : Eq Bool (name_eqb dn dname) Bool.true) \
             (hval : Eq KExpr dv defval) => \
             Eq.subst KExpr \
             (fun (z : KExpr) => Eq Bool (closed_b z) Bool.true) \
             dv defval hval \
             (band_eq_true_left (closed_b dv) (def_env_closed_b2 tail) hb)) \
             (fun (_hf : Eq Bool (name_eqb dn dname) Bool.false) \
             (htail : Eq (OptionType KExpr) (defval_for tail dname) (OptionType.some KExpr defval)) => \
             ih htail \
             (band_eq_true_right (closed_b dv) (def_env_closed_b2 tail) hb))) \
             env",
            "Fold-membership (def-env level, depth-aware): defval_for env dname = some defval and \
             def_env_closed_b2 env = true imply closed_b defval = true. DefEnv.rec; empty lookup \
             is absurd (option_none_ne_some); addDef splits the opt_pick fire (transport the \
             left band conjunct along dv = defval) / fall-through (IH on the right band \
             conjunct). The Stage-1 shape with the element test upgraded. DerivedProved, zero \
             axiom_deps. Front #1 Stage 3/4 prerequisite (fold soundness).",
            &[
                "DefEnv.rec",
                "defval_for",
                "def_env_closed_b2",
                "closed_b",
                "opt_pick_some_inv",
                "option_none_ne_some",
                "band_eq_true_left",
                "band_eq_true_right",
                "name_eqb",
                "Eq.subst",
            ],
        ))?;

        Ok(())
    }

    /// The four generic interface-discharge lemmas: `b2`-checker-true ->
    /// interface, for ANY env. Decompose the lookup, run the fold-membership
    /// chain to the per-element `closed_b` fact, convert to `is_closed_at _ 0`
    /// (`closed_at_b_sound`), and close with the invariance bridge at the
    /// interface's arbitrary depth/cutoff (`le_zero_n` supplies `Le 0 _`).
    fn add_depth_generic_discharge(&mut self) -> Result<(), SpecError> {
        // rec_env_closed_of_b2: checker-true -> RecEnvClosed.
        self.add_definition(Self::eccd_lemma(
            "rec_env_closed_of_b2",
            "forall (env : RecEnv), \
             Eq Bool (rec_env_closed_b2 env) Bool.true -> RecEnvClosed env",
            "fun (env : RecEnv) (hb : Eq Bool (rec_env_closed_b2 env) Bool.true) => \
             RecEnvClosed.mk env \
             (fun (rname : Name) (cname : Name) (rule : RecRule) (val : KExpr) (depth : Nat) \
             (hlk : Eq (OptionType RecRule) (recrule_for env rname cname) (OptionType.some RecRule rule)) => \
             opt_bind_some_inv RecRules RecRule (recrules_for env rname) \
             (fun (rules : RecRules) => recrule_in_rules rules cname) rule \
             (Eq KExpr (instantiate_at (recrule_rhs rule) val depth) (recrule_rhs rule)) hlk \
             (fun (rules : RecRules) \
             (hrules : Eq (OptionType RecRules) (recrules_for env rname) (OptionType.some RecRules rules)) \
             (hin : Eq (OptionType RecRule) (recrule_in_rules rules cname) (OptionType.some RecRule rule)) => \
             inst_closed_at_id (recrule_rhs rule) Nat.zero \
             (closed_at_b_sound (recrule_rhs rule) Nat.zero \
             (rec_rules_closed_b2_sound rules cname rule hin \
             (rec_env_closed_b2_sound env rname rules hrules hb))) \
             val depth (le_zero_n depth)))",
            "GENERIC depth-aware checker soundness (inst): rec_env_closed_b2 env = true -> \
             RecEnvClosed env, for ANY env. Decompose the recrule_for lookup (opt_bind_some_inv), \
             chain the two fold-membership lemmas to the rule's closed_b fact, convert to \
             is_closed_at _ 0 (closed_at_b_sound), close with the invariance bridge \
             inst_closed_at_id at the interface's arbitrary depth (le_zero_n). A concrete env — \
             including the reflected real kernel_core_red_env — now discharges RecEnvClosed by a \
             single Eq.refl Bool Bool.true. DerivedProved, zero axiom_deps. Front #1 Stage 3/4 \
             prerequisite (generic discharge).",
            &[
                "RecEnvClosed",
                "RecEnvClosed.mk",
                "rec_env_closed_b2",
                "rec_env_closed_b2_sound",
                "rec_rules_closed_b2_sound",
                "closed_at_b_sound",
                "inst_closed_at_id",
                "le_zero_n",
                "opt_bind_some_inv",
                "recrule_for",
                "recrules_for",
                "recrule_in_rules",
                "recrule_rhs",
                "instantiate_at",
            ],
        ))?;

        // rec_env_lift_closed_of_b2: checker-true -> RecEnvLiftClosed.
        self.add_definition(Self::eccd_lemma(
            "rec_env_lift_closed_of_b2",
            "forall (env : RecEnv), \
             Eq Bool (rec_env_lift_closed_b2 env) Bool.true -> RecEnvLiftClosed env",
            "fun (env : RecEnv) (hb : Eq Bool (rec_env_lift_closed_b2 env) Bool.true) => \
             RecEnvLiftClosed.mk env \
             (fun (rname : Name) (cname : Name) (rule : RecRule) (cutoff : Nat) (amount : Nat) \
             (hlk : Eq (OptionType RecRule) (recrule_for env rname cname) (OptionType.some RecRule rule)) => \
             opt_bind_some_inv RecRules RecRule (recrules_for env rname) \
             (fun (rules : RecRules) => recrule_in_rules rules cname) rule \
             (Eq KExpr (lift_at (recrule_rhs rule) cutoff amount) (recrule_rhs rule)) hlk \
             (fun (rules : RecRules) \
             (hrules : Eq (OptionType RecRules) (recrules_for env rname) (OptionType.some RecRules rules)) \
             (hin : Eq (OptionType RecRule) (recrule_in_rules rules cname) (OptionType.some RecRule rule)) => \
             lift_closed_at_id (recrule_rhs rule) Nat.zero \
             (closed_at_b_sound (recrule_rhs rule) Nat.zero \
             (rec_rules_closed_b2_sound rules cname rule hin \
             (rec_env_closed_b2_sound env rname rules hrules hb))) \
             cutoff amount (le_zero_n cutoff)))",
            "GENERIC depth-aware checker soundness (lift): rec_env_lift_closed_b2 env = true -> \
             RecEnvLiftClosed env, for ANY env. Same fold-membership chain as \
             rec_env_closed_of_b2 (the lift checker is the closedness alias); the interface \
             field closes with the lift invariance bridge lift_closed_at_id instead. \
             DerivedProved, zero axiom_deps. Front #1 Stage 3/4 prerequisite (generic discharge).",
            &[
                "RecEnvLiftClosed",
                "RecEnvLiftClosed.mk",
                "rec_env_lift_closed_b2",
                "rec_env_closed_b2_sound",
                "rec_rules_closed_b2_sound",
                "closed_at_b_sound",
                "lift_closed_at_id",
                "le_zero_n",
                "opt_bind_some_inv",
                "recrule_for",
                "recrules_for",
                "recrule_in_rules",
                "recrule_rhs",
                "lift_at",
            ],
        ))?;

        // def_env_closed_of_b2: checker-true -> DefEnvClosed.
        self.add_definition(Self::eccd_lemma(
            "def_env_closed_of_b2",
            "forall (env : DefEnv), \
             Eq Bool (def_env_closed_b2 env) Bool.true -> DefEnvClosed env",
            "fun (env : DefEnv) (hb : Eq Bool (def_env_closed_b2 env) Bool.true) => \
             DefEnvClosed.mk env \
             (fun (dname : Name) (defval : KExpr) (subval : KExpr) (depth : Nat) \
             (hlk : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr defval)) => \
             inst_closed_at_id defval Nat.zero \
             (closed_at_b_sound defval Nat.zero \
             (def_env_closed_b2_sound env dname defval hlk hb)) \
             subval depth (le_zero_n depth))",
            "GENERIC depth-aware checker soundness (inst): def_env_closed_b2 env = true -> \
             DefEnvClosed env, for ANY env. The def-env fold-membership lemma pins the looked-up \
             value's closed_b fact; closed_at_b_sound converts to is_closed_at _ 0; \
             inst_closed_at_id closes at the interface's arbitrary depth (le_zero_n). \
             DerivedProved, zero axiom_deps. Front #1 Stage 3/4 prerequisite (generic discharge).",
            &[
                "DefEnvClosed",
                "DefEnvClosed.mk",
                "def_env_closed_b2",
                "def_env_closed_b2_sound",
                "closed_at_b_sound",
                "inst_closed_at_id",
                "le_zero_n",
                "defval_for",
                "instantiate_at",
            ],
        ))?;

        // def_env_lift_closed_of_b2: checker-true -> DefEnvLiftClosed.
        self.add_definition(Self::eccd_lemma(
            "def_env_lift_closed_of_b2",
            "forall (env : DefEnv), \
             Eq Bool (def_env_lift_closed_b2 env) Bool.true -> DefEnvLiftClosed env",
            "fun (env : DefEnv) (hb : Eq Bool (def_env_lift_closed_b2 env) Bool.true) => \
             DefEnvLiftClosed.mk env \
             (fun (dname : Name) (defval : KExpr) (cutoff : Nat) (amount : Nat) \
             (hlk : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr defval)) => \
             lift_closed_at_id defval Nat.zero \
             (closed_at_b_sound defval Nat.zero \
             (def_env_closed_b2_sound env dname defval hlk hb)) \
             cutoff amount (le_zero_n cutoff))",
            "GENERIC depth-aware checker soundness (lift): def_env_lift_closed_b2 env = true -> \
             DefEnvLiftClosed env, for ANY env. Same membership chain as def_env_closed_of_b2 \
             (the lift checker is the closedness alias); closes with lift_closed_at_id. \
             DerivedProved, zero axiom_deps. Front #1 Stage 3/4 prerequisite (generic discharge).",
            &[
                "DefEnvLiftClosed",
                "DefEnvLiftClosed.mk",
                "def_env_lift_closed_b2",
                "def_env_closed_b2_sound",
                "closed_at_b_sound",
                "lift_closed_at_id",
                "le_zero_n",
                "defval_for",
                "lift_at",
            ],
        ))?;

        Ok(())
    }

    /// Regression demo (toy scale, subset-bundle-safe): all four closure
    /// interfaces over `faithful_red_env` (closed-LAMBDA rule rhs / def value
    /// — the shape the Stage-1 ceiling-0 checker also certified) by the
    /// single-rfl b2 route. The real-env payoff lives in
    /// `add_kernel_core_red_env_closed_witnesses` (full bundle only). Nothing
    /// carried is discharged — no masquerade.
    fn add_depth_checker_demo(&mut self) -> Result<(), SpecError> {
        let demos: [(&str, String, &str); 4] = [
            (
                "faithful_red_env_rec_closed_via_checker_b2",
                "RecEnvClosed (red_rec faithful_red_env)".to_string(),
                "rec_env_closed_of_b2 (red_rec faithful_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "faithful_red_env_rec_lift_closed_via_checker_b2",
                "RecEnvLiftClosed (red_rec faithful_red_env)".to_string(),
                "rec_env_lift_closed_of_b2 (red_rec faithful_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "faithful_red_env_def_closed_via_checker_b2",
                "DefEnvClosed (red_def faithful_red_env)".to_string(),
                "def_env_closed_of_b2 (red_def faithful_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "faithful_red_env_def_lift_closed_via_checker_b2",
                "DefEnvLiftClosed (red_def faithful_red_env)".to_string(),
                "def_env_lift_closed_of_b2 (red_def faithful_red_env) (Eq.refl Bool Bool.true)",
            ),
        ];

        for (name, type_src, value_src) in demos {
            let of_b2 = value_src
                .split_whitespace()
                .next()
                .expect("demo value_src starts with the generic lemma name");
            self.add_definition(Self::eccd_lemma(
                name,
                &type_src,
                value_src,
                &format!(
                    "Regression demo (Front #1 Stage 3/4 prerequisite): {type_src} discharged \
                     over faithful_red_env (closed-lambda rule rhs / def value) by the \
                     SINGLE-RFL depth-aware checker route — {of_b2} + Eq.refl Bool Bool.true; \
                     the kernel whnf-evaluates the closed_at_b fold over the concrete env. Demo \
                     only: the carried RedEnvFaithful hypotheses are untouched (no masquerade). \
                     DerivedProved, zero axiom_deps."
                ),
                &[of_b2, "faithful_red_env", "Eq.refl"],
            ))?;
        }

        Ok(())
    }

    /// THE PAYOFF (the Stage-4 feasibility gate): all four closure interfaces
    /// discharged over the MECHANICALLY REFLECTED REAL ENV
    /// `kernel_core_red_env` by the single-rfl depth-aware route. Registering
    /// each witness forces the kernel to whnf-EVALUATE `closed_at_b` over
    /// every real rule rhs (field-binding lambdas) and def value down to
    /// `Bool.true` — the certification the Stage-1 ceiling-0 checkers could
    /// not deliver (Stage 2 measured 0/86 rule RHSs bvar-free). FULL bundle
    /// only (kernel_core_red_env is not in the subset bundles). Nothing
    /// carried is discharged (the swap is Stage 4 proper) — no masquerade.
    pub(super) fn add_kernel_core_red_env_closed_witnesses(&mut self) -> Result<(), SpecError> {
        let witnesses: [(&str, String, &str); 4] = [
            (
                "kernel_core_red_env_rec_closed_via_checker_b2",
                "RecEnvClosed (red_rec kernel_core_red_env)".to_string(),
                "rec_env_closed_of_b2 (red_rec kernel_core_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "kernel_core_red_env_rec_lift_closed_via_checker_b2",
                "RecEnvLiftClosed (red_rec kernel_core_red_env)".to_string(),
                "rec_env_lift_closed_of_b2 (red_rec kernel_core_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "kernel_core_red_env_def_closed_via_checker_b2",
                "DefEnvClosed (red_def kernel_core_red_env)".to_string(),
                "def_env_closed_of_b2 (red_def kernel_core_red_env) (Eq.refl Bool Bool.true)",
            ),
            (
                "kernel_core_red_env_def_lift_closed_via_checker_b2",
                "DefEnvLiftClosed (red_def kernel_core_red_env)".to_string(),
                "def_env_lift_closed_of_b2 (red_def kernel_core_red_env) (Eq.refl Bool Bool.true)",
            ),
        ];

        for (name, type_src, value_src) in witnesses {
            let of_b2 = value_src
                .split_whitespace()
                .next()
                .expect("witness value_src starts with the generic lemma name");
            self.add_definition(Self::eccd_lemma(
                name,
                &type_src,
                value_src,
                &format!(
                    "THE PAYOFF (Front #1 Stage-4 feasibility gate): {type_src} discharged over \
                     the MECHANICALLY REFLECTED REAL kernel foundation-core env by the \
                     SINGLE-RFL depth-aware checker route — {of_b2} + Eq.refl Bool Bool.true. \
                     The kernel whnf-evaluates closed_at_b over every REAL rule rhs \
                     (field-binding lambdas) and def value down to Bool.true — the certification \
                     the Stage-1 ceiling-0 checkers measurably could not deliver (0/86 real rule \
                     RHSs are bvar-free). Witness only: the carried hypotheses are untouched \
                     (the swap is Stage 4 proper; no masquerade). DerivedProved, zero axiom_deps."
                ),
                &[of_b2, "kernel_core_red_env", "Eq.refl"],
            ))?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::build_spec_with_stack;

    /// All eight depth-aware checkers register as value-ful, non-axiom
    /// recursive defs with no axiom blockers.
    #[test]
    fn test_depth_checkers_are_valueful_defs() {
        let spec = build_spec_with_stack();
        for name in [
            "nat_lt_b",
            "closed_at_b",
            "closed_b",
            "rec_rules_closed_b2",
            "rec_env_closed_b2",
            "rec_env_lift_closed_b2",
            "def_env_closed_b2",
            "def_env_lift_closed_b2",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(def.value_src.is_some(), "{name} should have a value");
            assert!(!def.is_axiom, "{name} must not be an axiom");
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must have no axiom blockers: {:?}",
                def.axiom_deps
            );
        }
    }

    /// The soundness + invariance-bridge + fold-membership + generic-discharge
    /// lemmas are real DerivedProved terms (zero axiom_deps) and re-typecheck
    /// against the live kernel env.
    #[test]
    fn test_depth_soundness_lemmas_are_derived_proved_zero_axioms() {
        let spec = build_spec_with_stack();
        for name in [
            "bool_false_ne_true_t",
            "nat_lt_b_sound",
            "closed_at_b_sound",
            "inst_closed_at_id",
            "lift_closed_at_id",
            "rec_rules_closed_b2_sound",
            "rec_env_closed_b2_sound",
            "def_env_closed_b2_sound",
            "rec_env_closed_of_b2",
            "rec_env_lift_closed_of_b2",
            "def_env_closed_of_b2",
            "def_env_lift_closed_of_b2",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(!def.is_axiom, "{name} must not be an axiom (no masquerade)");
            assert_eq!(
                def.category,
                AxiomCategory::DerivedLemma,
                "{name} should be a DerivedLemma"
            );
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must carry zero axiom_deps: {:?}",
                def.axiom_deps
            );
            assert!(
                def.value_src.is_some(),
                "{name} must carry a constructive proof term"
            );
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} should elaborate and type-check: {e:?}"));
        }
    }

    /// The toy-env regression demo: faithful_red_env (closed-lambda rhs)
    /// discharges the full closure-interface bundle by the single-rfl
    /// depth-aware route.
    #[test]
    fn test_faithful_env_discharges_by_single_rfl_b2() {
        let spec = build_spec_with_stack();
        for name in [
            "faithful_red_env_rec_closed_via_checker_b2",
            "faithful_red_env_rec_lift_closed_via_checker_b2",
            "faithful_red_env_def_closed_via_checker_b2",
            "faithful_red_env_def_lift_closed_via_checker_b2",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(!def.is_axiom, "{name} must not be an axiom (no masquerade)");
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must carry zero axiom_deps: {:?}",
                def.axiom_deps
            );
            let value = def
                .value_src
                .as_deref()
                .unwrap_or_else(|| panic!("{name} must carry a proof term"));
            assert!(
                value.contains("(Eq.refl Bool Bool.true)"),
                "{name} must be the single-rfl checker route, got: {value}"
            );
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} (single-rfl witness) must kernel-check: {e:?}"));
        }
    }

    /// THE PAYOFF GATE (Stage-4 feasibility): the reflected REAL env
    /// kernel_core_red_env discharges all four closure interfaces by the
    /// single-rfl depth-aware route. The registration already kernel-checked
    /// each Eq.refl (closed_at_b whnf-evaluated to true over every real rule
    /// rhs and def value); this re-verifies every witness and pins its status.
    #[test]
    fn test_kernel_core_red_env_discharges_by_single_rfl_b2() {
        let spec = build_spec_with_stack();
        for name in [
            "kernel_core_red_env_rec_closed_via_checker_b2",
            "kernel_core_red_env_rec_lift_closed_via_checker_b2",
            "kernel_core_red_env_def_closed_via_checker_b2",
            "kernel_core_red_env_def_lift_closed_via_checker_b2",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(!def.is_axiom, "{name} must not be an axiom (no masquerade)");
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must carry zero axiom_deps: {:?}",
                def.axiom_deps
            );
            let value = def
                .value_src
                .as_deref()
                .unwrap_or_else(|| panic!("{name} must carry a proof term"));
            assert!(
                value.contains("(Eq.refl Bool Bool.true)"),
                "{name} must be the single-rfl checker route, got: {value}"
            );
            spec.verify_definition(name).unwrap_or_else(|e| {
                panic!("{name} (real-env single-rfl witness) must kernel-check: {e:?}")
            });
        }
    }
}
