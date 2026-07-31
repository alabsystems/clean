// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Substitution and DefEq bridge lemmas (PART 11b)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The GENUINE, non-circular proof term for `beta_subst_commutes_at`.
///
/// Closes the #2872 same-bundle cycle for real: instead of transporting the
/// unsubstituted `DefEq.beta` redex back through `def_eq_respects_subst_at`
/// (the old circular masquerade), it reduces the binder-depth beta redex
/// ARITHMETICALLY and discharges the residual raw-term equality with the
/// already-`DerivedProved`, zero-axiom de Bruijn substitution lemma
/// `instantiate_nested_commutes_zero_subst`.
///
/// Shape: `def_eq_eq_right L N R (def_eq_eq_left L M N eqLM (DefEq.beta A' b' arg')) eqNR`
/// where
///   `L = instantiate_at (app (lam A body) arg) val depth`,
///   `M = app (lam A' b') arg'`     (the structurally unfolded redex),
///   `N = instantiate b' arg'`      (the beta contractum),
///   `R = instantiate_at (instantiate body arg) val depth`,
///   `A' = instantiate_at A val depth`, `b' = instantiate_at body val (succ depth)`,
///   `arg' = instantiate_at arg val depth`,
///   `eqLM : Eq L M` via `instantiate_at_app` + `instantiate_at_lam` (Eq.cong),
///   `eqNR : Eq N R` via `Eq.symm` of `instantiate_nested_commutes_zero_subst`.
///
/// Referenced by both the spec definition (here) and the kernel `ProofLibrary`
/// registry (`crate::proofs::library_subst_micro_env`) so the two never diverge.
pub(crate) const BETA_SUBST_COMMUTES_AT_PROOF: &str = concat!(
    "fun (A : KExpr) (body : KExpr) (arg : KExpr) (val : KExpr) (depth : Nat) ",
    "(wd : DefEnvWellformed the_red_env) ",
    "(wr : RecEnvWellformed (red_rec the_red_env)) => ",
    "def_eq_eq_right ",
    "(instantiate_at (KExpr.app (KExpr.lam A body) arg) val depth) ",
    "(instantiate (instantiate_at body val (Nat.succ depth)) (instantiate_at arg val depth)) ",
    "(instantiate_at (instantiate body arg) val depth) ",
    "(def_eq_eq_left ",
    "(instantiate_at (KExpr.app (KExpr.lam A body) arg) val depth) ",
    "(KExpr.app (KExpr.lam (instantiate_at A val depth) (instantiate_at body val (Nat.succ depth))) ",
    "(instantiate_at arg val depth)) ",
    "(instantiate (instantiate_at body val (Nat.succ depth)) (instantiate_at arg val depth)) ",
    "(Eq.trans KExpr ",
    "(instantiate_at (KExpr.app (KExpr.lam A body) arg) val depth) ",
    "(KExpr.app (instantiate_at (KExpr.lam A body) val depth) (instantiate_at arg val depth)) ",
    "(KExpr.app (KExpr.lam (instantiate_at A val depth) (instantiate_at body val (Nat.succ depth))) ",
    "(instantiate_at arg val depth)) ",
    "(instantiate_at_app (KExpr.lam A body) arg val depth) ",
    "(Eq.cong KExpr KExpr ",
    "(fun (x : KExpr) => KExpr.app x (instantiate_at arg val depth)) ",
    "(instantiate_at (KExpr.lam A body) val depth) ",
    "(KExpr.lam (instantiate_at A val depth) (instantiate_at body val (Nat.succ depth))) ",
    "(instantiate_at_lam A body val depth))) ",
    "(DefEq.beta (instantiate_at A val depth) (instantiate_at body val (Nat.succ depth)) ",
    "(instantiate_at arg val depth))) ",
    "(Eq.symm KExpr ",
    "(instantiate_at (instantiate body arg) val depth) ",
    "(instantiate_at (instantiate_at body val (Nat.succ depth)) (instantiate_at arg val depth) Nat.zero) ",
    "(instantiate_nested_commutes_zero_subst body arg val depth))"
);

impl Specification {
    pub(super) fn add_substitution_def_eq_lemmas(&mut self) -> Result<(), SpecError> {
        // Congruence bridge: instantiate_at preserves application DefEq once both
        // instantiated subterms are already related.
        // Now DerivedProved: instantiate_at_app is DerivedProved; DefEq.app_cong,
        // Eq.subst, Eq.symm are FoundationalRules. Part of #464, #461.
        self.add_definition(SpecDefinition {
            name: "instantiate_at_app_preserves_def_eq".to_string(),
            type_src: "forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (val : KExpr) (depth : Nat), DefEq (instantiate_at f val depth) (instantiate_at f' val depth) -> DefEq (instantiate_at a val depth) (instantiate_at a' val depth) -> DefEq (instantiate_at (KExpr.app f a) val depth) (instantiate_at (KExpr.app f' a') val depth)".to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(val : KExpr) (depth : Nat) ",
                    "(hf : DefEq (instantiate_at f val depth) (instantiate_at f' val depth)) ",
                    "(ha : DefEq (instantiate_at a val depth) (instantiate_at a' val depth)) => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.app f a) val depth) ",
                    "(KExpr.app (instantiate_at f' val depth) (instantiate_at a' val depth)) ",
                    "(instantiate_at (KExpr.app f' a') val depth) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.app f a) val depth) ",
                    "(KExpr.app (instantiate_at f val depth) (instantiate_at a val depth)) ",
                    "(KExpr.app (instantiate_at f' val depth) (instantiate_at a' val depth)) ",
                    "(instantiate_at_app f a val depth) ",
                    "(DefEq.app_cong ",
                    "(instantiate_at f val depth) ",
                    "(instantiate_at f' val depth) ",
                    "(instantiate_at a val depth) ",
                    "(instantiate_at a' val depth) ",
                    "hf ha)) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.app f' a') val depth) ",
                    "(KExpr.app (instantiate_at f' val depth) (instantiate_at a' val depth)) ",
                    "(instantiate_at_app f' a' val depth))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "instantiate_at preserves application DefEq. DerivedProved. Part of #464, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq.app_cong".to_string(),
                "Eq.symm".to_string(),
                "def_eq_eq_left".to_string(),
                "def_eq_eq_right".to_string(),
                "instantiate_at_app".to_string(),
            ])),
            // instantiate_at_app is now DerivedLemma; rest are FoundationalRules.
            axiom_deps: HashSet::new(),
        })?;

        // Congruence bridge: instantiate_at preserves lambda DefEq once the domain
        // matches at the current depth and the body matches under one extra binder.
        // Now DerivedProved: instantiate_at_lam is DerivedProved. Part of #464, #461.
        self.add_definition(SpecDefinition {
            name: "instantiate_at_lam_preserves_def_eq".to_string(),
            type_src: "forall (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (val : KExpr) (depth : Nat), DefEq (instantiate_at A val depth) (instantiate_at A' val depth) -> DefEq (instantiate_at b val (Nat.succ depth)) (instantiate_at b' val (Nat.succ depth)) -> DefEq (instantiate_at (KExpr.lam A b) val depth) (instantiate_at (KExpr.lam A' b') val depth)".to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) ",
                    "(val : KExpr) (depth : Nat) ",
                    "(hA : DefEq (instantiate_at A val depth) (instantiate_at A' val depth)) ",
                    "(hb : DefEq (instantiate_at b val (Nat.succ depth)) (instantiate_at b' val (Nat.succ depth))) => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.lam A b) val depth) ",
                    "(KExpr.lam (instantiate_at A' val depth) (instantiate_at b' val (Nat.succ depth))) ",
                    "(instantiate_at (KExpr.lam A' b') val depth) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.lam A b) val depth) ",
                    "(KExpr.lam (instantiate_at A val depth) (instantiate_at b val (Nat.succ depth))) ",
                    "(KExpr.lam (instantiate_at A' val depth) (instantiate_at b' val (Nat.succ depth))) ",
                    "(instantiate_at_lam A b val depth) ",
                    "(DefEq.lam_cong ",
                    "(instantiate_at A val depth) ",
                    "(instantiate_at A' val depth) ",
                    "(instantiate_at b val (Nat.succ depth)) ",
                    "(instantiate_at b' val (Nat.succ depth)) ",
                    "hA hb)) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.lam A' b') val depth) ",
                    "(KExpr.lam (instantiate_at A' val depth) (instantiate_at b' val (Nat.succ depth))) ",
                    "(instantiate_at_lam A' b' val depth))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "instantiate_at preserves lambda DefEq. DerivedProved. Part of #464, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq.lam_cong".to_string(),
                "Eq.symm".to_string(),
                "def_eq_eq_left".to_string(),
                "def_eq_eq_right".to_string(),
                "instantiate_at_lam".to_string(),
            ])),
            // instantiate_at_lam is now DerivedLemma; rest are FoundationalRules.
            axiom_deps: HashSet::new(),
        })?;

        // Congruence bridge: instantiate_at preserves pi DefEq with the same
        // binder-depth split as the lambda case.
        // Now DerivedProved: instantiate_at_pi is DerivedProved. Part of #464, #461.
        self.add_definition(SpecDefinition {
            name: "instantiate_at_pi_preserves_def_eq".to_string(),
            type_src: "forall (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) (val : KExpr) (depth : Nat), DefEq (instantiate_at A val depth) (instantiate_at A' val depth) -> DefEq (instantiate_at B val (Nat.succ depth)) (instantiate_at B' val (Nat.succ depth)) -> DefEq (instantiate_at (KExpr.pi A B) val depth) (instantiate_at (KExpr.pi A' B') val depth)".to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) ",
                    "(val : KExpr) (depth : Nat) ",
                    "(hA : DefEq (instantiate_at A val depth) (instantiate_at A' val depth)) ",
                    "(hB : DefEq (instantiate_at B val (Nat.succ depth)) (instantiate_at B' val (Nat.succ depth))) => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.pi A B) val depth) ",
                    "(KExpr.pi (instantiate_at A' val depth) (instantiate_at B' val (Nat.succ depth))) ",
                    "(instantiate_at (KExpr.pi A' B') val depth) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.pi A B) val depth) ",
                    "(KExpr.pi (instantiate_at A val depth) (instantiate_at B val (Nat.succ depth))) ",
                    "(KExpr.pi (instantiate_at A' val depth) (instantiate_at B' val (Nat.succ depth))) ",
                    "(instantiate_at_pi A B val depth) ",
                    "(DefEq.pi_cong ",
                    "(instantiate_at A val depth) ",
                    "(instantiate_at A' val depth) ",
                    "(instantiate_at B val (Nat.succ depth)) ",
                    "(instantiate_at B' val (Nat.succ depth)) ",
                    "hA hB)) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.pi A' B') val depth) ",
                    "(KExpr.pi (instantiate_at A' val depth) (instantiate_at B' val (Nat.succ depth))) ",
                    "(instantiate_at_pi A' B' val depth))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "instantiate_at preserves pi DefEq. DerivedProved. Part of #464, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq.pi_cong".to_string(),
                "Eq.symm".to_string(),
                "def_eq_eq_left".to_string(),
                "def_eq_eq_right".to_string(),
                "instantiate_at_pi".to_string(),
            ])),
            // instantiate_at_pi is now DerivedLemma; rest are FoundationalRules.
            axiom_deps: HashSet::new(),
        })?;

        // Binder-depth beta case needed by the generalized substitution proof.
        //
        // GENUINE, NON-CIRCULAR proof (the #2872 cycle is GONE). Registered
        // BEFORE def_eq_respects_subst_at so the DefEq.rec beta case can refer
        // to a name that is ALREADY genuinely proved — there is no forward
        // declaration, no splice, and no dependency on def_eq_respects_subst_at.
        //
        // The proof reduces the binder-depth beta redex arithmetically:
        //   1. instantiate_at structurally distributes over the redex
        //      (instantiate_at_app then instantiate_at_lam, lifted into the
        //      application's function position by Eq.cong) — giving the
        //      *unfolded* redex  app (lam A' b') arg'  with
        //      A'=inst_at A val d, b'=inst_at body val (succ d), arg'=inst_at arg val d.
        //   2. DefEq.beta contracts that unfolded redex to  instantiate b' arg'.
        //   3. instantiate_nested_commutes_zero_subst — the de Bruijn
        //      substitution lemma, itself DerivedProved by KExpr.rec with ZERO
        //      axiom_deps — rewrites  instantiate_at (instantiate body arg) val d
        //      to  instantiate b' arg'  (= instantiate_at b' arg' 0).
        // def_eq_eq_left / def_eq_eq_right transport the DefEq across the two
        // raw-term equalities. No route passes through def_eq_respects_subst_at,
        // so beta_subst_commutes_at is a genuine value-bearing constant (kernel
        // Opaque, NOT a value-less Axiom) and is_def_eq DEBT is empty.
        // The wellformedness premises (wd, wr) are accepted for type-compatibility
        // with the DefEq.rec beta case but are not needed by this arithmetic proof.
        // Part of #464, #2872.
        self.add_definition(SpecDefinition {
            name: "beta_subst_commutes_at".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (body : KExpr) (arg : KExpr) (val : KExpr) (depth : Nat), ",
                "DefEnvWellformed the_red_env -> ",
                "RecEnvWellformed (red_rec the_red_env) -> ",
                "DefEq (instantiate_at (KExpr.app (KExpr.lam A body) arg) val depth) ",
                "(instantiate_at (instantiate body arg) val depth)"
            )
            .to_string(),
            value_src: Some(BETA_SUBST_COMMUTES_AT_PROOF.to_string()),
            is_axiom: false,
            description: concat!(
                "Binder-depth beta substitution commute: instantiate_at preserves ",
                "beta redexes at arbitrary depth. DerivedProved via a genuine, ",
                "non-circular arithmetic proof: instantiate_at_app/lam unfold the ",
                "redex, DefEq.beta contracts it, and the DerivedProved de Bruijn ",
                "substitution lemma instantiate_nested_commutes_zero_subst closes ",
                "the residual raw-term equality. No route through ",
                "def_eq_respects_subst_at (the #2872 same-bundle cycle is removed). ",
                "Part of #464, #2872."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq.beta".to_string(),
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "def_eq_eq_left".to_string(),
                "def_eq_eq_right".to_string(),
                "instantiate_at_app".to_string(),
                "instantiate_at_lam".to_string(),
                "instantiate_nested_commutes_zero_subst".to_string(),
            ])),
            // All dependencies are FoundationalRules or DerivedProved lemmas with
            // empty debt; the de Bruijn substitution lemma carries the induction.
            axiom_deps: HashSet::new(),
        })?;

        // delta/iota_subst_preserves_def_eq_at are now registered in
        // reduction_witnesses.rs as DerivedProved (Part of #725).

        // Binder-depth-aware substitution compatibility for DefEq. The proof
        // isolates delta/iota cases to the (now DerivedProved) reduction-witness
        // transport lemmas. All axiom_deps resolved by #725.
        self.add_definition(SpecDefinition {
            name: "def_eq_respects_subst_at".to_string(),
            type_src: "forall (A : KExpr) (B : KExpr) (val : KExpr) (depth : Nat), DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> DefEq A B -> DefEq (instantiate_at A val depth) (instantiate_at B val depth)".to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (B : KExpr) (val : KExpr) (depth : Nat) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (h : DefEq A B) => ",
                    "DefEq.rec ",
                    "(fun (a : KExpr) (b : KExpr) (_h : DefEq a b) => ",
                    "forall (w : KExpr) (d : Nat), DefEq (instantiate_at a w d) (instantiate_at b w d)) ",
                    "(fun (a : KExpr) (w : KExpr) (d : Nat) => DefEq.refl (instantiate_at a w d)) ",
                    "(fun (a : KExpr) (b : KExpr) (_h : DefEq a b) ",
                    "(ih : forall (w : KExpr) (d : Nat), DefEq (instantiate_at a w d) (instantiate_at b w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "DefEq.symm (instantiate_at a w d) (instantiate_at b w d) (ih w d)) ",
                    "(fun (a : KExpr) (b : KExpr) (c : KExpr) (_hab : DefEq a b) (_hbc : DefEq b c) ",
                    "(ih_ab : forall (w : KExpr) (d : Nat), DefEq (instantiate_at a w d) (instantiate_at b w d)) ",
                    "(ih_bc : forall (w : KExpr) (d : Nat), DefEq (instantiate_at b w d) (instantiate_at c w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "DefEq.trans (instantiate_at a w d) (instantiate_at b w d) (instantiate_at c w d) (ih_ab w d) (ih_bc w d)) ",
                    "(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) ",
                    "(w : KExpr) (d : Nat) => ",
                    "beta_subst_commutes_at A0 body arg w d wd wr) ",
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(_hf : DefEq f f') (_ha : DefEq a a') ",
                    "(ih_f : forall (w : KExpr) (d : Nat), DefEq (instantiate_at f w d) (instantiate_at f' w d)) ",
                    "(ih_a : forall (w : KExpr) (d : Nat), DefEq (instantiate_at a w d) (instantiate_at a' w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "instantiate_at_app_preserves_def_eq f f' a a' w d (ih_f w d) (ih_a w d)) ",
                    "(fun (A0 : KExpr) (A0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
                    "(_hA : DefEq A0 A0') (_hb : DefEq b0 b0') ",
                    "(ih_A : forall (w : KExpr) (d : Nat), DefEq (instantiate_at A0 w d) (instantiate_at A0' w d)) ",
                    "(ih_b : forall (w : KExpr) (d : Nat), DefEq (instantiate_at b0 w d) (instantiate_at b0' w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "instantiate_at_lam_preserves_def_eq A0 A0' b0 b0' w d (ih_A w d) (ih_b w (Nat.succ d))) ",
                    "(fun (A0 : KExpr) (A0' : KExpr) (B0 : KExpr) (B0' : KExpr) ",
                    "(_hA : DefEq A0 A0') (_hB : DefEq B0 B0') ",
                    "(ih_A : forall (w : KExpr) (d : Nat), DefEq (instantiate_at A0 w d) (instantiate_at A0' w d)) ",
                    "(ih_B : forall (w : KExpr) (d : Nat), DefEq (instantiate_at B0 w d) (instantiate_at B0' w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "instantiate_at_pi_preserves_def_eq A0 A0' B0 B0' w d (ih_A w d) (ih_B w (Nat.succ d))) ",
                    "(fun (e : KExpr) (e' : KExpr) (hd : delta_reduces e e') (w : KExpr) (d : Nat) => ",
                    "delta_subst_preserves_def_eq_at e e' w d wd hd) ",
                    "(fun (e : KExpr) (e' : KExpr) (hi : iota_reduces e e') (w : KExpr) (d : Nat) => ",
                    "iota_subst_preserves_def_eq_at e e' w d wr hi) ",
                    // zeta: inline mirror of the beta minor (BETA_SUBST_COMMUTES_AT_PROOF)
                    // over KExpr.let_. instantiate_at_let_ unfolds the redex, DefEq.zeta
                    // contracts it, instantiate_nested_commutes_zero_subst (SAME lemma the
                    // beta case uses, body:=b, arg:=v) closes the residual raw-term equality.
                    "(fun (ty : KExpr) (v : KExpr) (b : KExpr) (w : KExpr) (d : Nat) => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.let_ ty v b) w d) ",
                    "(instantiate (instantiate_at b w (Nat.succ d)) (instantiate_at v w d)) ",
                    "(instantiate_at (instantiate b v) w d) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.let_ ty v b) w d) ",
                    "(KExpr.let_ (instantiate_at ty w d) (instantiate_at v w d) (instantiate_at b w (Nat.succ d))) ",
                    "(instantiate (instantiate_at b w (Nat.succ d)) (instantiate_at v w d)) ",
                    "(instantiate_at_let_ ty v b w d) ",
                    "(DefEq.zeta (instantiate_at ty w d) (instantiate_at v w d) (instantiate_at b w (Nat.succ d)))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (instantiate b v) w d) ",
                    "(instantiate_at (instantiate_at b w (Nat.succ d)) (instantiate_at v w d) Nat.zero) ",
                    "(instantiate_nested_commutes_zero_subst b v w d))) ",
                    // let_cong: inline mirror of the lam_cong minor over KExpr.let_
                    // (ty/val at d, body at succ d) via instantiate_at_let_ + DefEq.let_cong.
                    "(fun (ty : KExpr) (ty' : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) (b' : KExpr) ",
                    "(_hty : DefEq ty ty') (_hv : DefEq v v') (_hb : DefEq b b') ",
                    "(ih_ty : forall (w : KExpr) (d : Nat), DefEq (instantiate_at ty w d) (instantiate_at ty' w d)) ",
                    "(ih_v : forall (w : KExpr) (d : Nat), DefEq (instantiate_at v w d) (instantiate_at v' w d)) ",
                    "(ih_b : forall (w : KExpr) (d : Nat), DefEq (instantiate_at b w d) (instantiate_at b' w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.let_ ty v b) w d) ",
                    "(KExpr.let_ (instantiate_at ty' w d) (instantiate_at v' w d) (instantiate_at b' w (Nat.succ d))) ",
                    "(instantiate_at (KExpr.let_ ty' v' b') w d) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.let_ ty v b) w d) ",
                    "(KExpr.let_ (instantiate_at ty w d) (instantiate_at v w d) (instantiate_at b w (Nat.succ d))) ",
                    "(KExpr.let_ (instantiate_at ty' w d) (instantiate_at v' w d) (instantiate_at b' w (Nat.succ d))) ",
                    "(instantiate_at_let_ ty v b w d) ",
                    "(DefEq.let_cong ",
                    "(instantiate_at ty w d) (instantiate_at ty' w d) ",
                    "(instantiate_at v w d) (instantiate_at v' w d) ",
                    "(instantiate_at b w (Nat.succ d)) (instantiate_at b' w (Nat.succ d)) ",
                    "(ih_ty w d) (ih_v w d) (ih_b w (Nat.succ d)))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.let_ ty' v' b') w d) ",
                    "(KExpr.let_ (instantiate_at ty' w d) (instantiate_at v' w d) (instantiate_at b' w (Nat.succ d))) ",
                    "(instantiate_at_let_ ty' v' b' w d))) ",
                    // proj_cong (proj/lit rung): single-hole mirror of let_cong via instantiate_at_proj.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) (_hsub : DefEq sub sub') ",
                    "(ih_sub : forall (w : KExpr) (d : Nat), DefEq (instantiate_at sub w d) (instantiate_at sub' w d)) ",
                    "(w : KExpr) (d : Nat) => ",
                    "def_eq_eq_right ",
                    "(instantiate_at (KExpr.proj s i sub) w d) ",
                    "(KExpr.proj s i (instantiate_at sub' w d)) ",
                    "(instantiate_at (KExpr.proj s i sub') w d) ",
                    "(def_eq_eq_left ",
                    "(instantiate_at (KExpr.proj s i sub) w d) ",
                    "(KExpr.proj s i (instantiate_at sub w d)) ",
                    "(KExpr.proj s i (instantiate_at sub' w d)) ",
                    "(instantiate_at_proj s i sub w d) ",
                    "(DefEq.proj_cong s i (instantiate_at sub w d) (instantiate_at sub' w d) (ih_sub w d))) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.proj s i sub') w d) ",
                    "(KExpr.proj s i (instantiate_at sub' w d)) ",
                    "(instantiate_at_proj s i sub' w d))) ",
                    "A B h val depth"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "DefEq is preserved by instantiate_at at any binder depth. DerivedProved: the DefEq.rec beta case calls the genuinely-proved beta_subst_commutes_at (no cycle — beta_subst_commutes_at does not route back through this lemma); all other cases are DerivedProved with empty helper closure. Part of #464, #2872.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq.rec".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.zeta".to_string(),
                "DefEq.let_cong".to_string(),
                "beta_subst_commutes_at".to_string(),
                "delta_subst_preserves_def_eq_at".to_string(),
                "instantiate_at_app_preserves_def_eq".to_string(),
                "instantiate_at_lam_preserves_def_eq".to_string(),
                "instantiate_at_pi_preserves_def_eq".to_string(),
                "instantiate_at_let_".to_string(),
                "instantiate_nested_commutes_zero_subst".to_string(),
                "def_eq_eq_left".to_string(),
                "def_eq_eq_right".to_string(),
                "Eq.symm".to_string(),
                "iota_subst_preserves_def_eq_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Definitional equality is preserved under top-level substitution.
        self.add_definition(SpecDefinition {
            name: "def_eq_respects_subst".to_string(),
            type_src: "forall (A : KExpr) (B : KExpr) (v : KExpr), DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> DefEq A B -> DefEq (instantiate A v) (instantiate B v)".to_string(),
            value_src: Some(
                "fun (A : KExpr) (B : KExpr) (v : KExpr) (wd : DefEnvWellformed the_red_env) (wr : RecEnvWellformed (red_rec the_red_env)) (h : DefEq A B) => def_eq_respects_subst_at A B v Nat.zero wd wr h".to_string()
            ),
            is_axiom: false,
            description: "If A ≡ B, then A[v/0] ≡ B[v/0]. DerivedProved via def_eq_respects_subst_at at depth 0 (the #2872 beta_subst_commutes_at cycle is removed — beta_subst_commutes_at is genuinely proved). Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["def_eq_respects_subst_at".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // Beta case: substitution preserves typed beta redexes.
        // Registered after def_eq_respects_subst so the checked proof term can
        // resolve its dependency in the current environment. Part of #661, #2872.
        self.add_definition(SpecDefinition {
            name: "beta_subst_commutes".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (body : KExpr) (arg : KExpr) (w : KExpr), ",
                "DefEnvWellformed the_red_env -> ",
                "RecEnvWellformed (red_rec the_red_env) -> ",
                "DefEq (instantiate (KExpr.app (KExpr.lam A body) arg) w) ",
                "(instantiate (instantiate body arg) w)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (body : KExpr) (arg : KExpr) (w : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) => ",
                    "def_eq_respects_subst ",
                    "(KExpr.app (KExpr.lam A body) arg) ",
                    "(instantiate body arg) ",
                    "w wd wr ",
                    "(DefEq.beta A body arg)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Beta case: substitution preserves typed beta redexes. ",
                "DerivedProved: apply DefEq.beta then def_eq_respects_subst ",
                "(the #2872 beta_subst_commutes_at cycle is removed — every member ",
                "of the chain is genuinely proved). ",
                "Part of #661, #2872."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq.beta".to_string(),
                "def_eq_respects_subst".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
