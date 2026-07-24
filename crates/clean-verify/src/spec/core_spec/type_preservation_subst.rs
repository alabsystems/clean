// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Substitution typing infrastructure for type preservation (PART 12 internals).
//!
//! Extracted from `type_preservation.rs` to stay under the 500-line file limit.
//! Contains:
//! - `substitution_typing_gen`: DerivedProved via Typing.rec (conv case uses Typing.conv)
//! - `substitution_typing`: DerivedProved via depth-0 specialization (inherits from gen)
//! - `def_eq_instantiate_arg_congr`: DerivedProved (delegates to the proved
//!   `def_eq_instantiate_arg_congr_at`, #3221)
//!
//! The conv case of Typing.rec transports typing across the subst-respecting
//! DefEq via the untyped Typing.conv rule directly (Brick 9: rerouted off the
//! FALSE def_eq_to_eq bridge; def_eq_respects_subst_at supplies the DefEq).
//!
//! Part of #464: Phase 4A constructive derivation.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Typing.rec sort case: transport Typing.sort n through instantiate_at_sort.
const SUBST_SORT_CASE: &str = concat!(
    "(fun (n : Level) (d0 : Nat) => ",
    "Eq.substType KExpr ",
    "(fun (x : KExpr) => Typing x (instantiate_at (KExpr.sort (Level.succ n)) a d0)) ",
    "(KExpr.sort n) (instantiate_at (KExpr.sort n) a d0) ",
    "(Eq.symm KExpr (instantiate_at (KExpr.sort n) a d0) (KExpr.sort n) ",
    "(instantiate_at_sort n a d0)) ",
    "(Eq.substType KExpr ",
    "(fun (y : KExpr) => Typing (KExpr.sort n) y) ",
    "(KExpr.sort (Level.succ n)) ",
    "(instantiate_at (KExpr.sort (Level.succ n)) a d0) ",
    "(Eq.symm KExpr (instantiate_at (KExpr.sort (Level.succ n)) a d0) ",
    "(KExpr.sort (Level.succ n)) (instantiate_at_sort (Level.succ n) a d0)) ",
    "(Typing.sort n))) ",
);

/// Typing.rec pi case: Typing.pi with IH at d and d+1, transported via instantiate_at_pi.
/// Part of #2870: result sort now uses imax_nat n m instead of m.
const SUBST_PI_CASE: &str = concat!(
    "(fun (A0 : KExpr) (B0 : KExpr) (n : Level) (m : Level) ",
    "(_hA0 : Typing A0 (KExpr.sort n)) (_hB0 : Typing B0 (KExpr.sort m)) ",
    "(ih_A0 : forall (d2 : Nat), Typing (instantiate_at A0 a d2) ",
    "(instantiate_at (KExpr.sort n) a d2)) ",
    "(ih_B0 : forall (d2 : Nat), Typing (instantiate_at B0 a d2) ",
    "(instantiate_at (KExpr.sort m) a d2)) ",
    "(d0 : Nat) => ",
    "Eq.substType KExpr ",
    "(fun (x : KExpr) => Typing x (instantiate_at (KExpr.sort (Level.imax n m)) a d0)) ",
    "(KExpr.pi (instantiate_at A0 a d0) (instantiate_at B0 a (Nat.succ d0))) ",
    "(instantiate_at (KExpr.pi A0 B0) a d0) ",
    "(Eq.symm KExpr (instantiate_at (KExpr.pi A0 B0) a d0) ",
    "(KExpr.pi (instantiate_at A0 a d0) (instantiate_at B0 a (Nat.succ d0))) ",
    "(instantiate_at_pi A0 B0 a d0)) ",
    "(Eq.substType KExpr ",
    "(fun (y : KExpr) => Typing (KExpr.pi (instantiate_at A0 a d0) ",
    "(instantiate_at B0 a (Nat.succ d0))) y) ",
    "(KExpr.sort (Level.imax n m)) (instantiate_at (KExpr.sort (Level.imax n m)) a d0) ",
    "(Eq.symm KExpr (instantiate_at (KExpr.sort (Level.imax n m)) a d0) (KExpr.sort (Level.imax n m)) ",
    "(instantiate_at_sort (Level.imax n m) a d0)) ",
    "(Typing.pi (instantiate_at A0 a d0) (instantiate_at B0 a (Nat.succ d0)) n m ",
    "(Eq.substType KExpr (fun (y : KExpr) => Typing (instantiate_at A0 a d0) y) ",
    "(instantiate_at (KExpr.sort n) a d0) (KExpr.sort n) ",
    "(instantiate_at_sort n a d0) (ih_A0 d0)) ",
    "(Eq.substType KExpr (fun (y : KExpr) => Typing (instantiate_at B0 a (Nat.succ d0)) y) ",
    "(instantiate_at (KExpr.sort m) a (Nat.succ d0)) (KExpr.sort m) ",
    "(instantiate_at_sort m a (Nat.succ d0)) (ih_B0 (Nat.succ d0)))))) ",
);

/// Typing.rec lam case: Typing.lam with IH at d and d+1, transported via instantiate_at_lam/pi.
/// Part of #2870: binder domain universe generalized from Nat.zero to u0.
const SUBST_LAM_CASE: &str = concat!(
    "(fun (A0 : KExpr) (b0 : KExpr) (B0 : KExpr) (u0 : Level) ",
    "(_hA0 : Typing A0 (KExpr.sort u0)) (_hb0 : Typing b0 B0) ",
    "(ih_A0 : forall (d2 : Nat), Typing (instantiate_at A0 a d2) ",
    "(instantiate_at (KExpr.sort u0) a d2)) ",
    "(ih_b0 : forall (d2 : Nat), Typing (instantiate_at b0 a d2) ",
    "(instantiate_at B0 a d2)) ",
    "(d0 : Nat) => ",
    "Eq.substType KExpr ",
    "(fun (x : KExpr) => Typing x (instantiate_at (KExpr.pi A0 B0) a d0)) ",
    "(KExpr.lam (instantiate_at A0 a d0) (instantiate_at b0 a (Nat.succ d0))) ",
    "(instantiate_at (KExpr.lam A0 b0) a d0) ",
    "(Eq.symm KExpr (instantiate_at (KExpr.lam A0 b0) a d0) ",
    "(KExpr.lam (instantiate_at A0 a d0) (instantiate_at b0 a (Nat.succ d0))) ",
    "(instantiate_at_lam A0 b0 a d0)) ",
    "(Eq.substType KExpr ",
    "(fun (y : KExpr) => Typing (KExpr.lam (instantiate_at A0 a d0) ",
    "(instantiate_at b0 a (Nat.succ d0))) y) ",
    "(KExpr.pi (instantiate_at A0 a d0) (instantiate_at B0 a (Nat.succ d0))) ",
    "(instantiate_at (KExpr.pi A0 B0) a d0) ",
    "(Eq.symm KExpr (instantiate_at (KExpr.pi A0 B0) a d0) ",
    "(KExpr.pi (instantiate_at A0 a d0) (instantiate_at B0 a (Nat.succ d0))) ",
    "(instantiate_at_pi A0 B0 a d0)) ",
    "(Typing.lam (instantiate_at A0 a d0) (instantiate_at b0 a (Nat.succ d0)) ",
    "(instantiate_at B0 a (Nat.succ d0)) u0 ",
    "(Eq.substType KExpr (fun (y : KExpr) => Typing (instantiate_at A0 a d0) y) ",
    "(instantiate_at (KExpr.sort u0) a d0) (KExpr.sort u0) ",
    "(instantiate_at_sort u0 a d0) (ih_A0 d0)) ",
    "(ih_b0 (Nat.succ d0))))) ",
);

/// Typing.rec app case (dependent rule): constructive via Typing.app + nested commutes.
///
/// With the dependent Typing.app rule, the result type is `instantiate B0 a0`.
/// The proof proceeds:
///   1. Transport source via `instantiate_at_app`
///   2. Transport f0 IH type via `instantiate_at_pi`
///   3. Apply `Typing.app` → `Typing (app ...) (instantiate (inst_at B0 a (succ d0)) (inst_at a0 a d0))`
///   4. Transport result type via `Eq.symm (instantiate_nested_commutes_zero_subst B0 a0 a d0)`
///      to match the motive target `inst_at (instantiate B0 a0) a d0`
///
/// Part of #464: eliminates the unprovable `substitution_typing_gen_app_case` axiom.
const SUBST_APP_CASE: &str = concat!(
    "(fun (f0 : KExpr) (a0 : KExpr) (A0 : KExpr) (B0 : KExpr) ",
    "(_hf0 : Typing f0 (KExpr.pi A0 B0)) (_ha0 : Typing a0 A0) ",
    "(ih_f0 : forall (d2 : Nat), Typing (instantiate_at f0 a d2) ",
    "(instantiate_at (KExpr.pi A0 B0) a d2)) ",
    "(ih_a0 : forall (d2 : Nat), Typing (instantiate_at a0 a d2) ",
    "(instantiate_at A0 a d2)) ",
    "(d0 : Nat) => ",
    // Outer transport: source via instantiate_at_app
    "Eq.substType KExpr ",
    "(fun (x : KExpr) => Typing x (instantiate_at (instantiate B0 a0) a d0)) ",
    "(KExpr.app (instantiate_at f0 a d0) (instantiate_at a0 a d0)) ",
    "(instantiate_at (KExpr.app f0 a0) a d0) ",
    "(Eq.symm KExpr (instantiate_at (KExpr.app f0 a0) a d0) ",
    "(KExpr.app (instantiate_at f0 a d0) (instantiate_at a0 a d0)) ",
    "(instantiate_at_app f0 a0 a d0)) ",
    // Inner transport: result type via nested commutes
    "(Eq.substType KExpr ",
    "(fun (y : KExpr) => Typing (KExpr.app (instantiate_at f0 a d0) ",
    "(instantiate_at a0 a d0)) y) ",
    "(instantiate (instantiate_at B0 a (Nat.succ d0)) (instantiate_at a0 a d0)) ",
    "(instantiate_at (instantiate B0 a0) a d0) ",
    "(Eq.symm KExpr ",
    "(instantiate_at (instantiate B0 a0) a d0) ",
    "(instantiate (instantiate_at B0 a (Nat.succ d0)) (instantiate_at a0 a d0)) ",
    "(instantiate_nested_commutes_zero_subst B0 a0 a d0)) ",
    // Apply Typing.app (dependent rule)
    "(Typing.app (instantiate_at f0 a d0) (instantiate_at a0 a d0) ",
    "(instantiate_at A0 a d0) (instantiate_at B0 a (Nat.succ d0)) ",
    // Transport f0 IH via instantiate_at_pi
    "(Eq.substType KExpr ",
    "(fun (y : KExpr) => Typing (instantiate_at f0 a d0) y) ",
    "(instantiate_at (KExpr.pi A0 B0) a d0) ",
    "(KExpr.pi (instantiate_at A0 a d0) (instantiate_at B0 a (Nat.succ d0))) ",
    "(instantiate_at_pi A0 B0 a d0) ",
    "(ih_f0 d0)) ",
    // a0 IH directly
    "(ih_a0 d0)))) ",
);

/// Typing.rec conv case: untyped Typing.conv directly on the subst-respecting
/// DefEq (no Eq.substType / def_eq_to_eq detour). Brick 9: rerouted off the FALSE
/// def_eq_to_eq bridge onto the untyped conversion rule Typing.conv
/// (Typing e A -> DefEq A B -> Typing e B).
const SUBST_CONV_CASE: &str = concat!(
    "(fun (e0 : KExpr) (A0 : KExpr) (B0 : KExpr) ",
    "(_he0 : Typing e0 A0) (eq0 : DefEq A0 B0) ",
    "(ih_e0 : forall (d2 : Nat), Typing (instantiate_at e0 a d2) ",
    "(instantiate_at A0 a d2)) ",
    "(d0 : Nat) => ",
    "Typing.conv (instantiate_at e0 a d0) ",
    "(instantiate_at A0 a d0) (instantiate_at B0 a d0) ",
    "(ih_e0 d0) ",
    "(def_eq_respects_subst_at A0 B0 a d0 wd wr eq0)) ",
);

/// Typing.rec preamble: fun binders + motive.
/// Part of #2870: binder domain universe generalized from Nat.zero to u.
const SUBST_PROOF_PREAMBLE: &str = concat!(
    "fun (A : KExpr) (B : KExpr) (b : KExpr) (a : KExpr) (d : Nat) (u : Level) ",
    "(wd : DefEnvWellformed the_red_env) ",
    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
    "(hA : Typing A (KExpr.sort u)) (hb : Typing b B) ",
    "(ha : Typing a A) => ",
    "Typing.rec ",
    "(fun (e0 : KExpr) (T0 : KExpr) (_ : Typing e0 T0) => ",
    "forall (d0 : Nat), ",
    "Typing (instantiate_at e0 a d0) (instantiate_at T0 a d0)) ",
);

/// Typing.rec application: apply the eliminator to the derivation.
const SUBST_PROOF_EPILOGUE: &str = "b B hb d";

fn subst_typing_gen_proof() -> String {
    format!(
        "{preamble}{sort}{pi}{lam}{app}{conv}{epilogue}",
        preamble = SUBST_PROOF_PREAMBLE,
        sort = SUBST_SORT_CASE,
        pi = SUBST_PI_CASE,
        lam = SUBST_LAM_CASE,
        app = SUBST_APP_CASE,
        conv = SUBST_CONV_CASE,
        epilogue = SUBST_PROOF_EPILOGUE,
    )
}

impl Specification {
    pub(super) fn add_type_preservation_subst(&mut self) -> Result<(), SpecError> {
        self.add_subst_typing_gen()?;
        self.add_subst_typing()?;
        self.add_def_eq_instantiate_arg_congr()?;
        Ok(())
    }

    fn add_def_eq_instantiate_arg_congr(&mut self) -> Result<(), SpecError> {
        // DefEq congruence for the argument position of instantiate.
        // If a ~ a', then instantiate B a ~ instantiate B a' for any B.
        // Proof: delegates to def_eq_instantiate_arg_congr_at at depth 0.
        // Part of #464, #3221.
        self.add_definition(SpecDefinition {
            name: "def_eq_instantiate_arg_congr".to_string(),
            type_src: concat!(
                "forall (B : KExpr) (a : KExpr) (a' : KExpr), ",
                "RedEnvFaithful the_red_env -> ",
                "DefEq a a' -> DefEq (instantiate B a) (instantiate B a')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (B : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(hf : RedEnvFaithful the_red_env) (h : DefEq a a') => ",
                    "def_eq_instantiate_arg_congr_at B a a' Nat.zero hf h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "DefEq congruence for instantiate argument: if a ~ a', then ",
                "B[a/0] ~ B[a'/0]. Proof: delegates to def_eq_instantiate_arg_congr_at ",
                "at depth 0. DerivedProved: def_eq_instantiate_arg_congr_at carries a ",
                "complete kernel-checked KExpr.rec proof (its status flag previously lagged). ",
                "Part of #464, #3221."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "def_eq_instantiate_arg_congr_at".to_string()
            ])),
            axiom_deps: HashSet::new(),
        })
    }

    fn add_subst_typing_gen(&mut self) -> Result<(), SpecError> {
        // DerivedProved via Typing.rec: sort/pi/lam/app cases constructive,
        // and the conv case transports typing via the untyped Typing.conv rule
        // directly on def_eq_respects_subst_at (Brick 9: rerouted off the FALSE
        // def_eq_to_eq bridge; def_eq_to_eq is DELETED, #2859). Every dependency
        // is now DerivedProved (def_eq_respects_subst_at graduated in #2872; the
        // sibling def_eq_instantiate_arg_congr lane graduated with the proved
        // def_eq_instantiate_arg_congr_at leaf, #3221), so the status flag no
        // longer lags.
        // App case uses dependent Typing.app rule + instantiate_nested_commutes_zero_subst.
        // Part of #464.
        self.add_definition(SpecDefinition {
            name: "substitution_typing_gen".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (B : KExpr) (b : KExpr) (a : KExpr) (d : Nat) (u : Level), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "has_type A (KExpr.sort u) -> has_type b B -> has_type a A -> ",
                "has_type (instantiate_at b a d) (instantiate_at B a d)"
            )
            .to_string(),
            value_src: Some(subst_typing_gen_proof()),
            is_axiom: false,
            description: concat!(
                "Depth-generalized substitution typing: if b : B and a : A (with A : Sort u), then ",
                "instantiate_at b a d : instantiate_at B a d for any depth d. ",
                "DerivedProved via Typing.rec: conv case uses Typing.conv (Brick 9). ",
                "App case closed by dependent Typing.app + ",
                "instantiate_nested_commutes_zero_subst transport. ",
                "Part of #464, #2870."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            // DerivedProved: conv case transports type via Typing.conv (Brick 9)
            // on the proved def_eq_respects_subst_at; other axiom_deps resolved
            // by #725 reduction witnesses.
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Typing.sort".to_string(),
                "Typing.pi".to_string(),
                "Typing.lam".to_string(),
                "Typing.app".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Typing.conv".to_string(),
                "typed_def_eq_to_def_eq".to_string(),
                "instantiate_at_sort".to_string(),
                "instantiate_at_app".to_string(),
                "instantiate_at_pi".to_string(),
                "instantiate_at_lam".to_string(),
                "instantiate_nested_commutes_zero_subst".to_string(),
                "def_eq_respects_subst_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })
    }

    fn add_subst_typing(&mut self) -> Result<(), SpecError> {
        // DerivedProved via substitution_typing_gen at depth 0. Part of #464.
        self.add_definition(SpecDefinition {
            name: "substitution_typing".to_string(),
            // Part of #2870: binder domain universe generalized from Nat.zero to u.
            type_src: concat!(
                "forall (A : KExpr) (B : KExpr) (b : KExpr) (a : KExpr) (u : Level), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "has_type A (KExpr.sort u) -> has_type b B -> has_type a A -> ",
                "has_type (instantiate b a) (instantiate B a)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (B : KExpr) (b : KExpr) (a : KExpr) (u : Level) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(hA : has_type A (KExpr.sort u)) ",
                    "(hb : has_type b B) ",
                    "(ha : has_type a A) => ",
                    "substitution_typing_gen A B b a Nat.zero u wd wr hA hb ha"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Substitution preserves typing: if b : B and a : A, then ",
                "b[a/x] : B[a/x]. DerivedProved from substitution_typing_gen at depth 0 ",
                "(the church_rosser_whnf frontier it formerly inherited is retired, #2859). ",
                "Part of #464."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            // DerivedProved: substitution_typing_gen graduated (its former
            // church_rosser_whnf / def_eq_to_eq frontier is retired).
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["substitution_typing_gen".to_string()])),
            axiom_deps: HashSet::new(),
        })
    }
}
