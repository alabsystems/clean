// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type preservation proof terms for the kernel ProofLibrary.
//!
//! Covers: type_preservation.rs, type_preservation_subst.rs, and
//! type_preservation_raw_bridge.rs spec definitions.
//!
//! Part of #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_type_pres_proofs(&mut self) {
        // === type_preservation.rs: def_eq_preserves_typing ===
        self.proofs.insert(
            "def_eq_preserves_typing".to_string(),
            ProofTerm::new(
                "def_eq_preserves_typing",
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(e : KExpr) (e' : KExpr) (T : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(ht : has_type e T) (heq : typing_is_def_eq e e') => ",
                    "AndType.left ",
                    "(forall (T : KExpr), has_type e T -> has_type e' T) ",
                    "(forall (T : KExpr), has_type e' T -> has_type e T) ",
                    "(def_eq_typing_iff hf e e' wd wr heq) T ht",
                ),
                "Typed definitional equality preserves typing via AndType.left of def_eq_typing_iff.",
            ),
        );

        // === type_preservation.rs: TypePreservation ===
        self.proofs.insert(
            "TypePreservation".to_string(),
            ProofTerm::new(
                "TypePreservation",
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(e : KExpr) (T : KExpr) (e' : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(ht : has_type e T) (heq : typing_is_def_eq e e') => ",
                    "def_eq_preserves_typing hf e e' T wd wr ht heq",
                ),
                "Type preservation theorem: forwards to def_eq_preserves_typing.",
            ),
        );

        // === type_preservation_subst.rs: substitution_typing_gen ===
        self.proofs.insert(
            "substitution_typing_gen".to_string(),
            ProofTerm::new(
                "substitution_typing_gen",
                concat!(
                    // SUBST_PROOF_PREAMBLE
                    "fun (A : KExpr) (B : KExpr) (b : KExpr) (a : KExpr) (d : Nat) (u : Level) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(hA : Typing A (KExpr.sort u)) (hb : Typing b B) ",
                    "(ha : Typing a A) => ",
                    "Typing.rec ",
                    "(fun (e0 : KExpr) (T0 : KExpr) (_ : Typing e0 T0) => ",
                    "forall (d0 : Nat), ",
                    "Typing (instantiate_at e0 a d0) (instantiate_at T0 a d0)) ",
                    // SUBST_SORT_CASE
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
                    // SUBST_PI_CASE
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
                    // SUBST_LAM_CASE
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
                    // SUBST_APP_CASE
                    "(fun (f0 : KExpr) (a0 : KExpr) (A0 : KExpr) (B0 : KExpr) ",
                    "(_hf0 : Typing f0 (KExpr.pi A0 B0)) (_ha0 : Typing a0 A0) ",
                    "(ih_f0 : forall (d2 : Nat), Typing (instantiate_at f0 a d2) ",
                    "(instantiate_at (KExpr.pi A0 B0) a d2)) ",
                    "(ih_a0 : forall (d2 : Nat), Typing (instantiate_at a0 a d2) ",
                    "(instantiate_at A0 a d2)) ",
                    "(d0 : Nat) => ",
                    "Eq.substType KExpr ",
                    "(fun (x : KExpr) => Typing x (instantiate_at (instantiate B0 a0) a d0)) ",
                    "(KExpr.app (instantiate_at f0 a d0) (instantiate_at a0 a d0)) ",
                    "(instantiate_at (KExpr.app f0 a0) a d0) ",
                    "(Eq.symm KExpr (instantiate_at (KExpr.app f0 a0) a d0) ",
                    "(KExpr.app (instantiate_at f0 a d0) (instantiate_at a0 a d0)) ",
                    "(instantiate_at_app f0 a0 a d0)) ",
                    "(Eq.substType KExpr ",
                    "(fun (y : KExpr) => Typing (KExpr.app (instantiate_at f0 a d0) ",
                    "(instantiate_at a0 a d0)) y) ",
                    "(instantiate (instantiate_at B0 a (Nat.succ d0)) (instantiate_at a0 a d0)) ",
                    "(instantiate_at (instantiate B0 a0) a d0) ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (instantiate B0 a0) a d0) ",
                    "(instantiate (instantiate_at B0 a (Nat.succ d0)) (instantiate_at a0 a d0)) ",
                    "(instantiate_nested_commutes_zero_subst B0 a0 a d0)) ",
                    "(Typing.app (instantiate_at f0 a d0) (instantiate_at a0 a d0) ",
                    "(instantiate_at A0 a d0) (instantiate_at B0 a (Nat.succ d0)) ",
                    "(Eq.substType KExpr ",
                    "(fun (y : KExpr) => Typing (instantiate_at f0 a d0) y) ",
                    "(instantiate_at (KExpr.pi A0 B0) a d0) ",
                    "(KExpr.pi (instantiate_at A0 a d0) (instantiate_at B0 a (Nat.succ d0))) ",
                    "(instantiate_at_pi A0 B0 a d0) ",
                    "(ih_f0 d0)) ",
                    "(ih_a0 d0)))) ",
                    // SUBST_CONV_CASE (Brick 9: rerouted off def_eq_to_eq onto untyped Typing.conv)
                    "(fun (e0 : KExpr) (A0 : KExpr) (B0 : KExpr) ",
                    "(_he0 : Typing e0 A0) (eq0 : DefEq A0 B0) ",
                    "(ih_e0 : forall (d2 : Nat), Typing (instantiate_at e0 a d2) ",
                    "(instantiate_at A0 a d2)) ",
                    "(d0 : Nat) => ",
                    "Typing.conv (instantiate_at e0 a d0) ",
                    "(instantiate_at A0 a d0) (instantiate_at B0 a d0) ",
                    "(ih_e0 d0) ",
                    "(def_eq_respects_subst_at A0 B0 a d0 wd wr eq0)) ",
                    // SUBST_PROOF_EPILOGUE
                    "b B hb d",
                ),
                concat!(
                    "Depth-generalized substitution typing: if b : B and a : A, then ",
                    "instantiate_at b a d : instantiate_at B a d. Via Typing.rec.",
                ),
            ),
        );

        // === type_preservation_subst.rs: substitution_typing ===
        self.proofs.insert(
            "substitution_typing".to_string(),
            ProofTerm::new(
                "substitution_typing",
                concat!(
                    "fun (A : KExpr) (B : KExpr) (b : KExpr) (a : KExpr) (u : Level) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(hA : has_type A (KExpr.sort u)) ",
                    "(hb : has_type b B) ",
                    "(ha : has_type a A) => ",
                    "substitution_typing_gen A B b a Nat.zero u wd wr hA hb ha",
                ),
                "Substitution typing at depth 0 via substitution_typing_gen.",
            ),
        );

        // === type_preservation_raw_bridge.rs: raw_type_conversion ===
        // #2859: Typing.conv is now UNTYPED and takes the raw DefEq directly, and
        // the raw_to_typed_def_eq forward bridge is retired — so the shim applies
        // Typing.conv directly to the raw is_def_eq witness (matching the
        // raw_type_conversion spec definition).
        self.proofs.insert(
            "raw_type_conversion".to_string(),
            ProofTerm::new(
                "raw_type_conversion",
                concat!(
                    "fun (e : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                    "(ht : has_type e T1) (heq : is_def_eq T1 T2) => ",
                    "Typing.conv e T1 T2 ht heq",
                ),
                "Raw type conversion compatibility shim via the untyped Typing.conv.",
            ),
        );

        // raw_def_eq_preserves_typing is RETIRED (#2859): under untyped DefEq.beta,
        // raw (symmetric) DefEq subject reduction is FALSE (subject-expansion
        // counterexample), so the spec definition was removed. The corresponding
        // library proof is dropped with it — every real consumer feeds the
        // now-untyped Typing.conv directly, or uses the FORWARD whnf_to lane.
    }
}
