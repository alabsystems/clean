// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel proof registration methods for ProofLibrary.
//!
//! Contains the core `add_*_proofs()` methods that populate the library
//! with proof terms for kernel properties (def_eq, typing, whnf, termination,
//! expression operations, soundness, type preservation).
//!
//! Forward simulation and implementation soundness proofs are in
//! `library_simulation.rs`.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    /// Add definitional equality proofs (C001: 7 constructive proof terms)
    ///
    /// All proofs directly invoke `DefEq` inductive constructors from the
    /// foundational rule base, avoiding the backward-compatible alias layer
    /// (`def_eq_refl`, `def_eq_symm`, etc.). This ensures every C001 proof
    /// term is fully constructive with zero HelperAxiom dependencies.
    ///
    /// Part of #3306: Replace C001 placeholder axioms with real inductive proofs.
    pub(super) fn add_def_eq_proofs(&mut self) {
        // ── C001-1: Reflexivity ──────────────────────────────────────────
        // DefEq.refl : forall (a : KExpr), DefEq a a
        // Proof: direct application of the DefEq.refl inductive constructor.
        self.proofs.insert(
            "def_eq_refl".to_string(),
            ProofTerm::new(
                "def_eq_refl",
                "fun (e : KExpr) => DefEq.refl e",
                "Reflexivity: direct DefEq.refl constructor (no alias indirection). Part of #3306.",
            ),
        );

        // ── C001-2: Symmetry ─────────────────────────────────────────────
        // DefEq.symm : forall (a b : KExpr), DefEq a b -> DefEq b a
        // Proof: direct application of the DefEq.symm inductive constructor.
        self.proofs.insert(
            "def_eq_symm".to_string(),
            ProofTerm::new(
                "def_eq_symm",
                "fun (a : KExpr) (b : KExpr) (h : DefEq a b) => DefEq.symm a b h",
                "Symmetry: direct DefEq.symm constructor. Part of #3306.",
            ),
        );

        // ── C001-3: Transitivity ─────────────────────────────────────────
        // DefEq.trans : forall (a b c : KExpr), DefEq a b -> DefEq b c -> DefEq a c
        // Proof: direct application of the DefEq.trans inductive constructor.
        self.proofs.insert(
            "def_eq_trans".to_string(),
            ProofTerm::new(
                "def_eq_trans",
                "fun (a : KExpr) (b : KExpr) (c : KExpr) (h1 : DefEq a b) (h2 : DefEq b c) => DefEq.trans a b c h1 h2",
                "Transitivity: direct DefEq.trans constructor. Part of #3306.",
            ),
        );

        // ── C001-4: Application congruence ───────────────────────────────
        // DefEq.app_cong : forall (f f' a a' : KExpr),
        //   DefEq f f' -> DefEq a a' -> DefEq (app f a) (app f' a')
        // Proof: direct application of the DefEq.app_cong inductive constructor.
        self.proofs.insert(
            "def_eq_congr_app".to_string(),
            ProofTerm::new(
                "def_eq_app_cong",
                "fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (hf : DefEq f f') (ha : DefEq a a') => DefEq.app_cong f f' a a' hf ha",
                "Application congruence: direct DefEq.app_cong constructor. Part of #3306.",
            ),
        );

        // ── C001-5: Lambda congruence ────────────────────────────────────
        // def_eq_lam_cong : forall (A b b' : KExpr),
        //   DefEq b b' -> DefEq (lam A b) (lam A b')
        // Proof: DefEq.lam_cong A A b b' (DefEq.refl A) hb
        // The simplified form keeps the domain A the same, so we use
        // DefEq.refl A for the domain equality witness.
        self.proofs.insert(
            "def_eq_congr_lam".to_string(),
            ProofTerm::new(
                "def_eq_lam_cong",
                "fun (A : KExpr) (b : KExpr) (b' : KExpr) (hb : DefEq b b') => DefEq.lam_cong A A b b' (DefEq.refl A) hb",
                "Lambda congruence: DefEq.lam_cong with DefEq.refl for domain. Part of #3306.",
            ),
        );

        // ── C001-6: Pi congruence ────────────────────────────────────────
        // DefEq.pi_cong : forall (A A' B B' : KExpr),
        //   DefEq A A' -> DefEq B B' -> DefEq (pi A B) (pi A' B')
        // Proof: direct application of the DefEq.pi_cong inductive constructor.
        self.proofs.insert(
            "def_eq_congr_pi".to_string(),
            ProofTerm::new(
                "def_eq_pi_cong",
                "fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) (hA : DefEq A A') (hB : DefEq B B') => DefEq.pi_cong A A' B B' hA hB",
                "Pi congruence: direct DefEq.pi_cong constructor. Part of #3306.",
            ),
        );

        // ── C001-7: Typed beta reduction ─────────────────────────────────
        // The `beta_reduction` property keeps the TYPED statement
        //   forall (A b a : KExpr) (B : KExpr) (u : Nat),
        //     Typing A (Sort u) -> Typing b B -> Typing a A ->
        //     DefEq (app (lam A b) a) (instantiate b a)
        // but DefEq.beta itself is now UNTYPED (church_rosser_whnf retirement
        // track): `forall (A b a : KExpr), DefEq (app (lam A b) a) (instantiate b a)`.
        // The proof binds the typing witnesses (to inhabit the typed property type)
        // and discards them, applying the untyped DefEq.beta constructor — exactly
        // as the `beta_reduction` spec alias does.
        self.proofs.insert(
            "def_eq_beta".to_string(),
            ProofTerm::new(
                "beta_reduction",
                "fun (A : KExpr) (b : KExpr) (a : KExpr) (_B : KExpr) (_u : Level) (_hA : Typing A (KExpr.sort _u)) (_hb : Typing b _B) (_ha : Typing a A) => DefEq.beta A b a",
                "Typed beta reduction property, discharged by the untyped DefEq.beta constructor. Part of #3306, #2859.",
            ),
        );
    }

    /// Add typing rule proofs
    pub(super) fn add_typing_proofs(&mut self) {
        // Sort typing (uses axiom)
        self.proofs.insert(
            "sort_typed".to_string(),
            ProofTerm::new(
                "sort_typing",
                "fun (n : Level) => sort_typing n",
                "Sort typing is directly an axiom",
            ),
        );

        // Identity function is well-typed
        // id : (A : Type) -> A -> A
        // id A x = x
        // Type: (A : Type) -> (x : A) -> A
        self.proofs.insert(
            "identity_typed".to_string(),
            ProofTerm::new(
                "identity_typing",
                "fun (A : Type) (x : A) => x",
                "The identity function (fun x => x) has type A -> A",
            ),
        );

        // Const function is well-typed
        // const : (A : Type) -> (B : Type) -> A -> B -> A
        // const A B a b = a
        self.proofs.insert(
            "const_typed".to_string(),
            ProofTerm::new(
                "const_typing",
                "fun (A : Type) (B : Type) (a : A) (b : B) => a",
                "The const function (fun a b => a) is well-typed",
            ),
        );

        // Composition is well-typed
        // compose : (A : Type) -> (B : Type) -> (C : Type) -> (B -> C) -> (A -> B) -> A -> C
        self.proofs.insert(
            "compose_typed".to_string(),
            ProofTerm::new(
                "compose_typing",
                "fun (A : Type) (B : Type) (C : Type) (g : B -> C) (f : A -> B) (x : A) => g (f x)",
                "Function composition is well-typed",
            ),
        );

        // Flip function
        // flip : (A : Type) -> (B : Type) -> (C : Type) -> (A -> B -> C) -> B -> A -> C
        self.proofs.insert(
            "flip_typed".to_string(),
            ProofTerm::new(
                "flip_typing",
                "fun (A : Type) (B : Type) (C : Type) (f : A -> B -> C) (b : B) (a : A) => f a b",
                "The flip function is well-typed",
            ),
        );
    }

    /// Add WHNF and reduction proofs (C004: 9 constructive proof terms)
    ///
    /// All 9 formerly-bare-constant proof terms now use explicit lambda
    /// abstractions that directly invoke inductive constructors or
    /// derived lemmas. This ensures every C004 proof term is fully
    /// constructive with zero HelperAxiom dependencies.
    ///
    /// Part of #3308: Replace C004 placeholder axioms with real constructive proofs.
    pub(super) fn add_whnf_proofs(&mut self) {
        // Sort is a value - uses the is_value.sort constructor
        self.proofs.insert(
            "sort_value".to_string(),
            ProofTerm::new(
                "is_value.sort",
                "fun (n : Level) => IsValue.sort n",
                "Sort n is a value (constructor of is_value inductive)",
            ),
        );

        // Lambda is a value - uses the is_value.lam constructor
        self.proofs.insert(
            "lam_value".to_string(),
            ProofTerm::new(
                "is_value.lam",
                "fun (ty : KExpr) (body : KExpr) => IsValue.lam ty body",
                "Lambda abstractions are values (constructor of is_value inductive)",
            ),
        );

        // Pi is a value - uses the is_value.pi constructor
        self.proofs.insert(
            "pi_value".to_string(),
            ProofTerm::new(
                "is_value.pi",
                "fun (ty : KExpr) (body : KExpr) => IsValue.pi ty body",
                "Pi types are values (constructor of is_value inductive)",
            ),
        );

        // Values are in WHNF - proof of the value_in_whnf derived lemma
        // Uses WhnfTo.refl constructor directly (whnf_to is inductive per #412)
        // Note: This proves the value_in_whnf spec definition using the PascalCase alias.
        self.proofs.insert(
            "value_whnf".to_string(),
            ProofTerm::new(
                "value_in_whnf",
                "fun (e : KExpr) (h : is_value e) => WhnfTo.refl e (value_is_whnf e h)",
                "Values are in WHNF: derived lemma proved via value_is_whnf + WhnfTo.refl",
            ),
        );

        // WHNF idempotence — constructive proof via whnf_to_target_is_whnf + whnf_to.refl.
        // Previously bare constant (Part of #1385); now eta-expanded for C004 (#3308).
        self.proofs.insert(
            "whnf_idem".to_string(),
            ProofTerm::new(
                "whnf_idempotent",
                "fun (e : KExpr) (e' : KExpr) (h : whnf_to e e') => whnf_to.refl e' (whnf_to_target_is_whnf e e' h)",
                "WHNF is idempotent: constructive proof via whnf_to_target_is_whnf + whnf_to.refl. Part of #3308.",
            ),
        );

        // WHNF confluence — constructive proof via whnf_to_preserves_def_eq + DefEq.symm + DefEq.trans.
        // Previously bare constant (Part of #1385); now eta-expanded for C004 (#3308).
        self.proofs.insert(
            "whnf_conf".to_string(),
            ProofTerm::new(
                "whnf_confluent",
                "fun (e : KExpr) (e1 : KExpr) (e2 : KExpr) (h1 : whnf_to e e1) (h2 : whnf_to e e2) => DefEq.trans e1 e e2 (DefEq.symm e e1 (whnf_to_preserves_def_eq e e1 h1)) (whnf_to_preserves_def_eq e e2 h2)",
                "WHNF confluence: constructive proof via whnf_to_preserves_def_eq + DefEq.symm + DefEq.trans. Part of #3308.",
            ),
        );

        // Beta reduction is deterministic — constructive proof via
        // beta_reduces_preserves_def_eq + DefEq.symm + DefEq.trans.
        // Previously bare constant (Part of #1385); now eta-expanded for C004 (#3308).
        self.proofs.insert(
            "beta_det".to_string(),
            ProofTerm::new(
                "beta_deterministic",
                "fun (e : KExpr) (r1 : KExpr) (r2 : KExpr) (h1 : beta_reduces e r1) (h2 : beta_reduces e r2) => DefEq.trans r1 e r2 (DefEq.symm e r1 (beta_reduces_preserves_def_eq e r1 h1)) (beta_reduces_preserves_def_eq e r2 h2)",
                "Beta deterministic: constructive proof via beta_reduces_preserves_def_eq + DefEq.symm + DefEq.trans. Part of #3308.",
            ),
        );

        // beta_reduces constructors (converted to inductive per #412)
        // BetaReduces.beta: beta reduction of redex
        self.proofs.insert(
            "beta_redex".to_string(),
            ProofTerm::new(
                "beta_reduces.beta",
                "fun (A : KExpr) (body : KExpr) (arg : KExpr) => BetaReduces.beta A body arg",
                "(λA.body) arg beta-reduces to instantiate body arg (constructor of beta_reduces inductive)",
            ),
        );

        // ── C004-4: BetaReduces.app_left ────────────────────────────────
        // Congruence in function position — eta-expanded from bare constructor.
        // Part of #3308.
        self.proofs.insert(
            "beta_app_left".to_string(),
            ProofTerm::new(
                "beta_reduces.app_left",
                "fun (f : KExpr) (f' : KExpr) (a : KExpr) (h : beta_reduces f f') => BetaReduces.app_left f f' a h",
                "f -> f' implies (f a) -> (f' a): direct BetaReduces.app_left constructor. Part of #3308.",
            ),
        );

        // ── C004-5: BetaReduces.app_right ───────────────────────────────
        // Congruence in argument position — eta-expanded from bare constructor.
        // Part of #3308.
        self.proofs.insert(
            "beta_app_right".to_string(),
            ProofTerm::new(
                "beta_reduces.app_right",
                "fun (f : KExpr) (a : KExpr) (a' : KExpr) (h : beta_reduces a a') => BetaReduces.app_right f a a' h",
                "a -> a' implies (f a) -> (f a'): direct BetaReduces.app_right constructor. Part of #3308.",
            ),
        );

        // ── C004-6: BetaReduces.lam_ty ──────────────────────────────────
        // Congruence in lambda type annotation — eta-expanded from bare constructor.
        // Part of #3308.
        self.proofs.insert(
            "beta_lam_ty".to_string(),
            ProofTerm::new(
                "beta_reduces.lam_ty",
                "fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (h : beta_reduces ty ty') => BetaReduces.lam_ty ty ty' body h",
                "ty -> ty' implies (lam ty body) -> (lam ty' body): direct BetaReduces.lam_ty constructor. Part of #3308.",
            ),
        );

        // ── C004-7: BetaReduces.lam_body ────────────────────────────────
        // Congruence in lambda body — eta-expanded from bare constructor.
        // Part of #3308.
        self.proofs.insert(
            "beta_lam_body".to_string(),
            ProofTerm::new(
                "beta_reduces.lam_body",
                "fun (ty : KExpr) (body : KExpr) (body' : KExpr) (h : beta_reduces body body') => BetaReduces.lam_body ty body body' h",
                "body -> body' implies (lam ty body) -> (lam ty body'): direct BetaReduces.lam_body constructor. Part of #3308.",
            ),
        );

        // ── C004-8: BetaReduces.pi_dom ──────────────────────────────────
        // Congruence in Pi domain — eta-expanded from bare constructor.
        // Part of #3308.
        self.proofs.insert(
            "beta_pi_dom".to_string(),
            ProofTerm::new(
                "beta_reduces.pi_dom",
                "fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (h : beta_reduces dom dom') => BetaReduces.pi_dom dom dom' body h",
                "dom -> dom' implies (pi dom body) -> (pi dom' body): direct BetaReduces.pi_dom constructor. Part of #3308.",
            ),
        );

        // ── C004-9: BetaReduces.pi_cod ──────────────────────────────────
        // Congruence in Pi codomain — eta-expanded from bare constructor.
        // Part of #3308.
        self.proofs.insert(
            "beta_pi_cod".to_string(),
            ProofTerm::new(
                "beta_reduces.pi_cod",
                "fun (dom : KExpr) (body : KExpr) (body' : KExpr) (h : beta_reduces body body') => BetaReduces.pi_cod dom body body' h",
                "body -> body' implies (pi dom body) -> (pi dom body'): direct BetaReduces.pi_cod constructor. Part of #3308.",
            ),
        );

        // whnf_to constructors (converted to inductive per #412)
        // WhnfTo.refl: values are in WHNF
        self.proofs.insert(
            "whnf_refl".to_string(),
            ProofTerm::new(
                "whnf_to.refl",
                "fun (e : KExpr) (h : is_whnf e) => WhnfTo.refl e h",
                "WHNF reflexivity (constructor of whnf_to inductive)",
            ),
        );

        // WhnfTo.step: one step of reduction followed by more
        // Eta-expanded from bare constructor for consistency with C004 (#3308).
        self.proofs.insert(
            "whnf_step".to_string(),
            ProofTerm::new(
                "whnf_to.step",
                "fun (e : KExpr) (e' : KExpr) (v : KExpr) (hs : whnf_step e e') (hr : whnf_to e' v) => WhnfTo.step e e' v hs hr",
                "e -> e' and e' ->* v implies e ->* v: direct WhnfTo.step constructor. Part of #3308.",
            ),
        );
    }

    /// Add termination proofs (converted from Verus)
    pub(super) fn add_termination_proofs(&mut self) {
        // WHNF terminates on well-typed terms
        self.proofs.insert(
            "whnf_term".to_string(),
            ProofTerm::new(
                "whnf_terminates_well_typed",
                "fun (e : KExpr) (T : KExpr) (h : has_type e T) => whnf_terminates_well_typed e T h",
                "WHNF terminates on well-typed terms (from Verus fuel-based termination)",
            ),
        );

        // Type inference terminates
        self.proofs.insert(
            "infer_term".to_string(),
            ProofTerm::new(
                "infer_terminates",
                "fun (e : KExpr) => infer_terminates e",
                "Type inference always terminates (from Verus lemma_infer_sort_succeeds, etc.)",
            ),
        );
    }

    /// Add expression operation proofs (C006: 12 constructive proof terms)
    ///
    /// All proofs reference DerivedProved spec definitions with real constructive
    /// value terms. The lift_at structural lemmas use Eq.refl (definitional
    /// equality). The composite lemmas (lift_zero_identity, instantiate_bvar_zero,
    /// lift_cancel) chain through equality transports. Zero HelperAxiom
    /// dependencies.
    ///
    /// Part of #3309: Replace C006 placeholder axioms with real constructive proofs.
    pub(super) fn add_expr_operation_proofs(&mut self) {
        // ── C006-1: lift_at sort identity ────────────────────────────────
        // lift_at (sort n) cutoff amount = sort n
        // Proof: Eq.refl — sort has no bound variables to lift.
        self.proofs.insert(
            "lift_at_sort".to_string(),
            ProofTerm::new(
                "lift_at_sort",
                "fun (n : Level) (cutoff : Nat) (amount : Nat) => Eq.refl KExpr (KExpr.sort n)",
                "lift_at on sort is identity. DerivedProved via Eq.refl. Part of #3309.",
            ),
        );

        // ── C006-2: lift_at distributes over app ─────────────────────────
        // lift_at (app f a) cutoff amount = app (lift_at f cutoff amount) (lift_at a cutoff amount)
        // Proof: Eq.refl — definitional by the match arm in lift_at.
        self.proofs.insert(
            "lift_at_app".to_string(),
            ProofTerm::new(
                "lift_at_app",
                "fun (f : KExpr) (a : KExpr) (cutoff : Nat) (amount : Nat) => Eq.refl KExpr (KExpr.app (lift_at f cutoff amount) (lift_at a cutoff amount))",
                "lift_at distributes over app. DerivedProved via Eq.refl. Part of #3309.",
            ),
        );

        // ── C006-3: lift_at distributes over lam ─────────────────────────
        // lift_at (lam ty body) cutoff amount = lam (lift_at ty cutoff amount) (lift_at body (succ cutoff) amount)
        // Proof: Eq.refl — definitional by the match arm in lift_at.
        self.proofs.insert(
            "lift_at_lam".to_string(),
            ProofTerm::new(
                "lift_at_lam",
                "fun (ty : KExpr) (body : KExpr) (cutoff : Nat) (amount : Nat) => Eq.refl KExpr (KExpr.lam (lift_at ty cutoff amount) (lift_at body (Nat.succ cutoff) amount))",
                "lift_at distributes over lam (incrementing cutoff). DerivedProved via Eq.refl. Part of #3309.",
            ),
        );

        // ── C006-4: lift_at distributes over pi ──────────────────────────
        // lift_at (pi ty body) cutoff amount = pi (lift_at ty cutoff amount) (lift_at body (succ cutoff) amount)
        // Proof: Eq.refl — definitional by the match arm in lift_at.
        self.proofs.insert(
            "lift_at_pi".to_string(),
            ProofTerm::new(
                "lift_at_pi",
                "fun (ty : KExpr) (body : KExpr) (cutoff : Nat) (amount : Nat) => Eq.refl KExpr (KExpr.pi (lift_at ty cutoff amount) (lift_at body (Nat.succ cutoff) amount))",
                "lift_at distributes over pi (incrementing cutoff). DerivedProved via Eq.refl. Part of #3309.",
            ),
        );

        // ── C006-5: lift_at amount zero is identity ──────────────────────
        // forall (e : KExpr) (cutoff : Nat), lift_at e cutoff 0 = e
        // Proof: KExpr.rec structural induction with cutoff-universalized motive.
        self.proofs.insert(
            "lift_at_amount_zero".to_string(),
            ProofTerm::new(
                "lift_at_amount_zero",
                "fun (e : KExpr) (cutoff : Nat) => lift_at_amount_zero e cutoff",
                "Lifting by amount 0 is identity. DerivedProved via KExpr.rec structural induction. Part of #3309.",
            ),
        );

        // ── C006-6: lift zero is identity ────────────────────────────────
        // forall (e : KExpr), lift e 0 = e
        // Proof: specialization of lift_at_amount_zero at cutoff 0.
        self.proofs.insert(
            "lift_zero".to_string(),
            ProofTerm::new(
                "lift_zero_identity",
                "fun (e : KExpr) => lift_at_amount_zero e Nat.zero",
                "lift e 0 = e. DerivedProved: specialization of lift_at_amount_zero at cutoff 0. Part of #3309.",
            ),
        );

        // ── C006-7: instantiate on sort is identity ──────────────────────
        // forall (n : Nat) (val : KExpr), instantiate (sort n) val = sort n
        // Proof: Eq.refl — sort has no bound variables to substitute.
        self.proofs.insert(
            "instantiate_sort".to_string(),
            ProofTerm::new(
                "instantiate_sort",
                "fun (n : Level) (val : KExpr) => Eq.refl KExpr (KExpr.sort n)",
                "instantiate (sort n) val = sort n. DerivedProved via Eq.refl. Part of #3309.",
            ),
        );

        // ── C006-8: instantiate distributes over app ─────────────────────
        // forall (f a val : KExpr), instantiate (app f a) val = app (instantiate f val) (instantiate a val)
        // Proof: forwarded through instantiate_at_app at depth 0.
        self.proofs.insert(
            "instantiate_app".to_string(),
            ProofTerm::new(
                "instantiate_app",
                "fun (f : KExpr) (a : KExpr) (val : KExpr) => instantiate_at_app f a val Nat.zero",
                "instantiate distributes over app. DerivedProved via instantiate_at_app at depth 0. Part of #3309.",
            ),
        );

        // ── C006-9: instantiate distributes over lam ─────────────────────
        // forall (ty b val : KExpr), instantiate (lam ty b) val = lam (instantiate ty val) (instantiate_at b val 1)
        // Proof: forwarded through instantiate_at_lam at depth 0.
        self.proofs.insert(
            "instantiate_lam".to_string(),
            ProofTerm::new(
                "instantiate_lam",
                "fun (ty : KExpr) (b : KExpr) (val : KExpr) => instantiate_at_lam ty b val Nat.zero",
                "instantiate distributes over lam with depth tracking. DerivedProved via instantiate_at_lam at depth 0. Part of #3309.",
            ),
        );

        // ── C006-10: instantiate distributes over pi ─────────────────────
        // forall (ty b val : KExpr), instantiate (pi ty b) val = pi (instantiate ty val) (instantiate_at b val 1)
        // Proof: forwarded through instantiate_at_pi at depth 0.
        self.proofs.insert(
            "instantiate_pi".to_string(),
            ProofTerm::new(
                "instantiate_pi",
                "fun (ty : KExpr) (b : KExpr) (val : KExpr) => instantiate_at_pi ty b val Nat.zero",
                "instantiate distributes over pi with depth tracking. DerivedProved via instantiate_at_pi at depth 0. Part of #3309.",
            ),
        );

        // ── C006-11: instantiate BVar 0 gives value ─────────────────────
        // forall (val : KExpr), instantiate (BVar 0) val = val
        // Proof: equality chain through instantiate_at_bvar, instantiate_bvar_at_eq,
        // and lift_at_amount_zero (all constructive).
        self.proofs.insert(
            "inst_bvar_zero".to_string(),
            ProofTerm::new(
                "instantiate_bvar_zero",
                "fun (val : KExpr) => instantiate_bvar_zero val",
                "instantiate (BVar 0) val = val. DerivedProved via equality chain. Part of #3309.",
            ),
        );

        // ── C006-12: lift/instantiate cancellation ───────────────────────
        // forall (e val : KExpr), instantiate_at (lift_at e 0 1) val 0 = e
        // Proof: specialization of lift_cancel_gen at cutoff 0. lift_cancel_gen is
        // proved via cutoff-universalized KExpr.rec structural induction.
        self.proofs.insert(
            "lift_cancel".to_string(),
            ProofTerm::new(
                "lift_cancel",
                "fun (e : KExpr) (val : KExpr) => lift_cancel_gen e val Nat.zero",
                "lift/instantiate cancellation: instantiate_at (lift_at e 0 1) val 0 = e. DerivedProved via lift_cancel_gen at cutoff 0. Part of #3309.",
            ),
        );
    }

    /// Add soundness proofs (converted from Verus)
    pub(super) fn add_soundness_proofs(&mut self) {
        // Sort typing soundness (connects to has_type specification)
        self.proofs.insert(
            "sort_sound".to_string(),
            ProofTerm::new(
                "sort_typing",
                "fun (n : Level) => sort_typing n",
                "Sort n : Sort (n+1) is sound (from Verus lemma_infer_sort_sound)",
            ),
        );

        // Pi formation soundness
        self.proofs.insert(
            "pi_sound".to_string(),
            ProofTerm::new(
                "pi_formation",
                "fun (A : KExpr) (B : KExpr) (n : Level) (m : Level) (hA : Typing A (KExpr.sort n)) (hB : Typing B (KExpr.sort m)) => pi_formation A B n m hA hB",
                "Pi formation rule is sound (from Verus typing_rule_pi specification)",
            ),
        );

        // Lambda typing soundness
        self.proofs.insert(
            "lam_sound".to_string(),
            ProofTerm::new(
                "lam_typing",
                "fun (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) (hA : Typing A (KExpr.sort u)) (hb : Typing b B) => lam_typing A b B u hA hb",
                "Lambda typing rule is sound (from Verus typing_rule_lam specification)",
            ),
        );

        // Application typing soundness
        self.proofs.insert(
            "app_sound".to_string(),
            ProofTerm::new(
                "app_typing",
                "fun (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) (hf : Typing f (KExpr.pi A B)) (ha : Typing a A) => app_typing f a A B hf ha",
                "Application typing rule is sound (from Verus typing_rule_app specification)",
            ),
        );

        self.proofs.insert(
            "constant_extension_intro".to_string(),
            ProofTerm::new(
                "ConstantExtension.mk",
                "fun (env : KEnv) (kind : ConstExtensionKind) (decl_id : Nat) (ty : KExpr) (value : KExpr) (u : Level) (h_fresh : FreshDeclName env decl_id) (h_ty : Typing ty (KExpr.sort u)) (h_value : Typing value ty) => ConstantExtension.mk env kind decl_id ty value u h_fresh h_ty h_value",
                "Immediate constant extension rule exposing the fresh-name side condition.",
            ),
        );

        self.proofs.insert(
            "inductive_extension_intro".to_string(),
            ProofTerm::new(
                "InductiveExtension.mk",
                "fun (env : KEnv) (decl_id : Nat) (num_params : Nat) (ind_ty : KExpr) (ctors : CtorDecls) (u : Level) (h_fresh : FreshDeclName env decl_id) (h_ty : Typing ind_ty (KExpr.sort u)) (h_pos : StrictlyPositiveCtorDecls ind_ty ctors) (h_wf : WellFormedCtorDecls env decl_id num_params ind_ty ctors) => InductiveExtension.mk env decl_id num_params ind_ty ctors u h_fresh h_ty h_pos h_wf",
                "Immediate inductive extension rule exposing positivity and constructor well-formedness side conditions.",
            ),
        );

        self.proofs.insert(
            "constant_extension_soundness".to_string(),
            ProofTerm::new(
                "constant_extension_preserves_soundness",
                "fun (env : KEnv) (env' : KEnv) (h_ext : ConstantExtension env env') (h_sound : EnvSound env) => constant_extension_preserves_soundness env env' h_ext h_sound",
                "One-step soundness for constant environment extensions.",
            ),
        );

        self.proofs.insert(
            "inductive_extension_soundness".to_string(),
            ProofTerm::new(
                "inductive_extension_preserves_soundness",
                "fun (env : KEnv) (env' : KEnv) (h_ext : InductiveExtension env env') (h_sound : EnvSound env) => inductive_extension_preserves_soundness env env' h_ext h_sound",
                "One-step soundness for inductive environment extensions.",
            ),
        );

        self.proofs.insert(
            "definitional_extension_soundness".to_string(),
            ProofTerm::new(
                "definitional_extension_sound",
                "definitional_extension_sound",
                "Definitional extensions preserve EnvSound across constant and inductive environment growth.",
            ),
        );
    }

    // Forward simulation proofs (add_forward_simulation_proofs) and
    // implementation soundness bridge proofs (add_implementation_soundness_proofs)
    // are in library_simulation.rs (#461).
}
