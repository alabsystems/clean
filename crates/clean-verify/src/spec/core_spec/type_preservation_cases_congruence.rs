// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Congruence type preservation forward/inverse proofs (app/lam/pi × 2).
//! Split from type_preservation_cases.rs.
//! Part of #464: Phase 4A constructive derivation.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the 6 congruence type preservation proofs (app/lam/pi × fwd/inv).
    ///
    /// Pi congruence (fwd/inv) is DerivedProved with no axiom_deps.
    /// App and lam congruence (fwd/inv) reconstruct the result type via the
    /// untyped `Typing.conv` rule (Brick 9: rerouted off the FALSE def_eq_to_eq
    /// bridge). The app cases are DerivedProved: their only formerly-pending
    /// dependency, `def_eq_instantiate_arg_congr`, graduated with the proved
    /// `def_eq_instantiate_arg_congr_at` leaf (#3221). The lam cases are kept
    /// conservatively DerivedPending (their declared status is pinned by the
    /// provenance gate). They are consumed by `def_eq_typing_iff` in
    /// `type_preservation_cases.rs`.
    pub(super) fn add_type_preservation_cases_congruence(&mut self) -> Result<(), SpecError> {
        // Type preservation for application congruence (forward)
        // Brick 9: the app-case result type is transported by the untyped
        // Typing.conv rule applied directly to the subst-respecting DefEq
        // (Typing e A -> DefEq A B -> Typing e B), no Eq.substType/def_eq_to_eq
        // detour. DerivedProved: def_eq_instantiate_arg_congr (the DefEq it
        // feeds Typing.conv) graduated once instantiate_bvar_at_arg_congr was
        // rerouted off def_eq_to_eq and the def_eq_instantiate_arg_congr_at
        // KExpr.rec leaf was proved (#3221); every other dep was already proved.
        // Part of #464: Phase 4A constructive derivation.
        self.add_definition(SpecDefinition {
            name: "app_type_preservation".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (T : KExpr), ",
                "has_type (KExpr.app f a) T -> ",
                "DefEq a a' -> ",
                "(forall (U : KExpr), has_type f U -> has_type f' U) -> ",
                "(forall (U : KExpr), has_type a U -> has_type a' U) -> ",
                "has_type (KExpr.app f' a') T"
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (hf : RedEnvFaithful the_red_env) ",
                "(f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (T : KExpr) ",
                "(h : has_type (KExpr.app f a) T) ",
                "(defEqAA : DefEq a a') ",
                "(trF : forall (U : KExpr), has_type f U -> has_type f' U) ",
                "(trA : forall (U : KExpr), has_type a U -> has_type a' U) => ",
                "Typing.rec ",
                "(fun (e : KExpr) (T0 : KExpr) (_h0 : Typing e T0) => ",
                "Eq KExpr e (KExpr.app f a) -> Typing (KExpr.app f' a') T0) ",
                // sort case: impossible (Sort n ≠ App f a)
                "(fun (n : Level) (eq : Eq KExpr (KExpr.sort n) (KExpr.app f a)) => ",
                "sort_ne_app n f a (Typing (KExpr.app f' a') (KExpr.sort (Level.succ n))) eq) ",
                // pi case: impossible (Pi A0 B0 ≠ App f a)
                "(fun (A0 : KExpr) (B0 : KExpr) (n : Level) (m : Level) ",
                "(_hA : Typing A0 (KExpr.sort n)) (_hB : Typing B0 (KExpr.sort m)) ",
                "(_ihA : Eq KExpr A0 (KExpr.app f a) -> Typing (KExpr.app f' a') (KExpr.sort n)) ",
                "(_ihB : Eq KExpr B0 (KExpr.app f a) -> Typing (KExpr.app f' a') (KExpr.sort m)) ",
                "(eq : Eq KExpr (KExpr.pi A0 B0) (KExpr.app f a)) => ",
                "pi_ne_app A0 B0 f a (Typing (KExpr.app f' a') (KExpr.sort (Level.imax n m))) eq) ",
                // lam case: impossible (Lam A0 b0 ≠ App f a)
                // Part of #2870: binder domain universe generalized from Nat.zero to _u0
                "(fun (A0 : KExpr) (b0 : KExpr) (B0 : KExpr) (_u0 : Level) ",
                "(_hA : Typing A0 (KExpr.sort _u0)) (_hb : Typing b0 B0) ",
                "(_ihA : Eq KExpr A0 (KExpr.app f a) -> Typing (KExpr.app f' a') (KExpr.sort _u0)) ",
                "(_ihb : Eq KExpr b0 (KExpr.app f a) -> Typing (KExpr.app f' a') B0) ",
                "(eq : Eq KExpr (KExpr.lam A0 b0) (KExpr.app f a)) => ",
                "lam_ne_app A0 b0 f a (Typing (KExpr.app f' a') (KExpr.pi A0 B0)) eq) ",
                // app case: PRODUCTIVE — reconstruct with Typing.conv bridge
                // Typing.app f' a' gives type (instantiate B0 a'). Motive needs
                // (instantiate B0 a0). Bridge: DefEq from a' to a (via arg_congr),
                // then Eq from a to a0 (via injectivity + Eq.cong).
                "(fun (f0 : KExpr) (a0 : KExpr) (A0 : KExpr) (B0 : KExpr) ",
                "(hf0 : Typing f0 (KExpr.pi A0 B0)) (ha0 : Typing a0 A0) ",
                "(_ihf : Eq KExpr f0 (KExpr.app f a) -> Typing (KExpr.app f' a') (KExpr.pi A0 B0)) ",
                "(_iha : Eq KExpr a0 (KExpr.app f a) -> Typing (KExpr.app f' a') A0) ",
                "(eq : Eq KExpr (KExpr.app f0 a0) (KExpr.app f a)) => ",
                "Typing.conv (KExpr.app f' a') ",
                "(instantiate B0 a') (instantiate B0 a0) ",
                "(Typing.app f' a' A0 B0 ",
                "(trF (KExpr.pi A0 B0) ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.pi A0 B0)) f0 f ",
                "(app_inj_fst f0 a0 f a eq) hf0)) ",
                "(trA A0 ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x A0) a0 a ",
                "(app_inj_snd f0 a0 f a eq) ha0))) ",
                "(def_eq_eq_right ",
                "(instantiate B0 a') (instantiate B0 a) (instantiate B0 a0) ",
                "(def_eq_instantiate_arg_congr B0 a' a hf (DefEq.symm a a' defEqAA)) ",
                "(Eq.symm KExpr (instantiate B0 a0) (instantiate B0 a) ",
                "(Eq.cong KExpr KExpr (fun (v : KExpr) => instantiate B0 v) a0 a ",
                "(app_inj_snd f0 a0 f a eq))))) ",
                // conv case: chain via Typing.conv
                "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                "(_he : Typing e0 T1) (eq_t : DefEq T1 T2) ",
                "(ih_e : Eq KExpr e0 (KExpr.app f a) -> Typing (KExpr.app f' a') T1) ",
                "(eq : Eq KExpr e0 (KExpr.app f a)) => ",
                "Typing.conv (KExpr.app f' a') T1 T2 (ih_e eq) eq_t) ",
                "(KExpr.app f a) T h (Eq.refl KExpr (KExpr.app f a))"
            ).to_string()),
            is_axiom: false,
            description: concat!(
                "Application type preservation: congruence preserves typing. ",
                "DerivedProved via Typing.rec + the untyped Typing.conv rule using ",
                "def_eq_instantiate_arg_congr for the dependent Typing.app result type ",
                "(Brick 9: rerouted off def_eq_to_eq; def_eq_instantiate_arg_congr ",
                "graduated with the proved def_eq_instantiate_arg_congr_at leaf, #3221). ",
                "Part of #464."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Typing.app".to_string(),
                "Typing.conv".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "Eq.symm".to_string(),
                "Eq.cong".to_string(),
                "DefEq.symm".to_string(),
                "def_eq_eq_right".to_string(),
                "sort_ne_app".to_string(),
                "pi_ne_app".to_string(),
                "lam_ne_app".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
                "def_eq_instantiate_arg_congr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Type preservation for lambda congruence (forward)
        // DerivedPending via Typing.rec with Eq-constraint motive + KExpr discrimination.
        // Motive: P(e, T, _) = Eq KExpr e (Lam A b) -> Typing (Lam A' b') T
        //
        // KEY: Typing.lam A b B produces type Pi A B. Changing A to A' gives Pi A' B,
        // which doesn't match the motive's T0 = Pi A0 B0 (where A0 = A via injectivity).
        // Brick 9: the untyped Typing.conv rule transports Pi A' B0 to Pi A0 B0
        // directly on the DefEq.pi_cong witness (no def_eq_to_eq / Eq.substType).
        // Part of #464: Phase 4A constructive derivation.
        self.add_definition(SpecDefinition {
            name: "lam_type_preservation".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (T : KExpr), ",
                "has_type (KExpr.lam A b) T -> ",
                "DefEq A A' -> ",
                "(forall (U : KExpr), has_type A U -> has_type A' U) -> ",
                "(forall (U : KExpr), has_type b U -> has_type b' U) -> ",
                "has_type (KExpr.lam A' b') T"
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (T : KExpr) ",
                "(h : has_type (KExpr.lam A b) T) ",
                "(defEqAA : DefEq A A') ",
                "(trA : forall (U : KExpr), has_type A U -> has_type A' U) ",
                "(trB : forall (U : KExpr), has_type b U -> has_type b' U) => ",
                "Typing.rec ",
                "(fun (e : KExpr) (T0 : KExpr) (_h0 : Typing e T0) => ",
                "Eq KExpr e (KExpr.lam A b) -> Typing (KExpr.lam A' b') T0) ",
                // sort case: impossible (Sort n ≠ Lam A b)
                "(fun (n : Level) (eq : Eq KExpr (KExpr.sort n) (KExpr.lam A b)) => ",
                "sort_ne_lam n A b (Typing (KExpr.lam A' b') (KExpr.sort (Level.succ n))) eq) ",
                // pi case: impossible (Pi A0 B0 ≠ Lam A b)
                "(fun (A0 : KExpr) (B0 : KExpr) (n : Level) (m : Level) ",
                "(_hA : Typing A0 (KExpr.sort n)) (_hB : Typing B0 (KExpr.sort m)) ",
                "(_ihA : Eq KExpr A0 (KExpr.lam A b) -> Typing (KExpr.lam A' b') (KExpr.sort n)) ",
                "(_ihB : Eq KExpr B0 (KExpr.lam A b) -> Typing (KExpr.lam A' b') (KExpr.sort m)) ",
                "(eq : Eq KExpr (KExpr.pi A0 B0) (KExpr.lam A b)) => ",
                "pi_ne_lam A0 B0 A b (Typing (KExpr.lam A' b') (KExpr.sort (Level.imax n m))) eq) ",
                // lam case: productive — reconstruct with Typing.conv bridge
                // Part of #2870: binder domain universe generalized from Nat.zero to u0
                "(fun (A0 : KExpr) (b0 : KExpr) (B0 : KExpr) (u0 : Level) ",
                "(hA0 : Typing A0 (KExpr.sort u0)) (hb0 : Typing b0 B0) ",
                "(_ihA : Eq KExpr A0 (KExpr.lam A b) -> Typing (KExpr.lam A' b') (KExpr.sort u0)) ",
                "(_ihb : Eq KExpr b0 (KExpr.lam A b) -> Typing (KExpr.lam A' b') B0) ",
                "(eq : Eq KExpr (KExpr.lam A0 b0) (KExpr.lam A b)) => ",
                // Typing.lam A' b' B0 u0 hA' hb' : Typing (Lam A' b') (Pi A' B0)
                // Need: Typing (Lam A' b') (Pi A0 B0), bridge via Typing.conv
                "Typing.conv (KExpr.lam A' b') ",
                "(KExpr.pi A' B0) (KExpr.pi A0 B0) ",
                "(Typing.lam A' b' B0 u0 ",
                "(trA (KExpr.sort u0) ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.sort u0)) A0 A ",
                "(lam_inj_fst A0 b0 A b eq) hA0)) ",
                "(trB B0 ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x B0) b0 b ",
                "(lam_inj_snd A0 b0 A b eq) hb0))) ",
                "(DefEq.pi_cong A' A0 B0 B0 ",
                "(Eq.substType KExpr (fun (x : KExpr) => DefEq A' x) A A0 ",
                "(Eq.symm KExpr A0 A (lam_inj_fst A0 b0 A b eq)) ",
                "(DefEq.symm A A' defEqAA)) ",
                "(DefEq.refl B0))) ",
                // app case: impossible (App g c ≠ Lam A b)
                "(fun (g : KExpr) (c : KExpr) (A0 : KExpr) (B0 : KExpr) ",
                "(_hg : Typing g (KExpr.pi A0 B0)) (_hc : Typing c A0) ",
                "(_ihg : Eq KExpr g (KExpr.lam A b) -> Typing (KExpr.lam A' b') (KExpr.pi A0 B0)) ",
                "(_ihc : Eq KExpr c (KExpr.lam A b) -> Typing (KExpr.lam A' b') A0) ",
                "(eq : Eq KExpr (KExpr.app g c) (KExpr.lam A b)) => ",
                "app_ne_lam g c A b (Typing (KExpr.lam A' b') (instantiate B0 c)) eq) ",
                // conv case: chain via Typing.conv
                "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                "(_he : Typing e0 T1) (eq_t : DefEq T1 T2) ",
                "(ih_e : Eq KExpr e0 (KExpr.lam A b) -> Typing (KExpr.lam A' b') T1) ",
                "(eq : Eq KExpr e0 (KExpr.lam A b)) => ",
                "Typing.conv (KExpr.lam A' b') T1 T2 (ih_e eq) eq_t) ",
                "(KExpr.lam A b) T h (Eq.refl KExpr (KExpr.lam A b))"
            ).to_string()),
            is_axiom: false,
            description: "Lambda type preservation: congruence preserves typing. Via Typing.rec + the untyped Typing.conv rule (DefEq on domain needed because Typing.lam embeds A in Pi A B); Brick 9 rerouted it off def_eq_to_eq, so the proof term is now def_eq_to_eq-free. Kept DerivedPending (status pinned by the provenance gate). Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Typing.lam".to_string(),
                "Typing.conv".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "Eq.symm".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.pi_cong".to_string(),
                "sort_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "app_ne_lam".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Type preservation for pi congruence (forward)
        // DerivedProved via Typing.rec with Eq-constraint motive + KExpr discrimination.
        // Motive: P(e, T, _) = Eq KExpr e (Pi A B) -> Typing (Pi A' B') T
        // Pi result type is Sort (imax_nat n m), but it is still reconstructed
        // directly from the transported sub-derivations, so no extra DefEq bridge is needed.
        // Part of #464: Phase 4A constructive derivation.
        self.add_definition(SpecDefinition {
            name: "pi_type_preservation".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) (T : KExpr), ",
                "has_type (KExpr.pi A B) T -> ",
                "(forall (U : KExpr), has_type A U -> has_type A' U) -> ",
                "(forall (U : KExpr), has_type B U -> has_type B' U) -> ",
                "has_type (KExpr.pi A' B') T"
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) (T : KExpr) ",
                "(h : has_type (KExpr.pi A B) T) ",
                "(trA : forall (U : KExpr), has_type A U -> has_type A' U) ",
                "(trB : forall (U : KExpr), has_type B U -> has_type B' U) => ",
                "Typing.rec ",
                "(fun (e : KExpr) (T0 : KExpr) (_h0 : Typing e T0) => ",
                "Eq KExpr e (KExpr.pi A B) -> Typing (KExpr.pi A' B') T0) ",
                // sort case: impossible (Sort n ≠ Pi A B)
                "(fun (n : Level) (eq : Eq KExpr (KExpr.sort n) (KExpr.pi A B)) => ",
                "sort_ne_pi n A B (Typing (KExpr.pi A' B') (KExpr.sort (Level.succ n))) eq) ",
                // pi case: productive — reconstruct with transported sub-derivations
                "(fun (A0 : KExpr) (B0 : KExpr) (n : Level) (m : Level) ",
                "(hA0 : Typing A0 (KExpr.sort n)) (hB0 : Typing B0 (KExpr.sort m)) ",
                "(_ihA : Eq KExpr A0 (KExpr.pi A B) -> Typing (KExpr.pi A' B') (KExpr.sort n)) ",
                "(_ihB : Eq KExpr B0 (KExpr.pi A B) -> Typing (KExpr.pi A' B') (KExpr.sort m)) ",
                "(eq : Eq KExpr (KExpr.pi A0 B0) (KExpr.pi A B)) => ",
                "Typing.pi A' B' n m ",
                "(trA (KExpr.sort n) ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.sort n)) A0 A ",
                "(pi_inj_fst A0 B0 A B eq) hA0)) ",
                "(trB (KExpr.sort m) ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.sort m)) B0 B ",
                "(pi_inj_snd A0 B0 A B eq) hB0))) ",
                // lam case: impossible (Lam A0 b0 ≠ Pi A B)
                // Part of #2870: binder domain universe generalized from Nat.zero to _u0
                "(fun (A0 : KExpr) (b0 : KExpr) (B0 : KExpr) (_u0 : Level) ",
                "(_hA : Typing A0 (KExpr.sort _u0)) (_hb : Typing b0 B0) ",
                "(_ihA : Eq KExpr A0 (KExpr.pi A B) -> Typing (KExpr.pi A' B') (KExpr.sort _u0)) ",
                "(_ihb : Eq KExpr b0 (KExpr.pi A B) -> Typing (KExpr.pi A' B') B0) ",
                "(eq : Eq KExpr (KExpr.lam A0 b0) (KExpr.pi A B)) => ",
                "lam_ne_pi A0 b0 A B (Typing (KExpr.pi A' B') (KExpr.pi A0 B0)) eq) ",
                // app case: impossible (App g c ≠ Pi A B)
                "(fun (g : KExpr) (c : KExpr) (A0 : KExpr) (B0 : KExpr) ",
                "(_hg : Typing g (KExpr.pi A0 B0)) (_hc : Typing c A0) ",
                "(_ihg : Eq KExpr g (KExpr.pi A B) -> Typing (KExpr.pi A' B') (KExpr.pi A0 B0)) ",
                "(_ihc : Eq KExpr c (KExpr.pi A B) -> Typing (KExpr.pi A' B') A0) ",
                "(eq : Eq KExpr (KExpr.app g c) (KExpr.pi A B)) => ",
                "app_ne_pi g c A B (Typing (KExpr.pi A' B') (instantiate B0 c)) eq) ",
                // conv case: chain via Typing.conv
                "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                "(_he : Typing e0 T1) (eq_t : DefEq T1 T2) ",
                "(ih_e : Eq KExpr e0 (KExpr.pi A B) -> Typing (KExpr.pi A' B') T1) ",
                "(eq : Eq KExpr e0 (KExpr.pi A B)) => ",
                "Typing.conv (KExpr.pi A' B') T1 T2 (ih_e eq) eq_t) ",
                "(KExpr.pi A B) T h (Eq.refl KExpr (KExpr.pi A B))"
            ).to_string()),
            is_axiom: false,
            description: "Pi type preservation: congruence preserves typing. DerivedProved via Typing.rec with Eq-constraint motive + KExpr discrimination. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Typing.pi".to_string(),
                "Typing.conv".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "sort_ne_pi".to_string(),
                "lam_ne_pi".to_string(),
                "app_ne_pi".to_string(),
                "pi_inj_fst".to_string(),
                "pi_inj_snd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Reverse type preservation for application congruence
        // Brick 9: result type transported by the untyped Typing.conv rule directly
        // on the def_eq_instantiate_arg_congr DefEq (no Eq.substType/def_eq_to_eq).
        // Same shape as forward: Typing.app f a A0 B0 gives (instantiate B0 a) but
        // the motive needs (instantiate B0 a0). DerivedProved: same graduation as
        // the forward case (def_eq_instantiate_arg_congr proved, #3221).
        // Part of #464: Phase 4A constructive derivation.
        self.add_definition(SpecDefinition {
            name: "app_type_preservation_inv".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (T : KExpr), ",
                "has_type (KExpr.app f' a') T -> ",
                "DefEq a a' -> ",
                "(forall (U : KExpr), has_type f' U -> has_type f U) -> ",
                "(forall (U : KExpr), has_type a' U -> has_type a U) -> ",
                "has_type (KExpr.app f a) T"
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (hf : RedEnvFaithful the_red_env) ",
                "(f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (T : KExpr) ",
                "(h : has_type (KExpr.app f' a') T) ",
                "(defEqAA : DefEq a a') ",
                "(trF : forall (U : KExpr), has_type f' U -> has_type f U) ",
                "(trA : forall (U : KExpr), has_type a' U -> has_type a U) => ",
                "Typing.rec ",
                "(fun (e : KExpr) (T0 : KExpr) (_h0 : Typing e T0) => ",
                "Eq KExpr e (KExpr.app f' a') -> Typing (KExpr.app f a) T0) ",
                // sort case: impossible (Sort n ≠ App f' a')
                "(fun (n : Level) (eq : Eq KExpr (KExpr.sort n) (KExpr.app f' a')) => ",
                "sort_ne_app n f' a' (Typing (KExpr.app f a) (KExpr.sort (Level.succ n))) eq) ",
                // pi case: impossible (Pi A0 B0 ≠ App f' a')
                "(fun (A0 : KExpr) (B0 : KExpr) (n : Level) (m : Level) ",
                "(_hA : Typing A0 (KExpr.sort n)) (_hB : Typing B0 (KExpr.sort m)) ",
                "(_ihA : Eq KExpr A0 (KExpr.app f' a') -> Typing (KExpr.app f a) (KExpr.sort n)) ",
                "(_ihB : Eq KExpr B0 (KExpr.app f' a') -> Typing (KExpr.app f a) (KExpr.sort m)) ",
                "(eq : Eq KExpr (KExpr.pi A0 B0) (KExpr.app f' a')) => ",
                "pi_ne_app A0 B0 f' a' (Typing (KExpr.app f a) (KExpr.sort (Level.imax n m))) eq) ",
                // lam case: impossible (Lam A0 b0 ≠ App f' a')
                // Part of #2870: binder domain universe generalized from Nat.zero to _u0
                "(fun (A0 : KExpr) (b0 : KExpr) (B0 : KExpr) (_u0 : Level) ",
                "(_hA : Typing A0 (KExpr.sort _u0)) (_hb : Typing b0 B0) ",
                "(_ihA : Eq KExpr A0 (KExpr.app f' a') -> Typing (KExpr.app f a) (KExpr.sort _u0)) ",
                "(_ihb : Eq KExpr b0 (KExpr.app f' a') -> Typing (KExpr.app f a) B0) ",
                "(eq : Eq KExpr (KExpr.lam A0 b0) (KExpr.app f' a')) => ",
                "lam_ne_app A0 b0 f' a' (Typing (KExpr.app f a) (KExpr.pi A0 B0)) eq) ",
                // app case: PRODUCTIVE — reconstruct with Typing.conv bridge
                // Typing.app f a gives type (instantiate B0 a). Motive needs
                // (instantiate B0 a0). Bridge: DefEq from a to a' (via arg_congr),
                // then Eq from a' to a0 (via injectivity + Eq.cong).
                "(fun (f0 : KExpr) (a0 : KExpr) (A0 : KExpr) (B0 : KExpr) ",
                "(hf0 : Typing f0 (KExpr.pi A0 B0)) (ha0 : Typing a0 A0) ",
                "(_ihf : Eq KExpr f0 (KExpr.app f' a') -> Typing (KExpr.app f a) (KExpr.pi A0 B0)) ",
                "(_iha : Eq KExpr a0 (KExpr.app f' a') -> Typing (KExpr.app f a) A0) ",
                "(eq : Eq KExpr (KExpr.app f0 a0) (KExpr.app f' a')) => ",
                "Typing.conv (KExpr.app f a) ",
                "(instantiate B0 a) (instantiate B0 a0) ",
                "(Typing.app f a A0 B0 ",
                "(trF (KExpr.pi A0 B0) ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.pi A0 B0)) f0 f' ",
                "(app_inj_fst f0 a0 f' a' eq) hf0)) ",
                "(trA A0 ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x A0) a0 a' ",
                "(app_inj_snd f0 a0 f' a' eq) ha0))) ",
                "(def_eq_eq_right ",
                "(instantiate B0 a) (instantiate B0 a') (instantiate B0 a0) ",
                "(def_eq_instantiate_arg_congr B0 a a' hf defEqAA) ",
                "(Eq.symm KExpr (instantiate B0 a0) (instantiate B0 a') ",
                "(Eq.cong KExpr KExpr (fun (v : KExpr) => instantiate B0 v) a0 a' ",
                "(app_inj_snd f0 a0 f' a' eq))))) ",
                // conv case: chain via Typing.conv
                "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                "(_he : Typing e0 T1) (eq_t : DefEq T1 T2) ",
                "(ih_e : Eq KExpr e0 (KExpr.app f' a') -> Typing (KExpr.app f a) T1) ",
                "(eq : Eq KExpr e0 (KExpr.app f' a')) => ",
                "Typing.conv (KExpr.app f a) T1 T2 (ih_e eq) eq_t) ",
                "(KExpr.app f' a') T h (Eq.refl KExpr (KExpr.app f' a'))"
            ).to_string()),
            is_axiom: false,
            description: concat!(
                "Application type preservation (reverse): congruence backwards ",
                "preserves typing. DerivedProved via Typing.rec + the untyped ",
                "Typing.conv rule using def_eq_instantiate_arg_congr for the dependent ",
                "Typing.app result type (Brick 9: rerouted off def_eq_to_eq; ",
                "def_eq_instantiate_arg_congr graduated with the proved ",
                "def_eq_instantiate_arg_congr_at leaf, #3221). Part of #464."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Typing.app".to_string(),
                "Typing.conv".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "Eq.symm".to_string(),
                "Eq.cong".to_string(),
                "DefEq.symm".to_string(),
                "def_eq_eq_right".to_string(),
                "sort_ne_app".to_string(),
                "pi_ne_app".to_string(),
                "lam_ne_app".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
                "def_eq_instantiate_arg_congr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Reverse type preservation for lambda congruence
        // DerivedPending via Typing.rec — same structure as lam_type_preservation
        // but operating on has_type (Lam A' b') T and reconstructing Lam A b.
        // Brick 9: result type transported by the untyped Typing.conv rule directly
        // on the DefEq.pi_cong witness (no def_eq_to_eq / Eq.substType detour).
        // Part of #464: Phase 4A constructive derivation.
        self.add_definition(SpecDefinition {
            name: "lam_type_preservation_inv".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (T : KExpr), ",
                "has_type (KExpr.lam A' b') T -> ",
                "DefEq A' A -> ",
                "(forall (U : KExpr), has_type A' U -> has_type A U) -> ",
                "(forall (U : KExpr), has_type b' U -> has_type b U) -> ",
                "has_type (KExpr.lam A b) T"
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (T : KExpr) ",
                "(h : has_type (KExpr.lam A' b') T) ",
                "(defEqA'A : DefEq A' A) ",
                "(trA : forall (U : KExpr), has_type A' U -> has_type A U) ",
                "(trB : forall (U : KExpr), has_type b' U -> has_type b U) => ",
                "Typing.rec ",
                "(fun (e : KExpr) (T0 : KExpr) (_h0 : Typing e T0) => ",
                "Eq KExpr e (KExpr.lam A' b') -> Typing (KExpr.lam A b) T0) ",
                // sort case: impossible
                "(fun (n : Level) (eq : Eq KExpr (KExpr.sort n) (KExpr.lam A' b')) => ",
                "sort_ne_lam n A' b' (Typing (KExpr.lam A b) (KExpr.sort (Level.succ n))) eq) ",
                // pi case: impossible
                "(fun (A0 : KExpr) (B0 : KExpr) (n : Level) (m : Level) ",
                "(_hA : Typing A0 (KExpr.sort n)) (_hB : Typing B0 (KExpr.sort m)) ",
                "(_ihA : Eq KExpr A0 (KExpr.lam A' b') -> Typing (KExpr.lam A b) (KExpr.sort n)) ",
                "(_ihB : Eq KExpr B0 (KExpr.lam A' b') -> Typing (KExpr.lam A b) (KExpr.sort m)) ",
                "(eq : Eq KExpr (KExpr.pi A0 B0) (KExpr.lam A' b')) => ",
                "pi_ne_lam A0 B0 A' b' (Typing (KExpr.lam A b) (KExpr.sort (Level.imax n m))) eq) ",
                // lam case: productive — reconstruct with Typing.conv bridge
                // Part of #2870: binder domain universe generalized from Nat.zero to u0
                "(fun (A0 : KExpr) (b0 : KExpr) (B0 : KExpr) (u0 : Level) ",
                "(hA0 : Typing A0 (KExpr.sort u0)) (hb0 : Typing b0 B0) ",
                "(_ihA : Eq KExpr A0 (KExpr.lam A' b') -> Typing (KExpr.lam A b) (KExpr.sort u0)) ",
                "(_ihb : Eq KExpr b0 (KExpr.lam A' b') -> Typing (KExpr.lam A b) B0) ",
                "(eq : Eq KExpr (KExpr.lam A0 b0) (KExpr.lam A' b')) => ",
                // Typing.lam A b B0 u0 hA hb : Typing (Lam A b) (Pi A B0)
                // Need: Typing (Lam A b) (Pi A0 B0), bridge via Typing.conv
                "Typing.conv (KExpr.lam A b) ",
                "(KExpr.pi A B0) (KExpr.pi A0 B0) ",
                "(Typing.lam A b B0 u0 ",
                "(trA (KExpr.sort u0) ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.sort u0)) A0 A' ",
                "(lam_inj_fst A0 b0 A' b' eq) hA0)) ",
                "(trB B0 ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x B0) b0 b' ",
                "(lam_inj_snd A0 b0 A' b' eq) hb0))) ",
                "(DefEq.pi_cong A A0 B0 B0 ",
                "(Eq.substType KExpr (fun (x : KExpr) => DefEq A x) A' A0 ",
                "(Eq.symm KExpr A0 A' (lam_inj_fst A0 b0 A' b' eq)) ",
                "(DefEq.symm A' A defEqA'A)) ",
                "(DefEq.refl B0))) ",
                // app case: impossible
                "(fun (g : KExpr) (c : KExpr) (A0 : KExpr) (B0 : KExpr) ",
                "(_hg : Typing g (KExpr.pi A0 B0)) (_hc : Typing c A0) ",
                "(_ihg : Eq KExpr g (KExpr.lam A' b') -> Typing (KExpr.lam A b) (KExpr.pi A0 B0)) ",
                "(_ihc : Eq KExpr c (KExpr.lam A' b') -> Typing (KExpr.lam A b) A0) ",
                "(eq : Eq KExpr (KExpr.app g c) (KExpr.lam A' b')) => ",
                "app_ne_lam g c A' b' (Typing (KExpr.lam A b) (instantiate B0 c)) eq) ",
                // conv case: chain
                "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                "(_he : Typing e0 T1) (eq_t : DefEq T1 T2) ",
                "(ih_e : Eq KExpr e0 (KExpr.lam A' b') -> Typing (KExpr.lam A b) T1) ",
                "(eq : Eq KExpr e0 (KExpr.lam A' b')) => ",
                "Typing.conv (KExpr.lam A b) T1 T2 (ih_e eq) eq_t) ",
                "(KExpr.lam A' b') T h (Eq.refl KExpr (KExpr.lam A' b'))"
            ).to_string()),
            is_axiom: false,
            description: "Lambda type preservation (reverse): congruence backwards preserves typing. Via Typing.rec + the untyped Typing.conv rule; Brick 9 rerouted it off def_eq_to_eq, so the proof term is now def_eq_to_eq-free. Kept DerivedPending (status pinned by the provenance gate). Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Typing.lam".to_string(),
                "Typing.conv".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "Eq.symm".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.pi_cong".to_string(),
                "sort_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "app_ne_lam".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Reverse type preservation for pi congruence
        // DerivedProved via Typing.rec — same structure as pi_type_preservation
        // but operating on has_type (Pi A' B') T and reconstructing Pi A B.
        // Part of #464: Phase 4A constructive derivation.
        self.add_definition(SpecDefinition {
            name: "pi_type_preservation_inv".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) (T : KExpr), ",
                "has_type (KExpr.pi A' B') T -> ",
                "(forall (U : KExpr), has_type A' U -> has_type A U) -> ",
                "(forall (U : KExpr), has_type B' U -> has_type B U) -> ",
                "has_type (KExpr.pi A B) T"
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) (T : KExpr) ",
                "(h : has_type (KExpr.pi A' B') T) ",
                "(trA : forall (U : KExpr), has_type A' U -> has_type A U) ",
                "(trB : forall (U : KExpr), has_type B' U -> has_type B U) => ",
                "Typing.rec ",
                "(fun (e : KExpr) (T0 : KExpr) (_h0 : Typing e T0) => ",
                "Eq KExpr e (KExpr.pi A' B') -> Typing (KExpr.pi A B) T0) ",
                // sort case: impossible
                "(fun (n : Level) (eq : Eq KExpr (KExpr.sort n) (KExpr.pi A' B')) => ",
                "sort_ne_pi n A' B' (Typing (KExpr.pi A B) (KExpr.sort (Level.succ n))) eq) ",
                // pi case: productive
                "(fun (A0 : KExpr) (B0 : KExpr) (n : Level) (m : Level) ",
                "(hA0 : Typing A0 (KExpr.sort n)) (hB0 : Typing B0 (KExpr.sort m)) ",
                "(_ihA : Eq KExpr A0 (KExpr.pi A' B') -> Typing (KExpr.pi A B) (KExpr.sort n)) ",
                "(_ihB : Eq KExpr B0 (KExpr.pi A' B') -> Typing (KExpr.pi A B) (KExpr.sort m)) ",
                "(eq : Eq KExpr (KExpr.pi A0 B0) (KExpr.pi A' B')) => ",
                "Typing.pi A B n m ",
                "(trA (KExpr.sort n) ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.sort n)) A0 A' ",
                "(pi_inj_fst A0 B0 A' B' eq) hA0)) ",
                "(trB (KExpr.sort m) ",
                "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.sort m)) B0 B' ",
                "(pi_inj_snd A0 B0 A' B' eq) hB0))) ",
                // lam case: impossible
                // Part of #2870: binder domain universe generalized from Nat.zero to _u0
                "(fun (A0 : KExpr) (b0 : KExpr) (B0 : KExpr) (_u0 : Level) ",
                "(_hA : Typing A0 (KExpr.sort _u0)) (_hb : Typing b0 B0) ",
                "(_ihA : Eq KExpr A0 (KExpr.pi A' B') -> Typing (KExpr.pi A B) (KExpr.sort _u0)) ",
                "(_ihb : Eq KExpr b0 (KExpr.pi A' B') -> Typing (KExpr.pi A B) B0) ",
                "(eq : Eq KExpr (KExpr.lam A0 b0) (KExpr.pi A' B')) => ",
                "lam_ne_pi A0 b0 A' B' (Typing (KExpr.pi A B) (KExpr.pi A0 B0)) eq) ",
                // app case: impossible
                "(fun (g : KExpr) (c : KExpr) (A0 : KExpr) (B0 : KExpr) ",
                "(_hg : Typing g (KExpr.pi A0 B0)) (_hc : Typing c A0) ",
                "(_ihg : Eq KExpr g (KExpr.pi A' B') -> Typing (KExpr.pi A B) (KExpr.pi A0 B0)) ",
                "(_ihc : Eq KExpr c (KExpr.pi A' B') -> Typing (KExpr.pi A B) A0) ",
                "(eq : Eq KExpr (KExpr.app g c) (KExpr.pi A' B')) => ",
                "app_ne_pi g c A' B' (Typing (KExpr.pi A B) (instantiate B0 c)) eq) ",
                // conv case: chain
                "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                "(_he : Typing e0 T1) (eq_t : DefEq T1 T2) ",
                "(ih_e : Eq KExpr e0 (KExpr.pi A' B') -> Typing (KExpr.pi A B) T1) ",
                "(eq : Eq KExpr e0 (KExpr.pi A' B')) => ",
                "Typing.conv (KExpr.pi A B) T1 T2 (ih_e eq) eq_t) ",
                "(KExpr.pi A' B') T h (Eq.refl KExpr (KExpr.pi A' B'))"
            ).to_string()),
            is_axiom: false,
            description: "Pi type preservation (reverse): congruence backwards preserves typing. DerivedProved via Typing.rec. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Typing.pi".to_string(),
                "Typing.conv".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "sort_ne_pi".to_string(),
                "lam_ne_pi".to_string(),
                "app_ne_pi".to_string(),
                "pi_inj_fst".to_string(),
                "pi_inj_snd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
