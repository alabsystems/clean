// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Typing generation lemmas (Sort/Pi/Lam) for typing_same_term_types_def_eq.
//! CPS-encoded (Pi/Lam) or direct (Sort). DerivedProved, no axiom deps.
//! Part of #461, #464. Design: designs/2026-03-18-464-typing-uniqueness-derivation.md

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// Sort injectivity extractor: (fun (e : KExpr) => KExpr.rec ... e)
// Inlined in typing_sort_gen proof term since concat!() requires literals.

impl Specification {
    /// Register typing generation lemmas.
    ///
    /// Must be called after typing_def_eq (Typing.rec) and discrimination
    /// lemmas, but before type_preservation_cases (typing_same_term_types_def_eq).
    pub(super) fn add_type_preservation_generation(&mut self) -> Result<(), SpecError> {
        self.add_typing_sort_gen()?;
        self.add_typing_pi_gen()?;
        self.add_typing_lam_gen()?;
        self.add_typing_app_gen()?;
        Ok(())
    }

    /// typing_sort_gen: Typing (Sort n) T → DefEq T (Sort (n+1)).
    /// Proof: Typing.rec, sort injectivity via KExpr.rec, discrimination.
    fn add_typing_sort_gen(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "typing_sort_gen".to_string(),
            type_src: concat!(
                "forall (n : Level) (T : KExpr), ",
                "Typing (KExpr.sort n) T -> ",
                "DefEq T (KExpr.sort (Level.succ n))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Level) (T : KExpr) (h : Typing (KExpr.sort n) T) => ",
                    "Typing.rec ",
                    // Motive: P(e, T, _) = ∀ n, e = Sort n → DefEq T (Sort (succ n))
                    "(fun (e : KExpr) (T0 : KExpr) (_ : Typing e T0) => ",
                    "forall (n : Level), Eq KExpr e (KExpr.sort n) -> DefEq T0 (KExpr.sort (Level.succ n))) ",
                    // sort case: e = Sort m, T = Sort (succ m)
                    // Given: Sort m = Sort n. Need: DefEq (Sort (succ m)) (Sort (succ n)).
                    // Via sort injectivity (inline KExpr.rec) + Eq.cong + Eq.substType + DefEq.refl.
                    "(fun (m : Level) (n0 : Level) (eq : Eq KExpr (KExpr.sort m) (KExpr.sort n0)) => ",
                    "Eq.substType KExpr ",
                    "(fun (x : KExpr) => DefEq (KExpr.sort (Level.succ m)) x) ",
                    "(KExpr.sort (Level.succ m)) ",
                    "(KExpr.sort (Level.succ n0)) ",
                    "(Eq.cong Level KExpr (fun (k : Level) => KExpr.sort (Level.succ k)) m n0 ",
                    "(Eq.cong KExpr Level ",
                    "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => Level) ",
                    "(fun (k : Level) => k) ",
                    "(fun (_ : Nat) => m) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => m) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => m) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => m) ",
                    "(fun (_ : Name) (_ : ListType Level) => m) ",
                    // let_ minor (7th KExpr ctor: ty, val, body — 3 recursive fields + 3 IHs,
                    // all Level under the (fun (_ : KExpr) => Level) motive; not Sort so yields m)
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) (_ : Level) => m) ",
                    // proj minor (8th ctor: s:Name, i:Nat, sub:KExpr — 1 recursive field + 1 IH,
                    // Level under the motive; not Sort so yields m)
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Level) => m) ",
                    // lit minor (9th ctor: v:Nat — no recursive fields; not Sort so yields m)
                    "(fun (_ : Nat) => m) ",
                    "e) ",
                    "(KExpr.sort m) (KExpr.sort n0) eq)) ",
                    "(DefEq.refl (KExpr.sort (Level.succ m)))) ",
                    // pi case: Pi A B ≠ Sort n (via Eq.symm + sort_ne_pi)
                    "(fun (A1 : KExpr) (B1 : KExpr) (_n1 : Level) (m1 : Level) ",
                    "(_hA : Typing A1 (KExpr.sort _n1)) (_hB : Typing B1 (KExpr.sort m1)) ",
                    "(_ihA : forall (n0 : Level), Eq KExpr A1 (KExpr.sort n0) -> DefEq (KExpr.sort _n1) (KExpr.sort (Level.succ n0))) ",
                    "(_ihB : forall (n0 : Level), Eq KExpr B1 (KExpr.sort n0) -> DefEq (KExpr.sort m1) (KExpr.sort (Level.succ n0))) ",
                    "(n0 : Level) (eq : Eq KExpr (KExpr.pi A1 B1) (KExpr.sort n0)) => ",
                    "sort_ne_pi n0 A1 B1 (DefEq (KExpr.sort (Level.imax _n1 m1)) (KExpr.sort (Level.succ n0))) ",
                    "(Eq.symm KExpr (KExpr.pi A1 B1) (KExpr.sort n0) eq)) ",
                    // lam case: Lam A b ≠ Sort n (via Eq.symm + sort_ne_lam)
                    // Part of #2870: binder domain universe generalized from Nat.zero to _u2
                    "(fun (A2 : KExpr) (b2 : KExpr) (B2 : KExpr) (_u2 : Level) ",
                    "(_hA : Typing A2 (KExpr.sort _u2)) (_hb : Typing b2 B2) ",
                    "(_ihA : forall (n0 : Level), Eq KExpr A2 (KExpr.sort n0) -> DefEq (KExpr.sort _u2) (KExpr.sort (Level.succ n0))) ",
                    "(_ihb : forall (n0 : Level), Eq KExpr b2 (KExpr.sort n0) -> DefEq B2 (KExpr.sort (Level.succ n0))) ",
                    "(n0 : Level) (eq : Eq KExpr (KExpr.lam A2 b2) (KExpr.sort n0)) => ",
                    "sort_ne_lam n0 A2 b2 (DefEq (KExpr.pi A2 B2) (KExpr.sort (Level.succ n0))) ",
                    "(Eq.symm KExpr (KExpr.lam A2 b2) (KExpr.sort n0) eq)) ",
                    // app case: App f a ≠ Sort n (via Eq.symm + sort_ne_app)
                    "(fun (f : KExpr) (a : KExpr) (A2 : KExpr) (B2 : KExpr) ",
                    "(_hf : Typing f (KExpr.pi A2 B2)) (_ha : Typing a A2) ",
                    "(_ihf : forall (n0 : Level), Eq KExpr f (KExpr.sort n0) -> DefEq (KExpr.pi A2 B2) (KExpr.sort (Level.succ n0))) ",
                    "(_iha : forall (n0 : Level), Eq KExpr a (KExpr.sort n0) -> DefEq A2 (KExpr.sort (Level.succ n0))) ",
                    "(n0 : Level) (eq : Eq KExpr (KExpr.app f a) (KExpr.sort n0)) => ",
                    "sort_ne_app n0 f a (DefEq (instantiate B2 a) (KExpr.sort (Level.succ n0))) ",
                    "(Eq.symm KExpr (KExpr.app f a) (KExpr.sort n0) eq)) ",
                    // conv case: compose via DefEq.trans
                    "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                    "(_he : Typing e0 T1) (deq : DefEq T1 T2) ",
                    "(ih : forall (n0 : Level), Eq KExpr e0 (KExpr.sort n0) -> DefEq T1 (KExpr.sort (Level.succ n0))) ",
                    "(n0 : Level) (eq : Eq KExpr e0 (KExpr.sort n0)) => ",
                    "DefEq.trans T2 T1 (KExpr.sort (Level.succ n0)) ",
                    "(DefEq.symm T1 T2 deq) (ih n0 eq)) ",
                    // Apply Typing.rec
                    "(KExpr.sort n) T h n (Eq.refl KExpr (KExpr.sort n))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Sort generation lemma: if Sort n : T, then DefEq T (Sort (n+1)). ",
                "DerivedProved via Typing.rec + inline sort injectivity + discrimination. ",
                "Part of #461, #464."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "KExpr.rec".to_string(),
                "Eq.cong".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "typed_def_eq_to_def_eq".to_string(),
                "sort_ne_pi".to_string(),
                "sort_ne_lam".to_string(),
                "sort_ne_app".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// typing_pi_gen: Typing (Pi A B) T → CPS with (n, m, A:Sort n, B:Sort m, DefEq T (Sort (imax n m))).
    /// Part of #2870: CPS now exposes both domain and codomain universe levels.
    fn add_typing_pi_gen(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "typing_pi_gen".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (B : KExpr) (T : KExpr) (R : Type), ",
                "Typing (KExpr.pi A B) T -> ",
                "(forall (n : Level) (m : Level), Typing A (KExpr.sort n) -> ",
                "Typing B (KExpr.sort m) -> DefEq T (KExpr.sort (Level.imax n m)) -> R) -> ",
                "R"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (B : KExpr) (T : KExpr) (R : Type) ",
                    "(h : Typing (KExpr.pi A B) T) ",
                    "(k : forall (n : Level) (m : Level), Typing A (KExpr.sort n) -> ",
                    "Typing B (KExpr.sort m) -> DefEq T (KExpr.sort (Level.imax n m)) -> R) => ",
                    "Typing.rec ",
                    // Motive: Q(e, T, _) = ∀ A0 B0, e = Pi A0 B0 →
                    //   (∀ n m, Typing A0 (Sort n) → Typing B0 (Sort m) → DefEq T (Sort (imax n m)) → R) → R
                    "(fun (e : KExpr) (T0 : KExpr) (_ : Typing e T0) => ",
                    "forall (A0 : KExpr) (B0 : KExpr), ",
                    "Eq KExpr e (KExpr.pi A0 B0) -> ",
                    "(forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq T0 (KExpr.sort (Level.imax n m)) -> R) -> R) ",
                    // sort case: Sort n ≠ Pi
                    "(fun (n : Level) (A0 : KExpr) (B0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.sort n) (KExpr.pi A0 B0)) ",
                    "(_ : forall (n0 : Level) (m : Level), Typing A0 (KExpr.sort n0) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq (KExpr.sort (Level.succ n)) (KExpr.sort (Level.imax n0 m)) -> R) => ",
                    "sort_ne_pi n A0 B0 R eq) ",
                    // pi case: PRODUCTIVE — extract domain and body typing
                    // Part of #2870: now provides both hA and hB to the continuation
                    "(fun (A1 : KExpr) (B1 : KExpr) (n1 : Level) (m1 : Level) ",
                    "(hA : Typing A1 (KExpr.sort n1)) (hB : Typing B1 (KExpr.sort m1)) ",
                    "(_ihA : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr A1 (KExpr.pi A0 B0) -> ",
                    "(forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq (KExpr.sort n1) (KExpr.sort (Level.imax n m)) -> R) -> R) ",
                    "(_ihB : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr B1 (KExpr.pi A0 B0) -> ",
                    "(forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq (KExpr.sort m1) (KExpr.sort (Level.imax n m)) -> R) -> R) ",
                    "(A0 : KExpr) (B0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.pi A1 B1) (KExpr.pi A0 B0)) ",
                    "(k0 : forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq (KExpr.sort (Level.imax n1 m1)) (KExpr.sort (Level.imax n m)) -> R) => ",
                    "k0 n1 m1 ",
                    "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.sort n1)) A1 A0 ",
                    "(pi_inj_fst A1 B1 A0 B0 eq) hA) ",
                    "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.sort m1)) B1 B0 ",
                    "(pi_inj_snd A1 B1 A0 B0 eq) hB) ",
                    "(DefEq.refl (KExpr.sort (Level.imax n1 m1)))) ",
                    // lam case: Lam ≠ Pi (via lam_ne_pi)
                    // Part of #2870: binder domain universe generalized from Nat.zero to _u2
                    "(fun (A2 : KExpr) (b2 : KExpr) (B2 : KExpr) (_u2 : Level) ",
                    "(_hA : Typing A2 (KExpr.sort _u2)) (_hb : Typing b2 B2) ",
                    "(_ihA : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr A2 (KExpr.pi A0 B0) -> ",
                    "(forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq (KExpr.sort _u2) (KExpr.sort (Level.imax n m)) -> R) -> R) ",
                    "(_ihb : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr b2 (KExpr.pi A0 B0) -> ",
                    "(forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq B2 (KExpr.sort (Level.imax n m)) -> R) -> R) ",
                    "(A0 : KExpr) (B0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.lam A2 b2) (KExpr.pi A0 B0)) ",
                    "(_ : forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq (KExpr.pi A2 B2) (KExpr.sort (Level.imax n m)) -> R) => ",
                    "lam_ne_pi A2 b2 A0 B0 R eq) ",
                    // app case: App ≠ Pi (via app_ne_pi)
                    "(fun (f : KExpr) (a : KExpr) (A2 : KExpr) (B2 : KExpr) ",
                    "(_hf : Typing f (KExpr.pi A2 B2)) (_ha : Typing a A2) ",
                    "(_ihf : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr f (KExpr.pi A0 B0) -> ",
                    "(forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq (KExpr.pi A2 B2) (KExpr.sort (Level.imax n m)) -> R) -> R) ",
                    "(_iha : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr a (KExpr.pi A0 B0) -> ",
                    "(forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq A2 (KExpr.sort (Level.imax n m)) -> R) -> R) ",
                    "(A0 : KExpr) (B0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.app f a) (KExpr.pi A0 B0)) ",
                    "(_ : forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq (instantiate B2 a) (KExpr.sort (Level.imax n m)) -> R) => ",
                    "app_ne_pi f a A0 B0 R eq) ",
                    // conv case: bridge T1 → T2
                    "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                    "(_he : Typing e0 T1) (deq : DefEq T1 T2) ",
                    "(ih : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr e0 (KExpr.pi A0 B0) -> ",
                    "(forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq T1 (KExpr.sort (Level.imax n m)) -> R) -> R) ",
                    "(A0 : KExpr) (B0 : KExpr) ",
                    "(eq : Eq KExpr e0 (KExpr.pi A0 B0)) ",
                    "(k0 : forall (n : Level) (m : Level), Typing A0 (KExpr.sort n) -> ",
                    "Typing B0 (KExpr.sort m) -> DefEq T2 (KExpr.sort (Level.imax n m)) -> R) => ",
                    "ih A0 B0 eq ",
                    "(fun (n : Level) (m : Level) (hAn : Typing A0 (KExpr.sort n)) ",
                    "(hBm : Typing B0 (KExpr.sort m)) ",
                    "(deq_T1 : DefEq T1 (KExpr.sort (Level.imax n m))) => ",
                    "k0 n m hAn hBm ",
                    "(DefEq.trans T2 T1 (KExpr.sort (Level.imax n m)) ",
                    "(DefEq.symm T1 T2 deq) deq_T1))) ",
                    // Apply Typing.rec
                    "(KExpr.pi A B) T h A B (Eq.refl KExpr (KExpr.pi A B)) k"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Pi generation lemma (CPS): if (Pi A B) : T, then ∃ n m with A : Sort n, ",
                "B : Sort m, and DefEq T (Sort (imax n m)). DerivedProved via Typing.rec + discrimination. ",
                "Part of #461, #464, #2870."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.substType".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "typed_def_eq_to_def_eq".to_string(),
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

    /// typing_lam_gen: Typing (Lam A b) T → CPS with (B, Typing b B, DefEq T (Pi A B)).
    fn add_typing_lam_gen(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "typing_lam_gen".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (b : KExpr) (T : KExpr) (R : Type), ",
                "Typing (KExpr.lam A b) T -> ",
                "(forall (B : KExpr), Typing b B -> DefEq T (KExpr.pi A B) -> R) -> ",
                "R"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (b : KExpr) (T : KExpr) (R : Type) ",
                    "(h : Typing (KExpr.lam A b) T) ",
                    "(k : forall (B : KExpr), Typing b B -> DefEq T (KExpr.pi A B) -> R) => ",
                    "Typing.rec ",
                    // Motive: Q(e, T, _) = ∀ A0 b0, e = Lam A0 b0 →
                    //   (∀ B, Typing b0 B → DefEq T (Pi A0 B) → R) → R
                    "(fun (e : KExpr) (T0 : KExpr) (_ : Typing e T0) => ",
                    "forall (A0 : KExpr) (b0 : KExpr), ",
                    "Eq KExpr e (KExpr.lam A0 b0) -> ",
                    "(forall (B : KExpr), Typing b0 B -> DefEq T0 (KExpr.pi A0 B) -> R) -> R) ",
                    // sort case: Sort ≠ Lam (via sort_ne_lam)
                    "(fun (n : Level) (A0 : KExpr) (b0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.sort n) (KExpr.lam A0 b0)) ",
                    "(_ : forall (B : KExpr), Typing b0 B -> DefEq (KExpr.sort (Level.succ n)) (KExpr.pi A0 B) -> R) => ",
                    "sort_ne_lam n A0 b0 R eq) ",
                    // pi case: Pi ≠ Lam (via pi_ne_lam)
                    "(fun (A1 : KExpr) (B1 : KExpr) (n1 : Level) (m1 : Level) ",
                    "(_hA : Typing A1 (KExpr.sort n1)) (_hB : Typing B1 (KExpr.sort m1)) ",
                    "(_ihA : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr A1 (KExpr.lam A0 b0) -> ",
                    "(forall (B : KExpr), Typing b0 B -> DefEq (KExpr.sort n1) (KExpr.pi A0 B) -> R) -> R) ",
                    "(_ihB : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr B1 (KExpr.lam A0 b0) -> ",
                    "(forall (B : KExpr), Typing b0 B -> DefEq (KExpr.sort m1) (KExpr.pi A0 B) -> R) -> R) ",
                    "(A0 : KExpr) (b0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.pi A1 B1) (KExpr.lam A0 b0)) ",
                    "(_ : forall (B : KExpr), Typing b0 B -> DefEq (KExpr.sort (Level.imax n1 m1)) (KExpr.pi A0 B) -> R) => ",
                    "pi_ne_lam A1 B1 A0 b0 R eq) ",
                    // lam case: PRODUCTIVE — extract body typing
                    // Part of #2870: binder domain universe generalized from Nat.zero to _u2
                    "(fun (A2 : KExpr) (b2 : KExpr) (B2 : KExpr) (_u2 : Level) ",
                    "(_hA : Typing A2 (KExpr.sort _u2)) (hb : Typing b2 B2) ",
                    "(_ihA : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr A2 (KExpr.lam A0 b0) -> ",
                    "(forall (B : KExpr), Typing b0 B -> DefEq (KExpr.sort _u2) (KExpr.pi A0 B) -> R) -> R) ",
                    "(_ihb : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr b2 (KExpr.lam A0 b0) -> ",
                    "(forall (B : KExpr), Typing b0 B -> DefEq B2 (KExpr.pi A0 B) -> R) -> R) ",
                    "(A0 : KExpr) (b0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.lam A2 b2) (KExpr.lam A0 b0)) ",
                    "(k0 : forall (B : KExpr), Typing b0 B -> DefEq (KExpr.pi A2 B2) (KExpr.pi A0 B) -> R) => ",
                    // From eq: lam_inj_fst gives A2 = A0, lam_inj_snd gives b2 = b0.
                    // Transport hb (Typing b2 B2) to Typing b0 B2.
                    // Build DefEq (Pi A2 B2) (Pi A0 B2) from A2 = A0.
                    "k0 B2 ",
                    "(Eq.substType KExpr (fun (x : KExpr) => Typing x B2) b2 b0 ",
                    "(lam_inj_snd A2 b2 A0 b0 eq) hb) ",
                    "(def_eq_eq_left (KExpr.pi A2 B2) (KExpr.pi A0 B2) (KExpr.pi A0 B2) ",
                    "(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi x B2) A2 A0 ",
                    "(lam_inj_fst A2 b2 A0 b0 eq)) ",
                    "(DefEq.refl (KExpr.pi A0 B2)))) ",
                    // app case: App ≠ Lam (via app_ne_lam)
                    "(fun (f : KExpr) (a : KExpr) (A2 : KExpr) (B2 : KExpr) ",
                    "(_hf : Typing f (KExpr.pi A2 B2)) (_ha : Typing a A2) ",
                    "(_ihf : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr f (KExpr.lam A0 b0) -> ",
                    "(forall (B : KExpr), Typing b0 B -> DefEq (KExpr.pi A2 B2) (KExpr.pi A0 B) -> R) -> R) ",
                    "(_iha : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr a (KExpr.lam A0 b0) -> ",
                    "(forall (B : KExpr), Typing b0 B -> DefEq A2 (KExpr.pi A0 B) -> R) -> R) ",
                    "(A0 : KExpr) (b0 : KExpr) ",
                    "(eq : Eq KExpr (KExpr.app f a) (KExpr.lam A0 b0)) ",
                    "(_ : forall (B : KExpr), Typing b0 B -> DefEq (instantiate B2 a) (KExpr.pi A0 B) -> R) => ",
                    "app_ne_lam f a A0 b0 R eq) ",
                    // conv case: bridge T1 → T2
                    "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                    "(_he : Typing e0 T1) (deq : DefEq T1 T2) ",
                    "(ih : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr e0 (KExpr.lam A0 b0) -> ",
                    "(forall (B : KExpr), Typing b0 B -> DefEq T1 (KExpr.pi A0 B) -> R) -> R) ",
                    "(A0 : KExpr) (b0 : KExpr) ",
                    "(eq : Eq KExpr e0 (KExpr.lam A0 b0)) ",
                    "(k0 : forall (B : KExpr), Typing b0 B -> DefEq T2 (KExpr.pi A0 B) -> R) => ",
                    "ih A0 b0 eq ",
                    "(fun (B : KExpr) (hbB : Typing b0 B) (deq_T1 : DefEq T1 (KExpr.pi A0 B)) => ",
                    "k0 B hbB (DefEq.trans T2 T1 (KExpr.pi A0 B) ",
                    "(DefEq.symm T1 T2 deq) deq_T1))) ",
                    // Apply Typing.rec
                    "(KExpr.lam A b) T h A b (Eq.refl KExpr (KExpr.lam A b)) k"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lam generation lemma (CPS): if (Lam A b) : T, then ∃ B with b : B ",
                "and DefEq T (Pi A B). DerivedProved via Typing.rec + discrimination. ",
                "Part of #461, #464."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "typed_def_eq_to_def_eq".to_string(),
                "def_eq_eq_left".to_string(),
                "sort_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "app_ne_lam".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }
}
