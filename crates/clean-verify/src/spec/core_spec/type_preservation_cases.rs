// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Typed conversion-lane case helpers and def_eq_typing_iff proof term.
//!
//! Split from type_preservation.rs. Contains:
//! - lam_typing_dom_sort: domain typing inversion (DerivedProved — no axiom deps)
//! - lam_typing_body_subst: inner lam inversion (DerivedPending via Typing.rec +
//!   pi_injectivity_def_eq + substitution_typing + def_eq_respects_subst)
//! - Beta preservation: DerivedPending via lam_typing_body_subst (promoted from HelperAxiom)
//! - Beta expansion: DerivedPending via Typing.lam/app reconstruction + type alignment leaf
//! - Congruence type preservation forward/inverse (app/lam/pi × 2 = 6 total;
//!   split into type_preservation_cases_congruence.rs — Part of #307)
//! - Delta/iota type preservation forward/backward (DerivedProved via #725
//!   reduction_witnesses.rs — previously 4 HelperAxioms, now 0)
//! - def_eq_typing_iff: bidirectional type preservation via TypedDefEq.rec (DerivedPending)
//!
//! Part of #464: Phase 4A constructive derivation.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register case helpers and the def_eq_typing_iff proof.
    ///
    /// All case helpers must be registered before def_eq_typing_iff because
    /// the spec validates that referenced identifiers in value_src are
    /// already registered.
    pub(super) fn add_type_preservation_cases(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // Lambda domain typing inversion (CPS): if lam A b : T, then ∃u. A : Sort u.
        // =========================================================
        // Part of #2870: CPS-encoded because the domain universe u is existential
        // (generalized from the hardcoded Nat.zero).
        // Proof by Typing.rec with motive:
        //   P(e, T, _) = ∀ A' b', e = lam A' b' → (∀ u, Typing A' (Sort u) → R) → R.
        // The sort/pi/app cases are vacuously true (discrimination).
        // The lam case calls the continuation with u and transported hA.
        // The conv case forwards the IH + continuation (term unchanged).
        // DerivedProved: only uses discrimination + lam_inj_fst + Eq.subst.
        // Part of #464: infrastructure for beta_preservation.
        self.add_definition(SpecDefinition {
            name: "lam_typing_dom_sort".to_string(),
            type_src: concat!(
                "forall (A_dom : KExpr) (body : KExpr) (T : KExpr) (R : Type), ",
                "Typing (KExpr.lam A_dom body) T -> ",
                "(forall (u : Level), Typing A_dom (KExpr.sort u) -> R) -> R"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (A_dom : KExpr) (body : KExpr) (T : KExpr) (R : Type) ",
                    "(hlam : Typing (KExpr.lam A_dom body) T) ",
                    "(k0 : forall (u : Level), Typing A_dom (KExpr.sort u) -> R) => ",
                    "Typing.rec ",
                    "(fun (e : KExpr) (T0 : KExpr) (_ : Typing e T0) => ",
                    "forall (A' : KExpr) (b' : KExpr), ",
                    "Eq KExpr e (KExpr.lam A' b') -> ",
                    "(forall (u : Level), Typing A' (KExpr.sort u) -> R) -> R) ",
                    // sort case: sort n ≠ lam
                    "(fun (n : Level) (A' : KExpr) (b' : KExpr) ",
                    "(eq : Eq KExpr (KExpr.sort n) (KExpr.lam A' b')) ",
                    "(_ : forall (u : Level), Typing A' (KExpr.sort u) -> R) => ",
                    "sort_ne_lam n A' b' R eq) ",
                    // pi case: pi ≠ lam
                    "(fun (A1 : KExpr) (B1 : KExpr) (n : Level) (m : Level) ",
                    "(_hA : Typing A1 (KExpr.sort n)) (_hB : Typing B1 (KExpr.sort m)) ",
                    "(_ihA : forall (A' : KExpr) (b' : KExpr), ",
                    "Eq KExpr A1 (KExpr.lam A' b') -> ",
                    "(forall (u : Level), Typing A' (KExpr.sort u) -> R) -> R) ",
                    "(_ihB : forall (A' : KExpr) (b' : KExpr), ",
                    "Eq KExpr B1 (KExpr.lam A' b') -> ",
                    "(forall (u : Level), Typing A' (KExpr.sort u) -> R) -> R) ",
                    "(A' : KExpr) (b' : KExpr) ",
                    "(eq : Eq KExpr (KExpr.pi A1 B1) (KExpr.lam A' b')) ",
                    "(_ : forall (u : Level), Typing A' (KExpr.sort u) -> R) => ",
                    "pi_ne_lam A1 B1 A' b' R eq) ",
                    // lam case: PRODUCTIVE — call continuation with u2 and transported hA
                    // Part of #2870: u2 is the existential domain universe
                    "(fun (A2 : KExpr) (b2 : KExpr) (B2 : KExpr) (u2 : Level) ",
                    "(hA2 : Typing A2 (KExpr.sort u2)) (_hb2 : Typing b2 B2) ",
                    "(_ihA2 : forall (A' : KExpr) (b' : KExpr), ",
                    "Eq KExpr A2 (KExpr.lam A' b') -> ",
                    "(forall (u : Level), Typing A' (KExpr.sort u) -> R) -> R) ",
                    "(_ihb2 : forall (A' : KExpr) (b' : KExpr), ",
                    "Eq KExpr b2 (KExpr.lam A' b') -> ",
                    "(forall (u : Level), Typing A' (KExpr.sort u) -> R) -> R) ",
                    "(A' : KExpr) (b' : KExpr) ",
                    "(eq : Eq KExpr (KExpr.lam A2 b2) (KExpr.lam A' b')) ",
                    "(k : forall (u : Level), Typing A' (KExpr.sort u) -> R) => ",
                    "k u2 (Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.sort u2)) ",
                    "A2 A' (lam_inj_fst A2 b2 A' b' eq) hA2)) ",
                    // app case: app ≠ lam
                    "(fun (f : KExpr) (a0 : KExpr) (A2 : KExpr) (B2 : KExpr) ",
                    "(_hf : Typing f (KExpr.pi A2 B2)) (_ha0 : Typing a0 A2) ",
                    "(_ihf : forall (A' : KExpr) (b' : KExpr), ",
                    "Eq KExpr f (KExpr.lam A' b') -> ",
                    "(forall (u : Level), Typing A' (KExpr.sort u) -> R) -> R) ",
                    "(_iha0 : forall (A' : KExpr) (b' : KExpr), ",
                    "Eq KExpr a0 (KExpr.lam A' b') -> ",
                    "(forall (u : Level), Typing A' (KExpr.sort u) -> R) -> R) ",
                    "(A' : KExpr) (b' : KExpr) ",
                    "(eq : Eq KExpr (KExpr.app f a0) (KExpr.lam A' b')) ",
                    "(_ : forall (u : Level), Typing A' (KExpr.sort u) -> R) => ",
                    "app_ne_lam f a0 A' b' R eq) ",
                    // conv case: forward IH + continuation (term unchanged)
                    "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                    "(_he : Typing e0 T1) (_deq : DefEq T1 T2) ",
                    "(ih : forall (A' : KExpr) (b' : KExpr), ",
                    "Eq KExpr e0 (KExpr.lam A' b') -> ",
                    "(forall (u : Level), Typing A' (KExpr.sort u) -> R) -> R) ",
                    "(A' : KExpr) (b' : KExpr) ",
                    "(eq : Eq KExpr e0 (KExpr.lam A' b')) ",
                    "(k : forall (u : Level), Typing A' (KExpr.sort u) -> R) => ",
                    "ih A' b' eq k) ",
                    // Apply Typing.rec to hlam with reflexivity witness + continuation
                    "(KExpr.lam A_dom body) T hlam ",
                    "A_dom body (Eq.refl KExpr (KExpr.lam A_dom body)) k0"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lambda domain typing inversion (CPS): if (λA.b) : T, then ∃u. A : Sort u. ",
                "Part of #2870: CPS-encoded because the domain universe is existential. ",
                "DerivedProved via Typing.rec with equality-accumulating motive. ",
                "Only uses discrimination lemmas and lam_inj_fst — no axiom deps. ",
                "Part of #464: infrastructure for beta_preservation."
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
                "sort_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "app_ne_lam".to_string(),
                "lam_inj_fst".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Lambda typing inversion: the inner Typing.rec needed by
        // beta_preservation. Factored out for clarity and reuse.
        // =========================================================
        // Given Typing (lam A b) (pi A0 B0) and Typing a A0, produces
        // Typing (instantiate b a) (instantiate B0 a). This is the
        // core inversion that extracts the body typing from a lambda
        // derivation and applies substitution_typing.
        //
        // The proof uses Typing.rec with a DefEq-accumulating motive
        // to handle conv chains: Q(e,T,_) = Eq e (lam A b) ->
        // DefEq T (pi A0 B0) -> Typing (instantiate b a) (instantiate B0 a).
        // The lam case uses pi_injectivity_def_eq to extract DefEq A A0
        // and DefEq B' B0, then bridges via substitution_typing +
        // Typing.conv + raw_to_typed_def_eq + def_eq_respects_subst.
        // Part of #464: Phase 4A constructive derivation (Packet B: #464).
        self.add_definition(SpecDefinition {
            name: "lam_typing_body_subst".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(A_dom : KExpr) (body : KExpr) (A0 : KExpr) (B0 : KExpr) (arg : KExpr), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "Typing (KExpr.lam A_dom body) (KExpr.pi A0 B0) -> ",
                "Typing arg A0 -> ",
                "Typing (instantiate body arg) (instantiate B0 arg)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(A_dom : KExpr) (body : KExpr) (A0 : KExpr) (B0 : KExpr) (arg : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(hlam : Typing (KExpr.lam A_dom body) (KExpr.pi A0 B0)) ",
                    "(harg : Typing arg A0) => ",
                    "Typing.rec ",
                    "(fun (e : KExpr) (T : KExpr) (_h : Typing e T) => ",
                    "Eq KExpr e (KExpr.lam A_dom body) -> DefEq T (KExpr.pi A0 B0) -> ",
                    "Typing (instantiate body arg) (instantiate B0 arg)) ",
                    // sort case: Sort n ≠ Lam
                    "(fun (n : Level) (eq : Eq KExpr (KExpr.sort n) (KExpr.lam A_dom body)) ",
                    "(_deq : DefEq (KExpr.sort (Level.succ n)) (KExpr.pi A0 B0)) => ",
                    "sort_ne_lam n A_dom body ",
                    "(Typing (instantiate body arg) (instantiate B0 arg)) eq) ",
                    // pi case: Pi A1 B1 ≠ Lam
                    "(fun (A1 : KExpr) (B1 : KExpr) (n : Level) (m : Level) ",
                    "(_hA : Typing A1 (KExpr.sort n)) (_hB : Typing B1 (KExpr.sort m)) ",
                    "(_ihA : Eq KExpr A1 (KExpr.lam A_dom body) -> ",
                    "DefEq (KExpr.sort n) (KExpr.pi A0 B0) -> ",
                    "Typing (instantiate body arg) (instantiate B0 arg)) ",
                    "(_ihB : Eq KExpr B1 (KExpr.lam A_dom body) -> ",
                    "DefEq (KExpr.sort m) (KExpr.pi A0 B0) -> ",
                    "Typing (instantiate body arg) (instantiate B0 arg)) ",
                    "(eq : Eq KExpr (KExpr.pi A1 B1) (KExpr.lam A_dom body)) ",
                    "(_deq : DefEq (KExpr.sort (Level.imax n m)) (KExpr.pi A0 B0)) => ",
                    "pi_ne_lam A1 B1 A_dom body ",
                    "(Typing (instantiate body arg) (instantiate B0 arg)) eq) ",
                    // lam case: PRODUCTIVE — extract body typing via lam injectivity,
                    // bridge domain/codomain via pi_injectivity_def_eq, apply
                    // substitution_typing and def_eq_respects_subst
                    // Part of #2870: binder domain universe generalized from Nat.zero to u2
                    "(fun (A2 : KExpr) (b2 : KExpr) (B2 : KExpr) (u2 : Level) ",
                    "(hA2 : Typing A2 (KExpr.sort u2)) (hb2 : Typing b2 B2) ",
                    "(_ihA2 : Eq KExpr A2 (KExpr.lam A_dom body) -> ",
                    "DefEq (KExpr.sort u2) (KExpr.pi A0 B0) -> ",
                    "Typing (instantiate body arg) (instantiate B0 arg)) ",
                    "(_ihb2 : Eq KExpr b2 (KExpr.lam A_dom body) -> ",
                    "DefEq B2 (KExpr.pi A0 B0) -> ",
                    "Typing (instantiate body arg) (instantiate B0 arg)) ",
                    "(eq_lam : Eq KExpr (KExpr.lam A2 b2) (KExpr.lam A_dom body)) ",
                    "(deq_pi : DefEq (KExpr.pi A2 B2) (KExpr.pi A0 B0)) => ",
                    // Part of #464 Packet B: retired `Eq.substType + def_eq_to_eq`
                    // transport in favor of direct `Typing.conv` + raw→typed
                    // DefEq bridge (raw_to_typed_def_eq from #464 Packet B').
                    "Typing.conv (instantiate body arg) ",
                    "(instantiate B2 arg) (instantiate B0 arg) ",
                    "(substitution_typing A_dom B2 body arg u2 wd wr ",
                    "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.sort u2)) ",
                    "A2 A_dom (lam_inj_fst A2 b2 A_dom body eq_lam) hA2) ",
                    "(Eq.substType KExpr (fun (x : KExpr) => Typing x B2) ",
                    "b2 body (lam_inj_snd A2 b2 A_dom body eq_lam) hb2) ",
                    // Inner harg transport: Typing arg A0 → Typing arg A_dom
                    // via raw_to_typed_def_eq on DefEq.symm of
                    // pi_injectivity_def_eq_dom.
                    "(Typing.conv arg A0 A_dom harg ",
                    "(DefEq.symm A_dom A0 ",
                    "(pi_injectivity_def_eq_dom hf A_dom A0 B2 B0 ",
                    "(Eq.substType KExpr ",
                    "(fun (x : KExpr) => DefEq (KExpr.pi x B2) (KExpr.pi A0 B0)) ",
                    "A2 A_dom (lam_inj_fst A2 b2 A_dom body eq_lam) deq_pi))))) ",
                    // Outer codomain transport on
                    // def_eq_respects_subst + pi_injectivity_def_eq_cod.
                    "(def_eq_respects_subst B2 B0 arg wd wr ",
                    "(pi_injectivity_def_eq_cod hf A_dom A0 B2 B0 ",
                    "(Eq.substType KExpr ",
                    "(fun (x : KExpr) => DefEq (KExpr.pi x B2) (KExpr.pi A0 B0)) ",
                    "A2 A_dom (lam_inj_fst A2 b2 A_dom body eq_lam) deq_pi)))) ",
                    // app case: App f a2 ≠ Lam
                    "(fun (f : KExpr) (a2 : KExpr) (A2 : KExpr) (B2 : KExpr) ",
                    "(_hf : Typing f (KExpr.pi A2 B2)) (_ha2 : Typing a2 A2) ",
                    "(_ihf : Eq KExpr f (KExpr.lam A_dom body) -> ",
                    "DefEq (KExpr.pi A2 B2) (KExpr.pi A0 B0) -> ",
                    "Typing (instantiate body arg) (instantiate B0 arg)) ",
                    "(_iha2 : Eq KExpr a2 (KExpr.lam A_dom body) -> ",
                    "DefEq A2 (KExpr.pi A0 B0) -> ",
                    "Typing (instantiate body arg) (instantiate B0 arg)) ",
                    "(eq : Eq KExpr (KExpr.app f a2) (KExpr.lam A_dom body)) ",
                    "(_deq : DefEq (instantiate B2 a2) (KExpr.pi A0 B0)) => ",
                    "app_ne_lam f a2 A_dom body ",
                    "(Typing (instantiate body arg) (instantiate B0 arg)) eq) ",
                    // conv case: chain DefEq via DefEq.trans
                    "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                    "(_he : Typing e0 T1) (deq_conv : DefEq T1 T2) ",
                    "(ih : Eq KExpr e0 (KExpr.lam A_dom body) -> ",
                    "DefEq T1 (KExpr.pi A0 B0) -> ",
                    "Typing (instantiate body arg) (instantiate B0 arg)) ",
                    "(eq0 : Eq KExpr e0 (KExpr.lam A_dom body)) ",
                    "(deq_outer : DefEq T2 (KExpr.pi A0 B0)) => ",
                    "ih eq0 (DefEq.trans T1 T2 (KExpr.pi A0 B0) ",
                    "deq_conv deq_outer)) ",
                    // Apply Typing.rec to hlam with reflexivity witnesses
                    "(KExpr.lam A_dom body) (KExpr.pi A0 B0) hlam ",
                    "(Eq.refl KExpr (KExpr.lam A_dom body)) ",
                    "(DefEq.refl (KExpr.pi A0 B0))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lambda typing inversion + substitution: if (λA.b) : Π(A0).B0 and a : A0, ",
                "then b[a/0] : B0[a/0]. DerivedPending via Typing.rec with DefEq-accumulating ",
                "motive, pi_injectivity_def_eq for domain/codomain bridging, substitution_typing ",
                "for the core substitution, and def_eq_respects_subst for result type bridging. ",
                "Part of #464."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Typing.conv".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "sort_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "app_ne_lam".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "pi_injectivity_def_eq_dom".to_string(),
                "pi_injectivity_def_eq_cod".to_string(),
                "substitution_typing".to_string(),
                "def_eq_respects_subst".to_string(),
            ])),
            // pi_injectivity_def_eq now DerivedProved via church_rosser_whnf (#2851).
            // delta/iota_subst DerivedProved via #725 reduction witnesses.
            // Part of #464 Packet B: def_eq_to_eq retired via raw_to_typed_def_eq
            // bridge (f71e7ee98); Typing.conv used directly for type transport.
            axiom_deps: HashSet::new(),
        })?;

        // Beta preservation — DerivedPending via Typing.rec on the application
        // derivation + lam_typing_body_subst for the inner inversion.
        // The proof applies Typing.rec with motive
        //   P(e,T,_) = Eq e (app (lam A b) a) -> Typing (instantiate b a) T
        // The app case extracts f0 = lam A b and a0 = a via injectivity, then
        // applies lam_typing_body_subst. The conv case chains via Typing.conv.
        // Part of #464: Phase 4A constructive derivation.
        self.add_definition(SpecDefinition {
            name: "beta_preservation".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(A : KExpr) (b : KExpr) (a : KExpr) (T : KExpr), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "has_type (KExpr.app (KExpr.lam A b) a) T -> ",
                "has_type (instantiate b a) T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(A_p : KExpr) (b_p : KExpr) (a_p : KExpr) (T_p : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(happ : Typing (KExpr.app (KExpr.lam A_p b_p) a_p) T_p) => ",
                    "Typing.rec ",
                    "(fun (e : KExpr) (T : KExpr) (_h : Typing e T) => ",
                    "Eq KExpr e (KExpr.app (KExpr.lam A_p b_p) a_p) -> ",
                    "Typing (instantiate b_p a_p) T) ",
                    // sort case: Sort n ≠ App
                    "(fun (n : Level) ",
                    "(eq : Eq KExpr (KExpr.sort n) (KExpr.app (KExpr.lam A_p b_p) a_p)) => ",
                    "sort_ne_app n (KExpr.lam A_p b_p) a_p ",
                    "(Typing (instantiate b_p a_p) (KExpr.sort (Level.succ n))) eq) ",
                    // pi case: Pi ≠ App
                    "(fun (A1 : KExpr) (B1 : KExpr) (n : Level) (m : Level) ",
                    "(_hA : Typing A1 (KExpr.sort n)) (_hB : Typing B1 (KExpr.sort m)) ",
                    "(_ihA : Eq KExpr A1 (KExpr.app (KExpr.lam A_p b_p) a_p) -> ",
                    "Typing (instantiate b_p a_p) (KExpr.sort n)) ",
                    "(_ihB : Eq KExpr B1 (KExpr.app (KExpr.lam A_p b_p) a_p) -> ",
                    "Typing (instantiate b_p a_p) (KExpr.sort m)) ",
                    "(eq : Eq KExpr (KExpr.pi A1 B1) (KExpr.app (KExpr.lam A_p b_p) a_p)) => ",
                    "pi_ne_app A1 B1 (KExpr.lam A_p b_p) a_p ",
                    "(Typing (instantiate b_p a_p) (KExpr.sort (Level.imax n m))) eq) ",
                    // lam case: Lam ≠ App
                    // Part of #2870: binder domain universe generalized from Nat.zero to u1
                    "(fun (A1 : KExpr) (b1 : KExpr) (B1 : KExpr) (u1 : Level) ",
                    "(_hA : Typing A1 (KExpr.sort u1)) (_hb : Typing b1 B1) ",
                    "(_ihA : Eq KExpr A1 (KExpr.app (KExpr.lam A_p b_p) a_p) -> ",
                    "Typing (instantiate b_p a_p) (KExpr.sort u1)) ",
                    "(_ihb : Eq KExpr b1 (KExpr.app (KExpr.lam A_p b_p) a_p) -> ",
                    "Typing (instantiate b_p a_p) B1) ",
                    "(eq : Eq KExpr (KExpr.lam A1 b1) (KExpr.app (KExpr.lam A_p b_p) a_p)) => ",
                    "lam_ne_app A1 b1 (KExpr.lam A_p b_p) a_p ",
                    "(Typing (instantiate b_p a_p) (KExpr.pi A1 B1)) eq) ",
                    // app case: PRODUCTIVE — extract f0 = lam A b, a0 = a,
                    // apply lam_typing_body_subst, bridge via Eq.substType for a0→a
                    "(fun (f0 : KExpr) (a0 : KExpr) (A0 : KExpr) (B0 : KExpr) ",
                    "(hf0 : Typing f0 (KExpr.pi A0 B0)) (ha0 : Typing a0 A0) ",
                    "(_ihf : Eq KExpr f0 (KExpr.app (KExpr.lam A_p b_p) a_p) -> ",
                    "Typing (instantiate b_p a_p) (KExpr.pi A0 B0)) ",
                    "(_iha : Eq KExpr a0 (KExpr.app (KExpr.lam A_p b_p) a_p) -> ",
                    "Typing (instantiate b_p a_p) A0) ",
                    "(eq : Eq KExpr (KExpr.app f0 a0) ",
                    "(KExpr.app (KExpr.lam A_p b_p) a_p)) => ",
                    // Goal: Typing (instantiate b_p a_p) (instantiate B0 a0)
                    // lam_typing_body_subst gives Typing (instantiate b_p a_p) (instantiate B0 a_p)
                    // Bridge: instantiate B0 a_p → instantiate B0 a0 via Eq.substType on a_p = a0
                    "Eq.substType KExpr ",
                    "(fun (v : KExpr) => Typing (instantiate b_p a_p) (instantiate B0 v)) ",
                    "a_p a0 ",
                    "(Eq.symm KExpr a0 a_p ",
                    "(app_inj_snd f0 a0 (KExpr.lam A_p b_p) a_p eq)) ",
                    "(lam_typing_body_subst hf A_p b_p A0 B0 a_p wd wr ",
                    "(Eq.substType KExpr (fun (x : KExpr) => Typing x (KExpr.pi A0 B0)) ",
                    "f0 (KExpr.lam A_p b_p) ",
                    "(app_inj_fst f0 a0 (KExpr.lam A_p b_p) a_p eq) hf0) ",
                    "(Eq.substType KExpr (fun (x : KExpr) => Typing x A0) ",
                    "a0 a_p ",
                    "(app_inj_snd f0 a0 (KExpr.lam A_p b_p) a_p eq) ha0))) ",
                    // conv case: chain via Typing.conv
                    "(fun (e0 : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                    "(_he : Typing e0 T1) (eq_t : DefEq T1 T2) ",
                    "(ih : Eq KExpr e0 (KExpr.app (KExpr.lam A_p b_p) a_p) -> ",
                    "Typing (instantiate b_p a_p) T1) ",
                    "(eq : Eq KExpr e0 (KExpr.app (KExpr.lam A_p b_p) a_p)) => ",
                    "Typing.conv (instantiate b_p a_p) T1 T2 (ih eq) eq_t) ",
                    // Apply Typing.rec to happ with reflexivity witness
                    "(KExpr.app (KExpr.lam A_p b_p) a_p) T_p happ ",
                    "(Eq.refl KExpr (KExpr.app (KExpr.lam A_p b_p) a_p))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Beta preservation: if (λA.b) a : T, then b[a/0] : T. DerivedPending via ",
                "Typing.rec + lam_typing_body_subst for inner lam inversion. Depends on ",
                "pi_injectivity_def_eq (from lam inversion) and delta/iota_subst helpers ",
                "(from substitution_typing). Part of #464."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Typing.conv".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "Eq.symm".to_string(),
                "sort_ne_app".to_string(),
                "pi_ne_app".to_string(),
                "lam_ne_app".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
                "lam_typing_body_subst".to_string(),
            ])),
            // pi_injectivity_def_eq now DerivedProved via church_rosser_whnf (#2851).
            // delta/iota_subst DerivedProved via #725 reduction witnesses.
            // Part of #464 Packet B: def_eq_to_eq no longer inherited from
            // lam_typing_body_subst (retired via raw_to_typed_def_eq bridge).
            axiom_deps: HashSet::new(),
        })?;

        // Typing uniqueness, beta expansion, congruence delegation, and
        // def_eq_typing_iff are in type_preservation_cases_def_eq.rs.
        self.add_type_preservation_cases_def_eq()?;

        Ok(())
    }
}
