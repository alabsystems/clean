// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Typing uniqueness, beta expansion, and bidirectional type preservation.
//!
//! Contains:
//! - typing_same_term_types_def_eq: DerivedPending via church_rosser_whnf.
//!   Pi-case Eq bridge uses the Packet-A `sort_def_eq_eq` specializer
//!   (Packet C retired the former `def_eq_to_eq` detour at lines 108/120).
//! - beta_expansion: typed-beta subject expansion (DerivedPending).
//!   The outer Eq.substType transport was retired in favor of `Typing.conv` +
//!   `raw_to_typed_def_eq` bridge (Packet C-residual, Part of #464).
//! - def_eq_typing_iff: bidirectional preservation via TypedDefEq.rec
//!   (DerivedPending via church_rosser_whnf).
//!
//! Part of #2765, #464 Packet C.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register typing uniqueness, beta expansion, and def_eq_typing_iff.
    ///
    /// Must be called after `add_type_preservation_cases` since
    /// typing_same_term_types_def_eq depends on generation lemmas, and
    /// def_eq_typing_iff depends on beta_preservation and congruence proofs.
    pub(super) fn add_type_preservation_cases_def_eq(&mut self) -> Result<(), SpecError> {
        // Type uniqueness (up to DefEq): if the same term has two types, those
        // types are definitionally equal. Derived constructively via Typing.rec +
        // generation lemmas. The App case uses pi_injectivity_def_eq_cod which
        // transitively depends on church_rosser_whnf, making this DerivedPending.
        //
        // Proof by Typing.rec on h1 with motive:
        //   P(e, T1, _) = ∀ T2, Typing e T2 → DefEq T1 T2
        //
        // Design: designs/2026-03-18-464-typing-uniqueness-derivation.md
        // Part of #461, #464.
        self.add_definition(SpecDefinition {
            name: "typing_same_term_types_def_eq".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(e : KExpr) (T1 : KExpr) (T2 : KExpr), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "has_type e T1 -> ",
                "has_type e T2 -> ",
                "DefEq T1 T2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(e : KExpr) (T1 : KExpr) (T2 : KExpr) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(h1 : has_type e T1) (h2 : has_type e T2) => ",
                    "Typing.rec ",
                    // Motive: P(e, T1, _) = ∀ T2, Typing e T2 → DefEq T1 T2
                    "(fun (e0 : KExpr) (T0 : KExpr) (_ : Typing e0 T0) => ",
                    "forall (T2 : KExpr), Typing e0 T2 -> DefEq T0 T2) ",
                    // ========== Sort case ==========
                    // e = Sort n, T1 = Sort (succ n).
                    // Given h2': Typing (Sort n) T2.
                    // By typing_sort_gen: DefEq T2 (Sort (succ n)).
                    // By DefEq.symm: DefEq (Sort (succ n)) T2. ✓
                    "(fun (n : Level) (T2 : KExpr) (h2p : Typing (KExpr.sort n) T2) => ",
                    "DefEq.symm T2 (KExpr.sort (Level.succ n)) ",
                    "(typing_sort_gen n T2 h2p)) ",
                    // ========== Pi case ==========
                    // Part of #2870: T1 = Sort (imax_nat _n m) instead of Sort m.
                    // e = Pi A B, T1 = Sort (imax_nat _n m).
                    // IH_A: ∀ T', Typing A T' → DefEq (Sort _n) T'.
                    // IH_B: ∀ T', Typing B T' → DefEq (Sort m) T'.
                    // Given h2': Typing (Pi A B) T2.
                    // By typing_pi_gen (CPS): get n2, m2, Typing A (Sort n2),
                    //   Typing B (Sort m2), DefEq T2 (Sort (imax_nat n2 m2)).
                    // By IH_A + IH_B + sort injectivity: Eq Nat _n n2, Eq Nat m m2.
                    // By imax_nat congruence: Eq Nat (imax_nat _n m) (imax_nat n2 m2).
                    // Lift to DefEq + DefEq.trans: DefEq (Sort (imax_nat _n m)) T2. ✓
                    "(fun (A : KExpr) (B : KExpr) (_n : Level) (m : Level) ",
                    "(_hA : Typing A (KExpr.sort _n)) (_hB : Typing B (KExpr.sort m)) ",
                    "(ihA : forall (T2 : KExpr), Typing A T2 -> DefEq (KExpr.sort _n) T2) ",
                    "(ihB : forall (T2 : KExpr), Typing B T2 -> DefEq (KExpr.sort m) T2) ",
                    "(T2 : KExpr) (h2p : Typing (KExpr.pi A B) T2) => ",
                    "typing_pi_gen A B T2 (DefEq (KExpr.sort (Level.imax _n m)) T2) h2p ",
                    "(fun (n2 : Level) (m2 : Level) (hAn2 : Typing A (KExpr.sort n2)) ",
                    "(hBm2 : Typing B (KExpr.sort m2)) ",
                    "(deq_T2 : DefEq T2 (KExpr.sort (Level.imax n2 m2))) => ",
                    // DefEq (Sort (imax_nat _n m)) T2 via bridge + DefEq.symm
                    "DefEq.trans (KExpr.sort (Level.imax _n m)) (KExpr.sort (Level.imax n2 m2)) T2 ",
                    // Bridge: DefEq (Sort (imax_nat _n m)) (Sort (imax_nat n2 m2))
                    // via Eq.substType from Eq KExpr built by sort injectivity + imax_nat congruence
                    "(Eq.substType KExpr (fun (x : KExpr) => DefEq x (KExpr.sort (Level.imax n2 m2))) ",
                    "(KExpr.sort (Level.imax n2 m2)) (KExpr.sort (Level.imax _n m)) ",
                    "(Eq.symm KExpr (KExpr.sort (Level.imax _n m)) (KExpr.sort (Level.imax n2 m2)) ",
                    // Eq KExpr (Sort (imax_nat _n m)) (Sort (imax_nat n2 m2))
                    "(Eq.cong Level KExpr KExpr.sort (Level.imax _n m) (Level.imax n2 m2) ",
                    // Eq Level (Level.imax _n m) (Level.imax n2 m2)
                    "(Eq.trans Level (Level.imax _n m) (Level.imax n2 m) (Level.imax n2 m2) ",
                    // Eq Level (Level.imax _n m) (Level.imax n2 m) — congruence in first arg
                    "(Eq.cong Level Level (fun (x : Level) => Level.imax x m) _n n2 ",
                    // Eq Nat _n n2 — sort injectivity on ihA via sort_def_eq_eq + Eq.cong
                    // Part of #464 Packet C: retired def_eq_to_eq in favor of
                    // the Sort-specialized Church-Rosser lemma from Packet A.
                    "(Eq.cong KExpr Level ",
                    "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => Level) ",
                    "(fun (k : Level) => k) (fun (_ : Nat) => _n) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => _n) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => _n) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => _n) ",
                    "(fun (_ : Name) (_ : ListType Level) => _n) ",
                    // let_ minor (7th KExpr ctor: ty, val, body — 3 recursive fields + 3 IHs, all Level)
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) (_ : Level) => _n) ",
                    // proj minor (s:Name, i:Nat, sub:KExpr — 1 IH:Level); lit minor (v:Nat)
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Level) => _n) ",
                    "(fun (_ : Nat) => _n) e) ",
                    "(KExpr.sort _n) (KExpr.sort n2) ",
                    "(sort_def_eq_eq hf _n n2 (ihA (KExpr.sort n2) hAn2)))) ",
                    // Eq Level (Level.imax n2 m) (Level.imax n2 m2) — congruence in second arg
                    "(Eq.cong Level Level (fun (y : Level) => Level.imax n2 y) m m2 ",
                    // Eq Level m m2 — sort injectivity on ihB via sort_def_eq_eq + Eq.cong
                    // Part of #464 Packet C.
                    "(Eq.cong KExpr Level ",
                    "(fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => Level) ",
                    "(fun (k : Level) => k) (fun (_ : Nat) => m) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => m) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => m) ",
                    "(fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => m) ",
                    "(fun (_ : Name) (_ : ListType Level) => m) ",
                    // let_ minor (7th KExpr ctor: ty, val, body — 3 recursive fields + 3 IHs, all Level)
                    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) (_ : Level) => m) ",
                    // proj minor (s:Name, i:Nat, sub:KExpr — 1 IH:Level); lit minor (v:Nat)
                    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Level) => m) ",
                    "(fun (_ : Nat) => m) e) ",
                    "(KExpr.sort m) (KExpr.sort m2) ",
                    "(sort_def_eq_eq hf m m2 (ihB (KExpr.sort m2) hBm2))))))) ",
                    "(DefEq.refl (KExpr.sort (Level.imax n2 m2)))) ",
                    "(DefEq.symm T2 (KExpr.sort (Level.imax n2 m2)) deq_T2))) ",
                    // ========== Lam case ==========
                    // e = Lam A b, T1 = Pi A B.
                    // IH_b: ∀ T', Typing b T' → DefEq B T'.
                    // Given h2': Typing (Lam A b) T2.
                    // By typing_lam_gen (CPS): get B', Typing b B', DefEq T2 (Pi A B').
                    // By IH_b: DefEq B B'.
                    // By DefEq.pi_cong + DefEq.refl: DefEq (Pi A B) (Pi A B').
                    // By DefEq.trans + DefEq.symm: DefEq (Pi A B) T2. ✓
                    // Part of #2870: binder domain universe generalized from Nat.zero to u_lam
                    "(fun (A : KExpr) (b : KExpr) (B : KExpr) (u_lam : Level) ",
                    "(_hA : Typing A (KExpr.sort u_lam)) (_hb : Typing b B) ",
                    "(_ihA : forall (T2 : KExpr), Typing A T2 -> DefEq (KExpr.sort u_lam) T2) ",
                    "(ihb : forall (T2 : KExpr), Typing b T2 -> DefEq B T2) ",
                    "(T2 : KExpr) (h2p : Typing (KExpr.lam A b) T2) => ",
                    "typing_lam_gen A b T2 (DefEq (KExpr.pi A B) T2) h2p ",
                    "(fun (B2 : KExpr) (hbB2 : Typing b B2) ",
                    "(deq_T2 : DefEq T2 (KExpr.pi A B2)) => ",
                    "DefEq.trans (KExpr.pi A B) (KExpr.pi A B2) T2 ",
                    "(DefEq.pi_cong A A B B2 (DefEq.refl A) (ihb B2 hbB2)) ",
                    "(DefEq.symm T2 (KExpr.pi A B2) deq_T2))) ",
                    // ========== App case ==========
                    // e = App f a, T1 = instantiate B a.
                    // IH_f: ∀ T', Typing f T' → DefEq (Pi A B) T'.
                    // Given h2': Typing (App f a) T2.
                    // By typing_app_gen (CPS): get A', B', Typing f (Pi A' B'),
                    //   Typing a A', DefEq T2 (instantiate B' a).
                    // By IH_f: DefEq (Pi A B) (Pi A' B').
                    // By pi_injectivity_def_eq_cod: DefEq B B'.
                    //   *** This introduces the church_rosser_whnf dependency ***
                    // By def_eq_respects_subst: DefEq (instantiate B a) (instantiate B' a).
                    // By DefEq.trans + DefEq.symm: DefEq (instantiate B a) T2. ✓
                    "(fun (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) ",
                    "(_hf : Typing f (KExpr.pi A B)) (_ha : Typing a A) ",
                    "(ihf : forall (T2 : KExpr), Typing f T2 -> DefEq (KExpr.pi A B) T2) ",
                    "(_iha : forall (T2 : KExpr), Typing a T2 -> DefEq A T2) ",
                    "(T2 : KExpr) (h2p : Typing (KExpr.app f a) T2) => ",
                    "typing_app_gen f a T2 (DefEq (instantiate B a) T2) h2p ",
                    "(fun (A2 : KExpr) (B2 : KExpr) ",
                    "(hf2 : Typing f (KExpr.pi A2 B2)) (ha2 : Typing a A2) ",
                    "(deq_T2 : DefEq T2 (instantiate B2 a)) => ",
                    "DefEq.trans (instantiate B a) (instantiate B2 a) T2 ",
                    "(def_eq_respects_subst B B2 a wd wr ",
                    "(pi_injectivity_def_eq_cod hf A A2 B B2 (ihf (KExpr.pi A2 B2) hf2))) ",
                    "(DefEq.symm T2 (instantiate B2 a) deq_T2))) ",
                    // ========== Conv case ==========
                    // Typing e0 T1' with DefEq T1' T1.
                    // IH: ∀ T2, Typing e0 T2 → DefEq T1' T2.
                    // Given h2': Typing e0 T2.
                    // By IH: DefEq T1' T2.
                    // By DefEq.symm on deq: DefEq T1 T1'.
                    // deq : typing_is_def_eq T1' T1, so T1 is the conv target.
                    // Typing.conv e0 T1' T1 he deq, so T = T1 and
                    //   deq is bridged back to raw DefEq when needed below.
                    // Need: DefEq T1 T2.
                    // DefEq.symm T1' T1 (typed_def_eq_to_def_eq T1' T1 deq) : DefEq T1 T1'.
                    // IH T2 h2' : DefEq T1' T2.
                    // DefEq.trans T1 T1' T2 ... (IH T2 h2').
                    "(fun (e0 : KExpr) (T1p : KExpr) (T1 : KExpr) ",
                    "(_he : Typing e0 T1p) (deq : DefEq T1p T1) ",
                    "(ih : forall (T2 : KExpr), Typing e0 T2 -> DefEq T1p T2) ",
                    "(T2 : KExpr) (h2p : Typing e0 T2) => ",
                    "DefEq.trans T1 T1p T2 ",
                    "(DefEq.symm T1p T1 deq) ",
                    "(ih T2 h2p)) ",
                    // Apply Typing.rec
                    "e T1 h1 T2 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Type uniqueness (up to DefEq): if e : T1 and e : T2, then DefEq T1 T2. ",
                "DerivedPending via Typing.rec + generation lemmas. App case requires ",
                "pi_injectivity_def_eq_cod which transitively depends on church_rosser_whnf. ",
                "Pi case uses sort_def_eq_eq (Packet A) + inline sort injectivity for ",
                "imax_nat bridge (Part of #2870). Part of #461, #464 Packet C."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.pi_cong".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.substType".to_string(),
                "KExpr.rec".to_string(),
                "sort_def_eq_eq".to_string(),
                "typed_def_eq_to_def_eq".to_string(),
                "imax_nat".to_string(),
                "typing_sort_gen".to_string(),
                "typing_pi_gen".to_string(),
                "typing_lam_gen".to_string(),
                "typing_app_gen".to_string(),
                "pi_injectivity_def_eq_cod".to_string(),
                "def_eq_respects_subst".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Beta expansion / subject expansion. Typed beta recursor view
        // (#2856) supplies the explicit typed beta inputs; only type
        // alignment on the substituted term remains. Part of #464 Packet
        // C-residual: outer Eq.substType transport retired in favor of
        // `Typing.conv` + `raw_to_typed_def_eq` bridge (f71e7ee98) now that
        // the DefEq→TypedDefEq forward bridge is available.
        self.add_definition(SpecDefinition {
            name: "beta_expansion".to_string(),
            // Part of #2870: binder domain universe generalized from Nat.zero to u
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(A : KExpr) (body : KExpr) (arg : KExpr) (B : KExpr) (T : KExpr) (u : Level), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "has_type A (KExpr.sort u) -> ",
                "has_type body B -> ",
                "has_type arg A -> ",
                "has_type (instantiate body arg) T -> ",
                "has_type (KExpr.app (KExpr.lam A body) arg) T"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (hf : RedEnvFaithful the_red_env) ",
                    "(A : KExpr) (body : KExpr) (arg : KExpr) (B : KExpr) (T : KExpr) (u : Level) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(hA : has_type A (KExpr.sort u)) ",
                    "(hbody : has_type body B) ",
                    "(harg : has_type arg A) ",
                    "(hinst : has_type (instantiate body arg) T) => ",
                    // Part of #464 Packet C-residual: retired residual
                    // `Eq.substType + def_eq_to_eq` transport in favor of
                    // `Typing.conv` + raw_to_typed_def_eq bridge (f71e7ee98).
                    "Typing.conv (KExpr.app (KExpr.lam A body) arg) ",
                    "(instantiate B arg) T ",
                    "(Typing.app (KExpr.lam A body) arg A B ",
                    "(Typing.lam A body B u hA hbody) harg) ",
                    "(typing_same_term_types_def_eq hf (instantiate body arg) ",
                    "(instantiate B arg) T wd wr ",
                    "(substitution_typing A B body arg u wd wr hA hbody harg) hinst)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Typed beta expansion (subject expansion): rebuilds (λA.body) arg : T ",
                "from explicit domain/body/argument typing data plus typing of the ",
                "substituted body. DerivedPending: transitively reaches the value-less ",
                "def_eq_to_eq bridge through typing_same_term_types_def_eq. ZERO ",
                "axiom_deps — church_rosser_whnf retired (#2859). ",
                "Part of #464 Packet C-residual: Eq.substType + def_eq_to_eq transport ",
                "retired in favor of Typing.conv + raw_to_typed_def_eq bridge. ",
                "Part of #2856, #464 Packet C."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.lam".to_string(),
                "Typing.app".to_string(),
                "Typing.conv".to_string(),
                "substitution_typing".to_string(),
                "typing_same_term_types_def_eq".to_string(),
            ])),
            // #2859: church_rosser_whnf retired. The true transitive HelperAxiom
            // closure is EMPTY — substitution_typing and
            // typing_same_term_types_def_eq are both HelperAxiom-free; the residual
            // is the value-less def_eq_to_eq bridge, not an axiom leaf.
            axiom_deps: HashSet::new(),
        })?;

        // Congruence type preservation (6 proofs) in type_preservation_cases_congruence.rs
        self.add_type_preservation_cases_congruence()?;

        // Delta/iota type preservation (forward/backward) are now registered in
        // reduction_witnesses.rs as DerivedProved (Part of #725).

        // ----- def_eq_typing_iff: central theorem -----

        // Bidirectional type preservation — DerivedPending via TypedDefEq.rec with AndType motive.
        // Part of #464: Phase 4A constructive derivation.
        self.add_definition(SpecDefinition {
            name: "def_eq_typing_iff".to_string(),
            type_src: concat!(
                "forall (hf : RedEnvFaithful the_red_env) ",
                "(e : KExpr) (e' : KExpr), ",
                "DefEnvWellformed the_red_env -> RecEnvWellformed (red_rec the_red_env) -> ",
                "typing_is_def_eq e e' -> ",
                "AndType (forall (T : KExpr), has_type e T -> has_type e' T) ",
                "(forall (T : KExpr), has_type e' T -> has_type e T)"
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (hf : RedEnvFaithful the_red_env) ",
                "(e : KExpr) (e' : KExpr) ",
                "(wd : DefEnvWellformed the_red_env) ",
                "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                "(h : typing_is_def_eq e e') => ",
                "TypedDefEq.rec ",
                // Motive P
                "(fun (a : KExpr) (b : KExpr) (_h : TypedDefEq a b) => ",
                "AndType (forall (T : KExpr), has_type a T -> has_type b T) ",
                "(forall (T : KExpr), has_type b T -> has_type a T)) ",
                // Case: refl — identity in both directions
                "(fun (a : KExpr) => AndType.intro ",
                "(forall (T : KExpr), has_type a T -> has_type a T) ",
                "(forall (T : KExpr), has_type a T -> has_type a T) ",
                "(fun (T : KExpr) (ht : has_type a T) => ht) ",
                "(fun (T : KExpr) (ht : has_type a T) => ht)) ",
                // Case: symm — swap AndType components from IH
                "(fun (a : KExpr) (b : KExpr) (_h : TypedDefEq a b) ",
                "(ih : AndType (forall (T : KExpr), has_type a T -> has_type b T) ",
                "(forall (T : KExpr), has_type b T -> has_type a T)) => ",
                "AndType.intro ",
                "(forall (T : KExpr), has_type b T -> has_type a T) ",
                "(forall (T : KExpr), has_type a T -> has_type b T) ",
                "(AndType.right ",
                "(forall (T : KExpr), has_type a T -> has_type b T) ",
                "(forall (T : KExpr), has_type b T -> has_type a T) ih) ",
                "(AndType.left ",
                "(forall (T : KExpr), has_type a T -> has_type b T) ",
                "(forall (T : KExpr), has_type b T -> has_type a T) ih)) ",
                // Case: trans — compose forward/backward from two IHs
                "(fun (a : KExpr) (b : KExpr) (c : KExpr) ",
                "(_hab : TypedDefEq a b) (_hbc : TypedDefEq b c) ",
                "(ih_ab : AndType (forall (T : KExpr), has_type a T -> has_type b T) ",
                "(forall (T : KExpr), has_type b T -> has_type a T)) ",
                "(ih_bc : AndType (forall (T : KExpr), has_type b T -> has_type c T) ",
                "(forall (T : KExpr), has_type c T -> has_type b T)) => ",
                "AndType.intro ",
                "(forall (T : KExpr), has_type a T -> has_type c T) ",
                "(forall (T : KExpr), has_type c T -> has_type a T) ",
                "(fun (T : KExpr) (ht : has_type a T) => ",
                "AndType.left (forall (U : KExpr), has_type b U -> has_type c U) ",
                "(forall (U : KExpr), has_type c U -> has_type b U) ih_bc T ",
                "(AndType.left (forall (U : KExpr), has_type a U -> has_type b U) ",
                "(forall (U : KExpr), has_type b U -> has_type a U) ih_ab T ht)) ",
                "(fun (T : KExpr) (ht : has_type c T) => ",
                "AndType.right (forall (U : KExpr), has_type a U -> has_type b U) ",
                "(forall (U : KExpr), has_type b U -> has_type a U) ih_ab T ",
                "(AndType.right (forall (U : KExpr), has_type b U -> has_type c U) ",
                "(forall (U : KExpr), has_type c U -> has_type b U) ih_bc T ht))) ",
                // Case: beta — use beta_preservation (fwd) and reconstructed
                // typed beta expansion (bwd). The typed recursor
                // provides the codomain + typing inputs explicitly.
                // Part of #2870: binder domain universe generalized from Nat.zero to u
                "(fun (A : KExpr) (body : KExpr) (arg : KExpr) ",
                "(B : KExpr) (u : Level) (hA : Typing A (KExpr.sort u)) ",
                "(hbody : Typing body B) (harg : Typing arg A) => ",
                "AndType.intro ",
                "(forall (T : KExpr), has_type (KExpr.app (KExpr.lam A body) arg) T -> has_type (instantiate body arg) T) ",
                "(forall (T : KExpr), has_type (instantiate body arg) T -> has_type (KExpr.app (KExpr.lam A body) arg) T) ",
                "(fun (T : KExpr) (ht : has_type (KExpr.app (KExpr.lam A body) arg) T) => ",
                "beta_preservation hf A body arg T wd wr ht) ",
                "(fun (T : KExpr) (ht : has_type (instantiate body arg) T) => ",
                "beta_expansion hf A body arg B T u wd wr hA hbody harg ht)) ",
                // Case: app_cong — use IHs with app_type_preservation/inv
                // via typed_def_eq_to_def_eq for the dependent result-type bridge.
                "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                "(_hf : TypedDefEq f f') (_ha : TypedDefEq a a') ",
                "(ih_f : AndType (forall (T : KExpr), has_type f T -> has_type f' T) ",
                "(forall (T : KExpr), has_type f' T -> has_type f T)) ",
                "(ih_a : AndType (forall (T : KExpr), has_type a T -> has_type a' T) ",
                "(forall (T : KExpr), has_type a' T -> has_type a T)) => ",
                "AndType.intro ",
                "(forall (T : KExpr), has_type (KExpr.app f a) T -> has_type (KExpr.app f' a') T) ",
                "(forall (T : KExpr), has_type (KExpr.app f' a') T -> has_type (KExpr.app f a) T) ",
                "(fun (T : KExpr) (ht : has_type (KExpr.app f a) T) => ",
                "app_type_preservation hf f f' a a' T ht (typed_def_eq_to_def_eq a a' _ha) ",
                "(AndType.left (forall (U : KExpr), has_type f U -> has_type f' U) ",
                "(forall (U : KExpr), has_type f' U -> has_type f U) ih_f) ",
                "(AndType.left (forall (U : KExpr), has_type a U -> has_type a' U) ",
                "(forall (U : KExpr), has_type a' U -> has_type a U) ih_a)) ",
                "(fun (T : KExpr) (ht : has_type (KExpr.app f' a') T) => ",
                "app_type_preservation_inv hf f f' a a' T ht (typed_def_eq_to_def_eq a a' _ha) ",
                "(AndType.right (forall (U : KExpr), has_type f U -> has_type f' U) ",
                "(forall (U : KExpr), has_type f' U -> has_type f U) ih_f) ",
                "(AndType.right (forall (U : KExpr), has_type a U -> has_type a' U) ",
                "(forall (U : KExpr), has_type a' U -> has_type a U) ih_a))) ",
                // Case: lam_cong — use IHs with lam_type_preservation/inv
                // lam_type_preservation now takes DefEq A A' (for Typing.conv bridge)
                "(fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) ",
                "(_hA : TypedDefEq A A') (_hb : TypedDefEq b b') ",
                "(ih_A : AndType (forall (T : KExpr), has_type A T -> has_type A' T) ",
                "(forall (T : KExpr), has_type A' T -> has_type A T)) ",
                "(ih_b : AndType (forall (T : KExpr), has_type b T -> has_type b' T) ",
                "(forall (T : KExpr), has_type b' T -> has_type b T)) => ",
                "AndType.intro ",
                "(forall (T : KExpr), has_type (KExpr.lam A b) T -> has_type (KExpr.lam A' b') T) ",
                "(forall (T : KExpr), has_type (KExpr.lam A' b') T -> has_type (KExpr.lam A b) T) ",
                "(fun (T : KExpr) (ht : has_type (KExpr.lam A b) T) => ",
                "lam_type_preservation A A' b b' T ht (typed_def_eq_to_def_eq A A' _hA) ",
                "(AndType.left (forall (U : KExpr), has_type A U -> has_type A' U) ",
                "(forall (U : KExpr), has_type A' U -> has_type A U) ih_A) ",
                "(AndType.left (forall (U : KExpr), has_type b U -> has_type b' U) ",
                "(forall (U : KExpr), has_type b' U -> has_type b U) ih_b)) ",
                "(fun (T : KExpr) (ht : has_type (KExpr.lam A' b') T) => ",
                "lam_type_preservation_inv A A' b b' T ht ",
                "(DefEq.symm A A' (typed_def_eq_to_def_eq A A' _hA)) ",
                "(AndType.right (forall (U : KExpr), has_type A U -> has_type A' U) ",
                "(forall (U : KExpr), has_type A' U -> has_type A U) ih_A) ",
                "(AndType.right (forall (U : KExpr), has_type b U -> has_type b' U) ",
                "(forall (U : KExpr), has_type b' U -> has_type b U) ih_b))) ",
                // Case: pi_cong — use IHs with pi_type_preservation/inv
                "(fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) ",
                "(_hA : TypedDefEq A A') (_hB : TypedDefEq B B') ",
                "(ih_A : AndType (forall (T : KExpr), has_type A T -> has_type A' T) ",
                "(forall (T : KExpr), has_type A' T -> has_type A T)) ",
                "(ih_B : AndType (forall (T : KExpr), has_type B T -> has_type B' T) ",
                "(forall (T : KExpr), has_type B' T -> has_type B T)) => ",
                "AndType.intro ",
                "(forall (T : KExpr), has_type (KExpr.pi A B) T -> has_type (KExpr.pi A' B') T) ",
                "(forall (T : KExpr), has_type (KExpr.pi A' B') T -> has_type (KExpr.pi A B) T) ",
                "(fun (T : KExpr) (ht : has_type (KExpr.pi A B) T) => ",
                "pi_type_preservation A A' B B' T ht ",
                "(AndType.left (forall (U : KExpr), has_type A U -> has_type A' U) ",
                "(forall (U : KExpr), has_type A' U -> has_type A U) ih_A) ",
                "(AndType.left (forall (U : KExpr), has_type B U -> has_type B' U) ",
                "(forall (U : KExpr), has_type B' U -> has_type B U) ih_B)) ",
                "(fun (T : KExpr) (ht : has_type (KExpr.pi A' B') T) => ",
                "pi_type_preservation_inv A A' B B' T ht ",
                "(AndType.right (forall (U : KExpr), has_type A U -> has_type A' U) ",
                "(forall (U : KExpr), has_type A' U -> has_type A U) ih_A) ",
                "(AndType.right (forall (U : KExpr), has_type B U -> has_type B' U) ",
                "(forall (U : KExpr), has_type B' U -> has_type B U) ih_B))) ",
                // Case: delta — use delta_type_preservation_fwd/bwd
                "(fun (e_d : KExpr) (e_d' : KExpr) (hd : delta_reduces e_d e_d') => ",
                "AndType.intro ",
                "(forall (T : KExpr), has_type e_d T -> has_type e_d' T) ",
                "(forall (T : KExpr), has_type e_d' T -> has_type e_d T) ",
                "(delta_type_preservation_fwd e_d e_d' wd hd) ",
                "(delta_type_preservation_bwd e_d e_d' wd hd)) ",
                // Case: iota — use iota_type_preservation_fwd/bwd
                "(fun (e_i : KExpr) (e_i' : KExpr) (hi : iota_reduces e_i e_i') => ",
                "AndType.intro ",
                "(forall (T : KExpr), has_type e_i T -> has_type e_i' T) ",
                "(forall (T : KExpr), has_type e_i' T -> has_type e_i T) ",
                "(iota_type_preservation_fwd e_i e_i' wr hi) ",
                "(iota_type_preservation_bwd e_i e_i' wr hi)) ",
                // Conclusion: apply recursor to the input derivation
                "e e' h"
            )
            .to_string()),
            is_axiom: false,
            description: concat!(
                "Bidirectional type preservation: typing_is_def_eq e e' implies both ",
                "has_type e T -> has_type e' T and has_type e' T -> has_type e T. ",
                "Proof via TypedDefEq.rec with bidirectional AndType motive. ",
                "Part of #464: Phase 4A constructive derivation."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            // pi_injectivity_def_eq now DerivedProved via church_rosser_whnf (#2851).
            // delta/iota helpers DerivedProved via #725 reduction witnesses.
            // typing_same_term_types_def_eq now DerivedPending via church_rosser_whnf (#461).
            // Transitive HelperAxiom frontier; def_eq_to_eq is a demoted bridge,
            // not a separate trust-frontier leaf.
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
