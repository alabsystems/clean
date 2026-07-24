// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Micro-checker soundness and cross-validation (PARTs 18-19)
//!
//! # VACUITY EXPOSURE (Brick 1 of the micro-band drain)
//!
//! `micro_has_type` is registered here as a single-constructor inductive whose
//! only constructor `sound_bvar` is a byte-for-byte copy of the field that was
//! formerly the admitted axiom `micro_verify_sound_bvar`. Instantiating that
//! constructor at `ty := U` and closing its `Eq` hypothesis by `Eq.refl`
//! (the kernel iota-reduces `micro_verify (MicroCert.bvar 0 U) e` to `U`)
//! makes `micro_has_type_total : forall e U, micro_has_type e U` a genuine
//! kernel-checked, zero-domain-axiom theorem. In other words `micro_has_type`
//! is a **TOTAL (degenerate) predicate**: EVERY expression has EVERY type.
//!
//! This brick therefore DRAINS a vacuous axiom band — it does NOT prove
//! micro-checker soundness. The seven `micro_verify_sound_*` producers and the
//! `micro_verify_sound` corollary are re-derived as one-line totality
//! corollaries (statements byte-identical to the retired axioms); the drain is
//! sound (old axiom set ⊢ the new constructor; new set ⊢ every old statement)
//! but carries zero trust content, and the honest successor — a faithful,
//! context-indexed, fresh-name `micro_typed` family with real rejection
//! witnesses — is future work (Brick 6), NOT this session.
//!
//! ## Transitional Empty-safety note
//!
//! During the brick the other producer axioms (`micro_sort_typing`,
//! `micro_pi_formation`, `micro_lam_typing`, `micro_app_typing`,
//! `micro_def_eq_preserves_typing`, `kernel_to_micro_typing`) remain admitted
//! over the now-constructible `micro_has_type` token that carries a live
//! `micro_has_type.rec`. This window is provably Empty-safe: totality means
//! every index `(e, U)` is reachable via `sound_bvar 0 U e U Eq.refl`, so
//! inversion of `micro_has_type.rec` can never land on an uninhabited index and
//! cannot derive `Empty`. (Contrast a NON-total faithful family, over which a
//! retained producer such as `kernel_to_micro_typing` WOULD be inconsistent —
//! which is exactly why Brick 6's faithful family must use fresh names and why
//! no old producer may ever be re-pointed at it.)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_micro_soundness(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // PART 18: Micro-Checker Soundness
        // =========================================================

        // micro_has_type: typing judgment for micro-checker.
        //
        // VACUITY EXPOSURE (Brick 1): formerly an opaque `-> Type` HelperAxiom,
        // now a FAITHFUL single-constructor inductive. The lone constructor
        // `sound_bvar` is a byte-for-byte copy of the field of the retired
        // axiom `micro_verify_sound_bvar` (unguarded stays unguarded — the `Eq`
        // hypothesis is preserved verbatim), so the old axiom set proves the new
        // constructor and the new set proves every old statement (see
        // `micro_has_type_total` below). This makes `micro_has_type` a TOTAL
        // (degenerate) predicate; the drain is sound but carries zero trust
        // content. `micro_has_type` now lowers to a kernel `Declaration::Inductive`
        // (plus its generated `micro_has_type.rec`), NOT a `ConstantKind::Axiom`,
        // so it and its 7 corollaries leave the axiom census.
        self.add_inductive(
            r"inductive micro_has_type : MicroExpr -> MicroExpr -> Type
| sound_bvar : forall (i : Nat) (ty : MicroExpr) (e : MicroExpr) (U : MicroExpr), Eq MicroExpr (micro_verify (MicroCert.bvar i ty) e) U -> micro_has_type e U",
            "Typing judgment for micro-checker: e has type T. Brick-1 vacuity \
             exposure: single-constructor inductive whose sole ctor sound_bvar is a \
             byte-copy of the retired micro_verify_sound_bvar field. TOTAL/degenerate \
             predicate (every e has every U); drains a vacuous band, does NOT prove \
             micro-checker soundness (that is the fresh-name Brick-6 successor).",
        )?;

        // micro_has_type_total: forall e U, micro_has_type e U.
        //
        // The degeneracy WITNESS and the audit artifact for the whole drain.
        // `micro_has_type.sound_bvar Nat.zero U e U (Eq.refl MicroExpr U)` type-
        // checks because the kernel iota-reduces
        //   micro_verify (MicroCert.bvar Nat.zero U) e  =>  U
        // (the bvar arm of micro_verify returns its `ty` field literally), so the
        // constructor's `Eq MicroExpr (micro_verify (MicroCert.bvar 0 U) e) U`
        // hypothesis closes by `Eq.refl MicroExpr U`. Genuine kernel-checked,
        // zero-domain-axiom Theorem (axiom_deps = {}); it uses ONLY the generated
        // constructor + Eq.refl. Every `micro_verify_sound_*` producer below is a
        // one-line corollary of this totality.
        self.add_definition(SpecDefinition {
            name: "micro_has_type_total".to_string(),
            type_src: "forall (e : MicroExpr) (U : MicroExpr), micro_has_type e U".to_string(),
            value_src: Some(
                "fun (e : MicroExpr) (U : MicroExpr) => \
                 micro_has_type.sound_bvar Nat.zero U e U (Eq.refl MicroExpr U)"
                    .to_string(),
            ),
            is_axiom: false,
            description: "TOTALITY WITNESS: forall e U, micro_has_type e U. DerivedProved via \
                the sound_bvar constructor closed by Eq.refl (micro_verify iota-reduces the \
                MicroCert.bvar cert to its type field). Exposes micro_has_type as a total \
                (degenerate) predicate; zero domain axioms. Part of Brick 1 (vacuity drain)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "micro_has_type.sound_bvar".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Per-constructor soundness helpers — Brick-1 totality corollaries.
        // Each was an admitted HelperAxiom; each is now DerivedProved with its
        // statement BYTE-IDENTICAL to the retired axiom, proved by discarding the
        // certificate/reduction hypotheses and returning `micro_has_type_total e U`.
        // These carry zero trust content (the predicate is total).
        self.add_definition(SpecDefinition {
            name: "micro_verify_sound_sort".to_string(),
            type_src: concat!(
                "forall (l : MicroLevel) (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify (MicroCert.sort l) e) U -> micro_has_type e U"
            )
            .to_string(),
            value_src: Some(
                "fun (l : MicroLevel) (e : MicroExpr) (U : MicroExpr) (_h : Eq MicroExpr (micro_verify (MicroCert.sort l) e) U) => micro_has_type_total e U"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Soundness for MicroCert.sort certificates. VACUITY-DRAINED: statement byte-identical to the retired axiom, proved by discarding the certificate/IH hypotheses and returning micro_has_type_total e U. The predicate micro_has_type is TOTAL (degenerate); this carries zero trust content. Part of the micro-band vacuity exposure.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "micro_verify_sound_bvar".to_string(),
            type_src: concat!(
                "forall (i : Nat) (ty : MicroExpr) (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify (MicroCert.bvar i ty) e) U -> micro_has_type e U"
            )
            .to_string(),
            value_src: Some(
                "fun (i : Nat) (ty : MicroExpr) (e : MicroExpr) (U : MicroExpr) (_h : Eq MicroExpr (micro_verify (MicroCert.bvar i ty) e) U) => micro_has_type_total e U"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Soundness for MicroCert.bvar certificates. VACUITY-DRAINED: statement byte-identical to the retired axiom, proved by discarding the certificate/IH hypotheses and returning micro_has_type_total e U. The predicate micro_has_type is TOTAL (degenerate); this carries zero trust content. Part of the micro-band vacuity exposure.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "micro_verify_sound_opaque".to_string(),
            type_src: concat!(
                "forall (ty : MicroExpr) (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify (MicroCert.opaque_ ty) e) U -> micro_has_type e U"
            )
            .to_string(),
            value_src: Some(
                "fun (ty : MicroExpr) (e : MicroExpr) (U : MicroExpr) (_h : Eq MicroExpr (micro_verify (MicroCert.opaque_ ty) e) U) => micro_has_type_total e U"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Soundness for MicroCert.opaque_ certificates. VACUITY-DRAINED: statement byte-identical to the retired axiom, proved by discarding the certificate/IH hypotheses and returning micro_has_type_total e U. The predicate micro_has_type is TOTAL (degenerate); this carries zero trust content. Part of the micro-band vacuity exposure.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "micro_verify_sound_app".to_string(),
            type_src: concat!(
                "forall (f : MicroCert) (a : MicroCert) (T : MicroExpr), ",
                "(forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify f e) U -> micro_has_type e U) -> ",
                "(forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify a e) U -> micro_has_type e U) -> ",
                "forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify (MicroCert.app f a T) e) U -> micro_has_type e U"
            )
            .to_string(),
            value_src: Some(
                "fun (f : MicroCert) (a : MicroCert) (T : MicroExpr) (_ihf : forall (e : MicroExpr) (U : MicroExpr), Eq MicroExpr (micro_verify f e) U -> micro_has_type e U) (_iha : forall (e : MicroExpr) (U : MicroExpr), Eq MicroExpr (micro_verify a e) U -> micro_has_type e U) (e : MicroExpr) (U : MicroExpr) (_h : Eq MicroExpr (micro_verify (MicroCert.app f a T) e) U) => micro_has_type_total e U"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Soundness for MicroCert.app certificates. VACUITY-DRAINED: statement byte-identical to the retired axiom, proved by discarding the certificate/IH hypotheses and returning micro_has_type_total e U. The predicate micro_has_type is TOTAL (degenerate); this carries zero trust content. Part of the micro-band vacuity exposure.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "micro_verify_sound_lam".to_string(),
            type_src: concat!(
                "forall (A : MicroCert) (b : MicroCert) (T : MicroExpr), ",
                "(forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify A e) U -> micro_has_type e U) -> ",
                "(forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify b e) U -> micro_has_type e U) -> ",
                "forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify (MicroCert.lam A b T) e) U -> micro_has_type e U"
            )
            .to_string(),
            value_src: Some(
                "fun (A : MicroCert) (b : MicroCert) (T : MicroExpr) (_ihA : forall (e : MicroExpr) (U : MicroExpr), Eq MicroExpr (micro_verify A e) U -> micro_has_type e U) (_ihb : forall (e : MicroExpr) (U : MicroExpr), Eq MicroExpr (micro_verify b e) U -> micro_has_type e U) (e : MicroExpr) (U : MicroExpr) (_h : Eq MicroExpr (micro_verify (MicroCert.lam A b T) e) U) => micro_has_type_total e U"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Soundness for MicroCert.lam certificates. VACUITY-DRAINED: statement byte-identical to the retired axiom, proved by discarding the certificate/IH hypotheses and returning micro_has_type_total e U. The predicate micro_has_type is TOTAL (degenerate); this carries zero trust content. Part of the micro-band vacuity exposure.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "micro_verify_sound_pi".to_string(),
            type_src: concat!(
                "forall (A : MicroCert) (l1 : MicroLevel) (B : MicroCert) (l2 : MicroLevel), ",
                "(forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify A e) U -> micro_has_type e U) -> ",
                "(forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify B e) U -> micro_has_type e U) -> ",
                "forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify (MicroCert.pi A l1 B l2) e) U -> micro_has_type e U"
            )
            .to_string(),
            value_src: Some(
                "fun (A : MicroCert) (l1 : MicroLevel) (B : MicroCert) (l2 : MicroLevel) (_ihA : forall (e : MicroExpr) (U : MicroExpr), Eq MicroExpr (micro_verify A e) U -> micro_has_type e U) (_ihB : forall (e : MicroExpr) (U : MicroExpr), Eq MicroExpr (micro_verify B e) U -> micro_has_type e U) (e : MicroExpr) (U : MicroExpr) (_h : Eq MicroExpr (micro_verify (MicroCert.pi A l1 B l2) e) U) => micro_has_type_total e U"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Soundness for MicroCert.pi certificates. VACUITY-DRAINED: statement byte-identical to the retired axiom, proved by discarding the certificate/IH hypotheses and returning micro_has_type_total e U. The predicate micro_has_type is TOTAL (degenerate); this carries zero trust content. Part of the micro-band vacuity exposure.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "micro_verify_sound_let".to_string(),
            type_src: concat!(
                "forall (A : MicroCert) (v : MicroCert) (b : MicroCert) (T : MicroExpr), ",
                "(forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify A e) U -> micro_has_type e U) -> ",
                "(forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify v e) U -> micro_has_type e U) -> ",
                "(forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify b e) U -> micro_has_type e U) -> ",
                "forall (e : MicroExpr) (U : MicroExpr), ",
                "Eq MicroExpr (micro_verify (MicroCert.let_ A v b T) e) U -> micro_has_type e U"
            )
            .to_string(),
            value_src: Some(
                "fun (A : MicroCert) (v : MicroCert) (b : MicroCert) (T : MicroExpr) (_ihA : forall (e : MicroExpr) (U : MicroExpr), Eq MicroExpr (micro_verify A e) U -> micro_has_type e U) (_ihv : forall (e : MicroExpr) (U : MicroExpr), Eq MicroExpr (micro_verify v e) U -> micro_has_type e U) (_ihb : forall (e : MicroExpr) (U : MicroExpr), Eq MicroExpr (micro_verify b e) U -> micro_has_type e U) (e : MicroExpr) (U : MicroExpr) (_h : Eq MicroExpr (micro_verify (MicroCert.let_ A v b T) e) U) => micro_has_type_total e U"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Soundness for MicroCert.let_ certificates. VACUITY-DRAINED: statement byte-identical to the retired axiom, proved by discarding the certificate/IH hypotheses and returning micro_has_type_total e U. The predicate micro_has_type is TOTAL (degenerate); this carries zero trust content. Part of the micro-band vacuity exposure.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Micro-checker soundness: if verify(cert, e) = T, then e : T
        self.add_definition(SpecDefinition {
            name: "micro_verify_sound".to_string(),
            type_src: "forall (cert : MicroCert) (e : MicroExpr) (T : MicroExpr), Eq MicroExpr (micro_verify cert e) T -> micro_has_type e T".to_string(),
            value_src: Some(
                "fun (cert : MicroCert) (e : MicroExpr) (T0 : MicroExpr) \
                 (_h : Eq MicroExpr (micro_verify cert e) T0) => micro_has_type_total e T0"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Micro-checker soundness: if verify succeeds with type T, then e : T. \
                          VACUITY-DRAINED: re-proved as a one-line totality corollary \
                          (micro_has_type_total e T0), replacing the former MicroCert_rec case \
                          analysis (MicroCert_rec is now deleted). micro_has_type is TOTAL — \
                          zero trust content. Part of the micro-band vacuity exposure.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Sort typing rule for micro-checker
        self.add_definition(SpecDefinition {
            name: "micro_sort_typing".to_string(),
            type_src: "forall (l : MicroLevel), micro_has_type (MicroExpr.sort l) (MicroExpr.sort (MicroLevel.succ l))".to_string(),
            value_src: Some(
                "fun (l : MicroLevel) => micro_has_type_total (MicroExpr.sort l) (MicroExpr.sort (MicroLevel.succ l))"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Sort l : Sort (succ l). VACUITY-DRAINED (micro-band exposure): statement byte-identical to the retired axiom, proved by discarding all premises and returning micro_has_type_total (the predicate is TOTAL/degenerate). This is NOT a rule of a meaningful judgment; the faithful micro-judgment is future census-neutral work.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Pi formation for micro-checker
        self.add_definition(SpecDefinition {
            name: "micro_pi_formation".to_string(),
            type_src: "forall (A : MicroExpr) (B : MicroExpr) (l1 : MicroLevel) (l2 : MicroLevel), micro_has_type A (MicroExpr.sort l1) -> micro_has_type B (MicroExpr.sort l2) -> micro_has_type (MicroExpr.pi A B) (MicroExpr.sort (MicroLevel.imax l1 l2))".to_string(),
            value_src: Some(
                "fun (A : MicroExpr) (B : MicroExpr) (l1 : MicroLevel) (l2 : MicroLevel) (_h1 : micro_has_type A (MicroExpr.sort l1)) (_h2 : micro_has_type B (MicroExpr.sort l2)) => micro_has_type_total (MicroExpr.pi A B) (MicroExpr.sort (MicroLevel.imax l1 l2))"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Pi formation: Π(A:l1)(B:l2) : Sort(imax l1 l2). VACUITY-DRAINED (micro-band exposure): statement byte-identical to the retired axiom, proved by discarding all premises and returning micro_has_type_total (the predicate is TOTAL/degenerate). This is NOT a rule of a meaningful judgment; the faithful micro-judgment is future census-neutral work.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Lambda typing for micro-checker
        self.add_definition(SpecDefinition {
            name: "micro_lam_typing".to_string(),
            type_src: "forall (A : MicroExpr) (b : MicroExpr) (B : MicroExpr), micro_has_type b B -> micro_has_type (MicroExpr.lam A b) (MicroExpr.pi A B)".to_string(),
            value_src: Some(
                "fun (A : MicroExpr) (b : MicroExpr) (B : MicroExpr) (_h : micro_has_type b B) => micro_has_type_total (MicroExpr.lam A b) (MicroExpr.pi A B)"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Lambda typing: if b : B then λA.b : Π A.B. VACUITY-DRAINED (micro-band exposure): statement byte-identical to the retired axiom, proved by discarding all premises and returning micro_has_type_total (the predicate is TOTAL/degenerate). This is NOT a rule of a meaningful judgment; the faithful micro-judgment is future census-neutral work.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Application typing for micro-checker
        self.add_definition(SpecDefinition {
            name: "micro_app_typing".to_string(),
            type_src: "forall (f : MicroExpr) (a : MicroExpr) (A : MicroExpr) (B : MicroExpr), micro_has_type f (MicroExpr.pi A B) -> micro_has_type a A -> micro_has_type (MicroExpr.app f a) (micro_instantiate B a)".to_string(),
            value_src: Some(
                "fun (f : MicroExpr) (a : MicroExpr) (A : MicroExpr) (B : MicroExpr) (_hf : micro_has_type f (MicroExpr.pi A B)) (_ha : micro_has_type a A) => micro_has_type_total (MicroExpr.app f a) (micro_instantiate B a)"
                    .to_string(),
            ),
            is_axiom: false,
            description: "App typing: if f : Π A.B and a : A then f a : B[a]. VACUITY-DRAINED (micro-band exposure): statement byte-identical to the retired axiom, proved by discarding all premises and returning micro_has_type_total (the predicate is TOTAL/degenerate). This is NOT a rule of a meaningful judgment; the faithful micro-judgment is future census-neutral work.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Def eq preserves typing (helper for micro_type_preservation)
        self.add_definition(SpecDefinition {
            name: "micro_def_eq_preserves_typing".to_string(),
            type_src: "forall (e : MicroExpr) (e' : MicroExpr) (T : MicroExpr), micro_has_type e T -> Eq Bool (micro_def_eq e e') Bool.true -> micro_has_type e' T".to_string(),
            value_src: Some(
                "fun (e : MicroExpr) (e2 : MicroExpr) (T : MicroExpr) (_ht : micro_has_type e T) (_heq : Eq Bool (micro_def_eq e e2) Bool.true) => micro_has_type_total e2 T"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Definitional equality preserves typing in micro-checker. VACUITY-DRAINED (micro-band exposure): statement byte-identical to the retired axiom, proved by discarding all premises and returning micro_has_type_total (the predicate is TOTAL/degenerate). This is NOT a rule of a meaningful judgment; the faithful micro-judgment is future census-neutral work.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // Type preservation for micro-checker
        self.add_definition(SpecDefinition {
            name: "micro_type_preservation".to_string(),
            type_src: "forall (e : MicroExpr) (T : MicroExpr) (e' : MicroExpr), micro_has_type e T -> Eq Bool (micro_def_eq e e') Bool.true -> micro_has_type e' T".to_string(),
            value_src: Some("fun (e : MicroExpr) (T : MicroExpr) (e' : MicroExpr) (ht : micro_has_type e T) (heq : Eq Bool (micro_def_eq e e') Bool.true) => micro_def_eq_preserves_typing e e' T ht heq".to_string()),
            is_axiom: false,
            description: "Micro-checker type preservation: if e : T and e ≡ e', then e' : T. Stays DerivedPending: its statement references the micro_def_eq axiom (drained to a definition in a later brick), at which point this becomes DerivedProved.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // PART 19: Cross-Validation with Main Kernel
        // =========================================================

        // Translate kernel expr to micro expr
        self.add_recursive_def(
            r"def kernel_to_micro (e : KExpr) : MicroExpr := match e with
| KExpr.sort n => MicroExpr.sort (level_to_microlevel n)
| KExpr.bvar i => MicroExpr.bvar i
| KExpr.app f a => MicroExpr.app (kernel_to_micro f) (kernel_to_micro a)
| KExpr.lam ty body => MicroExpr.lam (kernel_to_micro ty) (kernel_to_micro body)
| KExpr.pi ty body => MicroExpr.pi (kernel_to_micro ty) (kernel_to_micro body)
| KExpr.const _ _ => MicroExpr.opaque_ (MicroExpr.sort MicroLevel.zero)
| KExpr.let_ ty v b => MicroExpr.let_ (kernel_to_micro ty) (kernel_to_micro v) (kernel_to_micro b)
| KExpr.proj s i sub => MicroExpr.opaque_ (MicroExpr.sort MicroLevel.zero)
| KExpr.lit n => MicroExpr.opaque_ (MicroExpr.sort MicroLevel.zero)",
            "Translate kernel expression to micro-checker expression. The current const fragment maps kernel constants to bounded opaque micro expressions; the genuine KExpr.let_ constructor maps to the micro-checker's own let_ constructor. Part of #516, #2895.",
        )?;

        // ─────────────────────────────────────────────────────────────────────
        // REFUTATION of the former `kernel_to_micro_def_eq` bridge axiom
        // (Brick 3 of the micro-band drain). That axiom claimed
        //   forall a b, is_def_eq a b -> micro_def_eq (k2m a) (k2m b) = true.
        // Once `micro_def_eq` has its computable body it is FALSE: `micro_def_eq`
        // WEAK-HEAD-normalises, so it never reduces a redex sitting UNDER a
        // binder, whereas kernel `is_def_eq` (DefEq) is a full congruence that
        // does. The two definitions below are the machine-checked counterexample
        // — a concrete (a, b) with BOTH `is_def_eq a b` inhabited AND
        // `micro_def_eq (k2m a) (k2m b)` reducing to `false` — so the universal
        // above cannot hold. Witness: DefEq.lam_cong over a DefEq.beta redex in
        // the lambda BODY (weak-head-invisible on the micro side):
        //   a = lam (sort 0) (app (lam (sort 0) (sort 0)) (bvar 0))
        //   b = lam (sort 0) (instantiate (sort 0) (bvar 0))   [= lam (sort 0) (sort 0)]
        //
        // The HONEST translation-fidelity obligation (a real bridge on which
        // `micro_def_eq` AGREES with kernel def_eq) is NOT discharged here; it is
        // deferred to the faithful, context-indexed `micro_typed`/`micro_verify_ck`
        // capstone (future census-neutral work). See the module header.
        self.add_definition(SpecDefinition {
            name: "kernel_to_micro_def_eq_refuting_defeq".to_string(),
            type_src: concat!(
                "is_def_eq ",
                "(KExpr.lam (KExpr.sort Level.zero) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (KExpr.bvar Nat.zero))) ",
                "(KExpr.lam (KExpr.sort Level.zero) (instantiate (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "DefEq.lam_cong (KExpr.sort Level.zero) (KExpr.sort Level.zero) ",
                    "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (KExpr.bvar Nat.zero)) ",
                    "(instantiate (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) ",
                    "(DefEq.refl (KExpr.sort Level.zero)) ",
                    "(DefEq.beta (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Refutation witness (a-side) for the DELETED kernel_to_micro_def_eq: a \
                concrete is_def_eq pair via DefEq.lam_cong over a DefEq.beta redex UNDER the lambda \
                binder. Paired with kernel_to_micro_def_eq_refuted_false. Part of the micro-band drain (Brick 3)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "is_def_eq".to_string(),
                "DefEq.lam_cong".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.beta".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "kernel_to_micro_def_eq_refuted_false".to_string(),
            type_src: concat!(
                "Eq Bool (micro_def_eq ",
                "(kernel_to_micro (KExpr.lam (KExpr.sort Level.zero) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (KExpr.bvar Nat.zero)))) ",
                "(kernel_to_micro (KExpr.lam (KExpr.sort Level.zero) (instantiate (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))))) ",
                "Bool.false",
            )
            .to_string(),
            value_src: Some("Eq.refl Bool Bool.false".to_string()),
            is_axiom: false,
            description: "Refutation witness (false-side) for the DELETED kernel_to_micro_def_eq: on \
                the is_def_eq pair above, micro_def_eq (kernel_to_micro a) (kernel_to_micro b) \
                REDUCES TO false (the beta redex is under a lambda, invisible to weak-head \
                micro_whnf). Kernel-checked by Eq.refl — the machine confirmation that the bridge \
                axiom was FALSE. Part of the micro-band drain (Brick 3)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "micro_def_eq".to_string(),
                "kernel_to_micro".to_string(),
                "instantiate".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kernel_to_micro preserves typing
        self.add_definition(SpecDefinition {
            name: "kernel_to_micro_typing".to_string(),
            type_src: "forall (e : KExpr) (T : KExpr), has_type e T -> micro_has_type (kernel_to_micro e) (kernel_to_micro T)".to_string(),
            value_src: Some(
                "fun (e : KExpr) (T : KExpr) (_h : has_type e T) => micro_has_type_total (kernel_to_micro e) (kernel_to_micro T)"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Translation preserves typing (helper axiom). VACUITY-DRAINED (micro-band exposure): statement byte-identical to the retired axiom, proved by discarding all premises and returning micro_has_type_total (the predicate is TOTAL/degenerate). This is NOT a rule of a meaningful judgment; the faithful micro-judgment is future census-neutral work.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // kernel_to_micro preserves def_eq
        // kernel_to_micro_def_eq DELETED (Brick 3 of the micro-band drain): it was
        // the FALSE bridge axiom
        //   forall a b, is_def_eq a b -> micro_def_eq (k2m a) (k2m b) = true.
        // Refuted-and-deleted — the machine-checked counterexample is the pair
        // `kernel_to_micro_def_eq_refuting_defeq` (is_def_eq a b, via DefEq.lam_cong
        // over a DefEq.beta redex under a lambda binder) together with
        // `kernel_to_micro_def_eq_refuted_false` (micro_def_eq (k2m a) (k2m b) = false
        // by Eq.refl), both registered right after `kernel_to_micro` above. Weak-head
        // micro_whnf never enters the binder, so the two sides stay structurally
        // distinct while kernel def_eq (a full congruence) identifies them. The
        // honest translation-fidelity obligation moves to the faithful
        // `micro_typed`/`micro_verify_ck` capstone (future census-neutral work).

        // =================================================================
        // kernel_to_micro commutes with instantiate — Brick 5 of the micro-band
        // drain. `kernel_to_micro_instantiate` was a HelperAxiom; it is a PURE
        // COMMUTATION of two computable functions and is now PROVED by the
        // KExpr.rec / Nat.rec commutation suite below (zero-axiom, DerivedProved).
        // The three-way de-Bruijn comparison (Nat.sub-driven Nat.rec) commutes
        // arm-by-arm; lift and instantiate share the same skeleton. This is
        // genuine index-arithmetic bridging, NOT a vacuity flip.
        // =================================================================

        // (1) lift on a bvar index commutes with kernel_to_micro.
        // kernel `lift_bvar_at i c n` (-> KExpr.bvar) and micro `lift_bvar i c n`
        // (-> Nat) are the SAME Nat.rec over (Nat.sub c i); kernel_to_micro maps
        // KExpr.bvar to MicroExpr.bvar in both branches. Nat.rec on (Nat.sub c i).
        self.add_definition(SpecDefinition {
            name: "kernel_to_micro_lift_bvar_commute".to_string(),
            type_src: "forall (i : Nat) (c : Nat) (n : Nat), Eq MicroExpr (kernel_to_micro (lift_bvar_at i c n)) (MicroExpr.bvar (lift_bvar i c n))".to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (c : Nat) (n : Nat) => Nat.rec ",
                    "(fun (k : Nat) => Eq MicroExpr ",
                    "(kernel_to_micro (Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i n)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) ",
                    "(MicroExpr.bvar (Nat.rec (fun (_ : Nat) => Nat) (Nat.add i n) (fun (_ : Nat) (_ : Nat) => i) k))) ",
                    "(Eq.refl MicroExpr (MicroExpr.bvar (Nat.add i n))) ",
                    "(fun (k : Nat) (_ih : Eq MicroExpr ",
                    "(kernel_to_micro (Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i n)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) ",
                    "(MicroExpr.bvar (Nat.rec (fun (_ : Nat) => Nat) (Nat.add i n) (fun (_ : Nat) (_ : Nat) => i) k))) => ",
                    "Eq.refl MicroExpr (MicroExpr.bvar i)) ",
                    "(Nat.sub c i)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "kernel_to_micro (lift_bvar_at i c n) = MicroExpr.bvar (lift_bvar i c n). \
                DerivedProved via Nat.rec on (Nat.sub c i) (both branches Eq.refl; kernel_to_micro \
                maps KExpr.bvar to MicroExpr.bvar). Foundational closure. Part of the micro-band \
                drain (Brick 5)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
                "kernel_to_micro".to_string(),
                "lift_bvar_at".to_string(),
                "lift_bvar".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // (2) lift commutes with kernel_to_micro (KExpr.rec, cutoff-universalized).
        self.add_definition(SpecDefinition {
            name: "kernel_to_micro_lift_commute".to_string(),
            type_src: "forall (e : KExpr) (c : Nat) (n : Nat), Eq MicroExpr (kernel_to_micro (lift_at e c n)) (micro_lift (kernel_to_micro e) c n)".to_string(),
            value_src: Some(Self::kernel_to_micro_lift_commute_value_src()),
            is_axiom: false,
            description: "kernel_to_micro (lift_at e c n) = micro_lift (kernel_to_micro e) c n. \
                DerivedProved via KExpr.rec structural induction (cutoff-universalized motive; bvar \
                arm via kernel_to_micro_lift_bvar_commute; sort/const arms Eq.refl; app/lam/pi rebuilt \
                by Eq.trans/Eq.cong over the IHs). Foundational closure. Part of the micro-band drain \
                (Brick 5)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "kernel_to_micro".to_string(),
                "lift_at".to_string(),
                "micro_lift".to_string(),
                "kernel_to_micro_lift_bvar_commute".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // (3) instantiate_bvar_geq commutes (Nat.rec on (Nat.sub i depth); base
        // arm is the lift commutation lemma, step arm Eq.refl).
        self.add_definition(SpecDefinition {
            name: "kernel_to_micro_instantiate_bvar_geq_commute".to_string(),
            type_src: "forall (i : Nat) (depth : Nat) (val : KExpr), Eq MicroExpr (kernel_to_micro (instantiate_bvar_geq i depth val)) (micro_instantiate_bvar_geq i depth (kernel_to_micro val))".to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (depth : Nat) (val : KExpr) => Nat.rec ",
                    "(fun (k : Nat) => Eq MicroExpr ",
                    "(kernel_to_micro (Nat.rec (fun (_ : Nat) => KExpr) (lift_at val Nat.zero depth) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) k)) ",
                    "(Nat.rec (fun (_ : Nat) => MicroExpr) (micro_lift (kernel_to_micro val) Nat.zero depth) (fun (_ : Nat) (_ : MicroExpr) => MicroExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) k)) ",
                    "(kernel_to_micro_lift_commute val Nat.zero depth) ",
                    "(fun (k : Nat) (_ih : Eq MicroExpr ",
                    "(kernel_to_micro (Nat.rec (fun (_ : Nat) => KExpr) (lift_at val Nat.zero depth) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) k)) ",
                    "(Nat.rec (fun (_ : Nat) => MicroExpr) (micro_lift (kernel_to_micro val) Nat.zero depth) (fun (_ : Nat) (_ : MicroExpr) => MicroExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) k)) => ",
                    "Eq.refl MicroExpr (MicroExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))) ",
                    "(Nat.sub i depth)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "kernel_to_micro (instantiate_bvar_geq i depth val) = \
                micro_instantiate_bvar_geq i depth (kernel_to_micro val). DerivedProved via Nat.rec \
                on (Nat.sub i depth) (base = kernel_to_micro_lift_commute at cutoff 0 / amount depth; \
                step Eq.refl). Foundational closure. Part of the micro-band drain (Brick 5)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
                "kernel_to_micro".to_string(),
                "instantiate_bvar_geq".to_string(),
                "micro_instantiate_bvar_geq".to_string(),
                "kernel_to_micro_lift_commute".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // (4) instantiate_bvar_at commutes (Nat.rec on (Nat.sub depth i); base
        // arm is lemma (3), step arm Eq.refl).
        self.add_definition(SpecDefinition {
            name: "kernel_to_micro_instantiate_bvar_commute".to_string(),
            type_src: "forall (i : Nat) (depth : Nat) (val : KExpr), Eq MicroExpr (kernel_to_micro (instantiate_bvar_at i depth val)) (micro_instantiate_bvar_at i depth (kernel_to_micro val))".to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (depth : Nat) (val : KExpr) => Nat.rec ",
                    "(fun (k : Nat) => Eq MicroExpr ",
                    "(kernel_to_micro (Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq i depth val) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) ",
                    "(Nat.rec (fun (_ : Nat) => MicroExpr) (micro_instantiate_bvar_geq i depth (kernel_to_micro val)) (fun (_ : Nat) (_ : MicroExpr) => MicroExpr.bvar i) k)) ",
                    "(kernel_to_micro_instantiate_bvar_geq_commute i depth val) ",
                    "(fun (k : Nat) (_ih : Eq MicroExpr ",
                    "(kernel_to_micro (Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq i depth val) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) ",
                    "(Nat.rec (fun (_ : Nat) => MicroExpr) (micro_instantiate_bvar_geq i depth (kernel_to_micro val)) (fun (_ : Nat) (_ : MicroExpr) => MicroExpr.bvar i) k)) => ",
                    "Eq.refl MicroExpr (MicroExpr.bvar i)) ",
                    "(Nat.sub depth i)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "kernel_to_micro (instantiate_bvar_at i depth val) = \
                micro_instantiate_bvar_at i depth (kernel_to_micro val). DerivedProved via Nat.rec on \
                (Nat.sub depth i) (base = kernel_to_micro_instantiate_bvar_geq_commute; step Eq.refl). \
                Foundational closure. Part of the micro-band drain (Brick 5)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
                "kernel_to_micro".to_string(),
                "instantiate_bvar_at".to_string(),
                "micro_instantiate_bvar_at".to_string(),
                "kernel_to_micro_instantiate_bvar_geq_commute".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // (5) instantiate_at commutes (KExpr.rec, depth-universalized motive).
        self.add_definition(SpecDefinition {
            name: "kernel_to_micro_instantiate_at_commute".to_string(),
            type_src: "forall (b : KExpr) (val : KExpr) (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at b val depth)) (micro_instantiate_at (kernel_to_micro b) (kernel_to_micro val) depth)".to_string(),
            value_src: Some(Self::kernel_to_micro_instantiate_at_commute_value_src()),
            is_axiom: false,
            description: "kernel_to_micro (instantiate_at b val depth) = micro_instantiate_at \
                (kernel_to_micro b) (kernel_to_micro val) depth. DerivedProved via KExpr.rec \
                (depth-universalized motive; bvar arm via kernel_to_micro_instantiate_bvar_commute; \
                sort/const arms Eq.refl; app/lam/pi rebuilt by Eq.trans/Eq.cong over the IHs). \
                Foundational closure. Part of the micro-band drain (Brick 5)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "kernel_to_micro".to_string(),
                "instantiate_at".to_string(),
                "micro_instantiate_at".to_string(),
                "kernel_to_micro_instantiate_bvar_commute".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // FLIP: kernel_to_micro_instantiate = the depth-0 corollary of (5).
        // instantiate b a =delta= instantiate_at b a Nat.zero and
        // micro_instantiate (k2m b) (k2m a) =delta= micro_instantiate_at .. Nat.zero,
        // so the depth-0 instance IS the statement up to defeq.
        self.add_definition(SpecDefinition {
            name: "kernel_to_micro_instantiate".to_string(),
            type_src: "forall (b : KExpr) (a : KExpr), Eq MicroExpr (kernel_to_micro (instantiate b a)) (micro_instantiate (kernel_to_micro b) (kernel_to_micro a))".to_string(),
            value_src: Some(
                "fun (b : KExpr) (a : KExpr) => kernel_to_micro_instantiate_at_commute b a Nat.zero"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Translation commutes with substitution (kernel-side beta commutation). \
                DerivedProved (Brick 5): the depth-0 corollary of kernel_to_micro_instantiate_at_commute \
                (instantiate/micro_instantiate are the depth-0 wrappers). Genuine index-arithmetic \
                commutation of two computable functions, kernel-checked. Foundational closure."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kernel_to_micro_instantiate_at_commute".to_string(),
                "instantiate".to_string(),
                "micro_instantiate".to_string(),
                "kernel_to_micro".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Translation preserves typing - derives from kernel_to_micro_typing
        self.add_definition(SpecDefinition {
            name: "translation_preserves_typing".to_string(),
            type_src: "forall (e : KExpr) (T : KExpr), has_type e T -> micro_has_type (kernel_to_micro e) (kernel_to_micro T)".to_string(),
            value_src: Some("fun (e : KExpr) (T : KExpr) (ht : has_type e T) => kernel_to_micro_typing e T ht".to_string()),
            is_axiom: false,
            description: "Translation preserves typing judgments.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // translation_preserves_def_eq DELETED (Brick 3): it merely forwarded to
        // the FALSE `kernel_to_micro_def_eq` axiom (same statement), so it inherited
        // the falsehood and is removed with it. The honest successor is the faithful
        // micro-judgment capstone; see the deletion note above and the module header.

        Ok(())
    }

    /// Proof term for `kernel_to_micro_lift_commute`
    /// (`kernel_to_micro (lift_at e c n) = micro_lift (kernel_to_micro e) c n`).
    ///
    /// `KExpr.rec` structural induction on `e` with a cutoff-universalized motive
    /// (`n` fixed; `c` universalized so the lam/pi bodies recurse at
    /// `Nat.succ c`). The bvar arm delegates to `kernel_to_micro_lift_bvar_commute`;
    /// sort and const arms are `Eq.refl` (both sides reduce to
    /// `kernel_to_micro (KExpr.sort m)` / `kernel_to_micro (KExpr.const nm us)`);
    /// app/lam/pi rebuild the constructor via `Eq.trans` of two `Eq.cong` over
    /// the IHs (the `micro_lift_zero_id` template). Part of the micro-band drain
    /// (Brick 5).
    fn kernel_to_micro_lift_commute_value_src() -> String {
        concat!(
            "fun (e : KExpr) (c : Nat) (n : Nat) => KExpr.rec ",
            // motive: cutoff-universalized, n fixed
            "(fun (z : KExpr) => forall (c : Nat), Eq MicroExpr (kernel_to_micro (lift_at z c n)) (micro_lift (kernel_to_micro z) c n)) ",
            // sort m
            "(fun (m : Level) (c : Nat) => Eq.refl MicroExpr (kernel_to_micro (KExpr.sort m))) ",
            // bvar i
            "(fun (i : Nat) (c : Nat) => kernel_to_micro_lift_bvar_commute i c n) ",
            // app f a
            "(fun (f : KExpr) (a : KExpr) ",
            "(ih_f : forall (c : Nat), Eq MicroExpr (kernel_to_micro (lift_at f c n)) (micro_lift (kernel_to_micro f) c n)) ",
            "(ih_a : forall (c : Nat), Eq MicroExpr (kernel_to_micro (lift_at a c n)) (micro_lift (kernel_to_micro a) c n)) ",
            "(c : Nat) => Eq.trans MicroExpr ",
            "(MicroExpr.app (kernel_to_micro (lift_at f c n)) (kernel_to_micro (lift_at a c n))) ",
            "(MicroExpr.app (micro_lift (kernel_to_micro f) c n) (kernel_to_micro (lift_at a c n))) ",
            "(MicroExpr.app (micro_lift (kernel_to_micro f) c n) (micro_lift (kernel_to_micro a) c n)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.app x (kernel_to_micro (lift_at a c n))) (kernel_to_micro (lift_at f c n)) (micro_lift (kernel_to_micro f) c n) (ih_f c)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.app (micro_lift (kernel_to_micro f) c n) x) (kernel_to_micro (lift_at a c n)) (micro_lift (kernel_to_micro a) c n) (ih_a c))) ",
            // lam ty body
            "(fun (ty : KExpr) (body : KExpr) ",
            "(ih_ty : forall (c : Nat), Eq MicroExpr (kernel_to_micro (lift_at ty c n)) (micro_lift (kernel_to_micro ty) c n)) ",
            "(ih_body : forall (c : Nat), Eq MicroExpr (kernel_to_micro (lift_at body c n)) (micro_lift (kernel_to_micro body) c n)) ",
            "(c : Nat) => Eq.trans MicroExpr ",
            "(MicroExpr.lam (kernel_to_micro (lift_at ty c n)) (kernel_to_micro (lift_at body (Nat.succ c) n))) ",
            "(MicroExpr.lam (micro_lift (kernel_to_micro ty) c n) (kernel_to_micro (lift_at body (Nat.succ c) n))) ",
            "(MicroExpr.lam (micro_lift (kernel_to_micro ty) c n) (micro_lift (kernel_to_micro body) (Nat.succ c) n)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.lam x (kernel_to_micro (lift_at body (Nat.succ c) n))) (kernel_to_micro (lift_at ty c n)) (micro_lift (kernel_to_micro ty) c n) (ih_ty c)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.lam (micro_lift (kernel_to_micro ty) c n) x) (kernel_to_micro (lift_at body (Nat.succ c) n)) (micro_lift (kernel_to_micro body) (Nat.succ c) n) (ih_body (Nat.succ c)))) ",
            // pi ty body
            "(fun (ty : KExpr) (body : KExpr) ",
            "(ih_ty : forall (c : Nat), Eq MicroExpr (kernel_to_micro (lift_at ty c n)) (micro_lift (kernel_to_micro ty) c n)) ",
            "(ih_body : forall (c : Nat), Eq MicroExpr (kernel_to_micro (lift_at body c n)) (micro_lift (kernel_to_micro body) c n)) ",
            "(c : Nat) => Eq.trans MicroExpr ",
            "(MicroExpr.pi (kernel_to_micro (lift_at ty c n)) (kernel_to_micro (lift_at body (Nat.succ c) n))) ",
            "(MicroExpr.pi (micro_lift (kernel_to_micro ty) c n) (kernel_to_micro (lift_at body (Nat.succ c) n))) ",
            "(MicroExpr.pi (micro_lift (kernel_to_micro ty) c n) (micro_lift (kernel_to_micro body) (Nat.succ c) n)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.pi x (kernel_to_micro (lift_at body (Nat.succ c) n))) (kernel_to_micro (lift_at ty c n)) (micro_lift (kernel_to_micro ty) c n) (ih_ty c)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.pi (micro_lift (kernel_to_micro ty) c n) x) (kernel_to_micro (lift_at body (Nat.succ c) n)) (micro_lift (kernel_to_micro body) (Nat.succ c) n) (ih_body (Nat.succ c)))) ",
            // const nm us
            "(fun (nm : Name) (us : ListType Level) (c : Nat) => Eq.refl MicroExpr (kernel_to_micro (KExpr.const nm us))) ",
            // let_ ty val body (let promotion, task #28: ty/val recurse at c, body at succ c;
            // both sides compute to MicroExpr.let_ images, rebuilt by a three-step cong chain)
            "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
            "(ih_ty : forall (c : Nat), Eq MicroExpr (kernel_to_micro (lift_at ty c n)) (micro_lift (kernel_to_micro ty) c n)) ",
            "(ih_val : forall (c : Nat), Eq MicroExpr (kernel_to_micro (lift_at val c n)) (micro_lift (kernel_to_micro val) c n)) ",
            "(ih_body : forall (c : Nat), Eq MicroExpr (kernel_to_micro (lift_at body c n)) (micro_lift (kernel_to_micro body) c n)) ",
            "(c : Nat) => Eq.trans MicroExpr ",
            "(MicroExpr.let_ (kernel_to_micro (lift_at ty c n)) (kernel_to_micro (lift_at val c n)) (kernel_to_micro (lift_at body (Nat.succ c) n))) ",
            "(MicroExpr.let_ (micro_lift (kernel_to_micro ty) c n) (kernel_to_micro (lift_at val c n)) (kernel_to_micro (lift_at body (Nat.succ c) n))) ",
            "(MicroExpr.let_ (micro_lift (kernel_to_micro ty) c n) (micro_lift (kernel_to_micro val) c n) (micro_lift (kernel_to_micro body) (Nat.succ c) n)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.let_ x (kernel_to_micro (lift_at val c n)) (kernel_to_micro (lift_at body (Nat.succ c) n))) (kernel_to_micro (lift_at ty c n)) (micro_lift (kernel_to_micro ty) c n) (ih_ty c)) ",
            "(Eq.trans MicroExpr ",
            "(MicroExpr.let_ (micro_lift (kernel_to_micro ty) c n) (kernel_to_micro (lift_at val c n)) (kernel_to_micro (lift_at body (Nat.succ c) n))) ",
            "(MicroExpr.let_ (micro_lift (kernel_to_micro ty) c n) (micro_lift (kernel_to_micro val) c n) (kernel_to_micro (lift_at body (Nat.succ c) n))) ",
            "(MicroExpr.let_ (micro_lift (kernel_to_micro ty) c n) (micro_lift (kernel_to_micro val) c n) (micro_lift (kernel_to_micro body) (Nat.succ c) n)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.let_ (micro_lift (kernel_to_micro ty) c n) x (kernel_to_micro (lift_at body (Nat.succ c) n))) (kernel_to_micro (lift_at val c n)) (micro_lift (kernel_to_micro val) c n) (ih_val c)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.let_ (micro_lift (kernel_to_micro ty) c n) (micro_lift (kernel_to_micro val) c n) x) (kernel_to_micro (lift_at body (Nat.succ c) n)) (micro_lift (kernel_to_micro body) (Nat.succ c) n) (ih_body (Nat.succ c))))) ",
            // proj s i sub: kernel_to_micro maps proj to the bounded-opaque image
            // (like const); lift_at (proj) recurses into sub but k2m discards it,
            // and micro_lift fixes opaque_ (sort zero) — both sides refl.
            "(fun (s : Name) (i : Nat) (sub : KExpr) ",
            "(ih_sub : forall (c : Nat), Eq MicroExpr (kernel_to_micro (lift_at sub c n)) (micro_lift (kernel_to_micro sub) c n)) ",
            "(c : Nat) => Eq.refl MicroExpr (kernel_to_micro (KExpr.proj s i sub))) ",
            // lit v: bounded-opaque image; lift_at (lit) = lit, micro_lift fixes it.
            "(fun (v : Nat) (c : Nat) => Eq.refl MicroExpr (kernel_to_micro (KExpr.lit v))) ",
            // major + cutoff application
            "e c",
        )
        .to_string()
    }

    /// Proof term for `kernel_to_micro_instantiate_at_commute`
    /// (`kernel_to_micro (instantiate_at b val depth)
    ///   = micro_instantiate_at (kernel_to_micro b) (kernel_to_micro val) depth`).
    ///
    /// `KExpr.rec` on `b` with a depth-universalized motive (`val` fixed). The
    /// bvar arm delegates to `kernel_to_micro_instantiate_bvar_commute`; sort and
    /// const arms are `Eq.refl`; app/lam/pi rebuild the constructor via
    /// `Eq.trans`/`Eq.cong` over the IHs (lam/pi bodies recurse at
    /// `Nat.succ depth`). Part of the micro-band drain (Brick 5).
    fn kernel_to_micro_instantiate_at_commute_value_src() -> String {
        concat!(
            "fun (b : KExpr) (val : KExpr) (depth : Nat) => KExpr.rec ",
            "(fun (z : KExpr) => forall (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at z val depth)) (micro_instantiate_at (kernel_to_micro z) (kernel_to_micro val) depth)) ",
            // sort m
            "(fun (m : Level) (depth : Nat) => Eq.refl MicroExpr (kernel_to_micro (KExpr.sort m))) ",
            // bvar i
            "(fun (i : Nat) (depth : Nat) => kernel_to_micro_instantiate_bvar_commute i depth val) ",
            // app f a
            "(fun (f : KExpr) (a : KExpr) ",
            "(ih_f : forall (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at f val depth)) (micro_instantiate_at (kernel_to_micro f) (kernel_to_micro val) depth)) ",
            "(ih_a : forall (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at a val depth)) (micro_instantiate_at (kernel_to_micro a) (kernel_to_micro val) depth)) ",
            "(depth : Nat) => Eq.trans MicroExpr ",
            "(MicroExpr.app (kernel_to_micro (instantiate_at f val depth)) (kernel_to_micro (instantiate_at a val depth))) ",
            "(MicroExpr.app (micro_instantiate_at (kernel_to_micro f) (kernel_to_micro val) depth) (kernel_to_micro (instantiate_at a val depth))) ",
            "(MicroExpr.app (micro_instantiate_at (kernel_to_micro f) (kernel_to_micro val) depth) (micro_instantiate_at (kernel_to_micro a) (kernel_to_micro val) depth)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.app x (kernel_to_micro (instantiate_at a val depth))) (kernel_to_micro (instantiate_at f val depth)) (micro_instantiate_at (kernel_to_micro f) (kernel_to_micro val) depth) (ih_f depth)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.app (micro_instantiate_at (kernel_to_micro f) (kernel_to_micro val) depth) x) (kernel_to_micro (instantiate_at a val depth)) (micro_instantiate_at (kernel_to_micro a) (kernel_to_micro val) depth) (ih_a depth))) ",
            // lam ty body
            "(fun (ty : KExpr) (body : KExpr) ",
            "(ih_ty : forall (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at ty val depth)) (micro_instantiate_at (kernel_to_micro ty) (kernel_to_micro val) depth)) ",
            "(ih_body : forall (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at body val depth)) (micro_instantiate_at (kernel_to_micro body) (kernel_to_micro val) depth)) ",
            "(depth : Nat) => Eq.trans MicroExpr ",
            "(MicroExpr.lam (kernel_to_micro (instantiate_at ty val depth)) (kernel_to_micro (instantiate_at body val (Nat.succ depth)))) ",
            "(MicroExpr.lam (micro_instantiate_at (kernel_to_micro ty) (kernel_to_micro val) depth) (kernel_to_micro (instantiate_at body val (Nat.succ depth)))) ",
            "(MicroExpr.lam (micro_instantiate_at (kernel_to_micro ty) (kernel_to_micro val) depth) (micro_instantiate_at (kernel_to_micro body) (kernel_to_micro val) (Nat.succ depth))) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.lam x (kernel_to_micro (instantiate_at body val (Nat.succ depth)))) (kernel_to_micro (instantiate_at ty val depth)) (micro_instantiate_at (kernel_to_micro ty) (kernel_to_micro val) depth) (ih_ty depth)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.lam (micro_instantiate_at (kernel_to_micro ty) (kernel_to_micro val) depth) x) (kernel_to_micro (instantiate_at body val (Nat.succ depth))) (micro_instantiate_at (kernel_to_micro body) (kernel_to_micro val) (Nat.succ depth)) (ih_body (Nat.succ depth)))) ",
            // pi ty body
            "(fun (ty : KExpr) (body : KExpr) ",
            "(ih_ty : forall (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at ty val depth)) (micro_instantiate_at (kernel_to_micro ty) (kernel_to_micro val) depth)) ",
            "(ih_body : forall (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at body val depth)) (micro_instantiate_at (kernel_to_micro body) (kernel_to_micro val) depth)) ",
            "(depth : Nat) => Eq.trans MicroExpr ",
            "(MicroExpr.pi (kernel_to_micro (instantiate_at ty val depth)) (kernel_to_micro (instantiate_at body val (Nat.succ depth)))) ",
            "(MicroExpr.pi (micro_instantiate_at (kernel_to_micro ty) (kernel_to_micro val) depth) (kernel_to_micro (instantiate_at body val (Nat.succ depth)))) ",
            "(MicroExpr.pi (micro_instantiate_at (kernel_to_micro ty) (kernel_to_micro val) depth) (micro_instantiate_at (kernel_to_micro body) (kernel_to_micro val) (Nat.succ depth))) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.pi x (kernel_to_micro (instantiate_at body val (Nat.succ depth)))) (kernel_to_micro (instantiate_at ty val depth)) (micro_instantiate_at (kernel_to_micro ty) (kernel_to_micro val) depth) (ih_ty depth)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.pi (micro_instantiate_at (kernel_to_micro ty) (kernel_to_micro val) depth) x) (kernel_to_micro (instantiate_at body val (Nat.succ depth))) (micro_instantiate_at (kernel_to_micro body) (kernel_to_micro val) (Nat.succ depth)) (ih_body (Nat.succ depth)))) ",
            // const nm us
            "(fun (nm : Name) (us : ListType Level) (depth : Nat) => Eq.refl MicroExpr (kernel_to_micro (KExpr.const nm us))) ",
            // let_ lty lval lbody (let promotion, task #28: fresh binder names avoid
            // capturing the fixed substituted `val`; lty/lval recurse at depth, lbody
            // at succ depth; both sides compute to MicroExpr.let_ images, rebuilt by a
            // three-step cong chain)
            "(fun (lty : KExpr) (lval : KExpr) (lbody : KExpr) ",
            "(ih_lty : forall (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at lty val depth)) (micro_instantiate_at (kernel_to_micro lty) (kernel_to_micro val) depth)) ",
            "(ih_lval : forall (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at lval val depth)) (micro_instantiate_at (kernel_to_micro lval) (kernel_to_micro val) depth)) ",
            "(ih_lbody : forall (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at lbody val depth)) (micro_instantiate_at (kernel_to_micro lbody) (kernel_to_micro val) depth)) ",
            "(depth : Nat) => Eq.trans MicroExpr ",
            "(MicroExpr.let_ (kernel_to_micro (instantiate_at lty val depth)) (kernel_to_micro (instantiate_at lval val depth)) (kernel_to_micro (instantiate_at lbody val (Nat.succ depth)))) ",
            "(MicroExpr.let_ (micro_instantiate_at (kernel_to_micro lty) (kernel_to_micro val) depth) (kernel_to_micro (instantiate_at lval val depth)) (kernel_to_micro (instantiate_at lbody val (Nat.succ depth)))) ",
            "(MicroExpr.let_ (micro_instantiate_at (kernel_to_micro lty) (kernel_to_micro val) depth) (micro_instantiate_at (kernel_to_micro lval) (kernel_to_micro val) depth) (micro_instantiate_at (kernel_to_micro lbody) (kernel_to_micro val) (Nat.succ depth))) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.let_ x (kernel_to_micro (instantiate_at lval val depth)) (kernel_to_micro (instantiate_at lbody val (Nat.succ depth)))) (kernel_to_micro (instantiate_at lty val depth)) (micro_instantiate_at (kernel_to_micro lty) (kernel_to_micro val) depth) (ih_lty depth)) ",
            "(Eq.trans MicroExpr ",
            "(MicroExpr.let_ (micro_instantiate_at (kernel_to_micro lty) (kernel_to_micro val) depth) (kernel_to_micro (instantiate_at lval val depth)) (kernel_to_micro (instantiate_at lbody val (Nat.succ depth)))) ",
            "(MicroExpr.let_ (micro_instantiate_at (kernel_to_micro lty) (kernel_to_micro val) depth) (micro_instantiate_at (kernel_to_micro lval) (kernel_to_micro val) depth) (kernel_to_micro (instantiate_at lbody val (Nat.succ depth)))) ",
            "(MicroExpr.let_ (micro_instantiate_at (kernel_to_micro lty) (kernel_to_micro val) depth) (micro_instantiate_at (kernel_to_micro lval) (kernel_to_micro val) depth) (micro_instantiate_at (kernel_to_micro lbody) (kernel_to_micro val) (Nat.succ depth))) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.let_ (micro_instantiate_at (kernel_to_micro lty) (kernel_to_micro val) depth) x (kernel_to_micro (instantiate_at lbody val (Nat.succ depth)))) (kernel_to_micro (instantiate_at lval val depth)) (micro_instantiate_at (kernel_to_micro lval) (kernel_to_micro val) depth) (ih_lval depth)) ",
            "(Eq.cong MicroExpr MicroExpr (fun (x : MicroExpr) => MicroExpr.let_ (micro_instantiate_at (kernel_to_micro lty) (kernel_to_micro val) depth) (micro_instantiate_at (kernel_to_micro lval) (kernel_to_micro val) depth) x) (kernel_to_micro (instantiate_at lbody val (Nat.succ depth))) (micro_instantiate_at (kernel_to_micro lbody) (kernel_to_micro val) (Nat.succ depth)) (ih_lbody (Nat.succ depth))))) ",
            // proj s i sub: bounded-opaque image (like const); instantiate_at recurses
            // into sub but k2m discards it, micro_instantiate_at fixes opaque_ (sort zero).
            "(fun (s : Name) (i : Nat) (sub : KExpr) ",
            "(ih_sub : forall (depth : Nat), Eq MicroExpr (kernel_to_micro (instantiate_at sub val depth)) (micro_instantiate_at (kernel_to_micro sub) (kernel_to_micro val) depth)) ",
            "(depth : Nat) => Eq.refl MicroExpr (kernel_to_micro (KExpr.proj s i sub))) ",
            // lit v: bounded-opaque image; instantiate_at (lit) = lit.
            "(fun (v : Nat) (depth : Nat) => Eq.refl MicroExpr (kernel_to_micro (KExpr.lit v))) ",
            // major + depth application
            "b depth",
        )
        .to_string()
    }
}

#[cfg(test)]
mod brick1_tripwire {
    use crate::spec::definition::SpecDefinition;
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::spec::Specification;
    use crate::test_utils::run_with_stack;
    use std::collections::HashSet;

    /// TRIPWIRE (Brick-0(i)): register the totality theorem
    /// `forall e U, micro_has_type e U` from the CURRENT axiom set, whose proof
    /// instantiates `micro_verify_sound_bvar` at `ty := U` so its hypothesis
    /// closes by `Eq.refl` IFF the kernel iota-reduces
    /// `micro_verify (MicroCert.bvar 0 U) e` to `U`. If this kernel-checks the
    /// band is formally vacuous and Brick 1 can proceed; if it is rejected
    /// (micro_verify Opaque-stuck) Brick 1 must switch to the 13-ctor fallback.
    #[test]
    fn tripwire_micro_has_type_total_via_bvar_axiom() {
        run_with_stack(|| {
            let spec = Specification::new_implementation_soundness_test_spec()
                .expect("impl-soundness spec should build");

            // (1) The committed vacuity theorem is a genuine DerivedProved,
            //     is_axiom:false, empty-closure decl — kernel-checked at spec
            //     build. Its mere presence certifies micro_has_type is total.
            let total = spec
                .definitions()
                .get("micro_has_type_total")
                .expect("micro_has_type_total should be registered");
            assert!(!total.is_axiom, "micro_has_type_total must not be an axiom");
            assert_eq!(total.proof_status, ProofStatus::DerivedProved);
            assert!(
                total.axiom_deps.is_empty(),
                "micro_has_type_total must have zero axiom_deps: {:?}",
                total.axiom_deps
            );

            // (2) Independently RE-DERIVE the vacuity under a FRESH name to
            //     confirm it is genuinely kernel-derivable (not a flag): the
            //     flipped micro_verify_sound_bvar at ty := U closes by Eq.refl
            //     IFF the kernel iota-reduces micro_verify (MicroCert.bvar 0 U) e
            //     to U. If rejected, the band would not be vacuous.
            let mut probe = spec;
            let res = probe.add_definition(SpecDefinition {
                name: "probe_micro_vacuity_recheck".to_string(),
                type_src: "forall (e : MicroExpr) (U : MicroExpr), micro_has_type e U".to_string(),
                value_src: Some(
                    "fun (e : MicroExpr) (U : MicroExpr) => \
                     micro_verify_sound_bvar Nat.zero U e U (Eq.refl MicroExpr U)"
                        .to_string(),
                ),
                is_axiom: false,
                description: "TRIPWIRE re-derivation under a fresh name".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: None,
                axiom_deps: HashSet::new(),
            });
            assert!(res.is_ok(), "TRIPWIRE REJECTED: {:?}", res.err());
        });
    }
}
