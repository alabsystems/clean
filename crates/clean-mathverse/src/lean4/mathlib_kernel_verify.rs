// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel verification of imported Mathlib lemmas.
//!
//! Given a kernel `Environment` loaded via [`load_module_with_deps`], this
//! module walks a list of target Mathlib lemma names and re-validates each
//! one through the kernel type-checker:
//!
//! 1. Look up the `ConstantInfo` by name.
//! 2. Re-run `TypeChecker::infer_type(&ci.type_)` on the declared type to
//!    confirm it is itself a well-formed type (not just that the `.olean`
//!    writer claimed it was).
//! 3. If the constant has a proof term (`ci.value = Some(_)`), re-run
//!    `TypeChecker::check_type(&proof, &ci.type_)` to confirm the proof term
//!    produces the declared type (kernel-verified proof).
//!
//! This closes the "is the imported theorem actually kernel-verified?" loop
//! independently of whatever the `.olean` loader did at load time. It is the
//! evidence required by `#3370` acceptance criterion 4 ("Imported declarations
//! pass `add_decl` kernel type checking") and the end-to-end test (criterion
//! 7): a single function that takes target lemma names and returns whether
//! each one survived kernel re-validation.
//!
//! The function does NOT bypass trust: every imported lemma with a proof term
//! is required to pass `check_type`, which runs Lean 4 `check()` semantics
//! (full definitional-equality rechecking, not fast `infer_only` inference).
//!
//! Reference: Lean 4 `type_checker.cpp:308-311`
//! (`check(e, lps) = infer_type_core(e, false)`).

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_kernel::ConstantKind;

/// Status of one lemma after kernel re-verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LemmaVerifyStatus {
    /// Lemma is a `Theorem` or `Definition` with a proof term; the kernel
    /// re-verified that the proof term has the declared type.
    KernelVerifiedWithProof,
    /// Lemma's declared type is well-formed (kernel `infer_type` succeeded),
    /// but the constant itself has no proof term in the environment — it is
    /// registered as an `Axiom` or `Opaque`. The trust boundary for this
    /// lemma is the axiom/opaque declaration, not a kernel proof.
    AxiomaticOnly,
    /// Lemma was not found in the environment. The Mathlib module providing
    /// it was either not loaded or the name resolves differently than the
    /// expected form.
    NotFound,
    /// Lemma was found but failed kernel re-verification. Includes a short
    /// error string from the type-checker.
    Failed(String),
}

impl LemmaVerifyStatus {
    /// Whether this status represents kernel-verified evidence that the
    /// lemma's proof term produces the claimed type.
    #[must_use]
    pub fn is_kernel_verified(&self) -> bool {
        matches!(self, Self::KernelVerifiedWithProof)
    }

    /// Whether this status represents a failure (not-found or type-error).
    #[must_use]
    pub fn is_failure(&self) -> bool {
        matches!(self, Self::NotFound | Self::Failed(_))
    }
}

/// Per-lemma verification report.
#[derive(Clone, Debug)]
pub struct LemmaVerifyReport {
    /// Lemma name as requested (e.g., `Nat.add_comm`).
    pub name: String,
    /// Verification outcome.
    pub status: LemmaVerifyStatus,
    /// Constant kind (if found): `Theorem`, `Definition`, `Axiom`, `Opaque`.
    pub kind: Option<ConstantKind>,
}

/// Batch verification summary across a list of lemmas.
#[derive(Clone, Debug, Default)]
pub struct KernelVerifySummary {
    /// Reports for each requested name, in order.
    pub reports: Vec<LemmaVerifyReport>,
}

impl KernelVerifySummary {
    /// Number of lemmas whose proof terms kernel-rechecked successfully.
    #[must_use]
    pub fn num_kernel_verified(&self) -> usize {
        self.reports
            .iter()
            .filter(|r| r.status.is_kernel_verified())
            .count()
    }

    /// Number of lemmas found in the environment (with or without proof).
    #[must_use]
    pub fn num_found(&self) -> usize {
        self.reports
            .iter()
            .filter(|r| !matches!(r.status, LemmaVerifyStatus::NotFound))
            .count()
    }

    /// Number of lemmas present only as axioms/opaque (no proof term, but
    /// declared type is well-formed).
    #[must_use]
    pub fn num_axiomatic(&self) -> usize {
        self.reports
            .iter()
            .filter(|r| matches!(r.status, LemmaVerifyStatus::AxiomaticOnly))
            .count()
    }

    /// Number of lemmas that failed kernel rechecking (proof term did not
    /// produce the declared type).
    #[must_use]
    pub fn num_failed(&self) -> usize {
        self.reports
            .iter()
            .filter(|r| matches!(r.status, LemmaVerifyStatus::Failed(_)))
            .count()
    }

    /// Number of lemmas that were requested but not found in the environment.
    #[must_use]
    pub fn num_not_found(&self) -> usize {
        self.reports
            .iter()
            .filter(|r| matches!(r.status, LemmaVerifyStatus::NotFound))
            .count()
    }

    /// Names of lemmas with `KernelVerifiedWithProof` status.
    #[must_use]
    pub fn kernel_verified_names(&self) -> Vec<String> {
        self.reports
            .iter()
            .filter(|r| r.status.is_kernel_verified())
            .map(|r| r.name.clone())
            .collect()
    }

    /// Names of lemmas that failed (found but failed rechecking).
    #[must_use]
    pub fn failed_names(&self) -> Vec<(String, String)> {
        self.reports
            .iter()
            .filter_map(|r| match &r.status {
                LemmaVerifyStatus::Failed(err) => Some((r.name.clone(), err.clone())),
                _ => None,
            })
            .collect()
    }
}

/// Re-verify each named lemma in the environment through the kernel.
///
/// For each `name`:
/// - If the constant does not exist: [`LemmaVerifyStatus::NotFound`].
/// - If the constant has no proof term (`Axiom` or `Opaque` without value):
///   runs `infer_type` on the declared type. If inference succeeds the
///   status is [`LemmaVerifyStatus::AxiomaticOnly`]; otherwise
///   [`LemmaVerifyStatus::Failed`].
/// - If the constant has a proof term: runs `check_type(&proof, &type_)`.
///   On success the status is [`LemmaVerifyStatus::KernelVerifiedWithProof`];
///   on failure it is [`LemmaVerifyStatus::Failed`].
///
/// The kernel `check_type` call uses Lean 4's full-check semantics
/// (`infer_only=false`), matching what `env.add_decl()` does when registering
/// a theorem. This makes the function a direct re-run of the `add_decl`
/// acceptance check for each named lemma.
pub fn verify_mathlib_lemmas_kernel(env: &Environment, names: &[&str]) -> KernelVerifySummary {
    let tc = TypeChecker::new(env);
    let mut summary = KernelVerifySummary::default();

    for &raw_name in names {
        let name = Name::from_string(raw_name);
        let Some(ci) = env.get_const(&name) else {
            summary.reports.push(LemmaVerifyReport {
                name: raw_name.to_string(),
                status: LemmaVerifyStatus::NotFound,
                kind: None,
            });
            continue;
        };

        let kind = ci.kind;

        // Always re-verify that the declared type is well-formed.
        if let Err(e) = tc.infer_type(&ci.type_) {
            summary.reports.push(LemmaVerifyReport {
                name: raw_name.to_string(),
                status: LemmaVerifyStatus::Failed(format!("type inference failed: {e:?}")),
                kind: Some(kind),
            });
            continue;
        }

        match &ci.value {
            Some(proof) => match tc.check_type(proof, &ci.type_) {
                Ok(()) => summary.reports.push(LemmaVerifyReport {
                    name: raw_name.to_string(),
                    status: LemmaVerifyStatus::KernelVerifiedWithProof,
                    kind: Some(kind),
                }),
                Err(e) => summary.reports.push(LemmaVerifyReport {
                    name: raw_name.to_string(),
                    status: LemmaVerifyStatus::Failed(format!("proof term check failed: {e:?}")),
                    kind: Some(kind),
                }),
            },
            None => summary.reports.push(LemmaVerifyReport {
                name: raw_name.to_string(),
                status: LemmaVerifyStatus::AxiomaticOnly,
                kind: Some(kind),
            }),
        }
    }

    summary
}

/// The canonical list of gamma-crown-relevant lemmas to attempt kernel
/// re-verification against. Covers at least 5 distinct gamma-crown axiom
/// categories:
///
/// - Nat arithmetic commutativity/associativity (Category B, C001/C002)
/// - Nat ordering transitivity (Category B, C007)
/// - Boolean/Prop identity lemmas (C008 inductive axioms)
/// - Propositional axioms (Init.Classical, shared across conjectures)
///
/// These lemmas are resolvable against the Lean 4 Init modules alone (no
/// Mathlib required), but the function can be called with any environment
/// that contains them.
#[must_use]
pub fn gamma_crown_target_lemmas() -> Vec<&'static str> {
    vec![
        // Nat arithmetic (C001/C002 Category B)
        "Nat.add_comm",
        "Nat.add_assoc",
        "Nat.mul_comm",
        "Nat.mul_assoc",
        "Nat.zero_add",
        "Nat.add_zero",
        "Nat.mul_one",
        "Nat.one_mul",
        // Nat ordering (C007 merge_sound_helper)
        "Nat.le_refl",
        "Nat.le_trans",
        // Core propositional axioms (Init.Classical / Init.Core)
        "propext",
        "Classical.choice",
        "Quot.sound",
    ]
}

/// Additional Mathlib-specific lemma names used to cover the Mathlib-only
/// path of acceptance criterion 5 ("Import at least 5 Mathlib lemmas relevant
/// to gamma-crown proofs"). Each entry points at a proved lemma in the
/// Mathlib tree; absence of a given entry in the environment is reported as
/// [`LemmaVerifyStatus::NotFound`] (a non-fatal signal that the Mathlib module
/// providing it was not loaded).
#[must_use]
pub fn gamma_crown_mathlib_target_lemmas() -> Vec<&'static str> {
    vec![
        // Matrix algebra (C003 spectral_norm, C010 zonotope)
        "Matrix.mul_assoc",
        "Matrix.one_mul",
        "Matrix.mul_one",
        // Real analysis (C003 Lipschitz, C028 Positivstellensatz)
        "abs_add",
        "sq_nonneg",
        "abs_nonneg",
        // Rat field properties (Category B across conjectures)
        "Rat.add_comm",
        "Rat.mul_comm",
    ]
}

#[cfg(test)]
#[path = "mathlib_kernel_verify_tests.rs"]
mod tests;
