// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! L1 — proof-name resolution for the `spec-link` pass.
//!
//! [`SpecProof`](crate::spec::SpecProof) is the IR analogue of aterm's
//! `proof_anchor!`: a claim that a model action is discharged by a named proof
//! harness. The standalone IR has no compiler/`DefId` view (Ob.2 is out of
//! scope), so it cannot resolve `proof_name` to a live Rust symbol on its own.
//! Instead the aterm build emits a tiny **[`HarnessManifest`]** — a JSON listing
//! every real `#[kani::proof] fn` (name + span) — and hands it to `spec-link`.
//!
//! [`crate::spec::link_spec_modules`] enforces **Ob.4 / Ob.1** for every
//! `SpecProof` independently of manifest policy. [`link_proofs`] validates the
//! manifest's identities, then adds **L1**:
//! `manifest.contains(proof_name)` must hold, else
//!   [`SpecLinkViolation::ProofUnresolved`](crate::spec::SpecLinkViolation::ProofUnresolved).
//!
//! The manifest is *optional* at the policy level: if `SpecProof`s exist but no
//! manifest is supplied, the CLI emits a WARNING ("proof_name unverified") that
//! `--require-manifest` promotes to an ERROR. That policy lives in the CLI; this
//! module is the pure obligation logic and only runs when a manifest is present.

use std::collections::{BTreeMap, BTreeSet};

use crate::spec::{SpecLinkViolation, SpecModule, SpecProof, normalize_violations};

/// A single proof harness the build discovered, as carried by a
/// [`HarnessManifest`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct HarnessEntry {
    /// The harness function name (the `#[kani::proof] fn` identifier). This is
    /// what a [`SpecProof::proof_name`] must match.
    pub name: String,
    /// Source span of the harness, as opaque text (e.g.
    /// `"crates/aterm-buffer/src/ring.rs:300:1"`). Carried for diagnostics;
    /// not interpreted by the resolution logic.
    #[cfg_attr(feature = "serde", serde(default))]
    pub span: String,
}

/// The set of real proof harnesses the aterm build emitted, against which a
/// [`SpecProof::proof_name`] is resolved (L1).
///
/// This is a tiny JSON document the build produces (e.g.
/// `target/trust/harness-manifest.json`). The CLI deserializes it with
/// `serde_json` and hands it to [`link_proofs`].
///
/// ```json
/// {
///   "harnesses": [
///     { "name": "ring_push_refines", "span": "crates/aterm-buffer/src/ring.rs:300:1" },
///     { "name": "ring_pop_refines",  "span": "crates/aterm-buffer/src/ring.rs:340:1" }
///   ]
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct HarnessManifest {
    /// Every real proof harness the build discovered.
    #[cfg_attr(feature = "serde", serde(default))]
    pub harnesses: Vec<HarnessEntry>,
}

/// Structural error in a proof-harness manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HarnessManifestError {
    /// A harness name is empty after trimming.
    BlankHarnessName { index: usize },
    /// Harness names are identities and must be unique.
    DuplicateHarnessName { name: String },
}

impl core::fmt::Display for HarnessManifestError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::BlankHarnessName { index } => {
                write!(f, "harness entry {index} has a blank name")
            }
            Self::DuplicateHarnessName { name } => {
                write!(f, "duplicate harness name `{name}`")
            }
        }
    }
}

impl std::error::Error for HarnessManifestError {}

impl HarnessManifest {
    /// Construct an empty manifest (no harnesses).
    pub fn new() -> Self {
        Self::default()
    }

    /// Build a manifest from an iterator of harness names (spans empty). Handy
    /// for tests and for producers that only have names.
    pub fn from_names<I, S>(names: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            harnesses: names
                .into_iter()
                .map(|n| HarnessEntry {
                    name: n.into(),
                    span: String::new(),
                })
                .collect(),
        }
    }

    /// True when a harness with exactly this `name` is present. This is the L1
    /// resolution predicate.
    pub fn contains(&self, name: &str) -> bool {
        !name.trim().is_empty()
            && self
                .harnesses
                .iter()
                .any(|h| !h.name.trim().is_empty() && h.name == name)
    }

    /// The set of harness names, for diagnostics / set operations.
    pub fn names(&self) -> BTreeSet<&str> {
        self.harnesses.iter().map(|h| h.name.as_str()).collect()
    }

    /// Reject blank or duplicate harness identities before L1 resolution.
    pub fn validate(&self) -> Result<(), HarnessManifestError> {
        let mut names = BTreeSet::new();
        for (index, harness) in self.harnesses.iter().enumerate() {
            if harness.name.trim().is_empty() {
                return Err(HarnessManifestError::BlankHarnessName { index });
            }
            if !names.insert(harness.name.as_str()) {
                return Err(HarnessManifestError::DuplicateHarnessName {
                    name: harness.name.clone(),
                });
            }
        }
        Ok(())
    }
}

/// Run the L1 proof-resolution checks over every [`SpecProof`] in `specs`,
/// resolving each `proof_name` against `manifest`.
///
/// Structural proof-reference closure (Ob.4/Ob.1) is enforced by
/// [`crate::spec::link_spec_modules`] even when no manifest is supplied. For
/// each structurally valid proof this function enforces:
///
/// 1. **L1** — `manifest.contains(proof_name)`; otherwise a
///    [`SpecLinkViolation::ProofUnresolved`].
///
/// Returns the violations found (possibly empty), or rejects a structurally
/// ambiguous manifest before attempting name resolution. The caller merges a
/// successful result into the overall
/// [`SpecLinkReport`](crate::spec::SpecLinkReport). This is the single public
/// source of truth for L1; callers do not need a separate validation step.
pub fn link_proofs(
    specs: &[SpecModule],
    manifest: &HarnessManifest,
) -> Result<Vec<SpecLinkViolation>, HarnessManifestError> {
    manifest.validate()?;

    let mut counts = BTreeMap::<&str, usize>::new();
    for spec in specs {
        *counts.entry(spec.name.as_str()).or_default() += 1;
    }
    let by_name: BTreeMap<&str, &SpecModule> = specs
        .iter()
        .filter(|spec| counts[spec.name.as_str()] == 1)
        .map(|spec| (spec.name.as_str(), spec))
        .collect();

    let mut violations: Vec<SpecLinkViolation> = Vec::new();

    for spec in specs {
        for proof in &spec.proofs {
            check_proof(&by_name, &spec.name, proof, manifest, &mut violations);
        }
    }

    normalize_violations(&mut violations);
    Ok(violations)
}

/// L1 for a single proof. Invalid machine/action references are left solely to
/// the unconditional base linker, avoiding duplicate Ob.4/Ob.1 diagnostics
/// when a manifest is present.
fn check_proof(
    by_name: &BTreeMap<&str, &SpecModule>,
    container: &str,
    proof: &SpecProof,
    manifest: &HarnessManifest,
    violations: &mut Vec<SpecLinkViolation>,
) {
    if proof.machine != container || proof.proof_name.trim().is_empty() {
        return;
    }
    match by_name.get(proof.machine.as_str()) {
        None => return,
        Some(spec) => {
            if !spec.has_action(&proof.action) {
                return;
            }
        }
    }

    // L1: the proof_name must resolve to a real harness in the manifest.
    if !manifest.contains(&proof.proof_name) {
        violations.push(SpecLinkViolation::ProofUnresolved {
            machine: proof.machine.clone(),
            action: proof.action.clone(),
            proof_name: proof.proof_name.clone(),
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::{ProofKind, SpecAnchor, SpecOrigin, SpecVar, SpecWaiver};

    fn ring_with_proof(proof_name: &str) -> SpecModule {
        SpecModule {
            name: "ring".to_string(),
            vars: vec![SpecVar::new("seq", "0..7")],
            actions: vec!["Push".to_string(), "Pop".to_string()],
            invariants: vec![],
            anchors: vec![SpecAnchor {
                machine: "ring".to_string(),
                action: "Push".to_string(),
                function: None,
                rust_symbol: "ring::Ring::push".to_string(),
                span: "src/ring.rs:42:4".to_string(),
                project: Some("ring::project".to_string()),
                projection_target: None,
            }],
            waivers: vec![SpecWaiver {
                machine: "ring".to_string(),
                action: "Pop".to_string(),
                reason: "pop has no shipping handler yet".to_string(),
            }],
            proofs: vec![SpecProof {
                machine: "ring".to_string(),
                action: "Push".to_string(),
                proof_name: proof_name.to_string(),
                kind: ProofKind::Kani,
            }],
            origin: SpecOrigin::Embedded,
            enforcement: crate::spec::SpecEnforcementMode::DesignOnly,
        }
    }

    #[test]
    fn l1_resolved_proof_is_ok() {
        let m = ring_with_proof("ring_push_refines");
        let manifest = HarnessManifest::from_names(["ring_push_refines"]);
        let violations = link_proofs(&[m], &manifest).expect("valid manifest");
        assert!(violations.is_empty(), "got: {violations:?}");
    }

    #[test]
    fn l1_unresolved_proof_fires() {
        let m = ring_with_proof("does_not_exist");
        let manifest = HarnessManifest::from_names(["ring_push_refines"]);
        let violations = link_proofs(&[m], &manifest).expect("valid manifest");
        assert_eq!(violations.len(), 1);
        assert!(matches!(
            &violations[0],
            SpecLinkViolation::ProofUnresolved { proof_name, .. } if proof_name == "does_not_exist"
        ));
        assert_eq!(violations[0].obligation(), "L1");
    }

    #[test]
    fn l1_skips_a_proof_with_a_structurally_invalid_action() {
        // The base linker owns Ob.1. L1 must not duplicate it or report a moot
        // harness error when the action half of the binding is already invalid.
        let mut m = ring_with_proof("ring_push_refines");
        m.proofs[0].action = "Nonexistent".to_string();
        let manifest = HarnessManifest::from_names(["ring_push_refines"]);
        let violations = link_proofs(&[m], &manifest).expect("valid manifest");
        assert!(violations.is_empty());
    }

    #[test]
    fn l1_skips_a_proof_with_a_structurally_invalid_machine() {
        let mut m = ring_with_proof("ring_push_refines");
        m.proofs[0].machine = "ghost".to_string();
        let manifest = HarnessManifest::from_names(["ring_push_refines"]);
        let violations = link_proofs(&[m], &manifest).expect("valid manifest");
        assert!(violations.is_empty());
    }

    #[test]
    fn l1_skips_a_foreign_proof_owned_by_another_container() {
        let mut a = SpecModule::new("A");
        a.actions.push("Step".to_string());
        a.proofs.push(SpecProof {
            machine: "B".to_string(),
            action: "Step".to_string(),
            proof_name: "missing".to_string(),
            kind: ProofKind::Kani,
        });
        let mut b = SpecModule::new("B");
        b.actions.push("Step".to_string());

        let base = crate::spec::validate_spec_structure(&[a.clone(), b.clone()]);
        assert!(base.iter().any(|violation| matches!(
            violation,
            SpecLinkViolation::ReferenceContainerMismatch { from: "proof", .. }
        )));
        assert!(
            link_proofs(&[a, b], &HarnessManifest::new())
                .expect("valid manifest")
                .is_empty()
        );
    }

    #[test]
    fn empty_manifest_makes_every_proof_unresolved() {
        let m = ring_with_proof("ring_push_refines");
        let violations = link_proofs(&[m], &HarnessManifest::new()).expect("valid empty manifest");
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].obligation(), "L1");
    }

    #[test]
    fn manifest_contains_predicate() {
        let manifest = HarnessManifest::from_names(["a_proof", "b_proof"]);
        assert!(manifest.contains("a_proof"));
        assert!(!manifest.contains("c_proof"));
        assert_eq!(manifest.names().len(), 2);
    }

    #[test]
    fn blank_manifest_name_is_invalid_and_cannot_resolve_blank_proof() {
        let manifest = HarnessManifest::from_names([" \t "]);
        assert!(matches!(
            manifest.validate(),
            Err(HarnessManifestError::BlankHarnessName { index: 0 })
        ));
        assert!(!manifest.contains(" \t "));

        let m = ring_with_proof(" \t ");
        // S0 owns the blank-proof diagnostic; L1 must not add a cascade.
        assert!(matches!(
            link_proofs(std::slice::from_ref(&m), &manifest),
            Err(HarnessManifestError::BlankHarnessName { index: 0 })
        ));
        assert!(
            crate::spec::validate_spec_structure(&[m])
                .iter()
                .any(|violation| matches!(
                    violation,
                    SpecLinkViolation::BlankSemanticValue {
                        subject: "proof",
                        field: "proof_name",
                        ..
                    }
                ))
        );
    }

    #[test]
    fn duplicate_manifest_name_is_invalid() {
        let manifest = HarnessManifest::from_names(["same", "same"]);
        assert!(matches!(
            manifest.validate(),
            Err(HarnessManifestError::DuplicateHarnessName { name }) if name == "same"
        ));
        assert!(matches!(
            link_proofs(&[ring_with_proof("same")], &manifest),
            Err(HarnessManifestError::DuplicateHarnessName { name }) if name == "same"
        ));
    }
}
