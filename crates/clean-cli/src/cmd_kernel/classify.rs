// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean kernel classify` handler (#3598) — incremental proof classifier.
//!
//! Seeds a kernel `Environment` with the same NN-verify / interval-arith /
//! CROWN overlay constants that `mathverse_shard build-native` uses (via the
//! shared [`clean_mathverse::build_library_native::seed_native_environment`]
//! entry point), then classifies declarations using the kernel's
//! `proof_quality` / `axiom_deps` APIs in
//! `clean_kernel::env::axiom_audit`.
//!
//! The goal is a sub-500ms per-theorem feedback loop: the full
//! `mathverse_shard build-native` pipeline takes ~90 seconds (env seeding +
//! shard flattening + kernel re-check + sidecar write). This handler
//! skips everything after classification, collapsing the loop to just the
//! env-seeding cost. See issue #3598 for the full design discussion.
//!
//! Feature-gated behind `math-overlays` because
//! [`seed_native_environment`](clean_mathverse::build_library_native::seed_native_environment)
//! calls the overlay-gated `init_nn_verify_*` registrars on `Environment`.
//! Without the feature the handler exits non-zero with an informative
//! message; behaviour mirrors `verify-constructive-claims`.

#[cfg(not(feature = "math-overlays"))]
use anyhow::bail;

/// User-facing classification returned for each requested declaration.
///
/// Split out of [`ProofQuality`] because the CLI also needs to distinguish
/// `TrustMarkerReached` (reached `sorry` / `sorryAx` / `trustedArith` /
/// `trustedAy`) from `AxiomDependent` (reached a plain domain axiom) — a
/// distinction the kernel's `ProofQuality` enum folds into a single
/// `AxiomDependent` variant. Keeping the split local to the CLI means the
/// kernel classifier stays untouched while agents still get the richer
/// triage view.
#[cfg(feature = "math-overlays")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "PascalCase")]
pub(crate) enum ClassificationTag {
    /// Theorem with an empty transitive domain-axiom closure. Safe to
    /// export into the clean-native shard.
    Constructive,
    /// Theorem whose closure contains at least one non-foundational axiom
    /// and NO trust markers.
    AxiomDependent,
    /// Theorem whose closure contains at least one trust marker
    /// (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`). Cannot be
    /// promoted to `Constructive` without removing the trust envelope.
    TrustMarkerReached,
    /// Theorem registered via `add_decl_structural` — not kernel-checked.
    Unchecked,
    /// Declaration is present but is not a theorem (axiom, opaque, or
    /// definition).
    NotATheorem,
    /// Declaration exists but the kernel returned no classification.
    /// Should not happen on well-formed declarations; reported verbatim
    /// so agents can file follow-ups.
    Unknown,
    /// Declaration is absent from the seeded env. The caller typo'd the
    /// name or the overlay that registers it is not in the default
    /// seeding list.
    NotFound,
}

#[cfg(feature = "math-overlays")]
#[derive(Debug, Clone, serde::Serialize)]
pub(crate) struct ClassifyRecord {
    pub name: String,
    pub kind: Option<String>,
    pub classification: ClassificationTag,
    pub axiom_closure: Vec<String>,
    pub trust_markers_reached: Vec<String>,
}

#[cfg(feature = "math-overlays")]
fn classify_one(env: &clean_kernel::Environment, name_str: &str) -> ClassifyRecord {
    use clean_kernel::{is_trust_marker, ConstantKind, Name, ProofQuality};

    let name = Name::from_string(name_str);
    let Some(info) = env.get_const(&name) else {
        return ClassifyRecord {
            name: name_str.to_owned(),
            kind: None,
            classification: ClassificationTag::NotFound,
            axiom_closure: vec![],
            trust_markers_reached: vec![],
        };
    };

    let kind = match info.kind {
        ConstantKind::Theorem => "Theorem",
        ConstantKind::Axiom => "Axiom",
        ConstantKind::Opaque => "Opaque",
        ConstantKind::Definition => "Definition",
    };

    // Pull the transitive closure once — shared by every variant's output.
    // `axiom_deps` already excludes foundational axioms.
    let mut closure: Vec<String> = env
        .axiom_deps(&name)
        .map(|set| set.into_iter().map(|n| n.to_string()).collect())
        .unwrap_or_default();
    closure.sort();
    let trust_markers: Vec<String> = closure
        .iter()
        .filter(|s| is_trust_marker(&Name::from_string(s)))
        .cloned()
        .collect();

    let classification = match env.proof_quality(&name) {
        Some(ProofQuality::Constructive) => ClassificationTag::Constructive,
        Some(ProofQuality::AxiomDependent { .. }) => {
            if !trust_markers.is_empty() {
                ClassificationTag::TrustMarkerReached
            } else {
                ClassificationTag::AxiomDependent
            }
        }
        Some(ProofQuality::Unchecked) => ClassificationTag::Unchecked,
        Some(ProofQuality::NotATheorem) => ClassificationTag::NotATheorem,
        Some(_) | None => ClassificationTag::Unknown,
    };

    ClassifyRecord {
        name: name_str.to_owned(),
        kind: Some(kind.to_owned()),
        classification,
        axiom_closure: closure,
        trust_markers_reached: trust_markers,
    }
}

/// Seed a fresh environment and classify the caller's requested names.
///
/// Separated from [`run`] so tests can assert the classification contract
/// without going through clap or touching stdout. Every public branch of
/// [`run`] ultimately dispatches through either this or
/// [`list_all_constructive`].
#[cfg(feature = "math-overlays")]
pub(crate) fn classify_names(names: &[String]) -> Vec<ClassifyRecord> {
    let mut env = clean_kernel::Environment::new();
    clean_mathverse::build_library_native::seed_native_environment(&mut env);
    names.iter().map(|n| classify_one(&env, n)).collect()
}

#[cfg(feature = "math-overlays")]
pub(crate) fn list_all_constructive() -> Vec<ClassifyRecord> {
    use clean_kernel::{ConstantKind, ProofQuality};

    let mut env = clean_kernel::Environment::new();
    clean_mathverse::build_library_native::seed_native_environment(&mut env);
    let names: Vec<String> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Theorem)
        .map(|c| c.name.to_string())
        .collect();
    names
        .iter()
        .filter_map(|n| {
            let rec = classify_one(&env, n);
            // Cheap belt-and-suspenders: double-check via ProofQuality, so
            // an agent reading the JSON output can trust the label even if
            // the enum mapping drifts in the future.
            let name = clean_kernel::Name::from_string(n);
            if matches!(env.proof_quality(&name), Some(ProofQuality::Constructive)) {
                Some(rec)
            } else {
                None
            }
        })
        .collect()
}

/// Diagnostic for `--why-rejected`: returns `Ok(msg)` describing the first
/// blocking axiom, or `Err(msg)` if the theorem is not AxiomDependent.
#[cfg(feature = "math-overlays")]
pub(crate) fn why_rejected(name_str: &str) -> Result<String, String> {
    let mut env = clean_kernel::Environment::new();
    clean_mathverse::build_library_native::seed_native_environment(&mut env);
    let rec = classify_one(&env, name_str);

    match rec.classification {
        ClassificationTag::AxiomDependent | ClassificationTag::TrustMarkerReached => {
            let Some(first) = rec.axiom_closure.first().cloned() else {
                return Err(format!(
                    "{name_str}: classified {:?} but axiom_closure is empty — \
                     classifier invariant violation",
                    rec.classification
                ));
            };
            // Look up the offending axiom's kind so the human-readable
            // summary doesn't require a follow-up `mathverse info` call.
            let kind = env
                .get_const(&clean_kernel::Name::from_string(&first))
                .map(|info| match info.kind {
                    clean_kernel::ConstantKind::Theorem => "Theorem",
                    clean_kernel::ConstantKind::Axiom => "Axiom",
                    clean_kernel::ConstantKind::Opaque => "Opaque",
                    clean_kernel::ConstantKind::Definition => "Definition",
                })
                .unwrap_or("Unknown");
            Ok(format!(
                "{name_str} is {:?}: first blocking axiom `{first}` ({kind})",
                rec.classification
            ))
        }
        ClassificationTag::Constructive => {
            Err(format!("{name_str} is Constructive — nothing to explain"))
        }
        ClassificationTag::NotFound => Err(format!("{name_str} not found in seeded environment")),
        other => Err(format!(
            "{name_str}: classification is {other:?}, not AxiomDependent"
        )),
    }
}

#[cfg(feature = "math-overlays")]
pub(super) fn run(
    names: Vec<String>,
    all_constructive: bool,
    why_rejected_name: Option<String>,
) -> anyhow::Result<()> {
    if let Some(name) = why_rejected_name {
        match why_rejected(&name) {
            Ok(msg) => {
                println!("{msg}");
                return Ok(());
            }
            Err(msg) => {
                eprintln!("{msg}");
                std::process::exit(1);
            }
        }
    }

    let records = if all_constructive {
        list_all_constructive()
    } else if names.is_empty() {
        eprintln!(
            "clean kernel classify: requires at least one NAME, \
             --all-constructive, or --why-rejected <NAME>"
        );
        std::process::exit(2);
    } else {
        classify_names(&names)
    };

    for rec in &records {
        let line = serde_json::to_string(rec)?;
        println!("{line}");
    }
    Ok(())
}

#[cfg(not(feature = "math-overlays"))]
pub(super) fn run(
    _names: Vec<String>,
    _all_constructive: bool,
    _why_rejected: Option<String>,
) -> anyhow::Result<()> {
    bail!(
        "clean kernel classify requires the `math-overlays` feature. \
         Rebuild with `cargo build -p clean-cli --features math-overlays` \
         (or the equivalent feature on the `clean` package)."
    );
}

#[cfg(test)]
mod tests {
    #[cfg(not(feature = "math-overlays"))]
    use super::*;

    /// Without `math-overlays`, the handler must fail closed with an
    /// informative error instead of silently returning Ok.
    #[cfg(not(feature = "math-overlays"))]
    #[test]
    fn classify_run_without_math_overlays_returns_feature_gate_error() {
        let err = run(vec!["Foo".into()], false, None)
            .expect_err("handler must refuse to run without `math-overlays`");
        let msg = format!("{err:#}");
        assert!(
            msg.contains("math-overlays"),
            "error message must call out the missing feature; got: {msg}"
        );
    }

    /// Rat.max_zero_zero is the canonical Tier-A constructive theorem
    /// registered by `init_nn_verify_ibp_width_zero`. It must come back as
    /// `Constructive` with an empty axiom closure or the native shard
    /// pipeline is fundamentally broken.
    #[cfg(feature = "math-overlays")]
    #[test]
    fn classify_rat_max_zero_zero_is_constructive() {
        use super::{classify_names, ClassificationTag};
        let records = classify_names(&["NNVerify.Rat.max_zero_zero".to_owned()]);
        assert_eq!(records.len(), 1);
        let rec = &records[0];
        assert_eq!(
            rec.classification,
            ClassificationTag::Constructive,
            "NNVerify.Rat.max_zero_zero must be Constructive; got {rec:?}"
        );
        assert!(
            rec.axiom_closure.is_empty(),
            "constructive theorems must have an empty axiom closure; got {:?}",
            rec.axiom_closure
        );
        assert!(rec.trust_markers_reached.is_empty());
    }

    /// Nonexistent names must produce a `NotFound` record rather than
    /// panicking. The `--all-constructive` fast path relies on this.
    #[cfg(feature = "math-overlays")]
    #[test]
    fn classify_missing_name_returns_not_found() {
        use super::{classify_names, ClassificationTag};
        let records = classify_names(&["Definitely.Not.A.Real.Theorem".to_owned()]);
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].classification, ClassificationTag::NotFound);
        assert!(records[0].kind.is_none());
    }

    /// `--all-constructive` must match the shard builder's count of
    /// constructive theorems: every theorem it returns has
    /// `classification == Constructive` and an empty axiom closure. We
    /// avoid pinning the exact count because it drifts with each demotion
    /// wave — but the invariants above are rock-stable.
    #[cfg(feature = "math-overlays")]
    #[test]
    fn list_all_constructive_records_satisfy_constructive_invariants() {
        use super::{list_all_constructive, ClassificationTag};
        let records = list_all_constructive();
        for rec in &records {
            assert_eq!(rec.classification, ClassificationTag::Constructive);
            assert!(
                rec.axiom_closure.is_empty(),
                "record {rec:?} is marked Constructive but has a non-empty closure",
            );
            assert!(rec.trust_markers_reached.is_empty());
            // Sanity: every listed record must be a theorem.
            assert_eq!(rec.kind.as_deref(), Some("Theorem"));
        }
    }

    /// `--why-rejected` must return Ok for AxiomDependent/TrustMarker cases
    /// and Err for everything else. Rat.max_zero_zero is Constructive, so
    /// it must be Err.
    #[cfg(feature = "math-overlays")]
    #[test]
    fn why_rejected_for_constructive_theorem_returns_err() {
        use super::why_rejected;
        let result = why_rejected("NNVerify.Rat.max_zero_zero");
        assert!(
            result.is_err(),
            "why-rejected on a Constructive theorem must Err; got {result:?}"
        );
        let msg = result.unwrap_err();
        assert!(
            msg.contains("Constructive"),
            "error message should explain the theorem is Constructive; got {msg}"
        );
    }
}
