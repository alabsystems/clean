// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::interpret::InterpretOptions;
use crate::request::{NativeAdapterInput, NativeDiagnosticLevel};
use crate::{ModuleImport, Producer};

mod parity;
mod stops;

#[derive(Clone, Copy)]
enum Case {
    Provenance,
    Serialization,
    Diagnostics,
}

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    stop_retirement: bool,
    work: usize,
    bytes: usize,
    work_limit: Option<usize>,
    byte_limit: Option<usize>,
}

impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        if self.stop_retirement && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("byte overflow")?;
        if self.work_limit.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(972))
}

fn fixture() -> NativeVerificationBundle {
    let mut bundle = crate::request::tests::native_bundle();
    bundle.provenance.producer_version.clear();
    bundle.provenance.source_digest = Some(ProofDigest {
        algorithm: ProofDigestAlgorithm::TrustIrStableV1,
        bytes: [0; 32],
    });
    bundle.provenance.source_language = NativeSourceLanguage::Rust;
    bundle.provenance.source_languages =
        BTreeSet::from([NativeSourceLanguage::Lean, NativeSourceLanguage::Swift]);
    bundle.provenance.toolchain = vec![NativeToolIdentity {
        name: " \u{2003}".into(),
        version: Some("\n".into()),
        revision: Some("\t".into()),
        digest: Some(ProofDigest {
            algorithm: ProofDigestAlgorithm::TrustIrStableV1,
            bytes: [0; 32],
        }),
    }];
    let mut other = bundle.module.functions[0].clone();
    other.id = FuncId::new(13);
    other.producer = Some(Producer::Other("λ".repeat(1100)));
    bundle.module.functions.push(other.clone());
    other.id = FuncId::new(5);
    bundle.module.functions.push(other);
    let mut imported = ModuleImport::new("κ🦀".repeat(400), ProofDigest::sha256([17; 32]));
    imported.producer = Some(Producer::Other("tool🦀".repeat(300)));
    bundle.module.imports = vec![
        ModuleImport::new("covered-clean", ProofDigest::sha256([18; 32]))
            .with_producer(Producer::Clean),
        imported,
        ModuleImport::new("unrecorded", ProofDigest::sha256([19; 32])),
    ];
    bundle.serialization.schema_version = 0;
    bundle.serialization.canonical_order = false;
    bundle.serialization.sort_unordered_sets = false;
    bundle.serialization.messagepack_named_fields = false;
    bundle.serialization.unknown_fields = NativeUnknownFieldPolicy::Preserve;
    bundle.diagnostics.include_source_spans = false;
    bundle.diagnostics.include_lineage = false;
    bundle.diagnostics.max_counterexamples = 0;
    bundle
}

fn run(
    bundle: &NativeVerificationBundle,
    case: Case,
    session: &mut ObservedSession<'_, Observer>,
) -> R<Vec<E>> {
    match case {
        Case::Provenance => bundle.provenance_errors_observed(session, site()),
        Case::Serialization => bundle.serialization_errors_observed(session, site()),
        Case::Diagnostics => bundle.diagnostics_policy_errors_observed(session, site()),
    }
}

fn observed(bundle: &NativeVerificationBundle, case: Case) -> Vec<E> {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = run(bundle, case, &mut session).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    errors
}

fn is_provenance(error: &E) -> bool {
    match error {
        E::EmptyProvenanceField(field) => matches!(
            *field,
            "provenance.producer_version" | "provenance.toolchain"
        ),
        E::EmptyDigest { field }
        | E::NonCryptographicDigest { field }
        | E::InputDigestMismatch { field, .. } => {
            matches!(*field, "provenance.source_digest" | "provenance.toolchain")
        }
        E::InvalidToolIdentityField { field, .. } => *field == "provenance.toolchain",
        E::BundlePrimaryLanguageUncovered { .. }
        | E::BundleLanguageUncovered { .. }
        | E::BundleImportLanguageUncovered { .. } => true,
        _ => false,
    }
}

fn ordinary(bundle: &NativeVerificationBundle, case: Case) -> Vec<E> {
    // Call the actual unchanged validator, retaining only this constituent's
    // exact exclusive variants/field labels. No copied validator is the oracle.
    bundle
        .validate()
        .err()
        .unwrap_or_default()
        .into_iter()
        .filter(|error| match case {
            Case::Provenance => is_provenance(error),
            Case::Serialization => matches!(
                error,
                E::UnsupportedSerializationSchemaVersion(_) | E::NonCanonicalSerialization(_)
            ),
            Case::Diagnostics => matches!(error, E::InvalidBundleDiagnosticsPolicy { .. }),
        })
        .collect()
}
