// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Test-only raw receipt retention; never a production importer or permission.
use super::*;
use crate::scalar_call::{ObservedScalarCall, ObservedScalarCallFailure};
use clean_compiler::primitive_uses::{ArtifactPayload, PrimitiveUseObservations};
use serde_json::json;
use std::path::PathBuf;

fn directory(label: &str) -> Option<PathBuf> {
    let root = std::env::var_os("CLEAN_PRIMITIVE_USE_CAPTURE")?;
    let directory = PathBuf::from(root).join(label);
    std::fs::create_dir_all(&directory).unwrap();
    Some(directory)
}
fn compiler(directory: &Path, trace: &PrimitiveUseObservations) {
    let mut rows = vec![];
    for artifact in trace.artifacts() {
        if let ArtifactPayload::TrustIrModule(module) = artifact.payload() {
            let path = format!("compiler-module-{}.trustir", artifact.id().ordinal());
            let bytes = clean_compiler::emit_trust_ir::serialize_module_bytes(module).unwrap();
            std::fs::write(directory.join(&path), bytes).unwrap();
            rows.push(
                json!({"owner":artifact.owner(),"ordinal":artifact.id().ordinal(),"path":path}),
            );
        } else {
            let path = format!("compiler-payload-{}.txt", artifact.id().ordinal());
            std::fs::write(
                directory.join(&path),
                format!("{:#?}\n", artifact.payload()),
            )
            .unwrap();
            rows.push(json!({"owner":artifact.owner(),"ordinal":artifact.id().ordinal(),"parent":artifact.parent().map(|id|id.ordinal()),"path":path}));
        }
    }
    let decisions = |events: &[clean_compiler::primitive_uses::PrimitiveDecision]| {
        events.iter().map(|event|json!({"owner":event.owner(),"occurrence":event.occurrence(),"iteration":event.iteration(),"before":event.before().ordinal(),"after":event.after().map(|id|id.ordinal()),"note":event.note()})).collect::<Vec<_>>()
    };
    let diagnostics: Vec<_> = trace
        .diagnostic_runs()
        .iter()
        .map(
            |run| json!({"role":format!("{:?}",run.role()),"decisions":decisions(run.decisions())}),
        )
        .collect();
    std::fs::write(directory.join("compiler-decisions.json"),serde_json::to_vec_pretty(&json!({"consumed":decisions(trace.decisions()),"diagnostics":diagnostics,"gaps":format!("{:?}",trace.gaps()),"retained_bytes":trace.retained_bytes(),"work":trace.recording_work(),"contexts":trace.retained_contexts()})).unwrap()).unwrap();
    std::fs::write(
        directory.join("compiler-snapshots.json"),
        serde_json::to_vec_pretty(&rows).unwrap(),
    )
    .unwrap();
}
fn native(directory: &Path, source: &Path, trace: &NativePrimitiveUseObservations) {
    std::fs::copy(source, directory.join("source.lean")).unwrap();
    let mut rows = vec![];
    for artifact in trace.artifacts() {
        let payload = match artifact.payload() {
            NativeArtifactPayload::Bytes { label, path, bytes } => {
                let capture = format!("native-artifact-{}.bin", artifact.id().ordinal());
                std::fs::write(directory.join(&capture), bytes).unwrap();
                json!({"kind":"actual-bytes","label":label,"original_path":path,"capture":capture,"bytes":bytes.len()})
            }
            NativeArtifactPayload::Command { program, arguments } => {
                json!({"kind":"actual-command","program":program.to_string_lossy(),"arguments":arguments.iter().map(|arg|arg.to_string_lossy()).collect::<Vec<_>>()})
            }
            NativeArtifactPayload::ProcessStatus { success, code } => {
                json!({"kind":"actual-process-status","success":success,"exit_code":code})
            }
            NativeArtifactPayload::ShimDemand {
                signature,
                definition,
                mismatch,
            } => {
                json!({"kind":"actual-shim-demand","signature":format!("{signature:?}"),"definition":definition,"mismatch":mismatch})
            }
            NativeArtifactPayload::LicenseCensus(census) => {
                json!({"kind":"actual-license-census","unvalidated":census.unvalidated,"kept":census.kept})
            }
            NativeArtifactPayload::RuntimeArchive {
                compiler,
                archiver,
                members,
            } => {
                json!({"kind":"actual-built-runtime","compiler":compiler,"archiver":archiver,"members":format!("{members:?}")})
            }
            NativeArtifactPayload::PreparedConstant(info) => {
                json!({"kind":"actual-prepared-input","name":info.name.to_string(),"record":format!("{info:#?}")})
            }
            NativeArtifactPayload::Environment(env) => {
                json!({"kind":"actual-input-context","lazy_source":env.has_constant_source()})
            }
            NativeArtifactPayload::ContextAlias(parent) => {
                json!({"kind":"actual-context-alias","ordinal":parent.ordinal()})
            }
        };
        rows.push(json!({"ordinal":artifact.id().ordinal(),"owner":artifact.owner(),"parent":artifact.parent().map(NativeArtifactId::ordinal),"payload":payload}));
    }
    std::fs::write(
        directory.join("native-artifacts.json"),
        serde_json::to_vec_pretty(&rows).unwrap(),
    )
    .unwrap();
    let events:Vec<_>=trace.decisions().iter().map(|event|json!({"role":format!("{:?}",event.role()),"owner":event.owner(),"name":event.name().map(ToString::to_string),"target":event.target().map(ToString::to_string),"context":event.context().map(NativeArtifactId::ordinal),"artifact":event.artifact().map(NativeArtifactId::ordinal),"outcome":event.outcome()})).collect();
    std::fs::write(directory.join("native-summary.json"),serde_json::to_vec_pretty(&json!({"gaps":format!("{:?}",trace.gaps()),"retained_bytes":trace.native_retained_bytes(),"work":trace.native_recording_work(),"contexts":trace.retained_contexts()})).unwrap()).unwrap();
    std::fs::write(
        directory.join("native-events.json"),
        serde_json::to_vec_pretty(&events).unwrap(),
    )
    .unwrap();
    if let Some(output) = trace.compiler() {
        compiler(directory, output.observations());
    }
}
pub(super) fn success(label: &str, source: &Path, call: &ObservedScalarCall) {
    if let Some(directory) = directory(label) {
        native(&directory, source, call.observations());
    }
}
pub(super) fn failure(label: &str, source: &Path, error: &ObservedScalarCallFailure) {
    eprintln!("ACTUAL_OBSERVED_REFUSAL {label}: {error:#}");
    if let Some(directory) = directory(label) {
        native(&directory, source, error.observations());
        std::fs::write(directory.join("actual-error.txt"), format!("{error:#}\n")).unwrap();
        if let Some(failure) = error.compiler_failure() {
            compiler(&directory, failure.observations());
        }
    }
}
pub(super) fn calls(label: &str, rows: &[serde_json::Value]) {
    if let Some(directory) = directory(label) {
        let path = directory.join("actual-calls.json");
        let mut recorded: Vec<serde_json::Value> = if path.is_file() {
            serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap()
        } else {
            vec![]
        };
        recorded.extend_from_slice(rows);
        std::fs::write(path, serde_json::to_vec_pretty(&recorded).unwrap()).unwrap();
    }
}

pub(super) fn legacy_module(label: &str, bytes: &[u8]) {
    if let Some(directory) = directory(label) {
        std::fs::write(directory.join("legacy-same-input.tmbc"), bytes).unwrap();
    }
}
