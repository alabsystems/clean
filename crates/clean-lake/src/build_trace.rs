// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The build trace: what lets `clean lake build` reuse a module's artifact.
//!
//! # What this replaced (T7a2, module-trust 2026-09-26)
//!
//! A module was skipped as "up to date" whenever its `.olean` was not older
//! than its source ([`crate::Workspace::needs_rebuild`]) — a timestamp test
//! that never read the artifact. Measured on the round-21 fixtures: a
//! `theorem t : False := sorry` artifact that an older builder left behind
//! next to a newer, honest-looking source file was skipped, and `clean lake
//! build` printed `Build OK (1 modules, 0.00s)` with exit 0. The same test
//! ignored dependencies entirely, so a module built against a dependency's
//! OLD value was reused after that dependency was rebuilt with a new one.
//!
//! # What a trace is
//!
//! After this builder has elaborated, kernel-checked and closure-gated a
//! module and written its three artifact files, it writes
//! `<module>.clean-trace` next to them, recording content digests (BLAKE3) of:
//!
//! - the module's source;
//! - the artifact files of every in-workspace module in its transitive import
//!   closure (the exact bytes this build loaded);
//! - the three artifact files of every module outside the workspace that its
//!   build loads — the whole closure of its toolchain-named imports and of
//!   its in-workspace dependencies' imports, not only a named import's root
//!   `.olean` (module-trust round 31);
//! - the three artifact files it wrote;
//!
//! plus the builder identity, whether the build ran with
//! `--permissive-imports`, and the `lean` arguments (`leanOptions`,
//! `moreLeanArgs`) the module was compiled with.
//!
//! A module is reused only when a trace exists and every one of those digests
//! matches the files on disk NOW. Anything else — no trace (an artifact some
//! other tool or an older builder wrote), a different source, a rebuilt or
//! rewritten dependency, a rewritten artifact, a permissive trace under a
//! strict build — rebuilds the module from source, and the build's verdict
//! then comes from that source.
//!
//! # What a trace does not prove
//!
//! It is a cache key, not a certificate: a process that deliberately rewrites
//! an artifact AND re-derives its trace gets the artifact reused. Every
//! consumer of an artifact (`clean check`, a dependent's build, `clean lake
//! verify-fresh`) still re-admits what it cites through
//! `clean_olean::ImportedConeGate`, whatever the trace says, and every build
//! — a reuse included — admits the modules outside the workspace that the
//! module rests on through the authority `clean check` uses
//! ([`crate::ImportAdmitter`]). Until round 31 a toolchain-named import was
//! pinned by its ROOT `.olean` only, not by the closure behind it.

use crate::error::LakeResult;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// Schema tag of a `.clean-trace` file; a trace with any other tag is not
/// read as a match.
const TRACE_SCHEMA: &str = "clean-lake-build-trace-v2";

/// One module's build trace (see the module docs).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ModuleBuildTrace {
    schema: String,
    /// The builder that wrote the artifact: the `.olean` git-hash stamp and
    /// this crate's version.
    builder: String,
    /// Digest of the module's source file.
    source: String,
    /// Per in-workspace module of the transitive import closure: the digest
    /// of its artifact files as they were when this module was built.
    inputs: BTreeMap<String, String>,
    /// Per module outside the workspace that the build loads: the digest of
    /// its three artifact files (`"unresolved"` for a toolchain-named import
    /// found nowhere).
    stdlib: BTreeMap<String, String>,
    /// Whether the build ran with `--permissive-imports`.
    permissive_imports: bool,
    /// The `lean` arguments the module was compiled with (its `leanOptions`
    /// as `-D…`, then `moreLeanArgs`). Absent in a trace written before they
    /// were honoured, which reads as none.
    #[serde(default)]
    lean_args: Vec<String>,
    /// Digest of the three artifact files this build wrote.
    outputs: String,
}

/// Path of a module's trace, next to its `.olean`.
pub fn trace_path(olean: &Path) -> PathBuf {
    olean.with_extension("clean-trace")
}

/// Who wrote a trace: the `.olean` format stamp, this crate's version, and
/// the BLAKE3 digest of the running executable.
///
/// The executable digest is what makes the identity name a BUILDER rather
/// than a release line. With only the format stamp and version
/// (`1ea5…+clean-lake-0.9.0`, constant across commits), a trace written by
/// any build of this version — one with a weaker or buggier gate among them
/// — was reused by a fixed one: the T7a2 shape (a leftover artifact credited
/// because something said it was built) one level up. A binary whose bytes
/// differ in any way now rebuilds what another binary vouched for. When the
/// executable cannot be read, the identity is unique to this process, so
/// nothing it writes is ever reused by another run (fail closed).
fn builder_identity() -> String {
    static IDENTITY: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    IDENTITY
        .get_or_init(|| {
            let exe = std::env::current_exe()
                .and_then(std::fs::read)
                .map(|bytes| digest_bytes(&bytes));
            let exe = exe.unwrap_or_else(|_| {
                let nanos = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map_or(0, |d| d.as_nanos());
                format!("unreadable-exe-{}-{nanos}", std::process::id())
            });
            format!(
                "{}+clean-lake-{}+exe-{exe}",
                crate::build::CLEAN_OLEAN_GIT_HASH,
                env!("CARGO_PKG_VERSION")
            )
        })
        .clone()
}

fn digest_bytes(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

/// Digest of a module's three artifact files (`.olean`, `.olean.server`,
/// `.olean.private`), each length-prefixed so a byte moved between parts
/// changes the digest. A missing part is recorded as absent, never skipped.
pub fn digest_artifact_parts(parts: &[PathBuf; 3]) -> LakeResult<String> {
    let mut hasher = blake3::Hasher::new();
    for part in parts {
        match std::fs::read(part) {
            Ok(bytes) => {
                hasher.update(b"present");
                hasher.update(&(bytes.len() as u64).to_le_bytes());
                hasher.update(&bytes);
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                hasher.update(b"absent");
            }
            Err(e) => return Err(e.into()),
        }
    }
    Ok(hasher.finalize().to_hex().to_string())
}

/// Everything a trace records about a module's inputs; built by the caller
/// from the workspace and compared (or completed with the outputs and
/// written).
pub(crate) struct TraceInputs {
    pub(crate) source: Vec<u8>,
    pub(crate) inputs: BTreeMap<String, String>,
    pub(crate) stdlib: BTreeMap<String, String>,
    pub(crate) permissive_imports: bool,
    pub(crate) lean_args: Vec<String>,
}

impl TraceInputs {
    fn into_trace(self, outputs: String) -> ModuleBuildTrace {
        ModuleBuildTrace {
            schema: TRACE_SCHEMA.to_string(),
            builder: builder_identity(),
            source: digest_bytes(&self.source),
            inputs: self.inputs,
            stdlib: self.stdlib,
            permissive_imports: self.permissive_imports,
            lean_args: self.lean_args,
            outputs,
        }
    }
}

/// Write the trace for an artifact this builder has just produced.
pub(crate) fn write_trace(
    olean: &Path,
    parts: &[PathBuf; 3],
    inputs: TraceInputs,
) -> LakeResult<()> {
    let trace = inputs.into_trace(digest_artifact_parts(parts)?);
    let json = serde_json::to_vec_pretty(&trace)
        .map_err(|e| std::io::Error::other(format!("serializing build trace: {e}")))?;
    std::fs::write(trace_path(olean), json)?;
    Ok(())
}

/// Remove a trace before its artifact is rewritten, so an interrupted or
/// failed build never leaves a trace next to files it does not describe.
pub(crate) fn remove_trace(olean: &Path) -> LakeResult<()> {
    match std::fs::remove_file(trace_path(olean)) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(e.into()),
    }
}

/// Why a module's artifact is not reused; `None` when it may be.
///
/// `permissive_now`: a trace written under `--permissive-imports` (whose
/// build may have continued past an import that failed to load) is reused
/// only by another permissive build.
pub(crate) fn reuse_refusal(
    olean: &Path,
    parts: &[PathBuf; 3],
    current: TraceInputs,
) -> LakeResult<Option<&'static str>> {
    let bytes = match std::fs::read(trace_path(olean)) {
        Ok(bytes) => bytes,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Some("no build trace")),
        Err(e) => return Err(e.into()),
    };
    let Ok(recorded) = serde_json::from_slice::<ModuleBuildTrace>(&bytes) else {
        return Ok(Some("unreadable build trace"));
    };
    if recorded.schema != TRACE_SCHEMA || recorded.builder != builder_identity() {
        return Ok(Some("trace from another builder"));
    }
    if recorded.permissive_imports && !current.permissive_imports {
        return Ok(Some("built with --permissive-imports"));
    }
    if recorded.lean_args != current.lean_args {
        return Ok(Some("leanOptions / moreLeanArgs changed"));
    }
    if recorded.source != digest_bytes(&current.source) {
        return Ok(Some("source changed"));
    }
    if recorded.inputs != current.inputs {
        return Ok(Some("a dependency's artifact changed"));
    }
    if recorded.stdlib != current.stdlib {
        return Ok(Some("an imported artifact outside the workspace changed"));
    }
    if recorded.outputs != digest_artifact_parts(parts)? {
        return Ok(Some("artifact differs from what this builder wrote"));
    }
    Ok(None)
}
