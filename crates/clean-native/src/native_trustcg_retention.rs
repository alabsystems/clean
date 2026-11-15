// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Requested diagnostic retention has no effect on compilation authority.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use super::{serialize_tmbc, LaneError, Module, Receipt};

impl Receipt {
    /// Local diagnostic directory retained at the caller's request.
    #[must_use]
    pub fn retained_directory(&self) -> Option<&Path> {
        self.retained_directory.as_deref()
    }
}

/// Whether native build artifacts are removed or retained, including on failure.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub enum ScratchRetention {
    /// Delete scratch artifacts when the build or its executable is dropped.
    #[default]
    Remove,
    /// Retain diagnostic artifacts even when code generation or linking refuses.
    Keep,
}

pub(super) enum BuildScratch {
    Temporary(tempfile::TempDir),
    Retained(PathBuf),
}

impl BuildScratch {
    pub(super) fn new(retention: ScratchRetention) -> Result<Self, LaneError> {
        let scratch = tempfile::Builder::new()
            .prefix("clean-trustcg-")
            .tempdir()
            .map_err(|e| LaneError::Link(format!("could not create a scratch directory: {e}")))?;
        Ok(match retention {
            ScratchRetention::Remove => Self::Temporary(scratch),
            ScratchRetention::Keep => Self::Retained(scratch.keep()),
        })
    }

    pub(super) fn path(&self) -> &Path {
        match self {
            Self::Temporary(scratch) => scratch.path(),
            Self::Retained(path) => path,
        }
    }

    pub(super) fn keep(self) -> PathBuf {
        match self {
            Self::Temporary(scratch) => scratch.keep(),
            Self::Retained(path) => path,
        }
    }
}

pub(super) fn record_input(module: &Module, dir: &Path) -> Result<String, LaneError> {
    let bytes = serialize_tmbc(module).map_err(|e| LaneError::core("serialize")(e.into()))?;
    let digest: String = Sha256::digest(&bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    let write = |name: &str, bytes: &[u8]| {
        let path = dir.join(name);
        std::fs::write(&path, bytes)
            .map_err(|e| LaneError::TrustCg(format!("could not retain {}: {e}", path.display())))
    };
    write("module.tmbc", &bytes)?;
    write(
        "module.tmbc.sha256",
        format!("{digest}  module.tmbc\n").as_bytes(),
    )?;
    Ok(digest)
}

pub(super) fn record_receipt(receipt: &Receipt) {
    let Some(dir) = &receipt.retained_directory else {
        return;
    };
    let result = serde_json::to_vec_pretty(receipt)
        .map_err(std::io::Error::other)
        .and_then(|bytes| std::fs::write(dir.join("build-receipt.json"), bytes));
    if let Err(error) = result {
        // Keep the original compilation outcome/cause. This diagnostic is not
        // a second verdict and must never replace a backend's refusal.
        eprintln!(
            "clean: could not retain build receipt in {}: {error}",
            dir.display()
        );
    }
}
