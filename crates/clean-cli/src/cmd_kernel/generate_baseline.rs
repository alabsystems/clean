// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean kernel generate-lean4-baseline` handler (#3445).
//!
//! In-process driver for the Lean 4 differential-testing baseline generator.
//! The underlying pipeline (`load_expressions` → `Lean4Baseline::generate` →
//! `Lean4Baseline::save`) lives in `clean_kernel::differential_baseline`; this
//! module forwards the optional `--output` path and, when absent, discovers a
//! workspace-relative default by walking upward for a `.git` directory.
//!
//! The legacy standalone binary baked the output path into the compiled
//! binary via `env!("CARGO_MANIFEST_DIR")`, which only resolves correctly when
//! invoked from `clean-kernel`. The unified CLI runs out of the `clean-cli`
//! (or top-level `clean`) package, so that environment variable no longer
//! points at the kernel crate. Runtime discovery keeps the default behaviour
//! byte-identical when invoked from inside the workspace.
//!
//! Part of Epic #3436 Phase 3 (#3445). See
//! `designs/2026-04-18-cli-orphan-inventory.md` §3.6.

use std::path::{Path, PathBuf};

use anyhow::Context;
use clean_kernel::differential_baseline::{load_expressions, Lean4Baseline, BASELINE_PATH};

/// Relative path from the workspace root to the kernel crate directory.
///
/// `BASELINE_PATH` is expressed relative to `crates/clean-kernel`
/// (`../../tests/differential/lean4_baseline.json` resolves to
/// `<workspace>/tests/differential/...` — but the legacy binary set
/// `CARGO_MANIFEST_DIR = <workspace>/crates/clean-kernel`, so joining
/// `BASELINE_PATH` onto that path produced `<workspace>/tests/differential/
/// lean4_baseline.json`). We replicate that resolution here so the output
/// location matches the legacy binary byte-for-byte.
const KERNEL_CRATE_DIR: &str = "crates/clean-kernel";

pub(super) fn run(output: Option<PathBuf>) -> anyhow::Result<()> {
    let baseline_path = resolve_output_path(output.as_deref())?;

    let expressions = load_expressions().context("failed to load expressions")?;
    let baseline = Lean4Baseline::generate(&expressions)?;
    baseline.save(&baseline_path)?;
    println!(
        "Saved Lean4 baseline to {} ({} cases).",
        baseline_path.display(),
        baseline.cases.len()
    );
    Ok(())
}

/// Resolve the output path from an optional `--output` override, falling back
/// to workspace-relative discovery via the enclosing `.git` directory.
fn resolve_output_path(explicit: Option<&Path>) -> anyhow::Result<PathBuf> {
    if let Some(path) = explicit {
        return Ok(path.to_path_buf());
    }
    let workspace_root = find_workspace_root().ok_or_else(|| {
        anyhow::anyhow!(
            "could not locate workspace root (no enclosing `.git` directory from {:?}); \
             pass --output <PATH> explicitly.",
            std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."))
        )
    })?;
    Ok(workspace_root.join(KERNEL_CRATE_DIR).join(BASELINE_PATH))
}

/// Walk up from the current working directory until a `.git` directory is
/// found. Returns `None` if no workspace root is located.
fn find_workspace_root() -> Option<PathBuf> {
    let mut dir = std::env::current_dir().ok()?;
    loop {
        if dir.join(".git").exists() {
            return Some(dir);
        }
        if !dir.pop() {
            return None;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn explicit_output_path_is_returned_verbatim() {
        let explicit = PathBuf::from("/tmp/explicit-baseline.json");
        let resolved = resolve_output_path(Some(&explicit)).expect("explicit path must resolve");
        assert_eq!(resolved, explicit);
    }

    #[test]
    fn workspace_discovery_matches_legacy_path_when_in_repo() {
        // When we are running this test from inside the clean workspace,
        // discovery must land on `<workspace>/crates/clean-kernel/../../tests/
        // differential/lean4_baseline.json` — i.e. the legacy binary's output.
        let resolved = match resolve_output_path(None) {
            Ok(path) => path,
            // Running outside a git checkout (e.g. a stripped archive) is a
            // valid state — treat it as "no workspace root" and skip the
            // positive assertion rather than flaking the test.
            Err(_) => return,
        };
        let as_str = resolved.to_string_lossy();
        assert!(
            as_str.ends_with("differential/lean4_baseline.json"),
            "resolved path `{as_str}` must end with the expected baseline filename"
        );
        assert!(
            as_str.contains("tests/differential"),
            "resolved path `{as_str}` must include tests/differential segment"
        );
    }
}
