// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hidden diagnostic: write the CONTENT digest of the environment `clean
//! check` finished with.
//!
//! On an import-only file that environment is exactly what the `.olean`
//! import built, so two binaries that must build the same environment can be
//! compared byte for byte (P1_IMPORT: the per-module import passes were made
//! proportional to what a module adds, and this is the proof that nothing but
//! time changed). Off unless the variable is set; it never alters a verdict.

use clean_kernel::Environment;
use std::path::PathBuf;
use std::time::Instant;

/// Names the file that receives the digest summary; the per-entry lines go
/// to the same path with `.entries` appended.
pub(crate) const ENV_DIGEST_OUT_ENV: &str = "CLEAN_CHECK_ENV_DIGEST_OUT";

/// Write the digest when [`ENV_DIGEST_OUT_ENV`] is set; a no-op otherwise.
pub(crate) fn write_env_digest_if_requested(env: &Environment) -> anyhow::Result<()> {
    let Some(out) = std::env::var_os(ENV_DIGEST_OUT_ENV) else {
        return Ok(());
    };
    let start = Instant::now();
    let digest = env.content_digest();
    let summary_path = PathBuf::from(&out);
    let mut entries_path = out;
    entries_path.push(".entries");
    std::fs::write(&summary_path, digest.render_summary())?;
    std::fs::write(PathBuf::from(entries_path), digest.render_entries())?;
    eprintln!(
        "env content digest {} written to {} in {:.1}s",
        digest.total,
        summary_path.display(),
        start.elapsed().as_secs_f64()
    );
    Ok(())
}
