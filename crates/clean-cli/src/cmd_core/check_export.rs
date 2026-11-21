// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use anyhow::Context;
use clean_kernel::env::{ConstantOrigin, EnvEffect};
use clean_kernel::{Environment, LeanWorld, Name};
use clean_olean::ndjson::{write_export, ExportWriteMeta};
use std::collections::BTreeSet;
use std::io::BufWriter;
use std::path::{Path, PathBuf};

/// The post-header environment already contains the file's ordinary imports.
/// Filter late artifact imports and changes to pre-existing declarations while
/// retaining private names and auxiliary declarations registered by the body.
pub(super) fn entry_constants(
    before: &Environment,
    env: &Environment,
    effect: &EnvEffect,
) -> BTreeSet<Name> {
    effect
        .changed_constant_names()
        .filter(|name| {
            before.get_const(name).is_none()
                && !matches!(
                    env.get_constant_origin(name),
                    Some(ConstantOrigin::Olean { .. } | ConstantOrigin::CleanPayload { .. })
                )
        })
        .cloned()
        .collect()
}

/// The environment from the same check whose verdict decides publication.
#[derive(Debug)]
pub(super) struct CheckedExport {
    pub(super) destination: PathBuf,
    pub(super) env: Environment,
    pub(super) targets: BTreeSet<Name>,
}

impl CheckedExport {
    pub(super) fn publish(self, source: &Path, world: LeanWorld) -> anyhow::Result<()> {
        let meta = ExportWriteMeta::for_source_world(world)
            .with_context(|| format!("no measured Lean identity for NDJSON export of {world}"))?;
        if self.destination.canonicalize().ok().as_deref() == Some(source.canonicalize()?.as_path())
        {
            anyhow::bail!("the NDJSON export destination is the checked source file");
        }
        let directory = self
            .destination
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        let mut staging = tempfile::NamedTempFile::new_in(directory)
            .with_context(|| format!("create temporary export in {}", directory.display()))?;
        write_export(
            &self.env,
            &self.targets,
            &meta,
            BufWriter::new(staging.as_file_mut()),
        )
        .with_context(|| format!("write NDJSON export {}", self.destination.display()))?;
        staging
            .persist(&self.destination)
            .with_context(|| format!("publish NDJSON export {}", self.destination.display()))?;
        Ok(())
    }
}
