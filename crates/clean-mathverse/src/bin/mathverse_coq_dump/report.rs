// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sidecar (`<module>.meta.json`) and top-level `manifest.json` schema plus
//! aggregation. Every non-emitted name is COUNTED here (skipped-with-reason);
//! coinductive axiomatization is a first-class counter, never silent.

use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Toolchain {
    pub coq: String,
    pub serapi: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SkipEntry {
    pub name: String,
    pub reason: String,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Counts {
    pub constants: u32,
    pub with_value: u32,
    pub axioms: u32,
    pub inductives: u32,
    pub ctors: u32,
    pub coinductive_axiomatized: u32,
    pub prim_records: u32,
    /// Record/class blocks (`mind_finite = BiFinite`) emitted as ordinary
    /// `CoqInductive` forms (they are non-recursive kernel inductives).
    #[serde(default)]
    pub records: u32,
    /// Inductive packets whose `TemplateArity` conclusion was collapsed to
    /// the shared single-level `Type` model at emission (template contract).
    #[serde(default)]
    pub template_collapsed: u32,
    /// Informational limitations that are NOT skips (e.g. primitive-record
    /// accessor bodies being `Proj`-valued, which sertop 8.20 cannot
    /// serialize) — counted so nothing is silent.
    #[serde(default)]
    pub notes: Vec<String>,
    pub skipped: Vec<SkipEntry>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ValidateStats {
    pub total: u32,
    pub translated: u32,
    pub axiomatized: u32,
    pub skipped: u32,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ModuleMeta {
    pub module: String,
    pub toolchain: Toolchain,
    pub counts: Counts,
    /// Nested modules that were recursively enumerated (their declarations
    /// are included in this module's dump).
    #[serde(default)]
    pub submodules: Vec<String>,
    pub validate: Option<ValidateStats>,
    pub generated_unix_ts: u64,
}

#[derive(Serialize)]
pub struct FailedModule {
    pub module: String,
    pub error: String,
}

#[derive(Default, Serialize)]
pub struct Totals {
    pub constants: u32,
    pub with_value: u32,
    pub axioms: u32,
    pub inductives: u32,
    pub ctors: u32,
    pub coinductive_axiomatized: u32,
    pub prim_records: u32,
    pub records: u32,
    pub template_collapsed: u32,
    pub skipped: u32,
}

#[derive(Serialize)]
pub struct Manifest {
    pub generated_unix_ts: u64,
    pub toolchain: Toolchain,
    pub modules_requested: usize,
    pub modules_written: usize,
    pub modules_fresh: usize,
    pub modules_failed: Vec<FailedModule>,
    pub totals: Totals,
    pub validate_totals: Option<ValidateStats>,
}

/// Per-module pipeline outcome.
pub enum Outcome {
    Written(ModuleMeta),
    /// Existing dump kept (`--force` absent); meta reloaded when parseable.
    Fresh(Option<ModuleMeta>),
    Failed(String),
}

pub fn unix_ts() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// Aggregate per-module outcomes into `<out>/manifest.json`. Fails (after
/// writing the manifest) when any module failed outright.
pub fn write_manifest(
    out_dir: &std::path::Path,
    toolchain: &Toolchain,
    requested: usize,
    results: &[(String, Outcome)],
) -> Result<()> {
    let mut totals = Totals::default();
    let mut validate_totals: Option<ValidateStats> = None;
    let mut written = 0usize;
    let mut fresh = 0usize;
    let mut failed = Vec::new();
    for (module, outcome) in results {
        let meta = match outcome {
            Outcome::Written(m) => {
                written += 1;
                Some(m)
            }
            Outcome::Fresh(m) => {
                fresh += 1;
                m.as_ref()
            }
            Outcome::Failed(e) => {
                failed.push(FailedModule {
                    module: module.clone(),
                    error: e.clone(),
                });
                None
            }
        };
        let Some(meta) = meta else { continue };
        let c = &meta.counts;
        totals.constants += c.constants;
        totals.with_value += c.with_value;
        totals.axioms += c.axioms;
        totals.inductives += c.inductives;
        totals.ctors += c.ctors;
        totals.coinductive_axiomatized += c.coinductive_axiomatized;
        totals.prim_records += c.prim_records;
        totals.records += c.records;
        totals.template_collapsed += c.template_collapsed;
        totals.skipped += c.skipped.len() as u32;
        if let Some(v) = &meta.validate {
            let agg = validate_totals.get_or_insert(ValidateStats {
                total: 0,
                translated: 0,
                axiomatized: 0,
                skipped: 0,
            });
            agg.total += v.total;
            agg.translated += v.translated;
            agg.axiomatized += v.axiomatized;
            agg.skipped += v.skipped;
        }
    }
    let manifest = Manifest {
        generated_unix_ts: unix_ts(),
        toolchain: toolchain.clone(),
        modules_requested: requested,
        modules_written: written,
        modules_fresh: fresh,
        modules_failed: failed,
        totals,
        validate_totals,
    };
    let path = out_dir.join("manifest.json");
    std::fs::write(&path, serde_json::to_string_pretty(&manifest)?)
        .with_context(|| format!("writing {}", path.display()))?;
    eprintln!(
        "[coq-dump] manifest: {} ({} written, {} fresh, {} failed)",
        path.display(),
        written,
        fresh,
        manifest.modules_failed.len()
    );
    if !manifest.modules_failed.is_empty() {
        bail!(
            "{} module(s) failed — see manifest.json",
            manifest.modules_failed.len()
        );
    }
    Ok(())
}
