// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! COQ-0 corpus dump driver: turn the installed Coq 8.20 stdlib into
//! per-module `.sexp` dumps in the exact importer forms consumed by
//! `clean_mathverse::coq::alpha::CoqImporter::import_sexp`:
//!
//! ```text
//! (CoqConstant "<qualified>" <type-sexp> <value-sexp>)
//! (CoqAxiom    "<qualified>" <type-sexp>)
//! (CoqInductive "<qualified>" <block-idx> <arity> (NumParams k) (Ctor "<qc>" <ty>)...)
//! ```
//!
//! Term payloads are RAW SerAPI-native Constr sexps exactly as sertop returns
//! them (the importer's `normalize_if_serapi` rewrites them); names are fully
//! qualified (DirPath segments reversed + `MPdot` segments + Id). Enumeration
//! uses `Print Module <M>.` (plain-text `str` field of the Notice message);
//! classification is per-name live queries: `Definition` → `CoqConstr`
//! (constant with body) / `CoqMInd` (inductive) / empty (fall back to
//! `TypeOf` → axiom). Never silently drops a name: every non-emitted
//! candidate lands in the sidecar's `skipped` list with a reason.
//!
//! Usage:
//!   mathverse_coq_dump --out=DIR (--module=M ... | --modules-file=F | --stdlib)
//!       [--sertop=PATH] [--jobs=N] [--timeout=SECS] [--validate] [--force]
//!       [--coq-theories=DIR]

mod dump;
mod emit;
mod listing;
mod recon;
mod report;
mod sertop;
mod sexp_io;

use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::time::Duration;

use anyhow::{bail, Context, Result};

use dump::DumpConfig;
use report::{Outcome, Toolchain};

fn main() {
    if let Err(e) = run() {
        eprintln!("error: {e:#}");
        std::process::exit(1);
    }
}

fn default_opam_path(rel: &str) -> PathBuf {
    let home = std::env::var_os("HOME")
        .map(PathBuf::from)
        .unwrap_or_default();
    home.join(".opam/mathverse-serapi").join(rel)
}

fn run() -> Result<()> {
    let mut sertop_path = default_opam_path("bin/sertop");
    let mut theories = default_opam_path("lib/coq/theories");
    let mut out: Option<PathBuf> = None;
    let mut modules: Vec<String> = Vec::new();
    let mut stdlib = false;
    let mut jobs: usize = 1;
    let mut timeout_secs: u64 = 60;
    let mut validate = false;
    let mut force = false;

    for arg in std::env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("--sertop=") {
            sertop_path = PathBuf::from(v);
        } else if let Some(v) = arg.strip_prefix("--out=") {
            out = Some(PathBuf::from(v));
        } else if let Some(v) = arg.strip_prefix("--module=") {
            modules.push(v.to_string());
        } else if let Some(v) = arg.strip_prefix("--modules-file=") {
            let text =
                std::fs::read_to_string(v).with_context(|| format!("reading modules file {v}"))?;
            modules.extend(
                text.lines()
                    .map(str::trim)
                    .filter(|l| !l.is_empty() && !l.starts_with('#'))
                    .map(str::to_string),
            );
        } else if let Some(v) = arg.strip_prefix("--coq-theories=") {
            theories = PathBuf::from(v);
        } else if let Some(v) = arg.strip_prefix("--jobs=") {
            jobs = v.parse().context("--jobs expects a positive integer")?;
        } else if let Some(v) = arg.strip_prefix("--timeout=") {
            timeout_secs = v.parse().context("--timeout expects seconds")?;
        } else if arg == "--stdlib" {
            stdlib = true;
        } else if arg == "--validate" {
            validate = true;
        } else if arg == "--force" {
            force = true;
        } else {
            bail!("unknown argument: {arg}");
        }
    }
    let out = out.context("--out=<dir> is required")?;
    if stdlib {
        modules.extend(discover_stdlib(&theories)?);
    }
    // De-duplicate, preserving order.
    let mut seen = HashSet::new();
    modules.retain(|m| seen.insert(m.clone()));
    if modules.is_empty() {
        bail!("no modules selected: pass --module=, --modules-file=, or --stdlib");
    }
    if jobs == 0 {
        jobs = 1;
    }

    let serapi_version = sertop_version(&sertop_path)?;
    let coq_version = serapi_version
        .split('+')
        .next()
        .unwrap_or(&serapi_version)
        .to_string();
    let toolchain = Toolchain {
        coq: coq_version,
        serapi: serapi_version,
    };
    let cfg = DumpConfig {
        sertop_path,
        timeout: Duration::from_secs(timeout_secs),
        validate,
        toolchain: toolchain.clone(),
    };
    std::fs::create_dir_all(&out).with_context(|| format!("creating {}", out.display()))?;

    // Worker pool: each worker owns its own sertop process(es).
    let queue: Mutex<Vec<String>> = Mutex::new(modules.iter().rev().cloned().collect());
    let results: Mutex<Vec<(String, Outcome)>> = Mutex::new(Vec::new());
    std::thread::scope(|s| {
        for _ in 0..jobs.min(modules.len()) {
            s.spawn(|| loop {
                let module = {
                    let mut q = queue.lock().unwrap_or_else(|p| p.into_inner());
                    match q.pop() {
                        Some(m) => m,
                        None => return,
                    }
                };
                let started = std::time::Instant::now();
                let outcome = process_module(&cfg, &out, force, &module);
                log_outcome(&module, &outcome, started.elapsed());
                results
                    .lock()
                    .unwrap_or_else(|p| p.into_inner())
                    .push((module, outcome));
            });
        }
    });
    let results = results.into_inner().unwrap_or_else(|p| p.into_inner());
    report::write_manifest(&out, &toolchain, modules.len(), &results)
}

fn process_module(cfg: &DumpConfig, out: &Path, force: bool, module: &str) -> Outcome {
    let sexp_path = out.join(format!("{module}.sexp"));
    let meta_path = out.join(format!("{module}.meta.json"));
    if !force && sexp_path.exists() && meta_path.exists() {
        let meta = std::fs::read_to_string(&meta_path)
            .ok()
            .and_then(|s| serde_json::from_str(&s).ok());
        return Outcome::Fresh(meta);
    }
    match dump::dump_module(cfg, module, &sexp_path, &meta_path) {
        Ok(meta) => Outcome::Written(meta),
        Err(e) => Outcome::Failed(format!("{e:#}")),
    }
}

fn log_outcome(module: &str, outcome: &Outcome, elapsed: Duration) {
    match outcome {
        Outcome::Written(meta) => {
            let c = &meta.counts;
            eprintln!(
                "[coq-dump] {module}: {} constants ({} with value), {} axioms, {} inductives/{} ctors, {} skipped ({:.1}s)",
                c.constants,
                c.with_value,
                c.axioms,
                c.inductives,
                c.ctors,
                c.skipped.len(),
                elapsed.as_secs_f64()
            );
        }
        Outcome::Fresh(_) => {
            eprintln!("[coq-dump] {module}: fresh, skipped (use --force to redump)");
        }
        Outcome::Failed(e) => eprintln!("[coq-dump] {module}: FAILED: {e}"),
    }
}

fn sertop_version(path: &Path) -> Result<String> {
    let out = std::process::Command::new(path)
        .arg("--version")
        .output()
        .with_context(|| format!("running {} --version", path.display()))?;
    let v = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if v.is_empty() {
        bail!(
            "{} --version produced no output — is the mathverse-serapi opam switch installed?",
            path.display()
        );
    }
    Ok(v)
}

/// Walk `<theories>/**/*.v` (with a compiled `.vo` sibling) into logical
/// module names `Coq.<subdirs>.<stem>`.
fn discover_stdlib(theories: &Path) -> Result<Vec<String>> {
    fn walk(dir: &Path, root: &Path, out: &mut Vec<String>) -> std::io::Result<()> {
        for entry in std::fs::read_dir(dir)? {
            let path = entry?.path();
            if path.is_dir() {
                walk(&path, root, out)?;
            } else if path.extension().is_some_and(|e| e == "v")
                && path.with_extension("vo").exists()
            {
                let Ok(rel) = path.strip_prefix(root) else {
                    continue;
                };
                let mut segs: Vec<String> = vec!["Coq".to_string()];
                for comp in rel.components() {
                    segs.push(comp.as_os_str().to_string_lossy().into_owned());
                }
                if let Some(last) = segs.last_mut() {
                    *last = last.trim_end_matches(".v").to_string();
                }
                out.push(segs.join("."));
            }
        }
        Ok(())
    }
    let mut mods = Vec::new();
    walk(theories, theories, &mut mods)
        .with_context(|| format!("walking {}", theories.display()))?;
    if mods.is_empty() {
        bail!(
            "no compiled stdlib modules under {} — is the mathverse-serapi opam switch installed?",
            theories.display()
        );
    }
    mods.sort();
    Ok(mods)
}
