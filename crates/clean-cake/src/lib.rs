// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cake build provenance + content-hash freshness.
//!
//! Cake is Clean's Layer-1 build system. This crate gives Cake a reproducible build
//! **signature** and a **content-hash freshness** predicate over any Lean `.olean`
//! artifact tree — whether Cake or an external Lean lake built it. It is the
//! trust-bearing alternative to a build system's timestamp-only `needs_rebuild`
//! heuristic: timestamps lie (a `git` checkout bumps a source's mtime without
//! changing its content), so a trust gate must reason about content.
//!
//! The decisive staleness signal is the **import-list diff**: every `.olean` records
//! its direct imports, and the `.lean` source carries its `import` lines. If the two
//! differ, the `.olean` predates the current source and is stale. That is exactly the
//! failure that once silently produced a `missing-from-environment` graduation
//! rejection: a root `.olean` whose recorded imports omitted a module the source had
//! since added (see `reports/invention-wave-graduation-2026-06-14.md`). Comparing
//! import lists catches it without timestamps, without a prior baseline, and without
//! a rebuild.
//!
//! Consumers (e.g. `clean mathverse graduate`) bind the resulting
//! [`CakeBuildSignature`] into their attestation next to the corpus pin, and refuse
//! to graduate from an environment Cake reports stale.
//!
//! ## Semantic identity ([`identity`])
//!
//! Beyond *build* provenance, Cake owns **semantic identity** — deciding when two
//! theorem statements are "the same object in different forms" so the corpus does
//! not count re-encodings as novel or miss them in search. See [`identity`] for the
//! tiered model (defeq-canonical digest + sound `is_def_eq` confirmation, and the
//! lineage of graded equivalence evidence toward the undecidable logical tier).

pub mod complexity;
pub mod goodness;
pub mod identity;
pub mod lineage;

use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

/// Schema tag for [`CakeBuildSignature`]; bump on any breaking field change.
pub const CAKE_BUILD_SIGNATURE_SCHEMA: &str = "cake-build-signature-v1";

/// Freshness of a single module's `.olean` relative to its `.lean` source.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum ModuleFreshness {
    /// `.olean` exists and its recorded direct imports match the source's imports.
    Fresh,
    /// `.olean` exists but its recorded direct imports differ from the source's
    /// `import` lines — the artifact predates the current source (the stale-olean bug).
    StaleImports,
    /// The source `.lean` exists but no `.olean` was built for it.
    MissingOlean,
    /// An `.olean` was requested for a module with no locatable `.lean` source.
    MissingSource,
}

impl ModuleFreshness {
    /// Is this module up to date?
    #[must_use]
    pub fn is_fresh(&self) -> bool {
        matches!(self, ModuleFreshness::Fresh)
    }

    /// Short kebab-case label (matches serde).
    #[must_use]
    pub fn label(&self) -> &'static str {
        match self {
            ModuleFreshness::Fresh => "fresh",
            ModuleFreshness::StaleImports => "stale-imports",
            ModuleFreshness::MissingOlean => "missing-olean",
            ModuleFreshness::MissingSource => "missing-source",
        }
    }
}

/// Per-module provenance: content digests + sorted import lists + freshness verdict.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleProvenance {
    /// Fully-qualified module name (e.g. `Crownproof.InventionWave4.bits_vs_split_dichotomy`).
    pub module: String,
    /// `blake3:<hex>` of the `.lean` source bytes, if the source was found.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_digest: Option<String>,
    /// `blake3:<hex>` of the `.olean` bytes, if the artifact was found.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub olean_digest: Option<String>,
    /// Direct imports parsed from the `.lean` source (sorted, deduped).
    pub source_imports: Vec<String>,
    /// Direct imports recorded in the `.olean` (sorted, deduped).
    pub olean_imports: Vec<String>,
    /// Content-hash freshness verdict.
    pub freshness: ModuleFreshness,
}

/// A Cake build signature over a set of modules: a reproducible environment
/// fingerprint plus a content-hash freshness verdict.
///
/// Reproducible: the same sources + `.oleans` + toolchain always yield the same
/// `env_digest`, so a verifier can recompute and compare. `fresh` is true iff every
/// module is [`ModuleFreshness::Fresh`].
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CakeBuildSignature {
    /// Schema tag ([`CAKE_BUILD_SIGNATURE_SCHEMA`]).
    pub schema: String,
    /// `lean-toolchain` identifier, if known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub toolchain: Option<String>,
    /// Per-module provenance, sorted by module name.
    pub modules: Vec<ModuleProvenance>,
    /// `blake3:<hex>` over the canonical (schema, toolchain, per-module digests +
    /// source imports) record. Determinism anchor.
    pub env_digest: String,
    /// True iff every module is fresh.
    pub fresh: bool,
    /// `"<module> (<status>)"` for each non-fresh module — actionable error detail.
    pub stale_modules: Vec<String>,
}

impl CakeBuildSignature {
    /// A human-actionable one-line summary of any staleness.
    #[must_use]
    pub fn staleness_summary(&self) -> Option<String> {
        if self.fresh {
            return None;
        }
        Some(format!(
            "Cake reports {} stale module(s): {} — rebuild (`clean lake build`) so the \
             .olean artifacts reflect current source.",
            self.stale_modules.len(),
            self.stale_modules.join(", ")
        ))
    }
}

/// Parse direct `import` module names from Lean source text.
///
/// Content-only and deliberately NOT stdlib-filtered: we compare against the
/// `.olean`'s full recorded import list, so both sides must use the same universe.
#[must_use]
pub fn parse_source_imports(source: &str) -> Vec<String> {
    let mut imports = Vec::new();
    for line in source.lines() {
        let line = line.trim();
        if line.starts_with("--") {
            continue;
        }
        if let Some(rest) = line.strip_prefix("import ") {
            // Take the module token; ignore a leading `runtime`/`meta` qualifier and
            // any trailing comment.
            let mut tok = rest.trim();
            for qualifier in ["runtime ", "meta "] {
                if let Some(stripped) = tok.strip_prefix(qualifier) {
                    tok = stripped.trim();
                }
            }
            let name = tok.split_whitespace().next().unwrap_or("");
            if !name.is_empty() {
                imports.push(name.to_string());
            }
        }
    }
    imports
}

/// Pure freshness classifier — decide a module's status from presence + import lists.
///
/// No filesystem; unit-testable in isolation. Order- and multiplicity-insensitive.
///
/// **Fresh iff every source `import` is present in the `.olean`'s recorded imports**
/// (subset, not equality). The `.olean` legitimately records MORE than the source's
/// explicit `import` lines — Lean auto-adds the implicit `Init`/prelude import — and
/// those extras are benign. The failure this guards is the dangerous direction: the
/// source declares an import the `.olean` LACKS, i.e. the artifact predates the
/// current source (a module was added but the `.olean` wasn't rebuilt — the
/// stale-root-olean bug). An `.olean` that is a superset of the current imports
/// (source dropped an import) still contains everything the source needs, so it is
/// not flagged: this predicate targets MISSING declarations, the failure that
/// surfaced as a silent `missing-from-environment` graduation rejection.
#[must_use]
pub fn classify_freshness(
    source_present: bool,
    olean_present: bool,
    src_imports: &[String],
    olean_imports: &[String],
) -> ModuleFreshness {
    if !source_present {
        return ModuleFreshness::MissingSource;
    }
    if !olean_present {
        return ModuleFreshness::MissingOlean;
    }
    let olean_set: std::collections::HashSet<&str> =
        olean_imports.iter().map(String::as_str).collect();
    let any_source_import_missing = src_imports
        .iter()
        .any(|imp| !olean_set.contains(imp.as_str()));
    if any_source_import_missing {
        ModuleFreshness::StaleImports
    } else {
        ModuleFreshness::Fresh
    }
}

fn blake3_hex(bytes: &[u8]) -> String {
    format!("blake3:{}", blake3::hash(bytes).to_hex())
}

fn sorted_deduped(mut v: Vec<String>) -> Vec<String> {
    v.sort();
    v.dedup();
    v
}

/// Compute provenance for one module from its source `.lean` and artifact `.olean`
/// paths. Missing files are reflected in the freshness verdict, not errors.
#[must_use]
pub fn module_provenance(module: &str, source_path: &Path, olean_path: &Path) -> ModuleProvenance {
    let source_bytes = std::fs::read(source_path).ok();
    let olean_bytes = std::fs::read(olean_path).ok();

    let src_imports_raw = source_bytes
        .as_deref()
        .map(|b| parse_source_imports(&String::from_utf8_lossy(b)))
        .unwrap_or_default();
    let olean_imports_raw: Vec<String> = olean_bytes
        .as_deref()
        .and_then(|b| clean_olean::parse_imports_only(b).ok())
        .map(|imps| imps.into_iter().map(|i| i.module_name).collect())
        .unwrap_or_default();

    let freshness = classify_freshness(
        source_bytes.is_some(),
        olean_bytes.is_some(),
        &src_imports_raw,
        &olean_imports_raw,
    );

    ModuleProvenance {
        module: module.to_string(),
        source_digest: source_bytes.as_deref().map(blake3_hex),
        olean_digest: olean_bytes.as_deref().map(blake3_hex),
        source_imports: sorted_deduped(src_imports_raw),
        olean_imports: sorted_deduped(olean_imports_raw),
        freshness,
    }
}

/// Build a [`CakeBuildSignature`] over `modules`, resolving each module's
/// `(source_path, olean_path)` via `paths`.
///
/// Decoupled from [`crate::workspace::Workspace`] for testability; callers with a
/// workspace use [`signature_for_workspace`].
pub fn build_signature(
    modules: &[String],
    toolchain: Option<String>,
    mut paths: impl FnMut(&str) -> (PathBuf, PathBuf),
) -> CakeBuildSignature {
    let mut provs: Vec<ModuleProvenance> = modules
        .iter()
        .map(|m| {
            let (src, olean) = paths(m);
            module_provenance(m, &src, &olean)
        })
        .collect();
    provs.sort_by(|a, b| a.module.cmp(&b.module));

    let stale_modules: Vec<String> = provs
        .iter()
        .filter(|p| !p.freshness.is_fresh())
        .map(|p| format!("{} ({})", p.module, p.freshness.label()))
        .collect();
    let fresh = stale_modules.is_empty();
    let env_digest = compute_env_digest(&provs, toolchain.as_deref());

    CakeBuildSignature {
        schema: CAKE_BUILD_SIGNATURE_SCHEMA.to_string(),
        toolchain,
        modules: provs,
        env_digest,
        fresh,
        stale_modules,
    }
}

/// Module name → relative path stem (`A.B.C` → `A/B/C`), no extension.
fn module_rel_path(module: &str) -> PathBuf {
    module.split('.').collect::<PathBuf>()
}

/// Resolve a module's `.olean` against ordered search-path roots (first hit wins).
/// Returns the candidate under the first root when none exist, so the absence is
/// reflected as [`ModuleFreshness::MissingOlean`] rather than a panic.
fn resolve_olean(module: &str, olean_search_paths: &[PathBuf]) -> PathBuf {
    let rel = module_rel_path(module).with_extension("olean");
    for root in olean_search_paths {
        let cand = root.join(&rel);
        if cand.exists() {
            return cand;
        }
    }
    olean_search_paths
        .first()
        .map(|r| r.join(&rel))
        .unwrap_or(rel)
}

/// Build a signature for a real project layout: `.lean` sources under `source_root`
/// and `.oleans` under `olean_search_paths` (the same roots passed to graduation's
/// `--olean-search-path`). This is the API graduation and `clean lake verify-fresh`
/// call.
#[must_use]
pub fn signature_from_search_paths(
    modules: &[String],
    source_root: &Path,
    olean_search_paths: &[PathBuf],
    toolchain: Option<String>,
) -> CakeBuildSignature {
    build_signature(modules, toolchain, |m| {
        let source = source_root.join(module_rel_path(m).with_extension("lean"));
        let olean = resolve_olean(m, olean_search_paths);
        (source, olean)
    })
}

/// Canonical, sorted, content-only `env_digest`. `provs` MUST already be sorted by
/// module name (as [`build_signature`] guarantees) so the digest is reproducible.
fn compute_env_digest(provs: &[ModuleProvenance], toolchain: Option<&str>) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(CAKE_BUILD_SIGNATURE_SCHEMA.as_bytes());
    hasher.update(b"\0toolchain\0");
    hasher.update(toolchain.unwrap_or("").as_bytes());
    for p in provs {
        hasher.update(b"\0module\0");
        hasher.update(p.module.as_bytes());
        hasher.update(b"\0source\0");
        hasher.update(p.source_digest.as_deref().unwrap_or("").as_bytes());
        hasher.update(b"\0olean\0");
        hasher.update(p.olean_digest.as_deref().unwrap_or("").as_bytes());
        for imp in &p.source_imports {
            hasher.update(b"\0import\0");
            hasher.update(imp.as_bytes());
        }
    }
    format!("blake3:{}", hasher.finalize().to_hex())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|x| (*x).to_string()).collect()
    }

    #[test]
    fn test_classify_fresh_when_imports_match_any_order() {
        let src = s(&["A", "B", "C"]);
        let olean = s(&["C", "A", "B"]); // same set, different order
        assert_eq!(
            classify_freshness(true, true, &src, &olean),
            ModuleFreshness::Fresh
        );
    }

    #[test]
    fn test_classify_stale_when_source_added_an_import() {
        // THE regression: source gained an import the .olean was built before.
        // (root Crownproof.lean imported bits_vs_split_dichotomy; stale olean did not.)
        let src = s(&[
            "Crownproof.Complete",
            "Crownproof.InventionWave4.bits_vs_split_dichotomy",
        ]);
        let olean = s(&["Crownproof.Complete"]);
        assert_eq!(
            classify_freshness(true, true, &src, &olean),
            ModuleFreshness::StaleImports
        );
    }

    #[test]
    fn test_classify_missing_olean_and_source() {
        assert_eq!(
            classify_freshness(true, false, &[], &[]),
            ModuleFreshness::MissingOlean
        );
        assert_eq!(
            classify_freshness(false, true, &[], &[]),
            ModuleFreshness::MissingSource
        );
    }

    #[test]
    fn test_parse_source_imports_basic_and_comments() {
        let src = "\
import Crownproof.Complete
-- import Crownproof.Ignored  (commented out)
import Crownproof.InventionWave4.slack_delta_domains
open Crownproof
theorem foo : True := trivial
import Crownproof.LateImport
";
        let imports = parse_source_imports(src);
        assert_eq!(
            imports,
            s(&[
                "Crownproof.Complete",
                "Crownproof.InventionWave4.slack_delta_domains",
                "Crownproof.LateImport"
            ])
        );
    }

    #[test]
    fn test_env_digest_is_deterministic_and_order_independent() {
        let paths = |_m: &str| {
            (
                PathBuf::from("/nonexistent.lean"),
                PathBuf::from("/nonexistent.olean"),
            )
        };
        let a = build_signature(&s(&["A", "B"]), Some("v4.30.0".into()), paths);
        let b = build_signature(&s(&["B", "A"]), Some("v4.30.0".into()), paths);
        // Same module set ⇒ same digest regardless of input order (build_signature sorts).
        assert_eq!(a.env_digest, b.env_digest);
        // Toolchain participates in the digest.
        let c = build_signature(&s(&["A", "B"]), Some("v4.31.0".into()), paths);
        assert_ne!(a.env_digest, c.env_digest);
    }

    #[test]
    fn test_signature_flags_stale_modules_with_summary() {
        // Both modules resolve to missing files ⇒ MissingSource ⇒ not fresh.
        let paths = |_m: &str| (PathBuf::from("/nope.lean"), PathBuf::from("/nope.olean"));
        let sig = build_signature(&s(&["X", "Y"]), None, paths);
        assert!(!sig.fresh);
        assert_eq!(sig.stale_modules.len(), 2);
        assert!(sig.staleness_summary().is_some());
    }

    #[test]
    fn test_classify_fresh_when_olean_has_extra_implicit_imports() {
        // Lean auto-adds `Init`: the .olean records a SUPERSET of the source's
        // explicit imports. That must read Fresh, not stale (the e2e false positive
        // this fix closes — a freshly-built module was wrongly flagged stale).
        let src = s(&["Crownproof.Complete", "Crownproof.CompleteIBP"]);
        let olean = s(&["Crownproof.Complete", "Crownproof.CompleteIBP", "Init"]);
        assert_eq!(
            classify_freshness(true, true, &src, &olean),
            ModuleFreshness::Fresh
        );
    }

    #[test]
    fn test_signature_from_search_paths_resolves_layout() {
        // A real source tree with a source but no built .olean ⇒ MissingOlean,
        // exercising module→path resolution (A.B.C → A/B/C.{lean,olean}).
        let tmp = tempfile::tempdir().unwrap();
        let src_root = tmp.path().join("src");
        std::fs::create_dir_all(src_root.join("Pkg/Sub")).unwrap();
        std::fs::write(
            src_root.join("Pkg/Sub/Mod.lean"),
            "import Pkg.Other\ntheorem t : True := trivial\n",
        )
        .unwrap();
        let olean_root = tmp.path().join("build");
        std::fs::create_dir_all(&olean_root).unwrap();

        let sig = signature_from_search_paths(
            &s(&["Pkg.Sub.Mod"]),
            &src_root,
            std::slice::from_ref(&olean_root),
            Some("v4.30.0".into()),
        );
        assert_eq!(sig.modules.len(), 1);
        let m = &sig.modules[0];
        assert_eq!(m.module, "Pkg.Sub.Mod");
        assert!(m.source_digest.is_some(), "source should be found + hashed");
        assert_eq!(m.source_imports, s(&["Pkg.Other"]));
        assert_eq!(m.freshness, ModuleFreshness::MissingOlean);
        assert!(!sig.fresh);
    }
}
