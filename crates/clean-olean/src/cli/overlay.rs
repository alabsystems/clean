// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Namespace overlay payload generator — library form.
//!
//! Ported from `crates/clean-olean/src/bin/generate_namespace_overlay.rs`
//! (#3442). The standalone binary becomes a thin compat shim that constructs
//! an [`OverlayConfig`] from `env::args` and calls
//! [`generate_namespace_overlay`]. The `clean olean generate-overlay`
//! subcommand dispatches here directly; no process forking, no string-shaped
//! error surface.
//!
//! Epic: #3436. Design:
//! `designs/2026-04-18-unified-cli-feature-index.md`.

use std::fs;
use std::path::{Path, PathBuf};

use clean_kernel::env::{ConstantInfo, Environment};

use crate::{default_search_paths, load_module_with_deps};

/// Configuration for a namespace-overlay generation run.
///
/// Parameters mirror the historical flag surface of
/// `generate_namespace_overlay` — see `clean help olean generate-overlay`.
#[derive(Debug, Clone, Default)]
pub struct OverlayConfig {
    /// Output directory for emitted `<module>.rs` and `<module>.payload.bin`
    /// files (plus the top-level `mod.rs`).
    pub output_dir: PathBuf,
    /// Namespace prefixes to snapshot. Each produces one overlay module.
    pub namespaces: Vec<String>,
    /// `.olean` modules to load into the source environment before
    /// snapshotting.
    pub modules: Vec<String>,
    /// `.olean` search paths. Empty ⇒ fall back to
    /// [`default_search_paths`](crate::default_search_paths).
    pub search_paths: Vec<PathBuf>,
    /// Seed `Topology.Manifold` and `Topology.LieGroup` via the kernel's
    /// overlay init helpers. Required when stdlib `.olean` files do not
    /// contain the requested namespaces on this machine.
    pub seed_topology_env: bool,
}

/// Per-namespace summary returned after a successful generation run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamespaceSummary {
    /// Namespace prefix that was snapshotted (e.g. `"Topology.Manifold"`).
    pub namespace: String,
    /// Emitted Rust module name (e.g. `"topology_manifold"`).
    pub module_name: String,
    /// Number of `ConstantInfo` entries serialized into the payload blob.
    pub decl_count: usize,
}

/// Aggregate report returned by [`generate_namespace_overlay`].
#[derive(Debug, Clone, Default)]
pub struct OverlayReport {
    /// One entry per namespace in the input order, deduplicated for the
    /// `mod.rs` listing.
    pub namespaces: Vec<NamespaceSummary>,
}

/// Errors raised while generating namespace overlays.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum OverlayError {
    /// `--output-dir` was not supplied.
    #[error("--output-dir is required")]
    MissingOutputDir,
    /// At least one `--namespace` is required.
    #[error("at least one --namespace is required")]
    NoNamespaces,
    /// `.olean` module load failed.
    #[error("failed loading module `{module}`: {source}")]
    ModuleLoad {
        /// Module name that failed to load.
        module: String,
        /// Upstream error from [`load_module_with_deps`].
        #[source]
        source: crate::ImportError,
    },
    /// Kernel init for a seeded topology namespace failed.
    #[error("topology seed `{what}` failed: {reason}")]
    TopologySeed {
        /// Which init helper reported the failure.
        what: &'static str,
        /// Kernel error message.
        reason: String,
    },
    /// No constants matched the requested namespace prefix.
    #[error("namespace `{0}` produced no constants; check --module / --search-path inputs")]
    EmptyNamespace(String),
    /// `bincode` serialization of the payload blob failed.
    #[error("bincode serialize failed for `{namespace}`: {source}")]
    Serialize {
        /// Namespace whose payload failed to serialize.
        namespace: String,
        /// Underlying bincode error.
        #[source]
        source: bincode::error::EncodeError,
    },
    /// Filesystem I/O (create dir, write file) failed.
    #[error("I/O error for `{path}`: {source}")]
    Io {
        /// Path that triggered the I/O error.
        path: PathBuf,
        /// Underlying OS error.
        #[source]
        source: std::io::Error,
    },
}

/// Generate namespace overlay payload modules under `cfg.output_dir`.
///
/// This is the library entry point used by both the compat binary and the
/// `clean olean generate-overlay` subcommand. See the `OverlayConfig` docs
/// for the argument contract.
pub fn generate_namespace_overlay(cfg: &OverlayConfig) -> Result<OverlayReport, OverlayError> {
    if cfg.output_dir.as_os_str().is_empty() {
        return Err(OverlayError::MissingOutputDir);
    }
    if cfg.namespaces.is_empty() {
        return Err(OverlayError::NoNamespaces);
    }

    fs::create_dir_all(&cfg.output_dir).map_err(|source| OverlayError::Io {
        path: cfg.output_dir.clone(),
        source,
    })?;

    let env = load_source_environment(cfg)?;

    let mut report = OverlayReport::default();
    let mut module_names: Vec<String> = Vec::new();
    for namespace in &cfg.namespaces {
        let payload = collect_namespace_payload(&env, namespace);
        if payload.is_empty() {
            return Err(OverlayError::EmptyNamespace(namespace.clone()));
        }

        let module_name = emit_namespace_module(&cfg.output_dir, namespace, &payload)?;
        report.namespaces.push(NamespaceSummary {
            namespace: namespace.clone(),
            module_name: module_name.clone(),
            decl_count: payload.len(),
        });
        module_names.push(module_name);
    }

    module_names.sort();
    module_names.dedup();
    emit_generated_mod(&cfg.output_dir, &module_names)?;
    Ok(report)
}

fn load_source_environment(cfg: &OverlayConfig) -> Result<Environment, OverlayError> {
    let mut env = Environment::default();

    let search_paths = if cfg.search_paths.is_empty() {
        default_search_paths()
    } else {
        cfg.search_paths.clone()
    };

    for module in &cfg.modules {
        load_module_with_deps(&mut env, module, &search_paths).map_err(|source| {
            OverlayError::ModuleLoad {
                module: module.clone(),
                source,
            }
        })?;
    }

    if cfg.seed_topology_env {
        env.init_topology_manifold()
            .map_err(|err| OverlayError::TopologySeed {
                what: "init_topology_manifold",
                reason: err.to_string(),
            })?;
        env.init_topology_lie_group()
            .map_err(|err| OverlayError::TopologySeed {
                what: "init_topology_lie_group",
                reason: err.to_string(),
            })?;
    }

    Ok(env)
}

fn to_snake_case(part: &str) -> String {
    let mut out = String::with_capacity(part.len());
    let mut prev_is_lower_or_digit = false;

    for ch in part.chars() {
        if ch.is_ascii_uppercase() {
            if prev_is_lower_or_digit {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
            prev_is_lower_or_digit = false;
        } else if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
            prev_is_lower_or_digit = ch.is_ascii_lowercase() || ch.is_ascii_digit();
        } else {
            out.push('_');
            prev_is_lower_or_digit = false;
        }
    }

    out
}

#[must_use]
pub(crate) fn namespace_to_module_name(namespace: &str) -> String {
    namespace
        .split('.')
        .filter(|part| !part.is_empty())
        .map(to_snake_case)
        .collect::<Vec<_>>()
        .join("_")
}

#[must_use]
pub(crate) fn is_in_namespace(name: &str, namespace: &str) -> bool {
    name == namespace
        || name
            .strip_prefix(namespace)
            .is_some_and(|suffix| suffix.starts_with('.'))
}

fn collect_namespace_payload(env: &Environment, namespace: &str) -> Vec<ConstantInfo> {
    let mut payload: Vec<ConstantInfo> = env
        .constants()
        .filter(|info| is_in_namespace(&info.name.to_string(), namespace))
        .cloned()
        .collect();

    payload.sort_by_key(|info| info.name.to_string());
    payload
}

fn emit_namespace_module(
    output_dir: &Path,
    namespace: &str,
    payload: &[ConstantInfo],
) -> Result<String, OverlayError> {
    let module_name = namespace_to_module_name(namespace);
    let source_path = output_dir.join(format!("{module_name}.rs"));
    let payload_file_name = format!("{module_name}.payload.bin");
    let payload_path = output_dir.join(&payload_file_name);

    let payload_bytes = bincode::serde::encode_to_vec(payload, bincode::config::standard())
        .map_err(|source| OverlayError::Serialize {
            namespace: namespace.to_owned(),
            source,
        })?;
    fs::write(&payload_path, &payload_bytes).map_err(|source| OverlayError::Io {
        path: payload_path.clone(),
        source,
    })?;

    let decl_names: Vec<String> = payload.iter().map(|info| info.name.to_string()).collect();

    let mut content = String::new();
    content.push_str("// Copyright 2026 Andrew Yates <andrewyates.name@gmail.com>\n");
    content.push_str("// Author: Andrew Yates <andrewyates.name@gmail.com>\n");
    content.push_str("// SPDX-License-Identifier: Apache-2.0\n\n");
    content.push_str("// @generated by clean-olean::cli::overlay.\n");
    content.push_str("// Do not edit manually. Regenerate via:\n");
    content.push_str("// clean olean generate-overlay --namespace <...> --output-dir <...>\n\n");
    content.push_str("use crate::env::types::ConstantInfo;\n\n");
    content.push_str(&format!(
        "pub(crate) const NAMESPACE: &str = \"{namespace}\";\n"
    ));
    content.push_str(&format!(
        "pub(crate) const DECL_COUNT: usize = {};\n\n",
        decl_names.len()
    ));

    content.push_str(&format!(
        "pub(crate) const DECL_NAMES: [&str; {}] = [\n",
        decl_names.len()
    ));
    for name in &decl_names {
        content.push_str(&format!("    \"{name}\",\n"));
    }
    content.push_str("];\n\n");

    content.push_str(&format!(
        "const PAYLOAD_BYTES: &[u8] = include_bytes!(\"{payload_file_name}\");\n\n"
    ));

    content.push_str("pub(crate) fn payload() -> Vec<ConstantInfo> {\n");
    content.push_str("    bincode::serde::decode_from_slice(PAYLOAD_BYTES, bincode::config::standard()).map(|(__v, _)| __v)\n");
    content.push_str("        .expect(\"generated overlay payload bytes should deserialize\")\n");
    content.push_str("}\n");

    fs::write(&source_path, content).map_err(|source| OverlayError::Io {
        path: source_path.clone(),
        source,
    })?;

    Ok(module_name)
}

fn emit_generated_mod(output_dir: &Path, module_names: &[String]) -> Result<(), OverlayError> {
    let file_path = output_dir.join("mod.rs");
    let mut content = String::new();
    content.push_str("// Copyright 2026 Andrew Yates <andrewyates.name@gmail.com>\n");
    content.push_str("// Author: Andrew Yates <andrewyates.name@gmail.com>\n");
    content.push_str("// SPDX-License-Identifier: Apache-2.0\n\n");
    content.push_str("// @generated by clean-olean::cli::overlay.\n\n");

    for module_name in module_names {
        content.push_str(&format!("pub(crate) mod {module_name};\n"));
    }

    fs::write(&file_path, content).map_err(|source| OverlayError::Io {
        path: file_path.clone(),
        source,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_namespace_to_module_name() {
        assert_eq!(
            namespace_to_module_name("Topology.Manifold"),
            "topology_manifold"
        );
        assert_eq!(
            namespace_to_module_name("Mathlib.Algebra.Linear"),
            "mathlib_algebra_linear"
        );
    }

    #[test]
    fn test_is_in_namespace_uses_dot_boundary() {
        assert!(is_in_namespace(
            "Topology.Manifold.Chart",
            "Topology.Manifold"
        ));
        assert!(is_in_namespace("Topology.Manifold", "Topology.Manifold"));
        assert!(!is_in_namespace(
            "Topology.Manifoldoid.Chart",
            "Topology.Manifold"
        ));
    }

    #[test]
    fn test_missing_output_dir_rejected() {
        let cfg = OverlayConfig {
            output_dir: PathBuf::new(),
            namespaces: vec!["Foo".to_owned()],
            seed_topology_env: true,
            ..OverlayConfig::default()
        };
        let err = generate_namespace_overlay(&cfg).expect_err("empty output_dir must fail");
        assert!(matches!(err, OverlayError::MissingOutputDir));
    }

    #[test]
    fn test_no_namespaces_rejected() {
        let cfg = OverlayConfig {
            output_dir: PathBuf::from("/tmp"),
            namespaces: vec![],
            seed_topology_env: true,
            ..OverlayConfig::default()
        };
        let err = generate_namespace_overlay(&cfg).expect_err("no namespaces must fail");
        assert!(matches!(err, OverlayError::NoNamespaces));
    }

    #[test]
    fn test_seeded_overlay_emits_modules() {
        // Validates the end-to-end pipeline with the in-process kernel seed:
        // create temp output dir, request Topology.Manifold, confirm files
        // land on disk and mod.rs lists the generated module.
        let tmp = tempfile::tempdir().expect("tempdir");
        let cfg = OverlayConfig {
            output_dir: tmp.path().to_path_buf(),
            namespaces: vec!["Topology.Manifold".to_owned()],
            seed_topology_env: true,
            ..OverlayConfig::default()
        };

        let report = generate_namespace_overlay(&cfg).expect("overlay generation");
        assert_eq!(report.namespaces.len(), 1);
        assert_eq!(report.namespaces[0].namespace, "Topology.Manifold");
        assert_eq!(report.namespaces[0].module_name, "topology_manifold");
        assert!(report.namespaces[0].decl_count > 0);

        let mod_rs = tmp.path().join("mod.rs");
        let contents = fs::read_to_string(&mod_rs).expect("read mod.rs");
        assert!(contents.contains("pub(crate) mod topology_manifold;"));
        assert!(tmp.path().join("topology_manifold.rs").exists());
        assert!(tmp.path().join("topology_manifold.payload.bin").exists());
    }
}
