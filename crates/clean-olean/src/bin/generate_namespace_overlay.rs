// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Deprecated standalone entry point for namespace overlay payload generation.
//!
//! Use `clean olean generate-overlay ...` instead. This binary is retained as
//! a thin compat shim: it forwards its `env::args()` into
//! [`clean_olean::cli::generate_namespace_overlay`] so existing scripts keep
//! working verbatim.
//!
//! Absorbed by `clean olean generate-overlay` under Epic #3436 (#3442). See
//! `designs/2026-04-18-unified-cli-feature-index.md` and
//! `designs/2026-04-18-cli-orphan-inventory.md`.

use std::path::PathBuf;
use std::process::ExitCode;

use clean_olean::cli::{generate_namespace_overlay, OverlayConfig, OverlayError};
use tracing::{error, info};

fn print_usage() {
    info!(
        "Usage: generate_namespace_overlay \\\n  --namespace <prefix> [--namespace <prefix> ...] \\\n  --output-dir <path> \\\n  [--module <module> ...] [--search-path <path> ...] [--seed-topology-env]\n\nDEPRECATED: prefer `clean olean generate-overlay ...` (#3442)."
    );
}

fn parse_args() -> Result<OverlayConfig, String> {
    let mut cfg = OverlayConfig::default();
    let mut args = std::env::args().skip(1);

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--output-dir" => {
                let path = args
                    .next()
                    .ok_or_else(|| "missing value after --output-dir".to_owned())?;
                cfg.output_dir = PathBuf::from(path);
            }
            "--namespace" => {
                let namespace = args
                    .next()
                    .ok_or_else(|| "missing value after --namespace".to_owned())?;
                cfg.namespaces.push(namespace);
            }
            "--module" => {
                let module = args
                    .next()
                    .ok_or_else(|| "missing value after --module".to_owned())?;
                cfg.modules.push(module);
            }
            "--search-path" => {
                let path = args
                    .next()
                    .ok_or_else(|| "missing value after --search-path".to_owned())?;
                cfg.search_paths.push(PathBuf::from(path));
            }
            "--seed-topology-env" => {
                cfg.seed_topology_env = true;
            }
            "-h" | "--help" => {
                print_usage();
                std::process::exit(0);
            }
            _ => {
                return Err(format!("unknown argument: {arg}"));
            }
        }
    }

    if cfg.modules.is_empty() && !cfg.seed_topology_env {
        return Err("provide --module entries and/or --seed-topology-env".to_owned());
    }

    Ok(cfg)
}

fn main() -> ExitCode {
    let _ = tracing_subscriber::fmt::try_init();

    let cfg = match parse_args() {
        Ok(cfg) => cfg,
        Err(err) => {
            error!(%err, "failed to parse CLI arguments");
            print_usage();
            return ExitCode::from(2);
        }
    };

    match generate_namespace_overlay(&cfg) {
        Ok(report) => {
            for summary in &report.namespaces {
                info!(
                    module = %summary.module_name,
                    namespace = %summary.namespace,
                    decls = summary.decl_count,
                    "generated namespace overlay payload"
                );
            }
            ExitCode::SUCCESS
        }
        Err(OverlayError::MissingOutputDir) => {
            error!("--output-dir is required");
            print_usage();
            ExitCode::from(2)
        }
        Err(OverlayError::NoNamespaces) => {
            error!("at least one --namespace is required");
            print_usage();
            ExitCode::from(2)
        }
        Err(err) => {
            error!(%err, "overlay generation failed");
            ExitCode::FAILURE
        }
    }
}
