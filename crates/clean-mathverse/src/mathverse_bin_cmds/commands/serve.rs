// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse serve` — turnkey wrapper that starts the `mathverse_serve`
//! distribution server over a located Core.
//!
//! Locates the Core, ensures the `baseline.mvix` novelty index exists, prints a
//! one-line corpus summary + the local URL, then execs the existing
//! `mathverse_serve` binary with the right environment. All server logic is
//! reused verbatim — this layer only does the discovery/bootstrap/summary the
//! env-only server lacks.

use std::path::PathBuf;

use crate::serve_launch::{
    self, core_summary, ensure_baseline_index, local_url, locate_serve_bin, resolve_core_dir,
    serve_bin_missing_hint, serve_command,
};

pub fn cmd_serve(args: &[String]) {
    let mut core: Option<PathBuf> = None;
    let mut port: u16 = 8080;
    let mut download_base: Option<String> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--core" => {
                i += 1;
                core = args.get(i).map(PathBuf::from);
            }
            "--port" => {
                i += 1;
                port = args
                    .get(i)
                    .and_then(|p| p.parse::<u16>().ok())
                    .unwrap_or_else(|| {
                        eprintln!("--port must be a valid TCP port (1-65535)");
                        std::process::exit(1);
                    });
            }
            "--download-base" => {
                i += 1;
                download_base = args.get(i).cloned();
            }
            "--help" | "-h" => {
                print_serve_usage();
                return;
            }
            other => {
                eprintln!("Unknown serve option: {other}");
                print_serve_usage();
                std::process::exit(1);
            }
        }
        i += 1;
    }

    // 1. Locate a servable Core.
    let core_dir = match resolve_core_dir(core.as_deref()) {
        Ok(dir) => dir,
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
    };

    // 2. Ensure the baseline novelty index (non-fatal on benign build failure —
    //    the server serves fine without it).
    match ensure_baseline_index(&core_dir) {
        Ok(true) => println!("Built baseline novelty index (baseline.mvix)."),
        Ok(false) => {}
        Err(e) => eprintln!("Warning: could not build baseline.mvix ({e}); serving without it."),
    }

    // 3. One-line corpus summary (cheap; manifest only).
    match core_summary(&core_dir) {
        Ok(s) => println!(
            "Core: {} — {} shard(s), {} declaration(s)",
            core_dir.display(),
            s.shard_count,
            s.total_constants
        ),
        Err(e) => eprintln!("Warning: could not read corpus summary: {e}"),
    }

    // 4. Locate the server binary and exec it.
    let Some(serve_bin) = locate_serve_bin() else {
        eprintln!("{}", serve_bin_missing_hint());
        std::process::exit(1);
    };
    println!("Serving on {} (Ctrl-C to stop)", local_url(port));
    println!("  GET /stats /search /shards /manifest /theorem/{{name}} /download/{{shard}}");
    if let Some(base) = &download_base {
        println!("  Shard downloads 302-redirect to {base}");
    }

    let mut cmd = serve_command(&serve_bin, &core_dir, port, download_base.as_deref());
    match cmd.status() {
        Ok(status) if status.success() => {}
        Ok(status) => {
            eprintln!("mathverse_serve exited with status {status}");
            std::process::exit(status.code().unwrap_or(1));
        }
        Err(e) => {
            eprintln!(
                "failed to start {} ({e}); set ${} or rebuild the server binary",
                serve_bin.display(),
                serve_launch::SERVE_BIN_ENV
            );
            std::process::exit(1);
        }
    }
}

fn print_serve_usage() {
    eprintln!("mathverse serve — start the Mathverse distribution server over a local Core");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --core <DIR>           Core directory (default: discovery path)");
    eprintln!("  --port <N>             TCP port to bind (default: 8080)");
    eprintln!("  --download-base <URL>  302-redirect shard downloads to this host");
}
