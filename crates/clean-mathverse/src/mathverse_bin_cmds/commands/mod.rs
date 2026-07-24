// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Command implementations for the mathverse CLI.
//!
//! Each submodule handles one or two related CLI subcommands.

mod deps;
mod diff;
mod download;
mod export;
mod find;
mod find_tag;
mod graph;
mod graph_delimited;
mod inspect;
mod list;
mod release;
mod sample;
mod search;
mod serve;
mod stats;
mod upload;
mod verify;
mod version;

pub use deps::{cmd_deps, cmd_uses};
pub use diff::cmd_diff;
pub use download::cmd_download;
pub use export::cmd_export;
pub use find::cmd_find;
pub use graph::cmd_graph;
pub use inspect::cmd_inspect;
pub use list::cmd_list;
pub use release::cmd_release;
pub use sample::cmd_sample;
pub use search::cmd_search;
pub use serve::cmd_serve;
pub use stats::{cmd_stats, cmd_systems};
pub use upload::cmd_upload;
pub use verify::cmd_verify;
pub use version::cmd_version;

use std::path::PathBuf;

use crate::mathverse_bin_cmds::fmt::OutputFormat;

// -----------------------------------------------------------------------
// Shared helpers
// -----------------------------------------------------------------------

fn default_library_dir() -> PathBuf {
    if let Ok(home) = std::env::var("HOME") {
        PathBuf::from(home).join(".mathverse/library")
    } else {
        PathBuf::from("data/mathverse-library")
    }
}

fn truncate(s: &str, max_len: usize) -> &str {
    if s.len() <= max_len {
        s
    } else {
        &s[..max_len]
    }
}

fn parse_format_arg(args: &[String]) -> OutputFormat {
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--format" {
            if let Some(val) = args.get(i + 1) {
                return OutputFormat::parse(val).unwrap_or_else(|| {
                    eprintln!(
                        "Unknown format: {val}. Use 'table', 'text', 'json', 'csv', or 'tsv'."
                    );
                    std::process::exit(1);
                });
            }
        }
        i += 1;
    }
    OutputFormat::Table
}
