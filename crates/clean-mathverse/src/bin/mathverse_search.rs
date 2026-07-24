// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Deprecation compat shim** for the original `mathverse_search` binary.
//!
//! The functionality of `mathverse_search` was absorbed into the unified
//! `clean mathverse <verb>` CLI in Epic #3436 / issue #3440. This shim preserves
//! the `mathverse_search` entry point so downstream scripts keep working, but
//! forwards each invocation to `clean mathverse` with the verb translated from
//! the original positional command.
//!
//! Translation table (matches
//! [`clean_mathverse::cli`](../../src/cli/mod.rs) exactly):
//!
//! | Legacy                                  | Forwarded                                     |
//! |-----------------------------------------|-----------------------------------------------|
//! | `mathverse_search name <pattern>`           | `clean mathverse search <pattern> --mode name`    |
//! | `mathverse_search type <pattern>`           | `clean mathverse search <pattern> --mode type`    |
//! | `mathverse_search info <name>`              | `clean mathverse info <name>`                     |
//! | `mathverse_search stats`                    | `clean mathverse stats`                           |
//! | `mathverse_search systems`                  | `clean mathverse systems`                         |
//!
//! Flags (`--shard-dir`, `--limit`, `--json`) pass through unchanged because
//! the new `clean mathverse` clap tree accepts the same spellings. Any
//! unrecognized argument is forwarded verbatim and surfaced as a clap error
//! from the canonical binary.
//!
//! Design references: `designs/2026-04-18-cli-orphan-inventory.md`,
//! `designs/2026-04-18-unified-cli-feature-index.md`.

use std::process::{Command, ExitCode};

/// Name of the canonical binary this shim forwards to.
const CANONICAL_BINARY: &str = "clean";

/// Stderr banner printed on every invocation so users notice the deprecation.
const DEPRECATION_NOTICE: &str = "\
warning: `mathverse_search` is deprecated and will be removed in a future release.
         Use `clean mathverse <verb>` instead. Forwarding...";

fn main() -> ExitCode {
    eprintln!("{DEPRECATION_NOTICE}");

    let argv: Vec<String> = std::env::args().skip(1).collect();
    let forwarded = match translate(&argv) {
        Ok(v) => v,
        Err(msg) => {
            eprintln!("mathverse_search: {msg}");
            eprintln!("Run `clean mathverse --help` for the current surface.");
            return ExitCode::from(2);
        }
    };

    match Command::new(CANONICAL_BINARY).args(&forwarded).status() {
        Ok(status) => match status.code() {
            Some(code) if (0..=255).contains(&code) => ExitCode::from(code as u8),
            _ => ExitCode::FAILURE,
        },
        Err(e) => {
            eprintln!(
                "mathverse_search: failed to exec `{CANONICAL_BINARY}`: {e}\n\
                 Ensure `{CANONICAL_BINARY}` is on PATH (try `cargo install --path crates/clean`).",
            );
            ExitCode::FAILURE
        }
    }
}

/// Translate the legacy positional argv into a canonical `clean mathverse ...`
/// argv (excluding the leading `clean` program name).
///
/// Returns an error string for diagnostics when the first positional is
/// unknown. The shim intentionally does *not* validate flag values — the
/// real clap tree owns that.
fn translate(argv: &[String]) -> Result<Vec<String>, String> {
    // Bare `mathverse_search` (no args) → forward help request.
    let Some(verb) = argv.first() else {
        return Ok(vec!["mathverse".to_owned(), "--help".to_owned()]);
    };

    let mut out: Vec<String> = vec!["mathverse".to_owned()];

    match verb.as_str() {
        // `name <pattern> [flags]` → `search <pattern> --mode name [flags]`
        "name" => {
            let rest = &argv[1..];
            let (pattern, flags) = split_pattern(rest, "name")?;
            out.push("search".to_owned());
            out.push(pattern);
            out.push("--mode".to_owned());
            out.push("name".to_owned());
            out.extend(flags.iter().cloned());
        }
        // `type <pattern> [flags]` → `search <pattern> --mode type [flags]`
        "type" => {
            let rest = &argv[1..];
            let (pattern, flags) = split_pattern(rest, "type")?;
            out.push("search".to_owned());
            out.push(pattern);
            out.push("--mode".to_owned());
            out.push("type".to_owned());
            out.extend(flags.iter().cloned());
        }
        // `info <name> [flags]` → `info <name> [flags]`
        "info" => {
            let rest = &argv[1..];
            let (pattern, flags) = split_pattern(rest, "info")?;
            out.push("info".to_owned());
            out.push(pattern);
            out.extend(flags.iter().cloned());
        }
        // `stats [flags]` → `stats [flags]`
        "stats" => {
            out.push("stats".to_owned());
            out.extend(argv[1..].iter().cloned());
        }
        // `systems [flags]` → `systems [flags]`
        "systems" => {
            out.push("systems".to_owned());
            out.extend(argv[1..].iter().cloned());
        }
        // Pass-through for `-h` / `--help` / `--version`.
        "-h" | "--help" | "help" => {
            out.push("--help".to_owned());
        }
        "--version" | "-V" => {
            return Ok(vec!["--version".to_owned()]);
        }
        other => {
            return Err(format!(
                "unknown subcommand `{other}`. \
                 Valid legacy verbs: name, type, info, stats, systems."
            ));
        }
    }

    Ok(out)
}

/// Pull the first non-flag argument as the positional pattern, returning the
/// remaining flag tail unchanged. The real clap parser in the canonical
/// binary handles flag validation.
fn split_pattern(rest: &[String], verb: &str) -> Result<(String, Vec<String>), String> {
    let mut pattern: Option<String> = None;
    let mut flags: Vec<String> = Vec::with_capacity(rest.len());
    for arg in rest {
        if pattern.is_none() && !arg.starts_with('-') {
            pattern = Some(arg.clone());
        } else {
            flags.push(arg.clone());
        }
    }
    match pattern {
        Some(p) => Ok((p, flags)),
        None => Err(format!("`{verb}` requires a positional <pattern> argument")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(v: &[&str]) -> Vec<String> {
        v.iter().map(|x| (*x).to_owned()).collect()
    }

    #[test]
    fn test_translate_name_to_search_mode_name() {
        let got = translate(&s(&["name", "Nat.add"])).unwrap();
        assert_eq!(
            got,
            s(&["mathverse", "search", "Nat.add", "--mode", "name"])
        );
    }

    #[test]
    fn test_translate_name_preserves_flags() {
        let got = translate(&s(&["name", "Nat.add", "--limit", "5", "--json"])).unwrap();
        assert_eq!(
            got,
            s(&[
                "mathverse",
                "search",
                "Nat.add",
                "--mode",
                "name",
                "--limit",
                "5",
                "--json",
            ])
        );
    }

    #[test]
    fn test_translate_type_to_search_mode_type() {
        let got = translate(&s(&["type", "group"])).unwrap();
        assert_eq!(got, s(&["mathverse", "search", "group", "--mode", "type"]));
    }

    #[test]
    fn test_translate_info_passthrough() {
        let got = translate(&s(&["info", "Nat.add_comm", "--json"])).unwrap();
        assert_eq!(got, s(&["mathverse", "info", "Nat.add_comm", "--json"]));
    }

    #[test]
    fn test_translate_stats_passthrough() {
        let got = translate(&s(&["stats", "--shard-dir", "/tmp/x"])).unwrap();
        assert_eq!(got, s(&["mathverse", "stats", "--shard-dir", "/tmp/x"]));
    }

    #[test]
    fn test_translate_systems_passthrough() {
        let got = translate(&s(&["systems"])).unwrap();
        assert_eq!(got, s(&["mathverse", "systems"]));
    }

    #[test]
    fn test_translate_bare_forwards_help() {
        let got = translate(&s(&[])).unwrap();
        assert_eq!(got, s(&["mathverse", "--help"]));
    }

    #[test]
    fn test_translate_version_flag() {
        let got = translate(&s(&["--version"])).unwrap();
        assert_eq!(got, s(&["--version"]));
    }

    #[test]
    fn test_translate_unknown_verb_errors() {
        let err = translate(&s(&["bogus"])).unwrap_err();
        assert!(err.contains("unknown subcommand"));
    }

    #[test]
    fn test_translate_name_missing_pattern_errors() {
        let err = translate(&s(&["name"])).unwrap_err();
        assert!(err.contains("requires a positional"));
    }
}
