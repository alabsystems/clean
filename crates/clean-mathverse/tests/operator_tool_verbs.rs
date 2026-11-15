// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The two operator-tool descriptors must list the verbs their binaries dispatch.
//!
//! # Why
//!
//! `mathverse convert` and `mathverse shard` are descriptor-ONLY surfaces: the
//! binaries are not clap subcommands, so `--help` cannot be generated from the
//! argument parser and the sub-verb list is prose somebody typed. Prose drifts.
//!
//! Measured 2026-09-01, both were wrong, in the same direction:
//!
//! * `mathverse_convert` dispatches **16** verbs; the descriptor listed 9.
//!   Undeclared: `build`, `status`, `update`, `fetch`, `opentheory`,
//!   `isabelle-binary`, `isabelle-mathlib-bridge`.
//! * `mathverse_shard` dispatches **11**; the descriptor listed 7. Undeclared:
//!   `build-coq`, `coq-import`, `lint-levels`, and — worst — `stamp`, which
//!   applies a kernel-verified manifest to shards on disk **destructively and
//!   without re-verifying**. A destructive verb that no help text mentions is
//!   the failure mode this file exists to prevent.
//!
//! The binary's own `print_usage` is hand-typed too: it listed all 11 when this
//! file was written and had dropped `lint-levels` by 2026-09-10, so the two help
//! surfaces in this one crate disagreed twice. The second `mathverse_shard` test
//! below reads `print_usage` against the same dispatch arms.
//!
//! # What this checks, and what it cannot
//!
//! Both directions: no dispatched verb is missing from the descriptor, and no
//! verb the descriptor names is absent from the dispatch (a phantom verb sends
//! a reader to run something that errors out). It does NOT check that the
//! description of each verb is accurate — only that the roster matches.

use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crates/clean-mathverse has a workspace root two levels up")
        .to_path_buf()
}

/// Top-level dispatch arms: `        "verb" => …` at the match's own indent.
///
/// Deliberately anchored to eight spaces. Nested matches inside an arm body are
/// indented further, so this reads the dispatch table and nothing else — which
/// is why the two counts below are exact rather than a floor.
fn dispatch_verbs(src: &str) -> Vec<String> {
    src.lines()
        .filter_map(|l| {
            let rest = l.strip_prefix("        \"")?;
            let (verb, tail) = rest.split_once('"')?;
            (tail.trim_start().starts_with("=>")
                && !verb.is_empty()
                && verb
                    .chars()
                    .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-'))
            .then(|| verb.to_string())
        })
        .collect()
}

/// The verbs a descriptor's `Sub-verbs, all N:` sentence names, plus N.
fn declared_verbs(desc: &str) -> (usize, Vec<String>) {
    let at = desc
        .find("Sub-verbs, all ")
        .expect("descriptor says `Sub-verbs, all N:`");
    let tail = &desc[at + "Sub-verbs, all ".len()..];
    let (n, rest) = tail.split_once(':').expect("`Sub-verbs, all N:`");
    let count: usize = n.trim().parse().expect("N is a number");
    // The sentence ends at the first `.` after the list; backticked tokens
    // after it (`stamp` in the DESTRUCTIVE note, the `cargo run` line) are
    // commentary, not roster entries.
    let list = rest.split_once(". ").map_or(rest, |(head, _)| head);
    let verbs = list
        .split('`')
        .skip(1)
        .step_by(2)
        .map(str::to_string)
        .collect();
    (count, verbs)
}

fn check(bin: &str, path: &str, expected: usize) {
    let root = repo_root();
    let src = std::fs::read_to_string(root.join(path)).expect("bin source is readable");
    let dispatched = dispatch_verbs(&src);
    assert_eq!(
        dispatched.len(),
        expected,
        "{bin}: extracted {} dispatch arm(s) from {path}, expected {expected}. \
         Either the binary gained/lost a verb (update this number AND the \
         descriptor), or the extraction stopped matching the file's shape — in \
         which case this check is silently reading nothing and must be fixed \
         before it is trusted. Found: {dispatched:?}",
        dispatched.len()
    );

    let d = clean_mathverse::cli::OPERATOR_TOOLS_FEATURES
        .iter()
        .find(|d| d.path.last() == Some(&bin))
        .unwrap_or_else(|| panic!("no descriptor for `mathverse {bin}`"));
    let (declared_n, declared) = declared_verbs(d.description);

    let missing: Vec<&String> = dispatched
        .iter()
        .filter(|v| !declared.contains(v))
        .collect();
    assert!(
        missing.is_empty(),
        "`clean help mathverse {bin}` does not mention {} verb(s) the binary \
         dispatches: {missing:?}. A reader cannot run what the help does not \
         name, and a DESTRUCTIVE verb hidden this way is how `mathverse_shard \
         stamp` went undocumented.",
        missing.len()
    );
    let phantom: Vec<&String> = declared
        .iter()
        .filter(|v| !dispatched.contains(v))
        .collect();
    assert!(
        phantom.is_empty(),
        "`clean help mathverse {bin}` names {phantom:?}, which {path} does not \
         dispatch. Following that help gets the reader a usage error."
    );
    assert_eq!(
        declared_n,
        dispatched.len(),
        "`clean help mathverse {bin}` says `all {declared_n}` but the binary \
         dispatches {}.",
        dispatched.len()
    );
}

#[test]
fn convert_descriptor_lists_every_dispatched_verb() {
    check(
        "convert",
        "crates/clean-mathverse/src/bin/mathverse_convert.rs",
        16,
    );
}

#[test]
fn shard_descriptor_lists_every_dispatched_verb() {
    check(
        "shard",
        "crates/clean-mathverse/src/bin/mathverse_shard/main.rs",
        11,
    );
}

/// The extractor must find real arms and reject look-alikes, or the checks
/// above pass by reading an empty list.
#[test]
fn dispatch_extraction_is_neither_blind_nor_greedy() {
    let src = "\
match verb {
        \"real-verb\" => f(),
        \"other\" => {
            match inner {
                \"nested\" => g(),
            }
        }
        \"Upper\" => h(),
    \"wrong-indent\" => i(),
        \"not-an-arm\",
        _ => usage(),
}";
    assert_eq!(
        dispatch_verbs(src),
        vec!["real-verb".to_string(), "other".to_string()],
        "must take top-level arms only: not the 16-space nested arm, not a \
         non-kebab name, not a differently-indented line, not a bare literal"
    );
}

/// `print_usage` is the roster a HUMAN reads at the terminal; every dispatched
/// verb must appear in it as `  <verb> …` (the descriptor gate above reads a
/// different surface, which is how `lint-levels` stayed undiscoverable here).
#[test]
fn mathverse_shard_print_usage_names_every_dispatched_verb() {
    let path = "crates/clean-mathverse/src/bin/mathverse_shard/main.rs";
    let src = std::fs::read_to_string(repo_root().join(path)).expect("bin source is readable");
    let start = src
        .find("fn print_usage()")
        .expect("main.rs defines print_usage");
    let body = &src[start..];
    let body = &body[..body.find("\n}\n").expect("print_usage closes")];
    let missing: Vec<String> = dispatch_verbs(&src)
        .into_iter()
        .filter(|verb| {
            !body.contains(&format!("\"  {verb} ")) && !body.contains(&format!("\"  {verb}\""))
        })
        .collect();
    assert!(
        missing.is_empty(),
        "mathverse_shard print_usage omits dispatched verb(s) {missing:?} — a user \
         reading `mathverse_shard` with no arguments cannot discover them"
    );
}

#[test]
fn declared_verb_parser_reads_the_roster_not_the_commentary() {
    let (n, v) = declared_verbs(
        "blah. Sub-verbs, all 2: `a`, `b`. NOTE that `b` is DESTRUCTIVE. Invoke via `cargo run`.",
    );
    assert_eq!(n, 2);
    assert_eq!(v, vec!["a".to_string(), "b".to_string()]);
}
