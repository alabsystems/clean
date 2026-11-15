// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `getopt_long` reading, against what pinned Lean was measured to do.

use super::*;

fn words(line: &str) -> Vec<String> {
    line.split_whitespace().map(str::to_owned).collect()
}

fn opts(line: &CommandLine) -> Vec<Opt> {
    line.options.iter().map(|parsed| parsed.opt).collect()
}

#[test]
fn test_parse_permutes_operands_and_options() {
    let line = parse(LeanDialect::V4_8_0, &words("a.lean --json -q")).expect("parses");
    assert_eq!(line.operands, vec!["a.lean"]);
    assert_eq!(opts(&line), vec![Opt::Json, Opt::Quiet]);
}

#[test]
fn test_parse_define_attached_and_separate() {
    let line = parse(
        LeanDialect::V4_8_0,
        &words("-DautoImplicit=false -D pp.all=true f.lean"),
    )
    .expect("parses");
    let values: Vec<_> = line
        .options
        .iter()
        .map(|parsed| parsed.value.clone())
        .collect();
    assert_eq!(
        values,
        vec![
            Some("autoImplicit=false".to_owned()),
            Some("pp.all=true".to_owned())
        ]
    );
}

#[test]
fn test_parse_unique_prefix_and_ambiguity() {
    let line = parse(LeanDialect::V4_8_0, &words("--vers")).expect("unique prefix");
    assert_eq!(opts(&line), vec![Opt::Version]);
    let err = parse(LeanDialect::V4_8_0, &words("--s f.lean")).expect_err("ambiguous");
    assert_eq!(
        err.getopt_line.as_deref(),
        Some("lean: option `--s' is ambiguous")
    );
}

#[test]
fn test_parse_modern_flags_are_unknown_to_4_8_0() {
    let err = parse(LeanDialect::V4_8_0, &words("--short-version")).expect_err("4.8.0");
    assert_eq!(
        err.getopt_line.as_deref(),
        Some("lean: unrecognized option `--short-version'")
    );
    let err = parse(LeanDialect::V4_8_0, &words("-V")).expect_err("4.8.0");
    assert_eq!(
        err.getopt_line.as_deref(),
        Some("lean: invalid option -- V")
    );
    let line = parse(LeanDialect::V4_30_0Rc2, &words("-V")).expect("4.30.0-rc2");
    assert_eq!(opts(&line), vec![Opt::ShortVersion]);
}

#[test]
fn test_parse_missing_argument_messages() {
    let err = parse(LeanDialect::V4_8_0, &words("f.lean -D")).expect_err("no argument");
    assert_eq!(
        err.getopt_line.as_deref(),
        Some("lean: option requires an argument -- D")
    );
    let err = parse(LeanDialect::V4_8_0, &words("--root")).expect_err("no argument");
    assert_eq!(
        err.getopt_line.as_deref(),
        Some("lean: option `--root' requires an argument")
    );
}

#[test]
fn test_parse_run_differs_per_release() {
    // Lean 4.8.0: `--run` is a flag and options are still read after the file.
    let line = parse(LeanDialect::V4_8_0, &words("--run r.lean a --json b")).expect("parses");
    assert_eq!(opts(&line), vec![Opt::RunFlag, Opt::Json]);
    assert_eq!(line.operands, vec!["r.lean", "a", "b"]);
    // Lean 4.30.0-rc2: `--run <file>` hands everything after it to the program.
    let line = parse(
        LeanDialect::V4_30_0Rc2,
        &words("--run r.lean a -x --json b"),
    )
    .expect("parses");
    assert_eq!(
        line.run_file,
        Some((
            "r.lean".to_owned(),
            vec!["a".into(), "-x".into(), "--json".into(), "b".into()]
        ))
    );
}

#[test]
fn test_parse_short_cluster_and_unknown_short() {
    let line = parse(LeanDialect::V4_8_0, &words("-qv")).expect("cluster");
    assert_eq!(opts(&line), vec![Opt::Quiet, Opt::Version]);
    let err = parse(LeanDialect::V4_8_0, &words("-Z")).expect_err("unknown");
    assert_eq!(
        err.getopt_line.as_deref(),
        Some("lean: invalid option -- Z")
    );
    let err = parse(LeanDialect::V4_8_0, &words("-1")).expect_err("in optstring, unhandled");
    assert_eq!(err.getopt_line, None);
}

#[test]
fn test_parse_refused_options_are_named() {
    let line = parse(
        LeanDialect::V4_30_0Rc2,
        &words("-o x.olean --server f.lean"),
    )
    .expect("parses");
    assert_eq!(
        opts(&line),
        vec![Opt::Refused(Refusal::Olean), Opt::Refused(Refusal::Server)]
    );
    assert_eq!(line.options[0].spelling, "-o");
    assert_eq!(line.options[0].value.as_deref(), Some("x.olean"));
    assert_eq!(line.operands, vec!["f.lean"]);
}

#[test]
fn test_parse_double_dash_ends_options() {
    let line = parse(LeanDialect::V4_8_0, &words("--json -- -q.lean")).expect("parses");
    assert_eq!(opts(&line), vec![Opt::Json]);
    assert_eq!(line.operands, vec!["-q.lean"]);
}
