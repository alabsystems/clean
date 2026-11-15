// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for `clean olean` clap parsing, resolve_args validation, and
//! [`FEATURES`] descriptor shape.

use std::path::PathBuf;

use clap::Parser;
use clean_features::{ensure_has_example, ensure_unique_paths, FeatureDescriptor};

use super::runner::resolve_args;
use super::{run, OleanArgs, OleanCliError, OleanCommands, VerifyBatchArgs, FEATURES};

/// Tiny parser embedding [`OleanArgs`] so we can exercise clap integration.
#[derive(Debug, Parser)]
struct Harness {
    #[command(subcommand)]
    command: Top,
}

#[derive(Debug, clap::Subcommand)]
enum Top {
    Olean(OleanArgs),
}

#[test]
fn test_verify_batch_defaults_parse() {
    let h =
        Harness::try_parse_from(["clean", "olean", "verify-batch", "/tmp/oleans"]).expect("parse");
    match h.command {
        Top::Olean(args) => match args.command {
            OleanCommands::VerifyBatch(a) => {
                assert_eq!(a.olean_dir, PathBuf::from("/tmp/oleans"));
                assert!(a.init_paths.is_empty());
                assert!(!a.json);
                assert_eq!(a.parallel, 1);
                assert!(!a.isolated);
                assert!(!a.load_only);
                assert!(!a.full_validation);
            }
            other => panic!("expected VerifyBatch, got {other:?}"),
        },
    }
}

#[test]
fn test_verify_batch_full_flag_set_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "olean",
        "verify-batch",
        "/tmp/oleans",
        "--init-path",
        "/opt/lean/lib",
        "--init-path",
        "/usr/local/lib/lean",
        "--json",
        "--json-report",
        "report.json",
        "--limit",
        "10",
        "--isolated",
        "--load-only",
        "--parallel",
        "4",
        "--cache-file",
        "verify.cache",
        "--full-validation",
    ])
    .expect("parse");
    match h.command {
        Top::Olean(args) => match args.command {
            OleanCommands::VerifyBatch(a) => {
                assert_eq!(a.olean_dir, PathBuf::from("/tmp/oleans"));
                assert_eq!(a.init_paths.len(), 2);
                assert!(a.json);
                assert_eq!(a.json_report, Some(PathBuf::from("report.json")));
                assert_eq!(a.limit, Some(10));
                assert!(a.isolated);
                assert!(a.load_only);
                assert_eq!(a.parallel, 4);
                assert_eq!(a.cache_file, Some(PathBuf::from("verify.cache")));
                assert!(a.full_validation);
            }
            other => panic!("expected VerifyBatch, got {other:?}"),
        },
    }
}

#[test]
fn test_resolve_args_rejects_zero_parallel() {
    let args = VerifyBatchArgs {
        olean_dir: PathBuf::from("."),
        init_paths: Vec::new(),
        json: false,
        json_report: None,
        limit: None,
        isolated: false,
        load_only: false,
        parallel: 0,
        cache_file: None,
        full_validation: false,
        max_heartbeats: None,
        stream_elide_proof_values: super::StreamElidePolicy::None,
        cache_dir: None,
    };
    let err = resolve_args(args).expect_err("should reject --parallel 0");
    assert!(matches!(err, OleanCliError::InvalidParallel));
}

#[test]
fn test_resolve_args_rejects_non_directory() {
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    let args = VerifyBatchArgs {
        olean_dir: tmp.path().to_path_buf(),
        init_paths: Vec::new(),
        json: false,
        json_report: None,
        limit: None,
        isolated: false,
        load_only: false,
        parallel: 1,
        cache_file: None,
        full_validation: false,
        max_heartbeats: None,
        stream_elide_proof_values: super::StreamElidePolicy::None,
        cache_dir: None,
    };
    let err = resolve_args(args).expect_err("should reject file path");
    assert!(matches!(err, OleanCliError::NotADirectory(_)));
}

#[test]
fn test_features_paths_are_unique() {
    let descriptors: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
    ensure_unique_paths(&descriptors).expect("olean descriptor paths must be unique");
}

#[test]
fn test_every_feature_has_an_example() {
    for d in FEATURES {
        ensure_has_example(d).unwrap_or_else(|e| {
            panic!(
                "descriptor `{}` must have at least one example: {e}",
                d.path_display()
            )
        });
    }
}

#[test]
fn test_feature_path_under_olean_root() {
    for d in FEATURES {
        assert_eq!(
            d.path[0],
            "olean",
            "descriptor `{}` must live under `olean`",
            d.path_display()
        );
    }
}

#[test]
fn test_generate_overlay_parses_required_flags() {
    let h = Harness::try_parse_from([
        "clean",
        "olean",
        "generate-overlay",
        "--output-dir",
        "/tmp/overlay",
        "--namespace",
        "Topology.Manifold",
        "--seed-topology-env",
    ])
    .expect("parse");
    match h.command {
        Top::Olean(args) => match args.command {
            OleanCommands::GenerateOverlay(g) => {
                assert_eq!(g.output_dir, PathBuf::from("/tmp/overlay"));
                assert_eq!(g.namespaces, vec!["Topology.Manifold".to_owned()]);
                assert!(g.seed_topology_env);
                assert!(g.modules.is_empty());
            }
            other => panic!("expected GenerateOverlay, got {other:?}"),
        },
    }
}

#[test]
fn test_generate_overlay_requires_source() {
    // Parsing succeeds; the dispatcher enforces the module-or-seed requirement.
    let h = Harness::try_parse_from([
        "clean",
        "olean",
        "generate-overlay",
        "--output-dir",
        "out",
        "--namespace",
        "Foo",
    ])
    .expect("parse");
    match h.command {
        Top::Olean(args) => {
            let err = run(args).expect_err("missing module/seed must error");
            assert!(matches!(err, OleanCliError::NoOverlaySource));
        }
    }
}

/// `simp-set` must default to the Init lane and must carry a repeatable
/// `--require`, which is the fail-closed half: without it the verb only
/// reports, and a named-sample assertion is what turns a silently-dropped
/// `@[simp]` entry into a loud failure at the decoder rather than a
/// "simp made no progress" in a Mathlib row days later.
#[test]
fn test_simp_set_defaults_and_require_list_parse() {
    let h = Harness::try_parse_from(["clean", "olean", "simp-set"]).expect("parse");
    match h.command {
        Top::Olean(args) => match args.command {
            OleanCommands::SimpSet(a) => {
                assert!(a.modules.is_empty(), "no --module means the Init lane");
                assert!(a.search_paths.is_empty());
                assert!(a.require.is_empty());
                assert!(!a.list);
                assert!(!a.json);
            }
            other => panic!("expected SimpSet, got {other:?}"),
        },
    }

    let h = Harness::try_parse_from([
        "clean",
        "olean",
        "simp-set",
        "--module",
        "Init",
        "--require",
        "beq_iff_eq",
        "--require",
        "Nat.add_zero",
        "--list",
        "--json",
    ])
    .expect("parse");
    match h.command {
        Top::Olean(args) => match args.command {
            OleanCommands::SimpSet(a) => {
                assert_eq!(a.modules, vec!["Init".to_string()]);
                assert_eq!(
                    a.require,
                    vec!["beq_iff_eq".to_string(), "Nat.add_zero".to_string()]
                );
                assert!(a.list);
                assert!(a.json);
            }
            other => panic!("expected SimpSet, got {other:?}"),
        },
    }
}

/// `ir-census` takes its modules positionally (at least one), walks the
/// closure only on request, and carries the three print switches the
/// differential script drives.
#[test]
fn test_ir_census_flags_parse() {
    assert!(
        Harness::try_parse_from(["clean", "olean", "ir-census"]).is_err(),
        "at least one module is required"
    );
    let h = Harness::try_parse_from([
        "clean",
        "olean",
        "ir-census",
        "--closure",
        "Mathlib.Tactic.Common",
        "Mathlib.Algebra.Group.Defs",
        "--search-path",
        "/a",
        "--print-decl",
        "Nat.add._boxed",
        "--print-module",
        "Init.Prelude",
        "--print-attrs",
        "--jobs",
        "2",
    ])
    .expect("parse");
    match h.command {
        Top::Olean(args) => match args.command {
            OleanCommands::IrCensus(a) => {
                assert_eq!(
                    a.modules,
                    vec!["Mathlib.Tactic.Common", "Mathlib.Algebra.Group.Defs"]
                );
                assert!(a.closure);
                assert_eq!(a.search_paths, vec![PathBuf::from("/a")]);
                assert_eq!(a.print_decls, vec!["Nat.add._boxed"]);
                assert_eq!(a.print_modules, vec!["Init.Prelude"]);
                assert!(a.print_attrs);
                assert_eq!(a.jobs, 2);
            }
            other => panic!("expected IrCensus, got {other:?}"),
        },
    }
}

#[test]
fn test_ir_census_zero_jobs_is_refused() {
    let h = Harness::try_parse_from(["clean", "olean", "ir-census", "Init", "--jobs", "0"])
        .expect("parse");
    let Top::Olean(args) = h.command;
    let err = run(args).expect_err("--jobs 0 must be refused");
    assert!(matches!(err, OleanCliError::InvalidJobs), "{err:?}");
    assert_eq!(err.to_string(), "--jobs must be >= 1");
}

/// A module name with an empty component is refused as an `ir-census` error.
/// It used to reach `?` and convert into `OleanCliError::Import`, whose text
/// named `import-reverify-metric`'s lane, a verb the user never ran.
#[test]
fn test_ir_census_malformed_module_is_an_ir_census_error() {
    let h = Harness::try_parse_from(["clean", "olean", "ir-census", "Init..Core"]).expect("parse");
    let Top::Olean(args) = h.command;
    let err = run(args).expect_err("an empty name component must be refused");
    assert!(matches!(err, OleanCliError::IrCensus(_)), "{err:?}");
    assert!(err.to_string().starts_with("ir-census: "), "{err}");
}

// -- `replay --from-export` and the 0/1/2 split ------------------------------

const EXPORT_META: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"f72c35b3f637c8c6571d353742168ab66cc22c00","version":"4.29.1"}}}"#;

fn write_export(dir: &tempfile::TempDir, name: &str, meta: &str, lines: &[&str]) -> PathBuf {
    let path = dir.path().join(name);
    let mut text = String::from(meta);
    for line in lines {
        text.push('\n');
        text.push_str(line);
    }
    text.push('\n');
    std::fs::write(&path, text).expect("write the export");
    path
}

fn run_parsed(argv: &[&str]) -> Result<(), OleanCliError> {
    let h = Harness::try_parse_from(argv).expect("parse");
    let Top::Olean(args) = h.command;
    run(args)
}

#[test]
fn test_replay_from_export_parses_and_excludes_module_flags() {
    let h = Harness::try_parse_from(["clean", "olean", "replay", "--from-export", "x.ndjson"])
        .expect("--from-export alone parses");
    let Top::Olean(args) = h.command;
    let OleanCommands::Replay {
        from_export,
        modules,
        ..
    } = args.command
    else {
        panic!("expected Replay");
    };
    assert_eq!(from_export, Some(PathBuf::from("x.ndjson")));
    assert!(modules.is_empty());
    for clash in [
        vec![
            "clean",
            "olean",
            "replay",
            "--from-export",
            "x.ndjson",
            "Init",
        ],
        vec![
            "clean",
            "olean",
            "replay",
            "--from-export",
            "x.ndjson",
            "--fresh",
        ],
    ] {
        assert!(
            Harness::try_parse_from(&clash).is_err(),
            "{clash:?} must not parse"
        );
    }
    assert!(
        Harness::try_parse_from(["clean", "olean", "replay"]).is_err(),
        "a module or --from-export is required"
    );
}

#[test]
fn test_replay_from_export_exit_codes_are_zero_one_two() {
    let dir = tempfile::tempdir().expect("tempdir");
    let honest = [
        r#"{"in":1,"str":{"pre":0,"str":"a"}}"#,
        r#"{"il":1,"succ":0}"#,
        r#"{"ie":0,"sort":1}"#,
        r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
    ];
    let good = write_export(&dir, "good.ndjson", EXPORT_META, &honest);
    let good = good.to_str().expect("utf-8 path");
    run_parsed(&["clean", "olean", "replay", "--from-export", good]).expect("accepted: exit 0");

    let mut forged = honest.to_vec();
    forged.insert(1, r#"{"in":1,"str":{"pre":0,"str":"b"}}"#);
    let bad = write_export(&dir, "bad.ndjson", EXPORT_META, &forged);
    let err = run_parsed(&[
        "clean",
        "olean",
        "replay",
        "--from-export",
        bad.to_str().expect("utf-8"),
    ])
    .expect_err("a rebound name index is rejected");
    assert!(
        matches!(err, OleanCliError::ExportRejected { .. }),
        "{err:?}"
    );
    assert_eq!(err.exit_code(), 1);

    let format4 = EXPORT_META.replace("\"3.1.0\"}", "\"4.0.0\"}");
    let unsupported = write_export(&dir, "v4.ndjson", &format4, &honest);
    let err = run_parsed(&[
        "clean",
        "olean",
        "replay",
        "--json",
        "--from-export",
        unsupported.to_str().expect("utf-8"),
    ])
    .expect_err("format 4 is declined");
    assert!(
        matches!(err, OleanCliError::ExportDeclined { .. }),
        "{err:?}"
    );
    assert_eq!(err.exit_code(), 2);
}

/// The `.olean` form's budget split: a replay whose every refusal is the
/// heartbeat budget running out exits 2, and the same module under the
/// kernel's default budget exits 0 (the control).
#[test]
fn test_replay_budget_exhaustion_exits_two_in_the_olean_form() {
    let fixtures = crate::test_support::compiled_fixture_dir("replay_forged");
    let fixtures = fixtures.to_str().expect("utf-8 fixture path");
    let err = run_parsed(&[
        "clean",
        "olean",
        "replay",
        "--exact",
        "--search-path",
        fixtures,
        "--max-heartbeats",
        "1",
        "--json",
        "ReplayHonestInd",
    ])
    .expect_err("one heartbeat starves the checks");
    assert!(
        matches!(
            err,
            OleanCliError::ReplayRefused {
                undecided: true,
                ..
            }
        ),
        "{err:?}"
    );
    assert_eq!(err.exit_code(), 2);
    let budget = clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT.to_string();
    run_parsed(&[
        "clean",
        "olean",
        "replay",
        "--exact",
        "--search-path",
        fixtures,
        "--max-heartbeats",
        &budget,
        "--json",
        "ReplayHonestInd",
    ])
    .expect("the default budget admits the honest module");
}
