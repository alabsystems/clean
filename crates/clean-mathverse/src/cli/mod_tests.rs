// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clap parse tests for `clean mathverse <verb>`.
//!
//! Hosted in a sibling file (pulled into `cli/mod.rs` via `#[path]`) so the
//! owning `mod.rs` stays under the 500-line file-size cap. Same pattern as
//! `cli/browse_dispatch.rs` ↔ `cli/browse_dispatch_tests.rs`.
//!
//! Covers:
//!
//! * Phase-1 typed-arg verbs — `search`, `info`, `stats`, `systems`.
//! * Phase-3.5 typed-arg browse verbs — `list`, `sample`, `deps`, `version`.
//! * Phase-3.5 passthrough-absorbed verbs (issue #3512) — `find`, `graph`,
//!   `diff`, `verify`, `download`, `export`, `release`. For passthrough
//!   verbs each test asserts both that clap routes the tokens to the
//!   expected `MathverseCommands` variant and that every trailing token (flags
//!   AND positional values) lands in `PassthroughArgs::rest` verbatim —
//!   the byte-for-byte parity contract with the standalone `mathverse` binary.

use super::*;
use clap::Parser;

/// Tiny parser that embeds `MathverseArgs` so we can exercise arg parsing.
#[derive(Debug, Parser)]
struct Harness {
    #[command(subcommand)]
    command: Top,
}

#[derive(Debug, clap::Subcommand)]
enum Top {
    Mathverse(MathverseArgs),
}

fn extract_rest(cmd: MathverseCommands) -> Vec<String> {
    match cmd {
        MathverseCommands::Find(p)
        | MathverseCommands::Graph(p)
        | MathverseCommands::Diff(p)
        | MathverseCommands::Verify(p)
        | MathverseCommands::Download(p)
        | MathverseCommands::Export(p)
        | MathverseCommands::Release(p) => p.rest,
        _ => panic!("expected a passthrough variant"),
    }
}

// ---------------------------------------------------------------------------
// Phase-1: typed-arg parse tests (search/info/stats/systems).
// ---------------------------------------------------------------------------

#[test]
fn test_search_defaults_parse() {
    let h = Harness::try_parse_from(["clean", "mathverse", "search", "Nat.add"]).expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Search(s) => {
                assert_eq!(s.pattern.as_deref(), Some("Nat.add"));
                assert_eq!(s.mode, SearchMode::Name);
                assert!(s.like.is_none());
                assert_eq!(s.limit, 20);
                assert!(!s.json);
            }
            _ => panic!("expected Search"),
        },
    }
}

#[test]
fn test_search_type_mode_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "search",
        "group theory",
        "--mode",
        "type",
        "--limit",
        "5",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Search(s) => {
                assert_eq!(s.pattern.as_deref(), Some("group theory"));
                assert_eq!(s.mode, SearchMode::Type);
                assert_eq!(s.limit, 5);
            }
            _ => panic!("expected Search"),
        },
    }
}

#[test]
fn test_search_like_flag_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "search",
        "--mode",
        "type",
        "--like",
        "Nat.add_comm",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Search(s) => {
                // `--like` carries the reference declaration; no positional
                // pattern is required for a type-directed query.
                assert!(s.pattern.is_none());
                assert_eq!(s.like.as_deref(), Some("Nat.add_comm"));
                assert_eq!(s.mode, SearchMode::Type);
            }
            _ => panic!("expected Search"),
        },
    }
}

#[test]
fn test_search_structural_mode_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "search",
        "Nat.add_comm",
        "--mode",
        "structural",
        "--index",
        "/tmp/baseline.mvix",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Search(s) => {
                assert_eq!(s.pattern.as_deref(), Some("Nat.add_comm"));
                assert_eq!(s.mode, SearchMode::Structural);
                assert_eq!(
                    s.index.as_deref(),
                    Some(std::path::Path::new("/tmp/baseline.mvix"))
                );
            }
            _ => panic!("expected Search"),
        },
    }
}

#[test]
fn test_info_parse() {
    let h = Harness::try_parse_from(["clean", "mathverse", "info", "Nat.add_comm", "--json"])
        .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Info(i) => {
                assert_eq!(i.name, "Nat.add_comm");
                assert!(i.json);
            }
            _ => panic!("expected Info"),
        },
    }
}

#[test]
fn test_stats_parse() {
    let h = Harness::try_parse_from(["clean", "mathverse", "stats"]).expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Stats(_) => {}
            _ => panic!("expected Stats"),
        },
    }
}

#[test]
fn test_systems_parse() {
    let h = Harness::try_parse_from(["clean", "mathverse", "systems", "--json"]).expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Systems(s) => assert!(s.json),
            _ => panic!("expected Systems"),
        },
    }
}

// ---------------------------------------------------------------------------
// Phase-3.5 (browse): typed-arg parse tests for list/sample/deps/version.
// These assert that the clap derive parser populates the typed argument
// structs correctly — no more free-form PassthroughArgs.
// ---------------------------------------------------------------------------

#[test]
fn test_list_parse_with_system_filter() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "list",
        "--system",
        "lean4",
        "--limit",
        "3",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::List(l) => {
                assert_eq!(l.system.as_deref(), Some("lean4"));
                assert_eq!(l.limit, 3);
                assert_eq!(l.offset, 0);
                assert!(!l.json);
            }
            _ => panic!("expected List"),
        },
    }
}

#[test]
fn test_sample_parse_with_seed() {
    let h = Harness::try_parse_from(["clean", "mathverse", "sample", "--n", "10", "--seed", "42"])
        .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Sample(s) => {
                assert_eq!(s.n, 10);
                assert_eq!(s.seed, 42);
                assert!(s.system.is_none());
                assert!(s.trust.is_none());
            }
            _ => panic!("expected Sample"),
        },
    }
}

#[test]
fn test_deps_parse_with_depth() {
    let h = Harness::try_parse_from(["clean", "mathverse", "deps", "Nat.add_comm", "--depth", "3"])
        .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Deps(d) => {
                assert_eq!(d.name, "Nat.add_comm");
                assert_eq!(d.depth, 3);
                assert!(!d.transitive);
                assert_eq!(d.limit, 200);
            }
            _ => panic!("expected Deps"),
        },
    }
}

#[test]
fn test_deps_parse_with_transitive_flag() {
    let h = Harness::try_parse_from(["clean", "mathverse", "deps", "Nat.add_comm", "--transitive"])
        .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Deps(d) => {
                assert!(d.transitive);
                assert_eq!(d.depth, 1);
            }
            _ => panic!("expected Deps"),
        },
    }
}

#[test]
fn test_version_parse_without_args() {
    let h = Harness::try_parse_from(["clean", "mathverse", "version"]).expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Version(v) => assert!(!v.json),
            _ => panic!("expected Version"),
        },
    }
}

#[test]
fn test_version_parse_with_json_flag() {
    let h = Harness::try_parse_from(["clean", "mathverse", "version", "--json"]).expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Version(v) => assert!(v.json),
            _ => panic!("expected Version"),
        },
    }
}

#[test]
fn test_replay_corpus_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "replay-corpus",
        "--production",
        "--json",
        "--output",
        "reports/mathverse-replay-production-corpus.json",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::ReplayCorpus(r) => {
                assert_eq!(
                    r.output,
                    PathBuf::from("reports/mathverse-replay-production-corpus.json")
                );
                assert_eq!(r.root, PathBuf::from("."));
                assert!(r.production);
                assert!(r.json);
            }
            _ => panic!("expected ReplayCorpus"),
        },
    }
}

#[test]
fn test_validate_replay_report_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "validate-replay-report",
        "--report",
        "reports/mathverse-replay-replacement.json",
        "--corpus",
        "reports/mathverse-replay-production-corpus.json",
        "--json",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::ValidateReplayReport(v) => {
                assert_eq!(
                    v.report,
                    PathBuf::from("reports/mathverse-replay-replacement.json")
                );
                assert_eq!(
                    v.corpus,
                    PathBuf::from("reports/mathverse-replay-production-corpus.json")
                );
                assert!(v.json);
            }
            _ => panic!("expected ValidateReplayReport"),
        },
    }
}

#[test]
fn test_stamp_verified_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "stamp-verified",
        "Init/SimpLemmas.olean",
        "Init/Data/Bool.olean",
        "--out-dir",
        "target/stamped",
        "--manifest",
        "reports/kv-manifest.json",
        "--json",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::StampVerified(s) => {
                assert_eq!(
                    s.inputs,
                    vec![
                        PathBuf::from("Init/SimpLemmas.olean"),
                        PathBuf::from("Init/Data/Bool.olean"),
                    ]
                );
                assert_eq!(s.out_dir, PathBuf::from("target/stamped"));
                assert_eq!(s.manifest, Some(PathBuf::from("reports/kv-manifest.json")));
                assert!(s.json);
            }
            _ => panic!("expected StampVerified"),
        },
    }
}

#[test]
fn test_stamp_verified_closure_root_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "stamp-verified",
        "/lib/lean/Mathlib/Logic/Basic.olean",
        "--out-dir",
        "target/stamped",
        "--closure-root",
        "/lib/lean",
        "--json",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::StampVerified(s) => {
                assert_eq!(s.closure_root, Some(PathBuf::from("/lib/lean")));
                assert_eq!(
                    s.inputs,
                    vec![PathBuf::from("/lib/lean/Mathlib/Logic/Basic.olean")]
                );
            }
            _ => panic!("expected StampVerified"),
        },
    }
}

#[test]
fn test_stamp_verified_parallel_jobs_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "stamp-verified",
        "/lib/lean/Mathlib/Logic/Basic.olean",
        "--out-dir",
        "target/stamped",
        "--closure-root",
        "/lib/lean",
        "--parallel",
        "--jobs",
        "8",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::StampVerified(s) => {
                assert!(s.parallel, "--parallel must set the flag");
                assert_eq!(s.jobs, Some(8), "--jobs must carry the worker count");
                assert_eq!(s.closure_root, Some(PathBuf::from("/lib/lean")));
            }
            _ => panic!("expected StampVerified"),
        },
    }
}

#[test]
fn test_stamp_verified_parallel_defaults_off() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "stamp-verified",
        "Init/SimpLemmas.olean",
        "--out-dir",
        "target/stamped",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::StampVerified(s) => {
                assert!(!s.parallel, "--parallel must default OFF");
                assert_eq!(s.jobs, None, "--jobs must default to None (= cores)");
            }
            _ => panic!("expected StampVerified"),
        },
    }
}

#[test]
fn test_stamp_verified_closure_root_defaults_none() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "stamp-verified",
        "Init/SimpLemmas.olean",
        "--out-dir",
        "target/stamped",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::StampVerified(s) => {
                assert_eq!(s.closure_root, None, "closure-root defaults to None");
            }
            _ => panic!("expected StampVerified"),
        },
    }
}

#[test]
fn test_stamp_verified_closure_elide_defaults_opaque() {
    // WS3 bounded-memory: the elision policy defaults to the statically-sound
    // `opaque` subset whenever `--closure-elide` is omitted.
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "stamp-verified",
        "/lib/lean/Mathlib/Logic/Basic.olean",
        "--out-dir",
        "target/stamped",
        "--closure-root",
        "/lib/lean",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::StampVerified(s) => {
                assert_eq!(s.closure_elide, ClosureElide::Opaque);
                assert_eq!(
                    s.closure_elide.to_kernel(),
                    clean_kernel::env::ProofValueElision::OpaqueOnly
                );
            }
            _ => panic!("expected StampVerified"),
        },
    }
}

#[test]
fn test_stamp_verified_closure_elide_parse_opaque_and_theorem() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "stamp-verified",
        "/lib/lean/Mathlib/Logic/Basic.olean",
        "--out-dir",
        "target/stamped",
        "--closure-root",
        "/lib/lean",
        "--closure-elide",
        "opaque-and-theorem",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::StampVerified(s) => {
                assert_eq!(s.closure_elide, ClosureElide::OpaqueAndTheorem);
                assert_eq!(
                    s.closure_elide.to_kernel(),
                    clean_kernel::env::ProofValueElision::OpaqueAndTheorem
                );
            }
            _ => panic!("expected StampVerified"),
        },
    }
}

#[test]
fn test_stamp_verified_requires_input() {
    // `inputs` is `required = true`; clap must reject a bare invocation.
    let res = Harness::try_parse_from([
        "clean",
        "mathverse",
        "stamp-verified",
        "--out-dir",
        "target/stamped",
    ]);
    assert!(
        res.is_err(),
        "stamp-verified must require at least one input"
    );
}

// ---------------------------------------------------------------------------
// KV-guardrail verbs (ratchet check/update, elision-gate, fingerprint).
// ---------------------------------------------------------------------------

#[test]
fn test_ratchet_check_parse_defaults() {
    let h = Harness::try_parse_from(["clean", "mathverse", "ratchet", "check"]).expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Ratchet {
                command: RatchetCommands::Check(c),
            } => {
                assert_eq!(c.summary, PathBuf::from("data/last_stamp_summary.json"));
                assert_eq!(c.ratchet, PathBuf::from("data/mathlib_kv_ratchet.json"));
                assert!(!c.json);
            }
            _ => panic!("expected Ratchet::Check"),
        },
    }
}

#[test]
fn test_ratchet_check_parse_summary_json_flags() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "ratchet",
        "check",
        "--summary",
        "data/last_stamp_summary.json",
        "--json",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Ratchet {
                command: RatchetCommands::Check(c),
            } => {
                assert_eq!(c.summary, PathBuf::from("data/last_stamp_summary.json"));
                assert!(c.json);
            }
            _ => panic!("expected Ratchet::Check"),
        },
    }
}

#[test]
fn test_ratchet_update_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "ratchet",
        "update",
        "--ratchet",
        "data/mathlib_kv_ratchet.json",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Ratchet {
                command: RatchetCommands::Update(u),
            } => {
                assert_eq!(u.ratchet, PathBuf::from("data/mathlib_kv_ratchet.json"));
                assert_eq!(u.summary, PathBuf::from("data/last_stamp_summary.json"));
            }
            _ => panic!("expected Ratchet::Update"),
        },
    }
}

#[test]
fn test_elision_gate_parse_positional_order() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "elision-gate",
        "data/kv_elision_opaque.json",
        "data/kv_elision_oat.json",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::ElisionGate(e) => {
                assert_eq!(
                    e.opaque_manifest,
                    PathBuf::from("data/kv_elision_opaque.json")
                );
                assert_eq!(
                    e.opaque_and_theorem_manifest,
                    PathBuf::from("data/kv_elision_oat.json")
                );
                assert!(!e.json);
            }
            _ => panic!("expected ElisionGate"),
        },
    }
}

#[test]
fn test_elision_gate_requires_two_manifests() {
    let res = Harness::try_parse_from([
        "clean",
        "mathverse",
        "elision-gate",
        "data/kv_elision_opaque.json",
    ]);
    assert!(res.is_err(), "elision-gate must require both manifests");
}

#[test]
fn test_fingerprint_parse() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "fingerprint",
        "reports/kv-manifest.json",
        "--json",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::Fingerprint(f) => {
                assert_eq!(f.manifest, PathBuf::from("reports/kv-manifest.json"));
                assert!(f.json);
            }
            _ => panic!("expected Fingerprint"),
        },
    }
}

#[test]
fn test_fingerprint_requires_manifest() {
    let res = Harness::try_parse_from(["clean", "mathverse", "fingerprint"]);
    assert!(res.is_err(), "fingerprint must require a manifest path");
}

// ---------------------------------------------------------------------------
// Phase-3.5 (passthrough, #3512): parse tests for the 7 re-absorbed verbs
// (find/graph/diff/verify/download/export/release). Each test asserts
// (1) the tokens parse through clap, (2) the parser routes to the expected
// variant, and (3) every trailing token lands in `PassthroughArgs::rest`
// verbatim — the byte-for-byte parity contract with the standalone `mathverse`
// binary.
// ---------------------------------------------------------------------------

#[test]
fn test_find_dispatches_with_trailing_flags() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "find",
        "Nat.add",
        "--semantic",
        "--limit",
        "5",
    ])
    .expect("parse");
    let Top::Mathverse(args) = h.command;
    assert!(matches!(args.command, MathverseCommands::Find(_)));
    assert_eq!(
        extract_rest(args.command),
        vec!["Nat.add", "--semantic", "--limit", "5"]
    );
}

#[test]
fn test_graph_dispatches_with_subcommand() {
    let h = Harness::try_parse_from(["clean", "mathverse", "graph", "search", "Nat.add"])
        .expect("parse");
    let Top::Mathverse(args) = h.command;
    assert!(matches!(args.command, MathverseCommands::Graph(_)));
    assert_eq!(extract_rest(args.command), vec!["search", "Nat.add"]);
}

#[test]
fn test_diff_dispatches_with_two_paths() {
    let h = Harness::try_parse_from(["clean", "mathverse", "diff", "a.mathverse", "b.mathverse"])
        .expect("parse");
    let Top::Mathverse(args) = h.command;
    assert!(matches!(args.command, MathverseCommands::Diff(_)));
    assert_eq!(
        extract_rest(args.command),
        vec!["a.mathverse", "b.mathverse"]
    );
}

#[test]
fn test_verify_dispatches_with_dir() {
    let h = Harness::try_parse_from(["clean", "mathverse", "verify", "data/mathverse-shards"])
        .expect("parse");
    let Top::Mathverse(args) = h.command;
    assert!(matches!(args.command, MathverseCommands::Verify(_)));
    assert_eq!(extract_rest(args.command), vec!["data/mathverse-shards"]);
}

#[test]
fn test_download_dispatches_with_force() {
    let h = Harness::try_parse_from(["clean", "mathverse", "download", "--force"]).expect("parse");
    let Top::Mathverse(args) = h.command;
    assert!(matches!(args.command, MathverseCommands::Download(_)));
    assert_eq!(extract_rest(args.command), vec!["--force"]);
}

#[test]
fn test_export_dispatches_with_subcommand() {
    let h =
        Harness::try_parse_from(["clean", "mathverse", "export", "clean-native"]).expect("parse");
    let Top::Mathverse(args) = h.command;
    assert!(matches!(args.command, MathverseCommands::Export(_)));
    assert_eq!(extract_rest(args.command), vec!["clean-native"]);
}

#[test]
fn test_release_dispatches_with_subcommand() {
    let h = Harness::try_parse_from(["clean", "mathverse", "release", "info"]).expect("parse");
    let Top::Mathverse(args) = h.command;
    assert!(matches!(args.command, MathverseCommands::Release(_)));
    assert_eq!(extract_rest(args.command), vec!["info"]);
}

#[test]
fn test_release_dispatches_with_trailing_flags() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "release",
        "verify",
        "--manifest",
        "release.json",
    ])
    .expect("parse");
    let Top::Mathverse(args) = h.command;
    assert!(matches!(args.command, MathverseCommands::Release(_)));
    assert_eq!(
        extract_rest(args.command),
        vec!["verify", "--manifest", "release.json"]
    );
}

#[test]
fn test_passthrough_variant_tolerates_empty_trailing_args() {
    // `clean mathverse download` with no trailing args maps to an empty
    // `PassthroughArgs::rest`; the underlying `cmd_download` then prints
    // usage and exits. The parse layer must not reject the empty case.
    let h = Harness::try_parse_from(["clean", "mathverse", "download"]).expect("parse");
    let Top::Mathverse(args) = h.command;
    assert!(matches!(args.command, MathverseCommands::Download(_)));
    assert!(extract_rest(args.command).is_empty());
}

// ---------------------------------------------------------------------------
// Graduation verb (mathverse-graduation-v2 intake gate).
// ---------------------------------------------------------------------------

#[test]
fn test_graduate_parse_with_candidates() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "graduate",
        "--project",
        "tests/fixtures/graduation/pilot/math-project.json",
        "--candidates",
        "GradPilot.imp_self,GradPilot.imp_trans",
        "--baseline",
        "data/mathverse-shards",
        "--out",
        "/tmp/graduated",
        "--json",
    ])
    .expect("parse");
    let Top::Mathverse(args) = h.command;
    match args.command {
        MathverseCommands::Graduate(g) => {
            assert_eq!(
                g.candidates,
                vec!["GradPilot.imp_self", "GradPilot.imp_trans"]
            );
            assert!(!g.all);
            assert!(g.json);
            assert_eq!(g.residual_risk, "unreviewed");
            assert_eq!(g.baseline_release, "local-shards");
        }
        _ => panic!("expected Graduate"),
    }
}

#[test]
fn test_graduate_parse_baseline_index_flag() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "graduate",
        "--project",
        "p.json",
        "--candidates",
        "GradPilot.imp_self",
        "--baseline-index",
        "/tmp/mathverse-v1.2.0.mvix",
        "--baseline-release",
        "mathverse-v1.2.0",
        "--out",
        "/tmp/g",
    ])
    .expect("parse");
    let Top::Mathverse(args) = h.command;
    match args.command {
        MathverseCommands::Graduate(g) => {
            assert_eq!(
                g.baseline_index.as_deref(),
                Some(std::path::Path::new("/tmp/mathverse-v1.2.0.mvix"))
            );
            assert_eq!(g.baseline_release, "mathverse-v1.2.0");
        }
        _ => panic!("expected Graduate"),
    }
}

#[test]
fn test_index_build_parse_defaults() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "index-build",
        "_mathverse-artifacts/mathverse-v1.2.0",
        "-o",
        "/tmp/mathverse-v1.2.0.mvix",
    ])
    .expect("parse");
    let Top::Mathverse(args) = h.command;
    match args.command {
        MathverseCommands::IndexBuild(a) => {
            assert_eq!(
                a.release_dir,
                PathBuf::from("_mathverse-artifacts/mathverse-v1.2.0")
            );
            assert_eq!(a.out, PathBuf::from("/tmp/mathverse-v1.2.0.mvix"));
            assert_eq!(a.check_sample, 0);
            assert!(!a.json);
        }
        _ => panic!("expected IndexBuild"),
    }
}

#[test]
fn test_index_build_parse_check_sample_json() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "index-build",
        "shards",
        "--out",
        "idx.mvix",
        "--check-sample",
        "2",
        "--json",
    ])
    .expect("parse");
    let Top::Mathverse(args) = h.command;
    match args.command {
        MathverseCommands::IndexBuild(a) => {
            assert_eq!(a.check_sample, 2);
            assert!(a.json);
        }
        _ => panic!("expected IndexBuild"),
    }
}

#[test]
fn test_index_build_parse_requires_out() {
    let res = Harness::try_parse_from(["clean", "mathverse", "index-build", "shards"]);
    assert!(res.is_err(), "index-build must require --out");
}

#[test]
fn test_index_tree_score_parse_defaults() {
    let h = Harness::try_parse_from(["clean", "mathverse", "index-tree-score", "/tmp/stamped"])
        .expect("parse");
    let Top::Mathverse(args) = h.command;
    match args.command {
        MathverseCommands::IndexTreeScore(a) => {
            assert_eq!(a.shard_dir, PathBuf::from("/tmp/stamped"));
            // `--out` is optional (unlike index-build); default fuel/max_hits apply.
            assert!(a.out.is_none());
            assert_eq!(a.fuel, crate::graduate::tree_score::TREE_SCORE_FUEL);
            assert_eq!(a.max_hits, 256);
            assert!(!a.json);
        }
        _ => panic!("expected IndexTreeScore"),
    }
}

#[test]
fn test_index_tree_score_parse_out_fuel_json() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "index-tree-score",
        "/tmp/stamped",
        "--out",
        "reports/ts.json",
        "--fuel",
        "1000",
        "--max-hits",
        "8",
        "--json",
    ])
    .expect("parse");
    let Top::Mathverse(args) = h.command;
    match args.command {
        MathverseCommands::IndexTreeScore(a) => {
            assert_eq!(a.out, Some(PathBuf::from("reports/ts.json")));
            assert_eq!(a.fuel, 1000);
            assert_eq!(a.max_hits, 8);
            assert!(a.json);
        }
        _ => panic!("expected IndexTreeScore"),
    }
}

#[test]
fn test_graduate_parse_requires_candidates_or_all() {
    let res = Harness::try_parse_from([
        "clean",
        "mathverse",
        "graduate",
        "--project",
        "p.json",
        "--out",
        "/tmp/g",
    ]);
    assert!(res.is_err(), "graduate must require --candidates or --all");
}

#[test]
fn test_graduate_parse_all_conflicts_with_candidates() {
    let res = Harness::try_parse_from([
        "clean",
        "mathverse",
        "graduate",
        "--project",
        "p.json",
        "--out",
        "/tmp/g",
        "--all",
        "--candidates",
        "X",
    ]);
    assert!(res.is_err(), "--all conflicts with --candidates");
}

// ---------------------------------------------------------------------------
// isabelle-sessions: AFP wave session-ROOT generator (afp_session_gen.py port).
// ---------------------------------------------------------------------------

#[test]
fn test_isabelle_sessions_parse_defaults_are_machine_portable() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "isabelle-sessions",
        "--out",
        "/tmp/zp_afp_wave_a",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::IsabelleSessions(s) => {
                assert_eq!(s.mode, IsabelleSessionsMode::Afp, "default mode is afp");
                assert!(s.entries.is_none());
                assert_eq!(s.parent, "ZP-Lib3e");
                assert_eq!(s.afp_thys, PathBuf::from("~/isabelle-work/afp/thys"));
                assert!(
                    s.hol_src.is_none(),
                    "spine source resolves from ISABELLE_HOME at dispatch"
                );
                assert_eq!(s.out, PathBuf::from("/tmp/zp_afp_wave_a"));
                assert_eq!(s.cap, 12, "default cap is the Lib3-lesson 12");
            }
            _ => panic!("expected IsabelleSessions"),
        },
    }
}

#[test]
fn test_isabelle_sessions_parse_all_flags() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "isabelle-sessions",
        "--mode",
        "wavec",
        "--entries",
        "scripts/isabelle/afp_wave_c_seed.txt",
        "--parent",
        "ZP-Lib2",
        "--afp-thys",
        "/data/afp/thys",
        "--hol-src",
        "/opt/isabelle/src/HOL",
        "--out",
        "/tmp/zp_wave_c",
        "--cap",
        "9",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::IsabelleSessions(s) => {
                assert_eq!(s.mode, IsabelleSessionsMode::Wavec);
                assert_eq!(
                    s.entries.as_deref(),
                    Some(std::path::Path::new("scripts/isabelle/afp_wave_c_seed.txt"))
                );
                assert_eq!(s.parent, "ZP-Lib2");
                assert_eq!(s.afp_thys, PathBuf::from("/data/afp/thys"));
                assert_eq!(
                    s.hol_src.as_deref(),
                    Some(std::path::Path::new("/opt/isabelle/src/HOL"))
                );
                assert_eq!(s.cap, 9);
            }
            _ => panic!("expected IsabelleSessions"),
        },
    }
}

#[test]
fn test_isabelle_sessions_requires_out() {
    let res = Harness::try_parse_from(["clean", "mathverse", "isabelle-sessions"]);
    assert!(res.is_err(), "isabelle-sessions must require --out");
}

#[test]
fn test_isabelle_capture_chain_accepts_portable_home_override() {
    let h = Harness::try_parse_from([
        "clean",
        "mathverse",
        "isabelle-capture-chain",
        "--spec",
        "scripts/isabelle/lib3_backfill_chain.spec.json",
        "--isabelle-home",
        "/opt/Isabelle",
        "--dry",
    ])
    .expect("parse");
    match h.command {
        Top::Mathverse(args) => match args.command {
            MathverseCommands::IsabelleCaptureChain(c) => {
                assert_eq!(
                    c.spec,
                    PathBuf::from("scripts/isabelle/lib3_backfill_chain.spec.json")
                );
                assert_eq!(c.isabelle_home, Some(PathBuf::from("/opt/Isabelle")));
                assert_eq!(c.work_dir, PathBuf::from("~/isabelle-work"));
                assert!(c.dry);
                assert!(!c.resume);
            }
            _ => panic!("expected IsabelleCaptureChain"),
        },
    }
}
