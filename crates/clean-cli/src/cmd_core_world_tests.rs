// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::cli_args::{Cli, Commands};
use clap::Parser;
use clean_kernel::LeanWorld;

#[test]
fn cli_source_world_defaults_and_unknown_world_refusals_are_explicit() {
    let default = Cli::try_parse_from(["clean", "check", "f.lean"]).unwrap();
    let Commands::Check(args) = default.command else {
        panic!("check")
    };
    assert_eq!(args.lean_world, None);
    let selected = Cli::try_parse_from([
        "clean",
        "check",
        "--parse-only",
        "--lean-world",
        "v4.36.0-rc2",
        "f.lean",
    ])
    .unwrap();
    let Commands::Check(args) = selected.command else {
        panic!("check")
    };
    assert_eq!(args.lean_world, Some(LeanWorld::Lean436Rc2));
    for world in ["v4.31.0", "v4.36.0", "v4.99.0"] {
        let Err(refusal) = Cli::try_parse_from(["clean", "check", "--lean-world", world, "f.lean"])
        else {
            panic!("unknown world {world} must be refused")
        };
        assert!(refusal.to_string().contains(world));
    }
}

#[test]
fn parse_only_selected_world_preserves_default_refusals_and_recovers_nothing() {
    let source = "private variable (x : Nat)\npublic def checked : Nat := x\n";
    let seed = clean_parser::NotationSeed::new();
    let old = parse_only_counts(source, &seed);
    assert_eq!(old.hard_error, 1);
    let recent = parse_only_counts_in_world(source, &seed, LeanWorld::Lean436Rc2);
    assert_eq!(
        (
            recent.parse_ok,
            recent.rawdecl_recovered,
            recent.hard_error,
            recent.recovery_diagnostics
        ),
        (2, 0, 0, 0)
    );
}

#[test]
fn check_source_closure_inherits_the_explicit_entry_world() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::create_dir(dir.path().join("Src")).unwrap();
    std::fs::write(
        dir.path().join("lean-toolchain"),
        "leanprover/lean4:v4.99.0\n",
    )
    .unwrap();
    std::fs::write(
        dir.path().join("Src/lean-toolchain"),
        "leanprover/lean4:v4.35.0\n",
    )
    .unwrap();
    std::fs::write(
        dir.path().join("Src/Child.lean"),
        "private variable (x : Nat)\npublic def childValue : Nat := x\n",
    )
    .unwrap();
    std::fs::write(
        dir.path().join("Src/Other.lean"),
        "public def otherValue (n : Nat) : Nat := n\n",
    )
    .unwrap();
    let file = dir.path().join("Main.lean");
    std::fs::write(
        &file,
        "import Src.Child\nimport Src.Other\npublic def entryValue (n : Nat) : Nat := childValue (otherValue n)\n",
    )
    .unwrap();
    let check = |explicit| {
        collect_check_outcome_in_world(
            &file,
            false,
            false,
            clean_kernel::cli::PreludeMode::Builtin,
            false,
            false,
            clean_elab::ImportPolicy::FailClosed,
            clean_kernel::cli::DEFAULT_DECL_BUDGET,
            clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET,
            &[],
            explicit,
        )
    };
    // Implicitly the entry's v4.99.0 world is refused. That refuses its Lean
    // imports only (R111); the project's own sources are parsed in the
    // Oracle's language, never in Src's nested v4.35.0 or in v4.36.0-rc2, and
    // v4.30.0-rc2 rejects the `private variable` spelling, as pinned Lean
    // 4.30/4.35 do (the 2026-11-10 selected-source-world entry).
    let error = check(None).unwrap_err();
    assert!(
        error.to_string().contains("unexpected token 'variable'"),
        "{error:#}"
    );
    let (outcome, _) = check(Some(LeanWorld::Lean436Rc2)).unwrap();
    assert_eq!(outcome.lean_world, LeanWorld::Lean436Rc2);
    assert_eq!(
        outcome.environment_lean_world,
        Some(LeanWorld::Lean436Rc2.tag())
    );
    assert_eq!(outcome.success_count, 1, "{outcome:?}");
    assert_eq!(outcome.imported_decl_count, 2, "{outcome:?}");
    assert!(outcome.errors.is_empty(), "{outcome:?}");
    assert!(outcome.parser_diagnostics.is_empty(), "{outcome:?}");
    assert!(outcome.kernel_failures.is_empty(), "{outcome:?}");
    assert!(outcome.trust_failures.is_empty(), "{outcome:?}");
}
