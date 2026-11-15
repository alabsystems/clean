// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI surface for `clean compile` (Experimental).
//!
//! Epic #3436 Phase 4, issue #3453. Exposes the unified `clean compile` verb
//! for the `clean-compiler` crate. Marked `Stability::Experimental` because
//! `clean-compiler` intentionally does not yet commit to a stable public API:
//! the full `file → elaborate → compile → emit` pipeline is out of scope for
//! the MVP (explicit non-goal in the issue body).
//!
//! ## Scope (MVP)
//!
//! The MVP accepts a `<file>` path and a `--decl <name>` selector, plus an
//! `--emit <format>` format chooser (`l5ir`, `l5cnf`, `c`, `rust`) and an
//! `--opt-level <N>` hint. The top-level `clean-cli` crate owns the actual
//! source-file bridge because it already depends on parser, elaborator,
//! kernel, and compiler crates. This crate-local `run` helper remains a
//! typed-argument guard for non-top-level callers. This lets us:
//!
//! - Publish the clap surface so downstream tooling can link against the
//!   argument types without a follow-up breaking change.
//! - Register the `FeatureDescriptor` so `clean features --stability
//!   experimental` surfaces the verb for discoverability.
//! - Exercise the drift-prevention tests (`feature_coverage`, `docs_drift`).
//!
//! Full file-to-executable runtime closure remains tracked under #3708.
//!
//! ## Design refs
//!
//! - `designs/2026-04-18-cli-orphan-inventory.md` §4.3 (CLI mapping)
//! - `designs/2026-04-18-unified-cli-feature-index.md` (descriptor registry)
//!
//! The module is gated behind the `cli` Cargo feature so non-CLI consumers of
//! `clean-compiler` keep a minimal dependency graph (no clap, no
//! `clean-features`).

use std::path::PathBuf;

use clap::{Args, ValueEnum};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

// -- Arguments ----------------------------------------------------------------

/// Arguments for `clean compile`.
///
/// MVP positional `file` + `--decl <name>` selector. `--emit` and
/// `--opt-level` are consumed by the top-level `clean-cli` bridge.
#[derive(Debug, Clone, Args)]
pub struct CompileArgs {
    /// Path to the `.lean` source file containing the declaration.
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,
    /// Name of the single declaration to compile.
    #[arg(long, value_name = "NAME")]
    pub decl: Option<String>,
    /// Output format — one of `l5ir`, `l5cnf`, `c`, `rust`.
    #[arg(long, value_enum, default_value_t = EmitFormat::L5ir)]
    pub emit: EmitFormat,
    /// Optimization level: `0` disables optimization, `1` is the default
    /// pipeline, `2` and above are most aggressive.
    ///
    /// This is NOT advisory. `pipeline_config_from_opt_level` schedules passes
    /// per level — 0 turns off optimization, reference counting and boxing
    /// elision — and `clean run` forwards through the same path. The doc said
    /// "advisory; the MVP does not implement per-level pass scheduling" until
    /// 2026-08-31, which is anti-disclosure: it stops a reader trying a flag
    /// that works.
    #[arg(long, default_value_t = 0, value_name = "N")]
    pub opt_level: u8,
    /// Write output to this path instead of stdout. Required for `--emit obj`
    /// (a binary object cannot go to stdout); optional for the text formats.
    #[arg(long, short = 'o', value_name = "PATH")]
    pub output: Option<PathBuf>,
    /// A trust-ir module this compile LINKS AGAINST instead of re-embedding
    /// (repeatable; `--emit trustir-bin` only, trust-ir-backend feature).
    ///
    /// Each path must hold plain module bytes as `--emit trustir-bin` writes
    /// them; a `.tmbc` container is refused, because the import digest is
    /// taken over the module. A dependency whose link symbol exactly one
    /// supplied artifact defines (a body and externally visible linkage) is
    /// not compiled: the client declares it at the artifact's signature (with
    /// the backend functions generated from it, such as its boxed entry) and
    /// records one `Module.imports` row per artifact it uses, with the digest
    /// measured over the decoded module. A dependency two artifacts define is
    /// refused, and so is a compile root an artifact already defines. So is a
    /// call whose lowered shape differs from the artifact's signature; it is
    /// never re-boxed. A proof row is inherited only when the
    /// artifact's certificate was minted against the same source definition
    /// this compile elaborates, and the output is refused unless
    /// `validate_linked_module` accepts it against the supplied artifacts.
    /// Without this flag the whole dependency closure is compiled into one
    /// module.
    #[arg(long = "link-artifact", value_name = "PATH")]
    pub link_artifact: Vec<PathBuf>,
}

/// Emission format chooser for `clean compile --emit`.
///
/// Kept as an explicit enum (rather than a `String`) so clap surfaces the
/// allowed values in `--help` and rejects typos at parse time. The `Rust`
/// variant follows clap's `ValueEnum` lowercase rename, so users type
/// `--emit rust`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
#[clap(rename_all = "lower")]
pub enum EmitFormat {
    /// Emit L5IR (the IR after monomorphization and optimization).
    L5ir,
    /// Emit L5CNF (the early LCNF form before IR lowering).
    L5cnf,
    /// Emit C source via `emit_c`.
    C,
    /// Emit Rust source via `emit_rust`.
    Rust,
    /// Emit a textual `trust_ir` module via the experimental trust-ir backend
    /// (lowered in `ExternCalls` mode, i.e. ready for `trust-cg`). Only present
    /// when compiled with the `trust-ir-backend` feature.
    #[cfg(feature = "trust-ir-backend")]
    Trustir,
    /// Emit a BINARY `trust_ir` module — plain `trust_ir::binary::serialize_module`
    /// bytes, NOT the `.tmbc` container.
    ///
    /// This is the linkable artifact: a `.tmbc` carries `b"tMBC"` + a
    /// little-endian `u32` ahead of the module, which
    /// `trust_ir::binary::deserialize_module` refuses, and a digest taken over
    /// a container is not a digest of the module. `Module::stable_digest` is
    /// computed over the MODULE, so the file a consumer reads and the bytes the
    /// identity is taken over have to be the same thing. `--emit obj` keeps the
    /// container, because that is what the `trust-cg` CLI consumes.
    ///
    /// Requires `-o <path>`. trust-ir-backend feature.
    #[cfg(feature = "trust-ir-backend")]
    #[clap(name = "trustir-bin")]
    TrustirBin,
    /// Compile to a native object file (`.o`) by lowering to trust-ir and
    /// invoking the `trust-cg` backend. Requires `-o <path>` and a `trust-cg`
    /// binary (via `CLEAN_TRUST_CG_BIN` or `PATH`). trust-ir-backend feature.
    #[cfg(feature = "trust-ir-backend")]
    Obj,
}

// -- Errors -------------------------------------------------------------------

/// Errors surfaced by `clean compile` dispatch.
///
/// The MVP surface intentionally exposes only the wiring-level failures
/// (missing action, not-yet-implemented). Once the full pipeline is wired
/// up, this enum will grow variants wrapping [`crate::error::CompilerError`]
/// and file/name resolution failures.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CompilerCliError {
    /// Caller did not supply `<FILE>` or `--decl <NAME>`.
    #[error(
        "`clean compile` requires a source file and `--decl <NAME>` \
         selector; see `clean help compile`"
    )]
    MissingInput,
    /// The end-to-end pipeline is not yet wired up. Tracked under Epic
    /// #3436 Phase 4 follow-ups (#3453 landed the CLI surface only).
    #[error(
        "`clean compile` MVP: the end-to-end file → elaborate → compile → \
         emit pipeline is not yet wired up (see #3453 follow-ups under \
         Epic #3436 Phase 4)"
    )]
    NotYetImplemented,
}

// -- Public entry points ------------------------------------------------------

/// NOT the dispatch entry point for `clean compile`, despite what this comment
/// said until 2026-08-27. `cmd_compile::handle_compile_command` does not call
/// this function and never reaches it: it runs the real pipeline
/// (`select_lcnf_decl` -> `emit_decls`), which parses, elaborates and lowers
/// the declaration and its compilable dependency closure. `clean compile
/// <file> --decl <d> --emit c` emits C today.
///
/// This is a `pub` stub with NO production caller — only the three unit tests
/// below, which pin its `MissingInput` / `NotYetImplemented` returns. Those
/// tests are green and describe nothing a user can reach, which is how the
/// stale claim survived: the verb's `--help` text was derived from this
/// function's behaviour rather than the handler's.
///
/// Left in place rather than deleted because it is public API of this crate;
/// removing it is a separate change. Do not wire it into a dispatch path
/// without replacing the body.
pub fn run(args: CompileArgs) -> Result<(), CompilerCliError> {
    let Some(file) = args.file.as_ref() else {
        return Err(CompilerCliError::MissingInput);
    };
    let Some(decl) = args.decl.as_deref() else {
        return Err(CompilerCliError::MissingInput);
    };
    tracing::info!(
        file = %file.display(),
        decl = decl,
        emit = ?args.emit,
        opt_level = args.opt_level,
        "clean compile — MVP surface only; pipeline not yet wired"
    );
    Err(CompilerCliError::NotYetImplemented)
}

// -- Feature descriptor registry ---------------------------------------------

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const ORPHAN_INVENTORY_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "CLI orphan inventory — clean-compiler",
    target: "designs/2026-04-18-cli-orphan-inventory.md",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const ISSUE_3453: Reference = Reference {
    kind: RefKind::Issue,
    label: "Add clean compile (clean-compiler MVP, Experimental)",
    target: "#3453",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-compiler",
    target: "clean-compiler",
};

/// Feature descriptors surfaced by the `clean-compiler` crate.
///
/// Registered into the top-level CLI by
/// `clean-cli/src/registry.rs::all_features()`. Single descriptor at path
/// `["compile"]` with `Stability::Experimental` marker — the MVP surface is
/// intentionally limited (see module doc).
pub const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["compile"],
    domain_root: Some("compile"),
    alternative_forms: &[],
    feature_gate: None,
    summary: "Compile a Lean declaration through the clean-compiler pipeline (Experimental)",
    description: "\
Compile a single declaration from a `.lean` file through the clean-compiler \
pipeline. The MVP accepts a `<FILE>` positional and a `--decl <NAME>` \
selector plus `--emit <FORMAT>` (one of `l5ir`, `l5cnf`, `c`, `rust`) and \
an `--opt-level <N>` hint.\n\n\
Marked `Stability::Experimental` because THIS command stops at IR or source text \
(the `trust-ir-backend` cargo feature adds `--emit obj`, a native object via \
trust-cg): \
it does not itself link or run, and it is not a full Lean4 compiler/runtime \
replacement. The top-level `clean-cli` bridge owns parsing and elaboration, \
then lowers the selected declaration through the public `clean-compiler` \
L5CNF/IR emitters. Note `--emit l5ir`/`--emit l5cnf` print a structural dump \
of the IR, not compilable source; `--emit c`/`--emit rust` print source.\n\n\
Linking and running are NOT missing from the CLI — they live in `clean run`, \
which takes the same emit-C closure through `cc` to a native binary and \
executes it, honoring Lean's `def main : IO UInt32` entry contract (verified \
2026-08-26). #3708 tracks giving `clean compile` its own link step; read it as \
a gap in this verb, not in the toolchain.",
    category: Category::Build,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean compile foo.lean --decl foo",
            what: "compile declaration `foo` from `foo.lean` to default L5IR output",
        },
        Example {
            cmd: "clean compile foo.lean --decl foo --emit c --opt-level 2",
            what: "emit C source for declaration `foo` with aggressive optimization",
        },
        Example {
            cmd: "clean compile foo.lean --decl foo --emit rust",
            what: "emit Rust source for declaration `foo`",
        },
    ],
    see_also: &["run", "check", "eval"],
    references: &[
        DESIGN_REF,
        ORPHAN_INVENTORY_REF,
        ISSUE_3436,
        ISSUE_3453,
        CRATE_REF,
    ],
}];

/// Compile-time assertion that [`FEATURES`] is non-empty. Guards against
/// accidentally shipping an empty descriptor array, which would silently
/// disappear from `clean features` without any drift-test failure.
const _: () = {
    assert!(
        !FEATURES.is_empty(),
        "clean-compiler cli must expose at least one FeatureDescriptor"
    );
    let _: &[FeatureDescriptor] = FEATURES;
};

#[cfg(test)]
mod tests {
    use super::*;
    use clap::Parser;
    use clean_features::{ensure_has_example, ensure_unique_paths};

    /// Minimal parser harness that embeds [`CompileArgs`] under the
    /// top-level `compile` verb, mirroring the dispatch pattern in
    /// `clean-cli/src/cli_args.rs`. Avoids depending on the real
    /// `clean-cli` parser from a lib-internal unit test.
    #[derive(Parser, Debug)]
    #[command(name = "clean")]
    struct Harness {
        #[command(subcommand)]
        command: HarnessCommands,
    }

    #[derive(clap::Subcommand, Debug)]
    enum HarnessCommands {
        Compile(CompileArgs),
    }

    #[test]
    fn features_are_lint_clean() {
        let descriptors: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
        ensure_unique_paths(&descriptors).expect("compiler descriptor paths are unique");
        for descriptor in FEATURES {
            ensure_has_example(descriptor).expect("every compiler descriptor has ≥1 example");
        }
    }

    #[test]
    fn compile_has_experimental_stability() {
        assert_eq!(FEATURES.len(), 1);
        assert_eq!(FEATURES[0].path, &["compile"]);
        assert_eq!(FEATURES[0].stability, Stability::Experimental);
        assert_eq!(FEATURES[0].category, Category::Build);
        assert_eq!(FEATURES[0].domain_root, Some("compile"));
    }

    #[test]
    fn parses_positional_file_and_decl() {
        let argv = ["clean", "compile", "foo.lean", "--decl", "foo"];
        let parsed = Harness::try_parse_from(argv).expect("must parse positional+decl");
        let HarnessCommands::Compile(args) = parsed.command;
        assert_eq!(args.file.as_deref(), Some(std::path::Path::new("foo.lean")));
        assert_eq!(args.decl.as_deref(), Some("foo"));
        assert_eq!(args.emit, EmitFormat::L5ir);
        assert_eq!(args.opt_level, 0);
    }

    #[test]
    fn parses_emit_c_with_opt_level() {
        let argv = [
            "clean",
            "compile",
            "foo.lean",
            "--decl",
            "foo",
            "--emit",
            "c",
            "--opt-level",
            "2",
        ];
        let parsed = Harness::try_parse_from(argv).expect("must parse emit+opt-level");
        let HarnessCommands::Compile(args) = parsed.command;
        assert_eq!(args.emit, EmitFormat::C);
        assert_eq!(args.opt_level, 2);
    }

    #[test]
    fn parses_emit_rust() {
        let argv = [
            "clean", "compile", "foo.lean", "--decl", "foo", "--emit", "rust",
        ];
        let parsed = Harness::try_parse_from(argv).expect("must parse emit=rust");
        let HarnessCommands::Compile(args) = parsed.command;
        assert_eq!(args.emit, EmitFormat::Rust);
    }

    #[cfg(feature = "trust-ir-backend")]
    #[test]
    fn parses_emit_trustir() {
        let argv = [
            "clean", "compile", "foo.lean", "--decl", "foo", "--emit", "trustir",
        ];
        let parsed = Harness::try_parse_from(argv).expect("must parse emit=trustir");
        let HarnessCommands::Compile(args) = parsed.command;
        assert_eq!(args.emit, EmitFormat::Trustir);
    }

    #[test]
    fn rejects_unknown_emit_format() {
        let argv = [
            "clean", "compile", "foo.lean", "--decl", "foo", "--emit", "bogus",
        ];
        let res = Harness::try_parse_from(argv);
        assert!(res.is_err(), "clap must reject --emit bogus");
    }

    #[test]
    fn run_returns_missing_input_without_file() {
        let args = CompileArgs {
            file: None,
            decl: Some("foo".to_owned()),
            emit: EmitFormat::L5ir,
            opt_level: 0,
            output: None,
            link_artifact: Vec::new(),
        };
        let err = run(args).expect_err("missing file must error");
        assert!(matches!(err, CompilerCliError::MissingInput));
    }

    #[test]
    fn run_returns_missing_input_without_decl() {
        let args = CompileArgs {
            file: Some(PathBuf::from("foo.lean")),
            decl: None,
            emit: EmitFormat::L5ir,
            opt_level: 0,
            output: None,
            link_artifact: Vec::new(),
        };
        let err = run(args).expect_err("missing decl must error");
        assert!(matches!(err, CompilerCliError::MissingInput));
    }

    #[test]
    fn run_returns_not_yet_implemented_with_all_args() {
        let args = CompileArgs {
            file: Some(PathBuf::from("foo.lean")),
            decl: Some("foo".to_owned()),
            emit: EmitFormat::L5ir,
            opt_level: 0,
            output: None,
            link_artifact: Vec::new(),
        };
        let err = run(args).expect_err("MVP must surface NotYetImplemented");
        assert!(matches!(err, CompilerCliError::NotYetImplemented));
    }
}
