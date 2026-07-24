// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clean CLI library entrypoint.
//!
//! Exposes the CLI dispatcher as a library function so that both the
//! `clean-cli` binary and the canonical `clean` packaging binary can
//! share the same implementation without cross-package source paths.

mod authority_source_guard;
mod cli;
mod cli_args;
mod cmd_artifacts;
mod cmd_attempts;
mod cmd_audit;
mod cmd_auto;
mod cmd_axiom_audit_release_check;
mod cmd_bench;
mod cmd_cake;
mod cmd_cert;
mod cmd_commit;
mod cmd_compile;
mod cmd_core;
mod cmd_discover;
mod cmd_export_cert;
mod cmd_factory;
mod cmd_features;
mod cmd_fold;
mod cmd_help;
mod cmd_kernel;
mod cmd_lake;
mod cmd_lsp;
mod cmd_math;
mod cmd_mathverse;
mod cmd_native_library;
mod cmd_olean;
mod cmd_project;
mod cmd_promote;
mod cmd_prove;
mod cmd_release;
mod cmd_repl;
mod cmd_replacement;
mod cmd_research;
mod cmd_run;
mod cmd_rust_sem;
#[cfg(feature = "sat-verify")]
mod cmd_sat_verify;
mod cmd_solver;
mod cmd_sorry_census;
mod cmd_sorry_trace;
mod cmd_tla_sem;
mod cmd_tlaps;
mod cmd_vendor;
pub(crate) mod doc_render;
mod factory;
mod math_project;
mod native_build;
pub(crate) mod registry;
#[cfg(test)]
mod test_env;

use clap::Parser;
use clean_auto::cli::AutoCommands;
use clean_server::WebSocketConfig;
use cli_args::{Cli, Commands, VerifyCommands};

/// Pre-load .olean environment for --init or --stdlib server flags.
fn preload_olean_env(init: bool, stdlib: bool) -> Option<clean_kernel::Environment> {
    if !stdlib && !init {
        return None;
    }
    let module = if stdlib { "Std" } else { "Init" };
    tracing::info!("Pre-loading {module} library from .olean files...");
    let search_paths = clean_olean::default_search_paths();
    let cache = clean_olean::ModuleCache::new();
    let mut env = clean_kernel::Environment::new();
    match clean_olean::load_module_with_deps_cached(&mut env, module, &search_paths, &cache) {
        Ok(summaries) => {
            let total: usize = summaries.iter().map(|s| s.added_constants).sum();
            tracing::info!(
                "Loaded {module}: {} modules, {total} constants",
                summaries.len()
            );
            Some(env)
        }
        Err(e) => {
            tracing::warn!("Failed to pre-load {module}: {e}");
            tracing::warn!("Server will start with empty environment");
            None
        }
    }
}

/// Dispatch the server subcommand (async, isolated so `run` stays small).
async fn dispatch_server(
    port: u16,
    no_gpu: bool,
    websocket: bool,
    init: bool,
    stdlib: bool,
    theorem_index: Option<std::path::PathBuf>,
) -> anyhow::Result<()> {
    let addr = format!("127.0.0.1:{port}").parse()?;
    let initial_env = preload_olean_env(init, stdlib);
    let project_theorem_index = theorem_index
        .as_deref()
        .map(clean_server::proof_state::ProjectTheoremIndexProvider::from_path)
        .transpose()?;

    if websocket {
        let mut config = WebSocketConfig {
            addr,
            gpu_enabled: !no_gpu,
            ..Default::default()
        };
        config.initial_env = initial_env;
        config.project_theorem_index = project_theorem_index;
        println!("Starting WebSocket server on {}...", config.addr);
        clean_server::serve_websocket(config).await?;
    } else {
        let mut config = clean_server::ServerConfig::new()
            .with_addr(addr)
            .with_gpu(!no_gpu);
        config.initial_env = initial_env;
        config.project_theorem_index = project_theorem_index;
        println!("Starting TCP server on {}...", config.addr);
        clean_server::serve(config).await?;
    }
    Ok(())
}

/// Dispatch every non-server, non-async subcommand. Kept separate so the
/// top-level `run` stays within the per-file function-size budget.
fn dispatch_sync(command: Commands) -> anyhow::Result<()> {
    match command {
        Commands::Check(args) => {
            // Apply the TCB-neutral kernel memo-cache cap, if requested. CLI
            // value `0` means "unbounded" (no eviction), which we encode as
            // `usize::MAX` so no cache can ever reach the threshold. Any other
            // `N` is used verbatim; absent flag leaves the kernel default. The
            // cap is a global atomic, set before the worker thread spawns, so it
            // applies inside `run_check_on_large_stack`.
            if let Some(cap) = args.max_cache_entries {
                let kernel_cap = if cap == 0 { usize::MAX } else { cap };
                clean_kernel::set_global_max_cache_entries(kernel_cap);
            }
            // TCB-NEUTRAL robustness (a)-lite: run the check pipeline on a worker
            // thread with a large stack. The parser, elaborator, and kernel WHNF
            // reducer are all recursive (each already wraps recursion in
            // `stacker::maybe_grow`, but the default tokio worker thread that runs
            // `dispatch_sync` has only a ~2 MB stack, and stacker's first growth
            // segment is not always reached before a very deep concrete term —
            // e.g. a large transcoded LRAT certificate with thousands of nested
            // `List.cons` nodes — exhausts it). Giving the pipeline a deep stack
            // changes NO reduction logic and NO normal form: identical inputs
            // produce identical outputs; it only lets an already-correct deep
            // reduction run to completion instead of aborting with a Rust stack
            // overflow. See proofs/lrat_checker.lean (PHP(6,5) certificate).
            run_check_on_large_stack(args)?;
        }
        Commands::ExportCert(args) => {
            cmd_export_cert::handle_export_cert_command(args)?;
        }
        Commands::VerifyC(args) => {
            cmd_core::verify_c_file(&args.file, args.verbose, args.fail_unknown)?;
        }
        Commands::Verify { command } => match command {
            VerifyCommands::Rust(args) => cmd_rust_sem::handle_rust_verify_command(args)?,
            VerifyCommands::Tla(args) => cmd_tla_sem::handle_tla_verify_command(args)?,
            #[cfg(feature = "sat-verify")]
            VerifyCommands::Proof(args) => cmd_sat_verify::handle_verify_proof_command(args)?,
            // `VerifyCommands` is `#[non_exhaustive]` so future sibling verbs
            // (e.g. `verify c`, `verify wasm`) can drop in without breaking
            // this dispatcher. New variants must gain a concrete arm here.
            #[allow(unreachable_patterns)]
            _ => unreachable!("unhandled VerifyCommands variant; add a dispatch arm"),
        },
        Commands::Auto { command } => match command {
            AutoCommands::Prove(args) => cmd_auto::handle_auto_prove_command(args)?,
            AutoCommands::Premise(args) => cmd_auto::handle_auto_premise_command(args)?,
            // `AutoCommands` is `#[non_exhaustive]` so siblings (e.g.
            // `auto premise`, `auto smt`) can drop in without breaking this
            // dispatcher. New variants must gain a concrete arm here.
            _ => unreachable!("unhandled AutoCommands variant; add a dispatch arm"),
        },
        Commands::Eval(args) => {
            cmd_core::eval_expr(&args.expr, args.verbose)?;
        }
        Commands::Repl(_args) => {
            cmd_repl::run()?;
        }
        Commands::Lake(args) => cmd_lake::handle_lake_command(args.command, args.dir)?,
        Commands::Fold { command } => cmd_fold::handle_fold_command(command)?,
        Commands::Commit { command } => cmd_commit::handle_commit_command(command)?,
        Commands::Cert { command } => cmd_cert::handle_cert_command(command)?,
        Commands::Kernel { command } => cmd_kernel::handle_kernel_command(command)?,
        Commands::Bench { command } => cmd_bench::handle_bench_command(command)?,
        Commands::Promote { command } => cmd_promote::handle_promote_command(command)?,
        Commands::Prove { command } => cmd_prove::handle_prove_command(command)?,
        Commands::Release { command } => cmd_release::handle_release_command(command)?,
        Commands::Research { command } => cmd_research::handle_research_command(command)?,
        Commands::Replacement { command } => cmd_replacement::handle_replacement_command(command)?,
        Commands::Factory { command } => cmd_factory::handle_factory_command(command)?,
        Commands::Math { command } => cmd_math::handle_math_command(command)?,
        Commands::Project { command } => cmd_project::handle_project_command(command)?,
        Commands::Attempts { command } => cmd_attempts::handle_attempt_command(command)?,
        Commands::Artifacts { command } => cmd_artifacts::handle_artifacts_command(command)?,
        Commands::Audit { command } => cmd_audit::handle_audit_command(command)?,
        Commands::Discover(args) => cmd_discover::handle_discover_command(args)?,
        Commands::Tlaps(args) => cmd_tlaps::handle_tlaps_command(args)?,
        Commands::Features {
            category,
            stability,
            search,
            json,
        } => {
            cmd_features::run(
                category.as_deref(),
                stability.as_deref(),
                search.as_deref(),
                json,
            )?;
        }
        Commands::Help { path } => cmd_help::run(path.as_deref())?,
        Commands::Mathverse(args) => cmd_mathverse::handle_mathverse_command(args)?,
        Commands::Cake { command } => cmd_cake::handle_cake_command(command)?,
        Commands::Solver { command } => cmd_solver::handle_solver_command(command)?,
        Commands::Vendor { command } => cmd_vendor::handle_vendor_command(command)?,
        Commands::Olean(args) => cmd_olean::handle_olean_command(args)?,
        Commands::Compile(args) => cmd_compile::handle_compile_command(args)?,
        Commands::Run(args) => cmd_run::handle_run_command(args)?,
        Commands::SorryTrace(args) => cmd_sorry_trace::handle_sorry_trace_command(args)?,
        Commands::SorryCensus(args) => cmd_sorry_census::handle_sorry_census_command(args)?,
        Commands::Server(_) => {
            unreachable!("Server is dispatched in run() because it is async")
        }
        Commands::Lsp(_) => {
            unreachable!("Lsp is dispatched in run() because it is async")
        }
    }
    Ok(())
}

/// Stack size (in bytes) for the dedicated `clean check` worker thread.
///
/// The default tokio worker thread that runs `dispatch_sync` has a ~2 MB stack,
/// which the recursive parser / elaborator / kernel-WHNF pipeline can exhaust on
/// very deep concrete terms (e.g. a transcoded LRAT certificate with thousands of
/// nested `List.cons` nodes). 1 GiB comfortably absorbs those depths.
const CHECK_THREAD_STACK_SIZE: usize = 1024 * 1024 * 1024;

/// Run the `clean check` pipeline on a dedicated thread with a large stack.
///
/// TCB-NEUTRAL: this changes only the available stack depth, not any reduction
/// logic, definitional-equality decision, or normal form. The closure runs the
/// exact same `check_file_with_json` call that previously ran inline; identical
/// inputs yield identical outputs. The sole effect is that an already-correct but
/// deeply recursive reduction can finish instead of aborting with a Rust stack
/// overflow.
fn run_check_on_large_stack(args: clean_kernel::cli::CheckArgs) -> anyhow::Result<()> {
    let handle = std::thread::Builder::new()
        .name("clean-check".to_string())
        .stack_size(CHECK_THREAD_STACK_SIZE)
        .spawn(move || {
            cmd_core::check_file_with_json_with_imports(
                &args.file,
                args.verbose,
                args.allow_sorry,
                args.prelude,
                args.json,
                args.imports_prefer_olean,
            )
        })
        .map_err(|e| anyhow::anyhow!("failed to spawn clean-check worker thread: {e}"))?;
    handle
        .join()
        .map_err(|_| anyhow::anyhow!("clean-check worker thread panicked"))?
}

/// Run the clean CLI, parsing arguments from the process command line.
pub async fn run() -> anyhow::Result<()> {
    // LSP clients frame JSON-RPC on stdio and some (notably tower-lsp's own
    // tests, plus generic LSP extensions) treat any tracing chatter on stderr
    // as a protocol violation or noisy startup warning. Skip the
    // tracing-subscriber init for `lsp` so the server starts silently; all
    // other commands opt back in, with diagnostics on stderr so `--json`
    // stdout remains machine-readable.
    let cli = Cli::parse();
    if !matches!(cli.command, Commands::Lsp(_)) {
        tracing_subscriber::fmt()
            .with_writer(std::io::stderr)
            .init();
    }

    match cli.command {
        Commands::Server(args) => {
            dispatch_server(
                args.port,
                args.no_gpu,
                args.websocket,
                args.init,
                args.stdlib,
                args.theorem_index,
            )
            .await
        }
        Commands::Lsp(args) => cmd_lsp::handle_lsp_command(args).await,
        other => dispatch_sync(other),
    }
}

/// Return the process exit code requested by a command error, when the command
/// is forwarding an already-executed child process status.
pub fn forwarded_exit_code(err: &anyhow::Error) -> Option<i32> {
    cmd_lake::native_executable_exit_code(err)
}

#[cfg(test)]
mod cmd_core_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_external_cert;

/// Test-only helpers exposed for the `feature_coverage` integration test.
///
/// Hidden from rustdoc because this API is not part of the public library
/// surface — it only exists so `crates/clean-cli/tests/feature_coverage.rs`
/// can inspect the same clap tree and descriptor registry the binary
/// dispatches against. Part of Epic #3436.
#[doc(hidden)]
pub mod __test_support {
    use std::collections::BTreeMap;

    use clap::CommandFactory;
    use clean_features::{Category, FeatureDescriptor, Stability};

    /// Re-export the real top-level clap parser so integration tests can
    /// validate descriptor example `cmd` strings against the exact argument
    /// grammar the `clean` binary dispatches against. Without this, drift
    /// tests would need a stub parser (e.g. `external_subcommand`) that
    /// silently accepts invalid commands — defeating the point of the
    /// `every_feature_has_example` drift check (#3481).
    pub use crate::cli_args::Cli as TestCli;

    /// Apply the same filter predicate `clean features` uses when rendering
    /// the human or JSON index. Exposed so drift tests can exercise the
    /// stability/category/search filter without spawning a subprocess or
    /// duplicating the predicate logic.
    ///
    /// Part of #3455 (Phase 4 meta-gate): the coverage test for
    /// `clean features --stability experimental` depends on the **real**
    /// filter implementation, not a re-implementation that could drift.
    #[must_use]
    pub fn filter_descriptors(
        descriptors: Vec<&'static FeatureDescriptor>,
        category: Option<Category>,
        stability: Option<Stability>,
        search: Option<&str>,
    ) -> Vec<&'static FeatureDescriptor> {
        crate::cmd_features::filter_descriptors(descriptors, category, stability, search)
    }

    /// Return every clap subcommand path reachable from the top-level `Cli`
    /// parser. Includes nested groups (e.g. `["lake", "build"]`,
    /// `["fold", "verify"]`).
    #[must_use]
    pub fn collect_clap_paths() -> Vec<Vec<String>> {
        let command = <crate::cli_args::Cli as CommandFactory>::command();
        let mut out = Vec::new();
        for sub in command.get_subcommands() {
            walk(sub, Vec::new(), &mut out);
        }
        out
    }

    fn walk(cmd: &clap::Command, prefix: Vec<String>, out: &mut Vec<Vec<String>>) {
        let mut path = prefix;
        path.push(cmd.get_name().to_owned());
        out.push(path.clone());
        for sub in cmd.get_subcommands() {
            walk(sub, path.clone(), out);
        }
    }

    /// Return the live descriptor registry the `clean` binary dispatches
    /// against. Empty in Phase 1.
    #[must_use]
    pub fn all_features() -> Vec<&'static FeatureDescriptor> {
        crate::registry::all_features()
    }

    /// Metadata for one registered descriptor source: the per-crate slice, a
    /// short label identifying it, and the set of top-level verb roots the
    /// slice is allowed to cover. Returned by [`feature_sources`] for the
    /// slice-rooting drift test (Epic #3436, issue #3497).
    ///
    /// Each slice's `allowed_roots` is the intentional root set for that
    /// owning crate. A stray descriptor whose `path[0]` (or `domain_root`
    /// when set) falls outside this set fires
    /// `source_slice_domain_roots_match_allowlist` immediately — catching the
    /// "future crate registering `[\"foo\"]` from `clean-bar`" regression
    /// #3497 calls out.
    ///
    /// The allowlist is intentionally explicit rather than inferred from the
    /// slice itself: inferring the set from the slice would trivially accept
    /// whatever the slice contains and defeat the drift check.
    #[derive(Clone, Copy)]
    pub struct FeatureSource {
        /// Slice identifier (e.g. `"clean_kernel::cli::FEATURES"`). Used only
        /// in test-failure messages.
        pub name: &'static str,
        /// The `FEATURES` (or analogous) slice published by a domain crate.
        pub slice: &'static [FeatureDescriptor],
        /// Top-level verbs this slice is allowed to register. A descriptor
        /// whose normalized root is not in this list is a slice-rooting leak.
        pub allowed_roots: &'static [&'static str],
    }

    /// Per-source allowlist table: one entry per `v.extend(...)` line in
    /// [`crate::registry::all_features`]. Declared as a `const` table so the
    /// public [`feature_sources`] accessor stays small; the table itself is
    /// static data with no logic.
    const FEATURE_SOURCES: &[FeatureSource] = &[
        FeatureSource {
            name: "clean_c_sem::cli::FEATURES",
            slice: clean_c_sem::cli::FEATURES,
            allowed_roots: &["verify-c"],
        },
        FeatureSource {
            name: "clean_rust_sem::cli::FEATURES",
            slice: clean_rust_sem::cli::FEATURES,
            allowed_roots: &["verify"],
        },
        FeatureSource {
            name: "clean_auto::cli::FEATURES",
            slice: clean_auto::cli::FEATURES,
            allowed_roots: &["auto"],
        },
        FeatureSource {
            name: "clean_tla::cli::FEATURES",
            slice: clean_tla::cli::FEATURES,
            allowed_roots: &["verify"],
        },
        FeatureSource {
            name: "clean_server::cli::FEATURES",
            slice: clean_server::cli::FEATURES,
            allowed_roots: &["server"],
        },
        FeatureSource {
            name: "clean_fold::cli::FEATURES",
            slice: clean_fold::cli::FEATURES,
            allowed_roots: &["fold"],
        },
        FeatureSource {
            name: "clean_fold::commit::cli::FEATURES",
            slice: clean_fold::commit::cli::FEATURES,
            allowed_roots: &["commit"],
        },
        // `clean_kernel` owns both `check` (kernel type-checker) and the
        // `cert verify*` trio (certificate verification). They share one
        // slice to keep `clean-kernel/src/cli/mod.rs` under the 500-line cap.
        FeatureSource {
            name: "clean_kernel::cli::FEATURES",
            slice: clean_kernel::cli::FEATURES,
            allowed_roots: &["check", "cert"],
        },
        // Phase 3 kernel-verb absorptions (#3443/#3444/#3446/#3447): every
        // descriptor lives under the `kernel` verb.
        FeatureSource {
            name: "clean_kernel::cli::KERNEL_VERB_FEATURES",
            slice: clean_kernel::cli::KERNEL_VERB_FEATURES,
            allowed_roots: &["kernel"],
        },
        FeatureSource {
            name: "clean_elab::cli::FEATURES",
            slice: clean_elab::cli::FEATURES,
            allowed_roots: &["eval"],
        },
        FeatureSource {
            name: "clean_lake::cli::FEATURES",
            slice: clean_lake::cli::FEATURES,
            allowed_roots: &["lake"],
        },
        FeatureSource {
            name: "clean_cli::cli::FEATURES",
            slice: crate::cli::FEATURES,
            // `sorry-census` is a Rust wrapper around `scripts/sorry_census.sh`
            // owned by clean-cli (#1144). `export-cert` is the parser →
            // elaborator → kernel → `.cleancert` bundle pipeline (audit item 6
            // from `docs/mathbot/CLEAN-VERIFIER-AUDIT-2026-05-27.md`) — its
            // handler in `clean-cli/src/cmd_export_cert.rs` links the parser,
            // elaborator, and kernel cert bundle crates together, so it lives
            // here rather than in any single domain crate.
            // `run` is the Phase 5 native build-and-run path (Epic #3436): its
            // handler in `clean-cli/src/cmd_run.rs` reuses the `compile` emit-C
            // bridge and links against `clean-runtime`, so it lives here rather
            // than in any single domain crate.
            allowed_roots: &["repl", "sorry-trace", "sorry-census", "export-cert", "run"],
        },
        FeatureSource {
            name: "clean_cli::cli::bench::FEATURES",
            slice: crate::cli::bench::FEATURES,
            allowed_roots: &["bench"],
        },
        FeatureSource {
            name: "clean_cli::cli::promote::FEATURES",
            slice: crate::cli::promote::FEATURES,
            allowed_roots: &["promote"],
        },
        FeatureSource {
            name: "clean_cli::cmd_research::FEATURES",
            slice: crate::cmd_research::FEATURES,
            allowed_roots: &["research"],
        },
        FeatureSource {
            name: "clean_cli::cmd_factory::FEATURES",
            slice: crate::cmd_factory::FEATURES,
            allowed_roots: &["factory"],
        },
        FeatureSource {
            name: "clean_cli::cmd_math::FEATURES",
            slice: crate::cmd_math::FEATURES,
            allowed_roots: &["math"],
        },
        FeatureSource {
            name: "clean_cli::cmd_project::FEATURES",
            slice: crate::cmd_project::FEATURES,
            allowed_roots: &["project"],
        },
        FeatureSource {
            name: "clean_cli::cmd_attempts::FEATURES",
            slice: crate::cmd_attempts::FEATURES,
            allowed_roots: &["attempts"],
        },
        // `clean prove run/status/list` — submit a Lean goal to a remote /
        // automated prover backend (Aristotle / ax-prover), retrieve the proof,
        // and re-verify it locally. Handlers live in `clean-cli/src/cmd_prove.rs`
        // (they shell out to the external `aristotle` / `ax-prover` CLIs).
        FeatureSource {
            name: "clean_cli::cmd_prove::FEATURES",
            slice: crate::cmd_prove::FEATURES,
            allowed_roots: &["prove"],
        },
        // `clean cake build/graduate/verify` — the Layer-1 CAKE project
        // lifecycle. Handlers live in `clean-cli/src/cmd_cake.rs` (the build
        // step shells out to lake; graduate/verify reuse the clean-mathverse
        // graduation engine + full cake gate), so the descriptors live here.
        FeatureSource {
            name: "clean_cli::cmd_cake::FEATURES",
            slice: crate::cmd_cake::FEATURES,
            allowed_roots: &["cake"],
        },
        // `clean vendor fetch/package/status/clean` — vendored-sources lifecycle
        // for offline/reproducible builds (artifact-based; replaces fetch_vendor.sh).
        FeatureSource {
            name: "clean_cli::cmd_vendor::FEATURES",
            slice: crate::cmd_vendor::FEATURES,
            allowed_roots: &["vendor"],
        },
        // Artifact system v0 (master design v2 §5.6): generic release-artifact
        // list/get/verify/extract with fail-closed blake3 verification.
        FeatureSource {
            name: "clean_cli::cmd_artifacts::FEATURES",
            slice: crate::cmd_artifacts::FEATURES,
            allowed_roots: &["artifacts"],
        },
        FeatureSource {
            name: "clean_cli::cmd_audit::FEATURES",
            slice: crate::cmd_audit::FEATURES,
            allowed_roots: &["audit"],
        },
        FeatureSource {
            name: "clean_discovery::cli::FEATURES",
            slice: clean_discovery::cli::FEATURES,
            allowed_roots: &["discover"],
        },
        FeatureSource {
            name: "clean_tla::bench::cli::FEATURES",
            slice: clean_tla::bench::cli::FEATURES,
            allowed_roots: &["tlaps"],
        },
        FeatureSource {
            name: "clean_mathverse::cli::FEATURES",
            slice: clean_mathverse::cli::FEATURES,
            allowed_roots: &["mathverse"],
        },
        // Phase 3.5 (#3512) — browse-oriented mathverse verbs registered as a
        // separate slice to keep `cli/mod.rs` under the file-size cap. Mirrors
        // the `registry::all_features` `v.extend(BROWSE_FEATURES)` call.
        FeatureSource {
            name: "clean_mathverse::cli::BROWSE_FEATURES",
            slice: clean_mathverse::cli::BROWSE_FEATURES,
            allowed_roots: &["mathverse"],
        },
        // Phase 3.5 (#3512) — the 7 passthrough-absorbed mathverse verbs
        // (find / graph / diff / verify / download / export / release).
        // Mirrors the `registry::all_features` `v.extend(PASSTHROUGH_FEATURES)`
        // call; kept as a separate slice so the descriptor module stays
        // under the 500-line file-size cap.
        FeatureSource {
            name: "clean_mathverse::cli::PASSTHROUGH_FEATURES",
            slice: clean_mathverse::cli::PASSTHROUGH_FEATURES,
            allowed_roots: &["mathverse"],
        },
        // Phase 3.5 (#3513) — operator-tool descriptors (mathverse_convert /
        // mathverse_shard) surfaced via `Category::OperatorTools`.
        FeatureSource {
            name: "clean_mathverse::cli::OPERATOR_TOOLS_FEATURES",
            slice: clean_mathverse::cli::OPERATOR_TOOLS_FEATURES,
            allowed_roots: &["mathverse"],
        },
        FeatureSource {
            name: "clean_olean::cli::FEATURES",
            slice: clean_olean::cli::FEATURES,
            allowed_roots: &["olean"],
        },
        FeatureSource {
            name: "clean_lsp::cli::FEATURES",
            slice: clean_lsp::cli::FEATURES,
            allowed_roots: &["lsp"],
        },
        FeatureSource {
            name: "clean_compiler::cli::FEATURES",
            slice: clean_compiler::cli::FEATURES,
            allowed_roots: &["compile"],
        },
    ];

    /// Return the per-source `FEATURES` slices that populate the registry,
    /// each paired with a short label and the allowlisted set of root verbs
    /// the slice is permitted to register. Drift tests use this to assert
    /// that each slice's descriptors stay rooted in the crate's own domain
    /// (Epic #3436, issue #3497). The label is the slice identifier, not
    /// necessarily the crate name, because several crates publish more than
    /// one slice (e.g. `clean_kernel::cli::{FEATURES, KERNEL_VERB_FEATURES}`
    /// and `clean_mathverse::cli::{FEATURES, BROWSE_FEATURES, PASSTHROUGH_FEATURES, OPERATOR_TOOLS_FEATURES}`).
    ///
    /// The baseline list is a `const` table
    /// ([`self::FEATURE_SOURCES`](FEATURE_SOURCES)); the
    /// `sat-verify`-gated `clean_verify::cli::FEATURES` is appended at
    /// runtime because its visibility depends on a Cargo feature flag.
    #[must_use]
    pub fn feature_sources() -> Vec<FeatureSource> {
        #[cfg(not(feature = "sat-verify"))]
        {
            FEATURE_SOURCES.to_vec()
        }
        #[cfg(feature = "sat-verify")]
        {
            let mut sources: Vec<FeatureSource> = FEATURE_SOURCES.to_vec();
            sources.push(FeatureSource {
                name: "clean_verify::cli::FEATURES",
                slice: clean_verify::cli::FEATURES,
                allowed_roots: &["verify"],
            });
            sources
        }
    }

    /// Return the clap paths that are intentionally meta-only (no descriptor
    /// expected). Phase 1 treats `features`, `help`, and `repl` as meta.
    #[must_use]
    pub fn meta_paths() -> Vec<Vec<String>> {
        crate::registry::META_PATHS
            .iter()
            .map(|segments| segments.iter().map(|s| (*s).to_owned()).collect())
            .collect()
    }

    /// Render the full `docs/cli/` tree in memory as a `filename -> contents`
    /// map. Shared by the `gen_cli_docs` binary (which persists the map to
    /// disk) and the `docs_drift` integration test (which diffs it against
    /// the committed tree). Part of Phase 5 (#3482).
    #[must_use]
    pub fn render_all_docs(descriptors: &[&'static FeatureDescriptor]) -> BTreeMap<String, String> {
        crate::doc_render::render_all_docs(descriptors)
    }

    /// Filename (within `docs/cli/`) the generator uses for a descriptor.
    /// Exposed so the drift test can point to a specific file in its diff
    /// output without re-deriving the naming convention.
    #[must_use]
    pub fn doc_filename_for(descriptor: &FeatureDescriptor) -> String {
        crate::doc_render::filename_for(descriptor)
    }

    /// Filename of the generated top-level index file, relative to
    /// `docs/cli/`.
    #[must_use]
    pub fn doc_index_filename() -> &'static str {
        crate::doc_render::INDEX_FILENAME
    }
}
