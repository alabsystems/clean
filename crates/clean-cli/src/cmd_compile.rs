// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch the `clean compile` subcommand into the clean file-to-emit bridge.
//!
//! Argument parsing and descriptor registration live in
//! [`clean_compiler::cli`]. The top-level CLI owns the source-file bridge
//! because it already depends on parser, elaborator, kernel, and compiler
//! crates; moving that bridge into `clean-compiler` would invert the crate
//! dependency graph.
//!
//! Part of Epic #3436 Phase 4 (#3453): exposes `clean compile` as an
//! `Stability::Experimental` MVP surface. #3708 tracks the larger
//! file-to-executable runtime closure. The text emitters produce source/IR
//! only; `--emit obj` (trust-ir-backend feature) additionally lowers to
//! trust-ir and invokes `trust-cg` to write a native object — but neither
//! links the result into an executable.

use std::collections::HashSet;
use std::io::Write;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, Context};
use clean_compiler::cli::{CompileArgs, EmitFormat};
use clean_compiler::emit_c::CEmitConfig;
use clean_compiler::emit_rust::RustEmitConfig;
use clean_compiler::mangle::mangle_name;
use clean_compiler::pass_manager::{
    compile_lcnf_decls, compile_lcnf_to_c, compile_lcnf_to_rust, PipelineConfig,
};
use clean_compiler::{constant_to_decl, BoxingConfig, Decl, OptConfig, RCConfig};
use clean_elab::{
    elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context, ElabResult,
    FileContext,
};
use clean_kernel::{Environment, Expr, ExprVisitor, LevelVec, Name, TypeChecker};
use clean_parser::parse_file_with_tactics;
use clean_server::handlers::validate_decl_read_only;

use crate::cmd_run::is_primitive_denylisted;

/// Collects the names of every `Const` reachable from an expression.
///
/// Implements [`ExprVisitor`] with a no-op `combine` (the work happens as a
/// side effect in `visit_const`); the kernel's default `visit_expr` performs the
/// structural recursion for us. Used by the whole-module dependency walk to find
/// which other constants a declaration's value references.
struct ConstDepCollector {
    deps: Vec<Name>,
}

impl ConstDepCollector {
    fn new() -> Self {
        Self { deps: Vec::new() }
    }

    /// Run the collector over a value expression, returning every referenced
    /// constant name (with duplicates — the BFS `seen` set dedups).
    fn collect(value: &Expr) -> Vec<Name> {
        let mut collector = Self::new();
        collector.visit_expr(value);
        collector.deps
    }
}

impl ExprVisitor for ConstDepCollector {
    type Result = ();

    fn combine(&self, _a: (), _b: ()) {}

    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
        self.deps.push(name.clone());
    }
}

/// Entry point wired from `dispatch_sync` in `lib.rs`.
pub(crate) fn handle_compile_command(args: CompileArgs) -> anyhow::Result<()> {
    // The native-object path writes a binary file, not text to stdout.
    #[cfg(feature = "trust-ir-backend")]
    if args.emit == EmitFormat::Obj {
        return compile_to_object(&args);
    }

    let output_path = args.output.clone();
    let output = compile_to_string(args)?;
    match output_path {
        Some(path) => std::fs::write(&path, output.as_bytes())
            .with_context(|| format!("failed to write output to {}", path.display()))?,
        None => {
            let mut stdout = std::io::stdout().lock();
            stdout.write_all(output.as_bytes())?;
            if !output.ends_with('\n') {
                writeln!(stdout)?;
            }
        }
    }
    Ok(())
}

pub(crate) fn compile_to_string(args: CompileArgs) -> anyhow::Result<String> {
    let (lcnf_decls, compile_env, pipeline) = select_lcnf_decl(&args)?;
    emit_decls(
        &lcnf_decls,
        &compile_env,
        args.emit,
        &pipeline,
        args.file.as_deref(),
    )
}

/// Elaborate the source file, select the requested declaration, and lower it
/// together with its transitive *compilable* dependency closure to a `Vec` of
/// L5CNF `Decl`s ready for a backend. Shared by the text emitters and the
/// native-object path.
///
/// The closure is a BFS over the value expressions of the selected declaration
/// and each compilable dependency. The **relaxed #14 extern boundary** decides
/// per referenced const — uniformly for source-file AND prelude consts — whether
/// it is compiled from source or forward-declared (extern) by the backend. A
/// const is COMPILED iff ALL of:
///
/// 1. Its mangled symbol is not in the PRIMITIVE_DENYLIST (every symbol with a
///    runtime shim — the `Nat.add`/`sub`/`mul`/`decEq` ops, the `HAdd`/`HMul`/
///    `HSub` typeclass dispatchers, the `Bool` ctors, and the `IO`-monad ops):
///    those keep their runtime shim, whose specific C contract (O(1) win,
///    representation invariant, or effect model) the lowered Lean body would
///    break. Stay extern.
/// 2. `constant_to_decl` returns `Ok(Some)`. `Ok(None)` (axiom/opaque/ctor/
///    noncomputable) or `Err(_)` (value present but lowering failed, e.g.
///    `List.length`) -> extern.
/// 3. The candidate `Decl` survives an isolated IR type-lowering probe. Some
///    consts pass `constant_to_decl` but the IR lowerer rejects their polymorphic
///    shape later (`List.reverse`, `Option.getD`); since that failure would
///    otherwise abort the whole `Vec<Decl>` emit, we probe in isolation and drop
///    to extern on failure.
///
/// In every drop case we do NOT emit a body, do NOT recurse into the dependency,
/// and crucially do NOT propagate any lowering `Err` — per-const fallback never
/// aborts the compile. Only the **root** (the selected decl) keeps hard-error
/// behavior: a non-compilable root is a usage error with the original message.
fn select_lcnf_decl(
    args: &CompileArgs,
) -> anyhow::Result<(Vec<Decl>, Environment, PipelineConfig)> {
    let file = args
        .file
        .as_deref()
        .ok_or_else(|| anyhow!("`clean compile` requires a source file"))?;
    let decl_name = args
        .decl
        .as_deref()
        .ok_or_else(|| anyhow!("`clean compile` requires `--decl <NAME>`"))?;

    let env = elaborate_file_to_env(file)?;
    let root_name = Name::from_string(decl_name);
    let root_info = env
        .get_const(&root_name)
        .ok_or_else(|| anyhow!("declaration `{decl_name}` was not found after elaboration"))?;
    let root_decl = constant_to_decl(&env, root_info)
        .with_context(|| format!("failed to lower `{decl_name}` to L5CNF"))?
        .ok_or_else(|| {
            anyhow!(
                "declaration `{decl_name}` is not compilable; axioms, opaque declarations, \
                theorems without runtime values, and noncomputable declarations cannot be emitted"
            )
        })?;

    // BFS over the dependency graph. `seen` dedups and terminates on cycles /
    // self- and mutual recursion: the root is inserted first, so a recursive
    // reference back to it is already in `seen` and the walk cannot loop.
    let mut seen: HashSet<Name> = HashSet::new();
    seen.insert(root_name.clone());

    let mut decls = vec![root_decl];

    // Worklist of value expressions still to scan for dependencies. We scan the
    // root's value, then each compilable dependency's value, transitively.
    let mut worklist: Vec<Name> = ConstDepCollector::collect(
        root_info
            .value
            .as_ref()
            .expect("constant_to_decl returned Some, so the root has a value"),
    );

    let pipeline = pipeline_config_from_opt_level(args.opt_level);

    // Silence the default panic hook for the duration of the dependency-probe
    // loop: a candidate dep that trips a `debug_assert!` during the isolated
    // probe is caught and dropped to extern (see below), so its panic trace is
    // expected noise, not a failure. Restored immediately after the loop.
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    while let Some(dep_name) = worklist.pop() {
        if !seen.insert(dep_name.clone()) {
            continue;
        }
        // Resolve the dependency. A name with no constant info is forward-declared
        // by the backend (extern); nothing to emit or recurse into.
        let Some(dep_info) = env.get_const(&dep_name) else {
            continue;
        };

        // RELAXED #14 EXTERN BOUNDARY. The old code dropped *every* prelude const
        // (`!source_decls.contains`) as an extern unconditionally. Many prelude
        // defs now lower (`Nat.pred`, `Nat.blt`, `String.length`, ...), so we
        // apply ONE uniform predicate to source AND prelude deps: a referenced
        // const is COMPILED from source iff
        //   (a) its mangled symbol is not in the PRIMITIVE_DENYLIST, AND
        //   (b) `constant_to_decl` -> `Ok(Some)`, AND
        //   (c) it survives the IR type-lowering probe.
        // Otherwise it stays an extern: do NOT emit, do NOT recurse, do NOT
        // propagate any `Err`. This per-const fallback never aborts the compile.

        // (a) PRIMITIVE_DENYLIST: any symbol with a runtime shim (Nat ops, the
        // HAdd/HMul/HSub typeclass dispatchers, Bool ctors, IO ops) keeps its
        // shim — the lowered body would break the shim's C contract (O(1) win,
        // representation invariant, or effect model). Stay extern.
        if is_primitive_denylisted(&mangle_name(&dep_name)) {
            continue;
        }

        // (b) A const that does not lower to a compilable `Decl` — `Ok(None)`
        // (axiom/opaque/ctor/noncomputable) or `Err(_)` (value present but
        // lowering failed, e.g. `List.length`) — is an extern. Drop and continue;
        // crucially do NOT propagate the `Err`.
        let Ok(Some(dep_decl)) = constant_to_decl(&env, dep_info) else {
            continue;
        };

        // (c) IR-PROBE GUARD for the DANGER bucket. Some consts lower to
        // `Ok(Some)` at L5CNF but the IR type lowerer rejects their polymorphic
        // shape later (`List.reverse`, `Option.getD` -> "unsupported IR type
        // expression"). That failure surfaces in `emit_decls` over the WHOLE
        // `Vec<Decl>`, so a single bad dep would abort the entire compile and
        // defeat per-const fallback. Probe each candidate through the same
        // pipeline in isolation first; on failure, keep it extern and continue.
        //
        // The probe is wrapped in `catch_unwind`: some lowering paths trip a
        // `debug_assert!` (e.g. `self.pending.is_empty()`) on shapes they cannot
        // handle, which would otherwise crash the whole compile. A panic here is
        // treated exactly like an `Err` — drop the dep to extern. This is sound:
        // the probe only borrows immutable `&dep_decl` / `&env` / `&pipeline` and
        // discards all probe output, so no shared state is left inconsistent.
        let probe = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            compile_lcnf_decls(std::slice::from_ref(&dep_decl), &env, &pipeline)
        }));
        if !matches!(probe, Ok(Ok(_))) {
            continue;
        }

        // Compilable dependency: emit it and keep walking its value.
        if let Some(value) = &dep_info.value {
            worklist.extend(ConstDepCollector::collect(value));
        }
        decls.push(dep_decl);
    }

    std::panic::set_hook(prev_hook);

    // Phase 0 #1: thread the real elaborated environment through to IR lowering
    // (so `to_ir`'s `build_ctor_env` sees the prelude constructors), together with
    // the transitive compilable closure. `env` is only borrowed by the dep-walk
    // above, so it is still owned here.
    Ok((decls, env, pipeline))
}

/// Compile the selected declaration to a native object file by lowering to
/// trust-ir and invoking the `trust-cg` backend. Requires `-o <path>` and a
/// `trust-cg` binary (located via `CLEAN_TRUST_CG_BIN` or `PATH`).
#[cfg(feature = "trust-ir-backend")]
fn compile_to_object(args: &CompileArgs) -> anyhow::Result<()> {
    use clean_compiler::emit_trust_ir::{serialize_tmbc, RuntimeLowering, TrustIrConfig};
    use clean_compiler::pass_manager::compile_lcnf_to_trust_ir;

    let out = args
        .output
        .as_deref()
        .ok_or_else(|| anyhow!("`--emit obj` requires an output path (`-o <PATH>`)"))?;
    let trust_cg = find_trust_cg().ok_or_else(|| {
        anyhow!(
            "trust-cg binary not found; set CLEAN_TRUST_CG_BIN or add `trust-cg` to PATH \
             (build it in the sibling trust-cg repo)"
        )
    })?;
    let target = host_trust_cg_target()?;

    let (lcnf_decls, compile_env, pipeline) = select_lcnf_decl(args)?;
    let config = TrustIrConfig {
        module_name: "clean_module".to_string(),
        use_clean_dialect: true,
        // ExternCalls: real runtime calls, i.e. trust-cg-compilable native code.
        runtime_lowering: RuntimeLowering::ExternCalls,
        // File-granular debug info: the emitted instructions carry spans
        // pointing at the compiled source file.
        source_file: args.file.as_ref().map(|p| p.display().to_string()),
        ..TrustIrConfig::default()
    };
    let module = compile_lcnf_to_trust_ir(&lcnf_decls, &compile_env, &pipeline, &config)?;

    let tmbc = tempfile::Builder::new()
        .suffix(".tmbc")
        .tempfile()
        .context("failed to create temporary .tmbc file")?;
    std::fs::write(tmbc.path(), serialize_tmbc(&module))
        .context("failed to write temporary .tmbc")?;

    let status = std::process::Command::new(&trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(out)
        .arg(tmbc.path())
        .status()
        .with_context(|| format!("failed to invoke trust-cg at {}", trust_cg.display()))?;
    if !status.success() {
        anyhow::bail!(
            "trust-cg failed to compile the trust-ir module to {}",
            out.display()
        );
    }
    Ok(())
}

/// Locate the `trust-cg` binary: `CLEAN_TRUST_CG_BIN` if set and a file, else
/// the first `trust-cg` on `PATH`.
#[cfg(feature = "trust-ir-backend")]
fn find_trust_cg() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("CLEAN_TRUST_CG_BIN") {
        let pb = PathBuf::from(p);
        if pb.is_file() {
            return Some(pb);
        }
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|dir| dir.join("trust-cg"))
        .find(|cand| cand.is_file())
}

/// Map the host architecture to a `trust-cg --target` value.
#[cfg(feature = "trust-ir-backend")]
fn host_trust_cg_target() -> anyhow::Result<&'static str> {
    match std::env::consts::ARCH {
        "aarch64" => Ok("aarch64"),
        "x86_64" => Ok("x86_64"),
        other => anyhow::bail!("unsupported host architecture for trust-cg: {other}"),
    }
}

/// Elaborate every declaration in `path`, returning the resulting environment
/// (prelude + source decls).
///
/// The #14 dependency walk no longer needs a source-file/prelude partition: the
/// relaxed extern boundary (see [`select_lcnf_decl`]) decides per-const whether a
/// referenced symbol is compiled from source or forward-declared by probing
/// `constant_to_decl` + IR lowering uniformly, regardless of which the const
/// originated in. So this returns only the environment.
fn elaborate_file_to_env(path: &Path) -> anyhow::Result<Environment> {
    let mut env = Environment::with_prelude();
    env.init_io_ops()
        .with_context(|| format!("failed to initialize IO operations for {}", path.display()))?;
    let mut in_flight: HashSet<PathBuf> = HashSet::new();
    let mut completed: HashSet<PathBuf> = HashSet::new();
    elaborate_file_into_env(path, &mut env, &mut in_flight, &mut completed)?;
    Ok(env)
}

/// Maximum intra-project import recursion depth — guards against pathological
/// resolver loops even when the `in_flight` cycle guard trips first. Mirrors
/// `cmd_core::MAX_IMPORT_DEPTH`.
const MAX_NATIVE_IMPORT_DEPTH: usize = 256;

/// Recursively elaborate `path` and every sibling `.lean` module it imports
/// into the shared `env`.
///
/// This is the codegen / native-build analog of `cmd_core::check_file_body`'s
/// first pass: BEFORE elaborating the file's own declarations, every
/// `import M.X.Y` directive is resolved to a project-local `.lean` source via
/// the shared [`clean_elab::resolve_intra_project_import`] resolver, and each
/// resolved file is elaborated into the SAME `env` first. By the time the
/// importing file's `main`/other decls elaborate, the imported constants
/// (e.g. `double`) are already registered, so they resolve instead of leaving
/// an unbound `FVar` sentinel that later crashes codegen.
///
/// External modules (Mathlib / Init / Batteries) resolve to `None` here and are
/// left for the `import` decl's normal `.olean` flow during elaboration below.
///
/// `in_flight` detects import cycles (a file currently on the elaboration
/// stack); `completed` dedups diamond-shaped graphs so a shared dependency is
/// elaborated once. Imported constants go through the normal kernel-checked
/// `elaborate_decl_and_register_with_warning` path — no `add_decl_unchecked`.
fn elaborate_file_into_env(
    path: &Path,
    env: &mut Environment,
    in_flight: &mut HashSet<PathBuf>,
    completed: &mut HashSet<PathBuf>,
) -> anyhow::Result<()> {
    if in_flight.len() >= MAX_NATIVE_IMPORT_DEPTH {
        anyhow::bail!(
            "import depth limit ({MAX_NATIVE_IMPORT_DEPTH}) exceeded while elaborating {}",
            path.display()
        );
    }

    let canonical = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    if completed.contains(&canonical) {
        return Ok(());
    }
    if !in_flight.insert(canonical.clone()) {
        anyhow::bail!(
            "import cycle detected at {}: file is already being elaborated",
            path.display()
        );
    }

    let result = elaborate_file_body(path, env, in_flight, completed);

    in_flight.remove(&canonical);
    if result.is_ok() {
        completed.insert(canonical);
    }
    result
}

fn elaborate_file_body(
    path: &Path,
    env: &mut Environment,
    in_flight: &mut HashSet<PathBuf>,
    completed: &mut HashSet<PathBuf>,
) -> anyhow::Result<()> {
    let source = std::fs::read_to_string(path)
        .with_context(|| format!("failed to read source file {}", path.display()))?;
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = parse_file_with_tactics(&source, &patterns)
        .with_context(|| format!("failed to parse {}", path.display()))?;

    // First pass: resolve `import M.X.Y` directives to sibling `.lean` sources
    // and elaborate them into the SAME `env` first, so their constants are
    // registered before this file's own decls reference them. External modules
    // (no project-local `.lean`) resolve to `None` and fall through to the
    // `.olean` flow handled by the `Import` decl in the main loop below.
    for decl in &decls {
        resolve_and_elaborate_imports(decl, path, env, in_flight, completed)?;
    }

    let mut file_ctx = FileContext::new();
    // Thread Lake `.olean` search paths so external imports still resolve via
    // the existing artifact loader during the main elaboration pass.
    file_ctx.set_import_search_paths(clean_elab::lake_import_search_paths_for_file(path));

    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        // Thread `file_ctx` so standalone `open`/`export` aliases and
        // file-scope notation persist across declarations (gap sweep B13),
        // keeping this surface consistent with `clean check`.
        let registered =
            elaborate_decl_and_register_with_context_and_warning(env, &processed, &mut file_ctx)
                .with_context(|| {
                    format!("failed to elaborate declaration in {}", path.display())
                })?;
        if let Some(warning) = registered.warning {
            anyhow::bail!(
                "refusing to compile declaration `{}` with trust warning {:?}",
                warning.decl_name,
                warning.kind
            );
        }
        validate_elab_result(&registered.result, env)
            .with_context(|| format!("kernel validation failed in {}", path.display()))?;
    }

    Ok(())
}

/// Walk a parsed declaration for `import M.X.Y` directives that resolve to a
/// project-local `.lean` source, and recursively elaborate each into `env`.
/// Descends through `namespace`/`section`/`mutual` wrappers and the bodies of
/// `set_option`/`open` that may carry nested decls, mirroring
/// `cmd_core::collect_intra_project_imports`.
fn resolve_and_elaborate_imports(
    decl: &clean_parser::SurfaceDecl,
    parent_path: &Path,
    env: &mut Environment,
    in_flight: &mut HashSet<PathBuf>,
    completed: &mut HashSet<PathBuf>,
) -> anyhow::Result<()> {
    use clean_parser::SurfaceDecl;
    match decl {
        SurfaceDecl::Import { paths, .. } => {
            for module_path in paths {
                if module_path.is_empty() {
                    continue;
                }
                let module_name = module_path.join(".");
                if let Some(import_file) =
                    clean_elab::resolve_intra_project_import(&module_name, parent_path)
                {
                    elaborate_file_into_env(&import_file, env, in_flight, completed)?;
                }
            }
        }
        SurfaceDecl::Namespace { decls, .. }
        | SurfaceDecl::Section { decls, .. }
        | SurfaceDecl::Mutual { decls, .. } => {
            for inner in decls {
                resolve_and_elaborate_imports(inner, parent_path, env, in_flight, completed)?;
            }
        }
        SurfaceDecl::SetOption {
            body: Some(body), ..
        }
        | SurfaceDecl::Open {
            body: Some(body), ..
        } => {
            resolve_and_elaborate_imports(body, parent_path, env, in_flight, completed)?;
        }
        _ => {}
    }
    Ok(())
}

fn validate_elab_result(result: &ElabResult, env: &Environment) -> anyhow::Result<()> {
    if matches!(
        result,
        ElabResult::Skipped | ElabResult::Command(_) | ElabResult::Multiple(_)
    ) {
        return Ok(());
    }

    let tc = TypeChecker::with_mode(env, env.mode());
    validate_decl_read_only(env, &tc, result)
        .map(|_| ())
        .map_err(|err| anyhow!(err))
}

fn pipeline_config_from_opt_level(opt_level: u8) -> PipelineConfig {
    match opt_level {
        0 => PipelineConfig {
            opt: OptConfig::minimal(),
            rc: RCConfig::minimal(),
            boxing: BoxingConfig::minimal(),
        },
        1 => PipelineConfig::default(),
        _ => PipelineConfig {
            opt: OptConfig::aggressive(),
            rc: RCConfig::aggressive(),
            boxing: BoxingConfig::default(),
        },
    }
}

// `source_file` feeds only the trust-ir arm's debug info; the other formats
// ignore it (and it is entirely unused without the `trust-ir-backend` feature).
#[cfg_attr(not(feature = "trust-ir-backend"), allow(unused_variables))]
fn emit_decls(
    decls: &[Decl],
    env: &Environment,
    emit: EmitFormat,
    pipeline: &PipelineConfig,
    source_file: Option<&Path>,
) -> anyhow::Result<String> {
    match emit {
        EmitFormat::L5cnf => Ok(format!("{decls:#?}\n")),
        EmitFormat::L5ir => {
            let artifacts = compile_lcnf_decls(decls, env, pipeline)?;
            Ok(format!("{:#?}\n", artifacts.boxed_ir_decls))
        }
        EmitFormat::C => Ok(compile_lcnf_to_c(
            decls,
            env,
            pipeline,
            CEmitConfig {
                check_ir: true,
                ..Default::default()
            },
        )?),
        EmitFormat::Rust => Ok(compile_lcnf_to_rust(
            decls,
            env,
            pipeline,
            RustEmitConfig {
                check_ir: true,
                ..Default::default()
            },
        )?),
        #[cfg(feature = "trust-ir-backend")]
        EmitFormat::Trustir => {
            use clean_compiler::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
            use clean_compiler::pass_manager::compile_lcnf_to_trust_ir;
            // ExternCalls lowering: every managed-runtime op becomes a call to
            // the Clean runtime, so the module is real, trust-cg-compilable code
            // (vs the opaque-dialect `Dialect` mode).
            let config = TrustIrConfig {
                module_name: "clean_module".to_string(),
                use_clean_dialect: true,
                runtime_lowering: RuntimeLowering::ExternCalls,
                // File-granular debug info, same as the `--emit obj` path.
                source_file: source_file.map(|p| p.display().to_string()),
                ..TrustIrConfig::default()
            };
            let module = compile_lcnf_to_trust_ir(decls, env, pipeline, &config)?;
            Ok(format!("{module}\n"))
        }
        #[cfg(feature = "trust-ir-backend")]
        EmitFormat::Obj => {
            // `--emit obj` is intercepted in `handle_compile_command` (it writes
            // a binary file), so it never reaches the text emitter.
            anyhow::bail!("internal error: `--emit obj` must be handled before `emit_decls`")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write_temp_lean(source: &str) -> (tempfile::TempDir, std::path::PathBuf) {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("compile_smoke.lean");
        std::fs::write(&file, source).expect("write fixture");
        (dir, file)
    }

    fn compile_fixture(source: &str, decl: &str, emit: EmitFormat) -> anyhow::Result<String> {
        let (_dir, file) = write_temp_lean(source);
        compile_to_string(CompileArgs {
            file: Some(file),
            decl: Some(decl.to_owned()),
            emit,
            opt_level: 0,
            output: None,
        })
    }

    #[test]
    fn compile_file_emit_c_for_simple_decl() {
        let output = compile_fixture("def demoId (x : Nat) : Nat := x", "demoId", EmitFormat::C)
            .expect("simple declaration should emit C");

        assert!(
            output.contains("l_demoId("),
            "C output should contain a named emitted function: {output}"
        );
    }

    #[test]
    fn compile_file_emits_only_selected_decl() {
        let source = r#"
def compileSelected (x : Nat) : Nat := x
def compileUnselected (x : Nat) : Nat := x
"#;

        let output = compile_fixture(source, "compileSelected", EmitFormat::C)
            .expect("selected declaration should emit C");

        assert!(
            output.contains("l_compileSelected("),
            "C output should contain selected declaration: {output}"
        );
        assert!(
            !output.contains("l_compileUnselected("),
            "C output should not emit unselected declaration: {output}"
        );
    }

    #[test]
    fn compile_file_emits_transitive_dependency_closure() {
        // `usesHelper` references the user decl `helper`. The whole-module
        // closure must emit BOTH bodies, not just the selected root.
        let source = r#"
def helper (n : Nat) : Nat := n
def usesHelper (x : Nat) : Nat := helper x
"#;
        let output = compile_fixture(source, "usesHelper", EmitFormat::C)
            .expect("decl with a user dependency should emit C");

        assert!(
            output.contains("l_usesHelper("),
            "C output should emit the selected root: {output}"
        );
        assert!(
            output.contains("l_helper("),
            "C output should emit the transitive dependency body: {output}"
        );
    }

    #[test]
    fn compile_file_arithmetic_caller_emits_and_calls_runtime_extern() {
        // `n + n` desugars through the `HAdd` typeclass: `HAdd.hAdd (HAdd.mk
        // ... Nat.add) n n`. The `Nat.add` handed to `HAdd.mk` is UNAPPLIED
        // (0 args, arity 2), so it must be emitted as a closure value
        // (`clean_alloc_closure((void*)l_Nat_add, 2, 0)`), NOT a 0-arg call
        // `l_Nat_add()` (the #16 function-as-value codegen bug). The body is
        // emitted and references the forward-declared runtime symbol via a
        // closure pointer, never DEFINING it.
        let output = compile_fixture(
            "def double (n : Nat) : Nat := n + n",
            "double",
            EmitFormat::C,
        )
        .expect("arithmetic caller must compile (extern boundary)");

        assert!(
            output.contains("l_double("),
            "C output should emit the arithmetic caller body: {output}"
        );
        // The unapplied Nat.add is a closure, not a buggy 0-arg call.
        assert!(
            output.contains("clean_alloc_closure((void*)l_Nat_add, 2, 0)"),
            "unapplied Nat.add must be an arity-2 closure value: {output}"
        );
        assert_eq!(
            output.matches("l_Nat_add()").count(),
            0,
            "must NOT emit a buggy 0-arg call of the 2-ary l_Nat_add: {output}"
        );
    }

    #[test]
    fn compile_file_explicit_nat_add_caller_emits_and_calls_extern() {
        // Directly naming the prelude `Nat.add` definition. `constant_to_decl`
        // returns Err (not Ok(None)) for it because it has a value; the extern
        // boundary must catch that Err and forward-declare, not propagate it.
        let output = compile_fixture(
            "def addsThings (x : Nat) : Nat := Nat.add x x",
            "addsThings",
            EmitFormat::C,
        )
        .expect("explicit Nat.add caller must compile (extern boundary catches Err)");

        assert!(
            output.contains("l_addsThings("),
            "C output should emit the caller body: {output}"
        );
        assert!(
            output.contains("l_Nat_add("),
            "C output should call the forward-declared runtime extern l_Nat_add: {output}"
        );
    }

    #[test]
    fn compile_file_emit_rust_for_simple_decl() {
        let output = compile_fixture(
            "def demoId (x : Nat) : Nat := x",
            "demoId",
            EmitFormat::Rust,
        )
        .expect("simple declaration should emit Rust");

        assert!(
            output.contains("pub unsafe fn l_demoId("),
            "Rust output should contain a named emitted function: {output}"
        );
    }

    #[test]
    fn compile_public_kernel_success_main_emit_c() {
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("crate is under repo-root/crates/clean-cli");
        let file = repo_root.join("demos/public/kernel_check_success.lean");

        let output = compile_to_string(CompileArgs {
            file: Some(file),
            decl: Some("main".to_owned()),
            emit: EmitFormat::C,
            opt_level: 0,
            output: None,
        })
        .expect("public kernel-check demo main should emit C");

        assert!(
            output.contains("l_main("),
            "C output should contain the selected main declaration: {output}"
        );
    }

    /// Build a two-file project: `Lib.lean` defines `double`, `Main.lean`
    /// imports it and uses `double 5`. Compiling `Main`'s `five` must resolve
    /// the intra-project `import Lib`, elaborate `Lib.lean` into the codegen
    /// environment, and emit BOTH bodies — closing the GAP 1 codegen import
    /// gap. Before the fix, `double` was never registered and the elaborator
    /// emitted an unbound `FVar` sentinel that crashed codegen.
    #[test]
    fn compile_resolves_intra_project_import_and_emits_dependency() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        std::fs::write(
            root.join("Lib.lean"),
            "def double (n : Nat) : Nat := n + n\n",
        )
        .expect("Lib.lean");
        let main = root.join("Main.lean");
        std::fs::write(&main, "import Lib\ndef five : Nat := double 5\n").expect("Main.lean");

        let output = compile_to_string(CompileArgs {
            file: Some(main),
            decl: Some("five".to_owned()),
            emit: EmitFormat::C,
            opt_level: 0,
            output: None,
        })
        .expect("intra-project import should resolve and compile");

        assert!(
            output.contains("l_five("),
            "C output should emit the selected root `five`: {output}"
        );
        assert!(
            output.contains("l_double("),
            "C output should emit the imported `double` from Lib.lean: {output}"
        );
    }

    /// Three-decl chain: `Lib.lean` defines `double` and `triple`, `Main.lean`
    /// uses both. The import resolver must register the whole imported module
    /// so the closure walk pulls in both helpers.
    #[test]
    fn compile_resolves_intra_project_import_three_decl_chain() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        std::fs::write(
            root.join("Lib.lean"),
            "def double (n : Nat) : Nat := n + n\ndef triple (n : Nat) : Nat := n + n + n\n",
        )
        .expect("Lib.lean");
        let main = root.join("Main.lean");
        std::fs::write(
            &main,
            "import Lib\ndef answer : Nat := double 5 + triple 4\n",
        )
        .expect("Main.lean");

        let output = compile_to_string(CompileArgs {
            file: Some(main),
            decl: Some("answer".to_owned()),
            emit: EmitFormat::C,
            opt_level: 0,
            output: None,
        })
        .expect("three-decl import chain should resolve and compile");

        assert!(
            output.contains("l_double("),
            "C output should emit imported `double`: {output}"
        );
        assert!(
            output.contains("l_triple("),
            "C output should emit imported `triple`: {output}"
        );
    }

    /// An import cycle (`A` imports `B`, `B` imports `A`) must be detected and
    /// reported cleanly, never panic or loop forever.
    #[test]
    fn compile_intra_project_import_cycle_errors_cleanly() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        std::fs::write(root.join("A.lean"), "import B\ndef a : Nat := 1\n").expect("A.lean");
        std::fs::write(root.join("B.lean"), "import A\ndef b : Nat := 2\n").expect("B.lean");

        let err = compile_to_string(CompileArgs {
            file: Some(root.join("A.lean")),
            decl: Some("a".to_owned()),
            emit: EmitFormat::C,
            opt_level: 0,
            output: None,
        })
        .expect_err("import cycle must error, not loop or panic");

        assert!(
            err.to_string().contains("import cycle detected"),
            "unexpected error for import cycle: {err:#}"
        );
    }

    /// Diamond import: `D` imports `B` and `C`, both of which import `A`. The
    /// shared dependency `A` must be elaborated exactly once (the `completed`
    /// dedup), so re-registering its constant does not raise an
    /// "already declared" error.
    #[test]
    fn compile_intra_project_diamond_dedups_shared_dependency() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        std::fs::write(root.join("A.lean"), "def base : Nat := 7\n").expect("A.lean");
        std::fs::write(root.join("B.lean"), "import A\ndef fromB : Nat := base\n").expect("B.lean");
        std::fs::write(root.join("C.lean"), "import A\ndef fromC : Nat := base\n").expect("C.lean");
        let d = root.join("D.lean");
        std::fs::write(&d, "import B\nimport C\ndef top : Nat := fromB + fromC\n").expect("D.lean");

        let output = compile_to_string(CompileArgs {
            file: Some(d),
            decl: Some("top".to_owned()),
            emit: EmitFormat::C,
            opt_level: 0,
            output: None,
        })
        .expect("diamond import must dedup the shared dependency and compile");

        assert!(
            output.contains("l_top("),
            "C output should emit the root `top`: {output}"
        );
        assert!(
            output.contains("l_base("),
            "C output should emit the shared transitive dependency `base`: {output}"
        );
    }

    /// An external-looking import (`Mathlib.X`) with no project-local `.lean`
    /// must NOT abort the compile: it resolves to `None` here and keeps its
    /// existing `.olean` flow (a no-op when no artifact is present). A decl
    /// that does not actually reference any external symbol still compiles.
    #[test]
    fn compile_external_import_is_not_resolved_as_local() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        let main = root.join("Main.lean");
        std::fs::write(
            &main,
            "import Mathlib.Data.Nat.Basic\ndef plain (n : Nat) : Nat := n\n",
        )
        .expect("Main.lean");

        let output = compile_to_string(CompileArgs {
            file: Some(main),
            decl: Some("plain".to_owned()),
            emit: EmitFormat::C,
            opt_level: 0,
            output: None,
        })
        .expect("external import with no local .lean must not abort the compile");

        assert!(
            output.contains("l_plain("),
            "C output should emit the local decl: {output}"
        );
    }

    #[test]
    fn compile_file_unknown_decl_errors() {
        let err = compile_fixture("def demoId (x : Nat) : Nat := x", "missing", EmitFormat::C)
            .expect_err("unknown declaration must fail");

        assert!(
            err.to_string().contains("was not found after elaboration"),
            "unexpected error for missing declaration: {err:#}"
        );
    }

    #[cfg(feature = "trust-ir-backend")]
    #[test]
    fn compile_file_emit_trustir_for_simple_decl() {
        let output = compile_fixture(
            "def demoId (x : Nat) : Nat := x",
            "demoId",
            EmitFormat::Trustir,
        )
        .expect("simple declaration should emit trust-ir");

        assert!(
            output.contains("module \"clean_module\""),
            "trust-ir output should be a textual module: {output}"
        );
        assert!(
            output.contains("@demoId("),
            "trust-ir output should contain the lowered user function: {output}"
        );
    }

    #[cfg(feature = "trust-ir-backend")]
    #[test]
    fn compile_emit_obj_without_output_errors() {
        let (_dir, file) = write_temp_lean("def demoId (x : Nat) : Nat := x");
        let err = handle_compile_command(CompileArgs {
            file: Some(file),
            decl: Some("demoId".to_owned()),
            emit: EmitFormat::Obj,
            opt_level: 0,
            output: None,
        })
        .expect_err("`--emit obj` without `-o` must fail");
        assert!(
            err.to_string().contains("requires an output path"),
            "unexpected error for missing -o: {err:#}"
        );
    }

    #[cfg(feature = "trust-ir-backend")]
    #[test]
    fn compile_file_emit_obj_produces_object() {
        // Needs the trust-cg backend binary; skip cleanly where it is absent
        // (e.g. CI without the sibling repo built).
        if find_trust_cg().is_none() {
            eprintln!("skipping compile_file_emit_obj_produces_object: trust-cg not found");
            return;
        }
        let (dir, file) = write_temp_lean("def demoId (x : Nat) : Nat := x");
        let obj = dir.path().join("demoId.o");
        handle_compile_command(CompileArgs {
            file: Some(file),
            decl: Some("demoId".to_owned()),
            emit: EmitFormat::Obj,
            opt_level: 0,
            output: Some(obj.clone()),
        })
        .expect("`--emit obj` should produce a native object");
        let meta = std::fs::metadata(&obj).expect("object file should exist");
        assert!(meta.len() > 0, "emitted object file should be non-empty");
    }
}
