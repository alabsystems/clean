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

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use anyhow::{anyhow, Context};
use clean_compiler::cli::{CompileArgs, EmitFormat};
use clean_compiler::emit_c::CEmitConfig;
use clean_compiler::emit_rust::RustEmitConfig;
use clean_compiler::mangle::mangle_name;
use clean_compiler::pass_manager::{compile_lcnf_decls_for, PipelineConfig};
use clean_compiler::{
    constant_to_decl_with_meaning, BoxingConfig, CompilerError, Decl, OptConfig, RCConfig,
};
use clean_elab::module_driver::validate_decl_read_only;
use clean_elab::{
    elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context, ElabResult,
    FileContext, RegistrationWarning,
};
use clean_kernel::{Environment, Expr, ExprVisitor, LevelVec, Name, TypeChecker};

use crate::native_build::is_primitive_denylisted;
use crate::native_eager_io::prepare_native_constant;
use crate::native_ffi_audit::{
    refuse_compiled_before_binding, refuse_ffi_root, route_ffi_dep, CodeMeaning, FfiRoute,
};
use crate::native_opaque_audit::refuse_unfaithful_body;
use clean_compiler::ffi_bridge::ImplementedByMap;

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

pub fn compile_to_string(args: CompileArgs) -> anyhow::Result<String> {
    compile_to_string_with_decl_type(args).map(|(c, _)| c)
}

/// Emit the requested declaration AND report the elaborated type it was
/// declared at.
///
/// The native entry driver needs both. Arity it can read off the emitted C
/// prototype, but the *return shape* is invisible there: `IO Unit` and
/// `IO UInt32` both lower to `clean_obj* l_main(...)`, and that distinction is
/// exactly what decides whether the process exit status is a hardcoded `0` or
/// the value the entry returned. So the driver reads it from the Lean type,
/// which is the only place it survives lowering.
///
/// This costs no extra elaboration: [`select_lcnf_decl`] already returns the
/// elaborated environment it built, so the type is a lookup on the way out.
pub(crate) fn compile_to_string_with_decl_type(
    args: CompileArgs,
) -> anyhow::Result<(String, Option<Expr>)> {
    let (lcnf_decls, compile_env, pipeline) = select_lcnf_decl(&args)?;
    let selected_name = args
        .decl
        .as_deref()
        .map(parse_compile_decl_name)
        .transpose()?;
    let decl_type = selected_name
        .as_ref()
        .and_then(|name| compile_env.get_const(name))
        .map(|info| info.type_.clone());
    let emitted = emit_decls(
        &lcnf_decls,
        &compile_env,
        args.emit,
        &pipeline,
        args.file.as_deref(),
        CodeMeaning::LeanCompiled,
    )?;
    Ok((emitted, decl_type))
}

pub(crate) fn parse_compile_decl_name(source: &str) -> anyhow::Result<Name> {
    let name = clean_parser::parse_name(source).with_context(|| {
        format!("invalid declaration name `{source}`; --decl requires one Lean identifier")
    })?;
    if name.is_relative_constructor() || name.is_anonymous() {
        anyhow::bail!(
            "invalid declaration name `{source}`; --decl requires a declaration identity"
        );
    }
    Ok(name
        .qualify_under(&clean_parser::SurfaceName::default())
        .into_name())
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
/// and retain prelude fallback for runtime shims. A SOURCE definition whose
/// lowering or probe fails is refused with its original cause: it cannot be
/// satisfied by a prelude shim. The root also keeps hard-error behavior.
pub fn select_lcnf_decl(
    args: &CompileArgs,
) -> anyhow::Result<(Vec<Decl>, Environment, PipelineConfig)> {
    select_lcnf_decl_denying(args, &is_primitive_denylisted)
}

/// [`select_lcnf_decl`] with the PRIMITIVE_DENYLIST predicate (condition 1)
/// supplied by the caller. Production passes [`is_primitive_denylisted`]
/// verbatim; the WS6.3 census test passes that predicate minus one symbol, to
/// show by the emitted symbol set that dropping a shim puts its source body
/// back into the build.
pub(crate) fn select_lcnf_decl_denying(
    args: &CompileArgs,
    denylisted: &dyn Fn(&str) -> bool,
) -> anyhow::Result<(Vec<Decl>, Environment, PipelineConfig)> {
    select_lcnf_decl_with_meaning(args, denylisted, CodeMeaning::LeanCompiled)
}

/// [`select_lcnf_decl_denying`] for a build that promises `meaning`
/// (`native_ffi_audit::CodeMeaning`): `clean extract` selects with
/// [`CodeMeaning::KernelValue`] (`crate::select_lcnf_decl_kernel_meaning`).
pub(crate) fn select_lcnf_decl_with_meaning(
    args: &CompileArgs,
    denylisted: &dyn Fn(&str) -> bool,
    meaning: CodeMeaning,
) -> anyhow::Result<(Vec<Decl>, Environment, PipelineConfig)> {
    select_lcnf_decl_routed(args, denylisted, &|_| DepRoute::Compile, meaning)
        .map(|(decls, env, pipeline, _imported)| (decls, env, pipeline))
}

/// Where the dependency walk sends one referenced constant that survived the
/// #14 boundary checks (WS6.8). Without `--link-artifact` every such constant
/// is [`DepRoute::Compile`], which is the walk as it always was.
// `Import`/`Refuse` are constructed only by `compile_to_trustir_bin`, which
// exists only with the trust-ir backend; without it every route is `Compile`.
#[cfg_attr(not(feature = "trust-ir-backend"), allow(dead_code))]
pub(crate) enum DepRoute {
    /// Compile it into this module and keep walking its value.
    Compile,
    /// Exactly one linked artifact defines it: lower it (so every call site
    /// is shaped against its real signature) but emit only a declaration.
    /// Its value is still walked, and each dependency found there is routed
    /// on its own (see the walk in [`select_lcnf_decl_routed`]).
    Import,
    /// Refuse the compile with this reason (a symbol two artifacts define).
    Refuse(String),
}

/// [`select_lcnf_decl_denying`] with a per-dependency [`DepRoute`], also
/// returning the dependencies routed to [`DepRoute::Import`]. Their `Decl`s
/// are in the returned slice (the emitter declares them, never defines them).
pub(crate) fn select_lcnf_decl_routed(
    args: &CompileArgs,
    denylisted: &dyn Fn(&str) -> bool,
    route: &dyn Fn(&Name) -> DepRoute,
    meaning: CodeMeaning,
) -> anyhow::Result<(Vec<Decl>, Environment, PipelineConfig, Vec<Name>)> {
    let file = args
        .file
        .as_deref()
        .ok_or_else(|| anyhow!("`clean compile` requires a source file"))?;
    let decl_name = args
        .decl
        .as_deref()
        .ok_or_else(|| anyhow!("`clean compile` requires `--decl <NAME>`"))?;

    let root_name = parse_compile_decl_name(decl_name)?;
    let (env, source_opaques, source_decls) = elaborate_file_with_inventory(file)?;
    select_in_environment_ordered(
        env,
        &source_opaques,
        &root_name,
        args.opt_level,
        denylisted,
        route,
        SelectionPolicy {
            meaning,
            closure: None,
            source_decls: Some(&source_decls),
        },
    )
}

/// The single native declaration/dependency selection implementation. Both
/// Clean source elaboration and the owned external Lean handoff use every
/// eligibility, implemented_by, opaque, IO and FFI check below.
pub(crate) fn select_in_environment(
    env: Environment,
    source_opaques: &HashSet<Name>,
    root_name: &Name,
    opt_level: u8,
    denylisted: &dyn Fn(&str) -> bool,
    route: &dyn Fn(&Name) -> DepRoute,
    meaning: CodeMeaning,
) -> anyhow::Result<(Vec<Decl>, Environment, PipelineConfig, Vec<Name>)> {
    select_in_environment_ordered(
        env,
        source_opaques,
        root_name,
        opt_level,
        denylisted,
        route,
        SelectionPolicy {
            meaning,
            closure: None,
            source_decls: None,
        },
    )
}

pub(crate) fn select_in_environment_in_runtime_closure(
    env: Environment,
    source_opaques: &HashSet<Name>,
    root_name: &Name,
    opt_level: u8,
    denylisted: &dyn Fn(&str) -> bool,
    route: &dyn Fn(&Name) -> DepRoute,
    closure: &clean_compiler::RuntimeBindingClosure,
) -> anyhow::Result<(Vec<Decl>, Environment, PipelineConfig, Vec<Name>)> {
    select_in_environment_ordered(
        env,
        source_opaques,
        root_name,
        opt_level,
        denylisted,
        route,
        SelectionPolicy {
            meaning: CodeMeaning::LeanCompiled,
            closure: Some(closure),
            source_decls: None,
        },
    )
}

#[derive(Clone, Copy)]
struct SelectionPolicy<'a> {
    meaning: CodeMeaning,
    closure: Option<&'a clean_compiler::RuntimeBindingClosure>,
    source_decls: Option<&'a HashSet<Name>>,
}

fn lower_selected_constant(
    env: &Environment,
    info: &clean_kernel::ConstantInfo,
    policy: SelectionPolicy<'_>,
) -> Result<Option<Decl>, CompilerError> {
    match policy.closure {
        Some(closure) => clean_compiler::constant_to_decl_in_runtime_closure(env, info, closure),
        None => constant_to_decl_with_meaning(env, info, policy.meaning),
    }
}

fn compile_selected_decls(
    decls: &[Decl],
    env: &Environment,
    pipeline: &PipelineConfig,
    meaning: CodeMeaning,
    closure: Option<&clean_compiler::RuntimeBindingClosure>,
) -> Result<
    clean_compiler::pass_manager::PipelineArtifacts,
    clean_compiler::pass_manager::PipelineError,
> {
    match closure {
        Some(closure) => clean_compiler::pass_manager::compile_lcnf_decls_in_runtime_closure(
            decls, env, pipeline, closure,
        ),
        None => compile_lcnf_decls_for(decls, env, pipeline, meaning),
    }
}

fn select_in_environment_ordered(
    env: Environment,
    source_opaques: &HashSet<Name>,
    root_name: &Name,
    opt_level: u8,
    denylisted: &dyn Fn(&str) -> bool,
    route: &dyn Fn(&Name) -> DepRoute,
    policy: SelectionPolicy<'_>,
) -> anyhow::Result<(Vec<Decl>, Environment, PipelineConfig, Vec<Name>)> {
    let meaning = policy.meaning;
    let decl_name = root_name.to_string();
    let root_info = env
        .get_const(root_name)
        .ok_or_else(|| anyhow!("declaration `{decl_name}` was not found after elaboration"))?;
    // Code added before an `attribute [implemented_by]` command that rebinds
    // what it reaches runs whatever Lean's inliner left it: no root of this
    // environment is compiled (`native_ffi_audit`).
    // A kernel-value build substitutes nothing, so the record does not apply.
    if meaning == CodeMeaning::LeanCompiled && policy.closure.is_none() {
        refuse_compiled_before_binding(root_name, &env)?;
    }
    // A placeholder `opaque` compiles to a constant and prints a wrong answer
    // at exit 0 (`native_opaque_audit`); refuse it before it is lowered.
    refuse_unfaithful_body(root_info, root_name, source_opaques)?;
    // Lean compiles neither an `@[implemented_by]` declaration nor the body of
    // an `@[extern]` one (`native_ffi_audit`).
    refuse_ffi_root(&env, root_info, meaning)?;
    // The eager IO model runs an action where it is EVALUATED; rewrite the value
    // so that is where Lean runs it, or refuse (`native_eager_io`) -- and refuse
    // a recursion that reads fields of an argument it generalized
    // (`native_rec_split_audit`). Monad inlining reduces in an environment
    // where no constant with a compiler attribute unfolds
    // (`native_monad_inline::inlining_env`).
    let inline_env = crate::native_monad_inline::inlining_env(&env);
    let root_info = &prepare_native_constant(&env, &inline_env, root_info, meaning)?;
    let root_decl = lower_selected_constant(&env, root_info, policy)
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
    let mut imported: Vec<Name> = Vec::new();

    // Worklist of value expressions still to scan for dependencies. We scan the
    // root's value, then each compilable dependency's value, transitively.
    let mut worklist: Vec<Name> = clean_compiler::resolve_csimp_dependencies(
        &env,
        root_name,
        ConstDepCollector::collect(
            root_info
                .value
                .as_ref()
                .expect("constant_to_decl returned Some, so the root has a value"),
        ),
        meaning,
    )?;

    let pipeline = pipeline_config_from_opt_level(opt_level);
    // Every `@[implemented_by]` binding, read once for the walk below.
    let implemented_by = ImplementedByMap::from_env(&env);

    // Silence the default panic hook for the duration of the dependency-probe
    // loop: a candidate dep that trips a `debug_assert!` during the isolated
    // probe is caught and dropped to extern (see below), so its panic trace is
    // expected noise, not a failure. Restored immediately after the loop.
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    let mut refusal = None;
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
        if denylisted(&mangle_name(&dep_name)) {
            continue;
        }

        // (a0) FFI ATTRIBUTES (`native_ffi_audit`). Lean never runs the body of
        // an `@[implemented_by f]` declaration -- every call runs `f`, which
        // `to_lcnf` already substituted at each reference -- so walk `f`
        // instead and never lower this body. An `@[extern]` declaration with a
        // body is refused: Lean calls its C symbol, never the body.
        match route_ffi_dep(&env, &implemented_by, dep_info, root_name, meaning) {
            Ok(FfiRoute::Ordinary) => {}
            Ok(FfiRoute::Redirect(target)) => {
                worklist.push(target);
                continue;
            }
            Err(err) => {
                refusal = Some(anyhow::Error::from(err));
                break;
            }
        }

        // (a') RUNTIME FIDELITY. A prelude `opaque` whose value is a type-correct
        // stand-in (the kernel means it through a native reducer) lowers fine
        // and computes a constant: `(7 : Int) / 2` printed `0` at exit 0. Refuse
        // the build instead of compiling it (`native_opaque_audit`). Checked
        // BEFORE (b) because a placeholder body is exactly the kind that DOES
        // lower.
        if let Err(err) = refuse_unfaithful_body(dep_info, root_name, source_opaques) {
            refusal = Some(anyhow::Error::from(err));
            break;
        }
        // (a'') EAGER IO AND RECURSION SHAPE. A dependency's actions run where
        // they are evaluated and its recursions are compiled exactly like the
        // root's: rewrite or refuse it the same way.
        let dep_info = &match prepare_native_constant(&env, &inline_env, dep_info, meaning) {
            Ok(prepared) => prepared,
            Err(err) => {
                refusal = Some(anyhow::Error::from(err));
                break;
            }
        };

        // (a''') LINKED ARTIFACTS (WS6.8). A symbol two artifacts define is
        // ambiguous and refuses the build; one exactly one artifact defines is
        // imported, which needs the checks below to have a signature to
        // compare with the far one.
        let dep_route = route(&dep_name);
        if let DepRoute::Refuse(why) = dep_route {
            refusal = Some(anyhow!(why));
            break;
        }
        let importing = matches!(dep_route, DepRoute::Import);

        // (b) A const that does not lower to a compilable `Decl` — `Ok(None)`
        // (axiom/opaque/ctor/noncomputable) or `Err(_)` (value present but
        // lowering failed, e.g. `List.length`) — is an extern. Drop and continue;
        // crucially do NOT propagate the `Err`. The exception: a lowering that
        // met an `@[implemented_by]` it cannot substitute (a cycle, an absent
        // or `unsafe` end), or the order refusal (which the root check above
        // takes first). Dropped, the dependency became an undefined symbol
        // and the build failed at link time without a name. A link whose
        // implementation has another type here (an imported binding whose
        // target resolves to a resident declaration) is named the same way.
        let dep_decl = match lower_selected_constant(&env, dep_info, policy) {
            Ok(Some(dep_decl)) => dep_decl,
            Err(
                err @ (CompilerError::ImplementedByCycle { .. }
                | CompilerError::ImplementedByMissingTarget { .. }
                | CompilerError::ImplementedByUnsafeTarget { .. }
                | CompilerError::ImplementedByTypeMismatch { .. }
                | CompilerError::ImplementedByOrder { .. }
                | CompilerError::RuntimeBindingClosure { .. }
                | CompilerError::RuntimeBindingOrder { .. }),
            ) => {
                refusal = Some(
                    anyhow::Error::from(err)
                        .context(format!("dependency `{dep_name}` of `{root_name}`")),
                );
                break;
            }
            Err(err)
                if policy
                    .source_decls
                    .is_some_and(|names| names.contains(&dep_name)) =>
            {
                refusal = Some(anyhow::Error::from(err).context(format!(
                    "cannot lower source dependency `{dep_name}` of `{root_name}`"
                )));
                break;
            }
            Ok(None) | Err(_) => {
                if importing {
                    refusal = Some(unlowerable_import(&dep_name));
                    break;
                }
                continue;
            }
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
            compile_selected_decls(
                std::slice::from_ref(&dep_decl),
                &env,
                &pipeline,
                meaning,
                policy.closure,
            )
        }));
        if let Ok(Err(
            error @ clean_compiler::pass_manager::PipelineError::Compiler(
                CompilerError::RuntimeBindingClosure { .. }
                | CompilerError::RuntimeBindingOrder { .. }
                | CompilerError::ImplementedByOrder { .. },
            ),
        )) = &probe
        {
            refusal = Some(anyhow!(
                "checked runtime closure refused dependency `{dep_name}`: {error}"
            ));
            break;
        }
        if !matches!(probe, Ok(Ok(_))) {
            // A source body has no prelude shim to fall back to. Keep the
            // original refusal at the production caller instead of replacing
            // it with a missing-extern error at link-demand checking.
            if policy
                .source_decls
                .is_some_and(|names| names.contains(&dep_name))
            {
                let cause = match probe {
                    Ok(Err(err)) => err.to_string(),
                    Err(_) => "compiler probe panicked".to_string(),
                    Ok(Ok(_)) => unreachable!("probe failed above"),
                };
                refusal = Some(anyhow!(
                    "cannot compile source dependency `{dep_name}` of `{root_name}`: {cause}"
                ));
                break;
            }
            if importing {
                refusal = Some(unlowerable_import(&dep_name));
                break;
            }
            continue;
        }

        // Keep walking the dependency's value — an imported one's too. Its
        // own dependencies are classified one by one by the same route, so
        // whatever the artifact defines is imported, never re-embedded. The
        // walk itself is load-bearing: `resolve_instances` (`-O1`/`-O2`)
        // rewrites a client's `x + y` through an instance it reaches (say an
        // IMPORTED `instHAddUInt64`) into a direct `UInt64.add x y`, and the
        // boxing pass keeps that call's operands scalar only when the
        // primitive is in the slice — which it is only by being reached
        // through the instance's value. Unwalked, the client's call sites
        // are boxed and the native arithmetic arm refuses them (measured:
        // "arithmetic primitive UInt64.add produces U64 but the declaration
        // expects Ptr"). The slice is then exactly the flattening closure
        // with every artifact-defined body replaced by a declaration.
        if let Some(value) = &dep_info.value {
            match clean_compiler::resolve_csimp_dependencies(
                &env,
                &dep_name,
                ConstDepCollector::collect(value),
                meaning,
            ) {
                Ok(dependencies) => worklist.extend(dependencies),
                Err(error) => {
                    refusal = Some(anyhow::Error::from(error));
                    break;
                }
            }
        }
        // Imported dependency: lowered for its call shape and declared (not
        // defined) by the emitter.
        if importing {
            imported.push(dep_name.clone());
        }
        decls.push(dep_decl);
    }

    std::panic::set_hook(prev_hook);
    if let Some(err) = refusal {
        return Err(err);
    }

    // Phase 0 #1: thread the real elaborated environment through to IR lowering
    // (so `to_ir`'s `build_ctor_env` sees the prelude constructors), together with
    // the transitive compilable closure. `env` is only borrowed by the dep-walk
    // above, so it is still owned here.
    Ok((decls, env, pipeline, imported))
}

/// A dependency a linked artifact defines, which this compile cannot lower:
/// with no client-side signature there is no call shape to hold to the far
/// one, and falling back to the boxed extern would call the artifact's
/// definition at a signature it does not have.
fn unlowerable_import(name: &Name) -> anyhow::Error {
    anyhow!(
        "`{name}` is defined by a linked artifact, but this compile cannot lower it, so \
         its call shape cannot be checked against the artifact's signature; refusing \
         rather than calling it through the boxed extern fallback"
    )
}

/// `--emit trustir-bin`: write the LINKABLE trust-ir artifact.
///
/// Until this existed Clean could not produce a trust-ir file at all:
/// `--emit trustir` renders text to stdout, and the only binary writer,
/// `serialize_tmbc`, went to a tempfile that `--emit obj` deleted after handing
/// it to trust-cg. So `Module.imports` had no subject — nothing on disk for a
/// dependent module to cite or for `trust-ir validate --link` to read.
///
/// Two deliberate choices:
///
/// * **Plain module bytes, not the `.tmbc` container.** `deserialize_module`
///   refuses tMBC's `b"tMBC"` + LE-`u32` header, and more importantly
///   `Module::stable_digest` is computed over the MODULE — so if the file
///   carried a container, the bytes a consumer reads and the bytes identity is
///   taken over would be different things, and the digest in an import row
///   would be uncheckable from the artifact. `--emit obj` keeps the container,
///   because that is trust-cg's input format.
/// * **The module is named after the output stem**, not the hardcoded
///   `"clean_module"` every other path uses. Two artifacts that share a name
///   are still told apart by their digests, but a diagnostic that prints one
///   name for two crates is useless. This is scoped to the NEW emitter on
///   purpose: changing the name on the text or object paths would move the
///   digest of artifacts that already exist.
///
/// The stable digest is reported on stderr, so whoever records an import row
/// can compare it with the digest the producer will independently measure
/// rather than trusting either in isolation.
///
/// # `--link-artifact` (WS6.8)
///
/// Each named artifact is decoded through the canonical reader
/// (`LinkedArtifact::decode`; a `.tmbc` container is refused). The dependency
/// walk then routes every constant whose link symbol EXACTLY ONE artifact
/// defines to an import: it is lowered for its call shape, declared at the
/// artifact's signature (the emitter refuses the compile when the two
/// disagree — `CallShapeDisagreesWithFarSignature`, never a re-box), and its
/// body is not compiled. A symbol two artifacts define refuses the compile
/// (`SymbolAmbiguous`). After emission the import producer
/// (`link_imported_modules_for_cli`) writes one `Module.imports` row per
/// artifact used, digest measured over the decode, and inherits a far proof
/// only when the far certificate's comparand is this compile's own
/// elaboration of the symbol; it ends with `validate_linked_module` against
/// the supplied artifacts, so nothing is written a consumer would not
/// re-earn. Without the flag the closure is compiled into one module, as
/// before.
#[cfg(feature = "trust-ir-backend")]
pub fn compile_to_trustir_bin(args: &CompileArgs) -> anyhow::Result<()> {
    use clean_compiler::emit_trust_ir::{
        module_stable_digest_string, serialize_module_bytes, RuntimeLowering, TrustIrConfig,
    };
    use clean_compiler::emit_trust_ir_link::{
        importable_symbols, link_imported_modules_for_cli_in_environment, link_symbol,
        ArtifactLookup, LinkRefusal, LinkedArtifact,
    };
    use clean_compiler::pass_manager::compile_lcnf_to_trust_ir;

    let out = args
        .output
        .as_deref()
        .ok_or_else(|| anyhow!("`--emit trustir-bin` requires an output path (`-o <PATH>`)"))?;
    let mut linked: Vec<LinkedArtifact> = Vec::with_capacity(args.link_artifact.len());
    let mut digests = std::collections::BTreeSet::new();
    for path in &args.link_artifact {
        let bytes = std::fs::read(path)
            .with_context(|| format!("failed to read linked artifact {}", path.display()))?;
        let artifact =
            LinkedArtifact::decode(path.display().to_string(), &bytes).map_err(|e| anyhow!(e))?;
        // One module named twice (the same file, or a byte-identical copy
        // reached by two paths) is ONE definer of each of its symbols, not
        // two: identity is the digest, never the path. Without this, every
        // symbol it defines would refuse as `SymbolAmbiguous`.
        if digests.insert(module_stable_digest_string(&artifact.module)?) {
            linked.push(artifact);
        }
    }
    // One table decides both the walk and the emitter, so the two cannot
    // disagree about which artifact defines what.
    let table = importable_symbols(&linked);
    let route = |name: &Name| {
        let symbol = link_symbol(name);
        match table.get(&symbol) {
            Some(ArtifactLookup::Import(_)) => DepRoute::Import,
            Some(ArtifactLookup::Ambiguous) => DepRoute::Refuse(format!(
                "`{name}`: {} (symbol `{symbol}`)",
                LinkRefusal::SymbolAmbiguous
            )),
            None => DepRoute::Compile,
        }
    };
    let (lcnf_decls, compile_env, pipeline, imported) = select_lcnf_decl_routed(
        args,
        &is_primitive_denylisted,
        &route,
        CodeMeaning::LeanCompiled,
    )?;
    if let Some(root) = lcnf_decls.first() {
        let symbol = link_symbol(&root.name);
        if table.contains_key(&symbol) {
            anyhow::bail!(
                "the compile root `{}` (symbol `{symbol}`) is defined by a linked artifact; \
                 refusing to write a second definition of it",
                root.name
            );
        }
    }
    // The emitter's import table: every symbol exactly one artifact defines.
    // It declares (never defines) each function of its slice named there —
    // the imported constants AND the auxiliary functions the client's own
    // pipeline generates from them (boxed-entry versions, hoisted constants,
    // arithmetic wrappers), which would otherwise be second definitions of
    // symbols the artifact already defines.
    let imported_callees: std::collections::BTreeMap<_, _> = table
        .into_iter()
        .filter_map(|(symbol, row)| match row {
            ArtifactLookup::Import(far) => Some((symbol, far)),
            ArtifactLookup::Ambiguous => None,
        })
        .collect();
    // The CLIENT's elaboration of each imported constant — what this compile
    // means by it, and what a far proof must be about to be inherited.
    let client_sources: std::collections::BTreeMap<String, Expr> = imported
        .iter()
        .filter_map(|name| {
            let value = compile_env.get_const(name)?.value.clone()?;
            Some((link_symbol(name), value))
        })
        .collect();
    let module_name = out
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty())
        .unwrap_or("clean_module")
        .to_string();
    let config = TrustIrConfig {
        module_name,
        use_clean_dialect: true,
        // ExternCalls: real runtime calls, i.e. the same lowering `--emit obj`
        // hands to trust-cg. A linkable artifact and a compilable one must not
        // be two different lowerings.
        runtime_lowering: RuntimeLowering::ExternCalls,
        source_file: args.file.as_ref().map(|p| p.display().to_string()),
        imported_callees,
        ..TrustIrConfig::default()
    };
    let mut module = compile_lcnf_to_trust_ir(&lcnf_decls, &compile_env, &pipeline, &config)?;
    // Every declaration the emitter wrote from the import table is wanted;
    // only a source constant carries a client source (an auxiliary function
    // has no kernel definition, so it is an identity row at most).
    let wanted: Vec<(String, Option<Expr>)> = module
        .functions
        .iter()
        .filter(|f| f.is_declaration() && config.imported_callees.contains_key(&f.name))
        .map(|f| (f.name.clone(), client_sources.get(&f.name).cloned()))
        .collect();
    // Refuses (and nothing is written) when an artifact cannot be recorded,
    // when an imported declaration got no import row — the module would call
    // a symbol nothing binds — or when `validate_linked_module` refuses.
    let link_lines =
        link_imported_modules_for_cli_in_environment(&mut module, &linked, &wanted, &compile_env)
            .map_err(|e| anyhow!("refusing to write {}: {e}", out.display()))?;
    let bytes = serialize_module_bytes(&module)?;
    let digest = module_stable_digest_string(&module)?;
    std::fs::write(out, &bytes)
        .with_context(|| format!("failed to write trust-ir module to {}", out.display()))?;
    eprintln!(
        "wrote {} ({} bytes), module {:?}, stable digest {}",
        out.display(),
        bytes.len(),
        module.name,
        digest
    );
    for line in &link_lines {
        eprintln!("  {line}");
    }
    Ok(())
}

/// Compile the selected declaration to a native object file by lowering to
/// trust-ir and invoking the `trust-cg` backend. Requires `-o <path>` and a
/// `trust-cg` binary (located via `CLEAN_TRUST_CG_BIN` or `PATH`).
#[cfg(feature = "trust-ir-backend")]
pub fn compile_to_object(args: &CompileArgs) -> anyhow::Result<()> {
    use crate::native_trustcg::TrustCg;

    let out = args
        .output
        .as_deref()
        .ok_or_else(|| anyhow!("`--emit obj` requires an output path (`-o <PATH>`)"))?;
    let trust_cg = find_trust_cg()?.ok_or_else(|| {
        anyhow!(
            "trust-cg binary not found; set CLEAN_TRUST_CG_BIN or add `trust-cg` to PATH \
             (build it in the sibling trust-cg repo)"
        )
    })?;
    let target = host_trust_cg_target()?;
    let compiler = TrustCg::from_path(trust_cg)?;

    let (lcnf_decls, compile_env, pipeline) = select_lcnf_decl(args)?;
    write_selected_object(
        &lcnf_decls,
        &compile_env,
        &pipeline,
        &object_emit_config(args),
        (&compiler, target),
        out,
        None,
    )
}

/// The external source handoff uses the same object checks, licensing and
/// backend invocation as the ordinary source command above.
#[cfg(feature = "trust-ir-backend")]
pub(crate) fn emit_selected_object(
    decls: &[Decl],
    env: &Environment,
    pipeline: &PipelineConfig,
    source_file: Option<&Path>,
    out: &Path,
    closure: Option<&clean_compiler::RuntimeBindingClosure>,
) -> anyhow::Result<()> {
    emit_selected_object_with_check(decls, env, pipeline, source_file, out, closure, |_| Ok(()))
}

/// Additional consumer checks inspect the exact module subsequently checked,
/// licensed and compiled. No caller-supplied artifact can inherit that check.
#[cfg(feature = "trust-ir-backend")]
pub(crate) fn emit_selected_object_with_check(
    decls: &[Decl],
    env: &Environment,
    pipeline: &PipelineConfig,
    source_file: Option<&Path>,
    out: &Path,
    closure: Option<&clean_compiler::RuntimeBindingClosure>,
    check: impl FnOnce(&clean_compiler::emit_trust_ir_lane::Module) -> anyhow::Result<()>,
) -> anyhow::Result<()> {
    use crate::native_trustcg::TrustCg;
    let trust_cg = find_trust_cg()?.ok_or_else(|| {
        anyhow!("trust-cg binary not found; set CLEAN_TRUST_CG_BIN or add `trust-cg` to PATH")
    })?;
    let compiler = TrustCg::from_path(trust_cg)?;
    write_selected_object_with_check(
        decls,
        env,
        pipeline,
        &object_emit_config_from_source(source_file),
        (&compiler, host_trust_cg_target()?),
        out,
        closure,
        check,
    )
}

#[cfg(feature = "trust-ir-backend")]
fn write_selected_object(
    decls: &[Decl],
    env: &Environment,
    pipeline: &PipelineConfig,
    config: &clean_compiler::emit_trust_ir::TrustIrConfig,
    backend: (&dyn crate::native_trustcg::ObjectBackend, &str),
    out: &Path,
    closure: Option<&clean_compiler::RuntimeBindingClosure>,
) -> anyhow::Result<()> {
    write_selected_object_with_check(decls, env, pipeline, config, backend, out, closure, |_| {
        Ok(())
    })
}

#[cfg(feature = "trust-ir-backend")]
fn write_selected_object_with_check(
    decls: &[Decl],
    env: &Environment,
    pipeline: &PipelineConfig,
    config: &clean_compiler::emit_trust_ir::TrustIrConfig,
    backend: (&dyn crate::native_trustcg::ObjectBackend, &str),
    out: &Path,
    closure: Option<&clean_compiler::RuntimeBindingClosure>,
    check: impl FnOnce(&clean_compiler::emit_trust_ir_lane::Module) -> anyhow::Result<()>,
) -> anyhow::Result<()> {
    use crate::native_trustcg::checks::object_self_checks_for_env;
    use clean_compiler::pass_manager::compile_lcnf_to_trust_ir;
    let mut module = match closure {
        Some(closure) => clean_compiler::pass_manager::compile_lcnf_to_trust_ir_in_runtime_closure(
            decls, env, pipeline, config, closure,
        )?,
        None => compile_lcnf_to_trust_ir(decls, env, pipeline, config)?,
    };
    let (compiler, target) = backend;
    let checked = object_self_checks_for_env(env, &module)?;
    check(&module)?;
    let census = checked.license(&mut module)?;
    let scratch = tempfile::tempdir().context("failed to create object build directory")?;
    let object = compiler.compile_object(&module, target, scratch.path())?;
    std::fs::copy(&object, out)
        .with_context(|| format!("failed to write native object to {}", out.display()))?;
    eprintln!(
        "wrote {}; {} bodies use clean-compiler-unvalidated (no binary proof claim)",
        out.display(),
        census.unvalidated
    );
    Ok(())
}

/// The trust-ir emission config of `--emit obj`: the one lowering an object
/// is compiled from. Shared with the WS6.14 battery census so the census
/// measures exactly the module `clean compile --emit obj` hands trust-cg.
#[cfg(feature = "trust-ir-backend")]
pub(crate) fn object_emit_config(
    args: &CompileArgs,
) -> clean_compiler::emit_trust_ir::TrustIrConfig {
    object_emit_config_from_source(args.file.as_deref())
}

#[cfg(feature = "trust-ir-backend")]
fn object_emit_config_from_source(
    source_file: Option<&Path>,
) -> clean_compiler::emit_trust_ir::TrustIrConfig {
    use clean_compiler::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    TrustIrConfig {
        module_name: "clean_module".to_string(),
        use_clean_dialect: true,
        // ExternCalls: real runtime calls, i.e. trust-cg-compilable native code.
        runtime_lowering: RuntimeLowering::ExternCalls,
        // File-granular debug info: the emitted instructions carry spans
        // pointing at the compiled source file.
        source_file: source_file.map(|p| p.display().to_string()),
        ..TrustIrConfig::default()
    }
}

/// Locate `trust-cg`, refusing an invalid explicit selection before PATH lookup.
#[cfg(feature = "trust-ir-backend")]
fn find_trust_cg() -> Result<Option<PathBuf>, crate::native_trustcg::LaneError> {
    crate::native_trustcg::select_trust_cg_path(
        std::env::var_os("CLEAN_TRUST_CG_BIN"),
        std::env::var_os("PATH"),
    )
}

/// Map the host architecture to a `trust-cg --target` value.
#[cfg(feature = "trust-ir-backend")]
pub(crate) fn host_trust_cg_target() -> anyhow::Result<&'static str> {
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
///
/// `pub(crate)` for `cmd_extract`'s Rust backend: it needs exactly this front
/// half (same elaboration, same intra-project imports, same kernel-checked
/// registration) WITHOUT the root L5CNF lowering that `select_lcnf_decl`
/// additionally performs, because it translates the kernel value directly.
pub fn elaborate_file_to_env(path: &Path) -> anyhow::Result<Environment> {
    elaborate_file_to_env_with_source_opaques(path).map(|(env, _)| env)
}

/// The implicit environment for a Lean entry without `prelude`: Clean's built-in prelude
/// with Lean's IO operations registered (`IO.println` and the rest of the
/// effect surface `clean run` executes). Clean's program builds use it
/// (design 2026-09-30 §2.5): `clean compile`/`run` and `lake build`'s
/// executable step through [`elaborate_file_to_env`]. Trust's `.lean` front
/// door does not use it yet; decision R15 records why and what must hold first.
/// Explicit prelude entries use the module driver's bare setup instead.
pub fn lean_program_environment() -> anyhow::Result<Environment> {
    let mut env = Environment::with_prelude();
    env.init_io_ops()
        .context("failed to initialize the IO operations of the program environment")?;
    Ok(env)
}

/// [`elaborate_file_to_env`], also reporting every value-bearing `opaque` a
/// SOURCE file of this build declared (the file and its intra-project
/// imports). The native path compiles those from their value, as Lean does,
/// and refuses every other opaque it cannot vouch for — see
/// [`crate::native_opaque_audit`].
pub(crate) fn elaborate_file_to_env_with_source_opaques(
    path: &Path,
) -> anyhow::Result<(Environment, HashSet<Name>)> {
    elaborate_file_with_inventory(path).map(|(env, opaques, _)| (env, opaques))
}

fn elaborate_file_with_inventory(
    path: &Path,
) -> anyhow::Result<(Environment, HashSet<Name>, HashSet<Name>)> {
    let source_identity = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    let source_input = std::fs::read_to_string(path)?;
    let header = clean_parser::Parser::parse_header(&source_input)?;
    let decision = clean_olean::source_world_for_file(path, None)?;
    let mut source_setup =
        if clean_elab::module_driver::source_closure_needs_world_setup(path, &decision)? {
            Some(clean_elab::module_driver::SourceModuleSetup::for_program_file(&decision, path)?)
        } else {
            None
        };
    let mut env = if let Some(setup) = &mut source_setup {
        setup
            .initial_environment(&header)
            .map_err(anyhow::Error::from)
    } else if header.is_prelude {
        clean_elab::module_driver::module_environment_for_header_in_world(
            clean_elab::module_driver::EnvironmentSetup::default(),
            &decision,
            &header,
        )
        .map(|(env, _)| env)
        .map_err(anyhow::Error::from)
    } else {
        lean_program_environment()
    }
    .with_context(|| {
        format!(
            "failed to build the program environment for {}",
            path.display()
        )
    })?;
    // One Lean world for the build (G72, R111): the entry file's Lake
    // package's, as Lake builds every package with the root's toolchain.
    let source_entry = source_setup.as_ref().map(|_| source_identity);
    let source_inputs = source_entry
        .as_ref()
        .map(|canonical| {
            HashMap::from([(
                canonical.clone(),
                std::sync::Arc::<str>::from(source_input.as_str()),
            )])
        })
        .unwrap_or_default();
    let mut walk = SourceWalk {
        source_setup,
        source_inputs,
        source_entry,
        import_world: Some(clean_elab::import_world_for_file(path)),
        ..SourceWalk::default()
    };
    elaborate_file_into_env(path, &mut env, &mut walk)?;
    Ok((env, walk.source_opaques, walk.source_decls))
}

/// State threaded through the recursive intra-project elaboration.
#[derive(Default)]
struct SourceWalk {
    /// Fresh headers are permitted only with independent body comparison.
    source_setup: Option<clean_elab::module_driver::SourceModuleSetup>,
    /// Effects independently validated in this unchanged source invocation.
    faithful_effects: HashMap<PathBuf, clean_kernel::env::EnvEffect>,
    /// Exact source inputs shared with independent re-elaborations.
    source_inputs: HashMap<PathBuf, std::sync::Arc<str>>,
    /// Identity of the root whose header selected its initial environment.
    source_entry: Option<PathBuf>,
    /// Files currently on the elaboration stack (cycle detection).
    in_flight: HashSet<PathBuf>,
    /// Files already elaborated (diamond dedup).
    completed: HashSet<PathBuf>,
    /// Value-bearing `opaque`s the source files declared.
    source_opaques: HashSet<Name>,
    /// Names declared by source leaves, including lifted definition leaves.
    source_decls: HashSet<Name>,
    /// Canonical path of each imported source -> the module name its `import`
    /// wrote: Lean's main module for that file, which its `private`
    /// declarations are minted with (`_private.<module>.0.<name>`, G21), as
    /// `clean check` mints them.
    module_names: HashMap<PathBuf, Name>,
    /// The build's Lean world, selected once for the entry file; every file
    /// of the walk resolves its imports in it (`None`: each file selects its
    /// own).
    import_world: Option<Result<clean_elab::ImportWorld, clean_elab::ImportWorldRefusal>>,
}

/// Record every value-bearing `opaque` an elaboration result declares.
fn collect_source_opaques(result: &ElabResult, out: &mut HashSet<Name>) {
    match result {
        ElabResult::Opaque {
            name, val: Some(_), ..
        } => {
            out.insert(name.clone());
        }
        ElabResult::Multiple(results) => {
            for inner in results {
                collect_source_opaques(inner, out);
            }
        }
        _ => {}
    }
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
    walk: &mut SourceWalk,
) -> anyhow::Result<()> {
    if walk.in_flight.len() >= MAX_NATIVE_IMPORT_DEPTH {
        anyhow::bail!(
            "import depth limit ({MAX_NATIVE_IMPORT_DEPTH}) exceeded while elaborating {}",
            path.display()
        );
    }

    let canonical = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    if walk.in_flight.is_empty()
        && walk
            .source_entry
            .as_ref()
            .is_some_and(|expected| expected != &canonical)
    {
        anyhow::bail!(
            "source module {} changed identity after its header was read",
            path.display()
        );
    }
    if walk.completed.contains(&canonical) {
        return Ok(());
    }
    if !walk.in_flight.insert(canonical.clone()) {
        anyhow::bail!(
            "import cycle detected at {}: file is already being elaborated",
            path.display()
        );
    }

    let result = elaborate_file_body(path, env, walk);

    walk.in_flight.remove(&canonical);
    let effect = result?;
    if let Some(effect) = effect {
        // Even the first dependency may have seen its ordinary parent's
        // implicit Init. Compare EVERY imported body, not only siblings.
        if !walk.in_flight.is_empty() {
            let expected =
                match walk.faithful_effects.get(&canonical) {
                    Some(expected) => expected.clone(),
                    None => {
                        let mut setup = walk
                            .source_setup
                            .as_ref()
                            .map(clean_elab::module_driver::SourceModuleSetup::isolated)
                            .ok_or_else(|| anyhow::anyhow!("missing isolated source setup"))?;
                        let input = walk.source_inputs.get(&canonical).ok_or_else(|| {
                            anyhow::anyhow!("isolated source has no retained input")
                        })?;
                        let header = clean_parser::Parser::parse_header(input)?;
                        let mut isolated_env = setup.initial_environment(&header)?;
                        let mut isolated = SourceWalk {
                            source_setup: Some(setup),
                            faithful_effects: walk.faithful_effects.clone(),
                            source_inputs: walk.source_inputs.clone(),
                            source_entry: Some(canonical.clone()),
                            module_names: walk.module_names.clone(),
                            import_world: walk.import_world.clone(),
                            ..SourceWalk::default()
                        };
                        elaborate_file_into_env(path, &mut isolated_env, &mut isolated)
                            .with_context(|| {
                                format!(
                                "source module {} could not elaborate in its own import closure",
                                path.display()
                            )
                            })?;
                        let expected = isolated
                            .faithful_effects
                            .get(&canonical)
                            .cloned()
                            .ok_or_else(|| {
                                anyhow::anyhow!("isolated source module has no completed effect")
                            })?;
                        walk.faithful_effects.extend(isolated.faithful_effects);
                        expected
                    }
                };
            if let Some(reason) = expected.disagreement(&effect, env) {
                anyhow::bail!(
                    "source module {} differs from its own import closure: {reason}",
                    path.display()
                );
            }
        }
        walk.faithful_effects
            .entry(canonical.clone())
            .or_insert(effect);
    }
    walk.completed.insert(canonical);
    Ok(())
}

fn elaborate_file_body(
    path: &Path,
    env: &mut Environment,
    walk: &mut SourceWalk,
) -> anyhow::Result<Option<clean_kernel::env::EnvEffect>> {
    let source = std::fs::read_to_string(path)
        .with_context(|| format!("failed to read source file {}", path.display()))?;
    let canonical = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    if walk.source_setup.is_some() {
        if walk.in_flight.len() == 1
            && walk
                .source_entry
                .as_ref()
                .is_some_and(|expected| expected != &canonical)
        {
            anyhow::bail!(
                "source module {} changed identity after its header was read",
                path.display()
            );
        }
        if let Some(previous) = walk.source_inputs.get(&canonical) {
            if previous.as_ref() != source {
                anyhow::bail!(
                    "source module {} changed during isolated elaboration",
                    path.display()
                );
            }
        } else {
            walk.source_inputs
                .insert(canonical.clone(), std::sync::Arc::from(source.as_str()));
        }
    }
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let parsed = clean_parser::parse_file_with_tactics_diagnostics(&source, &patterns)
        .with_context(|| format!("failed to parse {}", path.display()))?;
    let header = parsed.header;
    let decls = parsed.decls;

    let mut file_ctx = FileContext::new();
    file_ctx.set_file_header(&header);
    // Thread Lake `.olean` search paths and the project's Lean world (G72) so
    // external imports still resolve via the existing artifact loader during
    // the main elaboration pass, in that world only.
    match &walk.import_world {
        Some(world) => file_ctx.set_import_context(path, world.clone()),
        None => file_ctx.set_import_context_for_file(path),
    }
    // Lean's main module: the name an importer wrote, else the entry file's
    // Lake (or path) name — the name `clean check` gives the same file.
    file_ctx.set_main_module(
        walk.module_names
            .get(&canonical)
            .cloned()
            .unwrap_or_else(|| clean_elab::entry_module_name(path)),
    );
    let decls = match &mut walk.source_setup {
        Some(setup) => setup
            .prepare(
                env,
                &header,
                &decls,
                &mut file_ctx,
                walk.completed.is_empty(),
            )
            .map_err(anyhow::Error::from),
        None => clean_elab::module_driver::elaborate_prelude_header(env, &decls, &mut file_ctx)
            .map_err(anyhow::Error::from),
    }
    .with_context(|| format!("failed to elaborate declaration in {}", path.display()))?;

    // First pass: resolve `import M.X.Y` directives to sibling `.lean` sources
    // and elaborate them into the SAME `env` first, so their constants are
    // registered before this file's own decls reference them. External modules
    // (no project-local `.lean`) resolve to `None` and fall through to the
    // `.olean` flow handled by the `Import` decl in the main loop below.
    let mut satisfied_from_source = HashSet::new();
    for decl in decls {
        resolve_and_elaborate_imports(decl, path, env, walk, &mut satisfied_from_source)?;
    }

    let mut before_own = None;
    if let Some(module) = file_ctx.main_module() {
        clean_kernel::env::csimp::begin_source_module(
            env,
            module.clone(),
            satisfied_from_source.iter().cloned().collect(),
        );
    }
    // ...and tell it which imports the pass above already satisfied from source,
    // so the fail-closed policy does not refuse them for lacking an artifact
    // this project has never built.
    for module in &satisfied_from_source {
        file_ctx.mark_import_satisfied_from_source(module);
    }

    for decl in decls {
        // As in the module driver's before_body checkpoint, artifacts loaded
        // by the header belong to the closure, not to the body's own effect.
        if walk.source_setup.is_some()
            && before_own.is_none()
            && !matches!(decl, clean_parser::SurfaceDecl::Import { .. })
        {
            before_own = Some(env.clone());
        }
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        // Thread `file_ctx` so standalone `open`/`export` aliases and
        // file-scope notation persist across declarations (gap sweep B13),
        // keeping this surface consistent with `clean check`.
        let registered =
            elaborate_decl_and_register_with_context_and_warning(env, &processed, &mut file_ctx)
                .with_context(|| {
                    format!("failed to elaborate declaration in {}", path.display())
                })?;
        // THE SAME K5 DEFECT, SECOND SITE (2026-09-17). This used to check
        // `registered.warning` and `registered.result` as ONE unit. A
        // `namespace` / `section` / `mutual` block elaborates to a single
        // `ElabResult::Multiple` that carries `warning: None`, and
        // `validate_elab_result` answered `Ok(())` for it — so both gates were
        // namespace-blind. Measured before this fix, on the same binary:
        //
        //   def topViaSorry : Nat := sorry                  -> REFUSED
        //   namespace N  def viaSorry : Nat := sorry  end N -> COMPILED
        //
        // and likewise a sibling whose elaboration FAILED aborted the file at
        // top level but not inside a namespace. Flatten first, then apply both
        // gates per member — the member's own registration warning, and its own
        // kernel validation — so where a declaration sits cannot change whether
        // it is gated.
        let mut leaves: Vec<&ElabResult> = Vec::new();
        registered.result.leaf_decls(&mut leaves);
        if leaves.is_empty() {
            refuse_trust_warning(registered.warning.as_ref())?;
            validate_elab_result(&registered.result, env)
                .with_context(|| format!("kernel validation failed in {}", path.display()))?;
            continue;
        }
        for leaf in leaves {
            if let ElabResult::Failed { name, error, .. } = leaf {
                anyhow::bail!(
                    "refusing to compile {}: declaration `{name}` failed to elaborate: {error}",
                    path.display()
                );
            }
            if let Some(name) = leaf.declaration_name() {
                walk.source_decls.insert(name.clone());
            }
            // By leaf, not by name (an `example` has no name), and read off the
            // leaf's constant closure: a sorry behind an alias or a cited
            // lemma is refused like one written in place.
            let warning = clean_elab::register::registration_warning_for_leaf(env, leaf);
            refuse_trust_warning(warning.as_ref())?;
            validate_elab_result(leaf, env)
                .with_context(|| format!("kernel validation failed in {}", path.display()))?;
        }
        collect_source_opaques(&registered.result, &mut walk.source_opaques);
    }

    if walk.source_setup.is_some() && before_own.is_none() {
        before_own = Some(env.clone());
    }
    Ok(before_own.map(|before| env.effect_since(&before)))
}

/// Refuse to compile a declaration that carries a trust warning (`sorry`,
/// `trustedArith`, `trustedAy`).
fn refuse_trust_warning(warning: Option<&RegistrationWarning>) -> anyhow::Result<()> {
    match warning {
        Some(warning) => anyhow::bail!(
            "refusing to compile declaration `{}` with trust warning {:?}",
            warning.decl_name,
            warning.kind
        ),
        None => Ok(()),
    }
}

/// Walk a parsed declaration for `import M.X.Y` directives that resolve to a
/// project-local `.lean` source, and recursively elaborate each into `env`.
/// Descends through `namespace`/`section`/`mutual` wrappers and the bodies of
/// `set_option`/`open` that may carry nested decls, mirroring
/// `cmd_core::collect_intra_project_imports`.
/// Resolve `import M.X.Y` to sibling `.lean` sources and elaborate them into
/// `env`, recording each module name that was satisfied that way in
/// `satisfied_from_source`.
///
/// That record is not bookkeeping: a source-only project has no `.olean` for its
/// own modules and never will, so the 2026-08-26 fail-closed import policy
/// (`clean_elab::ImportPolicy`) would otherwise read the expected absence as an
/// unresolvable module and refuse every internal import in the main pass.
fn resolve_and_elaborate_imports(
    decl: &clean_parser::SurfaceDecl,
    parent_path: &Path,
    env: &mut Environment,
    walk: &mut SourceWalk,
    satisfied_from_source: &mut HashSet<Name>,
) -> anyhow::Result<()> {
    use clean_parser::SurfaceDecl;
    match decl {
        SurfaceDecl::Import { paths, .. } => {
            for module_path in paths {
                if module_path.is_anonymous() {
                    continue;
                }
                let module_name = module_path.name();
                if let Some(import_file) =
                    clean_elab::resolve_intra_project_import(module_name, parent_path)
                {
                    let canonical =
                        std::fs::canonicalize(&import_file).unwrap_or_else(|_| import_file.clone());
                    walk.module_names
                        .entry(canonical)
                        .or_insert_with(|| module_name.clone());
                    elaborate_file_into_env(&import_file, env, walk)?;
                    satisfied_from_source.insert(module_name.clone());
                }
            }
        }
        SurfaceDecl::Namespace { decls, .. }
        | SurfaceDecl::Section { decls, .. }
        | SurfaceDecl::Mutual { decls, .. } => {
            for inner in decls {
                resolve_and_elaborate_imports(
                    inner,
                    parent_path,
                    env,
                    walk,
                    satisfied_from_source,
                )?;
            }
        }
        SurfaceDecl::SetOption {
            body: Some(body), ..
        }
        | SurfaceDecl::Open {
            body: Some(body), ..
        } => {
            resolve_and_elaborate_imports(body, parent_path, env, walk, satisfied_from_source)?;
        }
        _ => {}
    }
    Ok(())
}

fn validate_elab_result(result: &ElabResult, env: &Environment) -> anyhow::Result<()> {
    if let Some(message) = result.source_error_message() {
        anyhow::bail!(message);
    }
    // FAIL CLOSED on an unflattened block: skipping one is skipping every
    // declaration inside it. See `ElabResult::unflattened_block_refusal`.
    if let Some(refusal) = result.unflattened_block_refusal() {
        anyhow::bail!(refusal);
    }
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

/// Emit `decls` in `emit` format, for code that means `meaning`: the one
/// `decls` were lowered under. `clean compile` and `clean run` emit at
/// [`CodeMeaning::LeanCompiled`]; `clean extract` emits the
/// [`CodeMeaning::KernelValue`] closure `crate::select_lcnf_decl_kernel_meaning`
/// selects (`clean_compiler::pass_manager::compile_lcnf_decls_for`).
///
/// # Errors
///
/// Whatever the pipeline or the emitter refuses.
// `source_file` feeds only the trust-ir arm's debug info; the other formats
// ignore it (and it is entirely unused without the `trust-ir-backend` feature).
#[cfg_attr(not(feature = "trust-ir-backend"), allow(unused_variables))]
pub fn emit_decls(
    decls: &[Decl],
    env: &Environment,
    emit: EmitFormat,
    pipeline: &PipelineConfig,
    source_file: Option<&Path>,
    meaning: CodeMeaning,
) -> anyhow::Result<String> {
    emit_decls_ordered(decls, env, emit, pipeline, source_file, meaning, None)
}

pub(crate) fn emit_decls_in_runtime_closure(
    decls: &[Decl],
    env: &Environment,
    emit: EmitFormat,
    pipeline: &PipelineConfig,
    source_file: Option<&Path>,
    closure: &clean_compiler::RuntimeBindingClosure,
) -> anyhow::Result<String> {
    emit_decls_ordered(
        decls,
        env,
        emit,
        pipeline,
        source_file,
        CodeMeaning::LeanCompiled,
        Some(closure),
    )
}

#[cfg_attr(not(feature = "trust-ir-backend"), allow(unused_variables))]
fn emit_decls_ordered(
    decls: &[Decl],
    env: &Environment,
    emit: EmitFormat,
    pipeline: &PipelineConfig,
    source_file: Option<&Path>,
    meaning: CodeMeaning,
    closure: Option<&clean_compiler::RuntimeBindingClosure>,
) -> anyhow::Result<String> {
    match emit {
        EmitFormat::L5cnf => Ok(format!("{decls:#?}\n")),
        EmitFormat::L5ir => {
            let artifacts = compile_selected_decls(decls, env, pipeline, meaning, closure)?;
            Ok(format!("{:#?}\n", artifacts.boxed_ir_decls))
        }
        EmitFormat::C => Ok(
            compile_selected_decls(decls, env, pipeline, meaning, closure)?.emit_c(
                CEmitConfig {
                    check_ir: true,
                    ..Default::default()
                },
            )?,
        ),
        EmitFormat::Rust => Ok(
            compile_selected_decls(decls, env, pipeline, meaning, closure)?.emit_rust(
                RustEmitConfig {
                    check_ir: true,
                    ..Default::default()
                },
            )?,
        ),
        #[cfg(feature = "trust-ir-backend")]
        EmitFormat::Trustir => {
            use clean_compiler::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
            use clean_compiler::pass_manager::compile_lcnf_to_trust_ir_with_report_for;
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
            let module = match closure {
                Some(closure) => {
                    clean_compiler::pass_manager::compile_lcnf_to_trust_ir_in_runtime_closure(
                        decls, env, pipeline, &config, closure,
                    )?
                }
                None => {
                    compile_lcnf_to_trust_ir_with_report_for(
                        decls, env, pipeline, &config, meaning,
                    )?
                    .0
                }
            };
            Ok(format!("{module}\n"))
        }
        #[cfg(feature = "trust-ir-backend")]
        EmitFormat::Obj => {
            // `--emit obj` is intercepted in clean-cli's
            // `cmd_compile::handle_compile_command` (it writes a binary
            // file), so it never reaches the text emitter.
            anyhow::bail!("internal error: `--emit obj` must be handled before `emit_decls`")
        }
        #[cfg(feature = "trust-ir-backend")]
        EmitFormat::TrustirBin => {
            // Likewise intercepted: it writes plain trust-ir module bytes.
            anyhow::bail!(
                "internal error: `--emit trustir-bin` must be handled before `emit_decls`"
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_decl_query_uses_exact_source_identifier_syntax() {
        assert_eq!(
            parse_compile_decl_name("«A.B»").expect("quoted"),
            Name::anon().str("A.B")
        );
        assert_eq!(
            parse_compile_decl_name("A.B").expect("nested"),
            Name::anon().str("A").str("B")
        );
        assert_eq!(
            parse_compile_decl_name("«7»").expect("quoted numeral"),
            Name::anon().str("7")
        );
        assert_eq!(
            parse_compile_decl_name("_root_.A.B").expect("absolute"),
            Name::anon().str("A").str("B")
        );
        for malformed in ["7", ".B", "A.B trailing", "A..B"] {
            assert!(parse_compile_decl_name(malformed).is_err(), "{malformed}");
        }
    }

    #[test]
    fn compile_selects_exact_quoted_or_hierarchical_declaration() {
        let (_dir, file) = write_temp_lean(
            "def «A.B» (x : Nat) : Nat := x\nnamespace A\ndef B (x : Bool) : Bool := x\nend A\n",
        );
        for (query, expected) in [
            ("«A.B»", Name::anon().str("A.B")),
            ("A.B", Name::anon().str("A").str("B")),
        ] {
            let args = CompileArgs {
                file: Some(file.clone()),
                decl: Some(query.to_owned()),
                emit: EmitFormat::C,
                opt_level: 0,
                output: None,
                link_artifact: Vec::new(),
            };
            let (decls, env, _) = select_lcnf_decl(&args).expect("select exact declaration");
            assert_eq!(decls[0].name, expected);
            let expected_type = env
                .get_const(&expected)
                .expect("exact constant")
                .type_
                .clone();
            let (_, returned_type) =
                compile_to_string_with_decl_type(args).expect("emit selected declaration and type");
            assert_eq!(
                returned_type,
                Some(expected_type),
                "return type must come from the same selected identity"
            );
        }
    }

    fn write_temp_lean(source: &str) -> (tempfile::TempDir, PathBuf) {
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
            link_artifact: Vec::new(),
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
            link_artifact: Vec::new(),
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
            link_artifact: Vec::new(),
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
            link_artifact: Vec::new(),
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
            link_artifact: Vec::new(),
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
            link_artifact: Vec::new(),
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
    /// existing `.olean` flow. A decl that does not actually reference any
    /// external symbol still compiles.
    ///
    /// The module is `Mathlib.Data.Real.Basic` — one a `PRELUDE_PROVIDERS` entry
    /// names VERBATIM — and that choice is load-bearing since the 2026-08-26
    /// fail-closed import brick. The fixture used to be
    /// `Mathlib.Data.Nat.Basic`, which no provider names: it was served by the
    /// `Mathlib.*` prefix wildcard, which now resolves nothing. Both modules
    /// are equally "external-looking" and equally absent from the project tree,
    /// so this still measures local-vs-external resolution and nothing else.
    #[test]
    fn compile_external_import_is_not_resolved_as_local() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        let main = root.join("Main.lean");
        std::fs::write(
            &main,
            "import Mathlib.Data.Real.Basic\ndef plain (n : Nat) : Nat := n\n",
        )
        .expect("Main.lean");

        let output = compile_to_string(CompileArgs {
            file: Some(main),
            decl: Some("plain".to_owned()),
            emit: EmitFormat::C,
            opt_level: 0,
            output: None,
            link_artifact: Vec::new(),
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
    fn compile_emit_trustir_bin_without_output_errors() {
        let (_dir, file) = write_temp_lean("def demoId (x : Nat) : Nat := x");
        let err = compile_to_trustir_bin(&CompileArgs {
            file: Some(file),
            decl: Some("demoId".to_owned()),
            emit: EmitFormat::TrustirBin,
            opt_level: 0,
            output: None,
            link_artifact: Vec::new(),
        })
        .expect_err("`--emit trustir-bin` without `-o` must fail");
        assert!(
            err.to_string().contains("requires an output path"),
            "unexpected error for missing -o: {err:#}"
        );
    }

    /// The linkable artifact must be exactly what a consumer reads, and its
    /// digest must be what a `Module.imports` row would record.
    ///
    /// This is the property that makes the file citable at all: if the bytes
    /// on disk were a container, `deserialize_module` would refuse them, and a
    /// digest taken over the file would not be the module's identity.
    #[cfg(feature = "trust-ir-backend")]
    #[test]
    fn compile_emit_trustir_bin_is_plain_module_bytes_a_consumer_can_cite() {
        let (dir, file) = write_temp_lean("def demoId (x : Nat) : Nat := x");
        let out = dir.path().join("demolib.bin");
        compile_to_trustir_bin(&CompileArgs {
            file: Some(file),
            decl: Some("demoId".to_owned()),
            emit: EmitFormat::TrustirBin,
            opt_level: 0,
            output: Some(out.clone()),
            link_artifact: Vec::new(),
        })
        .expect("`--emit trustir-bin` should produce a module");
        let bytes = std::fs::read(&out).expect("artifact should exist");
        assert!(!bytes.is_empty(), "artifact should be non-empty");
        // NOT a `.tmbc`: the container's magic would make the canonical reader
        // refuse, so its absence is part of the contract, not an accident.
        assert_ne!(
            &bytes[..4.min(bytes.len())],
            b"tMBC",
            "the linkable artifact must not carry the trust-cg container header"
        );
        // The canonical reader accepts it, and refuses trailing bytes, so this
        // is a real decode rather than a prefix match.
        let decoded = clean_compiler::emit_trust_ir::deserialize_module_bytes(&bytes)
            .expect("the canonical reader must accept the artifact");
        // The module is named after the output stem, so two artifacts are
        // distinguishable in diagnostics.
        assert_eq!(decoded.name, "demolib");
        // And the digest a consumer computes over these bytes is the identity an
        // import row would record.
        let reencoded = clean_compiler::emit_trust_ir::serialize_module_bytes(&decoded)
            .expect("decoded module has a wire identity");
        assert_eq!(
            reencoded, bytes,
            "the artifact must round-trip byte-exactly"
        );
        assert_eq!(
            clean_compiler::emit_trust_ir::module_stable_digest_string(&decoded)
                .expect("decoded module has a wire identity"),
            clean_compiler::emit_trust_ir::module_stable_digest_string(
                &clean_compiler::emit_trust_ir::deserialize_module_bytes(&bytes).expect("decodes")
            )
            .expect("decoded module has a wire identity"),
            "the digest must be a function of the bytes alone"
        );
        // A trailing byte is REFUSED at load, so the decode above was a real
        // one and not a prefix match.
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(
            clean_compiler::emit_trust_ir::deserialize_module_bytes(&trailing).is_err(),
            "the canonical reader must refuse trailing bytes"
        );
    }

    #[cfg(feature = "trust-ir-backend")]
    #[test]
    fn compile_emit_obj_without_output_errors() {
        let (_dir, file) = write_temp_lean("def demoId (x : Nat) : Nat := x");
        let err = compile_to_object(&CompileArgs {
            file: Some(file),
            decl: Some("demoId".to_owned()),
            emit: EmitFormat::Obj,
            opt_level: 0,
            output: None,
            link_artifact: Vec::new(),
        })
        .expect_err("`--emit obj` without `-o` must fail");
        assert!(
            err.to_string().contains("requires an output path"),
            "unexpected error for missing -o: {err:#}"
        );
    }

    // ── K5, second site: the compile gates must not be namespace-blind ──────
    //
    // `clean compile` refuses a declaration that carries a trust warning and
    // aborts a file whose declaration fails to elaborate. Before the 2026-09-17
    // fix both gates read the top-level `ElabResult` only, so a `namespace`
    // block — one `Multiple` carrying `warning: None` — walked straight past
    // them. The battery is by failure KIND and by POSITION inside the block;
    // the controls pin that legitimate namespaced code still compiles.

    /// A `sorry` inside a namespace must be refused exactly as at top level.
    #[test]
    fn a_sorry_inside_a_namespace_is_refused_like_one_at_top_level() {
        let top = compile_fixture(
            "def topViaSorry : Nat := sorry",
            "topViaSorry",
            EmitFormat::C,
        )
        .expect_err("a sorry at top level is refused");
        assert!(
            format!("{top:#}").contains("trust warning"),
            "top-level control must refuse on the trust warning: {top:#}"
        );

        for (source, decl) in [
            (
                "namespace NsSorry\ndef viaSorry : Nat := sorry\nend NsSorry\n",
                "NsSorry.viaSorry",
            ),
            (
                "section\ndef sectionViaSorry : Nat := sorry\nend\n",
                "sectionViaSorry",
            ),
            (
                "namespace Outer\nnamespace Inner\ndef deepViaSorry : Nat := sorry\nend Inner\nend Outer\n",
                "Outer.Inner.deepViaSorry",
            ),
            (
                "namespace NsLate\ndef nsGood : Nat := 1\ndef lateViaSorry : Nat := sorry\nend NsLate\n",
                "NsLate.nsGood",
            ),
        ] {
            let err = compile_fixture(source, decl, EmitFormat::C).expect_err(
                "a sorry inside a block must be refused wherever the block puts it",
            );
            assert!(
                format!("{err:#}").contains("trust warning"),
                "must refuse on the trust warning, not incidentally: {err:#}"
            );
        }
    }

    /// A declaration that failed to elaborate must abort the file from inside a
    /// namespace exactly as it does at top level.
    #[test]
    fn a_failed_declaration_inside_a_namespace_aborts_the_file() {
        let top = compile_fixture(
            "def topGood : Nat := 1\ndef topBad : Bool := (0 : Nat)",
            "topGood",
            EmitFormat::C,
        )
        .expect_err("a failing sibling at top level aborts the file");
        assert!(format!("{top:#}").contains("Type mismatch"), "{top:#}");

        let err = compile_fixture(
            "namespace NsBad\ndef nsGood : Nat := 1\ndef nsBad : Bool := (0 : Nat)\nend NsBad\n",
            "NsBad.nsGood",
            EmitFormat::C,
        )
        .expect_err("a failing sibling inside a namespace must abort the file too");
        let text = format!("{err:#}");
        assert!(
            text.contains("failed to elaborate") && text.contains("nsBad"),
            "the refusal must name the failing member: {text}"
        );
    }

    /// Control: legitimate namespaced code still compiles. The gates must refuse
    /// what is wrong, not everything inside a block.
    #[test]
    fn legitimate_namespaced_declarations_still_compile() {
        let output = compile_fixture(
            "namespace NsOk\ndef nsId (x : Nat) : Nat := x\ndef nsUse (x : Nat) : Nat := nsId x\nend NsOk\n",
            "NsOk.nsUse",
            EmitFormat::C,
        )
        .expect("a namespace of good declarations must still compile");
        assert!(!output.is_empty());
    }

    #[cfg(feature = "trust-ir-backend")]
    #[test]
    fn object_codegen_checks_bind_the_module_and_refuse_claimless_bodies() {
        use crate::native_trustcg::checks::object_self_checks_for_env;
        use clean_compiler::pass_manager::compile_lcnf_to_trust_ir as emit_module;

        let (_dir, file) = write_temp_lean("def demoId (x : Nat) : Nat := x");
        let args = CompileArgs {
            file: Some(file),
            decl: Some("demoId".to_owned()),
            emit: EmitFormat::Obj,
            opt_level: 0,
            output: None,
            link_artifact: Vec::new(),
        };
        let (decls, env, pipeline) = select_lcnf_decl(&args).expect("checked source");
        let module = emit_module(&decls, &env, &pipeline, &object_emit_config(&args))
            .expect("checked emitted module");
        let checked = object_self_checks_for_env(&env, &module).expect("object self-checks");

        let mut changed = module.clone();
        changed
            .functions
            .iter_mut()
            .find(|f| !f.blocks.is_empty())
            .expect("defined function")
            .name
            .push_str("_changed");
        assert!(checked.license(&mut changed).is_err());

        let mut claimless = module.clone();
        claimless
            .functions
            .iter_mut()
            .find(|f| !f.blocks.is_empty())
            .expect("defined function")
            .body_gate = None;
        let checked_claimless =
            object_self_checks_for_env(&env, &claimless).expect("structural self-checks");
        assert!(checked_claimless.license(&mut claimless).is_err());

        let mut licensed = module;
        let census = checked
            .license(&mut licensed)
            .expect("checked object license");
        assert!(census.unvalidated > 0);
    }

    #[cfg(feature = "trust-ir-backend")]
    #[test]
    fn compile_file_emit_obj_produces_object() {
        // Needs the trust-cg backend binary; skip cleanly where it is absent
        // (e.g. CI without the sibling repo built).
        if find_trust_cg().expect("valid trust-cg selection").is_none() {
            eprintln!("skipping compile_file_emit_obj_produces_object: trust-cg not found");
            return;
        }
        let (dir, file) = write_temp_lean("def demoId (x : Nat) : Nat := x");
        let obj = dir.path().join("demoId.o");
        compile_to_object(&CompileArgs {
            file: Some(file),
            decl: Some("demoId".to_owned()),
            emit: EmitFormat::Obj,
            opt_level: 0,
            output: Some(obj.clone()),
            link_artifact: Vec::new(),
        })
        .expect("`--emit obj` should produce a native object");
        let meta = std::fs::metadata(&obj).expect("object file should exist");
        assert!(meta.len() > 0, "emitted object file should be non-empty");
    }
}

#[cfg(all(test, feature = "trust-ir-backend"))]
#[path = "compile_battery_census_tests.rs"]
mod battery_census_tests;

#[cfg(test)]
#[path = "compile_program_env_tests.rs"]
mod program_env_tests;

#[cfg(test)]
#[path = "compile_implemented_by_tests.rs"]
mod implemented_by_tests;

#[cfg(test)]
#[path = "compile_implemented_by_order_tests.rs"]
mod implemented_by_order_tests;

#[cfg(test)]
#[path = "compile_implemented_by_import_tests.rs"]
mod implemented_by_import_tests;
