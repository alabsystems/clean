// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The inputs every frontend builds the same way before the per-declaration
//! loop runs: the environment, the parse, the `FileContext`, the budget and the
//! process-wide lock that makes the trust counters attributable.

use crate::notation_imports::{seed_from_imports, HarvestStats};
use crate::FileContext;
use clean_kernel::Environment;
use clean_parser::{ParseError, ParseReport, SurfaceDecl};
use std::path::Path;
use std::sync::{Mutex, MutexGuard, OnceLock, PoisonError};

/// Elaborate a leading `prelude` before resolving source imports.
///
/// The ordinary declaration elaborator still enforces its empty-environment
/// guard. Returning the body prevents a caller from checking that same header
/// again after its explicit imports have populated the environment.
///
/// # Errors
/// Returns the ordinary elaborator's refusal when the environment is not fresh,
/// or refuses an ordinary module inheriting a prelude importer's bare setup.
pub fn elaborate_prelude_header<'a>(
    env: &mut Environment,
    decls: &'a [SurfaceDecl],
    context: &mut FileContext,
) -> Result<&'a [SurfaceDecl], crate::ElabError> {
    if let Some((header @ SurfaceDecl::Prelude { .. }, body)) = decls.split_first() {
        crate::elaborate_decl_and_register_with_context_and_warning(env, header, context)?;
        Ok(body)
    } else if crate::source_prelude::is_bare_module(env) {
        Err(crate::ElabError::NotImplemented(
            "an ordinary source module requires its own implicit Init environment; source-module isolation from a prelude importer is not implemented".to_string(),
        ))
    } else {
        Ok(decls)
    }
}

/// Which prelude a module is checked against.
///
/// Mirrors `clean_kernel::cli::PreludeMode`, which lives behind the kernel's
/// `cli` feature; this crate does not enable it, so the CLI maps one onto the
/// other.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum PreludeFlavor {
    /// Clean's hand-registered prelude plus the Clean-native `List` monad
    /// instances (`clean check`'s default).
    #[default]
    Builtin,
    /// The same prelude with no `List` monad instances and the strict monad
    /// gate on (`--prelude lean4-core`).
    Lean4Core,
}

/// Where a module's imports are expected to come from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum ImportArtifacts {
    /// The ordinary prelude; imports are loaded or elaborated on top of it.
    #[default]
    Source,
    /// `--imports-prefer-olean`: start from the import prelude so the genuine
    /// `.olean` structures are not shadowed by the prelude's hand-rolled ones.
    PreferOlean,
}

/// How to build the environment a module is elaborated into.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct EnvironmentSetup {
    /// The prelude flavour.
    pub prelude: PreludeFlavor,
    /// Where imports are expected to come from.
    pub imports: ImportArtifacts,
}

/// A failure standing up the environment, before any declaration of the module
/// is looked at. The messages are the ones `clean check` has always printed.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ModuleSetupError {
    /// A selected world must stand up its own genuine Init, never the
    /// oracle's handwritten Decidable or other versioned declarations.
    #[error("failed to initialize Lean world {world}: {reason}")]
    LeanWorld {
        world: clean_kernel::lean_world::LeanWorld,
        reason: String,
    },
    /// The import prelude could not be built.
    #[error("failed to initialize the import prelude: {0}")]
    ImportPrelude(String),
    /// The `List` monad instances could not be registered.
    #[error("failed to initialize List monad instances: {0}")]
    ListMonadInstances(String),
    /// The IO operation axioms could not be registered.
    #[error("failed to initialize IO operations: {0}")]
    IoOperations(String),
    /// `ULift` could not be registered.
    #[error("failed to initialize ULift: {0}")]
    ULift(String),
}

/// Build the environment `clean check` elaborates a module into.
///
/// Every frontend that wants `clean check`'s verdicts must start here: a module
/// checked against a different environment is a different check. The
/// registrations below were the check path's own until the driver moved them.
///
/// * Under [`ImportArtifacts::PreferOlean`] the prelude must NOT seed the
///   kernel's hand-rolled `extends`-structure stubs: `Preorder.mk` there has
///   FOUR fields where Lean's has five, and the importer dedups by name, so the
///   genuine structure was silently skipped — measured 2026-09-10 on
///   `Mathlib/Order/Defs/PartialOrder` (`lt_iff_le_not_ge` was `Unknown
///   structure field`). `try_with_prelude_for_import` is the kernel's
///   constructor for exactly this (WS17).
/// * [`PreludeFlavor::Builtin`] registers the Clean-native `Pure List` /
///   `Bind List` instances (a documented prelude extension; Lean core has
///   none); [`PreludeFlavor::Lean4Core`] leaves `List` uninstanced and turns on
///   the strict monad gate (B07, GAP_SWEEP_2026-07-09).
/// * IO operations are available to source elaboration through the optional
///   native stub theory. This constructor seeds none of them; emitted kernel
///   references request a fragment before the unchanged registration check.
/// * `ULift`, so `ULift.{u} Nat` is not an unknown identifier whose failure
///   path injects a `sorryAx` (GAP_SWEEP_2026-07-09 universes/p20). A
///   partial level list such as `ULift.{1}` elaborates as in Lean (the rest of
///   the levels are inferred); too many levels is a typed
///   `UniverseLevelMismatch`.
///
/// Native List and ULift registrars do not run under the import prelude;
/// genuine `Init` `.olean`s supply those names. IO signatures are an explicit
/// optional stub fragment, requested by source terms or execution backends.
pub fn module_environment(setup: EnvironmentSetup) -> Result<Environment, ModuleSetupError> {
    let prefer_olean = setup.imports == ImportArtifacts::PreferOlean;
    let mut env = if prefer_olean {
        Environment::try_with_prelude_for_import()
            .map_err(|e| ModuleSetupError::ImportPrelude(e.to_string()))?
    } else {
        Environment::with_prelude()
    };
    match setup.prelude {
        PreludeFlavor::Builtin => {
            if !prefer_olean {
                env.init_monad_list_insts()
                    .map_err(|e| ModuleSetupError::ListMonadInstances(e.to_string()))?;
            }
        }
        PreludeFlavor::Lean4Core => env.set_lean4_core_strict_monads(true),
    }
    if !prefer_olean {
        env.init_ulift()
            .map_err(|e| ModuleSetupError::ULift(e.to_string()))?;
    }
    Ok(env)
}

/// Build the environment of a selected source world. Missing or unsupported
/// genuine inputs are a setup error, not a fallback. A frontend that credits
/// imported proofs must retain the pre-import base returned by
/// [`module_environment_with_import_base_in_world`].
pub fn module_environment_in_world(
    setup: EnvironmentSetup,
    decision: &clean_olean::SourceWorldDecision,
) -> Result<Environment, ModuleSetupError> {
    module_environment_with_import_base_in_world(setup, decision).map(|(env, _base)| env)
}

/// Build the selected environment and retain its kernel base BEFORE imports.
///
/// Recent worlds import genuine Init over the canonical quotient/reducer
/// facilities of [`Environment::for_lean_replay`], with no handwritten prelude.
/// The second environment contains only those facilities: a citation gate must
/// replay Init declarations over it, rather than trusting a post-import
/// snapshot. Existing worlds retain their unchanged built-in base.
pub fn module_environment_with_import_base_in_world(
    setup: EnvironmentSetup,
    decision: &clean_olean::SourceWorldDecision,
) -> Result<(Environment, Environment), ModuleSetupError> {
    use clean_kernel::lean_world::LeanWorld;
    if !matches!(decision.world(), LeanWorld::Lean435 | LeanWorld::Lean436Rc2) {
        let mut env = module_environment(setup)?;
        if let Some(world) = decision.declared_world() {
            clean_olean::declare_environment_world(&mut env, world).map_err(|error| {
                ModuleSetupError::LeanWorld {
                    world: decision.world(),
                    reason: error.to_string(),
                }
            })?;
        }
        return Ok((env.clone(), env));
    }
    let fail = |reason: String| ModuleSetupError::LeanWorld {
        world: decision.world(),
        reason,
    };
    let mut env = Environment::for_lean_replay();
    clean_olean::declare_environment_world(&mut env, decision.world().tag())
        .map_err(|error| fail(error.to_string()))?;
    if setup.prelude == PreludeFlavor::Lean4Core {
        env.set_lean4_core_strict_monads(true);
    }
    let imports = decision
        .imports()
        .map_err(|refusal| fail(refusal.to_string()))?;
    with_import_base(env, |env| {
        clean_olean::load_module_with_deps(
            env,
            "Init",
            &clean_olean::search_paths_in_world(imports),
        )
        .map(|_| ())
        .map_err(|error| fail(error.to_string()))
    })
}

/// Select a genuinely empty starting environment for an explicit prelude header.
pub fn module_environment_for_header_in_world(
    setup: EnvironmentSetup,
    decision: &clean_olean::SourceWorldDecision,
    header: &clean_parser::FileHeader,
) -> Result<(Environment, clean_olean::ImportedConeGate), ModuleSetupError> {
    if !header.is_prelude {
        let (env, base) = module_environment_with_import_base_in_world(setup, decision)?;
        return Ok((env, clean_olean::ImportedConeGate::new(&base)));
    }
    // `new()` seeds trust-marker declarations; a prelude header permits none.
    let mut env = Environment::default();
    env.ensure_native_reducers();
    if let Some(world) = decision.declared_world() {
        clean_olean::declare_environment_world(&mut env, world).map_err(|error| {
            ModuleSetupError::LeanWorld {
                world: decision.world(),
                reason: error.to_string(),
            }
        })?;
    }
    if setup.prelude == PreludeFlavor::Lean4Core {
        env.set_lean4_core_strict_monads(true);
    }
    crate::source_prelude::mark_bare_module(&mut env);
    let import_base = if header.imports.is_empty() {
        clean_olean::ImportedConeGate::new(&Environment::default())
    } else {
        foundation_import_base(decision)?
    };
    Ok((env, import_base))
}

/// Admit only the genuine world's logical foundations and their dependency
/// cone. Native Eq and OfNat implementations must not shadow genuine imports.
fn foundation_import_base(
    decision: &clean_olean::SourceWorldDecision,
) -> Result<clean_olean::ImportedConeGate, ModuleSetupError> {
    use clean_kernel::Name;
    use std::collections::BTreeSet;

    let fail = |error: String| ModuleSetupError::ImportPrelude(error);
    let mut imported = Environment::for_lean_replay();
    if let Some(world) = decision.declared_world() {
        clean_olean::declare_environment_world(&mut imported, world)
            .map_err(|error| fail(error.to_string()))?;
    }
    let imports = decision
        .imports()
        .map_err(|refusal| fail(refusal.to_string()))?;
    clean_olean::load_module_with_deps(
        &mut imported,
        "Init.Core",
        &clean_olean::search_paths_in_world(imports),
    )
    .map_err(|error| fail(error.to_string()))?;
    let targets: BTreeSet<Name> = [
        "propext",
        "Classical.choice",
        "Quot",
        "Quot.mk",
        "Quot.lift",
        "Quot.ind",
        "Quot.sound",
    ]
    .into_iter()
    .map(Name::from_string)
    .collect();
    // This starts empty, checks canonical axiom statements and their premises,
    // regenerates inductive families and refuses any incomplete replay. Never
    // trust the imported Init snapshot or a foundational name on its own.
    clean_olean::ImportedConeGate::from_reference_cone(&imported, &targets).map_err(fail)
}

fn with_import_base(
    mut env: Environment,
    load: impl FnOnce(&mut Environment) -> Result<(), ModuleSetupError>,
) -> Result<(Environment, Environment), ModuleSetupError> {
    let import_base = env.clone();
    load(&mut env)?;
    Ok((env, import_base))
}

/// The parse `clean check` runs: the builtin tactic grammar, seeded with the
/// notation the file's project-local imports declare, keeping the parser's
/// recovery diagnostics instead of discarding them.
///
/// The harvest comes back beside the parse, not inside it, so a caller can
/// report what the seed read even when the parse fails. A file with no
/// resolvable imports gets an empty seed, and a parse with an empty seed is
/// the unseeded tactic-aware parse.
pub fn parse_module(path: &Path, content: &str) -> (HarvestStats, Result<ParseReport, ParseError>) {
    match clean_olean::source_world_for_file(path, None) {
        Ok(decision) => parse_module_in_world(path, content, &decision),
        Err(error) => (
            HarvestStats::default(),
            Err(ParseError::ModuleSyntaxRefused {
                line: 1,
                col: 0,
                message: error.to_string(),
            }),
        ),
    }
}

/// Parse using the entry file's already selected source/import decision.
pub fn parse_module_in_world(
    path: &Path,
    content: &str,
    decision: &clean_olean::SourceWorldDecision,
) -> (HarvestStats, Result<ParseReport, ParseError>) {
    let (seed, harvest) = seed_from_imports(path, content);
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    (
        harvest,
        clean_parser::parse_file_seeded_in_world(content, &patterns, &seed, decision.world()),
    )
}

/// A [`FileContext`] carrying `path`'s Lake `.olean` search paths and its
/// Lean main module ([`crate::entry_module_name`]) — the context `clean check`
/// starts an entry file from, so a `private` declaration gets the same
/// `_private.<module>.0.<name>` here (G21).
#[must_use]
pub fn module_file_context(path: &Path) -> FileContext {
    let mut file_ctx = FileContext::new();
    file_ctx.set_import_context_for_file(path);
    file_ctx.set_main_module(crate::entry_module_name(path));
    file_ctx
}

/// File context paired with [`parse_module_in_world`]'s exact decision.
#[must_use]
pub fn module_file_context_in_world(
    path: &Path,
    decision: &clean_olean::SourceWorldDecision,
) -> FileContext {
    let mut file_ctx = FileContext::new();
    file_ctx.set_source_world(path, decision);
    file_ctx.set_main_module(crate::entry_module_name(path));
    file_ctx
}

/// Arms the kernel's ambient per-declaration budget for as long as it lives
/// and disarms it on drop.
///
/// The budget is thread-local and threads are reused (libtest, rayon); a limit
/// left armed would silently bound unrelated later work on the same thread.
/// Arm it AFTER the environment is built: the budget bounds the declarations
/// of the file under check, not the fixed cost of the prelude.
#[must_use = "the budget is disarmed when the scope is dropped"]
pub struct DeclBudgetScope {
    _armed: (),
}

impl DeclBudgetScope {
    /// Arm `limit` kernel operations per declaration (`0` = unlimited).
    pub fn enter(limit: u64) -> Self {
        clean_kernel::tc::set_declaration_budget(limit);
        Self { _armed: () }
    }
}

impl Drop for DeclBudgetScope {
    fn drop(&mut self) {
        clean_kernel::tc::clear_declaration_budget();
    }
}

/// The process-wide lock every caller of
/// [`elaborate_decls`](super::elaborate_decls) holds while it runs.
///
/// `clean check` reports run TOTALS read off process-wide counters (the
/// `sorry` and kernel-failure counters behind `trust_summary`), and resets
/// them per run; two modules elaborating at once would pour into and reset
/// each other's totals. `clean check` also differences the process-wide
/// kernel-failure counter around every leaf
/// ([`ModuleObserver::kernel_failure_count`](super::ModuleObserver::kernel_failure_count)),
/// so its per-declaration verdicts depend on this lock too; the LSP and the
/// driver's default read the thread-scoped counter instead. Holders today:
/// `clean check` and `clean export-cert` (through `check_file_lock`) and the
/// LSP. `clean lake build`, `clean project check` and the `clean` crate's
/// `check_file` (which has a lock of its own) do not take it. A poisoned lock
/// is recovered: the guarded state is `()`.
pub fn module_elaboration_lock() -> MutexGuard<'static, ()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
}

#[cfg(test)]
mod import_base_tests {
    use super::with_import_base;
    use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility, TrustedEnvExt as _};
    use clean_kernel::inductive::{InductiveDecl, InductiveType};
    use clean_kernel::{Environment, Expr, Name};
    use std::collections::BTreeSet;

    #[test]
    fn selected_world_setup_does_not_trust_an_imported_false_axiom() {
        // Deliberately malformed imported evidence, not a native Lean oracle.
        // Capturing the base after this load would silently credit the axiom.
        let (env, base) = with_import_base(Environment::for_lean_replay(), |env| {
            env.add_inductive_core(InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: Name::from_string("WorldFixture.False"),
                    type_: Expr::prop(),
                    constructors: vec![],
                }],
            })
            .unwrap();
            assert!(env
                .extend_constants_structural(std::iter::once(ConstantInfo {
                    name: Name::from_string("WorldFixture.forgery"),
                    level_params: vec![],
                    type_: Expr::const_(Name::from_string("WorldFixture.False"), vec![]),
                    value: None,
                    is_reducible: false,
                    reducibility: Reducibility::Opaque,
                    kind: ConstantKind::Axiom,
                }))
                .is_empty());
            Ok(())
        })
        .unwrap();
        let name = Name::from_string("WorldFixture.forgery");
        assert!(base.get_const(&name).is_none());
        let verdict =
            clean_olean::ImportedConeGate::new(&base).check(&env, &BTreeSet::from([name]));
        assert!(!verdict.passed(false));
        assert!(
            !verdict.passed(true),
            "allow-sorry never admits a foreign axiom"
        );
        assert_eq!(verdict.imported_axioms, vec!["WorldFixture.forgery"]);
    }
}
