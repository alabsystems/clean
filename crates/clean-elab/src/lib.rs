// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// The elaborator keeps staged Lean compatibility and tactic APIs compiled
// before every downstream call path is wired; keep consumer builds quiet while
// narrower hygiene lints remain active.
//! clean Elaborator
//!
//! Converts surface syntax to kernel terms via:
//! - Type inference with metavariables
//! - Named to de Bruijn conversion
//! - Implicit argument insertion
//! - Type class instance resolution
//! - Macro expansion before elaboration
//!
//! # Example
//!
//! ```
//! use clean_elab::{elaborate, ElabCtx};
//! use clean_kernel::Environment;
//! use clean_parser::parse_expr;
//!
//! let env = Environment::new();
//! let mut ctx = ElabCtx::new(&env);
//! let surface = parse_expr("fun (x : Type) => x").unwrap();
//! let kernel_expr = ctx.elaborate(&surface).unwrap();
//! ```

pub mod agent_diagnostics;
pub mod attr_macro;
pub(crate) mod attr_macro_ext;
pub(crate) mod attr_scoping;
pub(crate) mod attr_scoping_integration;
pub(crate) mod attribute_ext;
pub(crate) mod attribute_ext2;
pub(crate) mod attribute_handlers;
pub mod attribute_registry;
pub(crate) mod attribute_registry_ext;
pub(crate) mod auto_bound;
pub(crate) mod auto_bound_ext;
pub(crate) mod auto_param_ext;
pub mod cert;
pub mod check_cmd;
#[cfg(feature = "cli")]
pub mod cli;
pub(crate) mod coercion;
pub(crate) mod coercion_ext;
pub(crate) mod coercion_ext2;
pub mod command_elab;
pub(crate) mod command_elab_ext;
pub mod command_elab_registry;
pub(crate) mod command_elab_registry_ext;
pub(crate) mod commands;
pub(crate) mod commands_ext;
pub(crate) mod dep_graph;
pub(crate) mod dep_graph_ext;
pub(crate) mod dep_graph_ext2;
pub(crate) mod dep_graph_ext2_impact;
pub mod derive;
pub(crate) mod derive_ext;
pub(crate) mod derive_ext2;
pub(crate) mod derive_ext_handlers;
pub(crate) mod derive_ext_handlers2;
pub mod derive_handlers;
pub(crate) mod derive_handlers_ext;
pub(crate) mod deriving_handlers;
pub(crate) mod diamond_resolution;
pub(crate) mod diamond_resolution_ext;
pub(crate) mod do_notation;
pub(crate) mod do_notation_desugar;
pub(crate) mod do_notation_desugar_control;
pub(crate) mod do_notation_desugar_ext;
pub(crate) mod do_notation_ext;
pub mod elab_cmd;
pub mod elab_hooks;
pub(crate) mod elab_hooks_ext;
pub(crate) mod env_snapshot;
pub(crate) mod env_snapshot_ext;
pub(crate) mod error;
pub mod eval_cmd;
pub(crate) mod eval_cmd_ext;
pub(crate) mod eval_cmd_ext2;
pub(crate) mod ffi_extern;
pub(crate) mod ffi_extern_ext;
pub(crate) mod file_context;
pub(crate) mod hetero_bridge_seed;
pub(crate) mod imports;
pub(crate) mod inductive_ext;
pub(crate) mod inductive_ext2;
pub(crate) mod inductive_ext_elab;
pub(crate) mod infer;
pub(crate) mod instance_priority;
pub(crate) mod instance_priority_ext;
pub(crate) mod instance_priority_ext2;
pub mod instance_resolution;
pub mod instance_synthesis;
pub(crate) mod instances;
pub(crate) mod instances_ext;
pub mod io_bridge;
pub(crate) mod io_monad;
pub(crate) mod io_monad_ext;
pub(crate) mod io_monad_ext2;
pub(crate) mod let_rec;
pub(crate) mod let_rec_ext;
pub(crate) mod let_rec_ext2;
pub mod macro_cmd;
pub(crate) mod macro_cmd_ext;
pub(crate) mod macro_hygiene;
pub(crate) mod macro_hygiene_ext;
pub(crate) mod macro_hygiene_ext2;
pub(crate) mod macro_hygiene_ext3;
pub(crate) mod macro_integration;
pub(crate) mod meta;
pub(crate) mod meta_ext;
pub(crate) mod mutual_decl;
pub(crate) mod mutual_decl_ext;
pub(crate) mod mutual_decl_ext2;
pub(crate) mod mutual_decl_ext3;
pub(crate) mod mutual_inductive;
pub(crate) mod mutual_inductive_ext;
pub(crate) mod mutual_recursion_desugar;
pub(crate) mod name_resolution;
pub(crate) mod name_resolution_ext;
pub(crate) mod name_resolution_ext2;
pub mod namespace;
pub(crate) mod namespace_ext;
pub(crate) mod namespace_open;
pub mod notation;
pub(crate) mod notation_ext;
pub(crate) mod notation_priority;
pub(crate) mod notation_priority_ext;
pub(crate) mod notation_scope;
pub(crate) mod notation_scope_ext;
pub(crate) mod notation_scope_ext2;
pub mod options_registry;
pub(crate) mod options_registry_ext;
#[cfg(test)]
mod test_env;
// Unwired roadmap prototype. Keep its unit coverage available without making
// placeholder match compilation part of the production elaborator surface.
#[cfg(test)]
pub(crate) mod pattern_match_ext;
mod prelude_providers;
pub(crate) mod preprocess;
pub(crate) mod preprocess_ext;
pub(crate) mod print_cmd;
pub(crate) mod proj_recursion;
pub mod register;
pub(crate) mod register_ext;
pub(crate) mod registration_warning;
pub(crate) mod section_scope;
pub(crate) mod section_scope_ext;
pub(crate) mod section_variable_ext;
pub(crate) mod section_variable_ext2;
pub(crate) mod structure_cmd;
pub(crate) mod structure_cmd_ext;
pub(crate) mod structure_extend;
pub(crate) mod structure_extend_ext;
pub(crate) mod structure_inherit;
pub(crate) mod structure_inherit_ext;
pub(crate) mod structure_inherit_ext2;
pub mod syntax_cmd;
pub mod tactic;
pub(crate) mod tc_outparam;
pub(crate) mod tc_outparam_ext;
pub(crate) mod tc_synthesis_ext;
pub(crate) mod tc_synthesis_ext2;
pub mod term_elab_registry;
pub(crate) mod unify;
pub(crate) mod unify_ext;
pub(crate) mod universe_constraint_ext;
pub(crate) mod universe_poly;
pub(crate) mod universe_poly_ext;
pub(crate) mod universe_poly_ext2;
pub(crate) mod variable_cmd;
pub(crate) mod variable_cmd_ext;
pub(crate) mod where_clause;
pub(crate) mod where_clause_ext;
pub(crate) mod where_desugar;
pub(crate) mod where_desugar_ext;

// These recovery implementations are unwired roadmap prototypes. Compile them
// only with their unit tests until the live pipeline owns their trust policy.
#[cfg(test)]
pub(crate) mod error_recovery;
#[cfg(test)]
pub(crate) mod error_recovery_ext;
#[cfg(test)]
pub(crate) mod error_recovery_ext2;
pub(crate) mod implicit_args;
pub(crate) mod implicit_args_ext;
pub(crate) mod info_tree;
pub(crate) mod info_tree_ext;
pub(crate) mod lean4_compat;
pub(crate) mod lean4_compat_ext;
pub(crate) mod lean4_compat_ext2;
pub(crate) mod string_interp_ext;
pub(crate) mod string_interpolation;
pub(crate) mod tactic_interp_ext;
pub(crate) mod tactic_interp_profile;

#[cfg(test)]
pub(crate) mod test_support;

#[cfg(test)]
#[path = "error_recovery_tests.rs"]
mod error_recovery_tests;

#[cfg(test)]
#[path = "error_recovery_ext_tests.rs"]
mod error_recovery_ext_tests;

#[cfg(test)]
#[path = "error_recovery_ext2_tests.rs"]
mod error_recovery_ext2_tests;

#[cfg(test)]
#[path = "info_tree_tests.rs"]
mod info_tree_tests;

#[cfg(test)]
#[path = "info_tree_ext_tests.rs"]
mod info_tree_ext_tests;

use clean_kernel::{env::TrustedEnvExt, Name};

// Re-export extracted types at crate root for backwards compatibility
use derive_handlers::register_user_derive_handler;
pub use error::{ElabElabError, ElabError};
pub use file_context::FileContext;
pub use imports::{
    lake_import_search_paths_for_file, nearest_lake_root_for_file, olean_available_for_module,
    process_imports, resolve_intra_project_import,
};
pub use preprocess::preprocess_decl_with_context;
#[cfg(not(test))]
use register::register_elab_result;
#[cfg(test)]
pub(crate) use register::register_elab_result;
pub use register::{kernel_check_failure_count, register_aesop_rule};

// =============================================================================
// Stack overflow protection for deep recursion
// =============================================================================

/// Minimum stack space to reserve before recursive calls (32 KB).
const MIN_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack size to grow to when running low (1 MB).
const STACK_GROWTH_SIZE: usize = 1024 * 1024;

/// Stack-safe recursive call wrapper.
///
/// Mirrors the kernel's `stack_safe` pattern (`clean-kernel/src/expr/mod.rs`).
/// Before executing the closure, checks remaining stack space against
/// `MIN_STACK_RED_ZONE` and spawns a new thread with `STACK_GROWTH_SIZE`
/// if running low.
///
/// # REQUIRES
/// - `stacker` crate must be a dependency
///
/// # ENSURES
/// - Closure is called exactly once
/// - Provides stack overflow protection for deep recursion
#[inline(always)]
pub(crate) fn stack_safe<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(MIN_STACK_RED_ZONE, STACK_GROWTH_SIZE, f)
}

pub use check_cmd::CheckResult as EnhancedCheckResult;
pub use check_cmd::{check_expression, check_name};
pub use commands::{CheckResult, EvalResult, PrintResult};
pub use eval_cmd::{eval_expression, EvalResult as EnhancedEvalResult};
pub use infer::{
    ClassRegistration, CommandOutput, DerivedInstance, ElabCtx, ElabResult, HoleContext,
};
pub use instances::{ClassInfo, InstanceInfo, InstanceTable, DEFAULT_PRIORITY};
pub use macro_integration::{
    expand_surface_macros, surface_to_syntax, syntax_to_surface, MacroCtx, MacroExpansionError,
};
pub use meta::{FreshMVarQ, MetaCtx, SynthInstanceQResult, TransparencyMode};
pub use print_cmd::{print_declaration, DeclKind, PrintResult as EnhancedPrintResult};
pub use registration_warning::{
    RegisteredElabResult, RegistrationWarning, RegistrationWarningKind,
};
pub use tactic::{
    apply, assumption, constructor, exact, intro, intros, rfl, Goal, LocalDecl, ProofState,
    RewriteCandidate, TacticError, TacticResult,
};
pub use unify::{MetaId, MetaState, MetaVar, Unifier, UnifyResult};

/// Domain-prefixed alias for collision-free imports.
///
/// Use `ElabLocalDecl` when importing from multiple crates with `LocalDecl` types.
pub use tactic::LocalDecl as ElabLocalDecl;

/// Common imports for elaboration users.
///
/// # Example
///
/// ```rust
/// use clean_elab::prelude::*;
///
/// let env = clean_kernel::Environment::new();
/// let mut ctx = ElabCtx::new(&env);
/// // ... elaborate expressions
/// ```
pub mod prelude {
    pub use crate::meta::{MetaCtx, TransparencyMode};
    pub use crate::tactic::{
        apply, assumption, constructor, exact, intro, intros, rfl, Goal, LocalDecl, ProofState,
        RewriteCandidate, TacticError, TacticResult,
    };
    pub use crate::unify::{MetaId, MetaState, MetaVar, Unifier, UnifyResult};
    pub use crate::{
        elaborate, elaborate_decl, elaborate_decl_and_register,
        elaborate_decl_and_register_with_context, elaborate_decl_and_register_with_warning,
        preprocess_decl_with_context, ElabCtx, ElabError, ElabResult, FileContext,
        RegisteredElabResult, RegistrationWarning, RegistrationWarningKind,
    };
}

/// Elaborate surface syntax to kernel expression
///
/// # REQUIRES
/// - `env` is a valid Environment with required types (Nat, Bool, etc. if used)
/// - `surface` is a valid surface expression from the parser
///
/// # ENSURES
/// - On success, returns kernel `Expr` with de Bruijn indices
/// - Metavariables are resolved during elaboration
/// - Universe levels are inferred and resolved
pub fn elaborate(
    env: &clean_kernel::Environment,
    surface: &clean_parser::SurfaceExpr,
) -> Result<clean_kernel::Expr, ElabError> {
    let mut ctx = ElabCtx::new(env);
    ctx.elaborate(surface)
}

/// Elaborate a surface declaration to a kernel declaration result
///
/// # REQUIRES
/// - Same as `elaborate`
///
/// # ENSURES
/// - On success, returns `ElabResult` variant matching declaration type
/// - Declaration name is extracted and validated
pub fn elaborate_decl(
    env: &clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
) -> Result<ElabResult, ElabError> {
    let mut ctx = ElabCtx::new(env);
    ctx.elab_decl(decl)
}

/// Elaborate a declaration (without kernel registration) and return both the
/// elaboration result and the hole contexts captured during elaboration.
///
/// Unlike [`elaborate_decl_and_register_with_warning`], this does **not**
/// register the declaration, so it surfaces hole contexts even for declarations
/// that would fail kernel registration — most notably a declaration containing
/// an unfilled `_` hole, whose unsolved metavariable is a free variable the
/// kernel rejects. That is precisely the case an IDE needs: the user is hovering
/// a hole they have not yet filled in.
///
/// The returned `Vec<HoleContext>` is always populated from the elaboration
/// state regardless of whether `result` is `Ok` or `Err`, so callers can show
/// hole goals even when the surrounding term does not fully type-check.
///
/// IDE-surface only: nothing is added to `env`.
pub fn elaborate_decl_capturing_holes(
    env: &clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
) -> (Result<ElabResult, ElabError>, Vec<HoleContext>) {
    let mut ctx = ElabCtx::new(env);
    let result = ctx.elab_decl(decl);
    let hole_contexts = ctx.collect_hole_contexts();
    (result, hole_contexts)
}

/// Elaborate a surface declaration and register any aesop rules
///
/// This is the primary entry point for elaborating declarations with attributes.
/// It handles the full lifecycle:
/// 1. Processes imports to initialize appropriate Mathlib stubs
/// 2. Elaborates the declaration
/// 3. Registers any `@[aesop ...]` attributes as rules in the environment
/// 4. Returns the elaboration result
///
/// # REQUIRES
/// - `env` is a mutable Environment
/// - `decl` is a valid surface declaration
///
/// # ENSURES
/// - On success, declaration is added to `env`
/// - Aesop rules (if any) are registered in `env`
/// - Import declarations initialize appropriate stubs
/// - Returns `ElabResult` indicating what was done
///
/// # Example
/// ```text
/// let decl = parse_decl("@[aesop safe apply] theorem my_intro : A → B := sorry")?;
/// let result = elaborate_decl_and_register(&mut env, &decl)?;
/// // The aesop rule is now registered in env
/// ```
pub fn elaborate_decl_and_register(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
) -> Result<ElabResult, ElabError> {
    Ok(elaborate_decl_and_register_with_warning(env, decl)?.result)
}

/// Elaborate a declaration with file-level context that persists namespace state.
///
/// Unlike [`elaborate_decl_and_register`], this variant carries namespace state
/// (from `open` and `export` commands) across declarations via [`FileContext`].
/// Use this when processing a sequence of declarations from a single file:
///
/// ```text
/// let mut file_ctx = FileContext::new();
/// for decl in parse_file(code)? {
///     let processed = preprocess_decl_with_context(&decl, &mut file_ctx);
///     elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)?;
/// }
/// ```
///
/// After `open Nat`, subsequent calls will resolve `add` as `Nat.add`.
///
/// # REQUIRES
/// - `env` is a mutable Environment
/// - `decl` is a valid surface declaration (typically pre-processed via
///   [`preprocess_decl_with_context`])
/// - `file_ctx` tracks accumulated variables, universe params, and namespace state
///
/// # ENSURES
/// - On success, declaration is added to `env`
/// - Namespace state from `open`/`export` is persisted in `file_ctx`
pub fn elaborate_decl_and_register_with_context(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    file_ctx: &mut FileContext,
) -> Result<ElabResult, ElabError> {
    Ok(elaborate_decl_and_register_inner(env, decl, Some(file_ctx))?.result)
}

/// Elaborate, register, and return both the result and any trust warning,
/// while threading namespace / option state through a `FileContext`.
pub fn elaborate_decl_and_register_with_context_and_warning(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    file_ctx: &mut FileContext,
) -> Result<RegisteredElabResult, ElabError> {
    elaborate_decl_and_register_inner(env, decl, Some(file_ctx))
}

/// Elaborate a surface declaration, register it, and return any trust warnings.
///
/// This is the report-returning variant of [`elaborate_decl_and_register`].
/// After successful registration, it queries the kernel's stored declaration
/// trust summary provenance and returns a [`RegisteredElabResult`] containing both the
/// elaboration result and an optional [`RegistrationWarning`].
///
/// The warning selection policy preserves Lean 4's `warnIfUsesSorry`
/// priority for explicit vs synthetic `sorry`, while also surfacing
/// `trustedArith` and `trustedAy` debt when no sorry is present.
///
/// # REQUIRES
/// - `env` is a mutable Environment
/// - `decl` is a valid surface declaration
///
/// # ENSURES
/// - On success, declaration is added to `env`
/// - Warning is computed only after successful registration
/// - If attribute registration fails, no stale warning is returned
pub fn elaborate_decl_and_register_with_warning(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
) -> Result<RegisteredElabResult, ElabError> {
    elaborate_decl_and_register_inner(env, decl, None)
}

/// Internal implementation shared by all `elaborate_decl_and_register*` variants.
///
/// When `file_ctx` is `Some`, namespace state is injected into the `ElabCtx`
/// before elaboration and extracted back afterward so `open`/`export` aliases
/// persist across declarations.
fn elaborate_decl_and_register_inner(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    file_ctx: Option<&mut FileContext>,
) -> Result<RegisteredElabResult, ElabError> {
    elaborate_decl_and_register_inner_with_aux(env, decl, file_ctx, None)
}

/// Build an [`ElabResult::Failed`] leaf for an inner declaration (a member of a
/// `namespace`/`section`/`mutual` block) whose elaboration or kernel check
/// failed.
///
/// The leaf carries a best-effort, namespace-qualified name (so reporting shows
/// e.g. `T.b` rather than the bare short name), a clone of the inner surface
/// declaration (for span-accurate diagnostics), and the original error. It is
/// deliberately NOT registered into the kernel — it stands for a decl that
/// already failed — but it IS a counted leaf so the failure is tallied and
/// reported, never silently dropped.
fn failed_inner_leaf(
    fc: &FileContext,
    inner: &clean_parser::SurfaceDecl,
    error: ElabError,
) -> ElabResult {
    let short = preprocess_ext::decl_name(inner).unwrap_or("");
    let ns = fc.namespace_state().current_namespace();
    let qualified = if short.is_empty() {
        ns.to_string()
    } else if ns.is_anon() {
        short.to_string()
    } else {
        format!("{ns}.{short}")
    };
    ElabResult::Failed {
        name: qualified,
        decl: Box::new(inner.clone()),
        error: Box::new(error),
    }
}

/// Record `local instance` / `scoped instance` registrations from a
/// just-registered elaboration result into the `FileContext` (B99).
///
/// - `local instance` → recorded at the current local-scope depth; retired
///   (hidden from all later resolution) when that section/namespace block
///   ends. Previously the modifier was silently DROPPED, so a `local
///   instance` leaked past `end` (r82 `instprio_local_section_shadow`:
///   9 provable outside the section where Lean proves 5).
/// - `scoped instance` → recorded with its declaring namespace (the current
///   namespace at registration); visible only while that namespace is
///   current or opened. Previously registered as if global (r82
///   `instprio_scoped_open_in`: 2 provable without `open` where Lean
///   proves 1).
///
/// `Multiple` results (namespace/section blocks) are walked recursively;
/// every other result kind carries no instance scope.
fn record_instance_scopes(fc: &mut FileContext, result: &ElabResult) {
    use clean_parser::DeclScope;
    match result {
        ElabResult::Instance {
            name, modifiers, ..
        } => match modifiers.scope {
            DeclScope::Local => fc.record_local_instance(name.clone()),
            DeclScope::Scoped => {
                let ns = fc.namespace_state().current_namespace().clone();
                fc.record_scoped_instance(name.clone(), ns);
            }
            DeclScope::Default => {}
        },
        ElabResult::Multiple(results) => {
            for inner in results {
                record_instance_scopes(fc, inner);
            }
        }
        _ => {}
    }
}

/// Track AA: like [`elaborate_decl_and_register_inner`] but installs an optional
/// auxiliary-arm source on the `ElabCtx` before elaborating `decl`. Used to fuse
/// a nested-mutual fold's primary def through `T.rec` with the sibling's arms
/// filling the auxiliary minors. `aux_source` is `(container_short, aux_arms,
/// member_names)`; `None` leaves the standard path byte-for-byte unchanged.
fn elaborate_decl_and_register_inner_with_aux(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    mut file_ctx: Option<&mut FileContext>,
    aux_source: Option<(String, Vec<clean_parser::SurfaceMatchArm>, Vec<String>)>,
) -> Result<RegisteredElabResult, ElabError> {
    env.init_pprod().ok();
    // B101: seed the Lean-core `instHAdd`/`instHMul`/`instHSub` bridge
    // instances (kernel-checked; idempotent; skipped when the constants
    // already exist, e.g. via olean import) so user `Add`/`Mul`/`Sub`
    // instances are reachable through their operators.
    hetero_bridge_seed::seed_hetero_bridges(env);

    // Handle declare_aesop_rule_sets directly (before creating immutable borrow)
    if let clean_parser::SurfaceDecl::DeclareAesopRuleSets { names, .. } = decl {
        for name in names {
            let n = Name::from_string(name);
            env.declare_aesop_rule_set(n);
        }
        return Ok(RegisteredElabResult {
            result: ElabResult::Skipped,
            warning: None,
            hole_contexts: Vec::new(),
        });
    }

    // Handle imports: initialize appropriate Mathlib stubs
    if let clean_parser::SurfaceDecl::Import { paths, .. } = decl {
        let external_enabled = file_ctx
            .as_ref()
            .map(|fc| fc.external_import_search_enabled())
            .unwrap_or(true);
        if !external_enabled {
            // Clean-native authority check: skip Lake/.olean search and
            // initialize only Clean's built-in module preludes.
            imports::process_imports_clean_native(env, paths)?;
        } else if let Some(fc) = file_ctx.as_deref_mut() {
            // Use Lake-discovered search paths if available. Thread the file's
            // persistent `import_visited` set through every import so a Mathlib
            // file's large overlapping `.olean` closures are read once, not
            // re-read per top-level import (O(n²) → O(union)). Clone the search
            // paths (a file has few — just PathBufs) into a local so the
            // immutable `import_search_paths()` borrow does not conflict with
            // the mutable `import_visited_mut()` borrow of the same `fc`.
            let local_paths = fc.import_search_paths().to_vec();
            imports::process_imports_with_search_paths_shared(
                env,
                paths,
                &local_paths,
                fc.import_visited_mut(),
            )?;
        } else {
            process_imports(env, paths)?;
        }
        return Ok(RegisteredElabResult {
            result: ElabResult::Skipped,
            warning: None,
            hole_contexts: Vec::new(),
        });
    }

    if let clean_parser::SurfaceDecl::SetOption {
        name, value, body, ..
    } = decl
    {
        // Drop-in: tolerate an UNKNOWN option NAME as a no-op (Lean registers
        // many options Clean does not model — genInjectivity, linter.*); the
        // wrapped/subsequent decls must still elaborate. A KNOWN option with a
        // wrongly-typed value stays a loud error. See
        // `validate_command_option_lenient`.
        let _known = options_registry::validate_command_option_lenient(name, value.as_deref())?;
        if let Some(inner_decl) = body {
            // Per-declaration scoping: `set_option ... in <decl>`
            // Save previous value, set the option, elaborate the body, then restore.
            let prev = env.get_option(name).cloned();
            env.set_option(name.clone(), value.clone());
            let result = elaborate_decl_and_register_inner(env, inner_decl, file_ctx);
            // Restore previous option state
            match prev {
                Some(old_value) => {
                    env.set_option(name.clone(), old_value);
                }
                None => {
                    env.remove_option(name);
                }
            }
            return result;
        }
        // File-scope: option persists for all subsequent declarations
        env.set_option(name.clone(), value.clone());
        // Also persist in FileContext for section scoping
        if let Some(ref mut fc) = file_ctx {
            fc.set_option(name.clone(), value.clone());
        }
        return Ok(RegisteredElabResult {
            result: ElabResult::Skipped,
            warning: None,
            hole_contexts: Vec::new(),
        });
    }

    // Handle section blocks the same resilient, incremental way as namespace
    // blocks below, but with SECTION scope semantics.
    //
    // SOUNDNESS (#section-drops-all-but-last / namespace-ABORT lineage — see the
    // `elab_section` SOUNDNESS comment in infer/elaborate_decl.rs): the ElabCtx
    // path `elab_section` did `return Err(e)` on the FIRST failing inner decl,
    // discarding every good sibling. A real Mathlib module puts its ENTIRE file
    // body inside ONE unclosed `@[expose] public section` (no matching `end`), so
    // a single inner-decl failure collapsed the whole file to `decl_count == 1`.
    // `InferCtx.env` is `&Environment` (immutable), so `elab_section` physically
    // CANNOT register inners incrementally; therefore the fix lives HERE, where
    // `&mut env` is available, mirroring the namespace arm: each inner decl is
    // registered into `env` BEFORE the next (so later siblings resolve earlier
    // ones), a sibling failure becomes an explicit `ElabResult::Failed` leaf
    // (counted + reported, never silently swallowed) instead of aborting, and
    // every successful inner still flows through `add_decl`'s real kernel check.
    // No kernel/TCB code is touched. Matches Lean, which reports per-declaration
    // and continues.
    if let clean_parser::SurfaceDecl::Section { decls, .. } = decl {
        let mut results = Vec::new();
        let mut hole_contexts = Vec::new();
        // As in the namespace arm: when there is no persistent FileContext, use a
        // throwaway one so section scoping / variable threading still works.
        let mut temp_fc;
        let fc_ref: &mut FileContext = match file_ctx {
            Some(ref mut fc) => fc,
            None => {
                temp_fc = FileContext::new();
                &mut temp_fc
            }
        };
        // A `section` scopes `variable` / `universe` / `set_option` (via
        // `enter_section` / `exit_section`) AND `open` aliases — a section-level
        // `open Foo` is in force WITHIN the section but rolled back at `end`
        // (Lean `elabEnd` pops the section scope). It differs from a namespace
        // only in NOT adding a name PREFIX (so no enter_namespace here). Push an
        // alias scope like the namespace arm so section-level `open`s don't leak
        // past `end` (open_export_e2e::test_open_in_section_does_not_leak).
        fc_ref.enter_section();
        fc_ref.namespace_state_mut().push_scope();
        for inner in decls {
            // Thread section `variable` binders exactly as the top-level
            // section-marker path in `cmd_core` does: a `variable (x : T)` inner
            // mutates `fc_ref` via `add_variables`, and a later `def` / `theorem`
            // gets those binders prepended.
            //
            // A NESTED `section` inner must NOT be preprocessed here:
            // `preprocess_decl_with_context` calls `enter_section` AND the
            // recursive Section arm calls it again, so the inner section's
            // variable / option scope frame would be double-pushed and mismatched
            // on exit (leaking its `variable`s / `set_option`s to later siblings).
            // Nested sections self-manage their scope through this same arm, so
            // pass them through raw — mirroring how the namespace arm never
            // preprocesses its inners.
            let processed = if matches!(inner, clean_parser::SurfaceDecl::Section { .. }) {
                None
            } else {
                Some(crate::preprocess::preprocess_decl_with_context(
                    inner, fc_ref,
                ))
            };
            let to_elab = processed.as_ref().unwrap_or(inner);
            // COLLECT per-inner outcomes instead of `?`-aborting on the first
            // failure. A sibling failure must NOT drop the good siblings.
            match elaborate_decl_and_register_inner(env, to_elab, Some(fc_ref)) {
                Ok(inner_result) => {
                    hole_contexts.extend(inner_result.hole_contexts);
                    if !matches!(inner_result.result, ElabResult::Skipped) {
                        results.push(inner_result.result);
                    }
                }
                Err(error) => {
                    // Report against the ORIGINAL `inner` (span-accurate), not the
                    // preprocessed clone — matches the namespace arm.
                    results.push(failed_inner_leaf(fc_ref, inner, error));
                }
            }
        }
        // Pop the alias scope (roll back section-level `open`s) and restore
        // section-scoped `set_option`s in BOTH `fc_ref` and the kernel env
        // (`apply_options_to_env` only ever adds — a section-scoped option would
        // otherwise leak past the section).
        fc_ref.namespace_state_mut().pop_scope();
        fc_ref.exit_section_restoring_env_options(env);
        return Ok(RegisteredElabResult {
            result: ElabResult::Multiple(results),
            warning: None,
            hole_contexts,
        });
    }

    // Handle namespace blocks by processing each inner declaration individually
    // through the full elaborate-and-register pipeline (#3410). This ensures that
    // each declaration is registered in the environment before the next one is
    // elaborated, allowing cross-references between sibling declarations within
    // the same namespace (e.g., `def baz := bar` after `def bar := 0`).
    if let clean_parser::SurfaceDecl::Namespace { name, decls, .. } = decl {
        let mut results = Vec::new();
        let mut hole_contexts = Vec::new();
        // When file_ctx is None, create a temporary FileContext to carry the
        // namespace state through the inner declarations. This ensures
        // qualify_name() works even without a persistent file context.
        let mut temp_fc;
        let fc_ref: &mut FileContext = match file_ctx {
            Some(ref mut fc) => fc,
            None => {
                temp_fc = FileContext::new();
                &mut temp_fc
            }
        };
        fc_ref
            .namespace_state_mut()
            .enter_namespace(Name::from_string(name));
        // The namespace block is an alias-scope boundary (Lean pushes a Scope
        // per `namespace`; `end` pops it and discards its `open` decls). An
        // `open` inside the block must not leak past `end Foo` (gap sweep B13);
        // `export` aliases are inserted scope-immune and survive.
        fc_ref.namespace_state_mut().push_scope();
        // A namespace block is also a `local`-attribute scope boundary (B99):
        // a `local instance` declared inside dies at `end Foo`, exactly as in
        // a section.
        fc_ref.enter_local_scope();
        for inner in decls {
            // COLLECT per-inner outcomes instead of `?`-aborting on the first
            // failure (the namespace-ABORT bug). A sibling failure must NOT drop
            // the good siblings: each successful inner decl is still
            // individually elaborated and kernel-checked (and registered, so
            // later siblings can reference it), while each failure is recorded
            // as an explicit `ElabResult::Failed` leaf so it is still COUNTED and
            // REPORTED — never silently swallowed.
            match elaborate_decl_and_register_inner(env, inner, Some(fc_ref)) {
                Ok(inner_result) => {
                    // Preserve hole contexts from inner declarations so holes
                    // inside a namespace block remain visible to IDE surfaces.
                    hole_contexts.extend(inner_result.hole_contexts);
                    if !matches!(inner_result.result, ElabResult::Skipped) {
                        results.push(inner_result.result);
                    }
                }
                Err(error) => {
                    results.push(failed_inner_leaf(fc_ref, inner, error));
                }
            }
        }
        fc_ref.exit_local_scope();
        fc_ref.namespace_state_mut().pop_scope();
        fc_ref.namespace_state_mut().exit_namespace();
        return Ok(RegisteredElabResult {
            result: ElabResult::Multiple(results),
            warning: None,
            hole_contexts,
        });
    }

    // Recursion-through-projection desugaring (Track H, task 1): a recursive
    // method that matches on a *projection* of its sole decreasing binder and
    // rebuilds a wrapper around the smaller sub-component for the recursive
    // call. Split into an auxiliary equation-form def recursing structurally on
    // the projected field's inductive (lowered via the already-proven `T.rec`
    // path) plus a thin wrapper, then elaborate and register both in order —
    // exactly like the namespace path registers sibling decls one by one so the
    // wrapper can reference the auxiliary. Returns `None` (leaving the decl
    // untouched) for anything outside the conservative sound envelope.
    if let Some(split) = proj_recursion::desugar_projection_recursion(decl) {
        let mut results = Vec::new();
        let mut hole_contexts = Vec::new();
        for sub in &split {
            let sub_result = elaborate_decl_and_register_inner(env, sub, file_ctx.as_deref_mut())?;
            hole_contexts.extend(sub_result.hole_contexts);
            if !matches!(sub_result.result, ElabResult::Skipped) {
                results.push(sub_result.result);
            }
        }
        return Ok(RegisteredElabResult {
            result: ElabResult::Multiple(results),
            warning: None,
            hole_contexts,
        });
    }

    // Mutual structural recursion via product packing (Track H, task 2): a
    // `mutual` block whose members all recurse structurally on a single shared
    // inductive argument is lowered into ONE packed structural-recursive
    // function (returning a tuple of the components' results) plus projection
    // wrappers — with NO `WellFounded.fix`, `sorry`, or faked termination
    // axiom. The packed function reuses the already-proven equation-form `T.rec`
    // lowering verbatim. Register the synthesized decls in order (pack first,
    // then wrappers) so each wrapper can reference the pack. Returns `None`
    // (deferring to the existing `elab_mutual` path) for anything outside the
    // conservative sound envelope.
    if let clean_parser::SurfaceDecl::Mutual { decls: members, .. } = decl {
        if let Some(split) = mutual_recursion_desugar::desugar_mutual_structural(members) {
            let mut results = Vec::new();
            let mut hole_contexts = Vec::new();
            for sub in &split {
                let sub_result =
                    elaborate_decl_and_register_inner(env, sub, file_ctx.as_deref_mut())?;
                hole_contexts.extend(sub_result.hole_contexts);
                if !matches!(sub_result.result, ElabResult::Skipped) {
                    results.push(sub_result.result);
                }
            }
            return Ok(RegisteredElabResult {
                result: ElabResult::Multiple(results),
                warning: None,
                hole_contexts,
            });
        }

        // Track AA: a nested-mutual fold `{ T.f : T -> R, T.g : C T -> R }` (the
        // members recurse on DIFFERENT types — the parent inductive `T` and its
        // nested container `C T` — so the product-packing path above declines).
        // Fuse the pair into ONE `T.rec` application: `T.f` is elaborated through
        // the genuine nested mutual recursor with `T.g`'s arms filling the
        // auxiliary `T._<C>` minors (a real fold, NOT a degenerate default), then
        // `T.g` is registered against the now-defined `T.f`. NO `WellFounded.fix`,
        // NO `sorry`, NO faked termination axiom — the kernel re-checks the
        // recursor application. Declines (`None`) for anything outside the
        // envelope, deferring to the existing `elab_mutual` path.
        if let Some(fold) = mutual_recursion_desugar::desugar_mutual_nested(members) {
            let mut results = Vec::new();
            let mut hole_contexts = Vec::new();

            // Primary def: fused through `T.rec` with the auxiliary-arm source.
            let aux_source = Some((
                fold.container_short.clone(),
                fold.aux_arms.clone(),
                fold.member_names.clone(),
            ));
            let prim_result = elaborate_decl_and_register_inner_with_aux(
                env,
                &fold.primary_def,
                file_ctx.as_deref_mut(),
                aux_source,
            )?;
            hole_contexts.extend(prim_result.hole_contexts);
            if !matches!(prim_result.result, ElabResult::Skipped) {
                results.push(prim_result.result);
            }

            // Secondary def: `T.g` references the now-registered `T.f`; it folds
            // over the surface container `C T` with `T.f` calls on elements,
            // lowered through the ordinary `C.rec` structural path.
            let sec_result = elaborate_decl_and_register_inner(
                env,
                &fold.secondary_def,
                file_ctx.as_deref_mut(),
            )?;
            hole_contexts.extend(sec_result.hole_contexts);
            if !matches!(sec_result.result, ElabResult::Skipped) {
                results.push(sec_result.result);
            }

            return Ok(RegisteredElabResult {
                result: ElabResult::Multiple(results),
                warning: None,
                hole_contexts,
            });
        }
    }

    // Apply file-level option overrides to the environment before elaboration
    // so that options set in earlier declarations (including section-scoped ones)
    // are visible during type checking and elaboration.
    if let Some(ref fc) = file_ctx {
        fc.apply_options_to_env(env);
    }

    let mut ctx = ElabCtx::new(env);

    // Track AA: install the fused nested-mutual fold's auxiliary-arm source (if
    // any) so the nested-recursor minor builder fills the auxiliary minors with
    // the sibling's real fold body.
    ctx.set_nested_mutual_aux_arms(aux_source);

    // Inject persisted namespace state and namespace prefix from FileContext
    if let Some(ref file_ctx) = file_ctx {
        ctx.set_namespace_state(file_ctx.namespace_state().clone());
        // Instance scope state (B99): retired `local instance`s, `scoped
        // instance` namespaces, and the `@[default_instance]` table. All
        // empty unless the file actually used those forms.
        ctx.set_instance_scope_state(
            file_ctx.dead_local_instances().clone(),
            file_ctx.scoped_instance_map().clone(),
            file_ctx.default_instance_entries(),
        );
    }

    if let Some(ref mut file_ctx) = file_ctx {
        ctx.set_macro_ctx(file_ctx.take_macro_ctx());
        if let Some(tactic_registry) = file_ctx.take_tactic_registry() {
            ctx.set_tactic_registry(tactic_registry);
        }
        // `elab ... : term` registrations, persisted across declarations for the
        // same reason as the tactic registry above: ElabCtx is rebuilt per
        // declaration, so without this a registered term elaborator is dropped
        // before the next declaration can call it.
        ctx.set_user_term_elabs(file_ctx.take_user_term_elabs());
    }

    let result = ctx.elab_decl(decl);

    if let Some(ref mut file_ctx) = file_ctx {
        file_ctx.replace_macro_ctx(ctx.take_macro_ctx());
        file_ctx.replace_tactic_registry(ctx.take_tactic_registry());
        file_ctx.replace_user_term_elabs(ctx.take_user_term_elabs());
    }

    let result = result?;

    // Snapshot the hole contexts (expected types + locals for user-written `_`
    // holes) before dropping ctx. Read-only: this only inspects metavariable
    // types for IDE display and never affects what is registered in the kernel.
    let hole_contexts = ctx.collect_hole_contexts();

    // Collect all attributes before dropping ctx (releases immutable borrow of env)
    let aesop_attrs = ctx.take_aesop_attrs();
    let simp_attrs = ctx.take_simp_attrs();
    let reducibility_attrs = ctx.take_reducibility();
    let extern_attrs = ctx.take_extern();
    let export_attrs = ctx.take_export();
    let deprecated_attrs = ctx.take_deprecated();
    let inline_attrs = ctx.take_inline();
    let noinline_attrs = ctx.take_noinline();
    let always_inline_attrs = ctx.take_always_inline();
    let specialize_attrs = ctx.take_specialize();
    let csimp_attrs = ctx.take_csimp();
    let congr_attrs = ctx.take_congr();
    let ext_attrs = ctx.take_ext();
    let refl_attrs = ctx.take_refl();
    let symm_attrs = ctx.take_symm();
    let macro_inline_attrs = ctx.take_macro_inline();
    let inline_if_reduce_attrs = ctx.take_inline_if_reduce();
    let nospecialize_attrs = ctx.take_nospecialize();
    let implemented_by_attrs = ctx.take_implemented_by();
    let coe_attrs = ctx.take_coe();
    let match_pattern_attrs = ctx.take_match_pattern();
    let init_attrs = ctx.take_init();
    let default_instance_attrs = ctx.take_default_instance();
    let instance_attrs = ctx.take_instance_attrs();
    let derive_handler_attrs = ctx.take_derive_handler();
    let attribute_removals = ctx.take_attribute_removals();

    // Extract namespace state back to FileContext before dropping ctx.
    let ns_state = ctx.take_namespace_state();
    drop(ctx); // Release immutable borrow of env

    // Persist namespace state to FileContext (kept borrowed: the tail below
    // also records instance scope state into it — B99).
    if let Some(fc) = file_ctx.as_deref_mut() {
        *fc.namespace_state_mut() = ns_state;
    }

    // First register the declaration itself (so attributes can reference it)
    register_elab_result(env, &result)?;

    // Record `local` / `scoped` instance scope state into the FileContext
    // (B99). Must run AFTER successful registration (a rejected declaration
    // registers nothing, so it must not affect scope state) and reads the
    // just-persisted namespace state for the declaring namespace of `scoped`
    // instances.
    if let Some(fc) = file_ctx.as_deref_mut() {
        record_instance_scopes(fc, &result);
    }

    // Compute the warning after register_elab_result succeeds but before
    // returning, so we only report on actually-registered declarations.
    let warning = register::registration_warning_for_result(env, &result);

    // Register parameter names for named argument support (#1230)
    register::register_param_names(env, decl);

    // Now register attributes that reference the declaration

    // Register aesop rules
    for (name, attr) in aesop_attrs {
        register_aesop_rule(env, name, &attr);
    }

    // Register simp lemmas
    for (name, priority) in simp_attrs {
        env.register_simp_lemma(name, priority);
    }

    // Apply reducibility attributes
    // These override the default reducibility set at declaration time
    for (name, reducibility) in reducibility_attrs {
        env.set_reducibility(&name, reducibility);
    }

    // Register extern bindings
    for (decl_name, extern_name) in extern_attrs {
        env.register_extern(decl_name, extern_name);
    }

    // Register export bindings
    for (decl_name, export_name) in export_attrs {
        env.register_export(decl_name, export_name);
    }

    // Register deprecations
    for (name, msg) in deprecated_attrs {
        env.register_deprecated(name, msg);
    }

    // Register inline hints
    for name in inline_attrs {
        env.register_inline(name);
    }

    // Register noinline hints
    for name in noinline_attrs {
        env.register_noinline(name);
    }

    // Register always_inline hints
    for name in always_inline_attrs {
        env.register_always_inline(name);
    }

    // Register specialize hints
    for name in specialize_attrs {
        env.register_specialize(name);
    }

    // Register csimp lemmas
    for name in csimp_attrs {
        env.register_csimp(name);
    }

    // Register congr lemmas
    for name in congr_attrs {
        env.register_congr(name);
    }

    // Register ext lemmas
    for name in ext_attrs {
        env.register_ext(name);
    }

    // Register refl lemmas
    for name in refl_attrs {
        env.register_refl(name);
    }

    // Register symm lemmas
    for name in symm_attrs {
        env.register_symm(name);
    }

    // Register macro_inline hints
    for name in macro_inline_attrs {
        env.register_macro_inline(name);
    }

    // Register inline_if_reduce hints
    for name in inline_if_reduce_attrs {
        env.register_inline_if_reduce(name);
    }

    // Register nospecialize hints
    for name in nospecialize_attrs {
        env.register_nospecialize(name);
    }

    // Register @[implemented_by] bindings
    for (decl_name, impl_name) in implemented_by_attrs {
        let impl_n = Name::from_string(&impl_name);
        env.register_implemented_by(decl_name, impl_n);
    }

    // Register @[coe] coercions
    for name in coe_attrs {
        env.register_coercion(name);
    }

    // Register @[match_pattern] declarations
    for name in match_pattern_attrs {
        env.register_match_pattern(name);
    }

    // Register @[init] functions
    // Note: actual initialization execution requires IO runtime; we record the
    // registration so downstream consumers can query and execute init functions.
    for name in init_attrs {
        env.register_init_fn(name);
    }

    // Register @[default_instance] declarations (B99): record membership in
    // the kernel-side registry (pre-existing) AND the FileContext
    // default-instance table (class → entries with priority, declaration
    // order) that drives open-metavariable defaulting in instance
    // resolution. The class is read off the declaration type's conclusion
    // (like the `attribute [instance]` handler below); a conclusion without
    // a constant head cannot participate in class-goal defaulting, so only
    // the membership registry is updated for it (unchanged behavior).
    for (name, priority) in default_instance_attrs {
        if let Some(fc) = file_ctx.as_deref_mut() {
            let conclusion_class = env.get_const(&name).and_then(|info| {
                let mut conclusion = &info.type_;
                while let clean_kernel::ExprKind::Pi(_, _, body) = conclusion.kind() {
                    conclusion = body;
                }
                crate::instances::extract_class_app(conclusion).map(|(class_name, _)| class_name)
            });
            if let Some(class_name) = conclusion_class {
                fc.record_default_instance(name.clone(), class_name, priority);
            }
        }
        env.register_default_instance(name);
    }

    // Register `attribute [instance] foo` / `@[instance N] def foo` targets as
    // type class instances (B06; sweep row classes_instances/p14). Lean ground
    // truth: the `instance` attribute calls `addInstance`
    // (lean4 `src/Lean/Meta/Instances.lean`) after validating that the
    // declaration's type concludes in a class application. The class name is
    // read off the target type's conclusion; a non-class conclusion is a LOUD
    // error, exactly like Lean's "invalid 'instance' attribute". Duplicate
    // registration (e.g. re-running the attribute command) is a no-op.
    for (name, priority) in instance_attrs {
        if env.is_instance(&name) {
            continue;
        }
        let target_ty = env
            .get_const(&name)
            .map(|info| info.type_.clone())
            .ok_or_else(|| {
                ElabError::UnknownIdent(format!("attribute [instance] target {name}"))
            })?;
        let mut conclusion = &target_ty;
        while let clean_kernel::ExprKind::Pi(_, _, body) = conclusion.kind() {
            conclusion = body;
        }
        let class_name = crate::instances::extract_class_app(conclusion)
            .map(|(class_name, _)| class_name)
            .filter(|class_name| env.get_class_info(class_name).is_some())
            .ok_or_else(|| ElabError::Unsupported {
                feature: format!(
                    "attribute [instance]: type of `{name}` does not conclude in a \
                     registered class (got `{conclusion}`)"
                ),
            })?;
        env.register_instance(clean_kernel::KernelInstanceInfo {
            name,
            class_name,
            priority,
            type_: None,
            value: None,
        });
    }

    // Register @[derive_handler] declarations.
    for name in derive_handler_attrs {
        register_user_derive_handler(env, &name)?;
    }

    for (name, attr_name) in attribute_removals {
        match attr_name.as_str() {
            "simp" => {
                if !env.unregister_simp_lemma(&name) {
                    return Err(ElabError::Unsupported {
                        feature: format!("cannot remove @[{attr_name}]: not applied to '{}'", name),
                    });
                }
            }
            _ => {
                return Err(ElabError::Unsupported {
                    feature: format!("attribute removal for '[-{attr_name}]' is not supported"),
                });
            }
        }
    }

    Ok(RegisteredElabResult {
        result,
        warning,
        hole_contexts,
    })
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "derive_tests.rs"]
mod derive_tests;

#[cfg(test)]
#[path = "beq_recursive_tests.rs"]
mod beq_recursive_tests;

#[cfg(test)]
#[path = "let_tactic_body_visible_tests.rs"]
mod let_tactic_body_visible_tests;

#[cfg(test)]
#[path = "decidable_eq_fielded_tests.rs"]
mod decidable_eq_fielded_tests;

#[cfg(test)]
#[path = "decidable_eq_trackt_tests.rs"]
mod decidable_eq_trackt_tests;

#[cfg(test)]
#[path = "deriving_trackp_tests.rs"]
mod deriving_trackp_tests;

#[cfg(test)]
#[path = "derive_ext_tests.rs"]
mod derive_ext_tests;

#[cfg(test)]
mod macro_hygiene_tests;

#[cfg(test)]
mod tests_state_t_issue_3418;

#[cfg(test)]
mod mutual_recursion_desugar_tests;

#[cfg(test)]
mod mutual_inductive_elab_tests;

#[cfg(test)]
mod proj_recursion_tests;

#[cfg(test)]
mod dot_notation_pi_receiver_tests;

#[cfg(test)]
#[path = "track_r_basic_tests.rs"]
mod track_r_basic_tests;

#[cfg(test)]
#[path = "track_t_fixfv2_tests.rs"]
mod track_t_fixfv2_tests;

#[cfg(test)]
#[path = "track_aa_nested_fold_tests.rs"]
mod track_aa_nested_fold_tests;

#[cfg(test)]
mod tests_issue_3435;

#[cfg(test)]
mod tests_issue_3517;

#[cfg(test)]
mod tests_cases_dependent_motive;

#[cfg(test)]
mod tests_result_only_implicit;

#[cfg(test)]
mod tests_issue_3527;

#[cfg(test)]
mod tests_issue_3534;

#[cfg(test)]
mod wave0_tests;

#[cfg(test)]
mod tests_close_fvars_seq_focus;

#[cfg(test)]
mod tests_instance_candidate_hygiene;

#[cfg(test)]
mod tests_lean_fidelity_shapes;

#[cfg(test)]
mod tests_cases_imported_cases_on;

#[cfg(test)]
mod namespace_3410_tests;

#[cfg(test)]
mod lean4_corpus_tests;

#[cfg(test)]
#[path = "attr_macro_ext_tests.rs"]
mod attr_macro_ext_tests;

#[cfg(test)]
mod attr_scoping_tests;

#[cfg(test)]
mod attribute_wiring_tests;

#[cfg(test)]
mod structure_cmd_tests;

#[cfg(test)]
#[path = "structure_cmd_ext_tests.rs"]
mod structure_cmd_ext_tests;

#[cfg(test)]
mod do_notation_tests;

#[cfg(test)]
mod do_notation_desugar_tests;

#[cfg(test)]
mod do_notation_ext_tests;

#[cfg(test)]
#[path = "do_notation_desugar_ext_tests.rs"]
mod do_notation_desugar_ext_tests;

#[cfg(test)]
mod string_interpolation_tests;

#[cfg(test)]
mod lean4_compat_tests;

#[cfg(test)]
#[path = "lean4_compat_ext2_tests.rs"]
mod lean4_compat_ext2_tests;

#[cfg(test)]
mod auto_bound_tests;

#[cfg(test)]
mod auto_bound_ext_tests;

// NOTE: auto_param_ext_tests / lean4_compat_ext_tests / notation_ext_tests /
// where_clause_ext_tests are orphaned files (never declared here). They are also
// STALE — re-enabling them surfaces ~101 compile errors against removed/renamed
// APIs (e.g. `process_where_clause_ext`, `WhereClauseExtError`), so they are
// obsolete dead tests, not restorable coverage. Tracked for deletion/rewrite
// (org rule: tests must PASS, FAIL, or be DELETED) rather than silently orphaned.

// elab_hooks_tests declared in elab_hooks.rs (not here — see #3285)

#[cfg(test)]
#[path = "elab_hooks_ext_tests.rs"]
mod elab_hooks_ext_tests;

#[cfg(test)]
mod diamond_resolution_tests;

#[cfg(test)]
#[path = "diamond_resolution_ext_tests.rs"]
mod diamond_resolution_ext_tests;

#[cfg(test)]
mod macro_hygiene_ext_tests;

#[cfg(test)]
#[path = "macro_hygiene_ext2_tests.rs"]
mod macro_hygiene_ext2_tests;

#[cfg(test)]
#[path = "macro_hygiene_ext3_tests.rs"]
mod macro_hygiene_ext3_tests;

#[cfg(test)]
mod macro_hygiene_impl_tests;

#[cfg(test)]
mod env_snapshot_tests;

#[cfg(test)]
#[path = "env_snapshot_ext_tests.rs"]
mod env_snapshot_ext_tests;

#[cfg(test)]
mod universe_constraint_ext_tests;

#[cfg(test)]
mod universe_poly_tests;

// tc_outparam_tests declared in tc_outparam.rs (not here — see #3285)

#[cfg(test)]
mod tc_synthesis_ext_tests;

#[cfg(test)]
#[path = "tc_synthesis_ext2_tests.rs"]
mod tc_synthesis_ext2_tests;

#[cfg(test)]
mod structure_extend_ext_tests;

#[cfg(test)]
mod structure_inherit_tests;

#[cfg(test)]
mod structure_inherit_ext_tests;

#[cfg(test)]
#[path = "structure_inherit_ext2_tests.rs"]
mod structure_inherit_ext2_tests;

#[cfg(test)]
mod implicit_args_tests;

#[cfg(test)]
#[path = "implicit_args_ext_tests.rs"]
mod implicit_args_ext_tests;

// mutual_inductive_tests declared in mutual_inductive.rs (not here — see #3285)

#[cfg(test)]
#[path = "mutual_inductive_ext_tests.rs"]
mod mutual_inductive_ext_tests;

#[cfg(test)]
mod ffi_extern_tests;

#[cfg(test)]
#[path = "ffi_extern_ext_tests.rs"]
mod ffi_extern_ext_tests;

#[cfg(test)]
mod io_monad_tests;

#[cfg(test)]
#[path = "io_monad_ext_tests.rs"]
mod io_monad_ext_tests;

#[cfg(test)]
#[path = "io_monad_ext2_tests.rs"]
mod io_monad_ext2_tests;

#[cfg(test)]
mod let_rec_tests;

#[cfg(test)]
#[path = "let_rec_ext_tests.rs"]
mod let_rec_ext_tests;

#[cfg(test)]
#[path = "let_rec_ext2_tests.rs"]
mod let_rec_ext2_tests;

#[cfg(test)]
mod notation_priority_tests;

#[cfg(test)]
#[path = "notation_priority_ext_tests.rs"]
mod notation_priority_ext_tests;

// coercion_tests declared in coercion.rs (not here — see #3285)

#[cfg(test)]
#[path = "coercion_ext_tests.rs"]
mod coercion_ext_tests;

// where_desugar_ext_tests declared in where_desugar_ext.rs (not here — see #3285)

#[cfg(test)]
mod mutual_decl_ext_tests;

#[cfg(test)]
#[path = "mutual_decl_ext2_tests.rs"]
mod mutual_decl_ext2_tests;

#[cfg(test)]
#[path = "mutual_decl_ext3_tests.rs"]
mod mutual_decl_ext3_tests;

#[cfg(test)]
#[path = "section_scope_ext_tests.rs"]
mod section_scope_ext_tests;

#[cfg(test)]
mod section_variable_ext_tests;

#[cfg(test)]
mod namespace_ext_tests;

#[cfg(test)]
mod attribute_ext_tests;

#[cfg(test)]
#[path = "attribute_ext2_tests.rs"]
mod attribute_ext2_tests;

#[cfg(test)]
#[path = "attribute_registry_ext_tests.rs"]
mod attribute_registry_ext_tests;

#[cfg(test)]
#[path = "derive_ext2_tests.rs"]
mod derive_ext2_tests;

#[cfg(test)]
#[path = "derive_handlers_ext_tests.rs"]
mod derive_handlers_ext_tests;

#[cfg(test)]
mod derive_ext_handlers_tests;

#[cfg(test)]
#[path = "derive_ext_handlers2_tests.rs"]
mod derive_ext_handlers2_tests;

#[cfg(test)]
#[path = "instances_ext_tests.rs"]
mod instances_ext_tests;

#[cfg(test)]
mod instance_priority_ext_tests;

#[cfg(test)]
#[path = "instance_priority_ext2_tests.rs"]
mod instance_priority_ext2_tests;

#[cfg(test)]
mod tactic_interp_ext_tests;

#[cfg(test)]
mod notation_scope_ext_tests;

#[cfg(test)]
#[path = "options_registry_ext_tests.rs"]
mod options_registry_ext_tests;

#[cfg(test)]
#[path = "notation_scope_ext2_tests.rs"]
mod notation_scope_ext2_tests;

#[cfg(test)]
mod string_interp_ext_tests;

#[cfg(test)]
mod pattern_match_ext_tests;

#[cfg(test)]
mod inductive_ext_tests;

#[cfg(test)]
mod inductive_ext2_tests;

#[cfg(test)]
#[path = "commands_ext_tests.rs"]
mod commands_ext_tests;

#[cfg(test)]
#[path = "eval_cmd_ext_tests.rs"]
mod eval_cmd_ext_tests;

#[cfg(test)]
#[path = "macro_cmd_ext_tests.rs"]
mod macro_cmd_ext_tests;

#[cfg(test)]
#[path = "dep_graph_ext_tests.rs"]
mod dep_graph_ext_tests;

#[cfg(test)]
#[path = "dep_graph_ext2_tests.rs"]
mod dep_graph_ext2_tests;

#[cfg(test)]
#[path = "name_resolution_ext_tests.rs"]
mod name_resolution_ext_tests;

#[cfg(test)]
#[path = "name_resolution_ext2_tests.rs"]
mod name_resolution_ext2_tests;

#[cfg(test)]
#[path = "unify_ext_tests.rs"]
mod unify_ext_tests;

#[cfg(test)]
#[path = "command_elab_ext_tests.rs"]
mod command_elab_ext_tests;

#[cfg(test)]
#[path = "command_elab_registry_ext_tests.rs"]
mod command_elab_registry_ext_tests;

#[cfg(test)]
#[path = "universe_poly_ext_tests.rs"]
mod universe_poly_ext_tests;

#[cfg(test)]
#[path = "universe_poly_ext2_tests.rs"]
mod universe_poly_ext2_tests;

#[cfg(test)]
#[path = "meta_ext_tests.rs"]
mod meta_ext_tests;

#[cfg(test)]
#[path = "section_variable_ext2_tests.rs"]
mod section_variable_ext2_tests;

#[cfg(test)]
#[path = "preprocess_ext_tests.rs"]
mod preprocess_ext_tests;

#[cfg(test)]
#[path = "register_ext_tests.rs"]
mod register_ext_tests;

#[cfg(test)]
#[path = "variable_cmd_ext_tests.rs"]
mod variable_cmd_ext_tests;
