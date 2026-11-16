// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Load parsed .olean modules into the clean kernel environment.
//!
//! This bridges the low-level parsed structures into the kernel's
//! `Environment` by converting names, levels, and expressions.
//!
//! # Caching
//! Module loading involves two expensive operations:
//! 1. **Parsing**: Reading and interpreting the .olean binary format (~40% of time)
//! 2. **Loading**: Converting and registering constants in the environment (~60% of time)
//!
//! The `ModuleCache` can be used to cache parsed modules across multiple
//! `load_module_with_deps` calls, avoiding re-parsing when the same module
//! is needed by multiple dependents.

mod artifact;
mod artifact_ledger;
mod clean_payload_requirement;
pub use clean_payload_requirement::{
    clean_payload_imports_required, require_clean_payload_imports,
};
mod restatement_evidence;
pub(crate) use restatement_evidence::{
    CompletedCanonicalTheorem, PendingRestatement, TheoremRestatementCertificate,
};
mod authoritative_values;
mod convert;
mod convert_direct;
mod convert_expr;
mod convert_expr_direct;
mod deadline;
mod default_fn_binders;
mod load;
mod load_parse;
pub use default_fn_binders::{default_fn_binder_idx, DefaultFnBinderState};
mod type_binder_names;
pub use type_binder_names::{type_binder_name_idx, type_binder_names, TypeBinderNameState};
mod late_binding;
mod load_register;
mod load_shadowing;
mod projection_scan;
mod stored_families;
mod value_binder_names;
pub use load_register::{
    add_global_instance_entry, has_global_instance_entry, scoped_instance_idx, ScopedInstanceState,
};
mod lake_package;
mod module_cache_direct;
mod parse;
mod path;
mod policy;
mod project_world;
pub mod runtime;
mod typed_imports;
mod world_gate;
pub use world_gate::LeanWorldScope;
pub(crate) use world_gate::{
    bind_restored as bind_restored_world, declare as declare_world,
    environment_world as bound_world, part_world, validate_level_profile,
};

#[cfg(test)]
mod module_cache_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_alias_ext_import;
#[cfg(test)]
mod tests_class_ext_import;
#[cfg(test)]
mod tests_default_fn_binders;
#[cfg(test)]
mod tests_external_packages;
#[cfg(test)]
mod tests_import_passes;
#[cfg(test)]
mod tests_import_passes_fixture;
#[cfg(test)]
mod tests_instance_ext_import;
#[cfg(test)]
mod tests_instance_priority_adopt;
#[cfg(test)]
mod tests_membership_carrier_import;
#[cfg(test)]
mod tests_simp_ext_import;
#[cfg(test)]
mod tests_structure_ext_import;
#[cfg(test)]
mod tests_value_binder_names;

use hashbrown::HashMap;
use smallvec::SmallVec;
use std::path::PathBuf;
use std::sync::{Arc, RwLock};

// Re-export public API
pub use artifact::{read_artifact, ArtifactDepth, ArtifactRead};
pub use convert::is_projection_fn_body;
pub(crate) use convert::{infer_recursor_arg_order, is_aux_recursor_suffix, ConvertedConstant};
pub use load::{
    load_module_with_deps, load_module_with_deps_bounded, load_module_with_deps_bounded_shared,
    load_module_with_deps_bounded_shared_with_policy, load_module_with_deps_cached,
    load_module_with_deps_cached_guarded, load_module_with_deps_parallel,
    load_module_with_deps_replaying_module, load_module_with_deps_shared,
    load_module_with_deps_shared_with_policy, load_module_with_deps_with_import_policy,
    load_modules_with_deps, load_modules_with_deps_checked,
    load_modules_with_deps_checked_with_limits, load_modules_with_deps_with_import_policy,
    load_olean_file, load_olean_file_with_import_policy, load_typed_module_with_deps_bounded,
    load_typed_module_with_deps_bounded_shared, load_typed_module_with_deps_cached,
    load_typed_module_with_deps_parallel, CapturedModuleBytes, ModuleCaptureLimits,
};
pub(crate) use load_register::register_front_end_constants;
pub use load_register::{
    is_compiler_ir_name, load_parsed_module, load_parsed_module_at_index,
    load_parsed_module_at_index_with_import_policy, load_parsed_module_with_import_policy,
};
pub use load_shadowing::lean_accepts_restatement;
pub(crate) use parse::assemble_incremental_part;
pub use parse::{
    discover_olean_parts, parse_imports_and_const_names_only, parse_imports_only, parse_module,
    parse_module_file, parse_module_incremental, parse_module_incremental_types_only,
    parse_module_parts, parse_module_types_only,
};
#[cfg(any(test, feature = "cli"))]
pub(crate) use path::legacy_module_name;
pub use path::{
    active_stdlib_toolchain, alias_resolvable_toolchain_versions, default_search_paths,
    default_toolchain_versions, find_module_olean, resolve_typed_module_path,
    toolchain_versions_from_search_paths, typed_module_rel_path, ActiveStdlibToolchain,
    SearchPathBuilder,
};
pub use policy::{ImportKinds, OleanImportPolicy, UnpinnedOleanImportPolicy};
pub use project_world::{
    import_world_for_file, search_paths_in_world, source_world_for_file, source_world_for_snapshot,
    source_world_of, ImportWorld, ImportWorldRefusal, SourceWorldDecision, SourceWorldRefusal,
};
pub use stored_families::{stored_family_members, StoredFamilyMembers};
pub use typed_imports::{parse_typed_imports, TypedImport, TypedImportFlags};

// Test-only re-exports: used by import/tests.rs via `use super::*`.
#[cfg(test)]
pub(crate) use convert::decl_to_constant_info;
pub use convert::{
    convert_parsed_constant_to_const_info, convert_parsed_constant_to_declaration,
    convert_parsed_constant_to_type_stub, ConstantConvertSession,
};
#[cfg(test)]
pub(crate) use convert_expr::convert_expr;
/// The canonical, deterministic FVar/MVar-name hash used by the EAGER olean
/// import (`convert_expr_direct::read_and_convert_expr`). Re-exported so the
/// lazy `.mathverse` shard builder can hash FVar names IDENTICALLY — any other
/// hasher gives a different `FVarId` for the same name, which diverges the
/// reconstructed `Expr` identity and breaks eager-vs-lazy verdict parity.
pub use convert_expr::hash_str;
#[cfg(test)]
pub(crate) use convert_expr_direct::read_and_convert_expr;
#[cfg(any(feature = "cli", test))]
pub(crate) use load::stored_constant_names;
#[cfg(test)]
pub(crate) use load_parse::parse_load_module;
#[cfg(test)]
#[cfg(test)]
pub(crate) use load_register::load_module_direct_with_cache;
#[cfg(test)]
pub(crate) use path::{
    collect_default_search_paths, collect_default_search_paths_with_pinned,
    discover_lake_package_paths, module_name_from_path,
};

/// Errors that can arise while importing an .olean module into the kernel environment.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ImportError {
    /// An early recursor could not be bound to its complete artifact's checked
    /// authoritative record. This is a whole-artifact failure in every policy.
    #[error(
        "deferred recursor {name} in {module}, part {part} constant {ordinal}, refused: {reason}"
    )]
    DeferredRecursorRefused {
        /// Artifact identity.
        module: String,
        /// Original part label.
        part: String,
        /// Original constant-table index.
        ordinal: usize,
        /// Recursor identity.
        name: String,
        /// Exact binding failure.
        reason: String,
    },
    /// Error parsing the .olean file.
    #[error("parse error: {0}")]
    Parse(#[from] crate::OleanError),
    /// The caller's deadline (`clean_kernel::tc::run_until`) passed while the
    /// load ran, and the load stopped. What it had registered in the caller's
    /// environment by then is a partial load, never a result; the module
    /// cache holds only modules decoded whole.
    #[error("the load stopped at its caller's deadline")]
    Interrupted,
    /// An import or metadata computation stopped at a resource bound.
    /// A partially loaded environment is not usable.
    #[error("{operation} did not finish: {reason}")]
    ResourceLimit {
        /// Metadata computation which could not finish.
        operation: String,
        /// The bound that stopped the computation.
        reason: String,
    },
    /// Parse error with the exact base or companion path in a module graph.
    #[error("cannot parse .olean file `{path}`: {source}")]
    FileParse {
        /// File whose captured bytes could not be parsed.
        path: PathBuf,
        /// Underlying structured format error; no failed part is skipped.
        #[source]
        source: crate::OleanError,
    },
    /// Error adding declaration to environment.
    #[error("environment error: {0}")]
    Env(#[from] clean_kernel::env::EnvError),
    /// I/O error reading the file.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// An .olean file could not be read from disk (the path is known).
    ///
    /// Unlike [`ImportError::Io`], this names WHICH file failed — a
    /// Mathlib-scale load touches thousands of `.olean` files and a pathless
    /// io error is undebuggable.
    #[error(
        "cannot read .olean file `{path}`: {source}; check that the toolchain/package \
         build output still exists (re-run `lake build`, or re-select the search path \
         via LEAN_PATH / MATHLIB_PATH)"
    )]
    FileUnreadable {
        /// Path of the .olean file that could not be read.
        path: PathBuf,
        /// Underlying I/O error.
        #[source]
        source: std::io::Error,
    },
    /// Module not found in search paths.
    #[error("module {module} not found{}", render_module_search(searched))]
    ModuleNotFound {
        /// Name of the module that was not found.
        module: String,
        /// Paths that were searched.
        searched: Vec<PathBuf>,
    },
    /// Module graph is outside the bounded import surface.
    #[error("unsupported module {module}: {reason}")]
    UnsupportedModule {
        /// Name of the requested root module.
        module: String,
        /// Human-readable explanation.
        reason: String,
    },
    /// Import policy rejected unpinned external `.olean` constants.
    #[error(
        "import policy rejected unpinned external .olean import for {module}: \
         {olean_constants} .olean constants, {clean_payload_constants} Clean payload constants; \
         no pin/hash verification was supplied"
    )]
    UnpinnedExternalOleanRejected {
        /// Module name, or `<unknown>` when the load path could not infer it.
        module: String,
        /// Number of Lean `.olean` constants that would have been registered.
        olean_constants: usize,
        /// Number of Clean payload constants that would have been registered.
        clean_payload_constants: usize,
    },
    /// A Lean-written part whose header identity (version, flags, githash)
    /// is no world this build of Clean reads, a Canary world's, or a
    /// Measured world's the environment has not declared (R38, R81). Pinned
    /// `lean` refuses such a file too ("incompatible header").
    #[error(
        "unsupported Lean world: `{module}` was written by {found}; this build of Clean reads \
         {} (crates/clean-olean/lean_worlds.tsv), and pinned `lean` refuses such a file too \
         (\"incompatible header\"), so the import is refused",
        supported.join("; ")
    )]
    UnsupportedLeanWorld {
        /// The part's module label.
        module: String,
        /// Who wrote it: its header identity, or the world it belongs to.
        found: String,
        /// The worlds this build reads, with their identities.
        supported: Vec<String>,
    },
    /// A Lean part of a second world in one environment (R38: an environment
    /// reads one Lean world).
    #[error(
        "mixed Lean worlds: `{module}` is of Lean {world}, but this environment already reads \
         `{first}`, of Lean {first_world}; one environment reads one Lean world, so the import \
         is refused"
    )]
    MixedLeanWorlds {
        /// The part (or `<declaration>`) of the second world.
        module: String,
        /// Its world.
        world: String,
        /// The part (or `<declaration>`) that bound the environment.
        first: String,
        /// The world the environment reads.
        first_world: String,
    },
    /// A world a declaration names that no environment may declare.
    #[error("unknown Lean world `{world}`: {reason}")]
    UnknownLeanWorld {
        /// The world named.
        world: String,
        /// Why it cannot be declared.
        reason: String,
    },
    /// Constant declaration missing its type.
    #[error("missing type for constant {0}")]
    MissingType(String),
    /// Constant declaration missing its value.
    #[error("missing value for constant {0}")]
    MissingValue(String),
    /// Constant contains unsupported metavariables.
    #[error("unsupported metavariable in constant {0}")]
    UnsupportedMVar(String),
    /// Expression conversion from parsed format failed.
    #[error("expression conversion failed for {name}: {message}")]
    ExprConversion {
        /// Name of the constant being converted.
        name: String,
        /// Error message.
        message: String,
    },
    /// Universe level conversion failed.
    #[error("level conversion failed for {name}: {message}")]
    LevelConversion {
        /// Name of the constant being converted.
        name: String,
        /// Error message.
        message: String,
    },
    /// An imported structure-field table contradicts the same closure's own
    /// projection constants. One of the two was rewritten, and nothing
    /// available says which, so the import is refused rather than resolved
    /// in favour of either (module-trust round 27).
    #[error(
        "inconsistent artifact: the structure field table of {structure} is not the one its \
         projections define ({reason}); the import is refused"
    )]
    InconsistentStructureTable {
        /// The structure whose table was refused.
        structure: String,
        /// Which field disagrees, and how.
        reason: String,
    },
    /// An artifact part — a Clean payload or a Lean-built `.olean` — declares
    /// one name twice (module-trust round 28, Y5, and round 29, N2r: the later
    /// of two contradictory definitions used to win silently).
    #[error(
        "inconsistent artifact: it declares the {what} `{name}` more than once; \
         the import is refused"
    )]
    DuplicateDeclaration {
        /// The name declared twice.
        name: String,
        /// `declaration` or `structure field table`.
        what: &'static str,
    },
    /// An artifact declares a name another imported artifact already
    /// declared: a Clean payload with different content, a Lean-built record
    /// at all, as Lean refuses the import (module-trust rounds 28 and 29: the
    /// first one loaded used to be kept silently).
    #[error(
        "inconsistent artifacts: `{name}` is declared here and by `{first}`, which was \
         imported first; the import is refused"
    )]
    ConflictingDeclaration {
        /// The name declared twice.
        name: String,
        /// The module whose declaration was loaded first.
        first: String,
    },
    /// Two parts of one artifact — a module's `.olean`, `.olean.server` and
    /// `.olean.private`, or the Clean payloads they carry — state one
    /// declaration differently (module-trust round 30, X1: a genuine Lean
    /// build's `D.olean` said `D.e := 1` and its `D.olean.private`, which
    /// `lean` reads, `D.e := 0`; the later record was dropped unread and
    /// `D.e = 1` passed). A value-free stub a later part of a module-system
    /// artifact completes is not a disagreement: the kernel re-checks it at the
    /// upgrade (and a refusal there is [`Self::CompletionRefused`]). A
    /// non-module artifact's companion that completes its `.olean`'s stub is
    /// one (R131): every importer reads that artifact's `.olean` alone.
    #[error(
        "inconsistent artifact: the parts of `{module}` state `{name}` differently; the \
         import is refused"
    )]
    PartsDisagree {
        /// The name the parts disagree on.
        name: String,
        /// The module whose parts disagree.
        module: String,
    },
    /// Two parts of one artifact state an elaborator table Clean reads
    /// differently (module-trust round 31): Lean's levels are cumulative —
    /// what the `.olean` exports, the `.olean.server` and `.olean.private`
    /// state again, and a module whose parts are not Lean's module-system
    /// parts is read through its `.olean` alone — so a part that drops,
    /// changes or adds an instance, class, simp, alias or structure entry
    /// against another part gives two consumers two meanings (verification
    /// of `a7c69cb8c`: the server part alone naming `I.i1`, or the base part
    /// naming it at priority 2000, let `I.C.val = 1` pass where `lean` reads
    /// the private part's `I.i0`).
    #[error(
        "inconsistent artifact: the parts of `{module}` state the `{extension}` table \
         differently ({entry}); the import is refused"
    )]
    PartsDisagreeOnEntry {
        /// The module whose parts disagree.
        module: String,
        /// The extension whose table differs.
        extension: String,
        /// The entry one part states and another does not, as Clean reads it.
        entry: String,
    },
    /// Two parts of one artifact carry different module headers (import
    /// list, `isModule`): `lean` follows the part it reads, Clean the base
    /// part, so the two would load different closures.
    #[error(
        "inconsistent artifact: the parts of `{module}` state {what} differently; the import \
         is refused"
    )]
    PartsDisagreeOnHeader {
        /// The module whose parts disagree.
        module: String,
        /// `its imports` or `whether it is a module`.
        what: &'static str,
    },
    /// A module-system artifact (its `.olean` says `isModule`) without the
    /// part a consumer that is not itself a `module` reads: `lean` reads
    /// such a module's `.olean.private`, found only beside its
    /// `.olean.server`, and fails the import without it ("missing data
    /// file"). Nothing of the artifact is loaded.
    #[error(
        "inconsistent artifact: `{module}` is a module-system artifact without its `{part}`, \
         the part a consumer that is not a `module` reads; the import is refused"
    )]
    MissingModulePart {
        /// The module.
        module: String,
        /// `.olean.server` or `.olean.private`.
        part: &'static str,
    },
    /// A part of an artifact declares a constant the part a non-`module`
    /// consumer reads does not (R113). An importer reads a module-system
    /// artifact through its `.olean.private` when it is not itself a `module`
    /// (`leanchecker` imports every module that way) and any other artifact
    /// through its `.olean` (`Environment.lean`: `ImportedModule.mainModule?`);
    /// `leanchecker`'s default mode replays the artifact's last part. Lean's
    /// `writeModule` makes all of these one set of names — the exported and
    /// server levels are filtered subsets of the private one (measured over
    /// the pinned v4.30.0-rc2 `lib/lean`: 2,302 artifacts, 314,344
    /// exported/server names, 0 misplaced) — so a part that breaks it was not
    /// written by `writeModule`, and the whole artifact is refused. For a
    /// non-module artifact whose companions hold a complete, well-typed set,
    /// `leanchecker`'s default mode would accept what this refuses: stricter
    /// than Lean, the safe direction.
    #[error(
        "inconsistent artifact: `{module}`'s `{part}` declares `{name}`, which its \
         `{authoritative}` — the part a consumer that is not a `module` reads — does not; no \
         importer of the artifact sees the declaration, and `writeModule` never writes such an \
         artifact; the import is refused"
    )]
    MisplacedDeclaration {
        /// The module.
        module: String,
        /// The part that declares the misplaced name (`.olean` or
        /// `.olean.server`).
        part: &'static str,
        /// The part a non-`module` consumer reads (`.olean.private` for a
        /// module-system artifact, `.olean` otherwise).
        authoritative: &'static str,
        /// The misplaced constant.
        name: String,
    },
    /// A later part of an artifact completes a value-free stub with a value the
    /// kernel refuses at the checked upgrade (R131). Lean's `writeModule` stubs
    /// a public theorem in a module's `.olean` and keeps the theorem in its
    /// `.olean.private`, the part an importer that is not a `module` reads, so
    /// the declaration Lean reads is the refused value: the stub left resident
    /// is not a declaration of the artifact, and trusting it as an axiom
    /// accepted what the kernel refused. A load that leaves nothing to a replay
    /// refuses the import; a replay load records it in
    /// `LoadSummary::refused_completions` and refuses the declaration by name.
    #[error(
        "inconsistent artifact: `{module}` completes the value-free `{name}` with a value the \
         kernel refuses ({reason}); Lean reads the declaration with that value, so the import is \
         refused"
    )]
    CompletionRefused {
        /// The module.
        module: String,
        /// The declaration whose completion the kernel refused.
        name: String,
        /// The kernel's refusal.
        reason: String,
    },
    /// A declaration an artifact's AUTHORITATIVE part (`.olean.private` for a
    /// module-system artifact, `.olean` otherwise) states with a value is not
    /// resident after a re-check lane's load as the artifact's own declaration
    /// with that value (R142): the value did not convert, the kernel refused
    /// it, another declaration holds the name, or it was dropped unchecked.
    /// Lean reads the declaration with the value, so the import is refused,
    /// whatever kept it out.
    #[error(
        "inconsistent artifact: `{module}` states `{name}` with a value the environment does not \
         hold ({reason}); Lean reads the declaration with that value, so the import is refused"
    )]
    AuthoritativeValueNotResident {
        /// The module.
        module: String,
        /// The declaration.
        name: String,
        /// Why the value is not resident.
        reason: String,
    },
    /// An artifact refers to a name that no artifact had declared when it
    /// was loaded, and a later, different artifact declares it. A Lean
    /// artifact is built against its imports, which load before it.
    #[error(
        "inconsistent artifacts: `{referrer}` refers to `{name}`, which none of its imports \
         declares, and `{declared_by}` declares it afterwards; the import is refused"
    )]
    ForwardReference {
        /// The name referred to before any artifact declared it.
        name: String,
        /// The module that referred to it.
        referrer: String,
        /// The module that declared it later.
        declared_by: String,
    },
    /// Declarations of an artifact depend on themselves (module-trust round
    /// 29, C1/C4: `V0.v := Nat.succ V0.v` made unfolding loop). Lean's kernel
    /// admits no such declaration unless every member is `unsafe`.
    #[error(
        "inconsistent artifact: its declarations depend on themselves ({}); the import is \
         refused",
        names.join(" -> ")
    )]
    DefinitionalCycle {
        /// The members of the cycle.
        names: Vec<String>,
    },
    /// Two different artifacts would be loaded under one module label, so
    /// their declarations could not be told apart.
    #[error(
        "inconsistent artifacts: `{second}` would be loaded under the label `{label}`, which \
         `{first}` already uses; the import is refused"
    )]
    AmbiguousModuleLabel {
        /// The shared label.
        label: String,
        /// The artifact that holds it.
        first: String,
        /// The artifact that would share it.
        second: String,
    },
    /// A clean payload marks `protected` / `private` a declaration it does
    /// not carry: such a mark would change what an importer's identifiers
    /// resolve to, so the import is refused.
    #[error("inconsistent artifact: {reason} ({name}); the import is refused")]
    InconsistentDeclarationMark {
        /// The marked name.
        name: String,
        /// Which mark.
        reason: String,
    },
    /// A bootstrap environment may consume only validated Clean payload parts.
    #[error("inconsistent artifact: {module} has no Clean payload required by this bootstrap environment; the import is refused")]
    CleanPayloadRequired {
        /// The artifact part rejected by the local bootstrap policy.
        module: String,
    },
}

impl ImportError {
    /// A partial import stopped at a resource bound; no fallback is sound.
    #[must_use]
    pub fn is_resource_refusal(&self) -> bool {
        matches!(self, Self::Interrupted | Self::ResourceLimit { .. })
    }

    /// The artifact contradicts itself: part of it may already be in the
    /// environment, so no import policy may continue past it.
    #[must_use]
    pub fn is_inconsistent_artifact(&self) -> bool {
        matches!(
            self,
            Self::InconsistentStructureTable { .. }
                | Self::DuplicateDeclaration { .. }
                | Self::ConflictingDeclaration { .. }
                | Self::PartsDisagree { .. }
                | Self::PartsDisagreeOnEntry { .. }
                | Self::PartsDisagreeOnHeader { .. }
                | Self::MissingModulePart { .. }
                | Self::MisplacedDeclaration { .. }
                | Self::CompletionRefused { .. }
                | Self::AuthoritativeValueNotResident { .. }
                | Self::ForwardReference { .. }
                | Self::DefinitionalCycle { .. }
                | Self::AmbiguousModuleLabel { .. }
                | Self::InconsistentDeclarationMark { .. }
                | Self::CleanPayloadRequired { .. }
        )
    }

    /// The declarations this error is about, by name: the one it names, every
    /// member of a [`Self::DefinitionalCycle`], or none (a missing module, an
    /// unreadable file, a disagreement over a whole part). A caller that
    /// reports a refused load names these, never the load alone.
    #[must_use]
    pub fn declaration_names(&self) -> Vec<&str> {
        match self {
            Self::MissingType(name)
            | Self::MissingValue(name)
            | Self::UnsupportedMVar(name)
            | Self::ExprConversion { name, .. }
            | Self::LevelConversion { name, .. }
            | Self::DuplicateDeclaration { name, .. }
            | Self::ConflictingDeclaration { name, .. }
            | Self::PartsDisagree { name, .. }
            | Self::ForwardReference { name, .. }
            | Self::MisplacedDeclaration { name, .. }
            | Self::CompletionRefused { name, .. }
            | Self::AuthoritativeValueNotResident { name, .. }
            | Self::InconsistentDeclarationMark { name, .. } => vec![name.as_str()],
            Self::InconsistentStructureTable { structure, .. } => vec![structure.as_str()],
            Self::DefinitionalCycle { names } => names.iter().map(String::as_str).collect(),
            _ => Vec::new(),
        }
    }
}

/// Render the searched-path tail of a `ModuleNotFound` message.
///
/// Distinguishes "no search paths were discovered at all" (an environment
/// problem, not a missing module) from "the module is absent from the paths
/// that were searched", and names the env vars that extend the search.
fn render_module_search(searched: &[PathBuf]) -> String {
    if searched.is_empty() {
        ": no .olean search paths were discovered — set LEAN_PATH or MATHLIB_PATH, point \
         LEAN_PACKAGES_PATH at a lake project root, or install a Lean 4 toolchain via elan"
            .to_string()
    } else {
        format!(
            " in {} searched path(s): {:?}; if the module belongs to another package, add \
             its build/lib directory to LEAN_PATH (or LEAN_PACKAGES_PATH for a lake root)",
            searched.len(),
            searched
        )
    }
}

/// Reason a constant was skipped during import.
#[derive(Debug, Clone)]
pub struct SkippedConstant {
    /// Name of the skipped constant.
    pub name: String,
    /// Reason for skipping.
    pub reason: String,
}

/// Shared intern cache for expression deduplication across all constants in a module.
///
/// Keyed by `Expr::hash_cached()` (u32), with small-vec buckets for hash collisions.
/// Promoted from per-`convert_expr` call to per-`load_parsed_module` call so that
/// identical sub-expressions across different constants (e.g. `Nat`, `Prop`) share
/// the same `Arc<Expr>` allocation (#2383).
///
/// Wraps a `HashMap` + a running `total_entries` counter so that computing the
/// cache size is O(1) instead of the previous O(n) `values().map(len).sum()`.
/// Part of #3133.
pub(crate) struct ExprInternCache {
    pub(crate) map: HashMap<u32, SmallVec<[Arc<clean_kernel::expr::Expr>; 1]>>,
    /// Running count of total entries across all buckets.
    pub(crate) total_entries: u64,
}

impl Default for ExprInternCache {
    fn default() -> Self {
        Self {
            map: HashMap::new(),
            total_entries: 0,
        }
    }
}

impl ExprInternCache {
    /// Create a new cache pre-sized for the expected number of unique hashes.
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            map: HashMap::with_capacity(capacity),
            total_entries: 0,
        }
    }
}

/// Statistics about expression structure sharing achieved via hash-consing
/// during olean import (#2383).
#[derive(Debug, Clone, Default)]
pub struct ExprSharingStats {
    /// Total calls to intern_expr (one per sub-expression processed)
    pub total_intern_calls: u64,
    /// Cache hits: existing Arc<Expr> reused instead of allocating
    pub cache_hits: u64,
    /// Unique expressions stored in the intern cache
    pub unique_exprs: u64,
}

impl ExprSharingStats {
    pub(crate) fn merge(&mut self, other: &ExprSharingStats) {
        self.total_intern_calls += other.total_intern_calls;
        self.cache_hits += other.cache_hits;
        self.unique_exprs += other.unique_exprs;
    }

    /// Fraction of intern calls that were cache hits (0.0 to 1.0).
    pub fn hit_rate(&self) -> f64 {
        if self.total_intern_calls == 0 {
            0.0
        } else {
            self.cache_hits as f64 / self.total_intern_calls as f64
        }
    }

    /// Estimated Arc allocations saved by deduplication.
    pub fn allocations_saved(&self) -> u64 {
        self.cache_hits
    }
}

/// Per-extension diagnostic population, not restored semantic completeness.
/// There is one row for each source extension record, including unknown ones.
#[derive(Debug, Clone)]
pub struct ExtensionLoadAccounting {
    /// Exact typed identity on direct loading; legacy Parsed callers supplied
    /// only a display projection and cannot recover the original identity.
    pub extension_name: clean_kernel::name::Name,
    /// Complete raw entry Array size on direct loading; unknown for Parsed APIs.
    pub source_rows: Option<usize>,
    /// Rows recognized by the metadata decoder, not proof/body validation.
    pub decoded_rows: usize,
    /// Rows retained as unknown or malformed, never dropped or registered.
    pub undecoded_rows: usize,
    /// One line per undecoded row, `row <index>: <reason>`, so the loud
    /// signal names WHICH row was retained unmeasured and why, not only how
    /// many. Empty for legacy Parsed callers, whose rows carry no reason.
    pub undecoded_reasons: Vec<String>,
    /// Recognized simp/alias targets, and declarations of recognized
    /// `@[implemented_by]` / `@[extern]` rows, absent from the loaded environment.
    pub unresolved_targets: usize,
}

/// Status of an original recursor occurrence staged until artifact completion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeferredRecursorStatus {
    /// An earlier part cannot yet resolve its family's private dependencies.
    Pending,
    /// Exact typed record matches this artifact's strictly admitted recursor.
    Resolved,
    /// No matching admitted record was available at artifact completion.
    Refused(String),
}

/// An original recursor occurrence staged until its authoritative part loads.
#[derive(Debug, Clone)]
pub struct DeferredRecursor {
    /// Exact typed name read from the original record.
    pub name: clean_kernel::name::Name,
    /// Original constant-table index in this summary's part, never deduplicated.
    pub source_constant_ordinal: usize,
    /// Exact private-only dependencies that were absent in the early part.
    pub missing_dependencies: Vec<clean_kernel::name::Name>,
    /// Original strict rejection before the private context was available.
    pub initial_refusal: String,
    /// Staging is not proof or executable authority.
    pub status: DeferredRecursorStatus,
}

/// Summary of an import attempt.
#[derive(Debug, Clone)]
pub struct LoadSummary {
    /// Original artifact records captured before conversion or registration.
    /// Private so a loader-created unsafe stub cannot supply stored safety.
    pub(crate) stored_declarations: Option<StoredDeclarationPart>,
    /// Optional module name (deduced from path)
    pub module_name: Option<String>,
    /// Names of imported modules (as strings)
    pub imports: Vec<String>,
    /// Number of successfully added constants
    pub added_constants: usize,
    /// Constants skipped due to conversion issues
    pub skipped_constants: Vec<SkippedConstant>,
    /// Every early recursor occurrence awaiting a complete module artifact.
    /// Successful loads contain only Resolved rows, never proof claims.
    pub deferred_recursors: Vec<DeferredRecursor>,
    /// Constants ignored because they already exist in the environment
    pub duplicate_constants: usize,
    /// Expression structure sharing statistics from hash-consing (#2383)
    pub expr_sharing: ExprSharingStats,
    /// Names added to the env by THIS load — constants, inductives, constructors,
    /// and recursors — captured at the `tag_inserted_constants` chokepoint. Lets
    /// the verify-batch new-constant scan stay O(new) instead of re-scanning the
    /// whole growing env per module. Empty for an already-visited (short-circuited)
    /// module; the regenerated no-confusion constants are folded in as a synthetic
    /// summary by `load_module_with_deps_bounded_shared`.
    pub added_names: Vec<clean_kernel::name::Name>,
    /// Persistent-extension entries a typed decoder recognized but could not
    /// decode for this module (see `ParsedExtension::undecoded_entries`),
    /// PLUS decoded `Lean.Meta.simpExtension` entries whose origin constant
    /// is absent from the environment at restore time (skipped at import) —
    /// such a lemma has no kernel-checked statement to rewrite with, so it is
    /// not registered. Both classes degrade to the pre-decoder behavior
    /// (absent from the restored state, never guessed at); a non-zero count
    /// here is the loud signal that extension state was lost.
    pub extension_undecoded_entries: usize,
    /// Typed per-extension decomposition of the total above. Unknown modern
    /// payloads remain counted even when a selected canonical registry is read.
    pub extension_accounting: Vec<ExtensionLoadAccounting>,
    /// Human-readable descriptions of `Lean.classExtension` entries whose
    /// decoded `outParams` DISAGREE with a class already registered under the
    /// same name (a hand-registered kernel twin, or an earlier lane). The
    /// import bridge keeps the first registration (first-writer-wins) and does
    /// not overwrite; a non-empty list is the loud signal that Clean's
    /// hand-authored class metadata drifted from the real Lean `.olean` — a
    /// fidelity bug to reconcile, never a silent mismatch.
    pub class_out_param_mismatches: Vec<String>,
    /// Declarations of THIS module that were dropped because a constant of the
    /// same name was already resident and is not this module's own (another
    /// module's, or one the kernel seeded), each with the resident one's
    /// provenance. The rest of the module is then checked against that
    /// resident constant, so a Lean-profile re-check refuses each of these as
    /// already declared (Lean's `addDecl` refuses a name its environment
    /// holds). A restatement by another part of the same module
    /// (`.olean.server`/`.olean.private`) and a quotient primitive (the kernel
    /// seeds Lean's canonical quotient) are not listed.
    pub shadowed_declarations: Vec<(clean_kernel::name::Name, String)>,
    /// Of `skipped_constants`, the compiler/code-generator artifacts the
    /// `.olean` itself marks `unsafe` or `partial` (display names).
    /// `Lean.Environment.replay` never admits either, so a Lean-faithful replay
    /// leaves these out; every other skipped declaration is one Lean's replay
    /// would check, and a replay must refuse it.
    pub skipped_not_replayable: Vec<String>,
    /// Declarations of THIS module the loader dropped as restatements Lean's
    /// import accepts: a theorem or axiom whose universe parameters and type
    /// equal the resident constant's (`lean_accepts_restatement`). Each with
    /// who holds the name and whether the incoming declaration is a theorem.
    /// Lean's replay skips a restated theorem and refuses a restated axiom, so
    /// a replay needs both halves, and none of them is in `added_names`.
    pub restated_declarations: Vec<(clean_kernel::name::Name, String, bool)>,
    /// Declarations of THIS artifact that its authoritative part states with a
    /// value the load did not make resident with it, each with the reason: a
    /// value-free stub whose completion the kernel refused at the checked upgrade
    /// (R131, also listed in `skipped_constants`), and, under a policy that
    /// checks R142's invariant, any other way the value stayed out — it did not
    /// convert, another declaration holds the name, it was dropped unchecked.
    /// Lean reads the declaration with the value, so a replay refuses each of
    /// these by name and every use of one; a re-check lane's load refuses the
    /// import instead ([`ImportError::CompletionRefused`],
    /// [`ImportError::AuthoritativeValueNotResident`]).
    pub refused_completions: Vec<(clean_kernel::name::Name, String)>,
}

#[derive(Debug, Clone)]
pub(crate) struct StoredDeclarationPart {
    pub(crate) artifact: Option<String>,
    pub(crate) part: Option<String>,
    pub(crate) declarations: Vec<(clean_kernel::name::Name, Option<crate::DefinitionSafety>)>,
    pub(crate) pending_restatements: Vec<PendingRestatement>,
    pub(crate) certified_restatements: Vec<TheoremRestatementCertificate>,
    pub(crate) completed_theorems: Vec<CompletedCanonicalTheorem>,
}

impl Default for LoadSummary {
    /// An empty diagnostic summary has no original artifact evidence.
    fn default() -> Self {
        Self::empty()
    }
}

impl LoadSummary {
    pub(crate) fn empty() -> Self {
        Self {
            stored_declarations: None,
            module_name: None,
            imports: Vec::new(),
            added_constants: 0,
            skipped_constants: Vec::new(),
            deferred_recursors: Vec::new(),
            duplicate_constants: 0,
            expr_sharing: ExprSharingStats::default(),
            added_names: Vec::new(),
            extension_undecoded_entries: 0,
            extension_accounting: Vec::new(),
            class_out_param_mismatches: Vec::new(),
            shadowed_declarations: Vec::new(),
            refused_completions: Vec::new(),
            skipped_not_replayable: Vec::new(),
            restated_declarations: Vec::new(),
        }
    }
}

/// Maximum module bundles retained across loads. A bundle includes every
/// captured base/server/private part; active loads own independent Arc handles.
const MAX_MODULE_CACHE_ENTRIES: usize = 8192;

/// Bounded, thread-safe cache of typed, content-bound .olean module bundles.
///
/// Every lookup captures all parts again and compares content identities; a
/// matching mtime cannot reuse changed bytes or a different module path. No
/// rendered ParsedModule names reconstruct a cached kernel declaration.
///
/// At the entry bound, one quarter of arbitrary HashMap entries are evicted
/// (not LRU). Entries contain no Environment-derived declarations or verdicts.
#[derive(Default)]
pub struct ModuleCache {
    entries: RwLock<HashMap<PathBuf, Arc<module_cache_direct::DirectModule>>>,
}

impl ModuleCache {
    /// Create an empty cache.
    pub fn new() -> Self {
        Self::default()
    }

    /// Current retained bundle count; another thread may change it afterward.
    pub fn len(&self) -> usize {
        self.entries.read().unwrap_or_else(|e| e.into_inner()).len()
    }

    /// Whether the cache currently contains no bundles.
    pub fn is_empty(&self) -> bool {
        self.entries
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .is_empty()
    }

    /// Release cached bundles. Active loads retain their own Arc handles.
    pub fn clear(&self) {
        self.entries
            .write()
            .unwrap_or_else(|e| e.into_inner())
            .clear();
    }
}

/// Estimate the total number of constants in a module's dependency graph.
///
/// Uses known sizes for Init/Std/Mathlib module trees to avoid HashMap
/// resizing during bulk loading. Returns 0 for unknown modules (caller
/// falls back to per-module `reserve_capacity`).
///
/// Empirical data (Lean 4.28.0):
/// - Init: ~320 modules, ~57K constants
/// - Std:  ~520 modules (including Init deps), ~80K constants
/// - Mathlib: ~200K+ constants
pub(crate) fn estimate_module_graph_size(module: &str) -> usize {
    if module == "Init" || module.starts_with("Init.") {
        60_000
    } else if module == "Std" || module.starts_with("Std.") {
        90_000
    } else if module == "Mathlib" || module.starts_with("Mathlib.") {
        250_000
    } else if module == "Lean" || module.starts_with("Lean.") {
        100_000
    } else {
        // Unknown module tree — let per-module reserve_capacity handle it
        0
    }
}
