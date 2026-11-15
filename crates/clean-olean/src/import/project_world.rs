// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Lean world a checked file's imports resolve in (gap G72).
//!
//! `lean` resolves `import Lean` against its own sysroot: the toolchain the
//! project's `lean-toolchain` names, through elan. Clean resolved it against
//! the checkout's pin whatever the project pinned (`default_search_paths`),
//! so a package pinned to Lean 4.8.0 (trust-ir) was checked against
//! v4.30.0-rc2's library: Lean 4.8.0's `Lean.Syntax.setArg` was unknown, and
//! `Array.emptyWithCapacity`, which Lean 4.8.0 refuses, passed. The world gate
//! (`world_gate`, R81) cannot see this: every part loaded is the Oracle's, so
//! the environment holds one world, just not the project's.
//!
//! The rule ([`import_world_for`]) is R38's selection for source, less its
//! `--lean-world` flag, which plan item `world-decision-and-type` adds: the
//! world is the one named by the `lean-toolchain` the tool that checks the
//! file reads, read as elan reads it, or the Oracle (the checkout's pin) when
//! there is none ([`world_lean_toolchain`]). That is the nearest one, unless
//! a Lake package above it builds the file, whose `lake build` runs the
//! package's toolchain; Lake builds every package of a workspace with the
//! root's toolchain, so a file under `<ws>/.lake/packages/` takes `<ws>`'s.
//! A caller that elaborates several files into one environment selects the
//! world once, for its entry file (`clean check`, `clean-native`). A world of
//! `lean_worlds.tsv` read without
//! a declaration (R81), installed as that world's build, supplies the stdlib
//! root in place of the pin; any other is refused by name
//! ([`ImportWorldRefusal`]) and never resolved in another.
//!
//! `MATHLIB_PATH` / `LEAN_PATH` / `LEAN_PACKAGES_PATH` and Lake roots are
//! searched before that stdlib root, as `lean` searches `LEAN_PATH` before
//! its sysroot. They never choose a [`ImportWorld::Project`] world: the
//! caller declares it on the environment before any part loads
//! (`crate::declare_environment_world`), so a part they supply from another
//! world is refused as `MixedLeanWorlds`, as Lean refuses its header.
//! [`ImportWorld::CheckoutPin`] is not declared and keeps R81's rule (the
//! environment binds to the first world it reads), so there a Historical or
//! Frontend-only library on `LEAN_PATH` still chooses the world; decision
//! R111 records why.

use super::lake_package::{self, Ownership};
use super::path::collect_default_search_paths_with_pinned;
use crate::header::{OleanHeader, HEADER_SIZE_V2};
use crate::world::{
    lean_worlds, row_of_source_world, row_of_world, HeaderIdentity, LeanWorldRow, WorldState,
};
use clean_kernel::lean_world::LeanWorld;
use std::path::{Path, PathBuf};

#[cfg(test)]
#[path = "project_world_tests.rs"]
mod tests;

/// The owner every Lean world of `lean_worlds.tsv` is released under.
const LEAN_OWNER: &str = "leanprover/lean4:";

/// Where a checked file's imports resolve.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ImportWorld {
    /// No `lean-toolchain` above the file, one naming the Oracle, or one
    /// naming a Clean toolchain (`clean:stable`, what `clean lake new`
    /// writes): the checkout's pin.
    CheckoutPin,
    /// The project's `lean-toolchain` names this world, read without a
    /// declaration and installed as its build, other than the Oracle.
    Project {
        /// The world, as `lean_worlds.tsv` names it (`v4.8.0`).
        world: &'static str,
        /// The `lean-toolchain` file that named it.
        lean_toolchain: PathBuf,
        /// Its installed stdlib (`<toolchain>/lib/lean`).
        lib: PathBuf,
    },
    /// Deliberate source-language selection, including measured worlds.
    /// Its library has the registry's exact measured header identity.
    Explicit {
        /// Selected source language.
        world: LeanWorld,
        /// Installed and identity-checked standard library.
        lib: PathBuf,
    },
}

impl ImportWorld {
    /// Source grammar for this same import decision. Internal injected
    /// registry tests may use synthetic row names; production rows must map
    /// to a known source world, rather than silently falling back.
    pub fn source_world(&self) -> Result<LeanWorld, clean_kernel::lean_world::UnknownLeanWorld> {
        match self {
            Self::CheckoutPin => Ok(LeanWorld::ORACLE),
            Self::Project { world, .. } => world.parse(),
            Self::Explicit { world, .. } => Ok(*world),
        }
    }

    /// World to declare before imports. CheckoutPin retains R81/R111's
    /// first-artifact binding; explicit choices cannot bind to another world.
    #[must_use]
    pub fn declared_world(&self) -> Option<&'static str> {
        match self {
            Self::CheckoutPin => None,
            Self::Project { world, .. } => Some(world),
            Self::Explicit { world, .. } => Some(world.tag()),
        }
    }
}

/// Failure selecting one source grammar and its matching import library.
#[derive(Debug, Clone, thiserror::Error)]
pub enum SourceWorldRefusal {
    /// Existing project-selection policy remains fail closed.
    #[error(transparent)]
    Project(#[from] ImportWorldRefusal),
    /// No source feature decisions exist for this release.
    #[error(transparent)]
    Unknown(#[from] clean_kernel::lean_world::UnknownLeanWorld),
    /// Explicit selection must still identify a measured installed build.
    #[error("Lean world `{world}` cannot be selected: {reason}")]
    Explicit { world: LeanWorld, reason: String },
}

/// One decision shared by the parser and the import/elaboration frontend.
///
/// A project world [`import_world_for`] refuses refuses the run's imports
/// only (R-WR, decision R111): the refusal is carried here and every import
/// of a Lean module is then `UnresolvedImport` naming it, while a file with
/// no imports, or whose imports are the project's own source, still checks.
/// Its source language is then the Oracle's, the selection rule's default
/// (R38), which grants no feature decision of the refused release.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceWorldDecision {
    /// Grammar and source command semantics.
    world: LeanWorld,
    /// The matching artifact-library decision, or the project world's refusal.
    imports: Result<ImportWorld, ImportWorldRefusal>,
}

impl SourceWorldDecision {
    /// Source language chosen for this run.
    #[must_use]
    pub fn world(&self) -> LeanWorld {
        self.world
    }

    /// Matching import-library choice, validated by the same decision.
    ///
    /// # Errors
    ///
    /// The project world's refusal: no import of a Lean module may resolve,
    /// in that world or in another.
    pub fn imports(&self) -> Result<&ImportWorld, &ImportWorldRefusal> {
        self.imports.as_ref()
    }

    /// [`Self::imports`], owned, as a file context carries it.
    pub fn import_world(&self) -> Result<ImportWorld, ImportWorldRefusal> {
        self.imports.clone()
    }

    /// The world to declare on the environment before imports
    /// ([`ImportWorld::declared_world`]); none when the imports are refused,
    /// since nothing then loads.
    #[must_use]
    pub fn declared_world(&self) -> Option<&'static str> {
        self.imports
            .as_ref()
            .ok()
            .and_then(ImportWorld::declared_world)
    }
}

/// The source language of a run whose imports resolve as `imports` says:
/// the import world's own, or the Oracle's when the project world is refused
/// ([`SourceWorldDecision`]).
///
/// # Errors
///
/// [`clean_kernel::lean_world::UnknownLeanWorld`] for an import world with no
/// source-language decision.
pub fn source_world_of(
    imports: &Result<ImportWorld, ImportWorldRefusal>,
) -> Result<LeanWorld, clean_kernel::lean_world::UnknownLeanWorld> {
    match imports {
        Ok(world) => world.source_world(),
        Err(_) => Ok(LeanWorld::ORACLE),
    }
}

/// Select an explicit world, or reuse the existing nearest-toolchain/Lake
/// ownership rule. A project cannot implicitly opt in to a measured world:
/// a project world that rule refuses is carried in the decision as the
/// refusal of its imports ([`SourceWorldDecision::imports`]).
///
/// # Errors
/// An explicit world that is a canary, missing or another build, and an
/// import world with no source-language decision, are refused by name.
pub fn source_world_for_file(
    file: &Path,
    explicit: Option<LeanWorld>,
) -> Result<SourceWorldDecision, SourceWorldRefusal> {
    source_world_for(
        lean_worlds(),
        file,
        explicit,
        &crate::lean_toolchain::direct_elan_roots(),
    )
}

fn source_world_for(
    table: &'static [LeanWorldRow],
    file: &Path,
    explicit: Option<LeanWorld>,
    roots: &[PathBuf],
) -> Result<SourceWorldDecision, SourceWorldRefusal> {
    let imports = match explicit {
        None => import_world_for(table, file, roots),
        Some(world) => {
            let refuse = |reason: String| SourceWorldRefusal::Explicit { world, reason };
            let row = row_of_source_world(table, world)
                .ok_or_else(|| refuse("no measured registry row".to_string()))?;
            if row.state == WorldState::Canary {
                return Err(refuse("canary artifacts remain refused".to_string()));
            }
            let lib = installed_library(row, roots).map_err(refuse)?;
            Ok(ImportWorld::Explicit { world, lib })
        }
    };
    Ok(SourceWorldDecision {
        world: source_world_of(&imports)?,
        imports,
    })
}

fn installed_library(row: &LeanWorldRow, elan_roots: &[PathBuf]) -> Result<PathBuf, String> {
    let directory = format!("{}{}", LEAN_OWNER, row.world)
        .replace('/', "--")
        .replacen(':', "---", 1);
    let lib = elan_roots
        .iter()
        .map(|root| root.join("toolchains").join(&directory).join("lib/lean"))
        .find(|lib| lib.join("Init/Prelude.olean").is_file())
        .ok_or_else(|| {
            format!(
                "not installed (no {directory}/lib/lean under {})",
                elan_roots
                    .iter()
                    .map(|root| root.display().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })?;
    match installed_identity(&lib) {
        Some(identity) if identity == row.identity => Ok(lib),
        found => Err(format!(
            "installed at {} as another build ({}), not {}",
            lib.display(),
            found.map_or_else(|| "an unreadable header".to_string(), |i| i.describe()),
            row.identity.describe()
        )),
    }
}

/// A checked file's project names a Lean world its imports cannot resolve
/// in: not a world this Clean reads without a declaration, not installed, or
/// installed as another build.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error(
    "the project's Lean world `{toolchain}` (named by {}) {reason}; its imports are refused \
     rather than resolved in another Lean world",
    .lean_toolchain.display()
)]
pub struct ImportWorldRefusal {
    /// The toolchain the `lean-toolchain` file names, as written there.
    pub toolchain: String,
    /// The `lean-toolchain` file.
    pub lean_toolchain: PathBuf,
    /// Why the world cannot be used.
    pub reason: String,
}

/// Where a file's world is looked up from: `<ws>` for a file under
/// `<ws>/.lake/packages/` (the outermost such pair), since Lake builds every
/// package of a workspace with the root's toolchain; the file itself
/// otherwise.
fn world_anchor(file: &Path) -> PathBuf {
    let components: Vec<_> = file.components().collect();
    components
        .windows(2)
        .position(|pair| pair[0].as_os_str() == ".lake" && pair[1].as_os_str() == "packages")
        .map_or_else(
            || file.to_path_buf(),
            |at| components[..at].iter().collect(),
        )
}

/// Whether `dir` is a Lake package root: it holds the package's lakefile
/// (one that is not a file, which Lake refuses to read, still stops the
/// search, and [`lake_package::package_owns`] cannot read it).
fn is_lake_package_root(dir: &Path) -> bool {
    dir.join("lakefile.lean").exists() || dir.join("lakefile.toml").exists()
}

/// Which `lean-toolchain` names a file's world ([`world_lean_toolchain`]).
#[derive(Debug)]
enum Located {
    /// None at or above the file: the checkout's pin.
    Nothing,
    /// This one.
    At(PathBuf),
    /// One nearer than the enclosing Lake package's, naming another
    /// toolchain, under a lakefile that does not say plainly whether the
    /// package builds the file.
    Ambiguous {
        nearer: PathBuf,
        package_root: PathBuf,
    },
}

/// The nearest `lean-toolchain` at or above `dir`.
fn nearest_from(dir: &Path) -> Option<PathBuf> {
    dir.ancestors()
        .map(|dir| dir.join("lean-toolchain"))
        .find(|candidate| candidate.is_file())
}

/// Whether two `lean-toolchain` files name the same toolchain.
fn same_toolchain(a: &Path, b: &Path) -> bool {
    let read = |path: &Path| std::fs::read_to_string(path).ok();
    match (read(a), read(b)) {
        (Some(a), Some(b)) => matches!(
            (toolchain_line(&a), toolchain_line(&b)),
            (Some(a), Some(b)) if a == b
        ),
        _ => false,
    }
}

/// The `lean-toolchain` the tool that checks `file` reads.
///
/// - A file of a Lake dependency (under `<ws>/.lake/packages/`, as the path
///   is given, so a symlinked dependency keeps it) takes `<ws>`'s, as Lake
///   builds every package of a workspace with the root's toolchain
///   ([`world_anchor`]).
/// - Otherwise the nearest at or above the file's directory, unless it lies
///   below the nearest Lake package root above the file (a directory with a
///   `lakefile.lean` or `lakefile.toml`) and that package builds the file
///   ([`lake_package::package_owns`]): `lake build` then runs the package's
///   toolchain, the nearest at or above its root. A package that does not
///   build the file leaves it to `lean` run from its own directory, which
///   reads the nearer one. A lakefile that does not say plainly is
///   [`Located::Ambiguous`] when the two name different toolchains.
///
/// Measured 2026-10-22 with elan 4.2.3: in a v4.8.0 package with
/// `[[lean_lib]] name = "Inner"`, `lake build Inner.Lib`, `lake env lean
/// Inner/Lib.lean` and `lean Inner/Lib.lean` run from the root use Lean 4.8.0
/// although `Inner/lean-toolchain` names v4.30.0-rc2; under a package whose
/// only library is `Outer`, `lake build proj.Probe` is "unknown target" and
/// `lean Probe.lean` in `proj/` runs `proj/lean-toolchain`'s Lean 4.8.0.
fn world_lean_toolchain(file: &Path) -> Located {
    let given = std::path::absolute(file).unwrap_or_else(|_| file.to_path_buf());
    let anchor = world_anchor(&given);
    if anchor != given {
        let workspace = anchor.canonicalize().unwrap_or(anchor);
        return nearest_from(&workspace).map_or(Located::Nothing, Located::At);
    }
    let file = given.canonicalize().unwrap_or(given);
    let dir = if file.is_dir() {
        file.clone()
    } else {
        match file.parent() {
            Some(dir) => dir.to_path_buf(),
            None => return Located::Nothing,
        }
    };
    let Some(nearest) = nearest_from(&dir) else {
        return Located::Nothing;
    };
    let Some(root) = dir.ancestors().find(|dir| is_lake_package_root(dir)) else {
        return Located::At(nearest);
    };
    let below_root = nearest
        .parent()
        .is_some_and(|holder| holder != root && holder.starts_with(root));
    if !below_root {
        return Located::At(nearest);
    }
    let package = nearest_from(root);
    match lake_package::package_owns(root, &file) {
        Ownership::NotOwned => Located::At(nearest),
        Ownership::Owned => package.map_or(Located::Nothing, Located::At),
        Ownership::Unknown => match package {
            Some(package) if same_toolchain(&nearest, &package) => Located::At(nearest),
            _ => Located::Ambiguous {
                nearer: nearest,
                package_root: root.to_path_buf(),
            },
        },
    }
}

/// The toolchain a `lean-toolchain` file names, read as elan 4.2.3 reads it
/// (measured 2026-10-21): its FIRST line with surrounding whitespace trimmed;
/// later lines are ignored. `None` when elan refuses the file ("invalid
/// toolchain name"): an empty first line (a leading blank line included), a
/// comment, a byte-order mark, or any other character outside a toolchain
/// name's.
fn toolchain_line(content: &str) -> Option<&str> {
    let line = content.lines().next()?.trim();
    let name_char = |c: char| c.is_ascii_alphanumeric() || "._-+:/".contains(c);
    (!line.is_empty() && !line.starts_with('-') && line.chars().all(name_char)).then_some(line)
}

/// A Clean toolchain (`clean:stable`, `<org>/clean:v1.1.0`): a Clean project,
/// whose stdlib is this binary's own pin.
fn names_clean_toolchain(toolchain: &str) -> bool {
    toolchain == "clean"
        || toolchain
            .rsplit_once(':')
            .is_some_and(|(owner, _)| owner == "clean" || owner.ends_with("/clean"))
}

/// The world tag of a Lean toolchain: `v4.8.0` for `leanprover/lean4:v4.8.0`
/// and for elan's short spelling `v4.8.0`; `None` for another owner.
fn lean_world_tag(toolchain: &str) -> Option<&str> {
    match toolchain.strip_prefix(LEAN_OWNER) {
        Some(tag) => Some(tag),
        None => (!toolchain.contains(':') && toolchain.starts_with('v')).then_some(toolchain),
    }
}

/// The worlds of `table` read without a declaration, for a refusal to name.
fn readable_worlds(table: &[LeanWorldRow]) -> String {
    table
        .iter()
        .filter(|row| row.state.implicit())
        .map(|row| format!("{} ({})", row.world, row.state.label()))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The header identity of the stdlib at `lib`, read from its
/// `Init/Prelude.olean` header alone.
fn installed_identity(lib: &Path) -> Option<HeaderIdentity> {
    use std::io::Read;
    let mut bytes = Vec::with_capacity(HEADER_SIZE_V2);
    std::fs::File::open(lib.join("Init/Prelude.olean"))
        .ok()?
        .take(HEADER_SIZE_V2 as u64)
        .read_to_end(&mut bytes)
        .ok()?;
    OleanHeader::parse(&bytes)
        .ok()
        .map(|header| HeaderIdentity::of_header(&header))
}

/// The world `file`'s imports resolve in, over the worlds of `table` and the
/// elan roots to look for an installed toolchain under.
///
/// # Errors
///
/// [`ImportWorldRefusal`] when the file's `lean-toolchain` names a world
/// `table` does not read without a declaration, one that is not installed
/// under `elan_roots`, or an installation whose `Init/Prelude.olean` is not
/// that world's build.
pub(crate) fn import_world_for(
    table: &'static [LeanWorldRow],
    file: &Path,
    elan_roots: &[PathBuf],
) -> Result<ImportWorld, ImportWorldRefusal> {
    let (lean_toolchain, ambiguous_with) = match world_lean_toolchain(file) {
        Located::Nothing => return Ok(ImportWorld::CheckoutPin),
        Located::At(path) => (path, None),
        Located::Ambiguous {
            nearer,
            package_root,
        } => (nearer, Some(package_root)),
    };
    let raw = std::fs::read_to_string(&lean_toolchain).unwrap_or_default();
    let line = toolchain_line(&raw);
    let written = line.unwrap_or(raw.trim()).to_string();
    let refuse = |reason: String| ImportWorldRefusal {
        toolchain: written.clone(),
        lean_toolchain: lean_toolchain.clone(),
        reason,
    };
    if let Some(root) = ambiguous_with {
        return Err(refuse(format!(
            "is nearer than the toolchain of the Lake package at {}, which names another, and \
             that package's lakefile does not say plainly whether it builds this file \
             (`lake build` there would run the package's Lean, `lean` here this one)",
            root.display()
        )));
    }
    if line.is_none() {
        return Err(refuse(
            "is not a toolchain name elan reads (its first line, trimmed, must be one)".to_string(),
        ));
    }
    if names_clean_toolchain(&written) {
        return Ok(ImportWorld::CheckoutPin);
    }
    let Some(row) = lean_world_tag(&written).and_then(|tag| row_of_world(table, tag)) else {
        return Err(refuse(format!(
            "is not a Lean world this Clean reads (it reads {})",
            readable_worlds(table)
        )));
    };
    match row.state {
        WorldState::Oracle => return Ok(ImportWorld::CheckoutPin),
        WorldState::Historical | WorldState::FrontendOnly => {}
        WorldState::Measured | WorldState::Canary => {
            return Err(refuse(format!(
                "is a {} world, which no project selects by its lean-toolchain (R38)",
                row.state.label()
            )))
        }
    }
    let directory = format!("{}{}", LEAN_OWNER, row.world)
        .replace('/', "--")
        .replacen(':', "---", 1);
    let Some(lib) = elan_roots
        .iter()
        .map(|root| root.join("toolchains").join(&directory).join("lib/lean"))
        .find(|lib| lib.join("Init/Prelude.olean").is_file())
    else {
        return Err(refuse(format!(
            "is not installed (no {directory}/lib/lean under {})",
            elan_roots
                .iter()
                .map(|root| root.join("toolchains").display().to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )));
    };
    match installed_identity(&lib) {
        Some(identity) if identity == row.identity => Ok(ImportWorld::Project {
            world: row.world,
            lean_toolchain: lean_toolchain.clone(),
            lib,
        }),
        found => Err(refuse(format!(
            "is installed at {} as another build ({}), not {}",
            lib.display(),
            found.map_or_else(|| "an unreadable header".to_string(), |i| i.describe()),
            row.identity.describe()
        ))),
    }
}

/// The world `file`'s imports resolve in ([`import_world_for`] over the
/// worlds of `lean_worlds.tsv` and this process's elan roots).
///
/// # Errors
///
/// [`ImportWorldRefusal`], as [`import_world_for`].
pub fn import_world_for_file(file: &Path) -> Result<ImportWorld, ImportWorldRefusal> {
    import_world_for(
        lean_worlds(),
        file,
        &crate::lean_toolchain::direct_elan_roots(),
    )
}

/// The default search roots of `world`: [`crate::default_search_paths`],
/// with a project world's stdlib in place of the checkout's pin.
#[must_use]
pub fn search_paths_in_world(world: &ImportWorld) -> Vec<PathBuf> {
    search_paths_in_world_with(
        world,
        |key: &str| std::env::var_os(key),
        |path: &Path| std::fs::read_dir(path),
    )
}

/// [`search_paths_in_world`] over the given environment lookup.
pub(crate) fn search_paths_in_world_with<F, R>(
    world: &ImportWorld,
    var_lookup: F,
    read_dir: R,
) -> Vec<PathBuf>
where
    F: for<'a> FnMut(&'a str) -> Option<std::ffi::OsString>,
    R: for<'a> FnMut(&'a Path) -> std::io::Result<std::fs::ReadDir>,
{
    let lib = match world {
        ImportWorld::CheckoutPin => crate::pinned_lean_lib_path(),
        ImportWorld::Project { lib, .. } => Some(lib.clone()),
        ImportWorld::Explicit { lib, .. } => Some(lib.clone()),
    };
    collect_default_search_paths_with_pinned(var_lookup, read_dir, lib)
}
