// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The import world gate (docs/DECISIONS.md R38, R81).
//!
//! Pinned `lean` reads an `.olean` part only when its header carries its own
//! build's identity. Clean reads the worlds of
//! `crates/clean-olean/lean_worlds.tsv` ([`crate::world`]) and holds every
//! environment to ONE of them:
//!
//! * a Lean part whose identity no row carries, or a Canary row's, is refused
//!   by name ([`ImportError::UnsupportedLeanWorld`]);
//! * a Measured row's part loads only into an environment that declared that
//!   world ([`declare`]); an Oracle, Historical or Frontend-only row's loads
//!   without a declaration;
//! * the first Lean part an environment reads, or a declaration, binds it to
//!   that world, and a part of another world is refused
//!   ([`ImportError::MixedLeanWorlds`]);
//! * a part Clean's own exporter wrote (`TypedModuleLayout::CleanLegacy`) is
//!   of no world: it reads the world of the environment it loads into, whose
//!   Lean parts are its imports. Its githash is whatever the exporter was
//!   handed, so it identifies nothing.
//!
//! The binding is decided where every `LoadModule` registers
//! (`load_register::load_module_part_direct`, [`admit_part`]), and checked
//! earlier, without binding, wherever a loader reads a module's bytes before
//! it walks the module's imports ([`check_part_bytes`]), so a foreign module
//! is refused by name rather than by whatever its imports fail with first.
//!
//! A loader that reads parts itself and never registers one through
//! `load_module_part_direct` (`clean mathverse per-constant-verify`, which
//! registers through `load_parsed_module*`, and the closure-shard builder and
//! verifier) holds a [`LeanWorldScope`] to the same rule (R81).
//!
//! The gate compares identities; it does not authenticate them. A forged
//! header with the Oracle's identity passes it, as it passes `lean`.

use super::artifact_ledger::NoLedgerEntry;
use super::ImportError;
use crate::world::{self, LeanWorldRow, PartWriter, WorldState};
use clean_kernel::env::{
    register_persistent_ext, EnvExtensionEntry, Environment, ExtensionIdx, PersistentExtState,
};
use clean_kernel::name::Name;

#[cfg(test)]
#[path = "world_gate_tests.rs"]
mod tests;

#[path = "world_scope.rs"]
mod scope;
pub use scope::LeanWorldScope;

/// The `first` of a binding made by [`declare`].
const DECLARATION: &str = "<declaration>";

/// The world an environment reads, and the first part (or declaration) that
/// bound it. In-process state only: never exported, never snapshotted.
#[derive(Clone, Debug, Default)]
pub(crate) struct WorldBinding {
    bound: Option<(&'static str, String)>,
}

impl PersistentExtState for WorldBinding {
    type Entry = NoLedgerEntry;

    fn add_entry(&mut self, _entry: &Self::Entry) {}

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

static WORLD_BINDING_IDX: std::sync::OnceLock<ExtensionIdx> = std::sync::OnceLock::new();

fn binding_idx() -> ExtensionIdx {
    *WORLD_BINDING_IDX.get_or_init(|| {
        register_persistent_ext::<WorldBinding>(Name::from_string("Clean.olean.leanWorld"))
    })
}

fn bound(env: &Environment) -> Option<(&'static str, &str)> {
    env.get_ext_state::<WorldBinding>(binding_idx())?
        .bound
        .as_ref()
        .map(|(world, first)| (*world, first.as_str()))
}

fn level_profile(world: &str) -> Result<clean_kernel::level::LeanLevelProfile, ImportError> {
    // Entire official level.cpp comparisons pin these two operation
    // algebras. Informative header version strings never select one.
    world
        .parse::<clean_kernel::LeanWorld>()
        .map(clean_kernel::LeanWorld::level_profile)
        .map_err(|_| ImportError::UnknownLeanWorld {
            world: world.into(),
            reason: "no qualified universe algebra for this world".into(),
        })
}

fn bind(env: &mut Environment, world: &'static str, first: &str) -> Result<(), ImportError> {
    let profile = level_profile(world)?;
    env.set_lean_level_profile(profile);
    env.get_ext_state_mut::<WorldBinding>(binding_idx()).bound = Some((world, first.to_string()));
    Ok(())
}

pub(crate) fn validate_level_profile(env: &Environment) -> Result<(), ImportError> {
    if let Some((world, _)) = bound(env) {
        let expected = level_profile(world)?;
        if env.lean_level_profile() != expected {
            return Err(ImportError::UnknownLeanWorld {
                world: world.into(),
                reason: format!(
                    "source world requires {expected:?} universe algebra, found {:?}",
                    env.lean_level_profile()
                ),
            });
        }
    }
    Ok(())
}

/// What one part does to an environment's binding.
#[derive(Debug, PartialEq, Eq)]
enum Decision {
    /// Clean-written: no world.
    Neutral,
    /// The environment already reads this part's world.
    Same,
    /// The first Lean part: the environment now reads its world.
    Bind(&'static str),
}

/// The worlds `table` reads, for a refusal to name.
fn supported(table: &'static [LeanWorldRow]) -> Vec<String> {
    table
        .iter()
        .filter(|row| row.state != WorldState::Canary)
        .map(|row| {
            let state = if row.state.implicit() {
                row.state.label().to_string()
            } else {
                format!("{}, once declared", row.state.label())
            };
            let version = row
                .lean_version
                .map(|v| format!(" (lean_version \"{v}\")"))
                .unwrap_or_default();
            format!(
                "{} ({state}): {}{version}",
                row.world,
                row.identity.describe()
            )
        })
        .collect()
}

fn unsupported(table: &'static [LeanWorldRow], label: &str, found: String) -> ImportError {
    ImportError::UnsupportedLeanWorld {
        module: label.to_string(),
        found,
        supported: supported(table),
    }
}

/// The rule, over an explicit `table` and the environment's binding `bound`
/// (`(world, first)`), for the part labelled `label` that `writer` wrote.
fn decide(
    table: &'static [LeanWorldRow],
    bound: Option<(&str, &str)>,
    label: &str,
    writer: &PartWriter,
) -> Result<Decision, ImportError> {
    let PartWriter::Lean {
        identity,
        lean_version,
    } = writer
    else {
        return Ok(Decision::Neutral);
    };
    let Some(row) = world::row_of_identity(table, identity) else {
        let version = lean_version
            .as_deref()
            .map(|v| format!(", header lean_version \"{v}\""))
            .unwrap_or_default();
        return Err(unsupported(
            table,
            label,
            format!(
                "Lean ({}{version}), which is no world this build of Clean reads",
                identity.describe()
            ),
        ));
    };
    if row.state == WorldState::Canary {
        return Err(unsupported(
            table,
            label,
            format!(
                "Lean {} ({}), a Canary world, whose .olean files Clean refuses by name",
                row.world,
                identity.describe()
            ),
        ));
    }
    match bound {
        Some((world, _)) if world == row.world => Ok(Decision::Same),
        Some((world, first)) => Err(ImportError::MixedLeanWorlds {
            module: label.to_string(),
            world: row.world.to_string(),
            first: first.to_string(),
            first_world: world.to_string(),
        }),
        None if row.state.implicit() => Ok(Decision::Bind(row.world)),
        None => Err(unsupported(
            table,
            label,
            format!(
                "Lean {} ({}), a {} world this environment has not declared \
                 (clean_olean::declare_environment_world)",
                row.world,
                identity.describe(),
                row.state.label()
            ),
        )),
    }
}

/// The rule for declaring `world` over `table` and the binding `bound`: the
/// world to bind, or `None` when the environment already reads it.
fn declaration(
    table: &'static [LeanWorldRow],
    bound: Option<(&str, &str)>,
    world: &str,
) -> Result<Option<&'static str>, ImportError> {
    let Some(row) = world::row_of_world(table, world) else {
        return Err(ImportError::UnknownLeanWorld {
            world: world.to_string(),
            reason: "no row of crates/clean-olean/lean_worlds.tsv names it".to_string(),
        });
    };
    if row.state == WorldState::Canary {
        return Err(ImportError::UnknownLeanWorld {
            world: world.to_string(),
            reason: "it is a Canary world, whose .olean files Clean refuses by name".to_string(),
        });
    }
    match bound {
        Some((bound_world, _)) if bound_world == row.world => Ok(None),
        Some((bound_world, first)) => Err(ImportError::MixedLeanWorlds {
            module: DECLARATION.to_string(),
            world: row.world.to_string(),
            first: first.to_string(),
            first_world: bound_world.to_string(),
        }),
        None => Ok(Some(row.world)),
    }
}

fn writer_of(bytes: &[u8]) -> Result<PartWriter, ImportError> {
    Ok(world::part_writer_of_bytes(bytes)?)
}

/// Admit the part `bytes`, labelled `label`, into `env`: refuse it by name
/// when its world is not one `env` may read, and bind `env` to its world
/// when it is the first Lean part `env` reads.
pub(crate) fn admit_part(
    env: &mut Environment,
    label: Option<&str>,
    bytes: &[u8],
) -> Result<(), ImportError> {
    validate_level_profile(env)?;
    let label = label.unwrap_or("<unnamed module>");
    if let Decision::Bind(world) =
        decide(world::lean_worlds(), bound(env), label, &writer_of(bytes)?)?
    {
        bind(env, world, label)?;
    }
    Ok(())
}

/// [`admit_part`] without binding: what a loader asks of a module's bytes
/// before it walks the module's imports.
///
/// A part whose writer cannot be read here is left to the parser the loader
/// runs next, which refuses it with its own error; [`admit_part`], where it
/// would register, still refuses it.
pub(crate) fn check_part_bytes(
    env: &Environment,
    label: &str,
    bytes: &[u8],
) -> Result<(), ImportError> {
    let Ok(writer) = world::part_writer_of_bytes(bytes) else {
        return Ok(());
    };
    decide(world::lean_worlds(), bound(env), label, &writer).map(|_| ())
}

/// The world of the part `bytes` as an environment that declared nothing
/// would read it: `Some(world)` for a Lean part it may read, `None` for a
/// part Clean wrote.
///
/// # Errors
///
/// The part does not parse, or its world is refused
/// ([`ImportError::UnsupportedLeanWorld`]).
pub(crate) fn part_world(label: &str, bytes: &[u8]) -> Result<Option<&'static str>, ImportError> {
    Ok(
        match decide(world::lean_worlds(), None, label, &writer_of(bytes)?)? {
            Decision::Bind(world) => Some(world),
            Decision::Neutral | Decision::Same => None,
        },
    )
}

/// Bind an environment restored from a snapshot of a closure whose world
/// [`part_world`] measured to that world (a snapshot carries no binding).
pub(crate) fn bind_restored(
    env: &mut Environment,
    world: &'static str,
    first: &str,
) -> Result<(), ImportError> {
    let expected = level_profile(world)?;
    if env.lean_level_profile() != expected {
        return Err(ImportError::UnknownLeanWorld {
            world: world.into(),
            reason: "verified snapshot has a different universe algebra; cold replay required"
                .into(),
        });
    }
    env.get_ext_state_mut::<WorldBinding>(binding_idx()).bound = Some((world, first.into()));
    Ok(())
}

/// Declare that `env` reads `world` (`crate::declare_environment_world`).
pub(crate) fn declare(env: &mut Environment, world: &str) -> Result<(), ImportError> {
    validate_level_profile(env)?;
    if let Some(world) = declaration(world::lean_worlds(), bound(env), world)? {
        bind(env, world, DECLARATION)?;
    }
    Ok(())
}

/// The world `env` reads (`crate::environment_world`).
pub(crate) fn environment_world(env: &Environment) -> Option<&'static str> {
    bound(env).map(|(world, _)| world)
}
