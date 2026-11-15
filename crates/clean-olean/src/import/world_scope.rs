// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! [`LeanWorldScope`]: the world gate for a loader that reads `.olean` parts
//! itself (docs/DECISIONS.md R81).
//!
//! Every loader of this crate registers a part through
//! `load_register::load_module_part_direct`, where [`super::admit_part`]
//! holds the environment to one world. A loader outside it can read parts
//! without passing that point: `clean mathverse per-constant-verify` parses
//! its closure with `parse_module_file` and registers through
//! `load_parsed_module*` (a `ParsedModule` has no header), and the
//! closure-shard builder and verifier bind a `.mathverse` shard to its source
//! `.olean`. A scope holds such a loader to the same rule
//! ([`super::decide`]): the first Lean part it admits binds it, a part of an
//! unsupported world or of a second world is refused by name, and a part
//! Clean's exporter wrote is of no world.

use std::io::Read;
use std::path::Path;

use super::{bind, bound, decide, writer_of, Decision, ImportError};
use crate::header::{HEADER_SIZE_V2, MAGIC, VERSION};
use crate::world;
use clean_kernel::env::Environment;

/// One Lean world across the `.olean` parts a loader reads itself, held by
/// the rule an environment is held to.
#[derive(Clone, Debug, Default)]
pub struct LeanWorldScope {
    /// The world, and the part that bound it.
    bound: Option<(&'static str, String)>,
}

impl LeanWorldScope {
    /// A scope that has admitted nothing.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// A scope bound as `env` is, for a loader that reads parts itself into
    /// an environment the crate's loaders filled.
    #[must_use]
    pub fn of_environment(env: &Environment) -> Self {
        Self {
            bound: bound(env).map(|(world, first)| (world, first.to_string())),
        }
    }

    /// The world the scope reads, once a Lean part bound it.
    #[must_use]
    pub fn world(&self) -> Option<&'static str> {
        self.bound.as_ref().map(|(world, _)| *world)
    }

    /// Admit the part `bytes`, labelled `label` (its module name): refuse it
    /// by name when its world is not one the scope may read, and bind the
    /// scope to its world when it is the first Lean part.
    ///
    /// # Errors
    ///
    /// The header (or a v1 part's root `ModuleData`) does not parse;
    /// [`ImportError::UnsupportedLeanWorld`] for a world this build does not
    /// read; [`ImportError::MixedLeanWorlds`] for a part of a second world.
    pub fn admit_part(&mut self, label: &str, bytes: &[u8]) -> Result<(), ImportError> {
        let binding = self
            .bound
            .as_ref()
            .map(|(world, first)| (*world, first.as_str()));
        if let Decision::Bind(world) =
            decide(world::lean_worlds(), binding, label, &writer_of(bytes)?)?
        {
            self.bound = Some((world, label.to_string()));
        }
        Ok(())
    }

    /// [`Self::admit_part`] for the part at `path`. Only the 88-byte header
    /// is read, except for a v1 header, whose writer is told apart by its
    /// root `ModuleData` and so needs the whole part.
    ///
    /// # Errors
    ///
    /// [`ImportError::FileUnreadable`], or what [`Self::admit_part`] refuses.
    pub fn admit_olean_file(&mut self, label: &str, path: &Path) -> Result<(), ImportError> {
        let bytes = read_identity_bytes(path)?;
        self.admit_part(label, &bytes)
    }

    /// Admit the `.olean.server` and `.olean.private` companions beside the
    /// base part `path`, each that exists, labelled `{label}._server` and
    /// `{label}._private` as the module loaders label them.
    ///
    /// # Errors
    ///
    /// As [`Self::admit_olean_file`], for either companion.
    pub fn admit_companions(&mut self, label: &str, path: &Path) -> Result<(), ImportError> {
        for (extension, suffix) in [("olean.server", "._server"), ("olean.private", "._private")] {
            let companion = path.with_extension(extension);
            if companion.exists() {
                self.admit_olean_file(&format!("{label}{suffix}"), &companion)?;
            }
        }
        Ok(())
    }

    /// The artifact at `path`: its base part, then its companions.
    ///
    /// # Errors
    ///
    /// As [`Self::admit_olean_file`] and [`Self::admit_companions`].
    pub fn admit_artifact(&mut self, label: &str, path: &Path) -> Result<(), ImportError> {
        self.admit_olean_file(label, path)?;
        self.admit_companions(label, path)
    }

    /// Bind `env` to the scope's world, the part that bound the scope as its
    /// first: `env` then reads that world, as it would had a loader of this
    /// crate registered that part. A scope that read no Lean part leaves
    /// `env` as it is.
    ///
    /// # Errors
    ///
    /// [`ImportError::MixedLeanWorlds`] when `env` already reads another
    /// world.
    pub fn bind_environment(&self, env: &mut Environment) -> Result<(), ImportError> {
        let Some(&(world, ref first)) = self.bound.as_ref() else {
            return Ok(());
        };
        super::validate_level_profile(env)?;
        match bound(env) {
            None => {
                bind(env, world, first)?;
                Ok(())
            }
            Some((env_world, _)) if env_world == world => Ok(()),
            Some((env_world, env_first)) => Err(ImportError::MixedLeanWorlds {
                module: first.clone(),
                world: world.to_string(),
                first: env_first.to_string(),
                first_world: env_world.to_string(),
            }),
        }
    }
}

/// The bytes of the part at `path` that its writer is read from: the fixed
/// 88-byte header, or the whole part for a v1 header.
fn read_identity_bytes(path: &Path) -> Result<Vec<u8>, ImportError> {
    let unreadable = |source: std::io::Error| ImportError::FileUnreadable {
        path: path.to_path_buf(),
        source,
    };
    let mut file = std::fs::File::open(path).map_err(unreadable)?;
    let mut bytes = Vec::with_capacity(HEADER_SIZE_V2);
    file.by_ref()
        .take(HEADER_SIZE_V2 as u64)
        .read_to_end(&mut bytes)
        .map_err(unreadable)?;
    if bytes.starts_with(MAGIC) && bytes.get(MAGIC.len()) == Some(&VERSION) {
        file.read_to_end(&mut bytes).map_err(unreadable)?;
    }
    Ok(bytes)
}
