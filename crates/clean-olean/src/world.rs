// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean worlds: which Lean build wrote an `.olean` part, and which builds
//! this Clean reads (docs/DECISIONS.md R38, R81).
//!
//! Pinned `lean` reads a part only when its header carries its own build's
//! identity: header version, flags and githash (`module.cpp`,
//! `lean_compacted_region_read`, "incompatible header" otherwise). The
//! header's `lean_version` string is never compared there, and is only
//! informative here. The worlds Clean reads are the rows of
//! `crates/clean-olean/lean_worlds.tsv`; `build.rs` measures each row's
//! identity from the tracked fixtures it names, so the set is a property of
//! the commit, never of the box or of a hand-typed hash.
//!
//! The import gate that holds an environment to one world is
//! `import::world_gate`.

use crate::error::{OleanError, OleanResult};
use crate::header::{OleanHeader, HEADER_SIZE_V2, MAGIC, VERSION};
use crate::region::{CompactedRegion, TypedModuleLayout};

#[cfg(test)]
#[path = "world_tests.rs"]
mod tests;

/// Length of the githash every header identity compares.
const GITHASH_LEN: usize = 40;

/// What pinned `lean` compares before it reads an `.olean` part.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct HeaderIdentity {
    version: u8,
    flags: u8,
    githash: [u8; GITHASH_LEN],
}

impl HeaderIdentity {
    /// An identity from its three fields (`build.rs` writes these from the
    /// fixtures it measured).
    pub(crate) const fn from_parts(version: u8, flags: u8, githash: [u8; GITHASH_LEN]) -> Self {
        Self {
            version,
            flags,
            githash,
        }
    }

    /// The identity of a parsed v1 or v2 header. A v1 header has no flags
    /// byte; its identity's flags are 0.
    pub(crate) fn of_header(header: &OleanHeader) -> Self {
        let mut githash = [0u8; GITHASH_LEN];
        githash.copy_from_slice(&header.git_hash[..GITHASH_LEN]);
        Self::from_parts(header.version, header.flags, githash)
    }

    /// `olean v2, flags 0x01, githash 3dc1…` (a v1 header has no flags).
    pub(crate) fn describe(&self) -> String {
        let githash = self.githash.escape_ascii();
        if self.version == VERSION {
            format!("olean v{}, githash {githash}", self.version)
        } else {
            format!(
                "olean v{}, flags 0x{:02x}, githash {githash}",
                self.version, self.flags
            )
        }
    }
}

pub(crate) use clean_kernel::lean_world::LeanWorldState as WorldState;

/// One measured artifact row. Raw labels also support injected format-policy
/// tests; production source selection looks up this table by `LeanWorld`.
/// A label alone grants no source-language feature permission.
#[derive(Clone, Copy, Debug)]
pub(crate) struct LeanWorldRow {
    /// The release, as `lean-toolchain` spells its tag (`v4.30.0-rc2`).
    pub(crate) world: &'static str,
    /// What Clean does with its parts.
    pub(crate) state: WorldState,
    /// Measured by `build.rs` from the row's tracked fixtures.
    pub(crate) identity: HeaderIdentity,
    /// The fixtures' header `lean_version`, informative only (`None` for v1).
    pub(crate) lean_version: Option<&'static str>,
}

include!(concat!(env!("OUT_DIR"), "/lean_worlds.rs"));

/// Every world this build of Clean knows, in `lean_worlds.tsv` order.
pub(crate) fn lean_worlds() -> &'static [LeanWorldRow] {
    LEAN_WORLD_ROWS
}

/// The row of `table` whose identity is `identity`.
pub(crate) fn row_of_identity(
    table: &'static [LeanWorldRow],
    identity: &HeaderIdentity,
) -> Option<&'static LeanWorldRow> {
    table.iter().find(|row| &row.identity == identity)
}

/// The row of `table` named `world`.
pub(crate) fn row_of_world(
    table: &'static [LeanWorldRow],
    world: &str,
) -> Option<&'static LeanWorldRow> {
    table.iter().find(|row| row.world == world)
}

/// Look up a production source choice without accepting an arbitrary label.
pub(crate) fn row_of_source_world(
    table: &'static [LeanWorldRow],
    world: clean_kernel::LeanWorld,
) -> Option<&'static LeanWorldRow> {
    row_of_world(table, world.tag())
}

impl crate::ndjson::ExportWriteMeta {
    /// The selected source world's header, with the release identity measured
    /// from its Lean artifacts. A reader selects its own rules for this world.
    #[must_use]
    pub fn for_source_world(world: clean_kernel::LeanWorld) -> Option<Self> {
        let row = row_of_source_world(lean_worlds(), world)?;
        let version = world.tag().strip_prefix('v')?;
        Some(Self {
            lean_version: version.to_owned(),
            lean_githash: std::str::from_utf8(&row.identity.githash).ok()?.to_owned(),
        })
    }
}

/// Who wrote one `.olean` part.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum PartWriter {
    /// Lean: its header identity, and the header's informative version
    /// string (v2 and later).
    Lean {
        /// Header version, flags and githash.
        identity: HeaderIdentity,
        /// The header `lean_version`, never compared.
        lean_version: Option<String>,
    },
    /// Clean's own exporter (`TypedModuleLayout::CleanLegacy`): a part of no
    /// Lean world. Its githash is whatever the exporter was handed.
    Clean,
}

/// Who wrote the `.olean` part `bytes` (the whole part: a v1 header is told
/// apart from Clean's exporter by its root `ModuleData` layout, the
/// importer's own discriminator).
///
/// # Errors
///
/// The header or, for a v1 header, the root `ModuleData` does not parse, as
/// the importer's parser would report it.
pub(crate) fn part_writer_of_bytes(bytes: &[u8]) -> OleanResult<PartWriter> {
    if bytes.len() <= MAGIC.len() || &bytes[..MAGIC.len()] != MAGIC {
        // Too small or not an `.olean`: the header parser names which.
        OleanHeader::parse(bytes)?;
        return Err(OleanError::Region("not an .olean header".into()));
    }
    let version = bytes[MAGIC.len()];
    if version == VERSION {
        let header = OleanHeader::parse(bytes)?;
        let layout = CompactedRegion::new(bytes, header.base_addr).typed_module_layout()?;
        return Ok(match layout {
            TypedModuleLayout::CleanLegacy => PartWriter::Clean,
            TypedModuleLayout::LeanV1 | TypedModuleLayout::LeanV2 => PartWriter::Lean {
                identity: HeaderIdentity::of_header(&header),
                lean_version: None,
            },
        });
    }
    // v2, and v3 (Lean v4.36.0-rc1's closure format), share the 88-byte fixed
    // header (module.cpp@v4.36.0-rc1 `olean_header`): flags at 6, the version
    // string at 7..40, the githash at 40..80. A later version is read the
    // same way, only so that its refusal can name it.
    if bytes.len() < HEADER_SIZE_V2 {
        return Err(OleanError::FileTooSmall {
            expected: HEADER_SIZE_V2,
            actual: bytes.len(),
        });
    }
    let mut githash = [0u8; GITHASH_LEN];
    githash.copy_from_slice(&bytes[40..40 + GITHASH_LEN]);
    let raw = &bytes[7..40];
    let end = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
    Ok(PartWriter::Lean {
        identity: HeaderIdentity::from_parts(version, bytes[6], githash),
        lean_version: Some(String::from_utf8_lossy(&raw[..end]).into_owned()),
    })
}
