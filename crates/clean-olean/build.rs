// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Build script for clean-olean.
//!
//! Resolves the exact Lean toolchain pinned by the workspace at compile time
//! and emits a visible warning when it is unavailable. Discovery is anchored
//! at `CARGO_MANIFEST_DIR`, so an external Cargo caller cannot accidentally
//! select a different toolchain through its current working directory.
//!
//! See: <https://github.com/alabsystems/clean/issues/1257>

#[path = "lean_toolchain.rs"]
mod lean_toolchain;

fn main() {
    let manifest_dir = std::path::PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"),
    );
    let toolchain_file = manifest_dir
        .parent()
        .and_then(std::path::Path::parent)
        .expect("clean-olean is inside the Clean workspace")
        .join("lean-toolchain");

    println!("cargo:rerun-if-changed={}", toolchain_file.display());
    println!("cargo:rerun-if-changed=lean_toolchain.rs");
    println!("cargo:rerun-if-env-changed=ELAN_HOME");
    println!("cargo:rerun-if-env-changed=HOME");
    println!("cargo:rerun-if-env-changed=USERPROFILE");
    println!(
        "cargo:rerun-if-env-changed={}",
        lean_toolchain::PINNED_LEAN_LIB_ENV
    );
    println!("cargo:rerun-if-env-changed=CLEAN_OLEAN_REQUIRE_PINNED_LEAN");

    let resolved = lean_toolchain::resolve_pinned_lean(&manifest_dir);
    let oracle = write_lean_worlds(&manifest_dir, resolved.as_ref().ok());
    write_toolchain_manifest(resolved.as_ref().ok(), &oracle);
    match resolved {
        Ok(resolved) => {
            println!(
                "cargo:rustc-env={}={}",
                lean_toolchain::PINNED_LEAN_LIB_ENV,
                resolved.lib_path.display()
            );
            println!(
                "cargo:rustc-env={}={}",
                lean_toolchain::PINNED_LEAN_TOOLCHAIN_ENV,
                resolved.toolchain
            );
        }
        Err(error) => {
            println!(
                "cargo:warning=repository-pinned Lean unavailable: {error}. Real-.olean tests \
                 cannot carry toolchain authority; install the toolchain named by {}.",
                toolchain_file.display()
            );
            if std::env::var_os("CLEAN_OLEAN_REQUIRE_PINNED_LEAN").is_some() {
                panic!("CLEAN_OLEAN_REQUIRE_PINNED_LEAN is set: {error}");
            }
        }
    }
}

/// The `.olean` parts the importer reads for one module.
const OLEAN_PART_SUFFIXES: [&str; 3] = [".olean", ".olean.server", ".olean.private"];

/// Every `.olean` part under `dir`, as `/`-separated paths relative to `root`.
fn collect_olean_parts(root: &std::path::Path, dir: &std::path::Path, out: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let Ok(file_type) = entry.file_type() else {
            continue;
        };
        if file_type.is_dir() {
            collect_olean_parts(root, &path, out);
            continue;
        }
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if !OLEAN_PART_SUFFIXES
            .iter()
            .any(|suffix| name.ends_with(suffix))
        {
            continue;
        }
        if let Ok(rel) = path.strip_prefix(root) {
            let rel: Vec<String> = rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect();
            out.push(rel.join("/"));
        }
    }
}

/// Write `$OUT_DIR/pinned_toolchain_manifest.rs`: the pinned toolchain's name
/// and the BLAKE3 digest of every `.olean` part of its library, measured NOW,
/// when this binary is built. A toolchain module is identified at import time
/// by these digests (module-trust round 28: an EMPTY `<lib>/Init/Prelude.olean`
/// used to make a whole search root count as "the toolchain", so its modules
/// were neither bound to their source nor disclosed). A toolchain that is
/// unavailable here yields an empty manifest: every module is then an ordinary
/// artifact, disclosed or bound like any other — never trusted by default.
fn write_toolchain_manifest(
    resolved: Option<&lean_toolchain::PinnedLean>,
    oracle: &(String, Identity),
) {
    use std::fmt::Write as _;
    let out_dir =
        std::path::PathBuf::from(std::env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR"));
    let mut rows: Vec<(String, String)> = Vec::new();
    let mut toolchain = String::new();
    if let Some(resolved) = resolved {
        toolchain.clone_from(&resolved.toolchain);
        let mut rels = Vec::new();
        collect_olean_parts(&resolved.lib_path, &resolved.lib_path, &mut rels);
        rels.sort();
        // Every part the pinned toolchain ships should carry the Oracle's
        // identity; one that does not is refused at import by name, so the
        // disagreement is only reported here (R81).
        let mut foreign: Vec<&str> = Vec::new();
        for rel in &rels {
            let bytes = std::fs::read(resolved.lib_path.join(rel))
                .unwrap_or_else(|e| panic!("cannot read pinned toolchain file {rel}: {e}"));
            if !mint_identity(&bytes).is_ok_and(|id| id.key() == oracle.1.key()) {
                foreign.push(rel);
            }
            rows.push((rel.clone(), blake3::hash(&bytes).to_hex().to_string()));
        }
        if let Some(first) = foreign.first() {
            println!(
                "cargo:warning={} of the {} .olean parts of the pinned toolchain {} (first: {first}) \
                 do not carry the identity of the Oracle world {} ({}) that \
                 crates/clean-olean/lean_worlds.tsv measures from its fixtures; Clean refuses \
                 them at import (UnsupportedLeanWorld)",
                foreign.len(),
                rels.len(),
                resolved.lib_path.display(),
                oracle.0,
                describe(&oracle.1)
            );
        }
    }
    let mut src = String::new();
    writeln!(
        src,
        "/// The pinned Lean toolchain the manifest below was measured from \
         (empty when it was unavailable at build time)."
    )
    .expect("write to String");
    writeln!(
        src,
        "pub(crate) const PINNED_TOOLCHAIN: &str = {toolchain:?};"
    )
    .expect("write to String");
    writeln!(
        src,
        "/// `(library-relative path, BLAKE3 hex)` of every `.olean` part, sorted by path."
    )
    .expect("write to String");
    writeln!(
        src,
        "pub(crate) const PINNED_TOOLCHAIN_MANIFEST: &[(&str, &str)] = &["
    )
    .expect("write to String");
    for (rel, digest) in &rows {
        writeln!(src, "    ({rel:?}, {digest:?}),").expect("write to String");
    }
    writeln!(src, "];").expect("write to String");
    std::fs::write(out_dir.join("pinned_toolchain_manifest.rs"), src)
        .expect("write pinned_toolchain_manifest.rs");
}

/// What pinned `lean` compares before it reads an `.olean` part
/// (`module.cpp`, `lean_compacted_region_read`): header version, flags and
/// githash. The header's `lean_version` string rides along, informative only.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Identity {
    version: u8,
    flags: u8,
    githash: String,
    lean_version: Option<String>,
}

impl Identity {
    /// What the import gate compares: everything but `lean_version`.
    fn key(&self) -> (u8, u8, &str) {
        (self.version, self.flags, &self.githash)
    }
}

/// The header identity of one `.olean` part. A v1 header (Lean <= v4.13) has
/// no flags byte and no version string; v2 (and v3, whose fixed header is the
/// same 88 bytes) keeps flags at byte 6, the version string at 7..40 and the
/// githash at 40..80 (`src/header.rs` documents both layouts).
fn mint_identity(bytes: &[u8]) -> Result<Identity, String> {
    if bytes.len() < 6 || &bytes[..5] != b"olean" {
        return Err("not an .olean header".to_string());
    }
    let version = bytes[5];
    let (needed, flags, githash, lean_version) = if version == 1 {
        (56, 0, 6..46, None)
    } else {
        let raw = bytes.get(7..40).unwrap_or_default();
        let end = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
        (
            88,
            bytes.get(6).copied().unwrap_or_default(),
            40..80,
            Some(String::from_utf8_lossy(&raw[..end]).into_owned()),
        )
    };
    if bytes.len() < needed {
        return Err(format!(
            "an olean v{version} header needs {needed} bytes, the file has {}",
            bytes.len()
        ));
    }
    let githash = &bytes[githash];
    if !githash.iter().all(u8::is_ascii_hexdigit) {
        return Err("its githash is not 40 hex digits".to_string());
    }
    Ok(Identity {
        version,
        flags,
        githash: String::from_utf8_lossy(githash).into_owned(),
        lean_version,
    })
}

fn describe(id: &Identity) -> String {
    match &id.lean_version {
        None => format!("olean v{}, githash {}", id.version, id.githash),
        Some(v) => format!(
            "olean v{}, flags 0x{:02x}, githash {} (lean_version \"{v}\")",
            id.version, id.flags, id.githash
        ),
    }
}

/// The `WorldState` variant a `lean_worlds.tsv` state names.
fn state_variant(state: &str) -> Option<&'static str> {
    Some(match state {
        "oracle" => "Oracle",
        "historical" => "Historical",
        "frontend-only" => "FrontendOnly",
        "measured" => "Measured",
        "canary" => "Canary",
        _ => return None,
    })
}

/// Write `$OUT_DIR/lean_worlds.rs`: one `LeanWorldRow` per row of
/// `lean_worlds.tsv` (docs/DECISIONS.md R38, R81), its identity measured NOW
/// from the row's tracked fixtures — a property of the commit, never of the
/// box. Returns the Oracle row's world and identity.
///
/// Panics only on inconsistent tracked data: a malformed row, a missing
/// fixture, two fixtures of one row disagreeing, two rows sharing a world or
/// an identity, not exactly one `oracle` row, or an Oracle that is not the
/// `lean-toolchain` pin. An INSTALLED toolchain that disagrees with its row
/// is only reported (`cargo:warning`): the import gate refuses its files by
/// name at run time, since their identity is in no row.
fn write_lean_worlds(
    manifest_dir: &std::path::Path,
    pinned: Option<&lean_toolchain::PinnedLean>,
) -> (String, Identity) {
    use std::fmt::Write as _;
    let workspace = manifest_dir
        .parent()
        .and_then(std::path::Path::parent)
        .expect("clean-olean is inside the Clean workspace");
    let table = manifest_dir.join("lean_worlds.tsv");
    println!("cargo:rerun-if-changed={}", table.display());
    let text = std::fs::read_to_string(&table)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", table.display()));
    let pin = std::fs::read_to_string(workspace.join("lean-toolchain"))
        .unwrap_or_else(|e| panic!("cannot read lean-toolchain: {e}"));
    let pin = pin.trim();

    let mut src = String::from(
        "/// One row per world of `crates/clean-olean/lean_worlds.tsv`, in its order; \
         every identity\n/// measured by `build.rs` from the row's tracked fixtures.\n\
         pub(crate) const LEAN_WORLD_ROWS: &[LeanWorldRow] = &[\n",
    );
    let mut seen: Vec<(String, Identity)> = Vec::new();
    let mut oracle: Option<(String, Identity)> = None;
    for (line_no, line) in text.lines().enumerate() {
        let line_no = line_no + 1;
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let columns: Vec<&str> = line.split('\t').collect();
        let [world, state, toolchain, fixtures] = columns[..] else {
            panic!("lean_worlds.tsv:{line_no}: expected 4 tab-separated columns: {line:?}");
        };
        let variant = state_variant(state)
            .unwrap_or_else(|| panic!("lean_worlds.tsv:{line_no}: unknown state `{state}`"));
        if seen.iter().any(|(w, _)| w == world) {
            panic!("lean_worlds.tsv:{line_no}: the world `{world}` has two rows");
        }
        let mut identity: Option<(String, Identity)> = None;
        for fixture in fixtures.split(' ').filter(|f| !f.is_empty()) {
            let path = workspace.join(fixture);
            println!("cargo:rerun-if-changed={}", path.display());
            let bytes = std::fs::read(&path).unwrap_or_else(|e| {
                panic!("lean_worlds.tsv:{line_no}: tracked fixture {fixture} is missing: {e}")
            });
            let id = mint_identity(&bytes)
                .unwrap_or_else(|e| panic!("lean_worlds.tsv:{line_no}: {fixture}: {e}"));
            match &identity {
                Some((first, known)) if known != &id => panic!(
                    "lean_worlds.tsv:{line_no}: the fixtures of `{world}` disagree: {first} is \
                     {} and {fixture} is {}",
                    describe(known),
                    describe(&id)
                ),
                Some(_) => {}
                None => identity = Some((fixture.to_string(), id)),
            }
        }
        let Some((_, identity)) = identity else {
            panic!("lean_worlds.tsv:{line_no}: the world `{world}` names no fixture");
        };
        if let Some((other, _)) = seen.iter().find(|(_, id)| id.key() == identity.key()) {
            panic!(
                "lean_worlds.tsv:{line_no}: `{world}` and `{other}` share the identity {}",
                describe(&identity)
            );
        }
        if variant == "Oracle" {
            if oracle.is_some() {
                panic!("lean_worlds.tsv:{line_no}: a second oracle row (`{world}`)");
            }
            if toolchain != pin || pin.rsplit(':').next() != Some(world) {
                panic!(
                    "lean_worlds.tsv:{line_no}: the oracle row (`{world}`, {toolchain}) is not \
                     the lean-toolchain pin `{pin}`"
                );
            }
            oracle = Some((world.to_string(), identity.clone()));
        }
        // An installed toolchain of this world must write what its fixtures
        // carry; one that does not is refused at import, by name.
        let installed = if variant == "Oracle" {
            pinned.map(|p| p.lib_path.clone())
        } else {
            lean_toolchain::installed_lean_lib(toolchain)
        };
        if let Some(lib) = installed {
            let prelude = lib.join("Init/Prelude.olean");
            match std::fs::read(&prelude)
                .map_err(|e| e.to_string())
                .and_then(|b| mint_identity(&b))
            {
                Ok(found) if found.key() == identity.key() => {}
                Ok(found) => println!(
                    "cargo:warning=the installed toolchain {toolchain} ({}) writes {}, but \
                     lean_worlds.tsv measures `{world}` as {} from its tracked fixtures; Clean \
                     refuses that toolchain's .olean files at import (UnsupportedLeanWorld)",
                    prelude.display(),
                    describe(&found),
                    describe(&identity)
                ),
                Err(e) => println!(
                    "cargo:warning=cannot read the identity of {} ({toolchain}): {e}",
                    prelude.display()
                ),
            }
        }
        let lean_version = identity
            .lean_version
            .as_ref()
            .map_or_else(|| "None".to_string(), |v| format!("Some({v:?})"));
        writeln!(
            src,
            "    LeanWorldRow {{\n        world: {world:?},\n        state: WorldState::{variant},\n        \
             identity: HeaderIdentity::from_parts({}, 0x{:02x}, *b{:?}),\n        \
             lean_version: {lean_version},\n    }},",
            identity.version, identity.flags, identity.githash
        )
        .expect("write to String");
        seen.push((world.to_string(), identity));
    }
    src.push_str("];\n");
    let Some(oracle) = oracle else {
        panic!("lean_worlds.tsv has no oracle row; exactly one is the lean-toolchain pin `{pin}`");
    };
    let out_dir =
        std::path::PathBuf::from(std::env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR"));
    std::fs::write(out_dir.join("lean_worlds.rs"), src).expect("write lean_worlds.rs");
    oracle
}
