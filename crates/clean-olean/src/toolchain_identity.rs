// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Is an `.olean` the pinned Lean toolchain's own build of a module?
//!
//! The checker's declared base is the Lean toolchain this checkout pins
//! (`lean-toolchain`). A consumer that treats toolchain modules differently
//! from library artifacts (`clean check` / `clean export-cert` neither bind
//! them to a source nor list them as taken AS BUILT) must identify them by
//! WHAT THEY ARE, not by where they sit: module-trust round 28 measured that
//! an EMPTY `<lib>/Init/Prelude.olean` made a whole library root count as "a
//! toolchain root", so a rewritten `V0.olean` beside a source saying
//! otherwise was neither bound nor disclosed, and `V0.v = 1` passed with a
//! bundle `clean kernel cert verify` reported ALL PASSED.
//!
//! The identity is the BLAKE3 digest of every `.olean` part of the pinned
//! toolchain's library, measured by `build.rs` when this binary was built
//! (`PINNED_TOOLCHAIN_MANIFEST`). A module is a toolchain module only when
//! every part the importer reads for it (`.olean`, `.olean.server`,
//! `.olean.private`) is byte-identical to the manifest's, wherever it lives.
//! Anything else — another toolchain, a copied-then-edited module, a file
//! placed into the real toolchain directory after the build — is an ordinary
//! artifact.

use std::path::{Path, PathBuf};

include!(concat!(env!("OUT_DIR"), "/pinned_toolchain_manifest.rs"));

/// The parts the importer reads for one module, by suffix.
const PART_SUFFIXES: [&str; 3] = [".olean", ".olean.server", ".olean.private"];

/// The pinned toolchain's name (`leanprover/lean4:vX`), or `None` when this
/// binary was built without it (then no module is a toolchain module).
#[must_use]
fn pinned_toolchain_name() -> Option<&'static str> {
    (!PINNED_TOOLCHAIN.is_empty() && !PINNED_TOOLCHAIN_MANIFEST.is_empty())
        .then_some(PINNED_TOOLCHAIN)
}

fn manifest_digest(rel: &str) -> Option<&'static str> {
    PINNED_TOOLCHAIN_MANIFEST
        .binary_search_by(|(path, _)| (*path).cmp(rel))
        .ok()
        .map(|i| PINNED_TOOLCHAIN_MANIFEST[i].1)
}

fn with_suffix(olean: &Path, suffix: &str) -> PathBuf {
    let mut raw = olean.as_os_str().to_os_string();
    raw.push(&suffix[".olean".len()..]);
    PathBuf::from(raw)
}

/// Why `olean` (the file `module` resolved to) is not the pinned toolchain's
/// build of `module`; `Ok(toolchain)` when every part matches the manifest.
///
/// # Errors
///
/// A human-readable reason: the module is not in the manifest, a part is
/// missing, present where the toolchain has none, unreadable, or differs.
pub fn pinned_toolchain_module(module: &str, olean: &Path) -> Result<&'static str, String> {
    let Some(toolchain) = pinned_toolchain_name() else {
        return Err("this binary was built without the pinned Lean toolchain".to_string());
    };
    if module.is_empty() || module.split('.').any(str::is_empty) {
        return Err(format!("`{module}` is not a module name"));
    }
    let rel_base = module.split('.').collect::<Vec<_>>().join("/");
    for suffix in PART_SUFFIXES {
        let rel = format!("{rel_base}{suffix}");
        let path = with_suffix(olean, suffix);
        match (manifest_digest(&rel), path.is_file()) {
            (None, _) if suffix == ".olean" => {
                return Err(format!("{toolchain} has no module `{module}`"));
            }
            (None, false) => {}
            (None, true) => {
                return Err(format!(
                    "{} exists, but {toolchain} has no {rel}",
                    path.display()
                ));
            }
            (Some(_), false) => {
                return Err(format!(
                    "{toolchain}'s {rel} has no counterpart at {}",
                    path.display()
                ));
            }
            (Some(expected), true) => {
                let bytes = std::fs::read(&path)
                    .map_err(|e| format!("{} is unreadable: {e}", path.display()))?;
                let actual = blake3::hash(&bytes).to_hex();
                if actual.as_str() != expected {
                    return Err(format!(
                        "{} differs from {toolchain}'s {rel} (blake3 {}…, pinned {}…)",
                        path.display(),
                        &actual.as_str()[..16],
                        &expected[..16]
                    ));
                }
            }
        }
    }
    Ok(toolchain)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_manifest_is_sorted_and_unique() {
        assert!(
            PINNED_TOOLCHAIN_MANIFEST
                .windows(2)
                .all(|w| w[0].0 < w[1].0),
            "binary search needs a strictly sorted manifest"
        );
    }

    #[test]
    fn an_empty_prelude_is_not_the_toolchain() {
        let dir = tempfile::tempdir().expect("tempdir");
        let olean = dir.path().join("Init/Prelude.olean");
        std::fs::create_dir_all(olean.parent().expect("parent")).expect("mkdir");
        std::fs::write(&olean, b"").expect("write");
        assert!(pinned_toolchain_module("Init.Prelude", &olean).is_err());
    }

    #[test]
    fn a_module_the_toolchain_does_not_have_is_not_the_toolchain() {
        let dir = tempfile::tempdir().expect("tempdir");
        let olean = dir.path().join("V0.olean");
        std::fs::write(&olean, b"olean").expect("write");
        let err = pinned_toolchain_module("V0", &olean).expect_err("not a toolchain module");
        assert!(
            err.contains("has no module") || err.contains("built without"),
            "{err}"
        );
    }

    #[test]
    fn the_pinned_toolchain_itself_is_the_toolchain_and_one_flipped_byte_is_not() {
        let Some(lib) = crate::pinned_lean_lib_path() else {
            eprintln!("pinned Lean toolchain unavailable; skipping");
            // SELF-SKIP OK: needs the pinned Lean toolchain (lean-toolchain)
            // installed under elan; without it there is no real
            // Init/Prelude.olean to identify, and the skip prints why
            // (CLEAN_OLEAN_REQUIRE_PINNED_LEAN makes absence a build error).
            return;
        };
        if pinned_toolchain_name().is_none() {
            panic!(
                "the pinned Lean toolchain is installed at {} but this binary's \
                 PINNED_TOOLCHAIN_MANIFEST is empty: build.rs failed to measure it \
                 (or the toolchain was installed after the build -- rebuild clean-olean)",
                lib.display()
            );
        }
        let real = lib.join("Init/Prelude.olean");
        assert!(pinned_toolchain_module("Init.Prelude", &real).is_ok());

        // A byte-identical copy elsewhere is still the toolchain's module …
        let dir = tempfile::tempdir().expect("tempdir");
        let copy = dir.path().join("Init/Prelude.olean");
        std::fs::create_dir_all(copy.parent().expect("parent")).expect("mkdir");
        for suffix in PART_SUFFIXES {
            let from = with_suffix(&real, suffix);
            if from.is_file() {
                // Installed toolchains may be read-only. Preserve their bytes
                // without inheriting permissions in this owned mutation fixture.
                let bytes = std::fs::read(&from).expect("read toolchain part");
                std::fs::write(with_suffix(&copy, suffix), bytes).expect("write fixture part");
            }
        }
        assert!(pinned_toolchain_module("Init.Prelude", &copy).is_ok());

        // … one flipped byte in any part is not.
        let mut bytes = std::fs::read(&copy).expect("read copy");
        let last = bytes.len() - 1;
        bytes[last] ^= 1;
        std::fs::write(&copy, &bytes).expect("rewrite copy");
        assert!(pinned_toolchain_module("Init.Prelude", &copy).is_err());

        // … and neither is a module name the file does not belong to.
        assert!(pinned_toolchain_module("Init.Core", &real).is_err());
    }
}
