// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Byte-parity tests for `clean mathverse isabelle-sessions`.
//!
//! The golden trees under `tests/fixtures/isabelle_sessions/golden/` were
//! originally produced by the retired `scripts/isabelle/afp_session_gen.py`
//! (deleted when this port landed) over the checked-in fixture inputs, and are
//! now maintained as the Rust generator's own pinned output — the fragment
//! headers credit `clean mathverse isabelle-sessions` rather than the old
//! script. Regenerate the goldens through the generator (never hand-edit the
//! fixture files) after an intentional output change:
//!
//! ```text
//! REGEN_ISABELLE_SESSIONS_GOLDEN=1 \
//!   cargo test -p clean-mathverse --test isabelle_sessions_parity
//! ```
//!
//! When that env var is set, each test WRITES its generated tree into the
//! golden dir instead of asserting; a normal run (env unset) asserts every
//! mode reproduces its golden tree BYTE-FOR-BYTE: same file set, same bytes.
//! The fixtures exercise multi-chunk checkpointing, same-pass Kahn placement,
//! the import-cycle fallback, all three afp-mode skip warnings,
//! quoted/multi-line/`in "dir"` session headers, dotted and quoted imports,
//! the `@`-chained spine parents, non-recursive spine listing (`Analysis/ex`
//! exclusion), provider-chain topo order, spine-heap bases, unresolved bases,
//! and the `UNRESOLVED:None` missing-entry quirk.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use clean_mathverse::hol::isabelle_sessions::afp::{plan_afp_wave, write_afp_wave};
use clean_mathverse::hol::isabelle_sessions::read_entries_file;
use clean_mathverse::hol::isabelle_sessions::spine::{plan_spine, write_spine};
use clean_mathverse::hol::isabelle_sessions::wavec::{plan_wavec, write_wavec};

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/isabelle_sessions")
}

/// Map of file name → bytes for every regular file directly in `dir`.
fn dir_bytes(dir: &Path) -> BTreeMap<String, Vec<u8>> {
    let mut out = BTreeMap::new();
    for entry in fs::read_dir(dir).expect("fixture/output dir must list") {
        let entry = entry.expect("dir entry must read");
        let path = entry.path();
        assert!(
            path.is_file(),
            "unexpected non-file in generated output: {}",
            path.display()
        );
        let name = entry
            .file_name()
            .into_string()
            .expect("output file names are UTF-8");
        out.insert(name, fs::read(&path).expect("output file must read"));
    }
    out
}

/// Env var that flips every parity test from ASSERT to REGENERATE: the
/// generated tree is written back into the golden dir. This is the documented,
/// generator-driven way to update the fixtures after an intentional output
/// change — the fixtures must never be hand-edited.
const REGEN_ENV: &str = "REGEN_ISABELLE_SESSIONS_GOLDEN";

/// Assert parity, or regenerate the golden tree when [`REGEN_ENV`] is set.
fn assert_or_regen(golden: &Path, outdir: &Path) {
    if std::env::var_os(REGEN_ENV).is_some() {
        regenerate_golden(golden, outdir);
    } else {
        assert_dir_bytes_equal(golden, outdir);
    }
}

/// Overwrite `golden` with the exact bytes generated into `outdir` (creating the
/// dir, removing any stale files no longer produced). Only reached under
/// [`REGEN_ENV`].
fn regenerate_golden(golden: &Path, outdir: &Path) {
    fs::create_dir_all(golden).expect("golden dir must be creatable");
    let generated = dir_bytes(outdir);
    for stale in dir_bytes(golden).keys() {
        if !generated.contains_key(stale) {
            fs::remove_file(golden.join(stale)).expect("remove stale golden file");
        }
    }
    for (name, bytes) in &generated {
        fs::write(golden.join(name), bytes).expect("write regenerated golden file");
    }
}

/// Assert `outdir` reproduces `golden` byte-for-byte (same names, same bytes).
fn assert_dir_bytes_equal(golden: &Path, outdir: &Path) {
    let golden_files = dir_bytes(golden);
    let out_files = dir_bytes(outdir);
    assert_eq!(
        golden_files.keys().collect::<Vec<_>>(),
        out_files.keys().collect::<Vec<_>>(),
        "generated file set must match the pinned golden set"
    );
    for (name, golden_bytes) in &golden_files {
        let got = &out_files[name];
        assert!(
            got == golden_bytes,
            "byte mismatch vs golden in `{name}` (regenerate with {REGEN_ENV}=1):\
             \n--- golden ---\n{}\n--- generated ---\n{}",
            String::from_utf8_lossy(golden_bytes),
            String::from_utf8_lossy(got),
        );
    }
}

#[test]
fn test_afp_mode_matches_python_golden_bytes() {
    let fix = fixture_root();
    let entries =
        read_entries_file(&fix.join("input/wave_a.txt")).expect("wave_a entries must parse");
    assert_eq!(
        entries,
        [
            "Entry_Simple",
            "EntryBig",
            "EntryMulti",
            "EntryNoRoot",
            "EntryEmpty",
            "EntryNoSess",
            "EntryCycle"
        ],
        "comment/blank stripping must match the Python entries parser"
    );
    let plan = plan_afp_wave(&entries, &fix.join("input/afp_thys"), "ZP-Lib3e", 3)
        .expect("afp plan must succeed on the fixture tree");
    assert_eq!(
        plan.warnings,
        [
            "WARN: no ROOT for EntryNoRoot (skipped)",
            "WARN: no theories parsed for EntryEmpty (skipped)",
            "WARN: no session parsed in EntryNoSess/ROOT (skipped)",
        ],
        "skip diagnostics must match the Python stderr lines"
    );
    let out = tempfile::tempdir().expect("tempdir");
    write_afp_wave(&plan, out.path()).expect("afp write must succeed");
    assert_or_regen(&fix.join("golden/afp"), out.path());
}

#[test]
fn test_spine_mode_matches_python_golden_bytes() {
    let fix = fixture_root();
    let plan =
        plan_spine(&fix.join("input/hol_src"), 3).expect("spine plan must succeed on the fixture");
    assert!(plan.warnings.is_empty(), "no spine should be skipped");
    assert_eq!(
        plan.spine_last
            .last()
            .map(|(s, l)| (s.as_str(), l.as_str())),
        Some(("HOL-Probability", "ZP-Probability")),
        "spine completion order must end with HOL-Probability"
    );
    let out = tempfile::tempdir().expect("tempdir");
    write_spine(&plan, out.path()).expect("spine write must succeed");
    assert_or_regen(&fix.join("golden/spine"), out.path());
}

#[test]
fn test_wavec_mode_matches_python_golden_bytes() {
    let fix = fixture_root();
    let seeds =
        read_entries_file(&fix.join("input/wave_c_seed.txt")).expect("wave_c seeds must parse");
    let plan = plan_wavec(&fix.join("input/afp_thys"), &seeds)
        .expect("wavec plan must succeed on the fixture tree");
    assert_eq!(plan.seed_count, 5, "five seed entries requested");
    assert_eq!(
        plan.rows.len(),
        7,
        "closure pulls in the two provider entries"
    );
    assert_eq!(plan.unresolved().len(), 2, "Ghost_Entry + Unres_User");
    let out = tempfile::tempdir().expect("tempdir");
    write_wavec(&plan, out.path()).expect("wavec write must succeed");
    assert_or_regen(&fix.join("golden/wavec"), out.path());
}
