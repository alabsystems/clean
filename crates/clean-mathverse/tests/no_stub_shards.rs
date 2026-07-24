// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Hard regression test: refuses to validate the corpus if ANY shard in
//! `data/mathverse-shards/` is a name-only stub.
//!
//! A "stub" is a shard whose `expr_count <= 2` despite carrying ≥ 1000
//! constants. That signature is unique to the historical pattern where
//! the 5 structured importers (dafny / acl2 / coq_v / lean3 /
//! isabelle_thy) emitted `FlatExpr::sort(0)` as a shared placeholder for
//! every constant's type. The fidelity-tier classification in
//! `mathverse_fidelity_check.rs` calls this `SurfaceNamesOnly`.
//!
//! The point of this test is structural: any future change that
//! resurrects a stub shard fails CI on this file alone.

use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};

const MAGIC_OMEG: u32 = 0x4F4D_4547;

#[test]
fn mathverse_shard_corpus_contains_no_name_only_stubs() {
    let dir = match locate_shard_dir() {
        Some(d) => d,
        None => {
            eprintln!(
                "skip: data/mathverse-shards not present in this working copy — \
                 nothing to audit"
            );
            return;
        }
    };

    let mut shards = Vec::new();
    collect_shards(&dir, &mut shards);
    if shards.is_empty() {
        // The directory can exist (carrying only JSON manifests/metadata) while
        // the `.mathverse` binary shards themselves are absent — they are downloaded
        // GitHub Release assets, not checked in (see docs/MATHVERSE_RELEASE_PROCESS.md).
        // With no shards to audit, skip exactly as we do when the dir is absent;
        // the stub-detection invariant only applies to a materialized corpus.
        eprintln!(
            "skip: {} contains no .mathverse shards in this working copy \
             (shards are Release assets, fetched via `clean mathverse download`) — \
             nothing to audit",
            dir.display()
        );
        return;
    }

    let mut offenders: Vec<(PathBuf, u32, u32)> = Vec::new();
    for p in &shards {
        let (constants, exprs) = match read_header_counts(p) {
            Some(t) => t,
            None => continue, // not an mathverse shard
        };
        // Stub signature: many constants, only one or two shared FlatExpr.
        if constants >= 1000 && exprs <= 2 {
            offenders.push((p.clone(), constants, exprs));
        }
    }

    assert!(
        offenders.is_empty(),
        "found {} name-only stub shard(s) in {}:\n{}",
        offenders.len(),
        dir.display(),
        offenders
            .iter()
            .map(|(p, c, e)| format!(
                "  ! {}: {c} constants but only {e} FlatExpr",
                p.file_name().unwrap_or_default().to_string_lossy()
            ))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

fn locate_shard_dir() -> Option<PathBuf> {
    // From CARGO_MANIFEST_DIR = clean/crates/clean-mathverse ; ../../ is repo root.
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let candidate = manifest_dir.join("../../data/mathverse-shards");
    candidate
        .exists()
        .then(|| candidate.canonicalize().unwrap_or(candidate))
}

fn collect_shards(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let p = entry.path();
            if p.is_dir() {
                collect_shards(&p, out);
            } else if p.extension().is_some_and(|e| e == "mathverse") {
                out.push(p);
            }
        }
    }
}

fn read_header_counts(path: &Path) -> Option<(u32, u32)> {
    let mut buf = [0u8; 256];
    let mut f = fs::File::open(path).ok()?;
    f.read_exact(&mut buf).ok()?;
    let magic = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
    if magic != MAGIC_OMEG {
        return None;
    }
    // Per shard.rs: after the 4-byte magic, u32 fields are
    //   version, flags, string_count, string_data_len, level_count,
    //   expr_count, constant_count, ...
    let expr_count = u32::from_le_bytes([buf[24], buf[25], buf[26], buf[27]]);
    let constant_count = u32::from_le_bytes([buf[28], buf[29], buf[30], buf[31]]);
    Some((constant_count, expr_count))
}
