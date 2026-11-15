// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! **What the newest revalidation record's source rev re-derives, and what it
//! cannot.**
//!
//! The v3 record's measurement driver is hashed at the rev it names
//! (`enum_tag_stage2`). The record the scope binds NOW was trusted on its own
//! JSON: its `clean_source_rev` was compared with the scope file's copy of the
//! same string, and its driver hash with the driver committed today — but the
//! rev itself was never looked up, and it is not an object in this repository.
//!
//! So each record rev is either RESOLVED — its kernel digest and driver hash
//! re-derived at that commit — or named in [`UNRESOLVABLE`] while the rev and
//! its tree stay stated as NOT re-derivable, and the record's two content
//! claims are re-derived at pushed commits: the kernel-source digest (by
//! `scripts/crystal_freshness_scope.py`'s own definition) at the scope file's
//! `kernel_tree_read_at`, the one statement of that witness, which the
//! script's `--emit` reads the tree at; the driver hash at the row's driver
//! witness. A new unresolvable rev with no row fails here rather than being
//! taken on its word, and a row whose rev starts resolving fails too, so the
//! table cannot outlive its reason.

use super::enum_tag_stage2::{git_show, sha256_hex};
use super::{read_json, repo_root};

/// A record rev that is not an object here, and the pushed commit that
/// re-derives its driver hash (its kernel witness is the scope file's).
struct UnresolvableRev {
    rev: &'static str,
    /// The record's `clean_source_tree`: not an object here either.
    tree: &'static str,
    /// A pushed commit whose measurement driver hashes to the record's
    /// `measurement_driver_sha256`.
    driver_witness: &'static str,
}

/// Measured 2026-09-24. `c46d6594b` is not in this repository's object store,
/// `git fetch origin c46d6594b…` is refused (`not our ref`), and no other clone
/// on the measuring box (including trust's `first-party/clean` module) has it.
/// Where it went, from the pushed history: the record's lane — `dc2086ccb`
/// through `b93219f90`, the commit that added the record — was REBASED onto
/// `2f59b8a17` at 22:40:17 -0700 on 2026-09-20 (all seven share that committer
/// time). The driver change `7e173b8a8` was AUTHORED at 18:43:09, the record
/// was measured at 18:48:17 (`measured_utc` 01:48:17Z), and `b93219f90` was
/// authored at 18:50:39: the measured rev is the pre-rebase driver commit,
/// which was never pushed. Its kernel source is re-derivable — `b6248bf47`
/// (also `faf434b73`, `18409a6b8`) digests to the recorded value — and its
/// driver is `7e173b8a8`'s. Its TREE is not: the lane's diff re-applied onto
/// each kernel-identical candidate base gives a different tree, so what else
/// that checkout held is unknown.
const UNRESOLVABLE: &[UnresolvableRev] = &[UnresolvableRev {
    rev: "c46d6594b248bc2fd52c007fea57b587eeab1a21",
    tree: "3a920a8aec71ed32c2414b032f744f9a2d887673",
    driver_witness: "7e173b8a835982fecb3f1f842dc2a99d8d87a515",
}];

/// Is `oid` an object of this repository (of any type)?
fn is_object(oid: &str) -> bool {
    std::process::Command::new("git")
        .arg("-C")
        .arg(repo_root())
        .args(["cat-file", "-e", oid])
        .status()
        .unwrap_or_else(|e| panic!("could not run git to look up {oid} ({e})"))
        .success()
}

/// The kernel-source digest at a COMMITTED rev, by the scope script's own
/// definition: its `tree_at` and `kernel_digest`, imported, never a second
/// implementation of the walk. Fails closed on a rev git cannot archive.
fn kernel_digest_at(rev: &str) -> String {
    const DIGEST_AT: &str = "import shutil, sys\n\
        sys.path.insert(0, sys.argv[1])\n\
        import crystal_freshness_scope as s\n\
        root = s.tree_at(sys.argv[2])\n\
        try:\n    print(s.kernel_digest(root)[0])\n\
        finally:\n    shutil.rmtree(root.parent, ignore_errors=True)\n";
    let out = std::process::Command::new("python3")
        .args(["-c", DIGEST_AT])
        .arg(repo_root().join("scripts"))
        .arg(rev)
        .output()
        .unwrap_or_else(|e| panic!("could not run python3 to digest the kernel ({e})"));
    assert!(
        out.status.success(),
        "crystal_freshness_scope.py cannot digest the kernel at {rev}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

#[test]
fn the_newest_record_rev_is_rederived_or_named_unresolvable() {
    let scope = read_json("data/crystal_freshness_scope.json");
    let newest = scope["record"]
        .as_str()
        .expect("the scope names the newest revalidation record");
    let record = read_json(newest);
    let prov = &record["provenance"];
    let field = |key: &str| {
        prov[key]
            .as_str()
            .unwrap_or_else(|| panic!("{newest} provenance carries no `{key}`"))
    };
    let (rev, kernel, driver, driver_sha) = (
        field("clean_source_rev"),
        field("clean_kernel_src_sha256"),
        field("measurement_driver"),
        field("measurement_driver_sha256"),
    );
    let row = UNRESOLVABLE.iter().find(|u| u.rev == rev);
    let kernel_witness = scope["kernel_tree_read_at"].as_str();
    if is_object(rev) {
        assert_eq!(
            kernel_witness, None,
            "{rev} is a commit here, so the scope file must be read at it, not at a witness"
        );
        assert!(
            row.is_none(),
            "{rev} resolves in this repository now; delete its UNRESOLVABLE row — the record \
             is re-derived at the rev itself"
        );
        assert_eq!(
            kernel_digest_at(rev),
            kernel,
            "{newest}: kernel digest at {rev}"
        );
        assert_eq!(
            sha256_hex(&git_show(rev, driver)),
            driver_sha,
            "{newest}: {driver} at {rev}"
        );
        return;
    }
    let u = row.unwrap_or_else(|| {
        panic!(
            "{newest} names clean_source_rev {rev}, which is not an object in this repository, \
             and UNRESOLVABLE does not name it. Nothing about that rev can be re-derived here, so \
             the record is not taken on its word: find where the rev went, and name the pushed \
             commits that re-derive its kernel digest and driver hash."
        )
    });
    assert_eq!(
        Some(u.tree),
        prov["clean_source_tree"].as_str(),
        "{newest}: the UNRESOLVABLE row states a different tree than the record"
    );
    assert!(
        !is_object(u.tree),
        "{newest}'s clean_source_tree {} resolves now; re-derive the record from it",
        u.tree
    );
    let kernel_witness = kernel_witness.unwrap_or_else(|| {
        panic!(
            "data/crystal_freshness_scope.json covers {rev}, which is not a commit here, and names \
             no kernel_tree_read_at: its kernel tree was read nowhere anyone can check"
        )
    });
    for witness in [kernel_witness, u.driver_witness] {
        assert!(
            is_object(&format!("{witness}^{{commit}}")),
            "witness {witness} is not a commit in this repository; a witness nobody can check \
             re-derives nothing"
        );
    }
    assert_eq!(
        kernel_digest_at(kernel_witness),
        kernel,
        "{newest}: clean_kernel_src_sha256 is not the kernel digest at the pushed witness \
         {kernel_witness}"
    );
    assert_eq!(
        sha256_hex(&git_show(u.driver_witness, driver)),
        driver_sha,
        "{newest}: measurement_driver_sha256 is not {driver} at the pushed witness {}",
        u.driver_witness
    );
}
