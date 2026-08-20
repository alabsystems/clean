// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **A revalidation is a measurement of ONE clean-kernel tree. This binds it to
//! that tree, and re-runs the binding here.**
//!
//! [`super::freshness`] made the live-dump comparison non-optional in one
//! sense: the fixtures must point at a dated record, the record must say no
//! body's instructions moved, and the script must cover exactly the chained
//! bodies. But every one of those checks reads the SAME committed files, so all
//! of them pass forever, at any HEAD, no matter how far the kernel source has
//! moved from the tree the record was measured at. Nothing said which tree that
//! was.
//!
//! It had already gone stale. Both committed records were measured against
//! clean-kernel source tree `214f8ffd0d` (clean revs `f99b94e21` /
//! `f0846ade2`). At `891b7d153` the kernel source tree is `a3ae6c21fc`: three
//! files moved in `crates/clean-kernel/src/env/`, adding a field to
//! `Environment`, three registry methods and a `Reducibility` match arm. Every
//! link-2a gate stayed green throughout, because every link-2a gate reads a
//! fixture.
//!
//! ## Why this fails on CONTENT and not on NUMBERING
//!
//! The obvious gate — "fail whenever the kernel source moves" — is the one that
//! gets switched off. Whole-crate `functy.N` / `enum.N` / `struct.N` /
//! `@func.N` indices renumber when the crate gains ANY item, with zero
//! instructions changed; that is measured, not assumed (a producer-only A/B on
//! a byte-identical clean tree moved `functy.N` on all ten chains and `@func.N`
//! on `is_zero`, with every lineage stable). A gate that reddens on that fires
//! constantly, gets disabled, and takes the case that matters down with it.
//!
//! So the verdict is decided by SCOPE, which is the same renumbering/content
//! split `scripts/crystal_fixture_freshness.py` makes between its AMBER token
//! classes and `STRUCTURAL`, lifted one level up — from "which tokens moved in
//! the emitted text" to "which source could have moved them":
//!
//! * a chained body's own defining source file moved → **CONTENT-SCOPE, RED**.
//!   The body the spec module transcribes may not be the body the producer
//!   emits, and no fixture in this tree can tell you.
//! * the kernel moved elsewhere → **NUMBERING-SCOPE, AMBER**. Printed and
//!   ledgered as a revalidation debt, not failed.
//!
//! AMBER is not a claim that no body drifted. It is the refusal to make either
//! claim without a dump, stated where a reader will see it.
//!
//! ## Why this shells out
//!
//! The digest work lives in `scripts/crystal_freshness_scope.py` — one
//! implementation, so the pre-push gate and this test cannot disagree about
//! what "the kernel source" is. It hashes 1,890 files in ~0.24 s, which is why
//! it can sit in both. A second Rust reimplementation of the same digest would
//! be a second thing to keep in sync, and the first divergence between them
//! would be silent.
//!
//! The tests that need no compiler-free digest — that the scope file is
//! internally coherent and names a record that exists — are pure Rust below,
//! so a missing `python3` cannot empty the whole module.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

/// The derivable statement about which kernel tree the newest record covers.
const SCOPE: &str = "data/crystal_freshness_scope.json";
/// The mechanism that decides the verdict.
const SCRIPT: &str = "scripts/crystal_freshness_scope.py";

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("invariant: CARGO_MANIFEST_DIR is crates/clean-verify inside the repo")
        .to_path_buf()
}

fn scope_json() -> Value {
    let p = repo_root().join(SCOPE);
    let text = std::fs::read_to_string(&p).unwrap_or_else(|e| {
        panic!(
            "{} is missing or unreadable ({e}). It is what binds the crystal revalidation \
             records to the clean-kernel source they were measured at; without it every \
             link-2a gate is a comparison against a file of unknown vintage. Re-derive: \
             {SCRIPT} --emit",
            p.display()
        )
    });
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("{} is not valid JSON ({e})", p.display()))
}

/// **The verdict, decided by the one implementation that decides it.**
///
/// Exit 1 is CONTENT-SCOPE (or a mapping that no longer resolves under
/// `--strict`); exit 2 is an unusable scope file or a stale def_path → source
/// mapping. Both fail here. Exit 0 covers FRESH and the ledgered AMBER, and the
/// script's own output — reproduced in the failure message — says which.
#[test]
fn the_revalidation_scope_still_covers_this_kernel_tree() {
    let root = repo_root();
    let out = Command::new("python3")
        .arg(root.join(SCRIPT))
        .current_dir(&root)
        .output()
        .unwrap_or_else(|e| {
            panic!(
                "could not run `python3 {SCRIPT}` ({e}). This gate decides whether the \
                 committed revalidation still describes the kernel source in front of it; \
                 an unrunnable gate is not a passing one, so it fails closed."
            )
        });
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "{SCRIPT} exited {:?}.\n--- stdout ---\n{stdout}\n--- stderr ---\n{stderr}",
        out.status.code()
    );
    // A zero exit must still have produced a verdict; an empty run would pass
    // vacuously and that is the failure mode this whole module exists for.
    assert!(
        stdout.contains("verdict                FRESH")
            || stdout.contains("verdict                NUMBERING-SCOPE"),
        "{SCRIPT} exited 0 without printing a FRESH or NUMBERING-SCOPE verdict — it did not \
         actually decide anything.\n--- stdout ---\n{stdout}"
    );
}

/// The scope file names a record that is in the tree, and covers a real rev.
///
/// Checked without the script, so a machine with no `python3` still catches the
/// hand-edit shape: pointing the scope at a record that was never committed, or
/// dropping the rev that makes the pin meaningful.
#[test]
fn the_scope_file_names_a_committed_record_and_a_pinned_rev() {
    let scope = scope_json();
    let record = scope["record"]
        .as_str()
        .expect("the scope file must name the revalidation record it binds");
    assert!(
        record.starts_with("data/crystal_chain_revalidation_"),
        "the scope must bind a crystal revalidation record, not `{record}`"
    );
    assert!(
        repo_root().join(record).is_file(),
        "{SCOPE} names {record}, which is not in the tree. A scope bound to a record nobody \
         can read is a pin to nothing."
    );
    let rev = scope["covered_clean_rev"]
        .as_str()
        .expect("the scope file must pin the clean rev it was emitted at");
    assert!(
        rev.len() == 40 && rev.chars().all(|c| c.is_ascii_hexdigit()),
        "covered_clean_rev must be a full 40-character sha, not `{rev}`"
    );
    let digest = scope["clean_kernel_src_sha256"]
        .as_str()
        .expect("the scope file must pin the kernel source digest");
    assert!(
        digest.len() == 64 && digest.chars().all(|c| c.is_ascii_hexdigit()),
        "clean_kernel_src_sha256 must be a sha256 hex digest, not `{digest}`"
    );
    assert!(
        scope["digest_definition"]
            .as_str()
            .is_some_and(|s| s.contains("sorted path order")),
        "the scope file must carry the digest's DEFINITION — a digest whose recipe is not \
         written down cannot be re-derived by anyone who doubts it"
    );
    assert!(
        scope["clean_kernel_src_file_count"].as_u64().unwrap_or(0) > 1000,
        "the digest must cover the whole kernel source set; a count this small means the walk \
         found almost nothing and the digest is vacuous"
    );
}

/// **The scope covers exactly the bodies this gate chains.**
///
/// Same failure mode [`super::freshness`] closes for the fixture script, one
/// level up: a chain the scope does not pin has no content-drift check at all,
/// and the AMBER verdict would then be silently covering it.
#[test]
fn the_scope_pins_every_chained_body_and_its_source() {
    let scope = scope_json();
    let sources = scope["chained_body_sources"]
        .as_object()
        .expect("the scope file must carry a `chained_body_sources` object");

    let pinned: BTreeSet<&str> = sources.keys().map(String::as_str).collect();
    let chained: BTreeSet<&str> = super::freshness::EVIDENCE
        .iter()
        .map(|(stem, _)| *stem)
        .collect();
    assert_eq!(
        pinned, chained,
        "{SCOPE} and the chained bodies disagree. A body pinned by no source digest is a body \
         whose own file can move with this gate staying green — which is exactly the state all \
         eleven were in before {SCOPE} existed."
    );

    let root = repo_root();
    for (stem, entry) in sources {
        let file = entry["file"]
            .as_str()
            .unwrap_or_else(|| panic!("{stem}: the scope entry must name a source file"));
        assert!(
            file.starts_with("crates/clean-kernel/"),
            "{stem}: a chained body's source must live in the kernel, not `{file}`"
        );
        let path = root.join(file);
        assert!(
            path.is_file(),
            "{stem}: {file} is not in the tree. The mapping is stale, so the content-drift \
             check silently covers nothing — re-derive with {SCRIPT} --emit."
        );
        let pattern = entry["must_contain"].as_str().unwrap_or_else(|| {
            panic!("{stem}: the scope entry must carry the pattern that verifies the mapping")
        });
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("{stem}: {file} is unreadable ({e})"));
        assert!(
            text.contains(pattern),
            "{stem}: {file} no longer contains `{pattern}`. The def_path -> source mapping is \
             stale; a stale mapping does not fail a body, it stops checking one."
        );
        assert!(
            entry["sha256"]
                .as_str()
                .is_some_and(|s| s.len() == 64 && s.chars().all(|c| c.is_ascii_hexdigit())),
            "{stem}: the scope entry must pin a sha256 of the source file"
        );
    }
}
