// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The specification's world of the native-fold pin table
//! (`crates/clean-kernel/src/env/native_fold_canon.tsv`, rule in
//! `docs/issues/2026-09-26-kernel-native-fold-by-name.md`).
//!
//! A name-keyed kernel fold fires only when the environment's definition of
//! its head has a δ-closure digest the kernel holds as canonical. The
//! specification declares its OWN `Nat.add`, `Nat.pred` and `Nat.sub`
//! (`spec/foundation_nat.clean`: structural recursion on the second argument,
//! `Nat.rec` for the predecessor) and the kernel's builders (`init_nat` through
//! `init_rat`/`init_fin`) then add the rest of the arithmetic on top of them, so
//! every fold key's closure differs from the prelude's. Without these rows the
//! spec does not build: `init_boolean_analysis` checks `UInt32.ofNat`, whose
//! type needs `2 ^ 32` folded.
//!
//! The rows are minted from the full `Specification::new()` environment and
//! REVIEWED (`clean_kernel::env::native_fold_review`): a row whose own rules
//! agree with its definition three ways is pinned `fold`, a row a `fold` row
//! needs is pinned `definition`, the rest are unpinned. The battery fails when
//! a fresh reviewed mint and the pinned rows disagree, and
//! `CLEAN_NATIVE_FOLD_REPIN=1` rebuilds the spec under the kernel's mint
//! bypass (folds by name, as before authority), reviews it the same way,
//! rewrites this world's rows and then FAILS: the table is `include_str!`'d, so
//! the re-pinning binary cannot check the rows it wrote, and a re-pin run is
//! never a verdict. Rebuild and rerun without the variable.

use std::path::Path;

use clean_kernel::env::native_fold_review::review_world;
use clean_kernel::env::{canonical_fold_rows, native_fold_mint_bypass, Environment, FoldRole};
use clean_kernel::name::Name;
use clean_verify::spec::Specification;
use clean_verify::test_utils::{run_with_stack, shared_spec};

const WORLD: &str = "clean-verify-spec";

fn repinning() -> bool {
    std::env::var_os("CLEAN_NATIVE_FOLD_REPIN").is_some()
}

type Row = (String, String, String, String);

/// Every reviewed row this world pins (see the module docs); a re-pin reviews
/// under the mint bypass without the production leg.
fn mint(env: &Environment, repin: bool) -> Vec<Row> {
    let reviewed = if repin {
        native_fold_mint_bypass::run(|| review_world(env, WORLD, false))
    } else {
        review_world(env, WORLD, true)
    };
    let mut rows = Vec::new();
    for row in &reviewed {
        println!("{}", row.summary_line(WORLD));
        if !repin && row.role == Some(FoldRole::Fold) {
            if let Err(why) = clean_kernel::env::native_fold_review::fold_row_fires(env, &row.name)
            {
                panic!("{WORLD}: `fold` row {} does not fire: {why}", row.name);
            }
        }
        rows.extend(row.pinned_row(WORLD));
    }
    rows.sort();
    rows
}

/// Rewrite this world's rows of the kernel's table, keeping every other row.
fn repin(rows: &[Row]) {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-kernel/src/env/native_fold_canon.tsv");
    let text = std::fs::read_to_string(&path).expect("read native_fold_canon.tsv");
    let mut out: Vec<String> = text
        .lines()
        .filter(|line| {
            line.starts_with('#')
                || (!line.trim().is_empty() && line.split('\t').next() != Some(WORLD))
        })
        .map(str::to_string)
        .collect();
    out.extend(
        rows.iter()
            .map(|(w, n, h, r)| format!("{w}\t{n}\t{h}\t{r}")),
    );
    std::fs::write(&path, out.join("\n") + "\n").expect("write native_fold_canon.tsv");
}

#[test]
fn test_spec_fold_digests_are_pinned() {
    if repinning() {
        let spec = native_fold_mint_bypass::run(|| {
            run_with_stack(|| Specification::new().expect("the spec builds under the mint bypass"))
        });
        let rows = mint(spec.env(), true);
        repin(&rows);
        panic!(
            "{WORLD}: re-pinned {} rows of native_fold_canon.tsv under CLEAN_NATIVE_FOLD_REPIN; \
             review each changed closure, then rebuild and rerun without the variable -- a \
             re-pin run is never a verdict (the table is include_str!'d, so this binary still \
             holds the old rows)",
            rows.len()
        );
    }
    let env = shared_spec().env();
    let minted = mint(env, false);
    let mut pinned: Vec<Row> = canonical_fold_rows()
        .into_iter()
        .filter(|(w, _, _, _)| w == WORLD)
        .collect();
    pinned.sort();
    let missing: Vec<_> = minted.iter().filter(|r| !pinned.contains(r)).collect();
    let stale: Vec<_> = pinned.iter().filter(|r| !minted.contains(r)).collect();
    assert!(
        missing.is_empty() && stale.is_empty(),
        "{WORLD}: native_fold_canon.tsv drifted from the specification.\n\
         minted but not pinned ({}): {missing:#?}\npinned but not minted ({}): {stale:#?}\n\
         Re-pin with CLEAN_NATIVE_FOLD_REPIN=1 only after confirming each changed\n\
         closure still computes what its fold computes.",
        missing.len(),
        stale.len()
    );
    // Completeness: the spec's own arithmetic and what is built over it fold.
    for head in ["Nat.add", "Nat.sub", "Nat.pred", "Nat.mul", "Nat.pow"] {
        assert!(
            env.native_fold_authorized(&Name::from_string(head)),
            "{head} must fold in the specification: {:?}",
            env.native_fold_verdict(&Name::from_string(head))
        );
    }
}
