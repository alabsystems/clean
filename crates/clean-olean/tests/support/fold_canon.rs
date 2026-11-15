// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The minting, drift and re-pin logic shared by the Lean-world pin batteries
//! of native-fold authority (`clean_kernel::env::native_fold_authority`, table
//! `crates/clean-kernel/src/env/native_fold_canon.tsv`):
//! `tests/native_fold_canon_lean.rs` (the pinned toolchain, and the mixed
//! import-prelude world) and `tests/native_fold_canon_lean_v4_8_0.rs`, each of
//! which includes this file with `#[path]`.
//!
//! A world's rows are `(world, name, hex digest, role)`. A battery decodes the
//! world's `Init`, mints its rows — [`mint_reviewed`] assigns every role by the
//! kernel's review (`clean_kernel::env::native_fold_review`), [`mint`] lists
//! every pinnable row for a battery that reviews its own list — and hands the
//! rows it pins to [`check_world`], which fails when they differ from the
//! pinned rows and rewrites that world's rows (only) under
//! `CLEAN_NATIVE_FOLD_REPIN=1`.

use std::path::Path;

use clean_kernel::env::{canonical_fold_rows, Environment};

/// The environment variable that turns a drift failure into a re-pin.
const REPIN_ENV: &str = "CLEAN_NATIVE_FOLD_REPIN";

/// One pinned row: `(world, name, lower-case hex digest, role)`.
pub type FoldRow = (String, String, String, String);

/// Whether this run re-pins (see the module docs).
pub fn repin_requested() -> bool {
    std::env::var_os(REPIN_ENV).is_some()
}

/// Every row `env` mints for `world` (`Environment::native_fold_pin_rows`),
/// as `(world, name, hex)`, sorted — before any review assigns a role.
#[allow(dead_code)] // the v4.8.0 battery reviews its own list; the v4.30 one does not call this
pub fn mint(world: &str, env: &Environment) -> Vec<(String, String, String)> {
    let mut rows: Vec<(String, String, String)> = env
        .native_fold_pin_rows()
        .into_iter()
        .map(|(name, digest)| (world.to_string(), name.to_string(), digest.to_hex()))
        .collect();
    rows.sort();
    rows
}

/// A hand-reviewed world's rows (`native_fold_canon_lean_v4_8_0.rs`): each
/// `reviewed` row as `fold`, plus, as `definition`, every row of `fresh` (the
/// world's digests no other world pins) that a reviewed closure rests on as a
/// boundary, transitively — without which those folds are refused whatever
/// other worlds keep. Sorted.
#[allow(dead_code)] // the v4.8.0 battery's
pub fn fold_with_fresh_boundaries(
    env: &Environment,
    reviewed: &[(String, String, String)],
    fresh: &[(String, String, String)],
) -> Vec<FoldRow> {
    fold_with_required_definitions(env, reviewed, &[], fresh)
}

/// A reviewed list plus explicitly required definition roots (such as the
/// actual reducer argument registry), and every transitive boundary they need.
/// No definition root gets its own fold permission.
#[allow(dead_code)]
pub fn fold_with_required_definitions(
    env: &Environment,
    reviewed: &[(String, String, String)],
    definitions: &[String],
    fresh: &[(String, String, String)],
) -> Vec<FoldRow> {
    use clean_kernel::name::Name;
    use std::collections::{BTreeMap, HashSet};
    let mut rows: Vec<FoldRow> = reviewed
        .iter()
        .map(|(w, n, h)| (w.clone(), n.clone(), h.clone(), "fold".to_string()))
        .collect();
    let fresh: BTreeMap<&str, (&str, &str)> = fresh
        .iter()
        .map(|(w, name, hex)| (name.as_str(), (w.as_str(), hex.as_str())))
        .collect();
    let mut work: Vec<String> = reviewed.iter().map(|(_, n, _)| n.clone()).collect();
    let mut seen: HashSet<String> = work.iter().cloned().collect();
    for definition in definitions {
        if !seen.insert(definition.clone()) {
            continue;
        }
        if let Some((world, hex)) = fresh.get(definition.as_str()) {
            rows.push((
                (*world).to_string(),
                definition.clone(),
                (*hex).to_string(),
                "definition".into(),
            ));
        }
        work.push(definition.clone());
    }
    while let Some(name) = work.pop() {
        let Ok(closure) = env.native_fold_closure(&Name::from_string(&name)) else {
            continue;
        };
        for boundary in closure.boundaries.iter().map(ToString::to_string) {
            if !seen.insert(boundary.clone()) {
                continue;
            }
            if let Some((world, hex)) = fresh.get(boundary.as_str()) {
                rows.push((
                    (*world).to_string(),
                    boundary.clone(),
                    (*hex).to_string(),
                    "definition".into(),
                ));
            }
            work.push(boundary);
        }
    }
    rows.sort();
    rows
}

/// The rows `world` pins: every minted row with the role the kernel's review
/// assigns (`review_world`), sorted, each review printed as a `REVIEW` line.
/// A re-pin reviews under the mint bypass (every `reduce_nat` head folds by
/// name, as in Lean's kernel) without the production leg; an ordinary run
/// reviews under the compiled table with it, and every `fold` row must be
/// admitted there.
#[allow(dead_code)] // the v4.30 battery's; the v4.8.0 battery reviews its own list
pub fn mint_reviewed(world: &str, env: &Environment) -> Vec<FoldRow> {
    use clean_kernel::env::native_fold_review::review_world;
    use clean_kernel::env::FoldRole;
    let repin = repin_requested();
    let reviewed = if repin {
        clean_kernel::env::native_fold_mint_bypass::run(|| review_world(env, world, false))
    } else {
        review_world(env, world, true)
    };
    let mut rows = Vec::new();
    for row in &reviewed {
        println!("{}", row.summary_line(world));
        if !repin && row.role == Some(FoldRole::Fold) {
            if let Err(why) = clean_kernel::env::native_fold_review::fold_row_fires(env, &row.name)
            {
                panic!("{world}: `fold` row {} does not fire: {why}", row.name);
            }
        }
        rows.extend(row.pinned_row(world));
    }
    rows.sort();
    rows
}

/// Compare `minted` (already narrowed to what the battery admits) with the
/// pinned rows of `world`. Equal: return. Different: re-pin under
/// [`REPIN_ENV`], otherwise panic naming every row on either side.
pub fn check_world(world: &str, minted: &[FoldRow]) {
    assert!(
        !minted.is_empty(),
        "{world}: nothing minted — the Init load found no fold key"
    );
    let mut pinned: Vec<FoldRow> = canonical_fold_rows()
        .into_iter()
        .filter(|(w, _, _, _)| w == world)
        .collect();
    pinned.sort();
    // A re-pin writes unconditionally: the compiled table can be stale by
    // then (another world's re-pin in the same round rewrote the file), so
    // "equal to the compiled rows" does not mean "equal to the file".
    if repin_requested() {
        repin(world, minted);
        return;
    }
    if minted == pinned.as_slice() {
        return;
    }
    let missing: Vec<_> = minted.iter().filter(|r| !pinned.contains(r)).collect();
    let stale: Vec<_> = pinned.iter().filter(|r| !minted.contains(r)).collect();
    panic!(
        "{world}: native_fold_canon.tsv drifted from the decoded Init.\n\
         minted but not pinned ({}): {missing:#?}\npinned but not minted ({}): {stale:#?}\n\
         Re-pin with {REPIN_ENV}=1 only after confirming each changed\n\
         closure still computes what its fold computes.",
        missing.len(),
        stale.len()
    );
}

/// Rewrite `world`'s rows of the kernel's table, keeping every other row and
/// every comment line.
fn repin(world: &str, rows: &[FoldRow]) {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-kernel/src/env/native_fold_canon.tsv");
    let text = std::fs::read_to_string(&path).expect("read native_fold_canon.tsv");
    let mut out: Vec<String> = text
        .lines()
        .filter(|line| {
            line.starts_with('#')
                || (!line.trim().is_empty() && line.split('\t').next() != Some(world))
        })
        .map(str::to_string)
        .collect();
    out.extend(
        rows.iter()
            .map(|(w, n, h, r)| format!("{w}\t{n}\t{h}\t{r}")),
    );
    std::fs::write(&path, out.join("\n") + "\n").expect("write native_fold_canon.tsv");
}
