// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A world's ROLES (`native_fold_review.rs`): which of the rows an
//! environment mints are pinned, and as what.
//!
//! - `fold`: every row whose own rules pass [`super::review`], unless another
//!   world's row pins the same digest `refused` (a veto: the review's outcome
//!   can depend on what lies outside the closure).
//! - `refused`: every row whose own rules were exercised and DISAGREE — pinned
//!   whether or not anything needs it, since it is evidence that vetoes a
//!   `fold` row of the same digest in every world.
//! - `definition`: a row that is neither but that a `fold` row needs — a
//!   BOUNDARY of its closure (transitively: a boundary's own boundaries), or a
//!   constant its reducer RECOGNIZES in its arguments
//!   (`native_fold_canon::RECOGNIZED_ARGUMENT_NAMES`). Such a row vouches only
//!   that the closure is a known definition; its own reducer and folds stay
//!   off.
//! - every other minted row stays unpinned.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::{review, Review};
use crate::env::native_fold_authority::{FoldDigest, FoldRole};
use crate::env::Environment;
use crate::name::Name;

/// One minted row, its review and the role it is pinned with (`None`: not
/// pinned).
#[derive(Debug, Clone)]
pub struct RowReview {
    /// The fold key.
    pub name: Name,
    /// Its closure digest in this world.
    pub digest: FoldDigest,
    /// The role it is pinned with, if any.
    pub role: Option<FoldRole>,
    /// The review of its own rules.
    pub review: Review,
    /// For a `definition` row, the `fold` row that needs it.
    pub needed_by: Option<Name>,
    /// For a row this world reviewed as agreeing, the other world whose
    /// `refused` row of the same digest vetoes it.
    pub vetoed_by: Option<String>,
}

impl RowReview {
    /// One tab-separated line for the review table
    /// (`REVIEW world name role fired/cases verdict`).
    #[must_use]
    pub fn summary_line(&self, world: &str) -> String {
        let role = self.role.map_or("unpinned", FoldRole::as_str);
        let verdict = if self.review.passed() {
            "reviewed".to_string()
        } else if let Some(why) = &self.review.unreviewable {
            format!("not reviewed: {why}")
        } else if let Some(first) = self.review.failures.first() {
            let first: String = first.chars().take(300).collect();
            format!(
                "DISAGREES ({} failures): {first}",
                self.review.failures.len()
            )
        } else if self.review.fired == 0 && self.review.unanswered > 0 {
            "not reviewed: no independent reference for its inputs".to_string()
        } else {
            "not reviewed: the fold fired on no input".to_string()
        };
        let mut needed = self
            .needed_by
            .as_ref()
            .map(|n| format!(" (needed by {n})"))
            .unwrap_or_default();
        if let Some(world) = &self.vetoed_by {
            needed.push_str(&format!(" (vetoed by {world})"));
        }
        format!(
            "REVIEW\t{world}\t{}\t{role}{needed}\t{}/{}\t{verdict}",
            self.name, self.review.fired, self.review.cases
        )
    }

    /// The pinned row `(world, name, hex, role)`, or `None` when unpinned.
    #[must_use]
    pub fn pinned_row(&self, world: &str) -> Option<(String, String, String, String)> {
        let role = self.role?;
        Some((
            world.to_string(),
            self.name.to_string(),
            self.digest.to_hex(),
            role.as_str().to_string(),
        ))
    }
}

/// The table's rows as they stand ON DISK (a re-pin rewrites the file while
/// the compiled table stays the one this binary was built with, so a veto
/// another world's re-pin just added is visible to the next re-pin without a
/// rebuild), or the compiled rows when the file cannot be read. In an
/// ordinary run the two are the same file.
fn table_rows() -> Vec<(String, String, String, String)> {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/env/native_fold_canon.tsv");
    let Ok(text) = std::fs::read_to_string(path) else {
        return crate::env::canonical_fold_rows();
    };
    text.lines()
        .filter(|line| !line.trim().is_empty() && !line.starts_with('#'))
        .filter_map(|line| {
            let mut cols = line.split('\t');
            let row = (
                cols.next()?.to_string(),
                cols.next()?.to_string(),
                cols.next()?.to_string(),
                cols.next()?.to_string(),
            );
            cols.next().is_none().then_some(row)
        })
        .collect()
}

/// Review every row `env` mints (`Environment::native_fold_pin_rows`) for
/// `world` and assign roles (module docs). `production` adds the production
/// leg to every review (ordinary runs; a re-pin passes `false`). The vetoes
/// are read from the table's OTHER worlds ([`table_rows`]), so after one
/// world's re-pin adds a `refused` row, the worlds sharing that digest re-pin
/// once more to agree with it.
#[must_use]
pub fn review_world(env: &Environment, world: &str, production: bool) -> Vec<RowReview> {
    let minted: BTreeMap<Name, FoldDigest> = env.native_fold_pin_rows().into_iter().collect();
    // `CLEAN_FOLD_REVIEW_TRACE=1` names each head before its review starts,
    // so a review that runs away is attributable.
    let trace = std::env::var_os("CLEAN_FOLD_REVIEW_TRACE").is_some();
    let reviews: HashMap<Name, Review> = minted
        .keys()
        .map(|name| {
            if trace {
                eprintln!("REVIEWING {name}");
            }
            let started = std::time::Instant::now();
            let r = review(env, name, production);
            if trace {
                eprintln!(
                    "REVIEWED {name} {}ms fired={}/{} failures={}",
                    started.elapsed().as_millis(),
                    r.fired,
                    r.cases,
                    r.failures.len()
                );
            }
            (name.clone(), r)
        })
        .collect();
    let refused_elsewhere: HashMap<(String, String), String> = table_rows()
        .into_iter()
        .filter(|(w, _, _, role)| w != world && role == FoldRole::Refused.as_str())
        .map(|(w, name, hex, _)| ((name, hex), w))
        .collect();
    let vetoes: HashMap<Name, String> = reviews
        .iter()
        .filter(|(_, r)| r.passed())
        .filter_map(|(n, _)| {
            let hex = minted.get(n)?.to_hex();
            refused_elsewhere
                .get(&(n.to_string(), hex))
                .map(|w| (n.clone(), w.clone()))
        })
        .collect();
    let fold: BTreeSet<Name> = reviews
        .iter()
        .filter(|(n, r)| r.passed() && !vetoes.contains_key(*n))
        .map(|(n, _)| n.clone())
        .collect();
    let refused: BTreeSet<Name> = reviews
        .iter()
        .filter(|(_, r)| r.unreviewable.is_none() && !r.failures.is_empty())
        .map(|(n, _)| n.clone())
        .collect();
    let mut needed: BTreeMap<Name, Name> = BTreeMap::new();
    let mut work: Vec<(Name, Name)> = Vec::new();
    let push_needs =
        |name: &Name, by: &Name, with_recognized: bool, work: &mut Vec<(Name, Name)>| {
            if let Ok(closure) = env.native_fold_closure(name) {
                work.extend(closure.boundaries.into_iter().map(|b| (b, by.clone())));
            }
            if with_recognized && env.get_native_reducer(name).is_some() {
                work.extend(
                    crate::env::recognized_argument_names(name)
                        .iter()
                        .filter(|r| env.get_const(r).is_some())
                        .map(|r| (r.clone(), by.clone())),
                );
            }
        };
    for name in &fold {
        push_needs(name, name, true, &mut work);
    }
    while let Some((name, by)) = work.pop() {
        if fold.contains(&name) || needed.contains_key(&name) || !minted.contains_key(&name) {
            continue;
        }
        needed.insert(name.clone(), by.clone());
        push_needs(&name, &by, false, &mut work);
    }
    minted
        .into_iter()
        .map(|(name, digest)| {
            let role = if fold.contains(&name) {
                Some(FoldRole::Fold)
            } else if refused.contains(&name) {
                Some(FoldRole::Refused)
            } else if needed.contains_key(&name) {
                Some(FoldRole::Definition)
            } else {
                None
            };
            RowReview {
                review: reviews.get(&name).cloned().unwrap_or_default(),
                needed_by: needed.get(&name).cloned(),
                vetoed_by: vetoes.get(&name).cloned(),
                name,
                digest,
                role,
            }
        })
        .collect()
}
