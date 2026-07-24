// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Frequency census over a prepared Path-B batch: the coverage summary, the
//! decline **taxonomy histogram** (by [`Unsupported`] variant kind), the
//! **ranked unknown-const backlog** (the single largest growth lever — each new
//! fragment lane eats a slice of it), and the per-family support breakdown.
//!
//! This turns the opaque "68% unknown-const" taxonomy bucket
//! ([`docs/analysis/zproof-pathb-batch5.md`] §3b) into a concrete, prioritized
//! list of the specific constants worth teaching the pattern library next. Both
//! [`super::batch::write_batch`] (as `census.json`) and the
//! `pathb_unknown_const_census` example emit it.

use std::collections::BTreeMap;

use super::batch::PreparedGoal;
use super::types::{LeanGoal, Unsupported};

/// One ranked backlog row: an Isabelle constant the pattern library does not
/// render, its decline frequency over the pool, and an example serial.
#[derive(Debug, Clone, serde::Serialize)]
pub struct CensusEntry {
    /// The Isabelle constant name (`List.foldr`, `GCD.gcd_class.gcd`, …).
    pub name: String,
    /// How many pool declines named this constant.
    pub count: usize,
    /// A representative corpus serial that declined on it (for spot-checking).
    pub example_serial: Option<i64>,
}

/// Per-family support tally (family = first dotted component of the Isabelle
/// name, e.g. `List`, `Nat`, `GCD`).
#[derive(Debug, Clone, Copy, Default, serde::Serialize)]
pub struct FamilySupport {
    /// Faithfully translated in this family.
    pub supported: usize,
    /// Total candidates in this family.
    pub total: usize,
}

/// A frequency census over a prepared batch.
#[derive(Debug, Clone, serde::Serialize)]
pub struct Census {
    /// Total candidates.
    pub total: usize,
    /// Faithfully translated.
    pub supported: usize,
    /// Declined.
    pub unsupported: usize,
    /// Supported fraction, percent.
    pub coverage_pct: f64,
    /// Decline-reason kind → count (`unknown-const`, `class-premise`, …).
    pub reason_histogram: BTreeMap<String, usize>,
    /// Unknown Isabelle constants ranked by decline frequency (desc), then name.
    pub unknown_const_rank: Vec<CensusEntry>,
    /// Family → support tally.
    pub per_family: BTreeMap<String, FamilySupport>,
}

/// The family key of an Isabelle theorem name: its first dotted component.
fn family_of(isabelle: &str) -> &str {
    isabelle.split('.').next().unwrap_or(isabelle)
}

/// The taxonomy bucket key for an [`Unsupported`] verdict — the `Display` prefix
/// up to (not including) any `:name` payload, so all `unknown-const:*` fold into
/// one `unknown-const` bucket.
fn reason_kind(u: &Unsupported) -> String {
    let s = u.to_string();
    match s.split_once(':') {
        Some((kind, _)) => kind.to_string(),
        None => s,
    }
}

impl Census {
    /// Aggregate a census from prepared goals.
    #[must_use]
    pub fn from_goals(goals: &[PreparedGoal]) -> Self {
        let mut reason_histogram: BTreeMap<String, usize> = BTreeMap::new();
        let mut per_family: BTreeMap<String, FamilySupport> = BTreeMap::new();
        // const name -> (count, first-seen example serial)
        let mut unknown: BTreeMap<String, (usize, Option<i64>)> = BTreeMap::new();

        let mut supported = 0usize;
        for g in goals {
            let fam = per_family
                .entry(family_of(&g.isabelle).to_string())
                .or_default();
            fam.total += 1;
            match &g.goal {
                LeanGoal::Supported(_) => {
                    supported += 1;
                    fam.supported += 1;
                }
                LeanGoal::Unsupported(u) => {
                    *reason_histogram.entry(reason_kind(u)).or_insert(0) += 1;
                    if let Unsupported::UnknownConst(name) = u {
                        let e = unknown.entry(name.clone()).or_insert((0, None));
                        e.0 += 1;
                        if e.1.is_none() {
                            e.1 = g.serial;
                        }
                    }
                }
            }
        }

        let mut unknown_const_rank: Vec<CensusEntry> = unknown
            .into_iter()
            .map(|(name, (count, example_serial))| CensusEntry {
                name,
                count,
                example_serial,
            })
            .collect();
        // Rank by frequency desc, then name asc for a stable, reproducible order.
        unknown_const_rank.sort_by(|a, b| b.count.cmp(&a.count).then_with(|| a.name.cmp(&b.name)));

        let total = goals.len();
        let coverage_pct = if total == 0 {
            0.0
        } else {
            100.0 * supported as f64 / total as f64
        };
        Census {
            total,
            supported,
            unsupported: total - supported,
            coverage_pct,
            reason_histogram,
            unknown_const_rank,
            per_family,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::lean_name_from_isabelle;
    use super::super::types::{LeanGoal, SupportedGoal, Unsupported};
    use super::*;

    #[test]
    fn census_ranks_unknown_const_and_tallies_families() {
        let mk = |id: &str, serial: i64, isa: &str, goal: LeanGoal| PreparedGoal {
            id: id.to_string(),
            serial: Some(serial),
            isabelle: isa.to_string(),
            lean: lean_name_from_isabelle(isa),
            goal,
        };
        let sup = LeanGoal::Supported(SupportedGoal {
            name: "t".into(),
            signature: "theorem t : True".into(),
        });
        let goals = vec![
            mk(
                "s1",
                1,
                "List.foo",
                LeanGoal::Unsupported(Unsupported::UnknownConst("List.foldr".into())),
            ),
            mk(
                "s2",
                2,
                "List.bar",
                LeanGoal::Unsupported(Unsupported::UnknownConst("List.foldr".into())),
            ),
            mk(
                "s3",
                3,
                "GCD.g",
                LeanGoal::Unsupported(Unsupported::UnknownConst("GCD.gcd_class.gcd".into())),
            ),
            mk("s4", 4, "List.baz", sup.clone()),
            mk(
                "s5",
                5,
                "Nat.q",
                LeanGoal::Unsupported(Unsupported::PolymorphicOrder),
            ),
        ];
        let c = Census::from_goals(&goals);
        assert_eq!(c.total, 5);
        assert_eq!(c.supported, 1);
        assert_eq!(c.unsupported, 4);
        // Ranked: List.foldr (2) before GCD.gcd_class.gcd (1).
        assert_eq!(c.unknown_const_rank[0].name, "List.foldr");
        assert_eq!(c.unknown_const_rank[0].count, 2);
        assert_eq!(c.unknown_const_rank[0].example_serial, Some(1));
        assert_eq!(c.unknown_const_rank[1].name, "GCD.gcd_class.gcd");
        // Taxonomy histogram folds unknown-const:* into one bucket.
        assert_eq!(c.reason_histogram.get("unknown-const"), Some(&3));
        assert_eq!(c.reason_histogram.get("polymorphic-order"), Some(&1));
        // Per-family: List has 3 total (foo/bar/baz), 1 supported (baz).
        let list = c.per_family.get("List").expect("List family present");
        assert_eq!((list.total, list.supported), (3, 1));
    }
}
