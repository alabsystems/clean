// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Isabelle/HOL ↔ Lean 4/Mathlib cross-system equivalence bridge.
//!
//! The HOL-family unifier ([`crate::hol::cross_system`]) only aligns
//! HOL Light / HOL4 / Isabelle by *base name*, and the generic
//! [`crate::cross_system_index::CrossSystemIndex`] only links constants whose
//! names collapse to the *same* canonical token under
//! [`crate::equivalence::normalize_name`]. Neither catches the common case
//! where Isabelle/HOL and Lean 4/Mathlib state the *same* theorem under
//! *different* names — e.g. Isabelle `rev_rev_ident` vs Mathlib
//! `List.reverse_reverse`, or Isabelle `add.commute` vs Mathlib `add_comm`.
//!
//! This module bridges that gap with two layers:
//!
//! 1. **Curated alias layer** — a hand-vetted table
//!    ([`isabelle_mathlib_aliases.json`]) of high-confidence concept
//!    correspondences between real Isabelle and real Mathlib declaration names.
//!    An Isabelle decl matches a curated alias when one of its dotted-suffix
//!    keys equals the alias's `isabelle` field; the Mathlib side matches the
//!    same way against the `mathlib` field.
//! 2. **Normalized-name layer** — reuses [`normalize_name`] so that decls that
//!    *do* share a canonical token (e.g. both `..add_assoc`) link automatically.
//!
//! Discovered correspondences are emitted as [`IsabelleMathlibLink`] records
//! and can be serialized to a JSON [`BridgeReport`] — closing the
//! "links are in-memory only" gap noted in the cross-system audit — or turned
//! into `(ConstantIdx, ConstantIdx, EquivConfidence)` triples for registration
//! into a [`crate::library::MathverseLibrary`] via `add_equivalence`.
//!
//! **Soundness note.** These links are *heuristic name/concept correspondences*,
//! not machine-checked equivalence proofs. They are surfaced as
//! [`EquivConfidence::ErasedCandidate`] / [`EquivConfidence::ManualReview`] and
//! must never be promoted to `ProvedEquivalent` without an actual proof.

use std::collections::HashMap;
use std::io::{self, Write};

use serde::{Deserialize, Serialize};

use crate::equivalence::normalize_name;
use crate::graph_alpha::EquivConfidence;
use crate::types::{ConstantIdx, SourceSystem};

/// Curated alias table, embedded at compile time for a self-contained crate.
const ALIAS_JSON: &str = include_str!("isabelle_mathlib_aliases.json");

/// Confidence assigned to a purely coincidental normalized-name match (weaker
/// than any curated alias).
const NORMALIZED_MATCH_CONFIDENCE: f32 = 0.6;

/// Confidence at/above which a link is registered as an
/// [`EquivConfidence::ErasedCandidate`] rather than [`EquivConfidence::ManualReview`].
const CANDIDATE_CONFIDENCE_THRESHOLD: f32 = 0.85;

/// How a correspondence was established.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LinkMethod {
    /// Hand-curated alias (typically different names, same concept).
    CuratedAlias,
    /// Both names collapse to the same canonical token under `normalize_name`.
    NormalizedName,
}

/// One curated Isabelle ↔ Mathlib correspondence from the alias table.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct AliasEntry {
    /// Human-readable concept (e.g. "commutativity of addition").
    pub concept: String,
    /// Isabelle decl name (or dotted-suffix form) as emitted in `.yxml` exports.
    pub isabelle: String,
    /// Lean 4/Mathlib decl name.
    pub mathlib: String,
    /// `"theorem"` or `"definition"`.
    #[serde(default = "default_kind")]
    pub kind: String,
    /// Curator confidence in `[0.0, 1.0]`.
    #[serde(default = "default_conf")]
    pub confidence: f32,
    /// Optional caveat.
    #[serde(default)]
    pub note: String,
}

fn default_kind() -> String {
    "theorem".to_owned()
}
fn default_conf() -> f32 {
    0.8
}

#[derive(Clone, Debug, Default, Deserialize)]
struct AliasFile {
    #[serde(default)]
    aliases: Vec<AliasEntry>,
}

/// A resolved correspondence between an Isabelle declaration and a Mathlib
/// declaration.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct IsabelleMathlibLink {
    /// Canonical key the two names were matched under.
    pub canonical: String,
    /// Full Isabelle decl name (as stored in the shard / `.yxml`).
    pub isabelle_name: String,
    /// Full Mathlib decl name.
    pub mathlib_name: String,
    /// How the link was established.
    pub method: LinkMethod,
    /// Confidence in `[0.0, 1.0]`.
    pub confidence: f32,
}

impl IsabelleMathlibLink {
    /// Map this link's confidence to a graph [`EquivConfidence`].
    ///
    /// Name/concept correspondences are never `Exact` or `ProvedEquivalent`
    /// (those imply a checked equivalence); they are candidates pending review.
    #[must_use]
    pub fn equiv_confidence(&self) -> EquivConfidence {
        if self.confidence >= CANDIDATE_CONFIDENCE_THRESHOLD {
            EquivConfidence::ErasedCandidate {
                score: self.confidence,
            }
        } else {
            EquivConfidence::ManualReview
        }
    }
}

/// Serializable bundle of discovered links plus summary statistics.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct BridgeReport {
    /// Schema tag for forward-compat.
    pub schema: String,
    /// Number of distinct Isabelle decl names indexed.
    pub isabelle_names_indexed: usize,
    /// Number of distinct Mathlib decl names indexed.
    pub mathlib_names_indexed: usize,
    /// Number of curated aliases loaded.
    pub curated_alias_count: usize,
    /// Links established via the curated alias layer.
    pub curated_link_count: usize,
    /// Links established via the normalized-name layer.
    pub normalized_link_count: usize,
    /// All discovered links (sorted, deduplicated).
    pub links: Vec<IsabelleMathlibLink>,
}

/// Cross-system bridge between Isabelle/HOL and Lean 4/Mathlib.
#[derive(Clone, Debug)]
pub struct IsabelleMathlibBridge {
    aliases: Vec<AliasEntry>,
    /// Dotted-suffix key → indices of curated aliases whose `isabelle` field
    /// equals that key.
    isa_alias_keys: HashMap<String, Vec<usize>>,
    /// Dotted-suffix key → indices of curated aliases whose `mathlib` field
    /// equals that key.
    ml_alias_keys: HashMap<String, Vec<usize>>,
    isabelle_names: Vec<String>,
    mathlib_names: Vec<String>,
}

impl Default for IsabelleMathlibBridge {
    fn default() -> Self {
        Self::with_builtin_aliases()
    }
}

impl IsabelleMathlibBridge {
    /// Build a bridge from the embedded curated alias table.
    ///
    /// The embedded table is validated at build time, so a parse failure here
    /// is a programmer error in the data file rather than a runtime condition.
    #[must_use]
    pub fn with_builtin_aliases() -> Self {
        let file: AliasFile = serde_json::from_str(ALIAS_JSON)
            .expect("invariant: embedded isabelle_mathlib_aliases.json must be valid");
        Self::from_aliases(file.aliases)
    }

    /// Build a bridge from an explicit alias list (used by tests / custom tables).
    #[must_use]
    pub fn from_aliases(aliases: Vec<AliasEntry>) -> Self {
        let mut isa_alias_keys: HashMap<String, Vec<usize>> = HashMap::new();
        let mut ml_alias_keys: HashMap<String, Vec<usize>> = HashMap::new();
        for (i, a) in aliases.iter().enumerate() {
            isa_alias_keys
                .entry(a.isabelle.clone())
                .or_default()
                .push(i);
            ml_alias_keys.entry(a.mathlib.clone()).or_default().push(i);
        }
        Self {
            aliases,
            isa_alias_keys,
            ml_alias_keys,
            isabelle_names: Vec::new(),
            mathlib_names: Vec::new(),
        }
    }

    /// Number of curated aliases.
    #[must_use]
    pub fn alias_count(&self) -> usize {
        self.aliases.len()
    }

    /// Index a batch of Isabelle declaration names (fully qualified as exported).
    pub fn index_isabelle_names<I, S>(&mut self, names: I)
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.isabelle_names
            .extend(names.into_iter().map(Into::into));
    }

    /// Index a batch of Mathlib declaration names.
    pub fn index_mathlib_names<I, S>(&mut self, names: I)
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.mathlib_names.extend(names.into_iter().map(Into::into));
    }

    /// The set of real Mathlib names referenced by the curated alias table.
    ///
    /// Useful as a Mathlib name source when an on-disk Mathlib shard is not
    /// available: every entry here is a real Mathlib declaration name.
    #[must_use]
    pub fn curated_mathlib_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.aliases.iter().map(|a| a.mathlib.clone()).collect();
        names.sort();
        names.dedup();
        names
    }

    /// Compute all Isabelle ↔ Mathlib links at or above `min_confidence`.
    ///
    /// Curated-alias links take precedence; a pair already linked via the
    /// curated layer is not re-emitted by the normalized-name layer.
    #[must_use]
    pub fn compute_links(&self, min_confidence: f32) -> Vec<IsabelleMathlibLink> {
        let mut links: Vec<IsabelleMathlibLink> = Vec::new();
        let mut seen: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();

        // -- Layer 1: curated aliases ------------------------------------
        // For each indexed Isabelle name, find curated aliases whose `isabelle`
        // field is one of its dotted-suffix keys; then require the alias's
        // Mathlib name to also be present among indexed Mathlib names.
        let ml_by_key = self.index_by_suffix(&self.mathlib_names);
        for isa_name in &self.isabelle_names {
            for key in suffix_keys(isa_name) {
                let Some(alias_idxs) = self.isa_alias_keys.get(&key) else {
                    continue;
                };
                for &ai in alias_idxs {
                    let alias = &self.aliases[ai];
                    if alias.confidence < min_confidence {
                        continue;
                    }
                    // Mathlib side must be present in the indexed Mathlib names.
                    let Some(ml_fulls) = ml_by_key.get(&alias.mathlib) else {
                        continue;
                    };
                    for ml_full in ml_fulls {
                        let pair = (isa_name.clone(), ml_full.clone());
                        if !seen.insert(pair.clone()) {
                            continue;
                        }
                        links.push(IsabelleMathlibLink {
                            canonical: normalize_token(&alias.concept),
                            isabelle_name: isa_name.clone(),
                            mathlib_name: ml_full.clone(),
                            method: LinkMethod::CuratedAlias,
                            confidence: alias.confidence,
                        });
                    }
                }
            }
        }

        // -- Layer 2: normalized-name coincidences -----------------------
        if NORMALIZED_MATCH_CONFIDENCE >= min_confidence {
            let mut isa_by_canon: HashMap<String, Vec<&String>> = HashMap::new();
            for n in &self.isabelle_names {
                isa_by_canon
                    .entry(normalize_name(n, SourceSystem::Isabelle))
                    .or_default()
                    .push(n);
            }
            let mut ml_by_canon: HashMap<String, Vec<&String>> = HashMap::new();
            for n in &self.mathlib_names {
                ml_by_canon
                    .entry(normalize_name(n, SourceSystem::Lean4))
                    .or_default()
                    .push(n);
            }
            for (canon, isa_list) in &isa_by_canon {
                let Some(ml_list) = ml_by_canon.get(canon) else {
                    continue;
                };
                for isa_name in isa_list {
                    for ml_name in ml_list {
                        let pair = ((*isa_name).clone(), (*ml_name).clone());
                        if !seen.insert(pair.clone()) {
                            continue;
                        }
                        links.push(IsabelleMathlibLink {
                            canonical: canon.clone(),
                            isabelle_name: (*isa_name).clone(),
                            mathlib_name: (*ml_name).clone(),
                            method: LinkMethod::NormalizedName,
                            confidence: NORMALIZED_MATCH_CONFIDENCE,
                        });
                    }
                }
            }
        }

        links.sort_by(|a, b| {
            a.isabelle_name
                .cmp(&b.isabelle_name)
                .then_with(|| a.mathlib_name.cmp(&b.mathlib_name))
        });
        links
    }

    /// Build a serializable [`BridgeReport`] over the indexed names.
    #[must_use]
    pub fn report(&self, min_confidence: f32) -> BridgeReport {
        let links = self.compute_links(min_confidence);
        let curated = links
            .iter()
            .filter(|l| l.method == LinkMethod::CuratedAlias)
            .count();
        let normalized = links.len() - curated;
        let mut isa: Vec<&String> = self.isabelle_names.iter().collect();
        isa.sort();
        isa.dedup();
        let mut ml: Vec<&String> = self.mathlib_names.iter().collect();
        ml.sort();
        ml.dedup();
        BridgeReport {
            schema: "isabelle-mathlib-bridge-v1".to_owned(),
            isabelle_names_indexed: isa.len(),
            mathlib_names_indexed: ml.len(),
            curated_alias_count: self.aliases.len(),
            curated_link_count: curated,
            normalized_link_count: normalized,
            links,
        }
    }

    /// Resolve links into `(ConstantIdx, ConstantIdx, EquivConfidence)` triples
    /// ready for [`crate::library::MathverseLibrary::add_equivalence`].
    ///
    /// `resolve_isa` / `resolve_mathlib` map a full decl name to its library
    /// constant index; links whose endpoints cannot both be resolved are
    /// skipped.
    pub fn equivalence_triples<FI, FM>(
        links: &[IsabelleMathlibLink],
        resolve_isa: FI,
        resolve_mathlib: FM,
    ) -> Vec<(ConstantIdx, ConstantIdx, EquivConfidence)>
    where
        FI: Fn(&str) -> Option<ConstantIdx>,
        FM: Fn(&str) -> Option<ConstantIdx>,
    {
        links
            .iter()
            .filter_map(|link| {
                let a = resolve_isa(&link.isabelle_name)?;
                let b = resolve_mathlib(&link.mathlib_name)?;
                Some((a, b, link.equiv_confidence()))
            })
            .collect()
    }

    /// Group indexed names by every dotted-suffix key so curated `mathlib`
    /// fields (which may be unqualified, e.g. `add_comm`) match qualified
    /// Mathlib names (e.g. `Nat.add_comm`).
    fn index_by_suffix(&self, names: &[String]) -> HashMap<String, Vec<String>> {
        let mut map: HashMap<String, Vec<String>> = HashMap::new();
        for n in names {
            for key in suffix_keys(n) {
                map.entry(key).or_default().push(n.clone());
            }
        }
        for v in map.values_mut() {
            v.sort();
            v.dedup();
        }
        map
    }
}

/// Write a [`BridgeReport`] as pretty JSON.
///
/// # Errors
/// Returns an [`io::Error`] if serialization or writing fails.
pub fn write_report(w: &mut impl Write, report: &BridgeReport) -> io::Result<()> {
    let json = serde_json::to_string_pretty(report)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
    w.write_all(json.as_bytes())?;
    w.write_all(b"\n")
}

/// Parse a [`BridgeReport`] from JSON.
///
/// # Errors
/// Returns an [`io::Error`] if the input is not a valid report.
pub fn read_report(json: &str) -> io::Result<BridgeReport> {
    serde_json::from_str(json).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
}

/// Produce the dotted-suffix keys of a qualified name: the last 1..=4 segments.
///
/// `HOL.Groups.add.commute` → `["commute", "add.commute", "Groups.add.commute",
/// "HOL.Groups.add.commute"]`. Case-sensitive (Isabelle and Lean are).
fn suffix_keys(name: &str) -> Vec<String> {
    let parts: Vec<&str> = name.split('.').collect();
    let mut keys = Vec::with_capacity(4);
    let n = parts.len();
    for take in 1..=n.min(4) {
        keys.push(parts[n - take..].join("."));
    }
    keys
}

/// Normalize a concept label / canonical token: lowercase, spaces/dots/dashes
/// to underscores.
fn normalize_token(s: &str) -> String {
    s.to_lowercase()
        .replace([' ', '.', '-', '/'], "_")
        .replace("__", "_")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_aliases() -> Vec<AliasEntry> {
        vec![
            AliasEntry {
                concept: "commutativity of addition".to_owned(),
                isabelle: "add.commute".to_owned(),
                mathlib: "add_comm".to_owned(),
                kind: "theorem".to_owned(),
                confidence: 0.97,
                note: String::new(),
            },
            AliasEntry {
                concept: "reverse of reverse".to_owned(),
                isabelle: "rev_rev_ident".to_owned(),
                mathlib: "List.reverse_reverse".to_owned(),
                kind: "theorem".to_owned(),
                confidence: 0.9,
                note: String::new(),
            },
        ]
    }

    #[test]
    fn test_builtin_table_parses_and_is_nonempty() {
        let bridge = IsabelleMathlibBridge::with_builtin_aliases();
        assert!(
            bridge.alias_count() >= 50,
            "embedded alias table should be substantial, got {}",
            bridge.alias_count()
        );
    }

    #[test]
    fn test_suffix_keys() {
        assert_eq!(
            suffix_keys("HOL.Groups.add.commute"),
            vec![
                "commute".to_owned(),
                "add.commute".to_owned(),
                "Groups.add.commute".to_owned(),
                "HOL.Groups.add.commute".to_owned(),
            ]
        );
        assert_eq!(
            suffix_keys("rev_rev_ident"),
            vec!["rev_rev_ident".to_owned()]
        );
    }

    #[test]
    fn test_curated_link_different_names() {
        // Isabelle `rev_rev_ident` ↔ Mathlib `List.reverse_reverse`: pure
        // normalization would NEVER match these; the curated layer must.
        let mut bridge = IsabelleMathlibBridge::from_aliases(sample_aliases());
        bridge.index_isabelle_names(["HOL.List.rev_rev_ident".to_owned()]);
        bridge.index_mathlib_names(["List.reverse_reverse".to_owned()]);

        let links = bridge.compute_links(0.0);
        assert_eq!(links.len(), 1);
        assert_eq!(links[0].method, LinkMethod::CuratedAlias);
        assert_eq!(links[0].isabelle_name, "HOL.List.rev_rev_ident");
        assert_eq!(links[0].mathlib_name, "List.reverse_reverse");
        assert!((links[0].confidence - 0.9).abs() < f32::EPSILON);
    }

    #[test]
    fn test_curated_link_dotted_locale_form() {
        // Isabelle exports `Groups.abel_semigroup.add.commute`; alias key is
        // `add.commute`; Mathlib `Nat.add_comm` matches unqualified `add_comm`.
        let mut bridge = IsabelleMathlibBridge::from_aliases(sample_aliases());
        bridge.index_isabelle_names(["Groups.abel_semigroup.add.commute".to_owned()]);
        bridge.index_mathlib_names(["Nat.add_comm".to_owned()]);

        let links = bridge.compute_links(0.0);
        assert_eq!(
            links.len(),
            1,
            "dotted locale form should match add.commute"
        );
        assert_eq!(links[0].mathlib_name, "Nat.add_comm");
        assert_eq!(links[0].method, LinkMethod::CuratedAlias);
    }

    #[test]
    fn test_min_confidence_filters_curated() {
        let mut bridge = IsabelleMathlibBridge::from_aliases(sample_aliases());
        bridge.index_isabelle_names(["HOL.List.rev_rev_ident".to_owned()]);
        bridge.index_mathlib_names(["List.reverse_reverse".to_owned()]);
        // alias confidence is 0.9; a 0.95 floor drops it.
        assert!(bridge.compute_links(0.95).is_empty());
    }

    #[test]
    fn test_normalized_name_layer() {
        // No curated alias for `add_assoc`, but both normalize to `add_assoc`.
        let mut bridge = IsabelleMathlibBridge::from_aliases(Vec::new());
        bridge.index_isabelle_names(["HOL.Groups.add_assoc".to_owned()]);
        bridge.index_mathlib_names(["add_assoc".to_owned()]);

        let links = bridge.compute_links(0.0);
        assert_eq!(links.len(), 1);
        assert_eq!(links[0].method, LinkMethod::NormalizedName);
        assert_eq!(links[0].canonical, "add_assoc");
    }

    #[test]
    fn test_curated_precedence_over_normalized() {
        // If a pair is both a curated alias AND normalizes equal, only one
        // (curated) link is emitted.
        let aliases = vec![AliasEntry {
            concept: "addition associativity".to_owned(),
            isabelle: "add_assoc".to_owned(),
            mathlib: "add_assoc".to_owned(),
            kind: "theorem".to_owned(),
            confidence: 0.95,
            note: String::new(),
        }];
        let mut bridge = IsabelleMathlibBridge::from_aliases(aliases);
        bridge.index_isabelle_names(["HOL.Groups.add_assoc".to_owned()]);
        bridge.index_mathlib_names(["add_assoc".to_owned()]);

        let links = bridge.compute_links(0.0);
        assert_eq!(links.len(), 1);
        assert_eq!(links[0].method, LinkMethod::CuratedAlias);
    }

    #[test]
    fn test_report_round_trip() {
        let mut bridge = IsabelleMathlibBridge::from_aliases(sample_aliases());
        bridge.index_isabelle_names(["HOL.List.rev_rev_ident".to_owned()]);
        bridge.index_mathlib_names(["List.reverse_reverse".to_owned()]);

        let report = bridge.report(0.0);
        assert_eq!(report.curated_link_count, 1);
        assert_eq!(report.isabelle_names_indexed, 1);

        let mut buf = Vec::new();
        write_report(&mut buf, &report).expect("write report");
        let json = String::from_utf8(buf).expect("utf8");
        let back = read_report(&json).expect("read report");
        assert_eq!(report, back);
    }

    #[test]
    fn test_equivalence_triples_resolution() {
        let mut bridge = IsabelleMathlibBridge::from_aliases(sample_aliases());
        bridge.index_isabelle_names(["HOL.List.rev_rev_ident".to_owned()]);
        bridge.index_mathlib_names(["List.reverse_reverse".to_owned()]);
        let links = bridge.compute_links(0.0);

        let triples = IsabelleMathlibBridge::equivalence_triples(
            &links,
            |n| (n == "HOL.List.rev_rev_ident").then_some(10),
            |n| (n == "List.reverse_reverse").then_some(20),
        );
        assert_eq!(triples.len(), 1);
        assert_eq!(triples[0].0, 10);
        assert_eq!(triples[0].1, 20);
        assert!(matches!(
            triples[0].2,
            EquivConfidence::ErasedCandidate { .. }
        ));
    }

    #[test]
    fn test_equiv_confidence_thresholds() {
        let high = IsabelleMathlibLink {
            canonical: "c".to_owned(),
            isabelle_name: "i".to_owned(),
            mathlib_name: "m".to_owned(),
            method: LinkMethod::CuratedAlias,
            confidence: 0.9,
        };
        assert!(matches!(
            high.equiv_confidence(),
            EquivConfidence::ErasedCandidate { .. }
        ));
        let low = IsabelleMathlibLink {
            confidence: 0.6,
            ..high.clone()
        };
        assert!(matches!(
            low.equiv_confidence(),
            EquivConfidence::ManualReview
        ));
    }

    #[test]
    fn test_curated_mathlib_names_are_real() {
        let bridge = IsabelleMathlibBridge::with_builtin_aliases();
        let names = bridge.curated_mathlib_names();
        assert!(names.contains(&"add_comm".to_owned()));
        assert!(names.iter().all(|n| !n.is_empty()));
    }
}
