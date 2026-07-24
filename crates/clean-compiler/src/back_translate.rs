// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Back-Translation Infrastructure for Debugging Optimized IR
//!
//! Maps optimized IR constructs back to their source-level origins, enabling
//! debuggers and diagnostic tools to trace through optimization passes.
//!
//! Each optimization pass uses a [`PassTracer`] to record transformations
//! (renames, inlines, eliminations). The tracer produces a [`BackTranslationMap`]
//! that can look up the source origin of any optimized variable.
//!
//! Part of #1099.

use crate::ir::VarId;
use clean_kernel::Name;
use std::collections::HashMap;
use std::fmt;

/// A source location in the pre-optimization code.
///
/// Records which declaration and variable an optimized IR variable originated
/// from, along with the name of the pass that introduced the mapping.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceOrigin {
    /// The declaration (function) name where this variable originated.
    pub decl_name: Name,
    /// The original variable name, if known (e.g., a user-written let binding).
    pub var_name: Option<Name>,
    /// The optimization pass that created this mapping.
    pub pass: String,
}

impl fmt::Display for SourceOrigin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}", self.pass, self.decl_name)?;
        if let Some(ref var) = self.var_name {
            write!(f, ".{}", var)?;
        }
        Ok(())
    }
}

/// Reason a variable was eliminated during optimization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EliminationRecord {
    /// The variable that was eliminated.
    pub var: VarId,
    /// Human-readable reason for elimination (e.g., "dead code", "constant folded").
    pub reason: String,
    /// The pass that eliminated it.
    pub pass: String,
}

/// An inline record mapping a call-site variable to its inlined source.
#[derive(Clone, Debug, PartialEq, Eq)]
struct InlineRecord {
    /// The variable at the call site in the optimized code.
    inlined_var: VarId,
    /// The declaration that was inlined.
    source_decl: Name,
    /// The variable in the source declaration's body.
    source_var: VarId,
}

/// Maps optimized IR variable IDs back to their source-level origins.
///
/// Supports direct origin lookups and chained lookups that follow rename
/// chains to their ultimate source. Also tracks variable eliminations and
/// inline expansions.
#[derive(Clone, Debug, Default)]
pub struct BackTranslationMap {
    /// Direct mapping from optimized VarId to its source origin.
    origins: HashMap<VarId, SourceOrigin>,
    /// Rename chains: maps new VarId -> old VarId, enabling chain traversal.
    rename_chains: HashMap<VarId, VarId>,
    /// Inline records for tracing through inlined function boundaries.
    inline_records: Vec<InlineRecord>,
    /// Eliminated variables with reasons.
    eliminations: Vec<EliminationRecord>,
}

impl BackTranslationMap {
    /// Create an empty back-translation map.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record that `optimized` originated from `origin`.
    pub fn record(&mut self, optimized: VarId, origin: SourceOrigin) {
        self.origins.insert(optimized, origin);
    }

    /// Record an inline expansion: `inlined_var` in the current code came from
    /// `source_var` inside `source_decl`.
    ///
    /// This creates both an inline record (for diagnostics) and a source origin
    /// entry so that `lookup` can resolve the inlined variable.
    pub fn record_inline(&mut self, inlined_var: VarId, source_decl: Name, source_var: VarId) {
        self.inline_records.push(InlineRecord {
            inlined_var,
            source_decl: source_decl.clone(),
            source_var,
        });
        // Also record as a direct origin so lookup works immediately.
        self.origins.insert(
            inlined_var,
            SourceOrigin {
                decl_name: source_decl,
                var_name: None,
                pass: String::from("inline"),
            },
        );
    }

    /// Look up the immediate source origin of `var`.
    ///
    /// Returns `None` if no origin has been recorded for this variable.
    #[must_use]
    pub fn lookup(&self, var: VarId) -> Option<&SourceOrigin> {
        self.origins.get(&var)
    }

    /// Merge another map into this one.
    ///
    /// Entries from `other` overwrite entries in `self` for the same VarId.
    /// Rename chains, inline records, and eliminations are all merged.
    pub fn merge(&mut self, other: BackTranslationMap) {
        self.origins.extend(other.origins);
        self.rename_chains.extend(other.rename_chains);
        self.inline_records.extend(other.inline_records);
        self.eliminations.extend(other.eliminations);
    }

    /// Follow rename chains to collect all source origins reachable from `var`.
    ///
    /// Returns origins in chain order: the first element is the immediate origin
    /// of `var`, and subsequent elements trace further back through renames.
    /// Returns an empty vec if `var` has no recorded origin.
    ///
    /// Chain traversal is bounded to prevent infinite loops from cyclic renames
    /// (which should not occur in well-formed optimization output but are
    /// defended against).
    #[must_use]
    pub fn chain_lookup(&self, var: VarId) -> Vec<&SourceOrigin> {
        let mut result = Vec::new();
        let mut current = var;
        // Bound: no chain should exceed the total number of rename entries.
        let max_depth = self.rename_chains.len() + 1;

        for _ in 0..max_depth {
            if let Some(origin) = self.origins.get(&current) {
                result.push(origin);
            }
            match self.rename_chains.get(&current) {
                Some(&prev) if prev != current => current = prev,
                _ => break,
            }
        }

        result
    }

    /// Return the number of recorded origins.
    #[must_use]
    pub fn origin_count(&self) -> usize {
        self.origins.len()
    }

    /// Return the number of recorded eliminations.
    #[must_use]
    pub fn elimination_count(&self) -> usize {
        self.eliminations.len()
    }

    /// Iterate over all elimination records.
    pub fn eliminations(&self) -> &[EliminationRecord] {
        &self.eliminations
    }

    /// Check whether a variable was eliminated.
    #[must_use]
    pub fn is_eliminated(&self, var: VarId) -> bool {
        self.eliminations.iter().any(|e| e.var == var)
    }
}

/// Builder that tracks transformations during an optimization pass.
///
/// Each optimization pass creates a `PassTracer` at the start, records
/// transformations as they happen, and calls [`into_map`](PassTracer::into_map)
/// at the end to produce a [`BackTranslationMap`] for that pass.
#[derive(Clone, Debug)]
pub struct PassTracer {
    pass_name: String,
    /// Renames: (old VarId, new VarId).
    renames: Vec<(VarId, VarId)>,
    /// Inline expansions.
    inlines: Vec<(VarId, Name, VarId)>,
    /// Eliminations: (VarId, reason).
    eliminations: Vec<(VarId, String)>,
}

impl PassTracer {
    /// Create a new tracer for the named optimization pass.
    #[must_use]
    pub fn new(pass_name: &str) -> Self {
        Self {
            pass_name: pass_name.to_owned(),
            renames: Vec::new(),
            inlines: Vec::new(),
            eliminations: Vec::new(),
        }
    }

    /// Record a variable rename: `old` was replaced by `new`.
    pub fn trace_rename(&mut self, old: VarId, new: VarId) {
        self.renames.push((old, new));
    }

    /// Record an inline expansion: `call_site` was replaced by the body of
    /// `target_decl`, with `target_var` being the corresponding variable in
    /// the inlined declaration's body.
    pub fn trace_inline(&mut self, call_site: VarId, target_decl: Name, target_var: VarId) {
        self.inlines.push((call_site, target_decl, target_var));
    }

    /// Record that `var` was eliminated (e.g., dead code, constant folded).
    pub fn trace_eliminate(&mut self, var: VarId, reason: &str) {
        self.eliminations.push((var, reason.to_owned()));
    }

    /// Consume the tracer and produce a [`BackTranslationMap`].
    ///
    /// Renames are stored as chain links. Inline expansions create full
    /// origin entries. Eliminations are stored as records.
    #[must_use]
    pub fn into_map(self) -> BackTranslationMap {
        let mut map = BackTranslationMap::new();

        // Record renames as chain links with origin entries on the new var.
        for (old, new) in &self.renames {
            map.rename_chains.insert(*new, *old);
            map.origins.insert(
                *new,
                SourceOrigin {
                    decl_name: Name::anon(),
                    var_name: None,
                    pass: self.pass_name.clone(),
                },
            );
        }

        // Record inline expansions.
        for (call_site, target_decl, target_var) in self.inlines {
            map.record_inline(call_site, target_decl.clone(), target_var);
            // Override the pass name from the generic "inline" to our actual pass.
            if let Some(origin) = map.origins.get_mut(&call_site) {
                origin.pass.clone_from(&self.pass_name);
            }
        }

        // Record eliminations.
        for (var, reason) in self.eliminations {
            map.eliminations.push(EliminationRecord {
                var,
                reason,
                pass: self.pass_name.clone(),
            });
        }

        map
    }

    /// Return the pass name.
    #[must_use]
    pub fn pass_name(&self) -> &str {
        &self.pass_name
    }
}

impl fmt::Display for PassTracer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PassTracer({}: {} renames, {} inlines, {} eliminations)",
            self.pass_name,
            self.renames.len(),
            self.inlines.len(),
            self.eliminations.len(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nm(s: &str) -> Name {
        s.parse().expect("valid name")
    }

    fn origin(decl: &str, var: Option<&str>, pass: &str) -> SourceOrigin {
        SourceOrigin {
            decl_name: nm(decl),
            var_name: var.map(nm),
            pass: pass.to_owned(),
        }
    }

    #[test]
    fn test_source_origin_display() {
        let with_var = origin("Nat.add", Some("x"), "inline");
        let s = format!("{with_var}");
        assert!(s.contains("inline") && s.contains("Nat.add"));

        let without_var = origin("Nat.add", None, "dce");
        let s = format!("{without_var}");
        assert!(s.contains("dce") && s.contains("Nat.add"));
    }

    #[test]
    fn test_map_record_lookup_and_missing() {
        let mut map = BackTranslationMap::new();
        assert_eq!(map.origin_count(), 0);
        assert!(map.lookup(VarId(99)).is_none());

        map.record(VarId(10), origin("List.map", Some("f"), "inline"));
        let found = map.lookup(VarId(10)).expect("should find recorded origin");
        assert_eq!(found.decl_name, nm("List.map"));
        assert_eq!(found.pass, "inline");
    }

    #[test]
    fn test_map_record_inline() {
        let mut map = BackTranslationMap::new();
        map.record_inline(VarId(5), nm("Nat.succ"), VarId(0));

        let o = map.lookup(VarId(5)).expect("should find inlined var");
        assert_eq!(o.decl_name, nm("Nat.succ"));
        assert_eq!(o.pass, "inline");
        assert_eq!(map.origin_count(), 1);
    }

    #[test]
    fn test_map_merge_and_overwrite() {
        let mut a = BackTranslationMap::new();
        a.record(VarId(1), origin("A", None, "p1"));
        let mut b = BackTranslationMap::new();
        b.record(VarId(2), origin("B", None, "p2"));
        b.record(VarId(1), origin("new", None, "p2"));

        a.merge(b);
        assert_eq!(a.origin_count(), 2);
        assert!(a.lookup(VarId(2)).is_some());
        // VarId(1) overwritten by merge
        assert_eq!(a.lookup(VarId(1)).unwrap().decl_name, nm("new"));
    }

    #[test]
    fn test_chain_lookup_follows_renames() {
        let mut map = BackTranslationMap::new();
        map.record(VarId(0), origin("original", Some("x"), "source"));
        map.record(VarId(1), origin("renamed", None, "pass1"));
        map.rename_chains.insert(VarId(1), VarId(0));
        map.record(VarId(2), origin("final", None, "pass2"));
        map.rename_chains.insert(VarId(2), VarId(1));

        let chain = map.chain_lookup(VarId(2));
        assert_eq!(chain.len(), 3);
        assert_eq!(chain[0].decl_name, nm("final"));
        assert_eq!(chain[1].decl_name, nm("renamed"));
        assert_eq!(chain[2].decl_name, nm("original"));

        // Single step and missing
        assert_eq!(map.chain_lookup(VarId(0)).len(), 1);
        assert!(map.chain_lookup(VarId(42)).is_empty());
    }

    #[test]
    fn test_chain_lookup_bounded_on_cycle() {
        let mut map = BackTranslationMap::new();
        map.record(VarId(0), origin("A", None, "p"));
        map.record(VarId(1), origin("B", None, "p"));
        map.rename_chains.insert(VarId(0), VarId(1));
        map.rename_chains.insert(VarId(1), VarId(0));
        // Must terminate despite the cycle.
        assert!(map.chain_lookup(VarId(0)).len() <= 3);
    }

    #[test]
    fn test_pass_tracer_rename_and_inline() {
        let mut tracer = PassTracer::new("cse");
        tracer.trace_rename(VarId(0), VarId(5));
        let map = tracer.into_map();
        assert_eq!(map.lookup(VarId(5)).unwrap().pass, "cse");

        let mut tracer = PassTracer::new("inline");
        tracer.trace_inline(VarId(10), nm("Nat.succ"), VarId(0));
        let map = tracer.into_map();
        let o = map.lookup(VarId(10)).expect("should find inlined var");
        assert_eq!(o.decl_name, nm("Nat.succ"));
        assert_eq!(o.pass, "inline");
    }

    #[test]
    fn test_pass_tracer_eliminate() {
        let mut tracer = PassTracer::new("dce");
        tracer.trace_eliminate(VarId(3), "dead code");
        let map = tracer.into_map();
        assert!(map.is_eliminated(VarId(3)));
        assert!(!map.is_eliminated(VarId(0)));
        assert_eq!(map.eliminations()[0].reason, "dead code");
        assert_eq!(map.eliminations()[0].pass, "dce");
    }

    #[test]
    fn test_pass_tracer_combined_operations() {
        let mut tracer = PassTracer::new("optimize");
        tracer.trace_rename(VarId(0), VarId(1));
        tracer.trace_inline(VarId(2), nm("helper"), VarId(0));
        tracer.trace_eliminate(VarId(3), "constant folded");

        let map = tracer.into_map();
        assert_eq!(map.origin_count(), 2);
        assert_eq!(map.elimination_count(), 1);
        assert!(map.lookup(VarId(1)).is_some());
        assert!(map.lookup(VarId(2)).is_some());
        assert!(map.is_eliminated(VarId(3)));
    }

    #[test]
    fn test_pass_tracer_display_and_name() {
        let mut tracer = PassTracer::new("simp");
        assert_eq!(tracer.pass_name(), "simp");
        tracer.trace_rename(VarId(0), VarId(1));
        tracer.trace_inline(VarId(2), nm("f"), VarId(0));
        tracer.trace_eliminate(VarId(3), "unused");

        let s = format!("{tracer}");
        assert!(s.contains("simp") && s.contains("1 renames"));
        assert!(s.contains("1 inlines") && s.contains("1 eliminations"));
    }

    #[test]
    fn test_merge_preserves_eliminations() {
        let mut a = BackTranslationMap::new();
        a.eliminations.push(EliminationRecord {
            var: VarId(1),
            reason: "dead".into(),
            pass: "dce".into(),
        });
        let mut b = BackTranslationMap::new();
        b.eliminations.push(EliminationRecord {
            var: VarId(2),
            reason: "folded".into(),
            pass: "cf".into(),
        });
        a.merge(b);
        assert_eq!(a.elimination_count(), 2);
        assert!(a.is_eliminated(VarId(1)) && a.is_eliminated(VarId(2)));
    }

    #[test]
    fn test_chain_lookup_through_tracer_renames() {
        let mut t1 = PassTracer::new("pass1");
        t1.trace_rename(VarId(0), VarId(1));
        let mut combined = t1.into_map();

        let mut t2 = PassTracer::new("pass2");
        t2.trace_rename(VarId(1), VarId(2));
        combined.merge(t2.into_map());

        combined.record(VarId(0), origin("root", Some("x"), "source"));
        let chain = combined.chain_lookup(VarId(2));
        assert_eq!(chain.len(), 3);
        assert_eq!(chain[2].decl_name, nm("root"));
    }
}
