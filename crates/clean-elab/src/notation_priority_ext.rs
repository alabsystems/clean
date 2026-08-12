// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended notation-priority analysis, diagnostics, and namespace-aware resolution.

pub(crate) use super::notation_priority::{
    Associativity, MixfixPattern, NotationPriority, PriorityConflict, PriorityEntry,
    PriorityResolver,
};

// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
#[path = "notation_priority_ext_detail.rs"]
mod detail;

#[cfg(test)]
pub(crate) use detail::{
    analyze_priority_conflicts, build_priority_lattice, conflicts_to_diagnostics,
    disambiguate_by_priority, patterns_overlap, ExtendedConflict, ExtendedPriorityResolver,
    NamespacePriorityOverride, PriorityConflictKind, PriorityLattice, PriorityResolutionError,
};
