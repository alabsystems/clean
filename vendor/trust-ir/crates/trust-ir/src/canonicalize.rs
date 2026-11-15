// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared planning for TrustIR's canonical function body form.
//!
//! D1a: canonical value ids are handed out from the exact range
//! `0..=u32::MAX`, never by a counter that could wrap, and the block walk reads
//! through iterators and slice patterns, never an index.

#![cfg_attr(
    not(test),
    deny(
        clippy::panic,
        clippy::unwrap_used,
        clippy::expect_used,
        clippy::indexing_slicing,
        clippy::arithmetic_side_effects,
        clippy::cast_possible_truncation
    )
)]

use std::collections::HashMap;
use std::collections::hash_map::Entry;

#[cfg(feature = "fmt")]
use crate::mem2reg::rewrite_node;
use crate::proof::ProofObligation;
#[cfg(feature = "fmt")]
use crate::proof::{ClausePlace, ProofFormula};
use crate::value::{FuncId, ValueId};
use crate::{Block, Function, ParamAttrs};

/// Borrowed canonicalization metadata shared by materializing and streaming
/// consumers. One plan is proportional to its function. A projected module
/// may retain plans for multiple non-identity functions, so its total retained
/// scratch is the sum of those fallback plans; identity functions need none.
pub(crate) struct FunctionCanonicalPlan {
    pub(crate) block_order: Vec<usize>,
    pub(crate) value_map: HashMap<ValueId, ValueId>,
    /// The number of distinct definitions: after the rewrite the function
    /// defines exactly `0..defined_count`.
    pub(crate) defined_count: u32,
    pub(crate) param_attrs_len: usize,
    pub(crate) preserve_source_provenance: bool,
}

impl FunctionCanonicalPlan {
    /// Return no plan when the existing function can be emitted through the
    /// raw borrowed walk with exactly the bytes legacy canonicalization would
    /// produce. The check is allocation-free and deliberately conservative;
    /// uncertain or genuinely non-canonical inputs use the full plan.
    pub(crate) fn new_if_needed(func: &Function) -> Option<Self> {
        (!has_identity_canonical_form(func)).then(|| Self::new(func))
    }

    pub(crate) fn new(func: &Function) -> Self {
        let mut ordered: Vec<(usize, &Block)> = func.blocks.iter().enumerate().collect();
        ordered.sort_by_key(|(_, block)| block.id.index());
        let block_order: Vec<usize> = ordered.iter().map(|&(index, _)| index).collect();

        // Dense ids, handed out at the first sight of each value. A key is a
        // `ValueId`, so there are at most 2^32 distinct keys, and the range
        // holds exactly 2^32 ids: it cannot run out, and the `None` arm
        // (which would leave the value unmapped) is unreachable. No counter
        // is incremented, so none can wrap.
        let mut value_map = HashMap::new();
        let mut dense = 0..=u32::MAX;

        // Canonical definitions are block parameters first, followed by
        // instruction results. Duplicate definitions retain the first ID.
        let params = ordered
            .iter()
            .flat_map(|(_, block)| block.params.iter().map(|(value, _)| *value));
        let results = ordered
            .iter()
            .flat_map(|(_, block)| block.body.iter())
            .flat_map(|node| node.results.iter().copied());
        for value in params.chain(results) {
            if let Entry::Vacant(slot) = value_map.entry(value)
                && let Some(id) = dense.next()
            {
                slot.insert(ValueId::new(id));
            }
        }
        // The first id not handed out is the count of distinct definitions.
        // When all 2^32 were handed out, every `ValueId` is defined, so no
        // binding dangles and `map_binding_value` never reads the count;
        // `u32::MAX` stands for it there.
        let defined_count = dense.next().unwrap_or(u32::MAX);

        // The prefix of `attrs.params` that ends at the last non-empty entry.
        let mut kept = func.attrs.params.as_slice();
        while let Some((last, rest)) = kept.split_last()
            && last.is_empty()
        {
            kept = rest;
        }
        let param_attrs_len = kept.len();
        let block_order_changed = block_order
            .iter()
            .enumerate()
            .any(|(canonical, &original)| canonical != original);
        let values_changed = value_map.iter().any(|(from, to)| from != to);
        let canonicalization_changed =
            block_order_changed || values_changed || param_attrs_len != func.attrs.params.len();

        // The legacy canonicalizer compared the transformed function (with
        // provenance temporarily removed) using derived PartialEq. Preserve
        // its exact non-reflexive-float behavior: NaN in BoundedOutput or a
        // dialect F64 attribute makes `func == func` false and drops the
        // carrier even when no structural rewrite is otherwise needed.
        let preserve_source_provenance =
            !canonicalization_changed && legacy_self_equality_holds(func);

        Self {
            block_order,
            value_map,
            defined_count,
            param_attrs_len,
            preserve_source_provenance,
        }
    }

    pub(crate) fn map_value(&self, value: ValueId) -> ValueId {
        self.value_map.get(&value).copied().unwrap_or(value)
    }

    /// Where a `ClausePlace::Value(value)` binding lands (roadmap WS4.4,
    /// NEW-1).
    ///
    /// A value the function DEFINES follows the same dense map as every body
    /// operand, so the binding keeps naming the value it named. A value the
    /// function does NOT define is a dangling binding, which the validator
    /// refuses (`InvalidFunctionSummary` / `InvalidObligationBinding`) — and
    /// it must stay dangling: it is never silently rebound. Leaving it
    /// literally unchanged is not enough, because after renumbering the dense
    /// range `0..defined_count` is fully defined, so a dangling `%1` would
    /// suddenly name whatever value was renumbered to `%1` and the refusal
    /// would vanish. A dangling id inside that range is therefore moved to
    /// `defined_count + id` (never defined after the rewrite), and one at or
    /// above it is left as is (already outside the defined range). On an
    /// already-canonical function no dangling id lies below `defined_count`,
    /// so the map is the identity there and canonicalization stays
    /// idempotent.
    pub(crate) fn map_binding_value(&self, value: ValueId) -> ValueId {
        if let Some(mapped) = self.value_map.get(&value) {
            return *mapped;
        }
        if value.index() < self.defined_count {
            return ValueId::new(self.defined_count.saturating_add(value.index()));
        }
        value
    }

    /// Rewrite every `ClausePlace::Value` binding of `formula` through
    /// [`Self::map_binding_value`].
    #[cfg(feature = "fmt")]
    pub(crate) fn remap_formula_bindings(&self, formula: &mut ProofFormula) {
        for (_, binding) in &mut formula.bindings {
            if let ClausePlace::Value(value) = &mut binding.place {
                *value = self.map_binding_value(*value);
            }
        }
    }
}

/// The function a module obligation's `ClausePlace::Value` bindings resolve
/// against (WS4.4, NEW-1): its `function` scope, else its `site`'s function —
/// the same rule the validator's `InvalidObligationBinding` check uses. `None`
/// for an unscoped obligation, which may bind only `World`.
pub(crate) fn obligation_owner(obligation: &ProofObligation) -> Option<FuncId> {
    obligation
        .function
        .or_else(|| obligation.site.map(|site| site.function))
}

/// `FuncId` -> position in `module.functions`, for every id that names
/// EXACTLY ONE function. A duplicated id is left out: an obligation scoped to
/// it is refused by the validator (`ObligationFunctionScopeUnresolved`), and
/// canonicalization must not pick one of the candidates to remap it against.
pub(crate) fn unique_function_positions<X>(module: &crate::ModuleG<X>) -> HashMap<FuncId, usize> {
    let mut positions: HashMap<FuncId, Option<usize>> = HashMap::new();
    for (index, function) in module.functions.iter().enumerate() {
        positions
            .entry(function.id)
            .and_modify(|slot| *slot = None)
            .or_insert(Some(index));
    }
    positions
        .into_iter()
        .filter_map(|(id, slot)| slot.map(|index| (id, index)))
        .collect()
}

/// Whether canonicalization can use the function exactly as stored.
///
/// The dense-definition scan mirrors `FunctionCanonicalPlan::new`: parameters
/// across all blocks precede instruction results, and repeated definitions
/// retain their first mapping. Once the accepted unique definitions are the
/// dense prefix `0..next`, any smaller ID is necessarily a duplicate whose
/// legacy mapping is already the identity. Undefined uses need no scan because
/// the legacy map leaves every absent ID unchanged.
fn has_identity_canonical_form(func: &Function) -> bool {
    if func
        .blocks
        .windows(2)
        .any(|pair| matches!(pair, [first, second] if first.id.index() > second.id.index()))
    {
        return false;
    }
    if func.attrs.params.last().is_some_and(ParamAttrs::is_empty) {
        return false;
    }

    let mut next = 0_u32;
    for (value, _) in func.blocks.iter().flat_map(|block| &block.params) {
        if !identity_definition(*value, &mut next) {
            return false;
        }
    }
    for value in func
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .flat_map(|node| &node.results)
    {
        if !identity_definition(*value, &mut next) {
            return false;
        }
    }

    // Derived PartialEq is intentionally non-reflexive for NaN-bearing proof
    // annotations and dialect attributes. Legacy canonicalization used that
    // exact comparison to decide whether a present provenance carrier survives.
    func.source_provenance.is_none() || legacy_self_equality_holds(func)
}

fn identity_definition(value: ValueId, next: &mut u32) -> bool {
    match value.index().cmp(next) {
        core::cmp::Ordering::Less => true,
        core::cmp::Ordering::Equal => {
            let Some(after) = next.checked_add(1) else {
                // Preserve the full planner's overflow behavior for the
                // theoretical 2^32-distinct-definition edge case.
                return false;
            };
            *next = after;
            true
        }
        core::cmp::Ordering::Greater => false,
    }
}

fn legacy_self_equality_holds(func: &Function) -> bool {
    PartialEq::eq(func, func)
}

/// Apply the shared canonical plan in place.
#[cfg(feature = "fmt")]
pub(crate) fn canonicalize_function(func: &mut Function) {
    let plan = FunctionCanonicalPlan::new(func);
    canonicalize_function_with(func, &plan);
}

/// Apply `plan` (computed from `func` as it is now) in place. Also remaps the
/// `ClausePlace::Value` bindings of the function's own summary clauses (WS4.4,
/// NEW-1); module obligations scoped to it are remapped by the caller, which
/// holds the module.
#[cfg(feature = "fmt")]
pub(crate) fn canonicalize_function_with(func: &mut Function, plan: &FunctionCanonicalPlan) {
    let source_provenance = func.source_provenance.take();

    func.attrs.params.truncate(plan.param_attrs_len);
    func.blocks.sort_by_key(|block| block.id.index());

    for block in &mut func.blocks {
        for (value, _) in &mut block.params {
            *value = plan.map_value(*value);
        }
        for node in &mut block.body {
            rewrite_node(node, &plan.value_map);
        }
    }
    if let Some(names) = &mut func.value_names {
        for (value, _) in names {
            *value = plan.map_value(*value);
        }
    }
    if let Some(summary) = &mut func.summary {
        for clause in summary
            .requires
            .iter_mut()
            .chain(&mut summary.ensures)
            .chain(&mut summary.decreases)
        {
            plan.remap_formula_bindings(clause);
        }
    }

    if plan.preserve_source_provenance {
        func.source_provenance = source_provenance;
    }
}
