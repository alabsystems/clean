// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Imported match-compiler metadata. This guides frontend reduction only;
//! it is not a declaration, a proof, or permission to skip kernel checking.

use super::{
    ConstantKind, EnvExtensionEntry, EnvExtensionEntryData, Environment,
    PersistentEnvExtensionState,
};
use crate::serde_budget::{with_decode_resource_limits, DecodeResourceLimits};
use crate::{ExprKind, Name};
use hashbrown::HashMap;
use serde::{Deserialize, Serialize};

/// Matcher fields used by reduction, with optional recent Lean metadata.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MatcherInfo {
    /// Parameters preceding the motive.
    pub num_params: u32,
    /// Discriminants following the motive.
    pub num_discrs: u32,
    /// Number of arguments supplied to each selected alternative.
    pub alt_num_params: Vec<u32>,
    /// Index of the elimination universe, absent for Prop-only elimination.
    pub u_elim_pos: Option<u32>,
    /// Optional names of the discriminant equations.
    pub discr_names: Vec<Option<Name>>,
    /// Recent Lean preserves alternative structure and the overlap graph.
    /// Lean 4.8 supplies only the already computed alternative arities.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub details: Option<MatcherDetails>,
}

/// The alternative information and overlaps written by recent Lean compilers.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct MatcherDetails {
    /// Field, overlap-assumption and unit-thunk counts for each alternative.
    pub alt_infos: Vec<MatcherAltInfo>,
    /// Rows and their targets are sorted and contain no duplicates.
    pub overlaps: Vec<MatcherOverlap>,
}

/// Structure of one match compiler alternative.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct MatcherAltInfo {
    /// Constructor fields, excluding named discriminant equations.
    pub num_fields: u32,
    /// Overlap assumptions, used by splitter alternatives.
    pub num_overlaps: u32,
    /// Whether Lean supplies an artificial Unit argument.
    pub has_unit_thunk: bool,
}

/// Alternatives overlapping a given alternative.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MatcherOverlap {
    /// Alternative whose overlapping predecessors are recorded.
    pub alternative: u32,
    /// Distinct overlapping alternative indices, in ascending order.
    pub overlapping: Vec<u32>,
}

impl MatcherDetails {
    /// Reproduce Lean's alternative arities without truncation or overflow.
    pub fn alt_num_params(&self, num_discr_eqs: u32) -> Option<Vec<u32>> {
        self.alt_infos
            .iter()
            .map(|info| {
                info.num_fields
                    .checked_add(info.num_overlaps)?
                    .checked_add(u32::from(info.has_unit_thunk))?
                    .checked_add(num_discr_eqs)
            })
            .collect()
    }
}

impl MatcherInfo {
    /// Number of arguments required before matcher reduction can select an arm.
    pub fn arity(&self) -> Option<usize> {
        usize::try_from(self.num_params)
            .ok()?
            .checked_add(1)?
            .checked_add(usize::try_from(self.num_discrs).ok()?)?
            .checked_add(self.alt_num_params.len())
    }
}

const STORAGE_KEY: &str = "Clean.matcherInfo.v1";
const PAYLOAD_PREFIX: &[u8] = b"Clean.matcherInfo.v1\0";
const MAX_PAYLOAD_BYTES: usize = 1 << 20;
const MAX_BINDERS: usize = 100_000;
/// Every decoded node and nesting level costs at least one payload byte, so
/// a payload within [`MAX_PAYLOAD_BYTES`] cannot exhaust this budget.
const PAYLOAD_DECODE_LIMITS: DecodeResourceLimits = DecodeResourceLimits {
    max_nodes: MAX_PAYLOAD_BYTES,
    max_depth: MAX_PAYLOAD_BYTES,
};

/// The persistent extension that stores matcher metadata, the storage
/// [`MatcherIndex`] is derived from.
pub(super) fn matcher_storage_key() -> Name {
    Name::from_string(STORAGE_KEY)
}

/// Whether `extension` is [`matcher_storage_key`].
pub(super) fn is_matcher_storage(extension: &Name) -> bool {
    *extension == matcher_storage_key()
}

fn decode_entry(entry: &EnvExtensionEntry) -> Option<MatcherInfo> {
    let EnvExtensionEntryData::Object(bytes) = &entry.data else {
        return None;
    };
    if bytes.len() > MAX_PAYLOAD_BYTES {
        return None;
    }
    let payload = bytes.strip_prefix(PAYLOAD_PREFIX)?;
    // A decode is a function of these bytes alone. Its own budget scope keeps
    // an enclosing one (a restore that runs inside a bounded decode) from
    // counting it or changing its answer.
    let value: MatcherInfo = with_decode_resource_limits(PAYLOAD_DECODE_LIMITS, || {
        serde_json::from_slice(payload).ok()
    })?;
    if serde_json::to_vec(&value).ok()?.as_slice() != payload {
        return None;
    }
    validate_details(&value).ok()?;
    Some(value)
}

/// The decoded matcher storage, by constant name: `Some(info)` when every
/// stored entry for the name decodes to `info`, `None` when any of them is
/// malformed or two disagree.
///
/// Plain data, never a lazily filled cell (`docs/DECISIONS.md`, 2026-11-15,
/// "No lazily filled cell for the matcher index" and "The matcher index lives
/// in its storage"). It lives inside the storage it
/// is derived from, [`super::extension_storage::PersistentExtensions`], whose
/// constructors and mutators keep it equal to [`MatcherIndex::decode`] of that
/// storage. Never serialized: the entries are the persisted form.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct MatcherIndex(HashMap<Name, Option<MatcherInfo>>);

impl MatcherIndex {
    /// Fold one stored entry in. A name ends at `Some(info)` exactly when
    /// every entry for it decodes to `info`, whatever order the entries come
    /// in, so an append at any module index keeps the index equal to a
    /// decode of the whole storage.
    pub(super) fn absorb(&mut self, entry: &EnvExtensionEntry) {
        let decoded = decode_entry(entry);
        self.0
            .entry(entry.name.clone())
            .and_modify(|previous| {
                if previous != &decoded {
                    *previous = None;
                }
            })
            .or_insert(decoded);
    }

    /// Decode a whole storage state.
    pub(super) fn decode(storage: Option<&PersistentEnvExtensionState>) -> Self {
        let mut index = Self::default();
        for entry in storage
            .into_iter()
            .flat_map(|state| state.imported_entries.iter().flatten())
        {
            index.absorb(entry);
        }
        index
    }

    /// The row for `name`: absent when no entry names it, `Some(None)` when
    /// its entries are malformed or disagree.
    pub(super) fn row(&self, name: &Name) -> Option<&Option<MatcherInfo>> {
        self.0.get(name)
    }

    /// The metadata every stored entry for `name` agrees on, if any.
    pub(super) fn lookup(&self, name: &Name) -> Option<&MatcherInfo> {
        self.0.get(name)?.as_ref()
    }

    /// Drop `name`'s row, once its storage holds no entry for it.
    pub(super) fn remove(&mut self, name: &Name) {
        self.0.remove(name);
    }
}

// These declaration-independent checks run at admission or index decoding,
// never once per simplifier lookup. Indexed values are borrowed immutably.
fn validate_details(info: &MatcherInfo) -> Result<(), &'static str> {
    if let Some(details) = &info.details {
        let equations = u32::try_from(info.discr_names.iter().filter(|n| n.is_some()).count())
            .map_err(|_| "matcher equation count exceeds u32")?;
        if details.alt_num_params(equations).as_ref() != Some(&info.alt_num_params) {
            return Err("matcher alternative details disagree with their arities");
        }
        let mut previous = None;
        let mut links = 0_usize;
        for row in &details.overlaps {
            if row.alternative as usize >= details.alt_infos.len()
                || previous.is_some_and(|p| p >= row.alternative)
            {
                return Err("matcher overlap keys are out of range or duplicated");
            }
            previous = Some(row.alternative);
            let mut target = None;
            for &index in &row.overlapping {
                if index >= row.alternative || target.is_some_and(|p| p >= index) {
                    return Err("matcher overlap targets are not distinct ordered predecessors");
                }
                target = Some(index);
                links += 1;
                if links > MAX_BINDERS {
                    return Err("matcher overlap graph exceeds its item bound");
                }
            }
        }
    }
    Ok(())
}

fn validate_info(
    declaration: &super::ConstantInfo,
    info: &MatcherInfo,
) -> Result<(), &'static str> {
    let arity = info
        .arity()
        .filter(|n| *n <= MAX_BINDERS)
        .ok_or("matcher arity exceeds the bounded metadata surface")?;
    if info.discr_names.len() != info.num_discrs as usize
        || info
            .alt_num_params
            .iter()
            .any(|n| *n as usize > MAX_BINDERS)
    {
        return Err("matcher discriminator/alternative metadata is inconsistent");
    }
    if declaration.kind != ConstantKind::Definition || declaration.value.is_none() {
        return Err("matcher target is not a definition with a body");
    }
    if info
        .u_elim_pos
        .is_some_and(|index| index as usize >= declaration.level_params.len())
    {
        return Err("matcher elimination universe is outside its definition");
    }
    let mut ty = &declaration.type_;
    let mut visited = 0;
    for _ in 0..arity {
        // Genuine Lean matchers (for example Classical.em.match_1) can
        // introduce local type aliases between their parameter binders.
        // Count only explicit Pi/let structure; this metadata admission does
        // not evaluate aliases or infer a matcher from a declaration name.
        while let ExprKind::Let(_, _, _, body, _) = ty.kind() {
            visited += 1;
            if visited > MAX_BINDERS {
                return Err("matcher type telescope exceeds its node bound");
            }
            ty = body;
        }
        let ExprKind::Pi(_, _, body) = ty.kind() else {
            return Err("matcher metadata requires more arguments than its definition");
        };
        visited += 1;
        if visited > MAX_BINDERS {
            return Err("matcher type telescope exceeds its node bound");
        }
        ty = body;
    }
    Ok(())
}

impl Environment {
    /// Register measured metadata only against its actual definition.
    /// A duplicate must be identical. Consumers must still reduce the actual
    /// body and check definitional equality; this record grants no authority.
    pub fn register_matcher_info(
        &mut self,
        name: Name,
        info: MatcherInfo,
    ) -> Result<(), &'static str> {
        let declaration = self
            .get_const(&name)
            .ok_or("matcher definition is absent")?;
        validate_info(declaration, &info)?;
        validate_details(&info)?;
        if let Some(previous) = self.persistent_extensions.matcher_index().row(&name) {
            return if previous.as_ref() == Some(&info) {
                Ok(())
            } else {
                Err("conflicting or malformed matcher metadata")
            };
        }
        let payload =
            serde_json::to_vec(&info).map_err(|_| "matcher metadata serialization failed")?;
        if payload.len() + PAYLOAD_PREFIX.len() > MAX_PAYLOAD_BYTES {
            return Err("matcher metadata payload exceeds its byte bound");
        }
        let mut bytes = PAYLOAD_PREFIX.to_vec();
        bytes.extend(payload);
        // The append indexes the entry like any other: it decodes to `info`.
        let key = matcher_storage_key();
        self.register_persistent_extension(key.clone());
        self.add_persistent_extension_entries(
            &key,
            0,
            vec![EnvExtensionEntry {
                name,
                data: EnvExtensionEntryData::Object(bytes),
            }],
        );
        self.generation += 1;
        Ok(())
    }

    /// Read metadata explicitly registered for this exact constant name.
    pub fn get_matcher_info(&self, name: &Name) -> Option<&MatcherInfo> {
        let info = self.persistent_extensions.matcher_info(name)?;
        let declaration = self.get_const(name)?;
        validate_info(declaration, info).ok()?;
        Some(info)
    }

    /// Drop the matcher metadata stored for a removed constant, with its
    /// index row.
    pub(super) fn forget_matcher_info(&mut self, name: &Name) {
        self.persistent_extensions.forget_matcher_rows(name);
    }
}

#[cfg(test)]
#[path = "matcher_tests.rs"]
mod tests;
