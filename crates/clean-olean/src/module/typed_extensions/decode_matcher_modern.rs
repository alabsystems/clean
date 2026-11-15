// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Six-field MatcherInfo measured from Lean 4.35.0 and 4.36.0-rc2.
//! Hash-map buckets and tree-set nodes retain their complete logical contents.

use super::*;
use clean_kernel::env::{MatcherAltInfo, MatcherDetails, MatcherInfo, MatcherOverlap};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

impl Reader<'_, '_> {
    fn matcher_nat(&self, pointer: u64) -> OleanResult<u32> {
        let value = self.nat(pointer)?;
        if value > MAX_ITEMS as u64 {
            return Err(invalid("matcher field exceeds its item bound"));
        }
        u32::try_from(value).map_err(|_| invalid("matcher field exceeds u32"))
    }

    fn matcher_visit(&self) -> OleanResult<()> {
        let remaining = self
            .remaining_items
            .get()
            .checked_sub(1)
            .ok_or_else(|| invalid("total matcher item budget exhausted"))?;
        self.remaining_items.set(remaining);
        Ok(())
    }

    pub(super) fn modern_matcher(&self, pointer: u64) -> OleanResult<TypedExtensionEntry> {
        let entry = self.object(pointer, 0, 2, 0)?;
        let name = self.name(self.field(entry, 0)?)?;
        let info = self.object(self.field(entry, 1)?, 0, 6, 0)?;
        let num_params = self.matcher_nat(self.field(info, 0)?)?;
        let num_discrs = self.matcher_nat(self.field(info, 1)?)?;
        let mut alt_infos = Vec::new();
        for pointer in self.array(self.field(info, 2)?)? {
            self.matcher_visit()?;
            // Two boxed Nats followed by one unboxed Bool byte.
            let alt = self.object(pointer, 0, 2, 1)?;
            let has_unit_thunk = match self.region.bytes_at(alt + 24, 1)?[0] {
                0 => false,
                1 => true,
                _ => return Err(invalid("matcher alternative Bool is not zero or one")),
            };
            alt_infos.push(MatcherAltInfo {
                num_fields: self.matcher_nat(self.field(alt, 0)?)?,
                num_overlaps: self.matcher_nat(self.field(alt, 1)?)?,
                has_unit_thunk,
            });
        }
        let u_elim_pos = self
            .option_nat(self.field(info, 3)?)?
            .map(|value| {
                u32::try_from(value)
                    .ok()
                    .filter(|n| *n as usize <= MAX_ITEMS)
                    .ok_or_else(|| invalid("matcher elimination universe exceeds its bound"))
            })
            .transpose()?;
        // DiscrInfo remains a one-field, unboxed Option Name.
        let discr_names = self
            .array(self.field(info, 4)?)?
            .into_iter()
            .map(|pointer| self.option_name(pointer))
            .collect::<OleanResult<Vec<_>>>()?;
        if discr_names.len() != num_discrs as usize {
            return Err(invalid("matcher discriminant metadata length mismatch"));
        }
        let overlaps = self.matcher_overlaps(self.field(info, 5)?, alt_infos.len())?;
        let details = MatcherDetails {
            alt_infos,
            overlaps,
        };
        let equations = u32::try_from(discr_names.iter().filter(|n| n.is_some()).count())
            .map_err(|_| invalid("matcher equation count exceeds u32"))?;
        let alt_num_params = details
            .alt_num_params(equations)
            .filter(|counts| counts.iter().all(|n| *n as usize <= MAX_ITEMS))
            .ok_or_else(|| invalid("matcher alternative arity exceeds its bound"))?;
        Ok(TypedExtensionEntry::Matcher {
            name,
            info: MatcherInfo {
                num_params,
                num_discrs,
                alt_num_params,
                u_elim_pos,
                discr_names,
                details: Some(details),
            },
        })
    }

    fn matcher_overlaps(
        &self,
        pointer: u64,
        alternatives: usize,
    ) -> OleanResult<Vec<MatcherOverlap>> {
        // Overlaps/HashMap/DHashMap wrappers erase to Raw { size, buckets }.
        let raw = self.object(pointer, 0, 2, 0)?;
        let size = self.matcher_nat(self.field(raw, 0)?)? as usize;
        let buckets = self.array(self.field(raw, 1)?)?;
        if !buckets.len().is_power_of_two() || size > alternatives {
            return Err(invalid("matcher overlap hash-map extent is invalid"));
        }
        let mut rows = BTreeMap::new();
        let mut visited = HashSet::new();
        for (index, mut node) in buckets.iter().copied().enumerate() {
            while node != 1 {
                self.matcher_visit()?;
                if !visited.insert(node) {
                    return Err(invalid("matcher overlap bucket cycle or shared list node"));
                }
                let cons = self.object(node, 1, 3, 0)?;
                let key = self.matcher_nat(self.field(cons, 0)?)?;
                let hash = u64::from(key);
                let fold = hash ^ (hash >> 32);
                let bucket = (fold ^ (fold >> 16)) as usize & (buckets.len() - 1);
                if key as usize >= alternatives || bucket != index {
                    return Err(invalid(
                        "matcher overlap key is out of range or in the wrong bucket",
                    ));
                }
                let values = self.matcher_overlap_set(self.field(cons, 1)?, alternatives)?;
                if values.iter().any(|&target| target >= key) {
                    return Err(invalid(
                        "matcher overlap targets must precede their alternative",
                    ));
                }
                if rows.insert(key, values).is_some() || rows.len() > size {
                    return Err(invalid(
                        "matcher overlap hash-map has duplicate keys or wrong size",
                    ));
                }
                node = self.field(cons, 2)?;
            }
        }
        if rows.len() != size {
            return Err(invalid(
                "matcher overlap hash-map size disagrees with its entries",
            ));
        }
        Ok(rows
            .into_iter()
            .map(|(alternative, overlapping)| MatcherOverlap {
                alternative,
                overlapping,
            })
            .collect())
    }

    fn matcher_overlap_set(&self, pointer: u64, alternatives: usize) -> OleanResult<Vec<u32>> {
        // TreeSet/TreeMap wrappers erase to Impl: inner has five fields;
        // leaf is constructor one, boxed as scalar three.
        enum Visit {
            Node(u64, Option<u32>, Option<u32>),
            Finish(u64, u32, u64, u64),
        }
        let mut pending = vec![Visit::Node(pointer, None, None)];
        let mut visited = HashSet::new();
        let mut sizes = HashMap::new();
        let mut values = BTreeSet::new();
        while let Some(visit) = pending.pop() {
            match visit {
                Visit::Node(3, _, _) => {}
                Visit::Node(pointer, lower, upper) => {
                    self.matcher_visit()?;
                    if !visited.insert(pointer) {
                        return Err(invalid("matcher overlap tree cycle or shared node"));
                    }
                    let node = self.object(pointer, 0, 5, 0)?;
                    let size = self.matcher_nat(self.field(node, 0)?)?;
                    let key = self.matcher_nat(self.field(node, 1)?)?;
                    if key as usize >= alternatives
                        || lower.is_some_and(|n| key <= n)
                        || upper.is_some_and(|n| key >= n)
                        || self.field(node, 2)? != 1
                        || !values.insert(key)
                    {
                        return Err(invalid("matcher overlap tree key/order/unit is invalid"));
                    }
                    let left = self.field(node, 3)?;
                    let right = self.field(node, 4)?;
                    pending.push(Visit::Finish(pointer, size, left, right));
                    pending.push(Visit::Node(right, Some(key), upper));
                    pending.push(Visit::Node(left, lower, Some(key)));
                }
                Visit::Finish(pointer, declared, left, right) => {
                    let count = |p| {
                        if p == 3 {
                            Some(0_u32)
                        } else {
                            sizes.get(&p).copied()
                        }
                    };
                    let actual = count(left)
                        .and_then(|n| n.checked_add(count(right)?))
                        .and_then(|n| n.checked_add(1))
                        .ok_or_else(|| invalid("matcher overlap tree size overflow"))?;
                    if actual != declared {
                        return Err(invalid(
                            "matcher overlap tree size disagrees with its nodes",
                        ));
                    }
                    sizes.insert(pointer, actual);
                }
            }
        }
        Ok(values.into_iter().collect())
    }
}
