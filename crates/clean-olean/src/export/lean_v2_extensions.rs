// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Standard declaration metadata in Lean 4.36's ModuleData entries.

use std::cmp::Ordering;

use clean_kernel::name::NameInner;
use clean_kernel::{ConstantKind, Name};

use super::lean_v2::{LeanV2RegionWriter, LeanV2Value};
use crate::error::{OleanError, OleanResult};

/// Name.quickCmp first compares the entire cached hash, then walks equal
/// kinds from the leaf toward the root. Persisted maps use this same order
/// for their binary searches on import.
pub(super) fn lean_quick_cmp(mut left: &Name, mut right: &Name) -> Ordering {
    let hash = left.lean4_hash().cmp(&right.lean4_hash());
    if hash != Ordering::Equal {
        return hash;
    }
    loop {
        match (left.inner(), right.inner()) {
            (NameInner::Anon, NameInner::Anon) => return Ordering::Equal,
            (NameInner::Anon, _) | (NameInner::Num(..), NameInner::Str(..)) => {
                return Ordering::Less;
            }
            (_, NameInner::Anon) | (NameInner::Str(..), NameInner::Num(..)) => {
                return Ordering::Greater;
            }
            (NameInner::Num(a, av), NameInner::Num(b, bv)) => {
                let order = av.cmp(bv);
                if order != Ordering::Equal {
                    return order;
                }
                (left, right) = (a, b);
            }
            (NameInner::Str(a, av), NameInner::Str(b, bv)) => {
                let order = av.cmp(bv);
                if order != Ordering::Equal {
                    return order;
                }
                (left, right) = (a, b);
            }
        }
    }
}

/// Name.lt orders the contents of each axiom list. Equal constructors
/// compare their parents first. Store the nearest unequal suffix to resolve
/// equal parents without descending through a recursive Rust call stack.
fn lean_name_cmp(mut left: &Name, mut right: &Name) -> Ordering {
    let mut suffix = Ordering::Equal;
    loop {
        let (left_parent, right_parent, order) = match (left.inner(), right.inner()) {
            (NameInner::Anon, NameInner::Anon) => return suffix,
            (NameInner::Anon, _) | (NameInner::Num(..), NameInner::Str(..)) => {
                return Ordering::Less;
            }
            (_, NameInner::Anon) | (NameInner::Str(..), NameInner::Num(..)) => {
                return Ordering::Greater;
            }
            (NameInner::Num(a, av), NameInner::Num(b, bv)) => (a, b, av.cmp(bv)),
            (NameInner::Str(a, av), NameInner::Str(b, bv)) => (a, b, av.cmp(bv)),
        };
        if order != Ordering::Equal {
            suffix = order;
        }
        (left, right) = (left_parent, right_parent);
    }
}

/// Serialize the standard name, axiom, and declaration kind tables for one
/// view. Each view's producer supplies its namespace and declaration scopes,
/// including an explicit empty axiom list where a declaration uses no axioms.
pub(super) fn standard_extensions(
    writer: &mut LeanV2RegionWriter,
    namespaces: &[Name],
    original_kinds: &[(&Name, ConstantKind)],
    axioms: &[(&Name, &[Name])],
) -> OleanResult<Vec<LeanV2Value>> {
    let private_lean = Name::anon().str("_private").str("Lean");
    let mut extensions = Vec::new();
    if !namespaces.is_empty() {
        let mut names: Vec<_> = namespaces.iter().collect();
        names.sort_unstable_by(|a, b| lean_quick_cmp(a, b));
        names.dedup();
        let values = write_name_array(writer, names)?;
        let key = private_lean
            .clone()
            .str("Namespace")
            .num(0)
            .str("Lean")
            .str("namespacesExt");
        extensions.push(write_pair(writer, &key, values)?);
    }
    if !axioms.is_empty() {
        let mut rows: Vec<_> = axioms
            .iter()
            .map(|&(name, axioms)| {
                let mut axioms: Vec<_> = axioms.iter().collect();
                axioms.sort_unstable_by(|a, b| lean_name_cmp(a, b));
                axioms.dedup();
                (name, axioms)
            })
            .collect();
        rows.sort_unstable_by(|a, b| lean_quick_cmp(a.0, b.0));
        check_duplicate_rows(&rows, "axiom dependencies")?;
        rows.dedup();
        let mut entries = Vec::with_capacity(rows.len());
        for (name, axioms) in rows {
            let values = write_name_array(writer, axioms)?;
            entries.push(write_pair(writer, name, values)?);
        }
        let values = writer.write_array(&entries)?;
        let key = private_lean
            .clone()
            .str("Util")
            .str("CollectAxioms")
            .num(0)
            .str("Lean")
            .str("exportedAxiomsExt");
        extensions.push(write_pair(writer, &key, values)?);
    }
    if !original_kinds.is_empty() {
        let mut rows = original_kinds.to_vec();
        rows.sort_unstable_by(|a, b| lean_quick_cmp(a.0, b.0));
        check_duplicate_rows(&rows, "original constant kind")?;
        rows.dedup();
        let mut entries = Vec::with_capacity(rows.len());
        for (name, kind) in rows {
            // Lean.ConstantKind constructor indices, independent of the
            // serialized ConstantInfo and Clean's ConstantKind orders.
            let index = match kind {
                ConstantKind::Definition => 0,
                ConstantKind::Theorem => 1,
                ConstantKind::Axiom => 2,
                ConstantKind::Opaque => 3,
            };
            entries.push(write_pair(writer, name, LeanV2Value::scalar(index)?)?);
        }
        let values = writer.write_array(&entries)?;
        let key = private_lean
            .str("OriginalConstKind")
            .num(0)
            .str("Lean")
            .str("privateConstKindsExt");
        extensions.push(write_pair(writer, &key, values)?);
    }
    Ok(extensions)
}

/// Rows have already been sorted by the typed name. Identical rows can be
/// coalesced. A second value for the same lookup key would be ambiguous.
fn check_duplicate_rows<T: PartialEq>(rows: &[(&Name, T)], table: &str) -> OleanResult<()> {
    for pair in rows.windows(2) {
        if pair[0].0 == pair[1].0 && pair[0].1 != pair[1].1 {
            return Err(OleanError::Region(format!(
                "conflicting Lean {table} entries for {}",
                pair[0].0
            )));
        }
    }
    Ok(())
}

fn write_pair(
    writer: &mut LeanV2RegionWriter,
    name: &Name,
    value: LeanV2Value,
) -> OleanResult<LeanV2Value> {
    let key = writer.write_name(name)?;
    writer.write_constructor(0, &[key, value], &[])
}

fn write_name_array<'a>(
    writer: &mut LeanV2RegionWriter,
    names: impl IntoIterator<Item = &'a Name>,
) -> OleanResult<LeanV2Value> {
    let values = names
        .into_iter()
        .map(|name| writer.write_name(name))
        .collect::<OleanResult<Vec<_>>>()?;
    writer.write_array(&values)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::header::OleanHeader;
    use crate::region::CompactedRegion;

    fn writer() -> LeanV2RegionWriter {
        let bytes =
            include_bytes!("../../../../tests/fixtures/olean/v4.36.0/plain/StablePlain.olean");
        LeanV2RegionWriter::new(&OleanHeader::parse(bytes).unwrap(), 0x10000).unwrap()
    }

    fn field(region: &CompactedRegion<'_>, object: u64, index: usize) -> u64 {
        let offset = region.ptr_to_offset(object).unwrap();
        region.read_u64_at(offset + 8 + 8 * index).unwrap()
    }

    fn array(region: &CompactedRegion<'_>, object: u64) -> Vec<u64> {
        let offset = region.ptr_to_offset(object).unwrap();
        let len = region.read_u64_at(offset + 8).unwrap() as usize;
        (0..len)
            .map(|i| region.read_u64_at(offset + 24 + 8 * i).unwrap())
            .collect()
    }

    fn name(region: &CompactedRegion<'_>, ptr: u64) -> Name {
        region.read_kernel_name_ptr(ptr).unwrap()
    }

    #[test]
    fn standard_extension_words_and_order_follow_lean_436() {
        let alpha = Name::anon().str("Alpha");
        let nested = alpha.clone().str("Nested");
        let zeta = Name::anon().str("Zeta");
        let opaque = nested.clone().str("opaqueNat");
        let uses = nested.clone().str("usesPremises");
        let natural = nested.clone().str("natural");
        let clean = nested.clone().str("cleanProof");
        let left = nested.clone().str("premiseA");
        let right = nested.clone().str("premiseZ");
        let bridge = nested.clone().str("bridge");
        let witness = nested.clone().str("witness");

        let mut writer = writer();
        let entries = standard_extensions(
            &mut writer,
            &[alpha.clone(), zeta.clone(), nested.clone(), alpha.clone()],
            &[
                (&natural, ConstantKind::Definition),
                (&uses, ConstantKind::Theorem),
                (&opaque, ConstantKind::Opaque),
                (&clean, ConstantKind::Theorem),
            ],
            &[
                (&clean, &[]),
                (
                    &uses,
                    &[witness.clone(), right.clone(), left.clone(), bridge.clone()],
                ),
            ],
        )
        .unwrap();
        let bytes = writer
            .finish_ordinary_module(&[], &[], &[], &[], &entries)
            .unwrap();
        let region = CompactedRegion::new(&bytes, 0x10000);
        let root = region.root_ptr().unwrap();
        let entries = array(&region, field(&region, root, 4));
        let private = Name::anon().str("_private").str("Lean");
        let expected_keys = [
            private
                .clone()
                .str("Namespace")
                .num(0)
                .str("Lean")
                .str("namespacesExt"),
            private
                .clone()
                .str("Util")
                .str("CollectAxioms")
                .num(0)
                .str("Lean")
                .str("exportedAxiomsExt"),
            private
                .str("OriginalConstKind")
                .num(0)
                .str("Lean")
                .str("privateConstKindsExt"),
        ];
        let actual_keys: Vec<_> = entries
            .iter()
            .map(|&row| name(&region, field(&region, row, 0)))
            .collect();
        assert_eq!(actual_keys, expected_keys);

        let namespaces: Vec<_> = array(&region, field(&region, entries[0], 1))
            .into_iter()
            .map(|ptr| name(&region, ptr))
            .collect();
        assert_eq!(namespaces, [nested, zeta, alpha]);

        let axioms: Vec<_> = array(&region, field(&region, entries[1], 1))
            .into_iter()
            .map(|row| {
                let dependencies = array(&region, field(&region, row, 1))
                    .into_iter()
                    .map(|ptr| name(&region, ptr))
                    .collect::<Vec<_>>();
                (name(&region, field(&region, row, 0)), dependencies)
            })
            .collect();
        assert_eq!(
            axioms,
            [
                (uses.clone(), vec![bridge, left, right, witness]),
                (clean.clone(), vec![]),
            ]
        );

        let kinds: Vec<_> = array(&region, field(&region, entries[2], 1))
            .into_iter()
            .map(|row| {
                (
                    name(&region, field(&region, row, 0)),
                    field(&region, row, 1),
                )
            })
            .collect();
        assert_eq!(kinds, [(opaque, 7), (uses, 3), (natural, 1), (clean, 3)]);
    }

    #[test]
    fn leaf_constructor_controls_lean_axiom_list_order() {
        let left = Name::anon().str("z").num(9);
        let right = Name::anon().str("a").str("a");
        assert_eq!(lean_name_cmp(&left, &right), Ordering::Less);
    }

    #[test]
    fn conflicting_metadata_cannot_be_serialized() {
        let name = Name::anon().str("sample");
        assert!(standard_extensions(
            &mut writer(),
            &[],
            &[
                (&name, ConstantKind::Definition),
                (&name, ConstantKind::Theorem)
            ],
            &[],
        )
        .is_err());
        assert!(standard_extensions(
            &mut writer(),
            &[],
            &[],
            &[(&name, &[]), (&name, std::slice::from_ref(&name))],
        )
        .is_err());
    }
}
