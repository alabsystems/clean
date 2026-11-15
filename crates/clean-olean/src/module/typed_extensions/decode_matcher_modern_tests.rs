// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const FIXTURES: [(&[u8], &str); 2] = [
    (
        include_bytes!(
            "../../../../../tests/fixtures/olean/v4.35.0/matcher-metadata/MatcherParity.olean"
        ),
        include_str!("../../../../../tests/fixtures/olean/v4.35.0/matcher-metadata/oracle.json"),
    ),
    (
        include_bytes!(
            "../../../../../tests/fixtures/olean/v4.36.0-rc2/matcher-metadata/MatcherParity.olean"
        ),
        include_str!(
            "../../../../../tests/fixtures/olean/v4.36.0-rc2/matcher-metadata/oracle.json"
        ),
    ),
];

fn region(bytes: &[u8]) -> CompactedRegion<'_> {
    let header = crate::header::OleanHeader::parse(bytes).unwrap();
    CompactedRegion::new(bytes, header.base_addr)
}

fn reader<'r, 'a>(region: &'r CompactedRegion<'a>) -> Reader<'r, 'a> {
    Reader {
        region,
        layout: region.typed_module_layout().unwrap(),
        legacy: false,
        remaining_items: Cell::new(MAX_TOTAL_ARRAY_ITEMS),
    }
}

fn extension(read: &Reader<'_, '_>) -> u64 {
    let root = read
        .region
        .ptr_to_offset(read.region.root_ptr().unwrap())
        .unwrap();
    read.array(read.field(root, 4).unwrap())
        .unwrap()
        .into_iter()
        .find(|&pointer| {
            let entry = read.region.ptr_to_offset(pointer).unwrap();
            read.name(read.field(entry, 0).unwrap()).unwrap()
                == Name::from_string("Lean.Meta.Match.Extension.extension")
        })
        .unwrap()
}

fn matcher_entry(read: &Reader<'_, '_>, suffix: &str) -> u64 {
    let ext = read.region.ptr_to_offset(extension(read)).unwrap();
    read.array(read.field(ext, 1).unwrap())
        .unwrap()
        .into_iter()
        .find(|&pointer| {
            let entry = read.region.ptr_to_offset(pointer).unwrap();
            read.name(read.field(entry, 0).unwrap()).unwrap()
                == Name::from_string(&format!("MatcherParity.{suffix}"))
        })
        .unwrap()
}

#[test]
fn modern_matcher_metadata_matches_both_independent_native_oracles() {
    for (bytes, oracle) in FIXTURES {
        let region = region(bytes);
        let read = reader(&region);
        assert_eq!(read.layout, TypedModuleLayout::LeanV2);
        let ext = read.extension(extension(&read)).unwrap();
        assert_eq!(ext.source_rows, Some(4));
        assert_eq!(ext.undecoded_entries, 0);
        let oracle: serde_json::Value = serde_json::from_str(oracle).unwrap();
        for expected in oracle.as_array().unwrap() {
            let name = Name::from_string(&format!(
                "MatcherParity.{}",
                expected["name"].as_str().unwrap()
            ));
            let actual = ext.entries.iter().find_map(|row| match row {
                TypedExtensionEntry::Matcher { name: found, info } if found == &name => Some(info),
                _ => None,
            });
            if expected["registered"] == false {
                assert!(actual.is_none());
                continue;
            }
            let info = actual.unwrap();
            assert_eq!(
                serde_json::to_value(info.num_params).unwrap(),
                expected["numParams"]
            );
            assert_eq!(
                serde_json::to_value(info.num_discrs).unwrap(),
                expected["numDiscrs"]
            );
            assert_eq!(
                serde_json::to_value(&info.alt_num_params).unwrap(),
                expected["altNumParams"]
            );
            assert_eq!(
                serde_json::to_value(info.u_elim_pos).unwrap(),
                expected["uElimPos"]
            );
            let names: Vec<_> = info
                .discr_names
                .iter()
                .map(|n| n.as_ref().map(ToString::to_string))
                .collect();
            assert_eq!(serde_json::to_value(names).unwrap(), expected["discrNames"]);
            let details = info.details.as_ref().unwrap();
            assert_eq!(
                serde_json::to_value(&details.alt_infos).unwrap(),
                expected["altInfos"]
            );
            assert_eq!(
                serde_json::to_value(&details.overlaps).unwrap(),
                expected["overlaps"]
            );
        }
    }
}

fn write_pointer(bytes: &mut [u8], offset: usize, pointer: u64) {
    bytes[offset..offset + 8].copy_from_slice(&pointer.to_le_bytes());
}

#[test]
fn modern_matcher_metadata_refuses_malformed_alternatives_maps_and_trees() {
    for (original, _) in FIXTURES {
        let compacted = region(original);
        let read = reader(&compacted);
        let entry = matcher_entry(&read, "chooseOverlap.match_1");
        let entry_at = compacted.ptr_to_offset(entry).unwrap();
        let info = compacted
            .ptr_to_offset(read.field(entry_at, 1).unwrap())
            .unwrap();
        let alts = read.array(read.field(info, 2).unwrap()).unwrap();
        let alt = compacted.ptr_to_offset(alts[0]).unwrap();
        let map = compacted
            .ptr_to_offset(read.field(info, 5).unwrap())
            .unwrap();
        let buckets = read.field(map, 1).unwrap();
        let buckets_at = compacted.ptr_to_offset(buckets).unwrap();
        let nodes = read.array(buckets).unwrap();
        let cons_pointer = nodes.iter().copied().find(|p| *p != 1).unwrap();
        let cons = compacted.ptr_to_offset(cons_pointer).unwrap();
        let tree_pointer = read.field(cons, 1).unwrap();
        let tree = compacted.ptr_to_offset(tree_pointer).unwrap();
        // Select row 1 explicitly: its singleton tree encodes predecessor 0.
        // Changing only that key preserves every representation invariant.
        let predecessor_tree = nodes
            .iter()
            .copied()
            .find_map(|mut pointer| {
                while pointer != 1 {
                    let node = compacted.ptr_to_offset(pointer).unwrap();
                    if read.field(node, 0).unwrap() == 3 {
                        return Some(
                            compacted
                                .ptr_to_offset(read.field(node, 1).unwrap())
                                .unwrap(),
                        );
                    }
                    pointer = read.field(node, 2).unwrap();
                }
                None
            })
            .unwrap();
        assert_eq!(read.field(predecessor_tree, 1).unwrap(), 1);
        for target in [1_u64, 2] {
            let mut changed = original.to_vec();
            write_pointer(&mut changed, predecessor_tree + 16, 2 * target + 1);
            let changed_region = region(&changed);
            let changed_read = reader(&changed_region);
            assert!(
                changed_read.modern_matcher(entry).is_err(),
                "self/forward target {target}"
            );
            let extension = changed_read.extension(extension(&changed_read)).unwrap();
            assert!(extension.undecoded_entries > 0);
            assert!(!extension.entries.iter().any(|row| matches!(row,
                TypedExtensionEntry::Matcher { name, .. }
                if name == &Name::from_string("MatcherParity.chooseOverlap.match_1"))));
        }
        let mutations = [
            (info + 6, vec![5]),
            (alt + 6, vec![3]),
            (alt + 24, vec![2]),
            (map + 8, 1_u64.to_le_bytes().to_vec()),
            (cons + 24, cons_pointer.to_le_bytes().to_vec()),
            (tree + 8, 199_u64.to_le_bytes().to_vec()),
            (tree + 16, 199_u64.to_le_bytes().to_vec()),
            (tree + 24, 3_u64.to_le_bytes().to_vec()),
            (tree + 32, tree_pointer.to_le_bytes().to_vec()),
            (tree + 32, 1_u64.to_le_bytes().to_vec()),
        ];
        for (offset, replacement) in mutations {
            let mut changed = original.to_vec();
            changed[offset..offset + replacement.len()].copy_from_slice(&replacement);
            assert!(
                reader(&region(&changed)).modern_matcher(entry).is_err(),
                "mutation at {offset}"
            );
        }
        let mut changed = original.to_vec();
        let index = nodes.iter().position(|p| *p == cons_pointer).unwrap();
        write_pointer(&mut changed, buckets_at + 24, cons_pointer);
        write_pointer(&mut changed, buckets_at + 24 + index * 8, 1);
        assert!(
            reader(&region(&changed)).modern_matcher(entry).is_err(),
            "wrong hash bucket"
        );
    }
}

#[test]
fn modern_matcher_metadata_charges_the_shared_item_budget() {
    let region = region(FIXTURES[0].0);
    let read = reader(&region);
    let entry = matcher_entry(&read, "chooseOverlap.match_1");
    read.remaining_items.set(0);
    assert!(read.modern_matcher(entry).is_err());
}

#[test]
fn modern_matcher_metadata_matches_large_native_overlap_graphs() {
    const LARGE_FIXTURES: [(&[u8], &str); 2] = [
        (
            include_bytes!("../../../../../tests/fixtures/olean/v4.35.0/matcher-metadata-large/LargeMatcher.olean"),
            include_str!("../../../../../tests/fixtures/olean/v4.35.0/matcher-metadata-large/oracle.json"),
        ),
        (
            include_bytes!("../../../../../tests/fixtures/olean/v4.36.0-rc2/matcher-metadata-large/LargeMatcher.olean"),
            include_str!("../../../../../tests/fixtures/olean/v4.36.0-rc2/matcher-metadata-large/oracle.json"),
        ),
    ];

    // Compare every genuine native tree node, including its actual stored size.
    // This also ensures that the large fixture still exercises branching trees.
    fn native_tree(read: &Reader<'_, '_>, pointer: u64, expected: &serde_json::Value) -> Vec<u32> {
        match expected["kind"].as_str().unwrap() {
            "leaf" => {
                assert_eq!(pointer, 3);
                Vec::new()
            }
            "inner" => {
                let node = read.object(pointer, 0, 5, 0).unwrap();
                let size = read.nat(read.field(node, 0).unwrap()).unwrap();
                let key = u32::try_from(read.nat(read.field(node, 1).unwrap()).unwrap()).unwrap();
                assert_eq!(size, expected["size"].as_u64().unwrap());
                assert_eq!(u64::from(key), expected["key"].as_u64().unwrap());
                assert_eq!(read.field(node, 2).unwrap(), 1);
                let mut values = native_tree(read, read.field(node, 3).unwrap(), &expected["left"]);
                values.push(key);
                values.extend(native_tree(
                    read,
                    read.field(node, 4).unwrap(),
                    &expected["right"],
                ));
                assert_eq!(size as usize, values.len());
                values
            }
            kind => panic!("unexpected genuine native tree kind {kind}"),
        }
    }

    for (bytes, oracle) in LARGE_FIXTURES {
        let compacted = region(bytes);
        let read = reader(&compacted);
        assert_eq!(read.layout, TypedModuleLayout::LeanV2);
        let extension_pointer = extension(&read);
        let ext = read.extension(extension_pointer).unwrap();
        let oracle: serde_json::Value = serde_json::from_str(oracle).unwrap();
        let expected_rows = oracle.as_array().unwrap();
        assert_eq!(
            expected_rows
                .iter()
                .map(|row| row["name"].as_str().unwrap())
                .collect::<Vec<_>>(),
            ["crossSparse", "crossSparseEq", "disjoint", "ordinary"]
        );
        assert_eq!(ext.source_rows, Some(3));
        assert_eq!(ext.undecoded_entries, 0);
        assert_eq!(ext.entries.len(), 3);
        let extension_at = compacted.ptr_to_offset(extension_pointer).unwrap();
        let wire_rows = read.array(read.field(extension_at, 1).unwrap()).unwrap();
        for expected in expected_rows {
            let label = expected["name"].as_str().unwrap();
            let name = Name::from_string(&format!("LargeMatcher.{label}.match_1"));
            let found: Vec<_> = ext
                .entries
                .iter()
                .filter_map(|row| match row {
                    TypedExtensionEntry::Matcher { name: actual, info } if actual == &name => {
                        Some(info)
                    }
                    _ => None,
                })
                .collect();
            if expected["registered"] == false {
                assert_eq!(label, "ordinary");
                assert!(found.is_empty());
                continue;
            }
            assert_eq!(expected["registered"], true);
            assert_eq!(found.len(), 1);
            let info = found[0];
            assert_eq!(
                serde_json::to_value(info.num_params).unwrap(),
                expected["numParams"]
            );
            assert_eq!(
                serde_json::to_value(info.num_discrs).unwrap(),
                expected["numDiscrs"]
            );
            assert_eq!(
                serde_json::to_value(&info.alt_num_params).unwrap(),
                expected["altNumParams"]
            );
            assert_eq!(
                serde_json::to_value(info.u_elim_pos).unwrap(),
                expected["uElimPos"]
            );
            let discr_names: Vec<_> = info
                .discr_names
                .iter()
                .map(|n| n.as_ref().map(ToString::to_string))
                .collect();
            assert_eq!(
                serde_json::to_value(discr_names).unwrap(),
                expected["discrNames"]
            );
            let details = info.details.as_ref().unwrap();
            assert_eq!(
                serde_json::to_value(&details.alt_infos).unwrap(),
                expected["altInfos"]
            );
            // HashMap enumeration is not the reader's sorted overlap-row order.
            // Sort only the expected view; retain the exact native oracle bytes.
            let mut overlaps = expected["overlaps"].as_array().unwrap().clone();
            overlaps.sort_by_key(|row| row["alternative"].as_u64().unwrap());
            assert_eq!(
                serde_json::to_value(&details.overlaps).unwrap(),
                serde_json::Value::Array(overlaps)
            );

            let entry = *wire_rows
                .iter()
                .find(|&&pointer| {
                    let entry = compacted.ptr_to_offset(pointer).unwrap();
                    read.name(read.field(entry, 0).unwrap()).unwrap() == name
                })
                .unwrap();
            let entry_at = compacted.ptr_to_offset(entry).unwrap();
            let raw_info = read
                .object(read.field(entry_at, 1).unwrap(), 0, 6, 0)
                .unwrap();
            let raw_map = read
                .object(read.field(raw_info, 5).unwrap(), 0, 2, 0)
                .unwrap();
            assert_eq!(
                read.nat(read.field(raw_map, 0).unwrap()).unwrap(),
                expected["rawSize"].as_u64().unwrap()
            );
            let buckets = read.array(read.field(raw_map, 1).unwrap()).unwrap();
            assert_eq!(
                buckets.len() as u64,
                expected["bucketCount"].as_u64().unwrap()
            );
            let expected_buckets = expected["buckets"].as_array().unwrap();
            assert_eq!(buckets.len(), expected_buckets.len());
            let mut largest_tree = 0;
            let mut longest_chain = 0;
            for (mut pointer, expected_bucket) in buckets.into_iter().zip(expected_buckets) {
                let expected_bucket = expected_bucket.as_array().unwrap();
                longest_chain = longest_chain.max(expected_bucket.len());
                for expected_node in expected_bucket {
                    let cons = read.object(pointer, 1, 3, 0).unwrap();
                    let key = read.nat(read.field(cons, 0).unwrap()).unwrap();
                    assert_eq!(key, expected_node["key"].as_u64().unwrap());
                    assert_eq!(key, expected_node["nativeHash"].as_u64().unwrap());
                    let set = read.field(cons, 1).unwrap();
                    let values = native_tree(&read, set, &expected_node["value"]["tree"]);
                    largest_tree = largest_tree.max(values.len());
                    assert_eq!(
                        serde_json::to_value(&values).unwrap(),
                        expected_node["value"]["values"]
                    );
                    let decoded = details
                        .overlaps
                        .iter()
                        .find(|row| u64::from(row.alternative) == key)
                        .unwrap();
                    assert_eq!(decoded.overlapping, values);
                    pointer = read.field(cons, 2).unwrap();
                }
                assert_eq!(pointer, 1);
            }
            if label == "disjoint" {
                assert_eq!(details.alt_infos.len(), 32);
                assert!(details.overlaps.is_empty());
                assert_eq!(largest_tree, 0);
                assert_eq!(longest_chain, 0);
            } else {
                assert_eq!(details.alt_infos.len(), 54);
                assert_eq!(details.overlaps.len(), 23);
                assert_eq!(
                    details
                        .overlaps
                        .iter()
                        .map(|row| row.overlapping.len())
                        .sum::<usize>(),
                    705
                );
                assert_eq!(largest_tree, 53);
                assert_eq!(longest_chain, 2);
            }
        }
    }
}
