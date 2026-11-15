// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::Ty;

fn int(value: u64) -> InterpretValue {
    InterpretValue::int(Ty::U64, value as i128).expect("u64")
}

fn lengths(snapshot: &ArrayStructure<'_>) -> Vec<u64> {
    let mut lengths = Vec::<u64>::new();
    for (index, node) in snapshot.nodes.iter().enumerate() {
        let len = match node {
            ArrayStructureNode::Dense(values) => values.len() as u64,
            ArrayStructureNode::Uniform { len, .. } => *len,
            ArrayStructureNode::Repeat { unit, count } => {
                assert!(*unit < index, "children must precede their parent");
                assert!(*count >= 2);
                lengths[*unit].checked_mul(*count).unwrap()
            }
            ArrayStructureNode::Concat { left, right } => {
                assert!(*left < index && *right < index);
                lengths[*left].checked_add(lengths[*right]).unwrap()
            }
        };
        assert_ne!(len, 0, "empty ropes have no stored nodes");
        lengths.push(len);
    }
    match snapshot.root {
        None => assert!(lengths.is_empty()),
        Some(root) => assert_eq!(root + 1, lengths.len()),
    }
    lengths
}

fn get<'a>(
    snapshot: &ArrayStructure<'a>,
    lengths: &[u64],
    mut index: u64,
) -> Option<&'a InterpretValue> {
    let mut node = snapshot.root?;
    if index >= lengths[node] {
        return None;
    }
    loop {
        match &snapshot.nodes[node] {
            ArrayStructureNode::Dense(values) => return values.get(index as usize),
            ArrayStructureNode::Uniform { value, .. } => return Some(value),
            ArrayStructureNode::Repeat { unit, .. } => {
                index %= lengths[*unit];
                node = *unit;
            }
            ArrayStructureNode::Concat { left, right } => {
                if index < lengths[*left] {
                    node = *left;
                } else {
                    index -= lengths[*left];
                    node = *right;
                }
            }
        }
    }
}

fn get_lazy(mut node: ArrayNode<'_>, mut index: u64) -> Option<&InterpretValue> {
    if index >= node.len() {
        return None;
    }
    loop {
        match node.kind() {
            ArrayNodeKind::Dense(values) => return values.get(index as usize),
            ArrayNodeKind::Uniform(value) => return Some(value),
            ArrayNodeKind::Repeat { unit, count } => {
                assert_eq!(node.len(), unit.len().checked_mul(count).unwrap());
                index %= unit.len();
                node = unit;
            }
            ArrayNodeKind::Concat { left, right } => {
                assert_eq!(node.len(), left.len().checked_add(right.len()).unwrap());
                if index < left.len() {
                    node = left;
                } else {
                    index -= left.len();
                    node = right;
                }
            }
        }
    }
}

fn assert_observation(array: &ArrayValue, probes: &[u64]) {
    let root = array.root_node();
    assert_eq!(root.map(|node| node.id()), array.structure_id());
    assert_eq!(root.map_or(0, |node| node.len()), array.len());
    if let Some(root) = root {
        assert!(!root.is_empty());
    }
    for &index in probes {
        match (
            root.and_then(|node| get_lazy(node, index)),
            array.get(index),
        ) {
            (Some(observed), Some(original)) => {
                assert!(
                    core::ptr::eq(observed, original),
                    "lazy payload must be borrowed in order"
                );
                assert_eq!(observed, original);
            }
            (None, None) => {}
            _ => panic!("lazy node bounds disagree at {index}"),
        }
    }
    let snapshot = array.structure();
    let sizes = lengths(&snapshot);
    assert_eq!(snapshot.nodes.len(), snapshot.identities.len());
    assert_eq!(
        array.structure_id(),
        snapshot.root.map(|root| snapshot.identities[root])
    );
    let second = array.structure();
    assert_eq!(snapshot.identities, second.identities);
    assert_eq!(snapshot.nodes.len(), array.rope.node_count());
    assert_eq!(snapshot.root.map_or(0, |root| sizes[root]), array.len());
    for &index in probes {
        match (get(&snapshot, &sizes, index), array.get(index)) {
            (Some(observed), Some(original)) => {
                assert!(
                    core::ptr::eq(observed, original),
                    "payload must be borrowed"
                );
                assert_eq!(observed, original);
            }
            (None, None) => {}
            _ => panic!("snapshot bounds disagree at {index}"),
        }
    }
}

#[test]
fn structure_preserves_empty_dense_windows_and_borrowed_payloads() {
    for count in [0, 1, 2, 15, 16, 17, 31, 32, 33, 65, 1024] {
        let array = ArrayValue::from_vec((0..count).map(int).collect());
        assert_observation(&array, &(0..=count).collect::<Vec<_>>());
        if count > 3 {
            let window = ArrayValue::from_rope(array.rope.slice(3, count - 3));
            assert_observation(&window, &(0..=count).collect::<Vec<_>>());
            assert_eq!(window.get(0), Some(&int(3)));
        }
    }
}

#[test]
fn structure_keeps_maximum_uniform_and_periodic_extents_compact() {
    let uniform = ArrayValue::splat(int(77), u64::MAX);
    let snapshot = uniform.structure();
    assert_eq!(snapshot.nodes.len(), 1);
    assert!(matches!(
        snapshot.nodes[0],
        ArrayStructureNode::Uniform { len: u64::MAX, .. }
    ));
    assert_observation(&uniform, &[0, 1, 1 << 40, u64::MAX - 1, u64::MAX]);

    let shared = uniform.clone();
    let equal_but_separate = ArrayValue::splat(int(77), u64::MAX);
    assert_eq!(uniform.structure_id(), shared.structure_id());
    assert_ne!(uniform.structure_id(), equal_but_separate.structure_id());
    assert_eq!(uniform, equal_but_separate);
    let mut seen = std::collections::HashSet::new();
    seen.insert(uniform.structure_id().unwrap());
    assert!(seen.contains(&shared.structure_id().unwrap()));
    assert!(!seen.contains(&equal_but_separate.structure_id().unwrap()));

    let count = u64::MAX / 2;
    let periodic = ArrayValue::from_vec(vec![int(10), int(20)]).repeat(count);
    let snapshot = periodic.structure();
    assert_eq!(snapshot.nodes.len(), 2);
    assert!(
        matches!(snapshot.nodes[1], ArrayStructureNode::Repeat { unit: 0, count: n } if n == count)
    );
    let probes = [0, 1, 2, (1 << 40) + 1, u64::MAX - 2, u64::MAX - 1];
    assert_observation(&periodic, &probes);
    for index in probes.into_iter().filter(|&i| i < periodic.len()) {
        assert_eq!(
            periodic.get(index),
            Some(&int(if index % 2 == 0 { 10 } else { 20 }))
        );
    }
}

#[test]
fn structure_records_shared_nodes_once_after_periodic_update() {
    let unit = ArrayValue::from_vec((0..17).map(int).collect());
    let base = unit.repeat(u64::MAX / 17);
    let index = u64::MAX / 2 + 3;
    let updated = base.set(index, int(999)).unwrap();
    let snapshot = updated.structure();
    assert!(
        snapshot.nodes.len() < 512,
        "observation must follow stored structure"
    );
    let mut references = vec![0; snapshot.nodes.len()];
    for node in &snapshot.nodes {
        match node {
            ArrayStructureNode::Repeat { unit, .. } => references[*unit] += 1,
            ArrayStructureNode::Concat { left, right } => {
                references[*left] += 1;
                references[*right] += 1;
            }
            _ => {}
        }
    }
    assert!(
        references.iter().any(|&count| count > 1),
        "shared edges must reuse one index"
    );
    let probes = [
        0,
        16,
        17,
        index - 1,
        index,
        index + 1,
        u64::MAX - 1,
        u64::MAX,
    ];
    assert_observation(&updated, &probes);
    for probe in probes.into_iter().filter(|&i| i < base.len()) {
        assert_eq!(base.get(probe), Some(&int(probe % 17)));
        assert_eq!(
            updated.get(probe),
            Some(&int(if probe == index { 999 } else { probe % 17 }))
        );
    }
}

#[test]
fn lazy_nodes_visit_overlapping_result_roots_once_per_distinct_node() {
    use std::collections::HashSet;
    let mut versions = vec![ArrayValue::from_vec((0..4096).map(int).collect())];
    for i in 0..1024 {
        let next = versions.last().unwrap().set(0, int(100_000 + i)).unwrap();
        versions.push(next);
    }
    versions.push(versions[0].clone());

    // Independent eager snapshots establish the full union, including nodes
    // shared between different roots. The lazy walker checks identity before
    // asking for children; it never snapshots or expands a logical array.
    let mut expected = HashSet::new();
    let mut snapshot_work = 0;
    for array in &versions {
        let snapshot = array.structure();
        snapshot_work += snapshot.nodes.len();
        expected.extend(snapshot.identities);
    }
    let mut seen = HashSet::new();
    let mut pending: Vec<_> = versions.iter().filter_map(ArrayValue::root_node).collect();
    let mut expanded = 0;
    let mut edges = 0;
    while let Some(node) = pending.pop() {
        if !seen.insert(node.id()) {
            continue;
        }
        expanded += 1;
        match node.kind() {
            ArrayNodeKind::Concat { left, right } => {
                pending.extend([left, right]);
                edges += 2;
            }
            ArrayNodeKind::Repeat { unit, .. } => {
                pending.push(unit);
                edges += 1;
            }
            ArrayNodeKind::Dense(_) | ArrayNodeKind::Uniform(_) => {}
        }
    }
    assert_eq!(seen, expected);
    assert_eq!(expanded, seen.len());
    assert!(edges <= 2 * expanded);
    assert!(
        snapshot_work > 50 * expanded,
        "fixture must expose repeated snapshot work"
    );
    println!(
        "lazy array batch: {} roots; {expanded} distinct node views; {snapshot_work} eager snapshot nodes",
        versions.len()
    );
}
