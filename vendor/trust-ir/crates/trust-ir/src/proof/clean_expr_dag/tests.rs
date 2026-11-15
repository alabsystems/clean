// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use clean_kernel::expr::{
    BigNat, BinderData, BinderInfo, ExprKind, FVarId, Literal, MDataValue, Multiplicity, ZFCSetExpr,
};

fn expression(kind: ExprKind) -> Expr {
    Expr::from_kind(kind)
}

fn roundtrip(expr: &Expr) -> Vec<u8> {
    let bytes = encode_clean_expr_dag_v2(expr).unwrap();
    let decoded = decode_clean_expr_dag_v2(&bytes).unwrap();
    // Legacy bytes independently observe ALL fields, even fields omitted by
    // kernel cached hashing, definitional equality or the lossy flat format.
    assert_eq!(
        bincode::serialize(&decoded).unwrap(),
        bincode::serialize(expr).unwrap()
    );
    assert_eq!(encode_clean_expr_dag_v2(&decoded).unwrap(), bytes);
    bytes
}

fn record(kind: u8, tag: u8, payload: &[u8]) -> Vec<u8> {
    let mut bytes = vec![kind, tag];
    bytes.extend_from_slice(payload);
    bytes
}
fn ids(values: &[u32]) -> Vec<u8> {
    values.iter().flat_map(|v| v.to_le_bytes()).collect()
}
fn carrier(records: &[Vec<u8>], root: u32) -> Vec<u8> {
    let mut bytes = MAGIC.to_vec();
    bytes.extend_from_slice(&(records.len() as u32).to_le_bytes());
    bytes.extend_from_slice(&root.to_le_bytes());
    for row in records {
        bytes.extend_from_slice(&(row.len() as u32).to_le_bytes());
        bytes.extend_from_slice(row);
    }
    bytes
}
fn err(bytes: &[u8], needle: &str) {
    let Err(error) = decode_clean_expr_dag_v2(bytes) else {
        panic!("malformed carrier must reject");
    };
    assert!(error.contains(needle), "expected {needle:?}, got {error}");
}

#[test]
fn dag_v2_leaf_wire_golden_is_stable() {
    let expected = b"CEXDAG02\x01\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x02\x0c";
    assert_eq!(
        encode_clean_expr_dag_v2(&expression(ExprKind::SProp)).unwrap(),
        expected
    );
    assert!(matches!(
        decode_clean_expr_dag_v2(expected).unwrap().kind(),
        ExprKind::SProp
    ));
}

#[test]
fn illegal_scalar_tags_and_record_lengths_refuse() {
    for (info, mult, reason) in [(4, 2, "binder info"), (0, 3, "multiplicity")] {
        let mut payload = vec![info, mult];
        payload.extend_from_slice(&ids(&[0, 0]));
        err(
            &carrier(&[record(2, 12, &[]), record(2, 5, &payload)], 1),
            reason,
        );
    }
    let mut let_payload = ids(&[0, 1, 1, 1]);
    let_payload.push(2);
    err(
        &carrier(
            &[
                record(0, 0, &[]),
                record(2, 12, &[]),
                record(2, 7, &let_payload),
            ],
            2,
        ),
        "boolean",
    );
    err(&carrier(&[record(2, 8, &[2])], 0), "BigNat tag");
    let mut oversized = carrier(&[record(2, 12, &[])], 0);
    oversized[16..20].copy_from_slice(&u32::MAX.to_le_bytes());
    err(&oversized, "truncated");
    let mut wrong_root = carrier(&[record(2, 12, &[])], 0);
    wrong_root[12..16].copy_from_slice(&1u32.to_le_bytes());
    err(&wrong_root, "root is not the final");
}

#[test]
fn exact_all_expression_and_zfc_variants_roundtrip() {
    let a = Arc::new(Expr::nat_lit(1));
    let b = Arc::new(Expr::nat_lit(2));
    let c = Arc::new(Expr::nat_lit(3));
    let d = Arc::new(Expr::nat_lit(4));
    let name = Name::anon().str("a.b").num(u64::MAX).str("1");
    let mut variants = vec![
        ExprKind::BVar(1_048_574),
        ExprKind::FVar(FVarId::new(u64::MAX)),
        ExprKind::Sort(Level::Zero),
        ExprKind::Const(name.clone(), vec![Level::Zero].into()),
        ExprKind::App(a.clone(), b.clone()),
        ExprKind::Let(name.clone(), a.clone(), b.clone(), c.clone(), true),
        ExprKind::Proj(name.clone(), u32::MAX, a.clone()),
        ExprKind::Lit(Literal::Nat(BigNat::Small(u64::MAX))),
        ExprKind::Lit(Literal::String(Arc::from("\0unicode λ"))),
        ExprKind::MData(
            vec![
                (name.clone(), MDataValue::Bool(true)),
                (name.clone(), MDataValue::Nat(u64::MAX)),
                (name.clone(), MDataValue::String(Arc::from("metadata\0"))),
                (name.clone(), MDataValue::Name(Name::anon().str("1"))),
            ],
            a.clone(),
        ),
        ExprKind::SProp,
        ExprKind::Squash(a.clone()),
        ExprKind::CubicalInterval,
        ExprKind::CubicalI0,
        ExprKind::CubicalI1,
        ExprKind::CubicalPath {
            ty: a.clone(),
            left: b.clone(),
            right: c.clone(),
        },
        ExprKind::CubicalPathLam { body: a.clone() },
        ExprKind::CubicalPathApp {
            path: a.clone(),
            arg: b.clone(),
        },
        ExprKind::CubicalHComp {
            ty: a.clone(),
            phi: b.clone(),
            u: c.clone(),
            base: d.clone(),
        },
        ExprKind::CubicalTransp {
            ty: a.clone(),
            phi: b.clone(),
            base: c.clone(),
        },
        ExprKind::CubicalCoe {
            ty: a.clone(),
            r: b.clone(),
            s: c.clone(),
            base: d.clone(),
        },
        ExprKind::ZFCMem {
            element: a.clone(),
            set: b.clone(),
        },
        ExprKind::ZFCComprehension {
            domain: a.clone(),
            pred: b.clone(),
        },
    ];
    for set in [
        ZFCSetExpr::Empty,
        ZFCSetExpr::Singleton(a.clone()),
        ZFCSetExpr::Pair(a.clone(), b.clone()),
        ZFCSetExpr::Union(a.clone()),
        ZFCSetExpr::PowerSet(a.clone()),
        ZFCSetExpr::Separation {
            set: a.clone(),
            pred: b.clone(),
        },
        ZFCSetExpr::Replacement {
            set: a.clone(),
            func: b.clone(),
        },
        ZFCSetExpr::Infinity,
        ZFCSetExpr::Choice(a),
    ] {
        variants.push(ExprKind::ZFCSet(set));
    }
    for variant in variants {
        roundtrip(&expression(variant));
    }
}

#[test]
fn all_binders_and_lossy_flat_collisions_remain_distinct() {
    let a = Arc::new(Expr::const_str("Nat"));
    let b = Arc::new(Expr::bvar(0));
    let mut unique = HashSet::new();
    for info in [
        BinderInfo::Default,
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ] {
        for mult in [Multiplicity::Zero, Multiplicity::One, Multiplicity::Many] {
            let binder = BinderData { info, mult };
            assert!(unique.insert(roundtrip(&expression(ExprKind::Lam(
                binder,
                a.clone(),
                b.clone()
            )))));
            assert!(unique.insert(roundtrip(&expression(ExprKind::Pi(
                binder,
                a.clone(),
                b.clone()
            )))));
        }
    }
    assert_eq!(unique.len(), 24);
    let names = [
        Name::anon(),
        Name::anon().str(""),
        Name::anon().str("a.b"),
        Name::anon().str("a").str("b"),
        Name::anon().num(1),
        Name::anon().str("1"),
    ];
    unique.clear();
    for name in names {
        assert!(unique.insert(roundtrip(&Expr::const_(name.clone(), vec![]))));
        for flag in [false, true] {
            assert!(unique.insert(roundtrip(&expression(ExprKind::Let(
                name.clone(),
                a.clone(),
                b.clone(),
                b.clone(),
                flag
            )))));
        }
    }
    assert_eq!(unique.len(), 18);
}

#[test]
fn nonnormal_bignats_metadata_and_levels_are_preserved_not_normalized() {
    let mut unique = HashSet::new();
    for n in [
        BigNat::Small(0),
        BigNat::Big(vec![]),
        BigNat::Big(vec![0]),
        BigNat::Big(vec![0, 0]),
        BigNat::Small(1),
        BigNat::Big(vec![1]),
        BigNat::Big(vec![1, 0]),
        BigNat::Big(vec![u64::MAX, u64::MAX]),
    ] {
        assert!(unique.insert(roundtrip(&expression(ExprKind::Lit(Literal::Nat(n))))));
    }
    let z: Arc<Level> = Arc::new(Level::Zero);
    for level in [
        Level::Zero,
        Level::Succ(z.clone().into()),
        Level::Max(z.clone().into(), z.clone().into()),
        Level::IMax(z.clone().into(), z.into()),
        Level::Param(Name::anon().str("u.v")),
    ] {
        assert!(unique.insert(roundtrip(&expression(ExprKind::Sort(level)))));
    }
    let a = (Name::anon().str("k"), MDataValue::Nat(1));
    let b = (Name::anon().str("k"), MDataValue::Nat(2));
    let inner = Arc::new(Expr::nat_lit(0));
    for metadata in [
        vec![],
        vec![a.clone()],
        vec![a.clone(), a.clone()],
        vec![a.clone(), b.clone()],
        vec![b, a],
    ] {
        assert!(unique.insert(roundtrip(&expression(ExprKind::MData(
            metadata,
            inner.clone()
        )))));
    }
}

fn shared(depth: usize) -> Expr {
    let mut term = Arc::new(Expr::nat_lit(0));
    for _ in 0..depth {
        term = Arc::new(expression(ExprKind::App(term.clone(), term)));
    }
    term.as_ref().clone()
}
fn unshared(depth: usize) -> Expr {
    if depth == 0 {
        Expr::nat_lit(0)
    } else {
        Expr::app(unshared(depth - 1), unshared(depth - 1))
    }
}

#[test]
fn canonical_sharing_is_linear_and_decoded_children_reuse_arcs() {
    for depth in 0..10 {
        assert_eq!(
            encode_clean_expr_dag_v2(&shared(depth)).unwrap(),
            encode_clean_expr_dag_v2(&unshared(depth)).unwrap()
        );
    }
    let bytes = encode_clean_expr_dag_v2(&shared(80)).unwrap();
    assert!(
        bytes.len() < 1500,
        "a 2^80 tree must stay an 81-node carrier"
    );
    let decoded = decode_clean_expr_dag_v2(&bytes).unwrap();
    let mut cursor = &decoded;
    for _ in 0..80 {
        let ExprKind::App(a, b) = cursor.kind() else {
            panic!("expected shared App");
        };
        assert!(Arc::ptr_eq(a, b));
        cursor = a;
    }
    assert_eq!(encode_clean_expr_dag_v2(&decoded).unwrap(), bytes);
    let shared = shared(2);
    let canonical = encode_clean_expr_dag_v2(&shared).unwrap();
    let exact = Limits {
        bytes: canonical.len(),
        ..LIMITS
    };
    assert_eq!(
        encode(&shared, exact).unwrap(),
        encode(&unshared(2), exact).unwrap()
    );
}

#[test]
fn cloned_large_metadata_names_do_not_reprocess_their_payload_per_use() {
    let name = Name::anon().str("large-name-component".repeat(100));
    let metadata = (0..1000)
        .map(|_| (name.clone(), MDataValue::Bool(true)))
        .collect();
    let expr = expression(ExprKind::MData(metadata, Arc::new(Expr::nat_lit(0))));
    let bytes = encode_clean_expr_dag_v2(&expr).unwrap();
    assert!(bytes.len() < 9000);
    let limits = Limits {
        bytes: bytes.len(),
        ..LIMITS
    };
    assert_eq!(encode(&expr, limits).unwrap(), bytes);
    let decoded = decode(&bytes, limits).unwrap();
    assert_eq!(encode(&decoded, limits).unwrap(), bytes);
}

#[test]
fn v1_and_v2_are_explicit_disjoint_carriers() {
    let expr = Expr::app(Expr::const_str("f"), Expr::nat_lit(7));
    let legacy = super::super::encode_clean_expr_v1(&expr).unwrap();
    assert_eq!(legacy, bincode::serialize(&expr).unwrap());
    let dag = roundtrip(&expr);
    assert!(decode_clean_expr_dag_v2(&legacy).is_err());
    assert!(super::super::decode_clean_expr_v1(&dag).is_err());
}

#[test]
fn exact_byte_node_depth_and_input_identity_bounds() {
    let expr = Expr::nat_lit(1);
    let bytes = encode_clean_expr_dag_v2(&expr).unwrap();
    let exact = Limits {
        bytes: bytes.len(),
        nodes: 1,
        depth: 1,
        ..LIMITS
    };
    assert_eq!(encode(&expr, exact).unwrap(), bytes);
    assert!(decode(&bytes, exact).is_ok());
    for limits in [
        Limits {
            bytes: bytes.len() - 1,
            ..exact
        },
        Limits { nodes: 0, ..exact },
        Limits { depth: 0, ..exact },
    ] {
        assert!(encode(&expr, limits).is_err());
        assert!(decode(&bytes, limits).is_err());
    }
    let expr = shared(7);
    let bytes = encode_clean_expr_dag_v2(&expr).unwrap();
    assert!(decode(&bytes, Limits { depth: 8, ..LIMITS }).is_ok());
    assert!(decode(&bytes, Limits { depth: 7, ..LIMITS }).is_err());
    assert!(encode(&expr, Limits { nodes: 9, ..LIMITS }).is_ok());
    assert!(
        encode(&unshared(7), Limits { nodes: 9, ..LIMITS })
            .unwrap_err()
            .contains("identity")
    );
    let deep = shared(512);
    let bytes = encode_clean_expr_dag_v2(&deep).unwrap();
    assert!(decode_clean_expr_dag_v2(&bytes).is_ok());
}

#[test]
fn depth_bound_spans_expression_level_name_and_metadata_edges() {
    let name = Name::anon().str("u").str("v");
    let level = Level::Param(name.clone());
    let expr = expression(ExprKind::Sort(level)); // Anon/Str/Str/Param/Sort = 5
    let bytes = encode_clean_expr_dag_v2(&expr).unwrap();
    assert!(decode(&bytes, Limits { depth: 5, ..LIMITS }).is_ok());
    assert!(decode(&bytes, Limits { depth: 4, ..LIMITS }).is_err());
    let expr = expression(ExprKind::MData(
        vec![(name, MDataValue::Bool(false))],
        Arc::new(Expr::nat_lit(0)),
    ));
    let bytes = encode_clean_expr_dag_v2(&expr).unwrap();
    assert!(decode(&bytes, Limits { depth: 4, ..LIMITS }).is_ok());
    assert!(decode(&bytes, Limits { depth: 3, ..LIMITS }).is_err());
}

#[test]
fn typed_backward_references_and_canonical_table_are_required() {
    let leaf = record(2, 12, &[]);
    for id in [0, 1, u32::MAX] {
        err(&carrier(&[record(2, 13, &ids(&[id]))], 0), "reference");
    }
    err(
        &carrier(&[record(0, 0, &[]), record(2, 13, &ids(&[0]))], 1),
        "not an Expr",
    );
    err(
        &carrier(&[leaf.clone(), record(2, 2, &ids(&[0]))], 1),
        "not a Level",
    );
    err(
        &carrier(&[leaf.clone(), record(1, 4, &ids(&[0]))], 1),
        "not a Name",
    );
    err(&carrier(&[leaf.clone(), leaf.clone()], 1), "duplicate");
    err(
        &carrier(&[leaf.clone(), record(2, 14, &[])], 1),
        "unreachable",
    );
    // Topologically valid, unique and reachable, but reverse of DFS child order.
    err(
        &carrier(&[record(2, 15, &[]), leaf, record(2, 4, &ids(&[1, 0]))], 2),
        "noncanonical",
    );
    err(&carrier(&[record(0, 0, &[])], 0), "root is not an Expr");
}

#[test]
fn malformed_tags_lengths_scalars_and_suffixes_fail_closed() {
    err(&carrier(&[record(3, 0, &[])], 0), "node type");
    for kind in 0..3 {
        err(&carrier(&[record(kind, 255, &[])], 0), "tag");
    }
    err(&carrier(&[record(2, 0, &ids(&[1_048_575]))], 0), "BVar");
    err(&carrier(&[record(2, 9, &ids(&[u32::MAX]))], 0), "count");
    let mut payload = ids(&[1]);
    payload.push(255);
    err(&carrier(&[record(2, 9, &payload)], 0), "UTF-8");
    err(&carrier(&[record(2, 12, &[0])], 0), "trailing node");
    let mut bytes = carrier(&[record(2, 12, &[])], 0);
    bytes.push(0);
    err(&bytes, "trailing carrier");
    bytes[0] ^= 1;
    err(&bytes, "magic");
    let mut bytes = MAGIC.to_vec();
    bytes.extend_from_slice(&u32::MAX.to_le_bytes());
    bytes.extend_from_slice(&0u32.to_le_bytes());
    err(&bytes, "node limit");
    let valid = carrier(&[record(2, 12, &[])], 0);
    for length in 0..valid.len() {
        assert!(decode_clean_expr_dag_v2(&valid[..length]).is_err());
    }
}

#[test]
fn expanded_level_work_is_checked_before_kernel_construction_and_aggregated() {
    let mut records = vec![record(1, 0, &[])];
    for i in 0..40 {
        records.push(record(1, 2, &ids(&[i, i])));
    }
    records.push(record(2, 2, &ids(&[40])));
    err(&carrier(&records, 41), "constructor work");

    // Two different constants use the same Level. Their independent constructor
    // costs must both count, even though the Level node itself is shared.
    let records = vec![
        record(0, 0, &[]),
        record(1, 0, &[]),
        record(2, 3, &ids(&[0, 1, 1])),
        record(2, 2, &ids(&[1])),
        record(2, 4, &ids(&[2, 3])),
    ];
    let bytes = carrier(&records, 4);
    assert!(
        decode(
            &bytes,
            Limits {
                constructor_work: 6,
                ..LIMITS
            }
        )
        .is_ok()
    );
    assert!(
        decode(
            &bytes,
            Limits {
                constructor_work: 5,
                ..LIMITS
            }
        )
        .unwrap_err()
        .contains("constructor work")
    );
}

#[test]
fn aggregate_pending_payloads_are_bounded_during_encoding() {
    let mut expr = Expr::nat_lit(0);
    for _ in 0..8 {
        expr = expression(ExprKind::MData(
            vec![(Name::anon(), MDataValue::String(Arc::from("x".repeat(100))))],
            Arc::new(expr),
        ));
    }
    let error = encode(
        &expr,
        Limits {
            bytes: 400,
            ..LIMITS
        },
    )
    .unwrap_err();
    assert!(error.contains("byte limit"), "{error}");
}
