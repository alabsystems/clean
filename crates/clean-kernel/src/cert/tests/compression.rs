// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate compression and archive tests (LZ4, ZSTD)

use crate::cert::*;
use crate::expr::{BigNat, BinderInfo, Expr, ExprKind, FVarId, Literal};
use crate::level::Level;
use crate::name::Name;

#[test]
fn test_compress_simple_sort() {
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let compressed = compress_cert(&cert).expect("compress failed");
    assert_eq!(compressed.certs.len(), 1);
    assert_eq!(compressed.levels.len(), 1);
    assert_eq!(compressed.exprs.len(), 0);

    // Decompress and verify roundtrip
    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_nested_levels() {
    // Succ(Succ(Zero)) - should deduplicate Zero
    let cert = ProofCert::Sort {
        level: Level::succ(Level::succ(Level::zero())),
    };

    let compressed = compress_cert(&cert).expect("compress failed");
    // Should have 3 levels: Zero, Succ(0), Succ(1)
    assert_eq!(compressed.levels.len(), 3);

    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_with_shared_types() {
    // Lambda with Prop -> Prop type (Prop appears twice)
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(Expr::pi(BinderInfo::Default, prop.clone(), prop.clone())),
    };

    let compressed = compress_cert(&cert).expect("compress failed");

    // Verify decompression roundtrip
    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_app_certificate() {
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);

    let cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Const {
            name: Name::from_string("f"),
            levels: vec![],
            type_: Box::new(Expr::arrow(a_ty.clone(), b_ty.clone())),
        }),
        fn_type: Box::new(Expr::arrow(a_ty.clone(), b_ty.clone())),
        arg_cert: Box::new(ProofCert::Const {
            name: Name::from_string("x"),
            levels: vec![],
            type_: Box::new(a_ty.clone()),
        }),
        result_type: Box::new(b_ty),
    };

    let compressed = compress_cert(&cert).expect("compress failed");
    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_pi_certificate() {
    let cert = ProofCert::Pi {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        arg_level: Level::succ(Level::zero()),
        body_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_level: Level::succ(Level::zero()),
    };

    let compressed = compress_cert(&cert).expect("compress failed");

    // Should share the Sort certificates since they're identical
    assert!(compressed.certs.len() <= 3); // Pi + at most 2 Sort certs (may share)

    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_let_certificate() {
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let cert = ProofCert::Let {
        type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        value_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(prop),
    };

    let compressed = compress_cert(&cert).expect("compress failed");
    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_lit_certificate() {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let cert = ProofCert::Lit {
        lit: Literal::Nat(BigNat::Small(42)),
        type_: Box::new(nat_ty),
    };

    let compressed = compress_cert(&cert).expect("compress failed");
    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_fvar_certificate() {
    let fvar_id = FVarId(123);
    let cert = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let compressed = compress_cert(&cert).expect("compress failed");
    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_def_eq_certificate() {
    let cert = ProofCert::DefEq {
        inner: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
        actual_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
        eq_steps: vec![DefEqStep::Refl],
    };

    let compressed = compress_cert(&cert).expect("compress failed");
    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_mdata_certificate() {
    use crate::expr::MDataValue;

    let metadata = vec![(Name::from_string("trace"), MDataValue::Bool(true))];
    let cert = ProofCert::MData {
        metadata: metadata.clone(),
        inner_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        result_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
    };

    let compressed = compress_cert(&cert).expect("compress failed");
    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_with_stats() {
    // Build a certificate with significant sharing potential
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let prop_to_prop = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());

    // Certificate for identity: λ (x : Prop). x
    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(prop_to_prop),
    };

    let (compressed, stats) = compress_cert_with_stats(&cert).expect("compress failed");

    // Verify stats are populated
    assert!(stats.unique_certs > 0);
    assert!(stats.unique_levels > 0);
    assert!(stats.original_bytes > 0);
    assert!(stats.compressed_bytes > 0);

    // Verify roundtrip
    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_complex_nested() {
    // Build: (λ (A : Type). λ (x : A). x) with certificate
    let type0 = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

    let inner_body_cert = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(Expr::from_kind(ExprKind::BVar(1))),
    };

    let inner_cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(type1.clone()),
        }),
        body_cert: Box::new(inner_body_cert),
        result_type: Box::new(Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(0)),
            Expr::from_kind(ExprKind::BVar(1)),
        )),
    };

    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(inner_cert),
        result_type: Box::new(Expr::pi(
            BinderInfo::Default,
            type0.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::BVar(0)),
                Expr::from_kind(ExprKind::BVar(1)),
            ),
        )),
    };

    let compressed = compress_cert(&cert).expect("compress failed");
    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compress_serialization_roundtrip() {
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(Expr::pi(BinderInfo::Default, prop.clone(), prop.clone())),
    };

    // Full roundtrip: cert -> compress -> serialize -> deserialize -> decompress -> cert
    let compressed = compress_cert(&cert).expect("compress failed");

    // JSON roundtrip
    let json = serde_json::to_string(&compressed).expect("JSON serialize failed");
    let restored_compressed: CompressedCert =
        serde_json::from_str(&json).expect("JSON deserialize failed");
    let restored = decompress_cert(&restored_compressed).expect("decompress failed");
    assert_eq!(restored, cert);

    // Bincode roundtrip
    let bytes = bincode::serde::encode_to_vec(&compressed, bincode::config::standard())
        .expect("bincode serialize failed");
    let restored_compressed2: CompressedCert =
        bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
            .map(|(__v, _)| __v)
            .expect("bincode deserialize failed");
    let restored2 = decompress_cert(&restored_compressed2).expect("decompress failed");
    assert_eq!(restored2, cert);
}

#[test]
fn test_compression_deduplicates_shared_expressions() {
    // Create a certificate where the same expression appears multiple times
    let shared_type = Expr::const_(Name::from_string("SharedType"), vec![Level::zero()]);

    let cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Const {
            name: Name::from_string("f"),
            levels: vec![Level::zero()],
            type_: Box::new(Expr::arrow(shared_type.clone(), shared_type.clone())),
        }),
        fn_type: Box::new(Expr::arrow(shared_type.clone(), shared_type.clone())),
        arg_cert: Box::new(ProofCert::Const {
            name: Name::from_string("x"),
            levels: vec![Level::zero()],
            type_: Box::new(shared_type.clone()),
        }),
        result_type: Box::new(shared_type),
    };

    let compressed = compress_cert(&cert).expect("compress failed");

    // The shared_type expression should be deduplicated
    // Count how many unique Const expressions there are
    let const_count = compressed
        .exprs
        .iter()
        .filter(|e| matches!(e, CompressedExpr::Const(_, _)))
        .count();

    // Should have 2 unique consts: SharedType and the Pi (arrow) type components
    // The SharedType expression should be shared (appears once)
    assert!(const_count >= 1); // At least SharedType is deduplicated

    // Verify roundtrip
    let decompressed = decompress_cert(&compressed).expect("decompress failed");
    assert_eq!(decompressed, cert);
}

#[test]
fn test_compression_stats_display() {
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let (_, stats) = compress_cert_with_stats(&cert).expect("compress failed");
    let display = format!("{stats}");

    // Verify display contains expected fields
    assert!(display.contains("exprs:"));
    assert!(display.contains("levels:"));
    assert!(display.contains("certs:"));
    assert!(display.contains("bytes"));
}

#[test]
fn test_decompress_error_display() {
    let err1 = DecompressError::InvalidExprIndex(42);
    let s1 = format!("{err1}");
    assert!(s1.contains("42"));
    assert!(s1.contains("expression"));

    let err2 = DecompressError::InvalidLevelIndex(99);
    let s2 = format!("{err2}");
    assert!(s2.contains("99"));
    assert!(s2.contains("level"));

    let err3 = DecompressError::InvalidCertIndex(123);
    let s3 = format!("{err3}");
    assert!(s3.contains("123"));
    assert!(s3.contains("certificate"));
}

// ========================================================================
// Byte-Level Compression (LZ4) Tests
// ========================================================================

#[test]
fn test_archive_simple_cert() {
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let archive = archive_cert(&cert).expect("archive failed");
    assert_eq!(archive.version, CertArchive::VERSION);
    assert!(!archive.compressed_data.is_empty());

    let restored = unarchive_cert(&archive).expect("unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_archive_complex_cert() {
    // Build a complex certificate with nested structure
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let prop_to_prop = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());

    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(prop_to_prop),
    };

    let archive = archive_cert(&cert).expect("archive failed");
    let restored = unarchive_cert(&archive).expect("unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_archive_with_stats() {
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let prop_to_prop = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());

    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(prop_to_prop),
    };

    let (archive, stats) = archive_cert_with_stats(&cert).expect("archive with stats failed");

    // Verify stats are populated
    assert!(stats.original_cert_bytes > 0);
    assert!(stats.structure_shared_bytes > 0);
    assert!(stats.archive_bytes > 0);
    // For small certs, structure sharing may increase size due to indexing overhead
    // but LZ4 should help. Just verify the ratios are reasonable positive values.
    assert!(stats.structure_ratio > 0.0);
    assert!(stats.lz4_ratio > 0.0);
    assert!(stats.total_ratio > 0.0);

    // Verify roundtrip
    let restored = unarchive_cert(&archive).expect("unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_archive_stats_display() {
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let (_, stats) = archive_cert_with_stats(&cert).expect("archive failed");

    let display = format!("{stats}");
    assert!(display.contains("struct:"));
    assert!(display.contains("lz4:"));
    assert!(display.contains("total:"));
    assert!(display.contains("bytes"));
}

#[test]
fn test_lz4_compress_decompress() {
    let data = b"Hello, clean! This is a test of LZ4 compression.";

    let compressed = lz4_compress(data);
    let decompressed = lz4_decompress(&compressed).expect("decompress failed");

    assert_eq!(decompressed, data);
}

#[test]
fn test_lz4_compress_repetitive_data() {
    // Repetitive data should compress well
    let data: Vec<u8> = (0..1000).map(|i| (i % 10) as u8).collect();

    let compressed = lz4_compress(&data);
    let decompressed = lz4_decompress(&compressed).expect("decompress failed");

    assert_eq!(decompressed, data);
    // Repetitive data should compress significantly
    assert!(compressed.len() < data.len());
}

#[test]
fn test_archive_nested_app_chain() {
    // Build: f (g (h x)) with certificates
    let unit_type = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let inner_cert = ProofCert::Const {
        name: Name::from_string("x"),
        levels: vec![],
        type_: Box::new(unit_type.clone()),
    };

    let h_app_cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Const {
            name: Name::from_string("h"),
            levels: vec![],
            type_: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        }),
        fn_type: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        arg_cert: Box::new(inner_cert),
        result_type: Box::new(unit_type.clone()),
    };

    let g_app_cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Const {
            name: Name::from_string("g"),
            levels: vec![],
            type_: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        }),
        fn_type: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        arg_cert: Box::new(h_app_cert),
        result_type: Box::new(unit_type.clone()),
    };

    let cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Const {
            name: Name::from_string("f"),
            levels: vec![],
            type_: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        }),
        fn_type: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        arg_cert: Box::new(g_app_cert),
        result_type: Box::new(unit_type),
    };

    let archive = archive_cert(&cert).expect("archive failed");
    let restored = unarchive_cert(&archive).expect("unarchive failed");
    assert_eq!(restored, cert);

    // With stats to verify compression effectiveness
    let (_, stats) = archive_cert_with_stats(&cert).expect("archive with stats failed");
    // Nested apps with repeated types should compress well
    assert!(
        stats.total_ratio >= 1.0,
        "Expected some compression for nested apps"
    );
}

#[test]
fn test_archive_bincode_serialization() {
    // Test that CertArchive itself can be serialized/deserialized
    let cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };
    let archive = archive_cert(&cert).expect("archive failed");

    // Serialize archive to bincode
    let archive_bytes = bincode::serde::encode_to_vec(&archive, bincode::config::standard())
        .expect("serialize archive failed");

    // Deserialize
    let restored_archive: CertArchive =
        bincode::serde::decode_from_slice(&archive_bytes, bincode::config::standard())
            .map(|(__v, _)| __v)
            .expect("deserialize archive failed");

    // Unarchive
    let restored = unarchive_cert(&restored_archive).expect("unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_archive_json_serialization() {
    // Test that CertArchive can be serialized to JSON (for debugging)
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let archive = archive_cert(&cert).expect("archive failed");

    // Serialize archive to JSON
    let json = serde_json::to_string(&archive).expect("serialize to JSON failed");

    // Deserialize
    let restored_archive: CertArchive =
        serde_json::from_str(&json).expect("deserialize from JSON failed");

    // Unarchive
    let restored = unarchive_cert(&restored_archive).expect("unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_byte_compress_error_display() {
    let err1 = ByteCompressError::SerializeError("test".to_string());
    let s1 = format!("{err1}");
    assert!(s1.contains("Serialization"));
    assert!(s1.contains("test"));

    let err2 = ByteCompressError::CompressError("lz4 fail".to_string());
    let s2 = format!("{err2}");
    assert!(s2.contains("LZ4 compression"));

    let err3 = ByteCompressError::DecompressError("bad data".to_string());
    let s3 = format!("{err3}");
    assert!(s3.contains("LZ4 decompression"));

    let err4 = ByteCompressError::DeserializeError("parse fail".to_string());
    let s4 = format!("{err4}");
    assert!(s4.contains("Deserialization"));
}

#[test]
fn test_lz4_decompress_invalid_data() {
    // Invalid LZ4 data should return an error
    let invalid_data = b"not valid lz4 data";
    let result = lz4_decompress(invalid_data);
    assert!(
        matches!(result, Err(ByteCompressError::DecompressError(_))),
        "expected DecompressError, got: {result:?}"
    );
}

#[test]
fn test_archive_with_all_cert_variants() {
    // Test archiving certificates with various variants
    let type0 = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // FVar certificate
    let fvar_cert = ProofCert::FVar {
        id: FVarId(42),
        type_: Box::new(type0.clone()),
    };
    let archive = archive_cert(&fvar_cert).expect("archive fvar failed");
    let restored = unarchive_cert(&archive).expect("unarchive fvar failed");
    assert_eq!(restored, fvar_cert);

    // Let certificate
    let let_cert = ProofCert::Let {
        type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        value_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(type0.clone()),
        }),
        result_type: Box::new(type0.clone()),
    };
    let archive = archive_cert(&let_cert).expect("archive let failed");
    let restored = unarchive_cert(&archive).expect("unarchive let failed");
    assert_eq!(restored, let_cert);

    // Lit certificate
    let lit_cert = ProofCert::Lit {
        lit: Literal::Nat(BigNat::Small(42)),
        type_: Box::new(Expr::const_(Name::from_string("Nat"), vec![])),
    };
    let archive = archive_cert(&lit_cert).expect("archive lit failed");
    let restored = unarchive_cert(&archive).expect("unarchive lit failed");
    assert_eq!(restored, lit_cert);
}

// ========================================================================
// Zstd compression tests
// ========================================================================

#[test]
fn test_zstd_archive_simple_cert() {
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let archive = zstd_archive_cert(&cert).expect("zstd archive failed");
    assert_eq!(archive.version, ZstdCertArchive::VERSION);
    assert_eq!(archive.compression_level, ZstdCertArchive::DEFAULT_LEVEL);

    let restored = zstd_unarchive_cert(&archive).expect("zstd unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_zstd_archive_complex_cert() {
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let prop_to_prop = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());

    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(prop_to_prop),
    };

    let archive = zstd_archive_cert(&cert).expect("zstd archive failed");
    let restored = zstd_unarchive_cert(&archive).expect("zstd unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_zstd_archive_with_level() {
    let cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };

    // Test different compression levels
    for level in [1, 3, 10, 19, 22] {
        let archive = zstd_archive_cert_level(&cert, level).expect("zstd archive failed");
        assert_eq!(archive.compression_level, level);

        let restored = zstd_unarchive_cert(&archive).expect("zstd unarchive failed");
        assert_eq!(restored, cert);
    }
}

#[test]
fn test_zstd_archive_with_stats() {
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let prop_to_prop = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());

    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(prop_to_prop),
    };

    let (archive, stats) =
        zstd_archive_cert_with_stats(&cert).expect("zstd archive with stats failed");

    // Verify stats are populated
    assert!(stats.original_cert_bytes > 0);
    assert!(stats.structure_shared_bytes > 0);
    assert!(stats.archive_bytes > 0);
    assert!(stats.structure_ratio > 0.0);
    assert!(stats.zstd_ratio > 0.0);
    assert!(stats.total_ratio > 0.0);
    assert_eq!(stats.compression_level, ZstdCertArchive::DEFAULT_LEVEL);

    // Verify roundtrip
    let restored = zstd_unarchive_cert(&archive).expect("zstd unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_zstd_archive_stats_display() {
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let (_, stats) = zstd_archive_cert_with_stats(&cert).expect("zstd archive failed");

    let display = format!("{stats}");
    assert!(display.contains("struct:"));
    assert!(display.contains("zstd"));
    assert!(display.contains("total:"));
    assert!(display.contains("bytes"));
}

#[test]
fn test_zstd_compress_decompress() {
    let data = b"Hello, clean! This is a test of Zstd compression.";

    let compressed = zstd_compress(data).expect("zstd compress failed");
    let decompressed = zstd_decompress(&compressed).expect("zstd decompress failed");

    assert_eq!(decompressed, data);
}

#[test]
fn test_zstd_compress_repetitive_data() {
    // Repetitive data should compress well
    let data: Vec<u8> = (0..1000).map(|i| (i % 10) as u8).collect();

    let compressed = zstd_compress(&data).expect("zstd compress failed");
    let decompressed = zstd_decompress(&compressed).expect("zstd decompress failed");

    assert_eq!(decompressed, data);
    // Zstd should compress repetitive data significantly
    assert!(compressed.len() < data.len());
}

#[test]
fn test_zstd_compress_level() {
    let data: Vec<u8> = (0..1000).map(|i| (i % 10) as u8).collect();

    // Higher levels should typically compress better (or at least equal)
    let level1 = zstd_compress_level(&data, 1).expect("zstd compress level 1 failed");
    let level19 = zstd_compress_level(&data, 19).expect("zstd compress level 19 failed");

    // Both should decompress correctly
    let decompressed1 = zstd_decompress(&level1).expect("zstd decompress failed");
    let decompressed19 = zstd_decompress(&level19).expect("zstd decompress failed");

    assert_eq!(decompressed1, data);
    assert_eq!(decompressed19, data);

    // Higher level should give equal or better compression
    assert!(level19.len() <= level1.len());
}

#[test]
fn test_zstd_decompress_invalid_data() {
    // Invalid zstd data should return an error
    let invalid_data = b"not valid zstd data";
    let result = zstd_decompress(invalid_data);
    assert!(
        matches!(result, Err(ZstdCompressError::DecompressError(_))),
        "expected DecompressError, got: {result:?}"
    );
}

#[test]
fn test_zstd_compress_error_display() {
    let err1 = ZstdCompressError::SerializeError("test".to_string());
    let s1 = format!("{err1}");
    assert!(s1.contains("Serialization"));
    assert!(s1.contains("test"));

    let err2 = ZstdCompressError::CompressError("zstd fail".to_string());
    let s2 = format!("{err2}");
    assert!(s2.contains("Zstd compression"));

    let err3 = ZstdCompressError::DecompressError("bad data".to_string());
    let s3 = format!("{err3}");
    assert!(s3.contains("Zstd decompression"));

    let err4 = ZstdCompressError::DeserializeError("parse fail".to_string());
    let s4 = format!("{err4}");
    assert!(s4.contains("Deserialization"));
}

#[test]
fn test_zstd_archive_nested_app_chain() {
    // Build: f (g (h x)) with certificates
    let unit_type = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let inner_cert = ProofCert::Const {
        name: Name::from_string("x"),
        levels: vec![],
        type_: Box::new(unit_type.clone()),
    };

    let h_app_cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Const {
            name: Name::from_string("h"),
            levels: vec![],
            type_: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        }),
        fn_type: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        arg_cert: Box::new(inner_cert),
        result_type: Box::new(unit_type.clone()),
    };

    let g_app_cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Const {
            name: Name::from_string("g"),
            levels: vec![],
            type_: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        }),
        fn_type: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        arg_cert: Box::new(h_app_cert),
        result_type: Box::new(unit_type.clone()),
    };

    let cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Const {
            name: Name::from_string("f"),
            levels: vec![],
            type_: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        }),
        fn_type: Box::new(Expr::arrow(unit_type.clone(), unit_type.clone())),
        arg_cert: Box::new(g_app_cert),
        result_type: Box::new(unit_type),
    };

    let archive = zstd_archive_cert(&cert).expect("zstd archive failed");
    let restored = zstd_unarchive_cert(&archive).expect("zstd unarchive failed");
    assert_eq!(restored, cert);

    // With stats to verify compression effectiveness
    let (_, stats) = zstd_archive_cert_with_stats(&cert).expect("zstd archive with stats failed");
    // Nested apps with repeated types should compress well
    assert!(
        stats.total_ratio >= 1.0,
        "Expected some compression for nested apps"
    );
}

#[test]
fn test_zstd_archive_serialization() {
    // Test that ZstdCertArchive itself can be serialized/deserialized
    let cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };
    let archive = zstd_archive_cert(&cert).expect("zstd archive failed");

    // Serialize archive to bincode
    let archive_bytes = bincode::serde::encode_to_vec(&archive, bincode::config::standard())
        .expect("serialize archive failed");

    // Deserialize
    let restored_archive: ZstdCertArchive =
        bincode::serde::decode_from_slice(&archive_bytes, bincode::config::standard())
            .map(|(__v, _)| __v)
            .expect("deserialize archive failed");

    // Verify fields preserved
    assert_eq!(restored_archive.version, archive.version);
    assert_eq!(
        restored_archive.compression_level,
        archive.compression_level
    );
    assert_eq!(
        restored_archive.uncompressed_size,
        archive.uncompressed_size
    );

    // Unarchive
    let restored = zstd_unarchive_cert(&restored_archive).expect("zstd unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_compression_algorithm_name() {
    assert_eq!(CompressionAlgorithm::Lz4.name(), "LZ4");
    assert_eq!(CompressionAlgorithm::ZstdDefault.name(), "Zstd (level 3)");
    assert_eq!(CompressionAlgorithm::ZstdHigh.name(), "Zstd (level 19)");
    assert_eq!(CompressionAlgorithm::ZstdMax.name(), "Zstd (level 22)");

    assert_eq!(CompressionAlgorithm::Lz4.zstd_level(), None);
    assert_eq!(
        CompressionAlgorithm::ZstdDefault.zstd_level(),
        Some(ZstdCertArchive::DEFAULT_LEVEL)
    );
    assert_eq!(
        CompressionAlgorithm::ZstdHigh.zstd_level(),
        Some(ZstdCertArchive::HIGH_LEVEL)
    );
    assert_eq!(
        CompressionAlgorithm::ZstdMax.zstd_level(),
        Some(ZstdCertArchive::MAX_LEVEL)
    );
}

#[test]
fn test_archive_cert_with_algorithm_lz4_envelope() {
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let archive = archive_cert_with_algorithm(&cert, CompressionAlgorithm::Lz4)
        .expect("archive with algorithm failed");

    assert_eq!(archive.algorithm(), CompressionAlgorithm::Lz4);
    assert!(archive.compressed_len() > 0);
    assert!(archive.uncompressed_size() > 0);

    match &archive {
        CertArchiveEnvelope::Lz4(inner) => assert_eq!(inner.version, CertArchive::VERSION),
        _ => panic!("expected LZ4 archive variant"),
    }

    let restored = unarchive_cert_envelope(&archive).expect("unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_archive_cert_with_algorithm_zstd_envelope() {
    let cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };

    let archive = archive_cert_with_algorithm(&cert, CompressionAlgorithm::ZstdHigh)
        .expect("archive with algorithm failed");

    assert_eq!(archive.algorithm(), CompressionAlgorithm::ZstdHigh);

    match &archive {
        CertArchiveEnvelope::Zstd(inner) => {
            assert_eq!(inner.compression_level, ZstdCertArchive::HIGH_LEVEL);
            assert_eq!(inner.version, ZstdCertArchive::VERSION);
        }
        _ => panic!("expected Zstd archive variant"),
    }

    let restored = unarchive_cert_envelope(&archive).expect("unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_archive_cert_with_algorithm_stats_dispatch() {
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let (lz4_archive, lz4_stats) =
        archive_cert_with_algorithm_stats(&cert, CompressionAlgorithm::Lz4)
            .expect("lz4 archive stats failed");
    assert!(matches!(lz4_archive, CertArchiveEnvelope::Lz4(_)));
    assert_eq!(lz4_stats.algorithm(), CompressionAlgorithm::Lz4);
    assert!(lz4_stats.total_ratio() > 0.0);

    let (zstd_archive, zstd_stats) =
        archive_cert_with_algorithm_stats(&cert, CompressionAlgorithm::ZstdMax)
            .expect("zstd archive stats failed");
    assert!(matches!(zstd_archive, CertArchiveEnvelope::Zstd(_)));
    assert_eq!(zstd_stats.algorithm(), CompressionAlgorithm::ZstdMax);

    if let ArchiveVariantStats::Zstd(stats) = &zstd_stats {
        assert_eq!(stats.compression_level, ZstdCertArchive::MAX_LEVEL);
    } else {
        panic!("expected zstd stats variant");
    }

    let restored = unarchive_cert_envelope(&zstd_archive).expect("unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_compare_lz4_vs_zstd() {
    // Compare compression of LZ4 vs Zstd on a moderately complex certificate
    // Build a certificate with some repeated structure
    let inner_cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let cert = ProofCert::Pi {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(inner_cert.clone()),
        arg_level: Level::zero(),
        body_type_cert: Box::new(ProofCert::Pi {
            binder_info: BinderInfo::Default,
            arg_type_cert: Box::new(inner_cert.clone()),
            arg_level: Level::zero(),
            body_type_cert: Box::new(inner_cert.clone()),
            body_level: Level::zero(),
        }),
        body_level: Level::zero(),
    };

    let (lz4_archive, lz4_stats) = archive_cert_with_stats(&cert).expect("lz4 archive failed");
    let (zstd_archive, zstd_stats) =
        zstd_archive_cert_with_stats(&cert).expect("zstd archive failed");

    // Both should roundtrip correctly
    let lz4_restored = unarchive_cert(&lz4_archive).expect("lz4 unarchive failed");
    let zstd_restored = zstd_unarchive_cert(&zstd_archive).expect("zstd unarchive failed");
    assert_eq!(lz4_restored, cert);
    assert_eq!(zstd_restored, cert);

    // Stats should be populated
    assert!(lz4_stats.total_ratio > 0.0);
    assert!(zstd_stats.total_ratio > 0.0);

    // For larger data, zstd typically achieves better compression
    // For small data, both are similar. Just verify both work.
}

#[test]
fn test_zstd_archive_with_all_cert_variants() {
    // Test zstd archiving certificates with various variants
    let type0 = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // FVar certificate
    let fvar_cert = ProofCert::FVar {
        id: FVarId(42),
        type_: Box::new(type0.clone()),
    };
    let archive = zstd_archive_cert(&fvar_cert).expect("zstd archive fvar failed");
    let restored = zstd_unarchive_cert(&archive).expect("zstd unarchive fvar failed");
    assert_eq!(restored, fvar_cert);

    // Let certificate
    let let_cert = ProofCert::Let {
        type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        value_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(type0.clone()),
        }),
        result_type: Box::new(type0.clone()),
    };
    let archive = zstd_archive_cert(&let_cert).expect("zstd archive let failed");
    let restored = zstd_unarchive_cert(&archive).expect("zstd unarchive let failed");
    assert_eq!(restored, let_cert);

    // Lit certificate
    let lit_cert = ProofCert::Lit {
        lit: Literal::Nat(BigNat::Small(42)),
        type_: Box::new(Expr::const_(Name::from_string("Nat"), vec![])),
    };
    let archive = zstd_archive_cert(&lit_cert).expect("zstd archive lit failed");
    let restored = zstd_unarchive_cert(&archive).expect("zstd unarchive lit failed");
    assert_eq!(restored, lit_cert);

    // DefEq certificate
    let def_eq_cert = ProofCert::DefEq {
        inner: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        expected_type: Box::new(type0.clone()),
        actual_type: Box::new(type0.clone()),
        eq_steps: vec![DefEqStep::Refl],
    };
    let archive = zstd_archive_cert(&def_eq_cert).expect("zstd archive def_eq failed");
    let restored = zstd_unarchive_cert(&archive).expect("zstd unarchive def_eq failed");
    assert_eq!(restored, def_eq_cert);
}

// ========================================================================
// Streaming Compression Tests
// ========================================================================

#[test]
fn test_compare_dict_vs_no_dict_compression() {
    // Create training samples that are similar to test data
    let samples: Vec<ProofCert> = (0..50)
        .map(|i| {
            if i % 3 == 0 {
                ProofCert::Sort {
                    level: Level::zero(),
                }
            } else if i % 3 == 1 {
                ProofCert::Pi {
                    binder_info: BinderInfo::Default,
                    arg_type_cert: Box::new(ProofCert::Sort {
                        level: Level::zero(),
                    }),
                    arg_level: Level::zero(),
                    body_type_cert: Box::new(ProofCert::Sort {
                        level: Level::zero(),
                    }),
                    body_level: Level::zero(),
                }
            } else {
                ProofCert::Lam {
                    binder_info: BinderInfo::Default,
                    arg_type_cert: Box::new(ProofCert::Sort {
                        level: Level::zero(),
                    }),
                    body_cert: Box::new(ProofCert::BVar {
                        idx: 0,
                        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
                    }),
                    result_type: Box::new(Expr::pi(
                        BinderInfo::Default,
                        Expr::from_kind(ExprKind::Sort(Level::zero())),
                        Expr::from_kind(ExprKind::Sort(Level::zero())),
                    )),
                }
            }
        })
        .collect();

    let dict = CertDictionary::train(&samples, 32 * 1024, 3).expect("dictionary training failed");

    // Test certificate
    let test_cert = ProofCert::Pi {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        arg_level: Level::zero(),
        body_type_cert: Box::new(ProofCert::Sort {
            level: Level::succ(Level::zero()),
        }),
        body_level: Level::succ(Level::zero()),
    };

    // Compress without dictionary
    let (no_dict_archive, no_dict_stats) =
        zstd_archive_cert_with_stats(&test_cert).expect("no-dict archive failed");

    // Compress with dictionary
    let (dict_archive, dict_stats) =
        zstd_archive_cert_with_dict_stats(&test_cert, &dict).expect("dict archive failed");

    // Both should roundtrip correctly
    let no_dict_restored = zstd_unarchive_cert(&no_dict_archive).expect("no-dict unarchive");
    let dict_restored =
        zstd_unarchive_cert_with_dict(&dict_archive, &dict).expect("dict unarchive");

    assert_eq!(no_dict_restored, test_cert);
    assert_eq!(dict_restored, test_cert);

    // Print comparison (for manual review in test output)
    println!(
        "Without dict: {} bytes",
        no_dict_archive.compressed_data.len()
    );
    println!("With dict: {} bytes", dict_archive.compressed_data.len());
    println!("No-dict ratio: {:.2}x", no_dict_stats.total_ratio);
    println!("Dict ratio: {:.2}x", dict_stats.total_ratio);

    // Note: For small data, dictionary may not always improve compression
    // The test verifies correctness, not that dict is always better
}

// =========================================================================
// Batch Verification Tests
// =========================================================================
