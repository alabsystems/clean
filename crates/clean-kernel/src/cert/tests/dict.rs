// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dictionary-based compression tests

use crate::cert::*;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;

#[test]
fn test_dict_from_bytes() {
    // Create dictionary from arbitrary bytes
    let dict_bytes = vec![0u8; 1024];
    let dict = CertDictionary::from_bytes(dict_bytes.clone(), 3);

    assert_eq!(dict.size(), 1024);
    assert_eq!(dict.data, dict_bytes);
    assert_eq!(dict.target_level, 3);
    assert_eq!(dict.version, CertDictionary::VERSION);
    assert!(dict.dict_id != 0); // Should have a computed ID
}

#[test]
fn test_dict_not_enough_samples() {
    // Try to train with too few samples
    let samples: Vec<ProofCert> = vec![
        ProofCert::Sort {
            level: Level::zero(),
        },
        ProofCert::Sort {
            level: Level::succ(Level::zero()),
        },
    ];

    let result = CertDictionary::train(&samples, 1024, 3);
    if let Err(DictTrainError::NotEnoughSamples { provided, minimum }) = result {
        assert_eq!(provided, 2);
        assert_eq!(minimum, CertDictionary::MIN_SAMPLES);
    } else {
        panic!("Expected NotEnoughSamples error");
    }
}

#[test]
fn test_dict_train_and_compress() {
    // Create enough sample certificates for training
    let samples: Vec<ProofCert> = (0..20)
        .map(|i| ProofCert::Sort {
            level: if i % 2 == 0 {
                Level::zero()
            } else {
                Level::succ(Level::zero())
            },
        })
        .collect();

    // Train dictionary
    let dict = CertDictionary::train(&samples, 16 * 1024, 3).expect("dictionary training failed");

    assert!(dict.size() > 0);
    assert_eq!(dict.sample_count, 20);
    assert_eq!(dict.target_level, 3);

    // Compress a new certificate with the dictionary
    let cert = ProofCert::Sort {
        level: Level::succ(Level::succ(Level::zero())),
    };

    let archive = zstd_archive_cert_with_dict(&cert, &dict).expect("dict archive failed");
    assert!(!archive.compressed_data.is_empty());
    assert_eq!(archive.dict_id, dict.dict_id);
    assert_eq!(archive.version, DictCertArchive::VERSION);

    // Decompress and verify
    let restored = zstd_unarchive_cert_with_dict(&archive, &dict).expect("dict unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_dict_compress_complex_cert() {
    // Create varied training samples
    let samples: Vec<ProofCert> = (0..15)
        .map(|i| {
            if i < 5 {
                ProofCert::Sort {
                    level: Level::zero(),
                }
            } else if i < 10 {
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

    // Complex nested certificate
    let complex_cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Lam {
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
        }),
        fn_type: Box::new(Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::Sort(Level::zero())),
            Expr::from_kind(ExprKind::Sort(Level::zero())),
        )),
        arg_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        result_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let archive = zstd_archive_cert_with_dict(&complex_cert, &dict).expect("dict archive failed");
    let restored = zstd_unarchive_cert_with_dict(&archive, &dict).expect("dict unarchive failed");
    assert_eq!(restored, complex_cert);
}

#[test]
fn test_dict_with_stats() {
    let samples: Vec<ProofCert> = (0..10)
        .map(|_| ProofCert::Sort {
            level: Level::zero(),
        })
        .collect();

    let dict = CertDictionary::train(&samples, 8 * 1024, 3).expect("training failed");

    let cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };

    let (archive, stats) =
        zstd_archive_cert_with_dict_stats(&cert, &dict).expect("archive with stats failed");

    assert!(stats.original_cert_bytes > 0);
    assert!(stats.structure_shared_bytes > 0);
    assert!(stats.archive_bytes > 0);
    assert!(stats.structure_ratio > 0.0);
    assert!(stats.dict_ratio > 0.0);
    assert!(stats.total_ratio > 0.0);
    assert_eq!(stats.compression_level, 3);
    assert_eq!(stats.dict_id, dict.dict_id);

    // Stats Display trait
    let display = format!("{stats}");
    assert!(display.contains("DictArchiveStats"));
    assert!(display.contains("struct:"));
    assert!(display.contains("dict["));

    let restored = zstd_unarchive_cert_with_dict(&archive, &dict).expect("unarchive failed");
    assert_eq!(restored, cert);
}

#[test]
fn test_dict_with_level() {
    let samples: Vec<ProofCert> = (0..10)
        .map(|i| ProofCert::Sort {
            level: if i % 2 == 0 {
                Level::zero()
            } else {
                Level::succ(Level::zero())
            },
        })
        .collect();

    let dict = CertDictionary::train(&samples, 8 * 1024, 3).expect("training failed");

    let cert = ProofCert::Sort {
        level: Level::succ(Level::succ(Level::zero())),
    };

    // Test at different compression levels
    for level in [1, 3, 10, 19] {
        let archive = zstd_archive_cert_with_dict_level(&cert, &dict, level)
            .unwrap_or_else(|_| panic!("archive at level {level} failed"));
        assert_eq!(archive.compression_level, level);

        let restored = zstd_unarchive_cert_with_dict(&archive, &dict).expect("unarchive failed");
        assert_eq!(restored, cert);
    }
}

#[test]
fn test_dict_mismatch_error() {
    let samples: Vec<ProofCert> = (0..10)
        .map(|_| ProofCert::Sort {
            level: Level::zero(),
        })
        .collect();

    let dict1 = CertDictionary::train(&samples, 8 * 1024, 3).expect("training dict1 failed");

    // Create a second different dictionary
    let dict2 = CertDictionary::from_bytes(vec![1, 2, 3, 4, 5], 3);

    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    // Compress with dict1
    let archive = zstd_archive_cert_with_dict(&cert, &dict1).expect("archive failed");

    // Try to decompress with dict2
    let result = zstd_unarchive_cert_with_dict(&archive, &dict2);
    if let Err(DictCompressError::DictMismatch { expected, found }) = result {
        assert_eq!(expected, dict1.dict_id);
        assert_eq!(found, dict2.dict_id);
    } else {
        panic!("Expected DictMismatch error");
    }
}

#[test]
fn test_dict_raw_bytes_compress() {
    let samples: Vec<ProofCert> = (0..10)
        .map(|_| ProofCert::Sort {
            level: Level::zero(),
        })
        .collect();

    let dict = CertDictionary::train(&samples, 8 * 1024, 3).expect("training failed");

    // Test raw byte compression
    let data = b"Hello, this is some test data for compression";
    let compressed = zstd_compress_with_dict(data, &dict).expect("compress failed");
    let decompressed = zstd_decompress_with_dict(&compressed, &dict).expect("decompress failed");

    assert_eq!(decompressed, data);
}

#[test]
fn test_dict_raw_bytes_with_level() {
    let samples: Vec<Vec<u8>> = (0..10).map(|i| vec![i as u8; 100]).collect();

    let dict = CertDictionary::train_from_bytes(&samples, 4 * 1024, 3).expect("training failed");

    let data = b"Test data with some repetitive patterns patterns patterns";

    // Compress at level 1 (fast)
    let compressed1 = zstd_compress_with_dict_level(data, &dict, 1).expect("compress l1 failed");
    let decompressed1 =
        zstd_decompress_with_dict(&compressed1, &dict).expect("decompress l1 failed");
    assert_eq!(decompressed1.as_slice(), data);

    // Compress at level 19 (high)
    let compressed19 = zstd_compress_with_dict_level(data, &dict, 19).expect("compress l19 failed");
    let decompressed19 =
        zstd_decompress_with_dict(&compressed19, &dict).expect("decompress l19 failed");
    assert_eq!(decompressed19.as_slice(), data);
}

#[test]
fn test_dict_train_error_display() {
    let err1 = DictTrainError::NotEnoughSamples {
        provided: 3,
        minimum: 5,
    };
    let display1 = format!("{err1}");
    assert!(display1.contains("Not enough samples"));
    assert!(display1.contains('3'));
    assert!(display1.contains('5'));

    let err2 = DictTrainError::SerializeError("test error".to_string());
    let display2 = format!("{err2}");
    assert!(display2.contains("Serialization error"));

    let err3 = DictTrainError::TrainError("zstd fail".to_string());
    let display3 = format!("{err3}");
    assert!(display3.contains("Dictionary training error"));
}

#[test]
fn test_dict_compress_error_display() {
    let err1 = DictCompressError::SerializeError("ser fail".to_string());
    assert!(format!("{err1}").contains("Serialization error"));

    let err2 = DictCompressError::CompressError("comp fail".to_string());
    assert!(format!("{err2}").contains("Dict compression error"));

    let err3 = DictCompressError::DecompressError("decomp fail".to_string());
    assert!(format!("{err3}").contains("Dict decompression error"));

    let err4 = DictCompressError::DeserializeError("deser fail".to_string());
    assert!(format!("{err4}").contains("Deserialization error"));

    let err5 = DictCompressError::DictMismatch {
        expected: 123,
        found: 456,
    };
    let display5 = format!("{err5}");
    assert!(display5.contains("Dictionary ID mismatch"));
    assert!(display5.contains("0x7b")); // 123 in hex
    assert!(display5.contains("0x1c8")); // 456 in hex
}

#[test]
fn test_dict_is_compatible_level() {
    let dict = CertDictionary::from_bytes(vec![0u8; 100], 10);

    // Within 5 levels
    assert!(dict.is_compatible_level(5));
    assert!(dict.is_compatible_level(10));
    assert!(dict.is_compatible_level(15));

    // Outside 5 levels
    assert!(!dict.is_compatible_level(1));
    assert!(!dict.is_compatible_level(19));
}

#[test]
fn test_dict_serialization() {
    let samples: Vec<ProofCert> = (0..10)
        .map(|_| ProofCert::Sort {
            level: Level::zero(),
        })
        .collect();

    let dict = CertDictionary::train(&samples, 4 * 1024, 3).expect("training failed");

    // Serialize the dictionary
    let dict_json = serde_json::to_string(&dict).expect("serialize dict failed");
    let restored_dict: CertDictionary =
        serde_json::from_str(&dict_json).expect("deserialize dict failed");

    assert_eq!(restored_dict.dict_id, dict.dict_id);
    assert_eq!(restored_dict.sample_count, dict.sample_count);
    assert_eq!(restored_dict.target_level, dict.target_level);
    assert_eq!(restored_dict.data, dict.data);

    // Bincode serialization
    let dict_bincode = bincode::serde::encode_to_vec(&dict, bincode::config::standard())
        .expect("serialize dict failed");
    let restored_dict2: CertDictionary =
        bincode::serde::decode_from_slice(&dict_bincode, bincode::config::standard())
            .map(|(__v, _)| __v)
            .expect("deserialize dict failed");
    assert_eq!(restored_dict2.dict_id, dict.dict_id);
}

#[test]
fn test_dict_archive_serialization() {
    let samples: Vec<ProofCert> = (0..10)
        .map(|_| ProofCert::Sort {
            level: Level::zero(),
        })
        .collect();

    let dict = CertDictionary::train(&samples, 4 * 1024, 3).expect("training failed");

    let cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };

    let archive = zstd_archive_cert_with_dict(&cert, &dict).expect("archive failed");

    // Serialize the archive
    let archive_json = serde_json::to_string(&archive).expect("serialize archive failed");
    let restored_archive: DictCertArchive =
        serde_json::from_str(&archive_json).expect("deserialize archive failed");

    assert_eq!(restored_archive.dict_id, archive.dict_id);
    assert_eq!(restored_archive.compressed_data, archive.compressed_data);

    // Verify it can be decompressed
    let restored_cert =
        zstd_unarchive_cert_with_dict(&restored_archive, &dict).expect("unarchive failed");
    assert_eq!(restored_cert, cert);
}
